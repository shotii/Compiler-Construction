{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CodeGenerator where

import AbsCPP

import Data.Word
import Data.String
import Data.List
import Data.Function
import qualified Data.Map as Map

import Control.Monad.State
import Control.Monad.Except
import Control.Applicative

import LLVM.General.Module
import LLVM.General.Context

import LLVM.General.AST
import LLVM.General.AST.Global
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.Float as F
import qualified LLVM.General.AST as AST
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST.Attribute as A
import qualified LLVM.General.AST.CallingConvention as CC
import qualified LLVM.General.AST.IntegerPredicate as IP
import qualified LLVM.General.AST.FloatingPointPredicate as FP


-------------------------------------------------------------------------------
-- Codegen State by Stephen Diehl
-------------------------------------------------------------------------------

type SymbolTable = [(String, Operand)]        -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3

data CodegenState                             -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
  = CodegenState {                           
    currentBlock :: Name                     -- Name of the active block to append to
  , blocks       :: Map.Map Name BlockState  -- Blocks for function
  , symtab       :: [SymbolTable]              -- Function scope symbol table
  , blockCount   :: Int                      -- Count of basic blocks
  , count        :: Word                     -- Count of unnamed instructions
  , names        :: Names                    -- Name Supply
  } deriving Show

data BlockState                             -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
  = BlockState {
    idx   :: Int                            -- Block index
  , stack :: [Named Instruction]            -- Stack of instructions
  , term  :: Maybe (Named Terminator)       -- Block terminator
} deriving Show

newtype LLVM a = LLVM { unLLVM :: State AST.Module a }  ---- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
  deriving (Functor, Applicative, Monad, MonadState AST.Module )

runLLVM :: AST.Module -> LLVM a -> AST.Module   -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
runLLVM = flip (execState . unLLVM)

liftError :: ExceptT String IO a -> IO a    -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
liftError = runExceptT >=> either fail return

------------------------------------
--Code Generator
------------------------------------

codeGen :: Program -> IO (AST.Module, String) -- Mostly from https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
codeGen p =  withContext $ \context -> liftError $ withModuleFromAST context mod $ \m -> do
    llstr <- moduleLLVMAssembly m
    return (mod, llstr)
    where
 	  initModule = defaultModule {moduleName = "defaultModule"}
  	  mod = codeGenProgram initModule p


codeGenProgram :: AST.Module -> Program -> AST.Module
codeGenProgram mod (PDefs defs) =
    runLLVM mod modn
	where 
		modn = mapM codeGenDef defs

codeGenDef :: Def -> LLVM ()
codeGenDef (DFun ty id args stms) =  case ty of
  Type_void -> do
    	define ty (show id) args bblock
      where
        bblock = createBlocks $ execCodegen $ do
          entry <- addBlock entryBlockName
          _ <- setBlock entry
	  void $ retvoid
          _ <- forM [ (ty,id) | (ADecl ty id) <- args] $ \a -> do
            var <- alloca $ fst a
            store var (makeLocalOperand (AST.Name $ show $ snd a) (fst a)) $ fst a
            assign  (show (snd a)) var
	  addScope
	  mapM_ codeGenStm stms
	  deleteScope
	  returnCheck  
  _ -> do
    	define ty (show id) args bblock
      where
        bblock = createBlocks $ execCodegen $ do
          entry <- addBlock entryBlockName
          setBlock entry
          forM [ (ty,id) | (ADecl ty id) <- args] $ \a -> do
            var <- alloca $ fst a
            store var (makeLocalOperand (AST.Name $ show $ snd a) (fst a)) $ fst a
            assign  (show (snd a)) var
	  addScope
	  mapM_ codeGenStm stms
	  deleteScope
          returnCheck

codeGenStm :: Stm -> Codegen ()
codeGenStm stm = case stm of
    SExp exp -> void $ codeGenExp exp
    SDecls ty ids -> do
	multiAssign ty ids
    SInit ty id exp -> do
    	x <- alloca ty
    	op <- codeGenExp exp
    	store x op ty
	assign (show id) x
    SReturn exp -> do
    	op <- codeGenExp exp
    	void $ ret op
    SReturnVoid -> void $ retvoid
    SWhile exp stm -> do
    	prewhile <- getBlock
    	condwhile <- addBlock entryBlockName
    	setBlock prewhile
    	br condwhile
    	setBlock condwhile
        condOp <- codeGenExp exp
        body <- addBlock entryBlockName
        setBlock body
        addScope
        codeGenStm stm 
        br condwhile
        deleteScope
        postwhile <- addBlock entryBlockName
        setBlock condwhile
        cbr condOp body postwhile
        setBlock postwhile
        return ()
    SBlock stms -> do
	entry <- addBlock entryBlockName
    	termCheck entry entry
	addScope
	mapM_ codeGenStm stms
	deleteScope
	entry' <- addBlock entryBlockName
	termCheck entry' entry'
    SIfElse exp stmthen stmelse -> do
            preif <- getBlock
            condOp <- codeGenExp exp
            thenblock <- addBlock entryBlockName
            setBlock thenblock
            addScope
            codeGenStm stmthen 
            blk' <- getBlock
            deleteScope
            elseblock <- addBlock entryBlockName
            setBlock elseblock
            addScope
            codeGenStm stmelse
            blk''<- getBlock
            deleteScope
            setBlock preif
            cbr condOp thenblock elseblock
            postif <- addBlock entryBlockName
            setBlock blk' 
            termCheck postif blk''
	    termCheck postif postif
            return ()

codeGenExp :: Exp -> Codegen AST.Operand
codeGenExp (ETyped e t) = case e of
    ETrue -> return $ cons $ C.Int 1 1
    EFalse -> return $ cons $ C.Int 1 0
    EInt i -> return $ cons $ C.Int 32 i
    EDouble d -> return $ cons $ C.Float $ F.Double d
    --EString s -> 
    EId id -> do
	v <- getvar (show id)
	load v t
    EApp id exps -> do
        args <- mapM codeGenExp exps
        call  (makeGlobalOperand (AST.Name (show id)) t) args t
    EPIncr exp ->  case t of
      Type_int -> do
        op <- codeGenExp exp
        add op ( cons $ C.Int 32 1) t
      Type_double -> do
        op <- codeGenExp exp
        fadd op ( cons $ C.Float $ F.Double 1.0) t
    EPDecr exp -> case t of
      Type_int -> do
        op <- codeGenExp exp
        sub op ( cons $ C.Int 32 1) t
      Type_double -> do
        op <- codeGenExp exp
        fsub op ( cons $ C.Float $ F.Double 1.0) t
    EIncr exp -> case t of
      Type_int -> do
        op <- codeGenExp exp
        add op ( cons $ C.Int 32 1) t
      Type_double -> do
        op <- codeGenExp exp
        fadd op ( cons $ C.Float $ F.Double 1.0) t
    EDecr exp -> case t of
      Type_int -> do
        op <- codeGenExp exp
        sub op ( cons $ C.Int 32 1) t
      Type_double -> do
        op <- codeGenExp exp
        fsub op ( cons $ C.Float $ F.Double 1.0) t
    ETimes exp1 exp2 -> case t of
      Type_int -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        mul op1 op2 t
      Type_double -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        fmul op1 op2 t
    EDiv exp1 exp2 -> case t of
      Type_int -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        CodeGenerator.div op1 op2 t
      Type_double -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        fdiv op1 op2 t
    EPlus exp1 exp2 -> case t of
      Type_int -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        add op1 op2 t
      Type_double -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        fadd op1 op2 t
    EMinus exp1 exp2 -> case t of
      Type_int -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        sub op1 op2 t
      Type_double -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        fsub op1 op2 t
    ELt exp1 exp2 -> case t of
      Type_int -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.SLT op1 op2 t
      Type_bool -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.SLT op1 op2 t
      Type_double -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        fcmp FP.OLT op1 op2 t
    EGt exp1 exp2 -> case t of
      Type_int -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.SGT op1 op2 t
      Type_bool -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.SGT op1 op2 t
      Type_double -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        fcmp FP.OGT op1 op2 t
    ELtEq exp1 exp2 -> case t of
      Type_int -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.SLE op1 op2 t
      Type_bool -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.SLE op1 op2 t
      Type_double -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        fcmp FP.OLE op1 op2 t
    EGtEq exp1 exp2 -> case t of
      Type_int -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.SGE op1 op2 t
      Type_bool -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.SGE op1 op2 t
      Type_double -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        fcmp FP.OGE op1 op2 t
    EEq exp1 exp2 -> case t of
      Type_int -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.EQ op1 op2 t
      Type_bool -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.EQ op1 op2 t
      Type_double -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        fcmp FP.OEQ op1 op2 t
    ENEq exp1 exp2 -> case t of
      Type_int -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.NE op1 op2 t
      Type_bool -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        icmp IP.NE op1 op2 t
      Type_double -> do
        op1 <- codeGenExp exp1
        op2 <- codeGenExp exp2
        fcmp FP.ONE op1 op2 t
    EAnd exp1 exp2 -> do
      op1 <- codeGenExp exp1
      op2 <- codeGenExp exp2
      icmp IP.EQ op1 op2 t
    EOr exp1 exp2 -> do
      op1 <- codeGenExp exp1
      op2 <- codeGenExp exp2
      icmp IP.NE op1 op2 t
    EAss exp1 exp2 -> do
        op1 <- codeGenExp' exp1
        op2 <- codeGenExp exp2
        store op1 op2 t
        
codeGenExp' :: Exp -> Codegen AST.Operand
codeGenExp' (ETyped e t) = case e of
    EId id -> getvar (show id)
    a -> codeGenExp (ETyped a t)


termCheck :: AST.Name -> AST.Name -> Codegen ()
termCheck nm1 nm2  = do
    (BlockState id st trm) <- current
    if (trm == Nothing) then do 
        br nm1
        void $ setBlock nm2 
    else 
        void $ setBlock nm2

returnCheck :: Codegen ()
returnCheck = do
         (BlockState id st trm) <- current
         if (trm == Nothing) then do 
                void $ retvoid
            else 
                return ()

multiAssign :: AbsCPP.Type -> [Id] -> Codegen ()
multiAssign ty [] = return ()
multiAssign ty (x:xs) = do
    y <- alloca ty
    assign (show x) y
    multiAssign ty xs


--------------------------------------------------------------------------------
--Scopes
--------------------------------------------------------------------------------
addScope :: Codegen ()
addScope = do
    st <- gets symtab
    modify $ \s -> s {symtab = [[]]++st}

deleteScope :: Codegen ()
deleteScope = do
    st <- gets symtab
    modify $ \s -> s {symtab = tail st}

define :: AbsCPP.Type -> String -> [Arg] -> [BasicBlock] -> LLVM () -- Modified and expanded from the basis from: https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
define rtype label args bblock = do
    modDefs <- gets moduleDefinitions   
    modify $ \s -> s { moduleDefinitions = modDefs ++ [globDef] }
	where
	globDef = GlobalDefinition $ functionDefaults {
   	 name = Name label,
   	 returnType = toASTType rtype,
    	parameters = ([Parameter (toASTType ty) (AST.Name (show id)) [] | (ADecl ty id) <- args], False), 
   	 basicBlocks = bblock
   	 }

toASTType :: AbsCPP.Type -> AST.Type
toASTType t = case t of
	Type_int -> T.i32
	--Type_string ->
	Type_bool -> T.i1
	Type_double -> T.double
	Type_void -> T.void


-------------------------------------------------------------------------------
-- Names by Stephen Diehl (https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3)
-------------------------------------------------------------------------------

type Names = Map.Map String Int

uniqueName :: String -> Names -> (String, Names)
uniqueName nm ns =
  case Map.lookup nm ns of
    Nothing -> (nm,  Map.insert nm 1 ns)
    Just ix -> (nm ++ show ix, Map.insert nm (ix+1) ns)

instance IsString Name where
  fromString = Name . fromString


-------------------------------------------------------------------------------
-- Codegen Operations by Stephen Diehl (https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3)
-------------------------------------------------------------------------------

newtype Codegen a = Codegen { runCodegen :: State CodegenState a }
  deriving (Functor, Applicative, Monad, MonadState CodegenState )

sortBlocks :: [(Name, BlockState)] -> [(Name, BlockState)]
sortBlocks = sortBy (compare `on` (idx . snd))

createBlocks :: CodegenState -> [BasicBlock]
createBlocks m = map makeBlock $ sortBlocks $ Map.toList (blocks m)

makeBlock :: (Name, BlockState) -> BasicBlock
makeBlock (l, (BlockState _ s t)) = BasicBlock l s (maketerm t)
  where
    maketerm (Just x) = x
    maketerm Nothing = error $ "Block has no terminator: " ++ (show l)

entryBlockName :: String
entryBlockName = "block"

emptyBlock :: Int -> BlockState
emptyBlock i = BlockState i [] Nothing

emptyCodegen :: CodegenState
emptyCodegen = CodegenState (Name entryBlockName) Map.empty [] 1 0 Map.empty

execCodegen :: Codegen a -> CodegenState
execCodegen m = execState (runCodegen m) emptyCodegen

fresh :: Codegen Word
fresh = do
  i <- gets count
  modify $ \s -> s { count = 1 + i }
  return $ i + 1

instr :: AbsCPP.Type -> Instruction -> Codegen (Operand)  --modified and expanded
instr t ins = do
  n <- fresh
  let ref = (UnName n)
  blk <- current
  let i = stack blk
  modifyBlock (blk { stack = i ++ [ref := ins] } )
  return $ makeLocalOperand ref t

terminator :: Named Terminator -> Codegen (Named Terminator)
terminator trm = do
  blk <- current
  modifyBlock (blk { term = Just trm })
  return trm

-------------------------------------------------------------------------------
-- Block Stack by Stephen Diehl (https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3)
-------------------------------------------------------------------------------


addBlock :: String -> Codegen Name
addBlock bname = do
  bls <- gets blocks
  ix <- gets blockCount
  nms <- gets names
  let new = emptyBlock ix
      (qname, supply) = uniqueName bname nms
  modify $ \s -> s { blocks = Map.insert (Name qname) new bls
                   , blockCount = ix + 1
                   , names = supply
                   }
  return (Name qname)

setBlock :: Name -> Codegen Name
setBlock bname = do
  modify $ \s -> s { currentBlock = bname }
  return bname

getBlock :: Codegen Name
getBlock = gets currentBlock

modifyBlock :: BlockState -> Codegen ()
modifyBlock new = do
  active <- gets currentBlock
  modify $ \s -> s { blocks = Map.insert active new (blocks s) }

current :: Codegen BlockState
current = do
  c <- gets currentBlock
  blks <- gets blocks
  case Map.lookup c blks of
    Just x -> return x
    Nothing -> error $ "No such block: " ++ show c
       
--------------------------------------------   
-- Symbol Table
--------------------------------------------


assign :: String -> Operand -> Codegen ()
assign var x = do
	st <- gets symtab
	if (null st) then
    		modify $ \s -> s { symtab = [[(var, x)]]}
   	else
		modify $ \s -> s { symtab = ([(var, x)] ++ head (st)):(tail st) }

getvar :: String -> Codegen Operand
getvar var = do
	syms <- gets symtab
	case [ x | x <- [ lookup var sym  | sym <- syms ] , x /= Nothing ] of
		[] -> error $ "Local variable not in scope: -" ++ show var
		Just x:xs -> return x


--References

local ::  AST.Name -> AST.Operand   -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
local = LocalReference T.double

global ::  AST.Name -> C.Constant   -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
global = C.GlobalReference T.double

makeLocalOperand :: AST.Name -> AbsCPP.Type -> AST.Operand
makeLocalOperand name Type_int = LocalReference T.i32 name
makeLocalOperand name Type_double = LocalReference T.float name
makeLocalOperand name Type_void = LocalReference T.void name
--makeLocalOperand name Type_string = LocalReference 
makeLocalOperand name Type_bool = LocalReference T.i1 name

makeGlobalOperand :: AST.Name -> AbsCPP.Type -> AST.Operand
makeGlobalOperand name Type_int = ConstantOperand $ C.GlobalReference T.i32 name
makeGlobalOperand name Type_double = ConstantOperand $ C.GlobalReference T.float name
makeGlobalOperand name Type_void = ConstantOperand $ C.GlobalReference T.void name
--makeGlobalOperand name Type_string = ConstantOperand . AST.GlobalReference 
makeGlobalOperand name Type_bool = ConstantOperand $ C.GlobalReference T.i1 name


-- Arithmetic and Constants
fadd :: Operand -> Operand -> AbsCPP.Type -> Codegen Operand                    -- Modified version based on https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
fadd a b t = instr t $ FAdd NoFastMathFlags a b []

add :: Operand -> Operand -> AbsCPP.Type -> Codegen Operand
add a b t = instr t $ Add True False a b []

fsub :: Operand -> Operand -> AbsCPP.Type -> Codegen Operand                    -- Modified version based on https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
fsub a b t = instr t $ FSub NoFastMathFlags a b []

sub :: Operand -> Operand -> AbsCPP.Type -> Codegen Operand
sub a b t = instr t $ Sub True False a b []

fmul :: Operand -> Operand -> AbsCPP.Type -> Codegen Operand                   -- Modified version based on https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
fmul a b t = instr t $ FMul NoFastMathFlags a b []

mul :: Operand -> Operand -> AbsCPP.Type -> Codegen Operand
mul a b t = instr t $ Mul True False a b []

fdiv :: Operand -> Operand -> AbsCPP.Type -> Codegen Operand                   -- Modified version based on https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
fdiv a b t = instr t $ FDiv NoFastMathFlags a b []

div :: Operand -> Operand -> AbsCPP.Type -> Codegen Operand
div a b t = instr t $ SDiv True a b []

fcmp :: FP.FloatingPointPredicate -> Operand -> Operand -> AbsCPP.Type -> Codegen Operand   -- Modified version based on https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
fcmp cond a b t = instr t $ FCmp cond a b [] 

icmp :: IP.IntegerPredicate -> Operand -> Operand -> AbsCPP.Type -> Codegen Operand
icmp cond a b t = instr t $ ICmp cond a b []

cons :: C.Constant -> Operand                             -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
cons = ConstantOperand

toArgs :: [Operand] -> [(Operand, [A.ParameterAttribute])]                   -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
toArgs = map (\x -> (x, []))

-- Effects
call :: Operand -> [Operand] -> AbsCPP.Type -> Codegen Operand                   -- Modified version based on https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
call fn args t = instr t $ Call False CC.C [] (Right fn) (toArgs args) [] []

alloca :: AbsCPP.Type -> Codegen Operand                                        -- Modified version based on https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
alloca t = instr t $ Alloca (toASTType t) Nothing 0 []

store :: Operand -> Operand -> AbsCPP.Type -> Codegen Operand                   -- Modified version based on https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
store ptr val t = instr t $ Store False ptr val Nothing 0 []

load :: Operand -> AbsCPP.Type -> Codegen Operand                               -- Modified version based on https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
load ptr t = instr t $ Load False ptr Nothing 0 []

-- Control Flow
br :: Name -> Codegen (Named Terminator)                                      -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
br val = terminator $ Do $ Br val []

cbr :: Operand -> Name -> Name -> Codegen (Named Terminator)                 -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
cbr cond tr fl = terminator $ Do $ CondBr cond tr fl []

ret :: Operand -> Codegen (Named Terminator)                                -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
ret val = terminator $ Do $ Ret (Just val) []

retvoid :: Codegen (Named Terminator)
retvoid = terminator $ Do $ Ret Nothing []                                    -- From https://github.com/sdiehl/kaleidoscope/tree/master/src/chapter3
