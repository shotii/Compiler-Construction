module TypeChecker where

import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Data.Map (Map)
import qualified Data.Map as Map
import Environment
import AbsCPP
import PrintCPP
import ErrM

typecheck :: Program -> Err Program
typecheck p = case evalState (runExceptT (checkProgram p)) emptyEnv of
        Left s -> fail ("Error: " ++ s)
        Right p -> return p

checkProgram :: Program -> Check Program
checkProgram (PDefs p) = do
	ret <- checkDefs p
	return (PDefs ret)

checkDefs :: [Def] -> Check [Def]
checkDefs [] = return []
checkDefs ((DFun rtype id args stms):defs) = do
    updateSig id (args, rtype)
    tdefs <- checkDefs defs         
    insertDefBlock args rtype
    mystms <- checkStms stms
    removeBlock
    return ((DFun rtype id args mystms):tdefs)
          
checkStms :: [Stm] -> Check [Stm]
checkStms [] = return []
checkStms (stm:stms) = do 
                        tstm <- checkStm stm
                        tstms <- checkStms stms
                        return (tstm:tstms)

checkStm :: Stm -> Check Stm
checkStm (SExp s) = do
	exp <- inferExp s
	return (SExp exp) 
checkStm (SDecls t []) = return (SDecls t [])
checkStm (SDecls t (id:ids)) = do
                                insertVar id t
                                b <- checkStm $ SDecls t ids
                                return (SDecls t (id:ids))
checkStm (SInit t id exp) = do
        x <- checkExp exp t         
        insertVar id t  
        return (SInit t id x)    
checkStm (SReturn exp) = do
        rtype <- lookupVar $ Id "return"
        x <- checkExp exp rtype 
        return (SReturn x)
checkStm SReturnVoid = do
        rtype <- lookupVar $ Id "return"
        if (rtype == Type_void) then return SReturnVoid else throwError "This return statement should not be void"
checkStm (SWhile exp stm) = do
        texp <- checkExp exp Type_bool
        tstm <- checkStm stm
        return (SWhile texp tstm)
checkStm (SBlock stms) = do
        addBlock
        tstms <- checkStms stms
        removeBlock
        return (SBlock tstms)
checkStm (SIfElse exp stm1 stm2) = do
        texp <- checkExp exp Type_bool
        tstm1 <- checkStm stm1
        tstm2 <- checkStm stm2
        return (SIfElse texp tstm1 tstm2) 


inferExp :: Exp -> Check Exp 
inferExp (ETyped e t) = return (ETyped e t)
inferExp (ETrue) = return (ETyped (ETrue) Type_bool) 
inferExp (EFalse) = return (ETyped (EFalse) Type_bool) 
inferExp (EInt x) = return (ETyped (EInt x) Type_int) 
inferExp (EDouble x) = return (ETyped (EDouble x) Type_double)
inferExp (EString x) = return (ETyped (EString x) Type_string)
inferExp (EId id) = do
	t <- lookupVar id
	return (ETyped (EId id) t)
inferExp (EIncr e1) = do
    --checkExp e1 Type_int
   	(ETyped te1 t) <- inferExp e1
    	if (elem t [Type_int, Type_double])	then return (ETyped (EIncr (ETyped te1 t)) t)
    	else throwError $ "Typemismatch: Integer or Double expected"
inferExp (EDecr e1) = do
	(ETyped te1 t) <- inferExp e1
    	if (elem t [Type_int, Type_double])	then return (ETyped (EDecr (ETyped te1 t)) t)
    	else throwError $ "Typemismatch: Integer or Double expected"
inferExp (EPDecr e1) = do
        (ETyped te1 t) <- inferExp e1
    	if (elem t [Type_int, Type_double])	then return (ETyped (EPDecr (ETyped te1 t)) t)
    	else throwError $ "Typemismatch: Integer or Double expected"
inferExp (EPIncr e1) = do
	(ETyped te1 t) <- inferExp e1
    	if (elem t [Type_int, Type_double])	then return (ETyped (EPIncr (ETyped te1 t)) t)
    	else throwError $ "Typemismatch: Integer or Double expected"
inferExp (EPlus e1 e2) = do 
	((ETyped te1 t), te2) <- inferBin e1 e2 [Type_int, Type_double, Type_string] "+"
	return (ETyped (EPlus (ETyped te1 t) te2) t)
inferExp (EMinus e1 e2)  = do
	((ETyped te1 t), te2) <- inferBin e1 e2 [Type_int, Type_double] "-"
	return (ETyped (EMinus (ETyped te1 t) te2) t)
inferExp (ETimes e1 e2)  = do 
	((ETyped te1 t), te2) <- inferBin e1 e2 [Type_int, Type_double] "*"
	return (ETyped (ETimes (ETyped te1 t) te2) t)
inferExp (EDiv e1 e2)  = do
	((ETyped te1 t), te2) <- inferBin e1 e2 [Type_int, Type_double] "/"
	return (ETyped (EDiv (ETyped te1 t) te2) t)
inferExp (EAss e1 e2) = do
	((ETyped te1 t), te2) <- inferBin e1 e2 [Type_int, Type_double, Type_string, Type_bool] "="
	return (ETyped (EAss (ETyped te1 t) te2) t)
inferExp (EOr e1 e2) = do 
    (te1, te2) <- inferBin e1 e2 [Type_bool] "||"
    return (ETyped (EOr te1 te2) Type_bool)
inferExp (EAnd e1 e2) = do 
    (te1, te2) <- inferBin e1 e2 [Type_bool] "&&"
    return (ETyped (EAnd te1 te2) Type_bool)
inferExp (ENEq e1 e2) = do
    (te1, te2) <- inferBin e1 e2 [Type_int, Type_double, Type_string, Type_bool] "!="
    return (ETyped (ENEq te1 te2) Type_bool)
inferExp (EEq e1 e2) = do 
    (te1, te2) <- inferBin e1 e2 [Type_int, Type_double, Type_string, Type_bool] "=="
    return (ETyped (EEq te1 te2) Type_bool)
inferExp (ELt e1 e2) = do 
    (te1, te2) <- inferBin e1 e2 [Type_int, Type_double, Type_string, Type_bool] "<"
    return (ETyped (ELt te1 te2) Type_bool)
inferExp (EGt e1 e2)  = do 
    (te1, te2) <- inferBin e1 e2 [Type_int, Type_double, Type_string, Type_bool] ">"
    return (ETyped (EGt te1 te2) Type_bool)
inferExp (ELtEq e1 e2) = do
    (te1, te2) <- inferBin e1 e2 [Type_int, Type_double, Type_string, Type_bool] "<="
    return (ETyped (ELtEq te1 te2) Type_bool)
inferExp (EGtEq e1 e2) = do 
    (te1, te2) <- inferBin e1 e2 [Type_int, Type_double, Type_string, Type_bool] ">="
    return (ETyped (EGtEq te1 te2) Type_bool)
inferExp (EApp id exps) = do
    (args, rtype) <- lookupSig id
    ret <- checkFunApp exps args
    return (ETyped (EApp id ret) rtype)
checkFunApp :: [Exp] -> [Type] -> Check [Exp]
checkFunApp [] [] = return []
checkFunApp [] _ = throwError "Number of parameters did not match function"
checkFunApp _ [] = throwError "Number of parameters did not match function"
checkFunApp (e:exps) (argt:argts) = do
            exp1 <- checkExp e argt
            rets <- checkFunApp exps argts
            return (exp1:rets)

inferBin :: Exp -> Exp -> [Type] -> String -> Check (Exp,Exp)
inferBin e1 e2 ts op = do
        (ETyped exp1 at) <- inferExp e1
        unless (elem at ts) $ throwError $ shows at " not defined for operation " ++ op
        exp2 <- checkExp e2 at
        return ((ETyped exp1 at), exp2)

checkExp :: Exp -> Type -> Check Exp
checkExp (ETyped e t) st = if (t == st) then return (ETyped e t) else throwError "Type mismatch"
checkExp ETrue t = if (t == Type_bool) then return (ETyped ETrue Type_bool) else throwError "Type mismatch: Did not expect boolean"
checkExp EFalse t = if (t == Type_bool) then return (ETyped EFalse Type_bool) else throwError "Type mismatch: Did not expect boolean"
checkExp (EInt x) t = if (t == Type_int) then return (ETyped (EInt x) Type_int) else throwError "Type mismatch: Did not expect int"
checkExp (EDouble x) t = if (t == Type_double) then return (ETyped (EDouble x) Type_double) else throwError "Type mismatch: Did not expect double"
checkExp (EString x) t = if (t == Type_string) then return (ETyped (EString x) Type_string) else throwError "Type mismatch: Did not expect string"
checkExp (EId id) t =  do
        at <- lookupVar id
        if (at == t) then return (ETyped (EId id) t) else throwError $ "Type " ++ shows at ( " of " ++ shows id " does not match assumed type " ++ show t )

checkExp (EIncr e1) t = if (notElem t  [Type_int, Type_double]) then throwError $ "Typemismatch: Integer or Double expected" else do
	te1 <- checkExp e1 t
	return (ETyped (EIncr te1) t)
checkExp (EPIncr e1) t =if (notElem t  [Type_int, Type_double]) then throwError $ "Typemismatch: Integer or Double expected" else do 
	te1 <- checkExp e1 t
	return (ETyped (EPIncr te1) t)
checkExp (EDecr e1) t = if (notElem t  [Type_int, Type_double]) then throwError $ "Typemismatch: Integer or Double expected" else do
	te1 <- checkExp e1 t
	return (ETyped (EDecr te1) t)
checkExp (EPDecr e1) t = if (notElem t  [Type_int, Type_double]) then throwError $ "Typemismatch: Integer or Double expected" else do
	te1 <- checkExp e1 t
	return (ETyped (EPDecr te1) t)
checkExp (EAss e1 e2) t = do
       te1 <- checkExp e1 t
       te2 <- checkExp e2 t
       return (ETyped (EAss te1 te2) t)
checkExp (EApp id exps) t = do
         (ETyped (EApp _ texps) rtype) <- inferExp(EApp id exps)
         if (rtype == t) then return (ETyped (EApp id texps) t) else throwError $ "Return type" ++ show rtype ++ " of function " ++ show id ++ " does not match expected type " ++ show t 
checkExp (ETimes e1 e2) t = do
	if (notElem t  [Type_int, Type_double]) then throwError $ "Typemismatch: Integer or Double expected" else do
        	te1 <- checkExp e1 t
        	te2 <- checkExp e2 t
        	return (ETyped (ETimes te1 te2) t)    
checkExp (EPlus e1 e2) t = do
	if (notElem t  [Type_int, Type_double, Type_string]) then throwError $ "Typemismatch: Integer, String or Double expected" else do
        	te1 <- checkExp e1 t
        	te2 <- checkExp e2 t  
        	return (ETyped (EPlus te1 te2) t)    
checkExp (EMinus e1 e2) t = do
	if (notElem t  [Type_int, Type_double]) then throwError $ "Typemismatch: Integer or Double expected" else do
        	te1 <- checkExp e1 t
        	te2 <- checkExp e2 t
        	return (ETyped (EMinus te1 te2) t)
checkExp (EDiv e1 e2) t = 
	if (notElem t  [Type_int, Type_double]) then throwError $ "Typemismatch: Integer or Double expected" else do
        	te1 <- checkExp e1 t
        	te2 <- checkExp e2 t
        	return (ETyped (EDiv te1 te2) t)
checkExp (EEq e1 e2) t = do
        (ETyped (EEq te1 te2) _) <- inferExp (EEq e1 e2)
        return (ETyped (EEq te1 te2) t)
checkExp (ENEq e1 e2) t = do
        (ETyped (ENEq te1 te2) _) <- inferExp (ENEq e1 e2)
        return (ETyped (ENEq te1 te2) t)
checkExp (ELt e1 e2) t = do
        (ETyped (ELt te1 te2) _) <- inferExp (ELt e1 e2)
        return (ETyped (ELt te1 te2) t)
checkExp (EGt e1 e2) t = do
        (ETyped (EGt te1 te2) _) <- inferExp (EGt e1 e2)
        return (ETyped (EGt te1 te2) t)
checkExp (ELtEq e1 e2) t = do
        (ETyped (ELtEq te1 te2) _) <- inferExp (ELtEq e1 e2)
        return (ETyped (ELtEq te1 te2) t)
checkExp (EGtEq e1 e2) t = do
        (ETyped (EGtEq te1 te2) _) <- inferExp (EGtEq e1 e2)
        return (ETyped (EGtEq te1 te2) t)
checkExp (EAnd e1 e2) t = do
        (ETyped (EAnd te1 te2) _) <- inferExp (EAnd e1 e2)
        return (ETyped (EAnd te1 te2) t)
checkExp (EOr e1 e2) t = do
        (ETyped (EOr te1 te2) _) <- inferExp (EOr e1 e2)
        return (ETyped (EOr te1 te2) t)
        


