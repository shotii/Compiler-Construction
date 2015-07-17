module Environment where

import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Data.Map (Map)
import qualified Data.Map as Map
import AbsCPP
import PrintCPP
import Test.QuickCheck

type Check = ExceptT String (StateT Env Identity)

type Env = (Sig, [Context])
type Sig = Map Id ([Type], Type)
type Context = Map Id Type

emptyEnv :: Env
emptyEnv = (Map.empty,[])

----------------------
-- Update Signature --
----------------------
updateSig :: Id -> ([Arg] , Type) -> Check ()
updateSig id_key (ts,t) = do
	(sig,cs) <- get
	case Map.insertLookupWithKey (\ key new old -> old ) id_key ([x | (ADecl x _) <- ts] ,t) sig of
		( Nothing, newsigs )  -> do
			put (newsigs, cs)
		( Just _, _ ) -> throwError ("Function "++ show id_key ++" already exists.")


insertDefBlock :: [Arg] -> Type -> Check ()
insertDefBlock args rtype = do
			addBlock
			insertArgs args
			insertVar (Id "return") rtype
                                        
----------------------
-- Lookup Signature --
----------------------
lookupSig :: Id -> Check ([Type], Type)
lookupSig id = do
	( sigs , _ ) <- get
	case Map.lookup id sigs of
		Nothing		-> throwError ("Function " ++ show id ++ " not defined.")
		Just value	-> return value 

----------------------
--Insert Variable --
----------------------
insertArgs :: [Arg] -> Check ()
insertArgs [] = return ()
insertArgs ((ADecl t id):ts) = do
	insertVar id t
	insertArgs ts

insertVar :: Id -> Type -> Check ()
insertVar id vartype = do
	--(sig, scope:rest) <- get
	(sig, c:cs) <- get
	case Map.lookup id c of 
		Nothing  ->  put (sig, (Map.insert id vartype c):cs)
		Just _  -> throwError $ "Multiple declarations for variable " ++ show id

----------------------
-- Lookup Variable --
----------------------
lookupVar :: Id -> Check Type
lookupVar id = do
	(sig, cs) <- get
     	case [x | x<-[Map.lookup id m | m <- cs], x /= Nothing] of 
                []                -> throwError $ "Variable " ++ shows id " has not been declared."
                Just x:xs           -> return x

----------------------
--Add Block --
----------------------
addBlock :: Check ()
addBlock = do 
	(sig, scope) <- get
	put (sig, Map.empty:scope)

----------------------
--Remove Block --
----------------------
removeBlock :: Check ()
removeBlock = do
	(sig, scope:rest) <- get 
	put (sig, rest)
