import Data.Map (Map)
import qualified Data.Map as Map
import AbsCPP
import PrintCPP
import ErrM
import Test.QuickCheck

instance Arbitrary Type where
        arbitrary = elements [Type_bool , Type_int , Type_double , Type_void , Type_string]
instance Arbitrary Id where
        arbitrary = elements [(Id "a"),(Id "b"),(Id "c"),(Id "d"),(Id "e"),(Id "f"),(Id "g")]
                        --(listOf1 $ (elements [(Id "a"),(Id "z")]))
                        --concatter (Id y):[] = Id y
                    --concatter (Id y):(Id x):[] = Id (y++x)
                        --concatter (Id y):(Id x):xs = concatter Id (y ++ x):xs)
--instance (Arbitrary (Map Id Type)) where
        --arbitrary = elements [Map.fromList [Id "test", Type_string]]

type Env = (Sig, [Context])
type Sig = Map Id ([Type], Type)
type Context = Map Id Type

----------------------
-- Update Signature --
----------------------
updateSig :: Env -> Id -> ([Type] , Type) -> Err Env
updateSig ( sigs , contexts)  id_key types_values = case Map.insertLookupWithKey (\ key new old -> old ) id_key types_values  sigs of
                  ( Nothing, newsigs )  -> return (newsigs,contexts)
                  ( Just _, _ ) -> fail ("Function "++ show id_key ++" already exists.")

exampleUpdateSig :: Bool
exampleUpdateSig = updateSig (Map.fromList [(Id "Add",([AbsCPP.Type_int,AbsCPP.Type_int],AbsCPP.Type_int)),(Id "Sub",([AbsCPP.Type_int,AbsCPP.Type_int],AbsCPP.Type_int))],[]) (Id "Main") ([],AbsCPP.Type_int) == Ok ( Map.fromList [(Id "Add",([AbsCPP.Type_int,AbsCPP.Type_int],AbsCPP.Type_int)),(Id "Sub",([AbsCPP.Type_int,AbsCPP.Type_int],AbsCPP.Type_int)),(Id "Main" ,([],AbsCPP.Type_int))] , [] )

justOk :: Err a -> Bool
justOk (Ok _) = True
justOk (Bad _) = False

testUpdateSig :: Env -> Id -> ([Type] , Type) -> Bool
testUpdateSig (sigs , contexts)  id_key types_values = case Map.lookup id_key sigs of
                                        Nothing -> justOk (updateSig (sigs , contexts)  id_key types_values)
                                        Just _  -> not (justOk (updateSig (sigs , contexts)  id_key types_values))
                                        
----------------------
-- Lookup Signature --
----------------------
lookupSig :: Env -> Id -> Err ([Type], Type)
lookupSig (sigs, _) id = case Map.lookup id sigs of
   Nothing       -> fail ("Function " ++ show id ++ " not defined.")
   Just value   -> return value 

----------------------
--Insert Variable --
----------------------
insertVar :: Env -> Id -> Type -> Err Env
insertVar (sig, scope:rest) id vartype = case Map.lookup id scope of 
                                        Nothing  ->  return (sig, (Map.insert id vartype scope):rest)
                                        Just _  -> fail ("Variable " ++ show id ++ " already exists.")


----------------------
-- Lookup Variable --
----------------------
lookupVar :: Env -> Id -> Err Type
lookupVar (sig, []) id                = fail ("Variable " ++ show id ++ " has not been declared.")
lookupVar (sig, scope:rest) id = case Map.lookup id scope of 
                                         Nothing     ->  (lookupVar (sig, rest) id) 
                                         Just vartype   -> return vartype

----------------------
--Add Block --
----------------------
addBlock :: Env -> Env
addBlock (sig, scope) = (sig, Map.empty:scope)

----------------------
--Remove Block --
----------------------
removeBlock :: Env -> Env
removeBlock (sig, scope:rest) = (sig, rest)
