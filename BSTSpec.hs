{-# LANGUAGE PartialTypeSignatures, TemplateHaskell,
    	     FlexibleInstances,MultiParamTypeClasses,StandaloneDeriving
#-}

module BSTSpec where

import qualified Data.List as L
import Data.Maybe
import Data.Function
import Test.QuickCheck
import Control.Applicative
import Control.Monad

import BST
--import QuickSpec

type Key = Int
type Val = Integer
type Tree = BST Key Val

-- invariant properties

prop_ArbitraryValid :: Tree -> Bool
prop_ArbitraryValid = valid

prop_NilValid = valid (nil :: Tree)

prop_InsertValid :: Key -> Val -> Tree -> Bool
prop_InsertValid k v t = valid (insert k v t)

prop_DeleteValid :: Key -> Tree -> Bool
prop_DeleteValid k t = valid (delete k t)

prop_UnionValid :: Tree -> Tree -> Bool
prop_UnionValid t t' = valid (union t t')

-- This property is very slow to test, because the validity function
-- is inefficient.

prop_ShrinkValid :: Tree -> Property
prop_ShrinkValid t =
  valid t ==>
    filter (not . valid) (shrink t) === []

-- postcondition properties

prop_InsertPost :: Key -> Val -> Tree -> Key -> Property
prop_InsertPost k v t k' =
  find k' (insert k v t)
  ===
  if k==k' then Just v else find k' t

prop_DeletePost :: Key-> Tree -> Key -> Property
prop_DeletePost k t k' =
  find k' (delete k t)
  ===
  if k==k' then Nothing else find k' t

prop_FindPostPresent :: Key -> Val -> Tree -> Property
prop_FindPostPresent k v t =
  find k (insert k v t) === Just v

prop_FindPostAbsent :: Key -> BST Key Val -> Property
prop_FindPostAbsent k t =
  find k (delete k t) === Nothing

-- This property justifies testing the find postcondition only in the
-- two cases above.
prop_InsertDeleteComplete :: Key -> Tree -> Property
prop_InsertDeleteComplete k t =
  case find k t of
    Nothing -> t === delete k t
    Just v  -> t === insert k v t

prop_UnionPost :: Tree -> Tree -> Key -> Property
prop_UnionPost t t' k =
  find k (union t t')
  ===
  (find k t <|> find k t')

-- metamorphic properties

prop_SizeInsert :: Key -> Val -> _
prop_SizeInsert k v t =
  size (insert k v t) >= size t

(=~=) :: (Eq k, Eq v, Show k, Show v) => BST k v -> BST k v -> Property
t1 =~= t2 =
  toList t1 === toList t2

-- When the "obvious" metamorphic property fails in a few special
-- cases, we can either add a precondition to the property (making it
-- "weak"), or handle the special case as well. Hence some of the
-- properties below appear in two forms.
prop_InsertInsertWeak :: (Key,Val) -> (Key,Val) -> Tree -> Property
prop_InsertInsertWeak (k,v) (k',v') t =
  k /= k' ==>
    insert k v (insert k' v' t)
    =~=
    insert k' v' (insert k v t)

prop_InsertInsert :: (Key,Val) -> (Key,Val) -> Tree -> Property
prop_InsertInsert (k,v) (k',v') t =
  insert k v (insert k' v' t)
  =~=
  if k==k' then insert k v t else insert k' v' (insert k v t)

prop_InsertDeleteWeak :: (Key,Val) -> Key -> Tree -> Property
prop_InsertDeleteWeak (k,v) k' t =
  k /= k' ==>
    insert k v (delete k' t)
    =~=
    delete k' (insert k v t)

prop_InsertDelete :: (Key,Val) -> Key -> Tree -> Property
prop_InsertDelete (k,v) k' t =
  insert k v (delete k' t)
--  ===
--  delete k' (insert k v t)
  =~=
  if k==k' then insert k v t else delete k' (insert k v t)

prop_InsertUnion :: (Key,Val) -> Tree -> Tree -> Property
prop_InsertUnion (k,v) t t' =
  insert k v (union t t')
  =~=
  union (insert k v t) t'

prop_DeleteNil k =
  delete k nil === (nil :: Tree)
  
prop_DeleteInsertWeak :: Key -> (Key,Val) -> Tree -> Property
prop_DeleteInsertWeak k (k',v') t =
  k /= k' ==>
    delete k (insert k' v' t)
    =~=
    insert k' v' (delete k t)

prop_DeleteInsert :: Key -> (Key,Val) -> Tree -> Property
prop_DeleteInsert k (k',v') t =
  delete k (insert k' v' t)
  =~=
  if k==k' then delete k t else insert k' v' (delete k t)

prop_DeleteDelete :: Key -> Key -> Tree -> Property
prop_DeleteDelete k k' t =
  delete k (delete k' t)
  =~=
  delete k' (delete k t)

prop_DeleteUnion :: Key -> Tree -> Tree -> Property
prop_DeleteUnion k t t' =
  delete k (union t t')
  =~=
  union (delete k t) (delete k t')

prop_UnionInsert :: Tree -> Tree -> (Key,Val) -> Property
prop_UnionInsert t t' (k,v) =
  union (insert k v t) t'
  =~=
  insert k v (union t t')

prop_UnionNil1 :: Tree -> Property
prop_UnionNil1 t =
  union nil t === t

prop_UnionNil2 :: Tree -> Property
prop_UnionNil2 t =
  union t nil === t

prop_UnionDeleteInsert :: Tree -> Tree -> (Key,Val) -> Property
prop_UnionDeleteInsert t t' (k,v) =
  union (delete k t) (insert k v t')
  =~=
  insert k v (union t t')

-- duplicate of prop_DeleteUnion
prop_UnionDeleteDelete :: Tree -> Tree -> Key -> Property
prop_UnionDeleteDelete t t' k =
  union (delete k t) (delete k t')
  =~=
  delete k (union t t')

prop_UnionUnionIdem :: Tree -> Property
prop_UnionUnionIdem t =
  union t t =~= t

prop_UnionUnionAssoc :: Tree -> Tree -> Tree -> Property
prop_UnionUnionAssoc t1 t2 t3 =
  union (union t1 t2) t3
  ===
  union t1 (union t2 t3)

prop_FindNil k =
  find k (nil :: Tree) === Nothing
  
prop_FindInsert :: Key -> (Key,Val) -> Tree -> Property
prop_FindInsert k (k',v') t =
  find k (insert k' v' t)
  ===
  if k==k' then Just v' else find k t

prop_FindDelete :: Key -> Key -> Tree -> Property
prop_FindDelete k k' t =
  find k (delete k' t)
  ===
  if k==k' then Nothing else find k t

-- duplicate of prop_UnionPost
prop_FindUnion :: Key -> Tree -> Tree -> Property
prop_FindUnion k t t' =
  find k (union t t')
  ===
  (find k t <|> find k t')

-- Congruence properties

data Equivs k v = BST k v :=~=: BST k v
  deriving Show

instance (Arbitrary k, Arbitrary v, Ord k) => Arbitrary (Equivs k v) where
  arbitrary = do
    kvs <- L.nubBy ((==) `on` fst) <$> arbitrary
    kvs' <- shuffle kvs
    return (tree kvs :=~=: tree kvs')
    where tree = foldr (uncurry insert) nil
  shrink (t1 :=~=: t2) =
    [ t1' :=~=: patch t1' t2
    | t1' <- shrink t1]
    where patch t1' t2 =
            foldr delete (foldr (uncurry insert) t2 insertions) deletions
            where deletions  = [k | k <- keys t2, isNothing (find k t1')]
                  insertions = [(k,v) | k <- keys t1', let Just v = find k t1']

prop_Equivs :: Equivs Key Val -> Property
prop_Equivs (t :=~=: t') = t =~= t'

prop_ShrinkEquivs :: Equivs Key Val -> Property
prop_ShrinkEquivs (t :=~=: t') =
  t =~= t' ==>
    all (\(t :=~=: t') -> t =~= t') (shrink (t :=~=: t'))
  where t =~= t' = toList t == toList t'

{-
-- This property is ineffective because its precondition discards
-- almost all interesting cases.
prop_InsertPreservesEquivWeak :: Key -> Val -> Tree -> Tree -> Property
prop_InsertPreservesEquivWeak k v t t' =
  toList t == toList t' ==>
    insert k v t =~= insert k v t'
-}

prop_InsertPreservesEquiv :: Key -> Val -> Equivs Key Val -> Property
prop_InsertPreservesEquiv k v (t :=~=: t') =
  insert k v t =~= insert k v t'

prop_DeletePreservesEquiv :: Key -> Equivs Key Val -> Property
prop_DeletePreservesEquiv k (t :=~=: t') =
  delete k t =~= delete k t'

prop_UnionPreservesEquiv :: Equivs Key Val -> Equivs Key Val -> Property
prop_UnionPreservesEquiv (t1 :=~=: t1') (t2 :=~=: t2') =
  union t1 t2 =~= union t1' t2'

prop_FindPreservesEquiv :: Key -> Equivs Key Val -> Property
prop_FindPreservesEquiv k (t :=~=: t') =
  find k t === find k t'

-- Completeness of insertion; every tree can be built just using
-- insert. This justifies the choice of generator.

prop_InsertComplete :: Tree -> Property
prop_InsertComplete t =
  t === foldl (flip $ uncurry insert) nil (insertions t)

prop_InsertCompleteForDelete :: Key -> Tree -> Property
prop_InsertCompleteForDelete k t =
  prop_InsertComplete (delete k t)

prop_InsertCompleteForUnion :: Tree -> Tree -> Property
prop_InsertCompleteForUnion t t' =
  prop_InsertComplete (union t t')

-- Model based properties

prop_NilModel =
  toList (nil :: Tree) === []

prop_InsertModel :: (Key, Val) -> Tree -> Property
prop_InsertModel (k,v) t =
  toList (insert k v t) === L.insert (k,v) (deleteKey k $ toList t)

prop_DeleteModel :: Key -> Tree -> Property
prop_DeleteModel k t =
  toList (delete k t) === deleteKey k (toList t)

prop_UnionModel :: Tree -> Tree -> Property
prop_UnionModel t t' =
  toList (union t t') === L.sort (L.unionBy ((==) `on` fst) (toList t) (toList t'))

prop_FindModel :: Key -> Tree -> Property
prop_FindModel k t =
  find k t === L.lookup k (toList t)

deleteKey k = filter ((/=k) . fst)

-- QuickSpec boilerplate
{-
deriving instance (Ord k, Ord v) => Ord (BST k v)

instance (Ord k, Ord v) => Observe () [(k,v)] (BST k v) where
  observe () = toList

runQuickSpec = quickSpec [
         monoTypeObserve (Proxy :: Proxy Tree),
	 background [
	   con "Nothing" (Nothing :: Maybe Val),
	   con "Just"    (Just    :: Val -> Maybe Val),
	   predicate "/=" ((/=) :: Key -> Key -> Bool)
	   ],
	 
	   con "nil"    (nil  :: Tree),
	   con "find"   (find :: Key -> Tree -> Maybe Val),
	   con "insert" (insert :: Key -> Val -> Tree -> Tree),
	   con "delete" (delete :: Key -> Tree -> Tree),
	   con "union"  (union :: Tree -> Tree -> Tree)
       ]
-}
class EqProp a where
  (====) :: a -> a -> Property

instance EqProp (Maybe Val) where
  x ==== y = property (x == y)

instance EqProp Tree where
  (====) = (=~=)

-- duplicate of prop_UnionUnionIdem
prop_qs_1 :: Tree -> Property
prop_qs_1 x =
  union x x ==== x

-- duplicate of prop_DeleteNil
prop_qs_2 :: Key -> Property
prop_qs_2 x =
  delete x nil ==== (nil :: Tree)

-- duplicate of prop_FindNil
prop_qs_3 :: Key -> Property
prop_qs_3 x =
  find x nil ==== (Nothing :: Maybe Val)

-- duplicate of prop_UnionNil2
prop_qs_4 :: Tree -> Property
prop_qs_4 x =
  union x nil ==== x

-- duplicate of prop_UnionNil1
prop_qs_5 :: Tree -> Property
prop_qs_5 x =
  union nil x ==== x

-- duplicate of prop_DeleteDelete
prop_qs_6 :: Key -> Key -> Tree -> Property
prop_qs_6 x y z =
  delete x (delete y z) ==== delete y (delete x z)

prop_qs_7 :: Key -> Tree -> Property
prop_qs_7 x y =
  delete x (delete x y) ==== delete x y

-- duplicate of prop_FindPostAbsent
prop_qs_8 :: Key -> Tree -> Property
prop_qs_8 x y =
  find x (delete x y) ==== Nothing

prop_qs_9 :: Key -> Key -> Tree -> Property
prop_qs_9 x y z =
  x /= y ==> find x (delete y z) ==== find x z

prop_qs_10 :: Tree -> Key -> Tree -> Property
prop_qs_10 x y z =
  union x (delete y x) ==== x

prop_qs_11 :: Tree -> Tree -> Property
prop_qs_11 x y =
  union x (union x y) ==== union x y

prop_qs_12 :: Tree -> Tree -> Property
prop_qs_12 x y =
  union x (union y x) ==== union x y

prop_qs_13 :: Key -> Tree -> Property
prop_qs_13 x y =
  union (delete x y) y ==== y

-- duplicate of prop_UnionAssoc
prop_qs_14 :: Tree -> Tree -> Tree -> Property
prop_qs_14 x y z =
  union (union x y) z ==== union x (union y z)

prop_qs_15 :: Key -> Val -> Tree -> Property
prop_qs_15 x y z =
  delete x (insert x y z) ==== delete x z

-- duplicate of prop_FindPostPresent
prop_qs_16 :: Key -> Val -> Tree -> Property
prop_qs_16 x y z =
  find x (insert x y z) ==== Just y

prop_qs_17 :: Key -> Val -> Tree -> Property
prop_qs_17 x y z =
  insert x y (delete x z) ==== insert x y z

prop_qs_18 :: Key -> Val -> Key -> Tree -> Property
prop_qs_18 x y z w =
  x /= z ==> insert x y (delete z w) ==== delete z (insert x y w)

-- duplicate of prop_InsertUnion
prop_qs_19 :: Key -> Val -> Tree -> Tree -> Property
prop_qs_19 x y z w =
  union (insert x y z) w ==== insert x y (union z w)

prop_qs_20 :: Key -> Key -> Val -> Property
prop_qs_20 x y z =
  find x (insert y z nil) ==== find y (insert x z nil)

prop_qs_21 :: Tree -> Key -> Val -> Property
prop_qs_21 x y z =
  union x (insert y z x) ==== union x (insert y z nil)

prop_qs_22 :: Key -> Val -> Key -> Tree -> Property
prop_qs_22 x y z w =
  insert x y (insert z y w) ==== insert z y (insert x y w)

prop_qs_23 :: Key -> Tree -> Tree -> Property
prop_qs_23 x y z =
  delete x (union y (delete x z)) ==== delete x (union y z)

prop_qs_24 :: Key -> Tree -> Tree -> Property
prop_qs_24 x y z =
  delete x (union (delete x y) z) ==== delete x (union y z)

prop_qs_25 :: Key -> Tree -> Tree -> Property
prop_qs_25 x y z =
  find x (union y (delete x z)) ==== find x y

prop_qs_26 :: Key -> Tree -> Tree -> Property
prop_qs_26 x y z =
  find x (union (delete x y) z) ==== find x (union z z)

prop_qs_27 :: Tree -> Key -> Tree -> Property
prop_qs_27 x y z =
  union x (delete y (union x z)) ==== union x (delete y z)

-- duplicate of prop_DeleteUnion
prop_qs_28 :: Key -> Tree -> Tree -> Property
prop_qs_28 x y z =
  union (delete x y) (delete x z) ==== delete x (union y z)

prop_qs_29 :: Key -> Tree -> Key -> Property
prop_qs_29 x y z =
  union (delete x y) (delete z y) ==== union (delete z y) (delete x y)

prop_qs_30 :: Key -> Tree -> Tree -> Property
prop_qs_30 x y z =
  union (delete x (union y z)) y ==== union y (delete x z)

prop_qs_31 ::Key -> Tree -> Tree -> Property
prop_qs_31 x y z =
  union (delete x (union y z)) z ==== union (delete x y) z

-- Test all properties in the module: don't touch this code!

return []
runTests :: IO Bool
--runTests = $quickCheckAll
runTests = $forAllProperties $ quickCheckWithResult stdArgs{maxSuccess=10000}

measureTests = do
  writeFile "mttfs.csv" ""
  mapM_ qcmttf $allProperties
  -- $forAllProperties $ qcmttf

qcmttf (pname,p) = do
  putStr $ pname ++ ": "
  m <- mttf p
  appendFile "mttfs.csv" $ name $ replace <$> show m ++"\n"
  if m <= 0 then do
      (m<0) `when` putStrLn "Sometimes passes, sometimes fails"
      quickCheckResult True
    else do
      putStrLn $ "Mean time to failure: "++show m
      r <- quickCheckResult False
      return $ r{numTests=round m}
  where replace '.' = ','
  	replace  c  = c
	name s = pname ++ ";" ++ s

ttf n p = do
  r <- quickCheckWithResult stdArgs{chatty=False,maxSuccess=n} p
  case r of
    Success{} -> return Nothing
    Failure{} -> return $ Just $ numTests r
    _         -> return Nothing

mttf :: Testable p => p -> IO Double
mttf p = do
  m <- ttf 10000 p
  case m of
    Nothing -> return 0
    Just n -> loop 1000 [n]
  where loop :: Int -> [Int] -> IO Double
        loop 0 ns = return $ (fromIntegral $ sum ns) / (fromIntegral $ length ns)
        loop k ns = do
          m <- ttf 1000000 p
	  case m of
	    Nothing ->
	      return (-1) --error "Sometimes passes, sometimes fails"
	    Just n ->
	      loop (k-1) (n:ns)

