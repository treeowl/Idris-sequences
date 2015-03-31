module Sequence2

import Control.Isomorphism

%default total

data Tree23 : Nat -> Type -> Type where
    Elem : a -> Tree23 0 a
    Node2 : Nat -> Lazy (Tree23 d a) -> Lazy (Tree23 d a) ->
            Tree23 (S d) a
    Node3 : Nat -> Lazy (Tree23 d a) -> Lazy (Tree23 d a) -> Lazy (Tree23 d a) ->
              Tree23 (S d) a

size23 : Tree23 d a -> Nat
size23 (Elem _) = 1
size23 (Node2 s _ _) = s
size23 (Node3 s _ _ _) = s

-- Recursively defined size, for use in proofs only. Very slow!
rSize23 : Tree23 d a -> Nat
rSize23 (Elem _) = 1
rSize23 (Node2 _ x y) = rSize23 x + rSize23 y
rSize23 (Node3 _ x y z) = rSize23 x + rSize23 y + rSize23 z

instance Foldable (Tree23 d) where
  foldr c n (Elem x) = c x n
  foldr c n (Node2 _ (Delay x) (Delay y)) = foldr c (foldr c n y) x
  foldr c n (Node3 _ (Delay x) (Delay y) (Delay z)) =
    foldr c (foldr c (foldr c n z) y) x

-- Recursively defined toList, for use in proofs only. Very slow!
rToList23 : Tree23 d a -> List a
rToList23 (Elem a) = [a]
rToList23 (Node2 _ x y) = rToList23 x ++ rToList23 y
rToList23 (Node3 _ x y z) = rToList23 x ++ rToList23 y ++ rToList23 z

--sizesAddNode2 : (size23 x = rSize23 x) -> (size23 y = rSize23 y) -> (size23 

--instance Sized (Tree23 d a) where
--  size = size23

data Valid23 : Tree23 d a -> Type where
  ElemValid : Valid23 (Elem x)
  Node2Valid : Valid23 x -> Valid23 y -> Valid23 (Node2 (size23 x + size23 y) x y)
  Node3Valid : Valid23 x -> Valid23 y -> Valid23 z
    -> Valid23 (Node3 (size23 x + size23 y + size23 z) x y z)

valid23ToSizeEq : Valid23 t -> size23 t = rSize23 t
valid23ToSizeEq ElemValid = Refl
valid23ToSizeEq (Node2Valid z w) =
  rewrite valid23ToSizeEq z
  in rewrite valid23ToSizeEq w in Refl
valid23ToSizeEq (Node3Valid w s t) =
  rewrite valid23ToSizeEq w
  in rewrite valid23ToSizeEq s
  in rewrite valid23ToSizeEq t
  in Refl

instance Functor (Tree23 d) where
  map f (Elem x) = Elem (f x)
  map f (Node2 s x y) = Node2 s (map f x) (map f y)
  map f (Node3 s x y z) = Node3 s (map f x) (map f y) (map f z)

data Digit : Nat -> Type -> Type where
  One : Nat -> Lazy (Tree23 d a) -> Digit d a
  Two : Nat -> Lazy (Tree23 d a) -> Lazy (Tree23 d a) -> Digit d a
  Three : Nat -> Lazy (Tree23 d a) -> Lazy (Tree23 d a) ->
          Lazy (Tree23 d a) -> Digit d a
  Four : Nat -> Lazy (Tree23 d a) -> Lazy (Tree23 d a) ->
          Lazy (Tree23 d a) -> Lazy (Tree23 d a) -> Digit d a

instance Foldable (Digit d) where
  foldr c n (One _ (Delay x)) = foldr c n x
  foldr c n (Two _ (Delay x) (Delay y)) = foldr c (foldr c n y) x
  foldr c n (Three _ (Delay x) (Delay y) (Delay z)) = foldr c (foldr c (foldr c n z) y) x
  foldr c n (Four _ (Delay x) (Delay y) (Delay z) (Delay w)) =
    foldr c (foldr c (foldr c (foldr c n w) z) y) x

data ValidDig : Digit d a -> Type where
  OneValid : Valid23 x -> ValidDig (One (size23 x) x)
  TwoValid : Valid23 x -> Valid23 y -> ValidDig (Two (size23 x+size23 y) x y)
  ThreeValid : Valid23 x -> Valid23 y -> Valid23 z -> ValidDig (Three (size23 x+size23 y+size23 z) x y z)
  FourValid : Valid23 x -> Valid23 y -> Valid23 z -> Valid23 w ->
              ValidDig (Four ((size23 x+size23 y)+(size23 z+size23 w)) x y z w)

sizeDig : Digit d a -> Nat
sizeDig (One s _) = s
sizeDig (Two s _ _) = s
sizeDig (Three s _ _ _) = s
sizeDig (Four s _ _ _ _) = s

rSizeDig : Digit d a -> Nat
rSizeDig (One _ x) = rSize23 x
rSizeDig (Two _ x y) = rSize23 x + rSize23 y
rSizeDig (Three _ x y z) = rSize23 x + rSize23 y + rSize23 z
rSizeDig (Four _ x y z w) = (rSize23 x + rSize23 y) + (rSize23 z + rSize23 w)

validDigToSizeEq : ValidDig dig -> sizeDig dig = rSizeDig dig
validDigToSizeEq (OneValid y) =
  rewrite valid23ToSizeEq y in Refl
validDigToSizeEq (TwoValid z w) =
  rewrite valid23ToSizeEq z
  in rewrite valid23ToSizeEq w in Refl
validDigToSizeEq (ThreeValid w s t) =
  rewrite valid23ToSizeEq w
  in rewrite valid23ToSizeEq s
  in rewrite valid23ToSizeEq t in Refl
validDigToSizeEq (FourValid s t u v) =
  rewrite valid23ToSizeEq s
  in rewrite valid23ToSizeEq t
  in rewrite valid23ToSizeEq u
  in rewrite valid23ToSizeEq v in Refl


%elim
data FingerTree : Nat -> Type -> Type where
  Empty : FingerTree d a
  Single : Tree23 d a -> FingerTree d a
  Deep : Nat -> Digit d a -> FingerTree (S d) a -> Digit d a ->
         FingerTree d a

instance Foldable (FingerTree d) where
  foldr c n Empty = n
  foldr c n (Single x) = foldr c n x
  foldr c n (Deep _ pr m sf) = foldr c (foldr c (foldr c n sf) m) pr

sizeFT : FingerTree d a -> Nat
sizeFT Empty = 0
sizeFT (Single x) = size23 x
sizeFT (Deep k x y z) = k

rSizeFT : FingerTree d a -> Nat
rSizeFT Empty = 0
rSizeFT (Single x) = rSize23 x
rSizeFT (Deep _ pr m sf) = rSizeDig pr + rSizeFT m + rSizeDig sf

{-
instance Sized (FingerTree d a) where
  size = sizeFT
  -}

data ValidFT : FingerTree d a -> Type where
  ValidEmpty : ValidFT Empty
  ValidSingle : Valid23 x -> ValidFT (Single x)
  ValidDeep : ValidDig pr -> ValidFT m -> ValidDig sf ->
              ValidFT (Deep (sizeDig pr + sizeFT m + sizeDig sf) pr m sf)

validFTToSizeEq : ValidFT t -> sizeFT t = rSizeFT t
validFTToSizeEq ValidEmpty = Refl -- ?validFTToSizeEq_rhs_1
validFTToSizeEq (ValidSingle y) =
 rewrite valid23ToSizeEq y in Refl
validFTToSizeEq (ValidDeep pr m sf) =
 rewrite validDigToSizeEq pr
 in rewrite validFTToSizeEq m
 in rewrite validDigToSizeEq sf in Refl

--validDeepToBetterSize : ValidFT (Deep s pr m sf) -> sizeFT (Deep s pr m sf) = sizeDig pr + sizeFT m + sizeDig sf
--validDeepToBetterSize (ValidDeep x y z) = ?

buildValidFT : ValidDig pr -> ValidFT m -> ValidDig sf -> {s:Nat} ->
               (s = sizeDig pr + sizeFT m + sizeDig sf) ->
               ValidFT (Deep s pr m sf)
buildValidFT vpr vm vsf sprf =
  rewrite sprf
  in ValidDeep vpr vm vsf

record Seq : Type -> Type where
  MkSeq : FingerTree 0 a -> Seq a

instance Foldable Seq where
  foldr c n (MkSeq t) = foldr c n t

-- shallowFT : {d:Nat} -> {

{-
deepen23 : {d:Nat} -> {dn : Nat} -> Tree23 d (Tree23 (S dn) a) -> Tree23 (S d) (Tree23 dn a)
deepen23 {dn} (Elem x) = ?deepen23_rhs_1
deepen23 (Node2 k x y) = ?deepen23_rhs_2
deepen23 (Node3 k x y z) = ?deepen23_rhs_3
-}

-- For proofs.
{-
deepenFT : {d:Nat} -> {dn : Nat} -> FingerTree (S d) (Tree23 dn a) -> FingerTree d (Tree23 (S dn) a)
deepenFT {d = d} Empty = Empty
deepenFT {d = d} {dn} (Single x) = ?deepen_rhs_2
deepenFT {d = d} {dn} (Deep k x y z) = ?deepen_rhs_3
-}

toListFTH : FingerTree d a -> List (Tree23 d a) -> List (Tree23 d a)
toListFTH Empty r = r
toListFTH (Single x) r = x :: r
toListFTH (Deep pr m sf) = ?toListFTHRHS


{-
toList : Seq a -> List a
toList = foldr (::) []
-}

data ValidSeq : Seq a -> Type where
  MkValidSeq : ValidFT t -> ValidSeq (MkSeq t)

-- TODO: length and all


emptySeq : Seq a
emptySeq = MkSeq Empty

emptyValid : ValidSeq emptySeq
emptyValid = MkValidSeq ValidEmpty

singleton : a -> Seq a
singleton x = MkSeq (Single (Elem x))

singletonValid : ValidSeq (singleton x)
singletonValid {x} = MkValidSeq (ValidSingle ElemValid)

valid23to23 : {t:Tree23 d a} -> Valid23 t -> Tree23 d a
valid23to23 {t} v = t

validFTToFT : {t:FingerTree d a} -> ValidFT t -> FingerTree d a
validFTToFT {t} v = t

validDigToDig : {dig:Digit d a} -> ValidDig dig -> Digit d a
validDigToDig {dig} v = dig

consFT : Tree23 d a -> FingerTree d a -> FingerTree d a
consFT x Empty = Single x
consFT x (Single y) = Deep (size23 x + size23 y) (One (size23 x) x) Empty (One (size23 y) y)
consFT x (Deep s (One spr y) m sf) = Deep (size23 x + s) (Two (size23 x+spr) x y) m sf
consFT x (Deep s (Two spr y z) m sf) = Deep (size23 x + s) (Three (size23 x+spr) x y z) m sf
consFT x (Deep s (Three spr y z w) m sf) = Deep (size23 x + s) (Four (size23 x +spr) x y z w) m sf
consFT x (Deep s (Four spr y z w v) m sf) =
  Deep (size23 x + s) (Two (size23 x+size23 y) x y) (Node3 (size23 z + size23 w + size23 v) z w v `consFT` m) sf

consFTSizeRight : (node : Tree23 d a) -> (tree : FingerTree d a) ->
                  sizeFT (consFT node tree) = size23 node + sizeFT tree
consFTSizeRight node Empty = rewrite plusZeroRightNeutral (size23 node) in Refl -- ?consFTSizeRight_rhs_1
consFTSizeRight node (Single x) = Refl
consFTSizeRight node (Deep k (One spr x) y z) = Refl
consFTSizeRight node (Deep k (Two spr x w) y z) = Refl
consFTSizeRight node (Deep k (Three spr x w s) y z) = Refl
consFTSizeRight node (Deep k (Four spr x w s t) y z) = Refl

-- It may be possible to write this more concisely, but
-- IT WORKS IT WORKS IT WORKS! AT LAST!

{-
consFTValid : Valid23 x -> ValidFT t -> ValidFT (consFT x t)
consFTValid xv ValidEmpty = ValidSingle xv
consFTValid {x} xv (ValidSingle zv {x=z}) =
  let prValid = OneValid xv
      sfValid = OneValid zv
      pzrn = plusZeroRightNeutral (size23 x)
      pcr = plusConstantRight (plus (size23 x) 0) (size23 x) (size23 z) pzrn
  in rewrite sym pcr
    in ValidDeep prValid ValidEmpty sfValid -- ?consFTValidSingle
consFTValid {x} xv (ValidDeep (OneValid y {x=x1}) vm vsf) =
  let prValid = TwoValid xv y
      m = validFTToFT vm
      sf = validDigToDig vsf
  in rewrite sym $ plusAssociative (size23 x1) (sizeFT m) (sizeDig sf)
  in rewrite plusAssociative (size23 x) (size23 x1) (plus (sizeFT m) (sizeDig sf))
  in rewrite plusAssociative (plus (size23 x) (size23 x1)) (sizeFT m) (sizeDig sf)
  in ValidDeep prValid vm vsf
consFTValid {x} xv (ValidDeep (TwoValid yv zv {x=x1} {y=x2}) vm vsf) =
  let assocPr = plusAssociative (size23 x) (size23 x1) (size23 x2)
  in rewrite assocPr
  in let prValid = ThreeValid xv yv zv
         m = validFTToFT vm
         sf = validDigToDig vsf
  in rewrite sym $ plusAssociative (size23 x1 + size23 x2) (sizeFT m) (sizeDig sf)
  in rewrite plusAssociative (size23 x) (size23 x1+size23 x2) (plus (sizeFT m) (sizeDig sf))
  in rewrite plusAssociative (plus (size23 x) (size23 x1+size23 x2)) (sizeFT m) (sizeDig sf)
  in rewrite assocPr in ValidDeep prValid vm vsf
consFTValid {x} xv (ValidDeep (ThreeValid yv zv wv {x=x1} {y=x2} {z=x3}) vm vsf) =
  let assocPr1 = plusAssociative (size23 x) (size23 x1+size23 x2) (size23 x3)
      assocPr2 = plusAssociative (size23 x) (size23 x1) (size23 x2)
  in rewrite assocPr1
  in rewrite assocPr2
  in let prValid = FourValid xv yv zv wv
         m = validFTToFT vm
         sf = validDigToDig vsf
  in rewrite sym $ plusAssociative (size23 x1 + size23 x2 + size23 x3) (sizeFT m) (sizeDig sf)
  in rewrite plusAssociative (size23 x) (size23 x1+size23 x2+size23 x3) (plus (sizeFT m) (sizeDig sf))
  in rewrite plusAssociative (plus (size23 x) (size23 x1+size23 x2+size23 x3)) (sizeFT m) (sizeDig sf)
  in rewrite assocPr1
  in rewrite assocPr2
  in rewrite sym $ plusAssociative (size23 x + size23 x1) (size23 x2) (size23 x3)
  in ValidDeep prValid vm vsf
consFTValid {x} xv (ValidDeep (FourValid {x=x1} yv {y} zv {z} wv {w} uv) vm {m} vsf {sf}) =
  let newPrefixValid = TwoValid xv yv
      newPrefixSizeEq = validDigToSizeEq newPrefixValid
      newNodeValid = Node3Valid zv wv uv
      newMiddleValid = consFTValid newNodeValid vm
  in rewrite plusAssociative (size23 x) (plus (plus (plus (size23 x1) (size23 y)) (plus (size23 z) (size23 w))) (sizeFT m)) (sizeDig sf)
   in rewrite sym $ plusAssociative (size23 x1) (size23 y) (plus (size23 z) (size23 w))
    in rewrite plusAssociative (size23 y) (size23 z) (size23 w)
     in rewrite sym $ plusAssociative (size23 x1) (plus (plus (size23 y) (size23 z)) (size23 w)) (sizeFT m)
      in rewrite plusAssociative (size23 x) (size23 x1) (plus (plus (plus (size23 y) (size23 z))(size23 w)) (sizeFT m))
       in rewrite sym $ consFTSizeRight (Node3 (plus (plus (size23 y)(size23 z)) (size23 w)) (Delay y) (Delay z) (Delay w)) m
        in ValidDeep newPrefixValid newMiddleValid vsf
        -}

cons : a -> Seq a -> Seq a
cons x (MkSeq t) = MkSeq (consFT (Elem x) t)

consToListWorks : {x:a} -> {xs:Seq a} -> toList (cons x xs) = x :: toList xs
consToListWorks {x = x} {xs = (MkSeq Empty)} = Refl
consToListWorks {x = x} {xs = (MkSeq (Single y))} = Refl
consToListWorks {x = x} {xs = (MkSeq (Deep k y z w))} = ?consTo_4

---------- Proofs ----------

