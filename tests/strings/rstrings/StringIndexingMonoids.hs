{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DeriveTraversable   #-}

{-@ LIQUID "--cores=10"            @-}
{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}
{-@ LIQUID "" @-}

module Main where

import Prelude hiding ( mempty, mappend, id, mconcat, map
                      , take, drop  
                      , error
                      )


import Data.String hiding (fromString)
import GHC.TypeLits
import Data.Maybe 

import String
import Language.Haskell.Liquid.ProofCombinators 

import Data.Proxy 

{-@ symbolVal :: forall n proxy. KnownSymbol n => x:proxy n 
  -> {v:String | v == n && v == symbolVal x } @-}
{-@ measure symbolVal :: p n -> String @-}


-------------------------------------------------------------------------------
----------  Indexing Structure Definition -------------------------------------
-------------------------------------------------------------------------------

data SM (target :: Symbol) where 
  SM :: RString       -- | input string
     -> (List Int)      -- | valid indices of target in input
     -> SM target
  deriving (Show)

{-@ data SM target 
  = SM { input   :: RString
       , indices :: List (GoodIndex input target)
       } @-}

{-@ type GoodIndex Input Target 
  = {i:Int | IsGoodIndex Input Target i }
  @-}

{-@ type GoodIndexTwo Input X Target 
  = {i:Int | (IsGoodIndex Input Target i)  && (IsGoodIndex (concatString Input X) Target i) }
  @-}


{-@ predicate IsGoodIndex Input Target I
  =  (subString Input I (stringLen Target)  == Target)
  && (I + stringLen Target <= stringLen Input)
  && (0 <= I)
  @-}

-------------------------------------------------------------------------------
----------  Monoid Operators on SM --------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect mempty @-}
mempty :: forall (target :: Symbol). (KnownSymbol target) =>  SM target
mempty = SM stringEmp N


{-@ reflect mappend @-}
mappend :: forall (target :: Symbol).  (KnownSymbol target) => SM target -> SM target -> SM target
mappend (SM i1 is1) (SM i2 is2)
  = SM (concatString i1 i2) (is1' `append` is `append` is2')
  where 
    tg   = fromString (symbolVal (Proxy :: Proxy target))
    is1' = map (castGoodIndexRight tg i1 i2) is1
    is   = makeNewIndices i1 i2 tg
    is2' = map (shiftStringRight tg i1 i2)   is2

-- | Helpers 
{-@ reflect shiftStringRight @-}
shiftStringRight :: RString -> RString -> RString -> Int -> Int 
{-@ shiftStringRight :: target:RString -> left:RString -> right:RString -> i:GoodIndex right target 
  -> {v:(GoodIndex {concatString left right} target) | v == i + stringLen left } @-}
shiftStringRight target left right i 
  = cast (subStringConcatFront right left (stringLen target) i) (shift (stringLen left) i)

{-@ reflect makeNewIndices @-}
{-@ makeNewIndices :: s1:RString -> s2:RString -> target:RString -> List (GoodIndex {concatString s1 s2} target) @-}
makeNewIndices :: RString -> RString -> RString -> List Int 
makeNewIndices s1 s2 target
  | stringLen target < 2 
  = N
  | otherwise
  = makeIndices (concatString s1 s2) target
                (maxInt (stringLen s1 - (stringLen target-1)) 0)
                (stringLen s1 - 1)

{-@ reflect maxInt @-}
maxInt :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 

{-@ reflect shift @-}
shift :: Int -> Int -> Int 
shift x y = x + y 

-- | Casting good indices: the below operators are liquid casts and behave like id at runtime


{-@ reflect castGoodIndexRight @-}
castGoodIndexRight :: RString -> RString -> RString -> Int -> Int  
{-@ castGoodIndexRight :: target:RString -> input:RString -> x:RString -> i:GoodIndex input target 
   -> {v:(GoodIndexTwo input x target)| v == i} @-}
castGoodIndexRight target input x i  = cast (subStringConcatBack input x (stringLen target) i) i



-------------------------------------------------------------------------------
----------  Indices' Generation -----------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect makeIndices @-}
makeIndices :: RString -> RString -> Int -> Int -> List Int 
{-@ makeIndices :: input:RString -> target:RString -> lo:Nat -> hi:Int -> List (GoodIndex input target) 
  / [hi - lo] @-}
makeIndices input target lo hi 
  | hi < lo 
  = N
  | lo == hi, isGoodIndex input target lo
  = lo `C` N
  | lo == hi 
  = N
  | isGoodIndex input target lo
  = lo `C` (makeIndices input target (lo + 1) hi)
  | otherwise 
  =    makeIndices input target (lo + 1) hi 

{-@ reflect isGoodIndex @-}
isGoodIndex :: RString -> RString -> Int -> Bool 
{-@ isGoodIndex :: input:RString -> target:RString -> i:Int 
  -> {b:Bool | Prop b <=> IsGoodIndex input target i} @-}
isGoodIndex input target i 
  =  subString input i (stringLen target)  == target  
  && i + stringLen target <= stringLen input
  && 0 <= i    


-------------------------------------------------------------------------------
----------  List Structure ----------------------------------------------------
-------------------------------------------------------------------------------
   
data List a = N | C a (List a) deriving (Eq, Functor, Foldable, Traversable)
{-@ data List [llen] a 
  = N | C {lhead :: a , ltail :: List a} @-}

instance Show a => Show (List a) where
  show xs = "[" ++ go xs ++ "]"
    where
      go N = ""
      go (C x N)  = show x 
      go (C x xs) = show x ++ ", " ++ go xs  

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-} 
llen :: List a -> Int 
llen N        = 0 
llen (C _ xs) = 1 + llen xs 

{-@ reflect map @-}
{-@ map :: (a -> b) -> is:List a -> {os:List b | llen is == llen os} @-}
map :: (a -> b) -> List a -> List b
map _ N        = N
map f (C x xs) = C (f x) (map f xs)

{-@ reflect append @-}
append :: List a -> List a -> List a 
append N        ys = ys 
append (C x xs) ys = x `C` (append xs ys)

{-@ type Pos = {v:Int | 0 < v } @-}




-------------------------------------------------------------------------------
----------  Proof that SM is a Monoid -----------------------------------------
-------------------------------------------------------------------------------


memptyLeft :: forall (target :: Symbol). (KnownSymbol target) => SM target -> Proof
{-@ memptyLeft :: xs:SM target -> {mappend xs mempty == xs } @-}
memptyLeft (SM i is) 
  =   lemma {- 1 -} (concatStringNeutralLeft i)
      lemma {- 2 -} (mapCastId tg i stringEmp is)
      lemma {- 3 -} (makeNewIndicesNullLeft i tg)
      lemma {- 4 -} (appendNil is)
      mappend (SM i is) (mempty :: SM target)
  ==. mappend (SM i is) (SM stringEmp N) 
  ==. SM   (concatString i stringEmp) 
           (is1 `append` isNew `append` is2)
       -- byLemma 1 
  ==. SM i (is1 `append` isNew `append` is2)
  ==. SM i (is  `append` N `append` N)
       -- byLemmata 2, 3 
  ==. SM i is 
       -- byLemma 4 
  *** QED 
  where
    tg    = fromString (symbolVal (Proxy :: Proxy target))
    is1   = map (castGoodIndexRight tg i stringEmp) is
    isNew = makeNewIndices i stringEmp tg
    is2   = map (shiftStringRight tg i stringEmp) N


-------------------------------------------------------------------------------
----------  Lemmata on Lists --------------------------------------------------
-------------------------------------------------------------------------------

{-@ appendNil :: xs:List a -> { append xs N = xs } @-} 
appendNil :: List a -> Proof 
appendNil N 
  =   append N N
  ==. N
  *** QED 
appendNil (C x xs) 
  =   append (C x xs) N
  ==. C x (append xs N)
  ==. C x xs ? appendNil xs 
  *** QED 




-------------------------------------------------------------------------------
----------  Lemmata on Empty Indices ------------------------------------------
-------------------------------------------------------------------------------


makeNewIndicesNullLeft :: RString -> RString -> Proof 
{-@ makeNewIndicesNullLeft 
  :: s:RString 
  -> t:RString 
  -> {makeNewIndices s stringEmp t == N } @-} 

makeNewIndicesNullLeft s t = undefined   
    

-------------------------------------------------------------------------------
----------  Casting Lemmata  --------------------------------------------------
-------------------------------------------------------------------------------



mapCastId :: RString -> RString -> RString -> List Int -> Proof 
{-@ mapCastId :: tg:RString -> x:RString -> y:RString -> is:List (GoodIndex x tg) -> 
      {map (castGoodIndexRight tg x y) is == is} @-}
mapCastId tg x y N 
  = map (castGoodIndexRight tg x y) N ==. N *** QED 
mapCastId tg x y (C i is) 
  =   map (castGoodIndexRight tg x y) (C i is) 
  ==. castGoodIndexRight tg x y i `C` map (castGoodIndexRight tg x y) is 
  ==. i `C` is 
       ? mapCastId tg x y is  
  *** QED 
