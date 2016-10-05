{-# LANGUAGE OverloadedStrings   #-}

{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}

module String where

import qualified Data.ByteString as BS
import qualified Data.String     as ST
import Language.Haskell.Liquid.ProofCombinators 


{-@ embed RString as Str @-}

data RString = S BS.ByteString 
  deriving (Eq, Show)

------------------------------------------------------------------------------
---------------  RString Interface in Logic --------------------------------
------------------------------------------------------------------------------


{-@ invariant {s:RString | 0 <= stringLen s } @-}

{-@ measure stringEmp    :: RString @-}
{-@ measure stringLen    :: RString -> Int @-}
{-@ measure subString    :: RString -> Int -> Int -> RString @-}
{-@ measure concatString :: RString -> RString -> RString @-}
{-@ measure fromString   :: String -> RString @-}
{-@ measure takeString   :: Int -> RString -> RString @-}
{-@ measure dropString   :: Int -> RString -> RString @-}

------------------------------------------------------------------------------
---------------  RString operators -----------------------------------------
------------------------------------------------------------------------------

{-@ assume concatString :: x:RString -> y:RString 
                 -> {v:RString | v == concatString x y && stringLen v == stringLen x + stringLen y } @-}
concatString :: RString -> RString -> RString
concatString (S s1) (S s2) = S (s1 `BS.append` s2)

{-@ assume stringEmp :: {v:RString | v == stringEmp  && stringLen v == 0 } @-}
stringEmp :: RString
stringEmp = S (BS.empty)

stringLen :: RString -> Int  
{-@ assume stringLen :: x:RString -> {v:Nat | v == stringLen x} @-}
stringLen (S s) = BS.length s 

{-@ assume subString  :: s:RString -> offset:Int -> ln:Int -> {v:RString | v == subString s offset ln } @-}
subString :: RString -> Int -> Int -> RString 
subString (S s) o l = S (BS.take l $ BS.drop o s) 

{-@ assume takeString :: i:Nat -> xs:{RString | i <= stringLen xs } -> {v:RString | stringLen v == i && v == takeString i xs } @-} 
takeString :: Int -> RString -> RString
takeString i (S s) = S (BS.take i s)

{-@ assume dropString :: i:Nat -> xs:{RString | i <= stringLen xs } -> {v:RString | stringLen v == stringLen xs - i && v == dropString i xs } @-} 
dropString :: Int -> RString -> RString
dropString i (S s) = S (BS.drop i s)

{-@ assume fromString :: i:String -> {o:RString | i == o && o == fromString i} @-}
fromString :: String -> RString
fromString = S . ST.fromString 

{-@ assume isNullString :: i:RString -> {b:Bool | Prop b <=> stringLen i == 0 } @-} 
isNullString :: RString -> Bool 
isNullString (S s) = BS.length s == 0 

------------------------------------------------------------------------------
---------------  Properties assumed for RStrings ---------------------------
------------------------------------------------------------------------------

-- | Empty Strings 

{-@ assume stringEmpProp :: x:RString  -> { stringLen x == 0 <=> x == stringEmp } @-}
stringEmpProp :: RString -> Proof
stringEmpProp _ = trivial 
 
concatStringNeutralLeft :: RString -> Proof
{-@ assume concatStringNeutralLeft :: x:RString -> {concatString x stringEmp == x} @-}
concatStringNeutralLeft _ = trivial

concatStringNeutralRight :: RString -> Proof
{-@ assume concatStringNeutralRight :: x:RString -> {concatString stringEmp x == x} @-}
concatStringNeutralRight _ = trivial

{-@ concatEmpLeft :: xi:{RString | stringLen xi == 0} -> yi:RString -> {concatString xi yi == yi} @-}
concatEmpLeft :: RString -> RString -> Proof
concatEmpLeft xi yi 
  =   concatString xi yi 
  ==. concatString stringEmp yi ? stringEmpProp xi 
  ==. yi                        ? concatStringNeutralRight yi
  *** QED 


{-@ concatEmpRight :: xi:RString -> yi:{RString | stringLen yi == 0} -> {concatString xi yi == xi} @-}
concatEmpRight :: RString -> RString -> Proof
concatEmpRight xi yi 
  =   concatString xi yi 
  ==. concatString xi stringEmp ? stringEmpProp yi 
  ==. xi                        ? concatStringNeutralLeft xi 
  *** QED 

-- | Concat

{-@ assume concatTakeDrop :: i:Nat -> xs:{RString | i <= stringLen xs} 
    -> {xs == concatString (takeString i xs) (dropString i xs) }  @-}
concatTakeDrop :: Int -> RString -> Proof 
concatTakeDrop _ _ = trivial

concatLen :: RString -> RString -> Proof
{-@ assume concatLen :: x:RString -> y:RString -> { stringLen (concatString x y) == stringLen x + stringLen y } @-}
concatLen _ _ = trivial

concatStringAssoc :: RString -> RString -> RString -> Proof
{-@ assume concatStringAssoc :: x:RString -> y:RString -> z:RString 
     -> {concatString (concatString x y) z == concatString x (concatString y z) } @-}
concatStringAssoc _ _ _ = trivial


-- | Substrings 

{-@ assume subStringConcatBack :: input:RString -> input':RString -> j:Int -> i:{Int | i + j <= stringLen input }
  -> { (subString input i j == subString (concatString input input') i j) 
    && (stringLen input <= stringLen (concatString input input'))
     } @-}
subStringConcatBack :: RString -> RString -> Int -> Int -> Proof 
subStringConcatBack _ _ _ _ = trivial  


{-@ assume subStringConcatFront  
  :: input:RString -> input':RString -> j:Int -> i:Int 
  -> { (subString input i j == subString (concatString input' input) (stringLen input' + i) j)
      && (stringLen (concatString input' input) == stringLen input + stringLen input')
    } @-}
subStringConcatFront :: RString -> RString -> Int -> Int -> Proof
subStringConcatFront _ _ _ _ = trivial
