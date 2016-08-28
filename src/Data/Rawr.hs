{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | == Prerequisite
--
--   You need GHC >= 8.0 and the following extensions in order to use this library:
--
--   >>> :set -XFlexibleContexts -XDataKinds -XOverloadedLabels -XScopedTypeVariables -XTypeOperators
--   >>> import Data.Rawr
--
--   as well as a few imports and extensions that will be used throughout this tutorial (but are not required to use this library):
--
--   >>> :set -XBangPatterns -XTypeFamilies
--   >>> import Control.Lens ((^.), (.~), (%~), (&))
--   >>> :m + Data.Monoid Data.Type.Equality
--
--   == Record Types
--
--   The type function 'R' is used to construct a record type:
--
--   >>> type Foo = R ( "a" := Int, "b" := Bool )
--
--   The above is analogous to the Haskell @data@ declaration:
--
--   >>> data FooHs = FooHs { a :: Int, b :: Bool }
--
--   Note that the order of fields doesn't matter. The record automatically sorts its fields by labels during construction, so the following two are equivalent:
--
--   >>> Refl :: R ( "a" := Int, "b" := Bool ) :~: R ( "b" := Bool, "a" := Int )
--   Refl
--
--   == Records
--
--   'R' is used to construct a value of type @Foo@:
--
--   >>> let foo = R ( #a := 42, #b := True ) :: Foo
--
--   This is the same as:
--
--   >>> let fooHs = FooHs { a = 42, b = True } :: FooHs
--
--   As is the case of record type declaration, the order of fields isn't significant either:
--
--   >>> let foo2 = R ( #b := True, #a := 42 ) :: Foo
--
--   Attempting to construct a record with duplicate labels is a type error:
--
--   >>> R ( #a := 1, #a := 1 )
--   <BLANKLINE>
--   ... error:
--   ... Duplicate labels "a"
--   ...
--
--   == Selector Labels
--
--   Labels can be used as selectors:
--
--   >>> #a foo
--   42
--
--   >>> #b foo
--   True
--
--   Selecting a non-existent field is a type error:
--
--   >>> #c foo
--   <BLANKLINE>
--   ... error:
--   ... Label "c" does not occur in R ( "a" := Int, "b" := Bool )
--   ...
--
--   == Lenses
--
--   You can also use labels as van Laarhoven lens:
--
--   >>> foo ^. #a
--   42
--
--   Due to the way van Laarhoven lenses are defined, this library does not need to depend on the @lens@ library, and you can use any of the alternative lens libraries that work with van Laarhoven lenses (@microlens@, @lens-family@, ..., etc).
--
--   Using label lenses on a non-existent field is also a type error:
--
--   >>> foo ^. #c
--   <BLANKLINE>
--   ... error:
--   ... Label "c" does not occur in R ( "a" := Int, "b" := Bool )
--   ...
--
--   == Pattern Matching
--
--   You can pattern match on records too! Unfortunately, as overloaded labels aren't supported in patterns (as of GHC 8.0.1), you need to supply the type annotation manually:
--
--   >>> case foo of R ( _ := b :: "b" := Bool, _ := a :: "a" := Int ) -> (a, b)
--   (42,True)
--
--   Notice that the order is also insignificant here.
--
--   === Pseudo row-polymorphism
--
--   You can match on parts of a record using 'P':
--
--   >>> case foo of r@(P ( _ := a :: "a" := Int )) -> r & #a .~ (a * 2)
--   R ( a := 84, b := True )
--
--   The difference is that while 'R' needs to match all fields of a record (as it is the inverse of constructing a record using `R`), 'P' doesn't.
--
--   With @PartialTypeSignatures@, you may omit the types of fields in the signature if they can be inferred from the usage:
--
--   >>> :set -XPartialTypeSignatures -Wno-partial-type-signatures
--   >>> case foo of r@(P ( _ := a :: "a" := _ )) -> r & #a .~ (a * 2)
--   R ( a := 84, b := True )
--
--   == Nested Records
--
--   Records can be arbitrarily nested:
--
--   >>> :{
--          type User = R ( "id" := Int, "name" := String )
--          type Post = R ( "id" := Int, "content" := String, "user" := User )
--       :}
--
--   >>> :{
--          let post = R ( #id := 123
--                       , #content := "lorem ipsum"
--                       , #user := R ( #id := 456
--                                    , #name := "testuser"
--                                    )
--                       ) :: Post
--       :}
--
--   Although the @id@ field is duplicated in both @User@ and @Post@, both selector labels and lenses are overloaded and will do the right thing™:
--
--   >>> #id post
--   123
--
--   >>> #id (#user post)
--   456
--
--   >>> post ^. #user . #id
--   456
--
--   >>> post & #user . #name %~ (<> "2")
--   R ( content := "lorem ipsum", id := 123, user := R ( id := 456, name := "testuser2" ) )
--
--   Examples of error messages with nested access via lenses:
--
--   >>> post ^. #user . #error
--   <BLANKLINE>
--   ... error:
--   ... Label "error" does not occur in R ( "id" := Int, "name" := [Char] )
--   ...
--
--   >>> post & #user . #error .~ "impossible"
--   <BLANKLINE>
--   ... error:
--   ... Label "error" does not occur in R ( "id" := Int, "name" := [Char] )
--   ...
--
--   == Extensible Records
--
--   You can merge two records together with ':*:':
--
--   >>> R ( #foo := True ) :*: R ( #bar := False )
--   R ( bar := False, foo := True )
--
--   Attempting to merge two records with duplicate labels is an error:
--
--   >>> R ( #foo := True ) :*: R ( #foo := True )
--   <BLANKLINE>
--   ... error:
--       • Duplicate labels "foo"
--   ...
--
--   The same operator can be used to partition a record type as well. In this case, the LHS determines the result of the partition. We can use this to model row-polymorphism:
--
--   >>> let f (R ( _ := a :: "a" := Int ) :*: _) = a * 2
--   >>> f $ R ( #a := (1 :: Int), #b := True )
--   2
--   >>> f $ R ( #a := (2 :: Int), #b := True, #c := False )
--   4
--
--   Renaming a field:
--
--   >>> let f (R ( _ := x :: "a" := Int ) :*: r) = R ( #x := x ) :*: r
--   >>> f $ R ( #a := (1 :: Int), #b := True )
--   R ( b := True, x := 1 )
--   >>> f $ R ( #a := (2 :: Int), #b := True, #c := False )
--   R ( b := True, c := False, x := 2 )
--   >>> f $ R ( #a := (3 :: Int), #x := True )
--   <BLANKLINE>
--   ... error:
--   ... Duplicate labels "x"
--   ...
--
--   == Strict Fields
--
--   To declare a field as strict, use ':=!' instead of ':='.
--
--   >>> type Bar = R ( "a" :=! Int, "b" := Bool, "c" :=! Char )
--   >>> data BarHs = BarHs { a :: !Int, b :: Bool, c :: !Char }
--   >>> let bar = R ( #a :=! 42, #b := True, #c :=! 'c' ) :: Bar
--
--   Constructing a record with a strict field bound to ⊥ is ⊥:
--
--   >>> R ( #a := undefined ) `seq` ()
--   ()
--   >>> R ( #a :=! undefined ) `seq` ()
--   *** Exception: Prelude.undefined
--   ...
--
--   >>> R ( #a := () ) & #a .~ undefined `seq` ()
--   ()
--   >>> R ( #a :=! () ) & #a .~ undefined `seq` ()
--   *** Exception: Prelude.undefined
--   ...
--
--   The current implementation of strict fields leaks the strictness info into the record's type. This implies that two records with same labels and types but different strictness properties aren't the same. (This may actually be a good thing?)
--
--   >>> Refl :: R ( "a" := () ) :~: R ( "a" :=! () )
--   <BLANKLINE>
--   ... error:
--   ... Couldn't match type ‘'Lazy’ with ‘'Strict’
--   ...
--
--   == Newtype
--
--   You can put records in a newtype, thus "giving" the record a name:
--
--   >>> newtype Baz = Baz ( R ( "l" := Int ) )
--   >>> let baz = Baz $ R ( #l := 1 )
--
--   Now you can construct cyclic records:
--
--   >>> newtype C = C ( R ( "c" := C ) ) deriving Show
--   >>> let c = C $ R ( #c := c )
--   >>> putStrLn $ take 100 $ show c
--   C R ( c := C R ( c := C R ( c := C R ( c := C R ( c := C R ( c := C R ( c := C R ( c := C R ( c := C
--
--   == Unlabeled Fields
--
--   It is also possible to have records with unlabeled fields. In this case, all operations are based on each field's position.
--
--   >>> let r = R (True, 42 :: Int, "foo" :: String, 'c')
--   >>> r
--   R ( True, 42, "foo", 'c' )
--
--   >>> case r of R (a :: Bool, b :: Int, c :: String, d :: Char) -> (a, b, c, d)
--   (True,42,"foo",'c')
--
--   >>> case r of R (a :: Bool, b :: Int) :*: _ -> (a, b)
--   (True,42)

module Data.Rawr
  (
  -- * Fields
    Strictness(..), Field(..), (:=), (:=!)
  -- ** Patterns for fields
  , pattern (:=), pattern (:=!), pattern Field, pattern Field'
  -- * Records
  -- $records
  -- ** Patterns for records
  , R, pattern R, pattern P
  -- ** Indexing records
  , (:!!)(..)
  -- ** Merging & partitioning records
  , (:*:), pattern (:*:)
  , (::*:)
  -- * Utilities
  , (:~)
  ) where

import Control.DeepSeq
import Data.Functor.Const
import Data.Foldable
import Data.Proxy
import GHC.Generics (Generic)
import GHC.TypeLits
import GHC.Types
import GHC.OverloadedLabels
import Language.Haskell.TH hiding (Strict)

-- | A helper type synonym to convert functional dependencies into nicer type-equality-like syntax.
--
--   >  (:!!) s a t
--
--   is equivalent to
--
--   >  t :~ (s :!! a)
--
--   which is roughly equivalent to:
--
--   >  t ~ (s !! a)
type (:~) r (f :: * -> Constraint) = f r
infix 0 :~

-- | Strictness annotations for a 'Field'.
data Strictness = Lazy | Strict

-- | A 'Field' consists of its strictness, an optional label (type-level 'Symbol') and the field's type:
--
--   >>> :kind Field
--   Field :: Strictness -> Maybe Symbol -> * -> *
--
data Field (s :: Strictness) (l :: Maybe Symbol) t = MkField { unField :: t } deriving (Eq, Ord, Generic, NFData)

instance (Monoid t) => Monoid (Field s l t) where
  mempty = MkField mempty
  MkField x `mappend` MkField y = MkField (x `mappend` y)

class WrapInField t f where
  wrapInField :: t -> f

instance WrapInField t (Field 'Lazy l t) where
  {-# INLINE wrapInField #-}
  wrapInField t = MkField t

instance WrapInField t (Field 'Strict l t) where
  {-# INLINE wrapInField #-}
  wrapInField !t = MkField t

-- | A labeled lazy field.
--
--   >>> :kind! "foo" := Int
--   "foo" := Int :: *
--   = Field 'Lazy ('Just "foo") Int
type family (:=) (l :: Symbol) (t :: *) = (f :: *) | f -> l t where
  (:=) l t = Field 'Lazy ('Just l) t

-- | A labeled strict field.
--
--   >>> :kind! "foo" :=! Int
--   "foo" :=! Int :: *
--   = Field 'Strict ('Just "foo") Int
type family (:=!) (l :: Symbol) (t :: *) = (f :: *) | f -> l t where
  (:=!) l t = Field 'Strict ('Just l) t

infix 2 :=
infix 2 :=!

-- | Construct or pattern-match a lazy labeled field.
--
--   >>> :t #foo := True
--   #foo := True :: Field 'Lazy ('Just "foo") Bool
pattern (:=) :: KnownSymbol l => Proxy l -> t -> Field 'Lazy ('Just l) t
pattern p := t <- ((\(MkField t) -> (Proxy :: Proxy l, t)) -> (p, t)) where
  _ := t = MkField t

-- | Construct or pattern-match a strict labeled field.
--
--   >>> :t #foo :=! True
--   #foo :=! True :: Field 'Strict ('Just "foo") Bool
pattern (:=!) :: KnownSymbol l => Proxy l -> t -> Field 'Strict ('Just l) t
pattern p :=! t <- ((\(MkField t) -> (Proxy :: Proxy l, t)) -> (p, t)) where
  _ :=! (!t) = MkField t

-- | Construct or pattern-match a lazy unlabeled field.
--
--   >>> :t Field True
--   Field True :: Field 'Lazy 'Nothing Bool
pattern Field :: t -> Field 'Lazy 'Nothing t
pattern Field t <- (unField -> t) where
  Field t = MkField t

-- | Strict version of `Field`.
--
--   >>> :t Field' True
--   Field' True :: Field 'Strict 'Nothing Bool
--
--   This can be used to construct a strict tuple:
--
--   >>> let !r  = R ( True, undefined :: Int )
--   >>> case r of R ( a :: Bool ) :*: _ -> a
--   True
--   >>> let !r' = R ( Field' True, Field' (undefined :: Int ) )
--   *** Exception: Prelude.undefined
--   ...
pattern Field' :: t -> Field 'Strict 'Nothing t
pattern Field' t <- (unField -> t) where
  Field' !t = MkField t

instance (KnownSymbol l, Show t) => Show (Field 'Lazy ('Just l) t) where
  show (l := t) = symbolVal l ++ " := " ++ show t

instance (KnownSymbol l, Show t) => Show (Field 'Strict ('Just l) t) where
  show (l :=! t) = symbolVal l ++ " :=! " ++ show t

instance Show t => Show (Field s 'Nothing t) where
  show (MkField t) = show t

type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

view :: Lens' s a -> s -> a
view l = getConst . l Const

instance l ~ l' => IsLabel (l :: Symbol) (Proxy l') where
  fromLabel _ = Proxy

-- | @(:!!) s l a@ says that the record @s@ has a field of type @a@ at index @l@, and provides a @Lens' s a@ to get/set that particular field.
--
--   If you are thinking that the syntax is ugly, we can use the utility operator `:~` to write @a :~ (s :!! l)@ which can be read as the equality constraint @a ~ (s !! t)@. Nice!
--
class (:!!) s (l :: Symbol) a | s l -> a where
  fieldLens :: Lens' s a

-- $records
-- A record is internally represented as a data family indexed by a list of 'Field':
--
-- >  data    family   Rec (xs :: [*])
-- >  data    instance Rec '[] = R0
-- >  newtype instance Rec '[Field s0 l0 t0] = R1 (Field s0 l0 t0)
-- >  data    instance Rec '[Field s0 l0 t0, Field s1 l1 t1] = R2 {-# UNPACK #-} !(Field s0 l0 t0) {-# UNPACK #-} !(Field s1 l1 t1)
-- >  ...
--
-- The @UNPACK@ pragmas ensure that a 'Field''s constructor is erased at runtime, thus the following record:
--
-- >  Rec '[ "a" := Int, "b" := Bool, "c" := String ]
--
-- has the same memory footprint as:
--
-- >  (Int, Bool, String)
--
-- or:
--
-- >  data Foo = Foo { a :: Int, b :: Bool, c :: String }
--
-- Note: See test-suite "datasize".
--
-- A record can be either:
--
--   * A labeled record: All of its fields are labeled and sorted using `CmpSymbol`.
--
--   * An unlabeled record: All fields are unlabeled and indexed by their positions. If all fields are lazy, they are isomorphic to Haskell tuples.
--
-- Mixing labeled and unlabeled fields isn't prohibited. This is enforced by the library's smart constructors.
--
-- 'Eq', 'Ord', 'Show', 'Monoid', 'NFData' instances are provided if all of the fields are also instances of respective classes.
--
-- Currently, records with up to 8 fields are supported.

data    family   Rec (xs :: [*])
data    instance Rec '[] = R0
newtype instance Rec '[ Field s0 l0 t0 ] = R1 (Field s0 l0 t0)
data    instance Rec '[ Field s0 l0 t0 , Field s1 l1 t1 ] =
  R2 {-# UNPACK #-} !(Field s0 l0 t0) {-# UNPACK #-} !(Field s1 l1 t1)
data    instance Rec '[ Field s0 l0 t0 , Field s1 l1 t1 , Field s2 l2 t2 ] =
  R3 {-# UNPACK #-} !(Field s0 l0 t0) {-# UNPACK #-} !(Field s1 l1 t1) {-# UNPACK #-} !(Field s2 l2 t2)
data    instance Rec '[ Field s0 l0 t0 , Field s1 l1 t1 , Field s2 l2 t2 , Field s3 l3 t3 ] =
  R4 {-# UNPACK #-} !(Field s0 l0 t0) {-# UNPACK #-} !(Field s1 l1 t1) {-# UNPACK #-} !(Field s2 l2 t2) {-# UNPACK #-} !(Field s3 l3 t3)
data    instance Rec '[ Field s0 l0 t0 , Field s1 l1 t1 , Field s2 l2 t2 , Field s3 l3 t3 , Field s4 l4 t4 ] =
  R5 {-# UNPACK #-} !(Field s0 l0 t0) {-# UNPACK #-} !(Field s1 l1 t1) {-# UNPACK #-} !(Field s2 l2 t2) {-# UNPACK #-} !(Field s3 l3 t3) {-# UNPACK #-} !(Field s4 l4 t4)
data    instance Rec '[ Field s0 l0 t0 , Field s1 l1 t1 , Field s2 l2 t2 , Field s3 l3 t3 , Field s4 l4 t4 , Field s5 l5 t5 ] =
  R6 {-# UNPACK #-} !(Field s0 l0 t0) {-# UNPACK #-} !(Field s1 l1 t1) {-# UNPACK #-} !(Field s2 l2 t2) {-# UNPACK #-} !(Field s3 l3 t3) {-# UNPACK #-} !(Field s4 l4 t4) {-# UNPACK #-} !(Field s5 l5 t5)
data    instance Rec '[ Field s0 l0 t0 , Field s1 l1 t1 , Field s2 l2 t2 , Field s3 l3 t3 , Field s4 l4 t4 , Field s5 l5 t5 , Field s6 l6 t6 ] =
  R7 {-# UNPACK #-} !(Field s0 l0 t0) {-# UNPACK #-} !(Field s1 l1 t1) {-# UNPACK #-} !(Field s2 l2 t2) {-# UNPACK #-} !(Field s3 l3 t3) {-# UNPACK #-} !(Field s4 l4 t4) {-# UNPACK #-} !(Field s5 l5 t5) {-# UNPACK #-} !(Field s6 l6 t6)
data    instance Rec '[ Field s0 l0 t0 , Field s1 l1 t1 , Field s2 l2 t2 , Field s3 l3 t3 , Field s4 l4 t4 , Field s5 l5 t5 , Field s6 l6 t6 , Field s7 l7 t7 ] =
  R8 {-# UNPACK #-} !(Field s0 l0 t0) {-# UNPACK #-} !(Field s1 l1 t1) {-# UNPACK #-} !(Field s2 l2 t2) {-# UNPACK #-} !(Field s3 l3 t3) {-# UNPACK #-} !(Field s4 l4 t4) {-# UNPACK #-} !(Field s5 l5 t5) {-# UNPACK #-} !(Field s6 l6 t6) {-# UNPACK #-} !(Field s7 l7 t7)

$(
  return $ do
    let s = VarT (mkName "s")
        l = VarT (mkName "l")
        t = VarT (mkName "t")
        mkField s' l' t' = ConT ''Field  `AppT` s' `AppT` (ConT 'Just `AppT` l') `AppT` t'
        fieldslt = mkField s l t
        f = mkName "f"
        x = mkName "x"
        x' = mkName "x'"
        cxt = [ConT ''WrapInField `AppT` t `AppT` fieldslt]
    n :: Integer <- [1 .. 8]
    i <- [1 .. n]
    let recList = [ if i == i' then fieldslt else mkField (VarT (mkName ("s" ++ show i'))) (VarT (mkName ("l" ++ show i'))) (VarT (mkName ("t" ++ show i'))) | i' <- [1 .. n] ]
        recTy = ConT ''Rec `AppT` foldr (\t ts -> (PromotedConsT `AppT` t) `AppT` ts) PromotedNilT recList
        ty = ConT ''(:!!) `AppT` recTy `AppT` l `AppT` t
        rPat = ConP (mkName ("R" ++ show n)) [ if i == i' then ConP 'MkField [VarP x] else VarP (mkName ("_" ++ show i')) | i' <- [1 .. n] ]
        rExp = foldl' AppE (ConE (mkName ("R" ++ show n))) [ if i == i' then AppE (VarE 'wrapInField) (VarE x') else VarE (mkName ("_" ++ show i')) | i' <- [1 .. n] ]
        body = NormalB $ UInfixE (LamE [VarP x'] rExp) (VarE '(<$>)) (VarE f `AppE` VarE x)
        fieldLensFn = FunD 'fieldLens [Clause [VarP (mkName "f"), rPat] body []]
    return $ InstanceD Nothing cxt ty [fieldLensFn]
 )

instance Show (Rec '[]) where
  show _ = "R ()"
instance Show (Field s0 l0 t0) => Show (Rec '[Field s0 l0 t0]) where
  show (R1 a) = "R ( " ++ show a ++ " )"
instance (Show (Field s0 l0 t0), Show (Field s1 l1 t1)) => Show (Rec '[Field s0 l0 t0, Field s1 l1 t1]) where
  show (R2 a b) = "R ( " ++ show a ++ ", " ++ show b ++ " )"
instance (Show (Field s0 l0 t0), Show (Field s1 l1 t1), Show (Field s2 l2 t2)) => Show (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2]) where
  show (R3 a b c) = "R ( " ++ show a ++ ", " ++ show b ++ ", " ++ show c ++ " )"
instance (Show (Field s0 l0 t0), Show (Field s1 l1 t1), Show (Field s2 l2 t2), Show (Field s3 l3 t3))
         => Show (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3]) where
  show (R4 a b c d) = "R ( " ++ show a ++ ", " ++ show b ++ ", " ++ show c ++ ", " ++ show d ++ " )"
instance (Show (Field s0 l0 t0), Show (Field s1 l1 t1), Show (Field s2 l2 t2), Show (Field s3 l3 t3), Show (Field s4 l4 t4))
         => Show (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4]) where
  show (R5 a b c d e) = "R ( " ++ show a ++ ", " ++ show b ++ ", " ++ show c ++ ", " ++ show d ++ ", " ++ show e ++ " )"
instance (Show (Field s0 l0 t0), Show (Field s1 l1 t1), Show (Field s2 l2 t2), Show (Field s3 l3 t3), Show (Field s4 l4 t4), Show (Field s5 l5 t5))
         => Show (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5]) where
  show (R6 a b c d e f) = "R ( " ++ show a ++ ", " ++ show b ++ ", " ++ show c ++ ", " ++ show d ++ ", " ++ show e ++ ", " ++ show f ++ " )"
instance (Show (Field s0 l0 t0), Show (Field s1 l1 t1), Show (Field s2 l2 t2), Show (Field s3 l3 t3), Show (Field s4 l4 t4), Show (Field s5 l5 t5), Show (Field s6 l6 t6))
         => Show (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6]) where
  show (R7 a b c d e f g) = "R ( " ++ show a ++ ", " ++ show b ++ ", " ++ show c ++ ", " ++ show d ++ ", " ++ show e ++ ", " ++ show f ++ ", " ++ show g ++ " )"
instance (Show (Field s0 l0 t0), Show (Field s1 l1 t1), Show (Field s2 l2 t2), Show (Field s3 l3 t3), Show (Field s4 l4 t4), Show (Field s5 l5 t5), Show (Field s6 l6 t6), Show (Field s7 l7 t7))
         => Show (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7]) where
  show (R8 a b c d e f g h) = "R ( " ++ show a ++ ", " ++ show b ++ ", " ++ show c ++ ", " ++ show d ++ ", " ++ show e ++ ", " ++ show f ++ ", " ++ show g ++ ", " ++ show h ++ " )"

deriving instance Eq (Rec '[])
deriving instance (Eq t0) => Eq (Rec '[Field s0 l0 t0])
deriving instance (Eq t0, Eq t1) => Eq (Rec '[Field s0 l0 t0, Field s1 l1 t1])
deriving instance (Eq t0, Eq t1, Eq t2) => Eq (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2])
deriving instance (Eq t0, Eq t1, Eq t2, Eq t3) => Eq (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3])
deriving instance (Eq t0, Eq t1, Eq t2, Eq t3, Eq t4) => Eq (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4])
deriving instance (Eq t0, Eq t1, Eq t2, Eq t3, Eq t4, Eq t5) => Eq (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5])
deriving instance (Eq t0, Eq t1, Eq t2, Eq t3, Eq t4, Eq t5, Eq t6) => Eq (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6])
deriving instance (Eq t0, Eq t1, Eq t2, Eq t3, Eq t4, Eq t5, Eq t6, Eq t7) => Eq (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7])

deriving instance Ord (Rec '[])
deriving instance (Ord t0) => Ord (Rec '[Field s0 l0 t0])
deriving instance (Ord t0, Ord t1) => Ord (Rec '[Field s0 l0 t0, Field s1 l1 t1])
deriving instance (Ord t0, Ord t1, Ord t2) => Ord (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2])
deriving instance (Ord t0, Ord t1, Ord t2, Ord t3) => Ord (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3])
deriving instance (Ord t0, Ord t1, Ord t2, Ord t3, Ord t4) => Ord (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4])
deriving instance (Ord t0, Ord t1, Ord t2, Ord t3, Ord t4, Ord t5) => Ord (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5])
deriving instance (Ord t0, Ord t1, Ord t2, Ord t3, Ord t4, Ord t5, Ord t6) => Ord (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6])
deriving instance (Ord t0, Ord t1, Ord t2, Ord t3, Ord t4, Ord t5, Ord t6, Ord t7) => Ord (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7])

instance NFData (Rec '[]) where
  {-# INLINE rnf #-}
  rnf R0 = ()

instance (NFData t0) => NFData (Rec '[Field s0 l0 t0]) where
  {-# INLINE rnf #-}
  rnf (R1 a) = rnf a

instance (NFData t0, NFData t1) => NFData (Rec '[Field s0 l0 t0, Field s1 l1 t1]) where
  {-# INLINE rnf #-}
  rnf (R2 a b) = rnf a `seq` rnf b

instance (NFData t0, NFData t1, NFData t2) => NFData (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2]) where
  {-# INLINE rnf #-}
  rnf (R3 a b c) = rnf a `seq` rnf b `seq` rnf c

instance (NFData t0, NFData t1, NFData t2, NFData t3) => NFData (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3]) where
  {-# INLINE rnf #-}
  rnf (R4 a b c d) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d

instance (NFData t0, NFData t1, NFData t2, NFData t3, NFData t4) => NFData (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4]) where
  {-# INLINE rnf #-}
  rnf (R5 a b c d e) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e

instance (NFData t0, NFData t1, NFData t2, NFData t3, NFData t4, NFData t5) => NFData (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5]) where
  {-# INLINE rnf #-}
  rnf (R6 a b c d e f) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e `seq` rnf f

instance (NFData t0, NFData t1, NFData t2, NFData t3, NFData t4, NFData t5, NFData t6)
         => NFData (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6]) where
  {-# INLINE rnf #-}
  rnf (R7 a b c d e f g) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e `seq` rnf f `seq` rnf g

instance (NFData t0, NFData t1, NFData t2, NFData t3, NFData t4, NFData t5, NFData t6, NFData t7)
         => NFData (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7]) where
  {-# INLINE rnf #-}
  rnf (R8 a b c d e f g h) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e `seq` rnf f `seq` rnf g `seq` rnf h

instance Monoid (Rec '[]) where
  mempty = R0
  _ `mappend` _ = R0

instance (Monoid t0) => Monoid (Rec '[Field s0 l0 t0]) where
  mempty = R1 mempty
  R1 a `mappend` R1 a' = R1 (a `mappend` a')

instance (Monoid t0, Monoid t1) => Monoid (Rec '[Field s0 l0 t0, Field s1 l1 t1]) where
  mempty = R2 mempty mempty
  R2 a b `mappend` R2 a' b' = R2 (a `mappend` a') (b `mappend` b')

instance (Monoid t0, Monoid t1, Monoid t2) => Monoid (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2]) where
  mempty = R3 mempty mempty mempty
  R3 a b c `mappend` R3 a' b' c' = R3 (a `mappend` a') (b `mappend` b') (c `mappend` c')

instance (Monoid t0, Monoid t1, Monoid t2, Monoid t3) => Monoid (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3]) where
  mempty = R4 mempty mempty mempty mempty
  R4 a b c d `mappend` R4 a' b' c' d' = R4 (a `mappend` a') (b `mappend` b') (c `mappend` c') (d `mappend` d')

instance (Monoid t0, Monoid t1, Monoid t2, Monoid t3, Monoid t4) => Monoid (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4]) where
  mempty = R5 mempty mempty mempty mempty mempty
  R5 a b c d e `mappend` R5 a' b' c' d' e' = R5 (a `mappend` a') (b `mappend` b') (c `mappend` c') (d `mappend` d') (e `mappend` e')

instance (Monoid t0, Monoid t1, Monoid t2, Monoid t3, Monoid t4, Monoid t5) =>
         Monoid (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5]) where
  mempty = R6 mempty mempty mempty mempty mempty mempty
  R6 a b c d e f `mappend` R6 a' b' c' d' e' f' = R6 (a `mappend` a') (b `mappend` b') (c `mappend` c') (d `mappend` d') (e `mappend` e') (f `mappend` f')

instance (Monoid t0, Monoid t1, Monoid t2, Monoid t3, Monoid t4, Monoid t5, Monoid t6) =>
         Monoid (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6]) where
  mempty = R7 mempty mempty mempty mempty mempty mempty mempty
  R7 a b c d e f g `mappend` R7 a' b' c' d' e' f' g' = R7 (a `mappend` a') (b `mappend` b') (c `mappend` c') (d `mappend` d') (e `mappend` e') (f `mappend` f') (g `mappend` g')

instance (Monoid t0, Monoid t1, Monoid t2, Monoid t3, Monoid t4, Monoid t5, Monoid t6, Monoid t7) =>
         Monoid (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7]) where
  mempty = R8 mempty mempty mempty mempty mempty mempty mempty mempty
  R8 a b c d e f g h `mappend` R8 a' b' c' d' e' f' g' h' = R8 (a `mappend` a') (b `mappend` b') (c `mappend` c') (d `mappend` d') (e `mappend` e') (f `mappend` f') (g `mappend` g') (h `mappend` h')

instance {-# OVERLAPPABLE #-}
         ( a ~ TypeError (Text "Label " :<>: ShowType l :<>: Text " does not occur in " :<>: PPRec s)
         ) => (:!!) s l a where
  fieldLens = undefined

-- Need s2fs ~ (s -> f s) for better type inference
instance {-# OVERLAPPING #-} (a :~ s :!! l, Functor f, a ~ b, s2fs ~ (s -> f s)) => IsLabel (l :: Symbol) ((a -> f b) -> s2fs) where
  fromLabel _ = fieldLens @s @l

instance {-# OVERLAPPING #-} (a :~ Rec xs :!! l) => IsLabel (l :: Symbol) (Rec xs -> a) where
  fromLabel _ = view (fieldLens @(Rec xs) @l)

type family ToField (a :: *) = (r :: *) where
  ToField (Field s l t) = Field s l t
  ToField a = Field 'Lazy 'Nothing a

class (r ~ ToField a) => ToFieldImpl (a :: *) (r :: *) | a -> r where
  toField :: a -> r

instance {-# OVERLAPPING #-} (r ~ Field s l t) => ToFieldImpl (Field s l t) r where
  toField = id

instance {-# OVERLAPPING #-} (r ~ Field 'Lazy 'Nothing a, r ~ ToField a) => ToFieldImpl a r where
  toField = Field

-- | 'R' takes a tuple, where each non-`Field` element @a@ is wrapped as a lazy non-labeled field @Field ''Lazy' ''Nothing' t@, and performs a merge-sort using `:*:` if the fields are labeled.
--
--   >>> :kind! R ( "foo" := Bool , "bar" := Int )
--   R ( "foo" := Bool , "bar" := Int ) :: *
--   = Rec
--       '[Field 'Lazy ('Just "bar") Int, Field 'Lazy ('Just "foo") Bool]
--
--   >>> :kind! R (Int, Bool)
--   R (Int, Bool) :: *
--   = Rec '[Field 'Lazy 'Nothing Int, Field 'Lazy 'Nothing Bool]
--
--   GHC should be capable of inlining most of the label-sorting away, therefore the following expression:
--
--   >  R ( #e := (), #d := (), #c := (), #b := (), #a := () )
--
--   should have similar performance as:
--
--   >  (\(e, d, c, b, a) -> (a, b, c, d, e)) ( #e := (), #d := (), #c := (), #b := (), #a := () )
--
--   Matching a field that does not occur in the record is an error:
--
--   >>> case R () of R ( _ :: "a" := Int ) -> ()
--   <BLANKLINE>
--   ... error:
--   ... Label "a" does not occur in R ()
--   ...
--
type family R (t :: *) = (r :: *) where
  R () = Rec '[]
  R (a, b) = Rec '[ToField a] :*: Rec '[ToField b]
  R (a, b, c) = Rec '[ToField a] :*: (Rec '[ToField b] :*: Rec '[ToField c])
  R (a, b, c, d) = (Rec '[ToField a] :*: Rec '[ToField b]) :*: (Rec '[ToField c] :*: Rec '[ToField d])
  R (a, b, c, d, e) = (Rec '[ToField a] :*: Rec '[ToField b]) :*: (Rec '[ToField c] :*: (Rec '[ToField d] :*: Rec '[ToField e]))
  R (a, b, c, d, e, f) = (Rec '[ToField a] :*: (Rec '[ToField b] :*: Rec '[ToField c])) :*: (Rec '[ToField d] :*: (Rec '[ToField e] :*: Rec '[ToField f]))
  R (a, b, c, d, e, f, g) = (Rec '[ToField a] :*: (Rec '[ToField b] :*: Rec '[ToField c])) :*: ((Rec '[ToField d] :*: Rec '[ToField e]) :*: (Rec '[ToField f] :*: Rec '[ToField g]))
  R (a, b, c, d, e, f, g, h) = ((Rec '[ToField a] :*: Rec '[ToField b]) :*: (Rec '[ToField c] :*: Rec '[ToField d])) :*: ((Rec '[ToField e] :*: Rec '[ToField f]) :*: (Rec '[ToField g] :*: Rec '[ToField h]))
  R a = Rec '[ToField a]

class (r ~ R t) => RImpl (t :: *) (r :: *) | t -> r where
  toR :: t -> r

instance {-# OVERLAPPING #-} (r ~ Rec '[]) => RImpl () r where
  toR () = R0

instance {-# OVERLAPPING #-}
         ( Field s0 l0 t0 :~ ToFieldImpl a
         , r ~ Rec '[Field s0 l0 t0]
         , r ~ R a
         ) => RImpl a r where
  {-# INLINE toR #-}
  toR (toField -> a) = R1 a

instance {-# OVERLAPPING #-}
         ( Field s0 l0 t0 :~ ToFieldImpl a
         , Field s1 l1 t1 :~ ToFieldImpl b
         , r :~ RecMergeImpl (Rec '[Field s0 l0 t0]) (Rec '[Field s1 l1 t1])
         , r ~ R (a, b)
         ) => RImpl (a, b) r where
  {-# INLINE toR #-}
  toR (toField -> a, toField -> b) = R1 a `recMerge` R1 b

instance {-# OVERLAPPING #-}
         ( Field s0 l0 t0 :~ ToFieldImpl a
         , Field s1 l1 t1 :~ ToFieldImpl b
         , Field s2 l2 t2 :~ ToFieldImpl c
         , rr :~ RecMergeImpl (Rec '[Field s1 l1 t1]) (Rec '[Field s2 l2 t2])
         , r :~ RecMergeImpl (Rec '[Field s0 l0 t0]) rr
         , r ~ R (a, b, c)
         ) => RImpl (a, b, c) r where
  {-# INLINE toR #-}
  toR (toField -> a, toField -> b, toField -> c) = R1 a `recMerge` (R1 b `recMerge` R1 c)

instance {-# OVERLAPPING #-}
         ( Field s0 l0 t0 :~ ToFieldImpl a
         , Field s1 l1 t1 :~ ToFieldImpl b
         , Field s2 l2 t2 :~ ToFieldImpl c
         , Field s3 l3 t3 :~ ToFieldImpl d
         , rl :~ RecMergeImpl (Rec '[Field s0 l0 t0]) (Rec '[Field s1 l1 t1])
         , rr :~ RecMergeImpl (Rec '[Field s2 l2 t2]) (Rec '[Field s3 l3 t3])
         , r :~ RecMergeImpl rl rr
         , r ~ R (a, b, c, d)
         ) => RImpl (a, b, c, d) r where
  {-# INLINE toR #-}
  toR (toField -> a, toField -> b, toField -> c, toField -> d) = (R1 a `recMerge` R1 b) `recMerge` (R1 c `recMerge` R1 d)

instance {-# OVERLAPPING #-}
         ( Field s0 l0 t0 :~ ToFieldImpl a
         , Field s1 l1 t1 :~ ToFieldImpl b
         , Field s2 l2 t2 :~ ToFieldImpl c
         , Field s3 l3 t3 :~ ToFieldImpl d
         , Field s4 l4 t4 :~ ToFieldImpl e
         , rl :~ RecMergeImpl (Rec '[Field s0 l0 t0]) (Rec '[Field s1 l1 t1])
         , rrr :~ RecMergeImpl (Rec '[Field s3 l3 t3]) (Rec '[Field s4 l4 t4])
         , rr :~ RecMergeImpl (Rec '[Field s2 l2 t2]) rrr
         , r :~ RecMergeImpl rl rr
         , r ~ R (a, b, c, d, e)
         ) => RImpl (a, b, c, d, e) r where
  {-# INLINE toR #-}
  toR (toField -> a, toField -> b, toField -> c, toField -> d, toField -> e) = (R1 a `recMerge` R1 b) `recMerge` (R1 c `recMerge` (R1 d `recMerge` R1 e))

instance {-# OVERLAPPING #-}
         ( Field s0 l0 t0 :~ ToFieldImpl a
         , Field s1 l1 t1 :~ ToFieldImpl b
         , Field s2 l2 t2 :~ ToFieldImpl c
         , Field s3 l3 t3 :~ ToFieldImpl d
         , Field s4 l4 t4 :~ ToFieldImpl e
         , Field s5 l5 t5 :~ ToFieldImpl f
         , rlr :~ RecMergeImpl (Rec '[Field s1 l1 t1]) (Rec '[Field s2 l2 t2])
         , rl :~ RecMergeImpl (Rec '[Field s0 l0 t0]) rlr
         , rrr :~ RecMergeImpl (Rec '[Field s4 l4 t4]) (Rec '[Field s5 l5 t5])
         , rr :~ RecMergeImpl (Rec '[Field s3 l3 t3]) rrr
         , r :~ RecMergeImpl rl rr
         , r ~ R (a, b, c, d, e, f)
         ) => RImpl (a, b, c, d, e, f) r where
  {-# INLINE toR #-}
  toR (toField -> a, toField -> b, toField -> c, toField -> d, toField -> e, toField -> f) =
    (R1 a `recMerge` (R1 b `recMerge` R1 c)) `recMerge` (R1 d `recMerge` (R1 e `recMerge` R1 f))

instance {-# OVERLAPPING #-}
         ( Field s0 l0 t0 :~ ToFieldImpl a
         , Field s1 l1 t1 :~ ToFieldImpl b
         , Field s2 l2 t2 :~ ToFieldImpl c
         , Field s3 l3 t3 :~ ToFieldImpl d
         , Field s4 l4 t4 :~ ToFieldImpl e
         , Field s5 l5 t5 :~ ToFieldImpl f
         , Field s6 l6 t6 :~ ToFieldImpl g
         , rlr :~ RecMergeImpl (Rec '[Field s1 l1 t1]) (Rec '[Field s2 l2 t2])
         , rl :~ RecMergeImpl (Rec '[Field s0 l0 t0]) rlr
         , rrl :~ RecMergeImpl (Rec '[Field s3 l3 t3]) (Rec '[Field s4 l4 t4])
         , rrr :~ RecMergeImpl (Rec '[Field s5 l5 t5]) (Rec '[Field s6 l6 t6])
         , rr :~ RecMergeImpl rrl rrr
         , r :~ RecMergeImpl rl rr
         , r ~ R (a, b, c, d, e, f, g)
         ) => RImpl (a, b, c, d, e, f, g) r where
  {-# INLINE toR #-}
  toR (toField -> a, toField -> b, toField -> c, toField -> d, toField -> e, toField -> f, toField -> g) =
    (R1 a `recMerge` (R1 b `recMerge` R1 c)) `recMerge` ((R1 d `recMerge` R1 e) `recMerge` (R1 f `recMerge` R1 g))

instance {-# OVERLAPPING #-}
         ( Field s0 l0 t0 :~ ToFieldImpl a
         , Field s1 l1 t1 :~ ToFieldImpl b
         , Field s2 l2 t2 :~ ToFieldImpl c
         , Field s3 l3 t3 :~ ToFieldImpl d
         , Field s4 l4 t4 :~ ToFieldImpl e
         , Field s5 l5 t5 :~ ToFieldImpl f
         , Field s6 l6 t6 :~ ToFieldImpl g
         , Field s7 l7 t7 :~ ToFieldImpl h
         , rll :~ RecMergeImpl (Rec '[Field s0 l0 t0]) (Rec '[Field s1 l1 t1])
         , rlr :~ RecMergeImpl (Rec '[Field s2 l2 t2]) (Rec '[Field s3 l3 t3])
         , rl :~ RecMergeImpl rll rlr
         , rrl :~ RecMergeImpl (Rec '[Field s4 l4 t4]) (Rec '[Field s5 l5 t5])
         , rrr :~ RecMergeImpl (Rec '[Field s6 l6 t6]) (Rec '[Field s7 l7 t7])
         , rr :~ RecMergeImpl rrl rrr
         , r :~ RecMergeImpl rl rr
         , r ~ R (a, b, c, d, e, f, g, h)
         ) => RImpl (a, b, c, d, e, f, g, h) r where
  {-# INLINE toR #-}
  toR (toField -> a, toField -> b, toField -> c, toField -> d, toField -> e, toField -> f, toField -> g, toField -> h) =
    ((R1 a `recMerge` R1 b) `recMerge` (R1 c `recMerge` R1 d)) `recMerge` ((R1 e `recMerge` R1 f) `recMerge` (R1 g `recMerge` R1 h))

class UnRImpl r t where
  unR :: r -> t

instance UnRImpl r () where
  unR _ = ()

type ReWrap r s l t = ( t :~ r :!! l, Field s ('Just l) t :~ WrapInField t)

instance (ReWrap r s0 l0 t0) => UnRImpl r (Field s0 ('Just l0) t0) where
  unR r = wrapInField $ view (fieldLens @r @l0) r

instance (ReWrap r s0 l0 t0, ReWrap r s1 l1 t1) => UnRImpl r (Field s0 ('Just l0) t0, Field s1 ('Just l1) t1) where
  unR r = ( wrapInField $ view (fieldLens @r @l0) r
          , wrapInField $ view (fieldLens @r @l1) r
          )

instance (ReWrap r s0 l0 t0, ReWrap r s1 l1 t1, ReWrap r s2 l2 t2) => UnRImpl r (Field s0 ('Just l0) t0, Field s1 ('Just l1) t1, Field s2 ('Just l2) t2) where
  unR r = ( wrapInField $ view (fieldLens @r @l0) r
          , wrapInField $ view (fieldLens @r @l1) r
          , wrapInField $ view (fieldLens @r @l2) r
          )

instance (ReWrap r s0 l0 t0, ReWrap r s1 l1 t1, ReWrap r s2 l2 t2, ReWrap r s3 l3 t3)
         => UnRImpl r (Field s0 ('Just l0) t0, Field s1 ('Just l1) t1, Field s2 ('Just l2) t2, Field s3 ('Just l3) t3) where
  unR r = ( wrapInField $ view (fieldLens @r @l0) r
          , wrapInField $ view (fieldLens @r @l1) r
          , wrapInField $ view (fieldLens @r @l2) r
          , wrapInField $ view (fieldLens @r @l3) r
          )

instance (ReWrap r s0 l0 t0, ReWrap r s1 l1 t1, ReWrap r s2 l2 t2, ReWrap r s3 l3 t3, ReWrap r s4 l4 t4)
         => UnRImpl r (Field s0 ('Just l0) t0, Field s1 ('Just l1) t1, Field s2 ('Just l2) t2, Field s3 ('Just l3) t3, Field s4 ('Just l4) t4) where
  unR r = ( wrapInField $ view (fieldLens @r @l0) r
          , wrapInField $ view (fieldLens @r @l1) r
          , wrapInField $ view (fieldLens @r @l2) r
          , wrapInField $ view (fieldLens @r @l3) r
          , wrapInField $ view (fieldLens @r @l4) r
          )

instance (ReWrap r s0 l0 t0, ReWrap r s1 l1 t1, ReWrap r s2 l2 t2, ReWrap r s3 l3 t3, ReWrap r s4 l4 t4, ReWrap r s5 l5 t5)
         => UnRImpl r (Field s0 ('Just l0) t0, Field s1 ('Just l1) t1, Field s2 ('Just l2) t2, Field s3 ('Just l3) t3, Field s4 ('Just l4) t4, Field s5 ('Just l5) t5) where
  unR r = ( wrapInField $ view (fieldLens @r @l0) r
          , wrapInField $ view (fieldLens @r @l1) r
          , wrapInField $ view (fieldLens @r @l2) r
          , wrapInField $ view (fieldLens @r @l3) r
          , wrapInField $ view (fieldLens @r @l4) r
          , wrapInField $ view (fieldLens @r @l5) r
          )

instance (ReWrap r s0 l0 t0, ReWrap r s1 l1 t1, ReWrap r s2 l2 t2, ReWrap r s3 l3 t3, ReWrap r s4 l4 t4, ReWrap r s5 l5 t5, ReWrap r s6 l6 t6)
         => UnRImpl r (Field s0 ('Just l0) t0, Field s1 ('Just l1) t1, Field s2 ('Just l2) t2, Field s3 ('Just l3) t3, Field s4 ('Just l4) t4, Field s5 ('Just l5) t5, Field s6 ('Just l6) t6) where
  unR r = ( wrapInField $ view (fieldLens @r @l0) r
          , wrapInField $ view (fieldLens @r @l1) r
          , wrapInField $ view (fieldLens @r @l2) r
          , wrapInField $ view (fieldLens @r @l3) r
          , wrapInField $ view (fieldLens @r @l4) r
          , wrapInField $ view (fieldLens @r @l5) r
          , wrapInField $ view (fieldLens @r @l6) r
          )

instance (ReWrap r s0 l0 t0, ReWrap r s1 l1 t1, ReWrap r s2 l2 t2, ReWrap r s3 l3 t3, ReWrap r s4 l4 t4, ReWrap r s5 l5 t5, ReWrap r s6 l6 t6, ReWrap r s7 l7 t7)
         => UnRImpl r (Field s0 ('Just l0) t0, Field s1 ('Just l1) t1, Field s2 ('Just l2) t2, Field s3 ('Just l3) t3, Field s4 ('Just l4) t4, Field s5 ('Just l5) t5, Field s6 ('Just l6) t6, Field s7 ('Just l7) t7) where
  unR r = ( wrapInField $ view (fieldLens @r @l0) r
          , wrapInField $ view (fieldLens @r @l1) r
          , wrapInField $ view (fieldLens @r @l2) r
          , wrapInField $ view (fieldLens @r @l3) r
          , wrapInField $ view (fieldLens @r @l4) r
          , wrapInField $ view (fieldLens @r @l5) r
          , wrapInField $ view (fieldLens @r @l6) r
          , wrapInField $ view (fieldLens @r @l7) r
          )

instance UnRImpl (Rec '[Field s0 'Nothing t0]) t0 where
  unR (R1 (MkField a)) = a

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1]) (t0, t1) where
  unR (R2 (MkField a) (MkField b)) = (a, b)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2]) (t0, t1, t2) where
  unR (R3 (MkField a) (MkField b) (MkField c)) = (a, b, c)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3]) (t0, t1, t2, t3) where
  unR (R4 (MkField a) (MkField b) (MkField c) (MkField d)) = (a, b, c, d)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4])
                 (t0, t1, t2, t3, t4) where
  unR (R5 (MkField a) (MkField b) (MkField c) (MkField d) (MkField e)) = (a, b, c, d, e)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4, Field s5 'Nothing t5])
                 (t0, t1, t2, t3, t4, t5) where
  unR (R6 (MkField a) (MkField b) (MkField c) (MkField d) (MkField e) (MkField f)) = (a, b, c, d, e, f)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4, Field s5 'Nothing t5, Field s6 'Nothing t6])
                 (t0, t1, t2, t3, t4, t5, t6) where
  unR (R7 (MkField a) (MkField b) (MkField c) (MkField d) (MkField e) (MkField f) (MkField g)) = (a, b, c, d, e, f, g)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4, Field s5 'Nothing t5, Field s6 'Nothing t6, Field s7 'Nothing t7])
                 (t0, t1, t2, t3, t4, t5, t6, t7) where
  unR (R8 (MkField a) (MkField b) (MkField c) (MkField d) (MkField e) (MkField f) (MkField g) (MkField h)) = (a, b, c, d, e, f, g, h)

instance UnRImpl (Rec '[Field s0 'Nothing t0]) (Field s0 'Nothing t0) where
  unR (R1 a) = a

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1])
                       (Field s0 'Nothing t0, Field s1 'Nothing t1) where
  unR (R2 a b) = (a, b)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2])
                       (Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2) where
  unR (R3 a b c) = (a, b, c)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3])
                       (Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3) where
  unR (R4 a b c d) = (a, b, c, d)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4])
                       (Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4) where
  unR (R5 a b c d e) = (a, b, c, d, e)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4, Field s5 'Nothing t5])
                       (Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4, Field s5 'Nothing t5) where
  unR (R6 a b c d e f) = (a, b, c, d, e, f)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4, Field s5 'Nothing t5, Field s6 'Nothing t6])
                       (Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4, Field s5 'Nothing t5, Field s6 'Nothing t6) where
  unR (R7 a b c d e f g) = (a, b, c, d, e, f, g)

instance UnRImpl (Rec '[Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4, Field s5 'Nothing t5, Field s6 'Nothing t6, Field s7 'Nothing t7])
                       (Field s0 'Nothing t0, Field s1 'Nothing t1, Field s2 'Nothing t2, Field s3 'Nothing t3, Field s4 'Nothing t4, Field s5 'Nothing t5, Field s6 'Nothing t6, Field s7 'Nothing t7) where
  unR (R8 a b c d e f g h) = (a, b, c, d, e, f, g, h)

-- | When 'R' is used as a constructor, it is equivalent to the type family 'R', except that it operates at value-level.
--
--   As a pattern, 'R' destructs all fields of a record into a tuple of 'Field's. For labeled records, the 'Field's in the tuple may be in arbitrarily order.
pattern R :: (r :~ RImpl t, t :~ UnRImpl r) => t -> r
pattern R x <- (unR -> x) where
        R = toR

-- | Given a tuple of 'Field's, 'P' binds the matching fields from the record. (Note: Partial matching is only available for labeled records.)
pattern P :: (t :~ UnRImpl r) => t -> r
pattern P x <- (unR -> x)

type family RecHead (r :: *) :: * where
  RecHead (Rec '[a, b, c, d, e, f, g, h]) = a
  RecHead (Rec '[a, b, c, d, e, f, g]) = a
  RecHead (Rec '[a, b, c, d, e, f]) = a
  RecHead (Rec '[a, b, c, d, e]) = a
  RecHead (Rec '[a, b, c, d]) = a
  RecHead (Rec '[a, b, c]) = a
  RecHead (Rec '[a, b]) = a
  RecHead (Rec '[a]) = a

class (r ~ RecHead a) => RecHeadImpl a r | a -> r where
  recHead :: a -> r
instance RecHeadImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7]) (Field s0 l0 t0) where
  {-# INLINE recHead #-}
  recHead (R8 a _ _ _ _ _ _ _) = a
instance RecHeadImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6]) (Field s0 l0 t0) where
  {-# INLINE recHead #-}
  recHead (R7 a _ _ _ _ _ _) = a
instance RecHeadImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5]) (Field s0 l0 t0) where
  {-# INLINE recHead #-}
  recHead (R6 a _ _ _ _ _) = a
instance RecHeadImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4]) (Field s0 l0 t0) where
  {-# INLINE recHead #-}
  recHead (R5 a _ _ _ _) = a
instance RecHeadImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3]) (Field s0 l0 t0) where
  {-# INLINE recHead #-}
  recHead (R4 a _ _ _) = a
instance RecHeadImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2]) (Field s0 l0 t0) where
  {-# INLINE recHead #-}
  recHead (R3 a _ _) = a
instance RecHeadImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1]) (Field s0 l0 t0) where
  {-# INLINE recHead #-}
  recHead (R2 a _) = a
instance RecHeadImpl (Rec '[Field s0 l0 t0]) (Field s0 l0 t0) where
  {-# INLINE recHead #-}
  recHead (R1 a) = a


type family RecTail (r :: *) :: * where
  RecTail (Rec '[a, b, c, d, e, f, g, h]) = Rec '[b, c, d, e, f, g, h]
  RecTail (Rec '[a, b, c, d, e, f, g]) = Rec '[b, c, d, e, f, g]
  RecTail (Rec '[a, b, c, d, e, f]) = Rec '[b, c, d, e, f]
  RecTail (Rec '[a, b, c, d, e]) = Rec '[b, c, d, e]
  RecTail (Rec '[a, b, c, d]) = Rec '[b, c, d]
  RecTail (Rec '[a, b, c]) = Rec '[b, c]
  RecTail (Rec '[a, b]) = Rec '[b]
  RecTail (Rec '[a]) = Rec '[]

class (r ~ RecTail a) => RecTailImpl a r | a -> r where
  recTail :: a -> r
instance RecTailImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7])
                     (Rec '[Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7]) where
  {-# INLINE recTail #-}
  recTail (R8 _ b c d e f g h) = R7 b c d e f g h
instance RecTailImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6])
                     (Rec '[Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6]) where
  {-# INLINE recTail #-}
  recTail (R7 _ b c d e f g) = R6 b c d e f g
instance RecTailImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5])
                     (Rec '[Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5]) where
  {-# INLINE recTail #-}
  recTail (R6 _ b c d e f) = R5 b c d e f
instance RecTailImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4]) (Rec '[Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4]) where
  {-# INLINE recTail #-}
  recTail (R5 _ b c d e) = R4 b c d e
instance RecTailImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3]) (Rec '[Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3]) where
  {-# INLINE recTail #-}
  recTail (R4 _ b c d) = R3 b c d
instance RecTailImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2]) (Rec '[Field s1 l1 t1, Field s2 l2 t2]) where
  {-# INLINE recTail #-}
  recTail (R3 _ b c) = R2 b c
instance RecTailImpl (Rec '[Field s0 l0 t0, Field s1 l1 t1]) (Rec '[Field s1 l1 t1]) where
  {-# INLINE recTail #-}
  recTail (R2 _ b) = R1 b
instance RecTailImpl (Rec '[Field s0 l0 t0]) (Rec '[]) where
  {-# INLINE recTail #-}
  recTail (R1 _) = R0

-- UNSAFE! Internal usage only: `RecCons` doesn't respect the label ordering of a record.
type family RecCons (x :: *) (xs :: *) = (r :: *) | r -> x xs where
  RecCons a (Rec '[b, c, d, e, f, g, h]) = Rec '[a, b, c, d, e, f, g, h]
  RecCons a (Rec '[b, c, d, e, f, g]) = Rec '[a, b, c, d, e, f, g]
  RecCons a (Rec '[b, c, d, e, f]) = Rec '[a, b, c, d, e, f]
  RecCons a (Rec '[b, c, d, e]) = Rec '[a, b, c, d, e]
  RecCons a (Rec '[b, c, d]) = Rec '[a, b, c, d]
  RecCons a (Rec '[b, c]) = Rec '[a, b, c]
  RecCons a (Rec '[b]) = Rec '[a, b]
  RecCons a (Rec '[]) = Rec '[a]

class (r ~ RecCons x xs) => RecConsImpl x xs r | x xs -> r, r -> x xs where
  recCons :: x -> xs -> r
instance RecConsImpl (Field s0 l0 t0) (Rec '[Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7])
                     (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7]) where
  {-# INLINE recCons #-}
  recCons a (R7 b c d e f g h) = R8 a b c d e f g h
instance RecConsImpl (Field s0 l0 t0) (Rec '[Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6])
                     (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6]) where
  {-# INLINE recCons #-}
  recCons a (R6 b c d e f g) = R7 a b c d e f g
instance RecConsImpl (Field s0 l0 t0) (Rec '[Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5])
                     (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5]) where
  {-# INLINE recCons #-}
  recCons a (R5 b c d e f) = R6 a b c d e f
instance RecConsImpl (Field s0 l0 t0) (Rec '[Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4]) (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4]) where
  {-# INLINE recCons #-}
  recCons a (R4 b c d e) = R5 a b c d e
instance RecConsImpl (Field s0 l0 t0) (Rec '[Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3]) (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3]) where
  {-# INLINE recCons #-}
  recCons a (R3 b c d) = R4 a b c d
instance RecConsImpl (Field s0 l0 t0) (Rec '[Field s1 l1 t1, Field s2 l2 t2]) (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2]) where
  {-# INLINE recCons #-}
  recCons a (R2 b c) = R3 a b c
instance RecConsImpl (Field s0 l0 t0) (Rec '[Field s1 l1 t1]) (Rec '[Field s0 l0 t0, Field s1 l1 t1]) where
  {-# INLINE recCons #-}
  recCons a (R1 b) = R2 a b
instance RecConsImpl (Field s0 l0 t0) (Rec '[]) (Rec '[Field s0 l0 t0]) where
  {-# INLINE recCons #-}
  recCons a R0 = R1 a

type family RecMerge (xs :: *) (ys :: *) = (r :: *) where
  RecMerge (Rec '[]) (Rec ys) = Rec ys
  RecMerge (Rec xs) (Rec '[]) = Rec xs
  RecMerge (Rec (Field sx ('Just lx) tx ': xs)) (Rec (Field sy ('Just ly) ty ': ys)) = RecMerge' (CmpSymbol lx ly) (Rec (Field sx ('Just lx) tx ': xs)) (Rec (Field sy ('Just ly) ty ': ys))
  RecMerge (Rec (Field sx ('Just lx) tx ': xs)) (Rec (Field sy 'Nothing ty ': ys)) = TypeError (Text "RecMerge: Cannot merge labeled and unlabeled fields")
  RecMerge (Rec (Field sx 'Nothing tx ': xs)) (Rec (Field sy ('Just l) ty ': ys)) = TypeError (Text "RecMerge: Cannot merge labeled and unlabeled fields")
  RecMerge (Rec (Field sx 'Nothing tx ': xs)) (Rec (Field sy 'Nothing ty ': ys)) = Field sx 'Nothing tx `RecCons` (Rec xs `RecMerge` Rec (Field sy 'Nothing ty ': ys))

class (r ~ RecMerge xs ys) => RecMergeImpl (xs :: *) (ys :: *) (r :: *) | xs ys -> r where
  recMerge :: xs -> ys -> r

instance RecMergeImpl (Rec '[]) (Rec ys) (Rec ys) where
  {-# INLINE recMerge #-}
  recMerge R0 ys = ys

instance RecMergeImpl (Rec xs) (Rec '[]) (Rec xs) where
  {-# INLINE recMerge #-}
  recMerge xs R0 = xs

instance ( r :~ RecMerge'Impl (CmpSymbol lx ly) (Rec (Field sx ('Just lx) tx ': xs)) (Rec (Field sy ('Just ly) ty ': ys))
         ) => RecMergeImpl (Rec (Field sx ('Just lx) tx ': xs)) (Rec (Field sy ('Just ly) ty ': ys)) r where
  {-# INLINE recMerge #-}
  recMerge = recMerge' @(CmpSymbol lx ly)

instance ( r ~ RecMerge (Rec (Field s ('Just l) t ': xs)) (Rec (Field sy 'Nothing ty ': ys))
         ) => RecMergeImpl (Rec (Field s ('Just l) t ': xs)) (Rec (Field sy 'Nothing ty ': ys)) r where
  recMerge = undefined

instance ( r ~ RecMerge (Rec (Field s 'Nothing t ': xs)) (Rec (Field s' ('Just l) t' ': ys))
         ) => RecMergeImpl (Rec (Field s 'Nothing t ': xs)) (Rec (Field s' ('Just l) t' ': ys)) r where
  recMerge = undefined

instance ( Field sx 'Nothing tx :~ RecHeadImpl (Rec (Field sx 'Nothing tx ': xs))
         , Rec xs :~ RecTailImpl (Rec (Field sx 'Nothing tx ': xs))
         , r' :~ RecMergeImpl (Rec xs) (Rec (Field sy 'Nothing ty ': ys))
         , r :~ RecConsImpl (Field sx 'Nothing tx) r'
         , r ~ RecMerge (Rec (Field sx 'Nothing tx ': xs)) (Rec (Field sy 'Nothing ty ': ys)) -- This shouldn't be needed.
         ) => RecMergeImpl (Rec (Field sx 'Nothing tx ': xs)) (Rec (Field sy 'Nothing ty ': ys)) r where
  {-# INLINE recMerge #-}
  recMerge xs ys = recHead xs `recCons` (recTail xs `recMerge` ys)

type family RecMerge' (ord :: Ordering) (xs :: *) (ys :: *) = (r :: *) where
  RecMerge' 'EQ (Rec (Field _ ('Just l) _ ': _)) _ = TypeError (Text "Duplicate labels " :<>: ShowType l)
  RecMerge' 'LT (Rec (Field sx lx tx ': xs)) ys = Field sx lx tx `RecCons` (Rec xs `RecMerge` ys)
  RecMerge' 'GT xs (Rec (Field sy ly ty ': ys)) = Field sy ly ty `RecCons` (xs `RecMerge` Rec ys)

class (r ~ RecMerge' ord xs ys) => RecMerge'Impl (ord :: Ordering) (xs :: *) (ys :: *) (r :: *) | ord xs ys -> r where
  recMerge' :: xs -> ys -> r

instance (r ~ RecMerge' 'EQ (Rec (Field sx l tx ': xs)) (Rec (Field sy l ty ': ys)))
         => RecMerge'Impl 'EQ (Rec (Field sx l tx ': xs)) (Rec (Field sy l ty ': ys)) r where
  recMerge' = undefined

instance ( Field sx lx tx :~ RecHeadImpl (Rec (Field sx lx tx ': xs))
         , Rec xs :~ RecTailImpl (Rec (Field sx lx tx ': xs))
         , merged :~ RecMergeImpl (Rec xs) ys
         , r :~ RecConsImpl (Field sx lx tx) merged
         ) => RecMerge'Impl 'LT (Rec (Field sx lx tx ': xs)) ys r where
  {-# INLINE recMerge' #-}
  recMerge' xs ys = recHead xs `recCons` (recTail xs `recMerge` ys)

instance ( Field sy ly ty :~ RecHeadImpl (Rec (Field sy ly ty ': ys))
         , Rec ys :~ RecTailImpl (Rec (Field sy ly ty ': ys))
         , merged :~ RecMergeImpl xs (Rec ys)
         , r :~ RecConsImpl (Field sy ly ty) merged
         ) => RecMerge'Impl 'GT xs (Rec (Field sy ly ty ': ys)) r where
  {-# INLINE recMerge' #-}
  recMerge' xs ys = recHead ys `recCons` (xs `recMerge` recTail ys)

type family RecConsFst (x :: *) (xs :: *) = (r :: *) | r -> x xs where
  RecConsFst x (Rec xs, Rec ys) = (x `RecCons` Rec xs, Rec ys)

class (r ~ RecConsFst x xs) => RecConsFstImpl (x :: *) (xs :: *) (r :: *) | x xs -> r, r -> x xs where
  recConsFst :: x -> xs -> r

instance ( Rec xs' :~ RecConsImpl x (Rec xs)
         , r ~ (Rec xs', Rec ys)
         ) => RecConsFstImpl x (Rec xs, Rec ys) r where
  {-# INLINE recConsFst #-}
  recConsFst x (xs, ys) = (x `recCons` xs, ys)

type family RecConsSnd (x :: *) (xs :: *) = (r :: *) | r -> x xs where
  RecConsSnd x (Rec xs, Rec ys) = (Rec xs, x `RecCons` Rec ys)

class (r ~ RecConsSnd x xs) => RecConsSndImpl (x :: *) (xs :: *) (r :: *) | x xs -> r, r -> x xs where
  recConsSnd :: x -> xs -> r

instance ( Rec ys' :~ RecConsImpl x (Rec ys)
         , r ~ (Rec xs, Rec ys')
         ) => RecConsSndImpl x (Rec xs, Rec ys) r where
  {-# INLINE recConsSnd #-}
  recConsSnd x (xs, ys) = (xs, x `recCons` ys)

type family RecPartition (ls :: [Maybe Symbol]) (xs :: *) = (r :: *) where
  RecPartition ('Nothing ': ls)  (Rec '[]) = TypeError (Text "RecPartition: Not enough fields in the record")
  RecPartition ('Just l ': ls) (Rec '[]) = TypeError (Text "RecPartition: Label " :<>: ShowType l :<>: Text " does not occur in the record")
  RecPartition '[] (Rec xs) = (Rec '[], Rec xs)
  RecPartition ('Just ly ': ls) (Rec (Field sx ('Just lx) tx ': xs)) = RecPartition' (CmpSymbol lx ly) ('Just ly ': ls) (Rec (Field sx ('Just lx) tx ': xs))
  RecPartition ('Nothing ': ls) (Rec (Field s 'Nothing t ': xs)) = RecConsFst (Field s 'Nothing t) (RecPartition ls (Rec xs))

type family RecPartition' (ord :: Ordering) (ls :: [Maybe Symbol]) (xs :: *) = (r :: *) where
  RecPartition' 'EQ (l ': ls) (Rec (Field s l t ': xs)) = Field s l t `RecConsFst` RecPartition ls (Rec xs)
  RecPartition' 'LT ls (Rec (Field s l t ': xs)) = Field s l t `RecConsSnd` RecPartition ls (Rec xs)
  RecPartition' 'GT ('Just l ': ls) (Rec xs) = TypeError (Text "RecPartition: Label " :<>: ShowType l :<>: Text " does not occur in the record")

class (r ~ RecPartition ls xs) => RecPartitionImpl (ls :: [Maybe Symbol]) (xs :: *) (r :: *) | ls xs -> r where
  recPartition :: xs -> r

instance (r ~ RecPartition ('Nothing ': ls)  (Rec '[])
         ) => RecPartitionImpl ('Nothing ': ls)  (Rec '[]) r where
  recPartition = undefined

instance (r ~ RecPartition ('Just l ': ls) (Rec '[])
         ) => RecPartitionImpl ('Just l ': ls) (Rec '[]) r where
  recPartition = undefined

instance RecPartitionImpl '[] (Rec xs) (Rec '[], Rec xs) where
  {-# INLINE recPartition #-}
  recPartition xs = (R0, xs)

instance ( r :~ RecPartition'Impl (CmpSymbol lx ly) ('Just ly ': ls) (Rec (Field sx ('Just lx) tx ': xs))
         ) => RecPartitionImpl ('Just ly ': ls) (Rec (Field sx ('Just lx) tx ': xs)) r where
  {-# INLINE recPartition #-}
  recPartition = recPartition' @(CmpSymbol lx ly) @('Just ly ': ls)

instance {-# OVERLAPPING #-}
         ( Field s 'Nothing t :~ RecHeadImpl (Rec (Field s 'Nothing t ': xs))
         , Rec xs :~ RecTailImpl (Rec (Field s 'Nothing t ': xs))
         , (Rec r0, Rec r1) :~ RecPartitionImpl ls (Rec xs)
         , r :~ RecConsFstImpl (Field s 'Nothing t) (Rec r0, Rec r1)
         ) => RecPartitionImpl ('Nothing ': ls) (Rec (Field s 'Nothing t ': xs)) r where
  {-# INLINE recPartition #-}
  recPartition xs = recConsFst (recHead xs) (recPartition @ls (recTail xs))

class (r ~ RecPartition' ord ls xs) => RecPartition'Impl (ord :: Ordering) (ls :: [Maybe Symbol]) (xs :: *) (r :: *) | ord ls xs -> r where
  recPartition' :: xs -> r

instance {-# OVERLAPPING #-}
         ( Field s l t :~ RecHeadImpl (Rec (Field s l t ': xs))
         , Rec xs :~ RecTailImpl (Rec (Field s l t ': xs))
         , (Rec r0, Rec r1) :~ RecPartitionImpl ls (Rec xs)
         , r :~ RecConsFstImpl (Field s l t) (Rec r0, Rec r1)
         ) => RecPartition'Impl 'EQ (l ': ls) (Rec (Field s l t ': xs)) r where
  {-# INLINE recPartition' #-}
  recPartition' xs = recHead xs `recConsFst` recPartition @ls (recTail xs)

instance ( Field s l t :~ RecHeadImpl (Rec (Field s l t ': xs))
         , Rec xs :~ RecTailImpl (Rec (Field s l t ': xs))
         , (Rec r0, Rec r1) :~ RecPartitionImpl ls (Rec xs)
         , r :~ RecConsSndImpl (Field s l t) (Rec r0, Rec r1)
         ) => RecPartition'Impl 'LT ls (Rec (Field s l t ': xs)) r where
  {-# INLINE recPartition' #-}
  recPartition' xs = recHead xs `recConsSnd` recPartition @ls (recTail xs)

instance (r ~ RecPartition' 'GT ('Just l ': ls) (Rec xs))
         => RecPartition'Impl 'GT ('Just l ': ls) (Rec xs) r where
  recPartition' = undefined

-- | Merge two records types.
--
--   >>> :kind! R ( "foo" := Int ) :*: R ( "bar" := Bool )
--   R ( "foo" := Int ) :*: R ( "bar" := Bool ) :: *
--   = Rec
--       '[Field 'Lazy ('Just "bar") Bool, Field 'Lazy ('Just "foo") Int]
--
--   >>> :kind! R ( Field 'Lazy 'Nothing Int ) :*: R ( Field 'Strict 'Nothing Bool )
--   R ( Field 'Lazy 'Nothing Int ) :*: R ( Field 'Strict 'Nothing Bool ) :: *
--   = Rec '[Field 'Lazy 'Nothing Int, Field 'Strict 'Nothing Bool]
type (:*:) x y = x `RecMerge` y
infixr 1 :*:

type family RecLabels (xs :: *) = (r :: [Maybe Symbol]) where
  RecLabels (Rec '[]) = '[]
  RecLabels (Rec (Field _ l _ ': xs)) = l ': RecLabels (Rec xs)

-- | A utility constraint for you to write signatures involving `:*:`. For example, the following function that deletes the field with label @a@ has the signature:
--
--   >>> :{
--          let f :: (r :~ R ( "a" := Int ) ::*: ys) => r -> ys
--              f (R ( _ :: "a" := Int) :*: ys) = ys
--       :}
class (r :~ RecMergeImpl xs ys, (xs, ys) :~ RecPartitionImpl (RecLabels xs) r) => (::*:) xs ys r
infix 1 ::*:
instance (r :~ RecMergeImpl xs ys, (xs, ys) :~ RecPartitionImpl (RecLabels xs) r) => (::*:) xs ys r

-- | === Constructor
--
--   Merge two records.
--
--   >>> R ( #foo := (1 :: Int) ) :*: R ( #bar := True )
--   R ( bar := True, foo := 1 )
--
--   >>> R ( 1 :: Int ) :*: R ( True )
--   R ( 1, True )
--
--   Merging labeled and unlabeled records is an error:
--
--   >>> R ( True ) :*: R ( #foo := True )
--   <BLANKLINE>
--   ... error:
--   ... RecMerge: Cannot merge labeled and unlabeled fields
--   ...
--
--   === Pattern
--
--   Partition a record based on the type of LHS.
--
--   >>> let r = R ( #a := (1 :: Int), #b := True, #c := "hello world" )
--   >>> case r of R ( _ := a :: "a" := Int, _ := c :: "c" := String ) :*: _ -> (a, c)
--   (1,"hello world")
--
--   This means that you can't write the above example as:
--
--   >>> case r of _ :*: R ( _ := a :: "a" := Int, _ := c :: "c" := String ) -> (a, c)
--   <BLANKLINE>
--   ... error:
--   ... Ambiguous type variable ‘...’ arising from a pattern
--   ...
--
--   Mismatches between the LHS and the record result in type errors:
--
--   >>> case R () of R ( _ :: "a" := Int ) :*: _ -> ()
--   <BLANKLINE>
--   ... error:
--   ... RecPartition: Label "a" does not occur in the record
--   ...
--
--   >>> case R () of R ( a :: Int ) :*: _ -> ()
--   <BLANKLINE>
--   ... error:
--   ... RecPartition: Not enough fields in the record
--   ...
--
--   >>> case R ( #a := True, #b := (1 :: Int) ) of R ( _ :: "a" := Int ) :*: _ -> ()
--   <BLANKLINE>
--   ... error:
--   ... Couldn't match type ‘Int’ with ‘Bool’ arising from a pattern
--   ...
--
--   >>> case R ( True, 1 :: Int ) of R ( a :: Int ) :*: _ -> ()
--   <BLANKLINE>
--   ... error:
--   ... Couldn't match type ‘Int’ with ‘Bool’ arising from a pattern
--   ...

pattern (:*:) :: forall xs ys r. (r :~ xs ::*: ys) => xs -> ys -> r
pattern (:*:) xs ys <- (recPartition @(RecLabels xs) -> (xs, ys)) where
        (:*:) xs ys = xs `recMerge` ys

type family PPRec (r :: *) = (e :: ErrorMessage) where
  PPRec (Rec '[]) = Text "R ()"
  PPRec (Rec '[Field s0 l0 t0]) =
    Text "R ( " :<>: PPField (Field s0 l0 t0) :<>: Text " )"
  PPRec (Rec '[Field s0 l0 t0, Field s1 l1 t1]) =
    Text "R ( " :<>: PPField (Field s0 l0 t0) :<>: Text ", " :<>: PPField (Field s1 l1 t1) :<>: Text " )"
  PPRec (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2]) =
    Text "R ( " :<>: PPField (Field s0 l0 t0) :<>: Text ", " :<>: PPField (Field s1 l1 t1) :<>: Text ", " :<>: PPField (Field s2 l2 t2) :<>: Text " )"
  PPRec (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3]) =
    Text "R ( " :<>: PPField (Field s0 l0 t0) :<>: Text ", " :<>: PPField (Field s1 l1 t1) :<>: Text ", " :<>: PPField (Field s2 l2 t2) :<>: Text ", " :<>: PPField (Field s3 l3 t3) :<>: Text " )"
  PPRec (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4]) =
    Text "R ( " :<>: PPField (Field s0 l0 t0) :<>: Text ", " :<>: PPField (Field s1 l1 t1) :<>: Text ", " :<>: PPField (Field s2 l2 t2) :<>: Text ", " :<>: PPField (Field s3 l3 t3) :<>: Text ", " :<>: PPField (Field s4 l4 t4) :<>: Text " )"
  PPRec (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5]) =
    Text "R ( " :<>: PPField (Field s0 l0 t0) :<>: Text ", " :<>: PPField (Field s1 l1 t1) :<>: Text ", " :<>: PPField (Field s2 l2 t2) :<>: Text ", " :<>: PPField (Field s3 l3 t3) :<>: Text ", " :<>: PPField (Field s4 l4 t4) :<>: Text ", " :<>: PPField (Field s5 l5 t5) :<>: Text " )"
  PPRec (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6]) =
    Text "R ( " :<>: PPField (Field s0 l0 t0) :<>: Text ", " :<>: PPField (Field s1 l1 t1) :<>: Text ", " :<>: PPField (Field s2 l2 t2) :<>: Text ", " :<>: PPField (Field s3 l3 t3) :<>: Text ", " :<>: PPField (Field s4 l4 t4) :<>: Text ", " :<>: PPField (Field s5 l5 t5) :<>: Text ", " :<>: PPField (Field s6 l6 t6) :<>: Text " )"
  PPRec (Rec '[Field s0 l0 t0, Field s1 l1 t1, Field s2 l2 t2, Field s3 l3 t3, Field s4 l4 t4, Field s5 l5 t5, Field s6 l6 t6, Field s7 l7 t7]) =
    Text "R ( " :<>: PPField (Field s0 l0 t0) :<>: Text ", " :<>: PPField (Field s1 l1 t1) :<>: Text ", " :<>: PPField (Field s2 l2 t2) :<>: Text ", " :<>: PPField (Field s3 l3 t3) :<>: Text ", " :<>: PPField (Field s4 l4 t4) :<>: Text ", " :<>: PPField (Field s5 l5 t5) :<>: Text ", " :<>: PPField (Field s6 l6 t6) :<>: Text ", " :<>: PPField (Field s7 l7 t7) :<>: Text " )"

type family PPField (r :: *) = (e :: ErrorMessage) where
  PPField (Field 'Lazy 'Nothing t) = ShowType t
  PPField (Field 'Strict 'Nothing t) = Text "!(" :<>: ShowType t :<>: Text ")"
  PPField (Field 'Lazy ('Just l) t) = ShowType l :<>: Text " := " :<>: ShowType t
  PPField (Field 'Strict ('Just l) t) = ShowType l :<>: Text " :=! " :<>: ShowType t

type (:<>:) x y = x ':<>: y
type Text x = 'Text x
type ShowType x = 'ShowType x
