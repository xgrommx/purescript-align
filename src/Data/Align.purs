module Data.Align where

import Prelude

import Data.Array (foldr)
import Data.Array as A
import Data.Bifoldable (class Bifoldable)
import Data.Bifunctor (class Bifunctor, bimap)
import Data.Compactable (class Compactable, compact)
import Data.Either (Either(..))
import Data.Foldable (class Foldable)
import Data.Identity (Identity(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.These (These(..), fromThese, mergeThese, these)
import Data.Tuple (Tuple(..), uncurry)
import Partial.Unsafe (unsafeCrashWith)

class Functor f <= Align f where
  nil :: forall a. f a
  align :: forall a b. f a -> f b -> f (These a b)
  alignWith :: forall a b c. (These a b -> c) -> f a -> f b -> f c

alignDefault :: forall f a b. Align f => f a -> f b -> f (These a b)
alignDefault = alignWith identity

alignWithDefault :: forall f a b c. Align f => (These a b -> c) -> f a -> f b -> f c
alignWithDefault f a b = f <$> align a b

instance alignMaybe :: Align Maybe where
  nil = Nothing
  align Nothing Nothing = Nothing
  align (Just a) Nothing = Just (This a)
  align Nothing (Just b) = Just (That b)
  align (Just a) (Just b) = Just (Both a b)
  alignWith f a b = alignWithDefault f a b

instance alignArray :: Align Array where
  nil = []
  align xs ys = case A.uncons xs, A.uncons ys of
    Nothing, Nothing -> []
    Just _, Nothing -> This <$> xs
    Nothing, Just _ -> That <$> ys
    Just r1, Just r2 -> Both r1.head r2.head A.: align r1.tail r2.tail
  alignWith f a b = alignWithDefault f a b

instance alignMap :: Ord k => Align (Map.Map k) where
  nil = Map.empty
  align m n = Map.unionWith merge (This <$> m) (That <$> n)
    where
      merge (This a) (That b) = Both a b
      merge _ _ = unsafeCrashWith "Align Map: merge"
  alignWith f a b = alignWithDefault f a b 

salign :: forall f a. Align f => Semigroup a => f a -> f a -> f a
salign = alignWith (mergeThese (<>))

padZip :: forall f a b. Align f => f a -> f b -> f (Tuple (Maybe a) (Maybe b))
padZip = alignWith (fromThese Nothing Nothing <<< bimap Just Just)

padZipWith :: forall f a b c. Align f => (Maybe a -> Maybe b -> c) -> f a -> f b -> f c
padZipWith f xs ys = uncurry f <$> padZip xs ys

lpadZipWith :: forall t a b c. Compactable t => Align t => (Maybe a -> b -> c) -> t a -> t b -> t c
lpadZipWith f xs ys = compact $ padZipWith (\x y -> f x <$> y) xs ys

lpadZip :: forall t a b. Compactable t => Align t => t a -> t b -> t (Tuple (Maybe a) b)
lpadZip = lpadZipWith Tuple

rpadZipWith :: forall t a b c. Compactable t => Align t => (a -> Maybe b -> c) -> t a -> t b -> t c
rpadZipWith f xs ys = lpadZipWith (flip f) ys xs

rpadZip :: forall t a b. Compactable t => Align t => t a -> t b -> t (Tuple a (Maybe b))
rpadZip = rpadZipWith Tuple

class Align f <= Unalign f where
  unalign :: forall a b. f (These a b) -> Tuple (f (Maybe a)) (f (Maybe b))

unalignDefault :: forall f a b. Unalign f => f (These a b) -> Tuple (f (Maybe a)) (f (Maybe b))
unalignDefault x = Tuple (left <$> x) (right <$> x)
  where
    left = these Just (const Nothing) (\a _ -> Just a)
    right = these (const Nothing) Just (\_ b -> Just b)

instance unalignMaybe :: Unalign Maybe where
  unalign x = unalignDefault x

instance unalignArray :: Unalign Array where
  unalign = foldr (these a b ab) (Tuple [] [])
    where
      a l (Tuple ls rs) = Tuple (Just l A.: ls) (Nothing A.: rs)
      b r (Tuple ls rs) = Tuple (Nothing A.: ls) (Just r A.: rs)
      ab l r (Tuple ls rs) = Tuple (Just l A.: ls) (Just r A.: rs)

class (Functor t, Foldable t) <= Crosswalk t where
  crosswalk :: forall f a b. Align f => (a -> f b) -> t a -> f (t b)
  sequenceL :: forall f a. Align f => t (f a) -> f (t a)

crosswalkDefault :: forall f t a b. Crosswalk t => Align f => (a -> f b) -> t a -> f (t b)     
crosswalkDefault f = sequenceL <<< map f 

sequenceLDefault :: forall f t a. Crosswalk t => Align f => t (f a) -> f (t a)
sequenceLDefault = crosswalk identity

instance crosswalkIdentity :: Crosswalk Identity where
  crosswalk f (Identity a) = map Identity (f a)
  sequenceL = sequenceLDefault

instance crosswalkMaybe :: Crosswalk Maybe where
  crosswalk _ Nothing = nil
  crosswalk f (Just a) = Just <$> f a
  sequenceL = sequenceLDefault

instance crosswalkArray :: Crosswalk Array where
  crosswalk f xss = case A.uncons xss of
    Nothing -> nil
    Just r -> alignWith (these pure identity (A.cons)) (f r.head) (crosswalk f r.tail)
  sequenceL = sequenceLDefault  

instance crosswalkThese :: Crosswalk (These a) where
  crosswalk _ (This _) = nil
  crosswalk f (That x) = That <$> f x
  crosswalk f (Both a x) = Both a <$> f x
  sequenceL = sequenceLDefault 

class (Bifunctor t, Bifoldable t) <= Bicrosswalk t where
  bicrosswalk :: forall f a b c d. Align f => (a -> f c) -> (b -> f d) -> t a b -> f (t c d)
  bisequenceL :: forall f a b. Align f => t (f a) (f b) -> f (t a b)

bicrosswalkDefault :: forall f t a b c d. Bicrosswalk t => Align f => (a -> f c) -> (b -> f d) -> t a b -> f (t c d)
bicrosswalkDefault f g = bisequenceL <<< bimap f g

bisequenceLDefault :: forall f t a b. Bicrosswalk t => Align f => t (f a) (f b) -> f (t a b)
bisequenceLDefault = bicrosswalk identity identity

instance bicrosswalkEither :: Bicrosswalk Either where
  bicrosswalk f _ (Left x)  = Left  <$> f x
  bicrosswalk _ g (Right x) = Right <$> g x
  bisequenceL = bisequenceLDefault

instance bicrosswalkThese :: Bicrosswalk These where
  bicrosswalk f _ (This x) = This <$> f x
  bicrosswalk _ g (That x) = That <$> g x
  bicrosswalk f g (Both x y) = align (f x) (g y)
  bisequenceL = bisequenceLDefault