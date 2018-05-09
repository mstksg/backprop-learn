{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module Data.Type.Util (
    pTake
  , pDrop
  , splitP
  , head_
  ) where

import           Data.Bifunctor
import           Data.Type.Combinator
import           Data.Type.Length
import           Data.Type.Product
import           Lens.Micro
import           Type.Family.List

splitP
    :: forall as bs f. ()
    => Length as
    -> Prod f (as ++ bs)
    -> (Prod f as, Prod f bs)
splitP = \case
    LZ   -> (Ø,)
    LS l -> \case
      x :< xs -> first (x :<) . splitP l $ xs

pTake
    :: forall as bs as' f. ()
    => Length as
    -> Lens (Prod f (as ++ bs)) (Prod f (as' ++ bs)) (Prod f as) (Prod f as')
pTake l f (splitP l->(xs,ys)) = flip (append' @_ @as' @bs) ys <$> f xs

pDrop
    :: forall as bs bs' f. ()
    => Length as
    -> Lens (Prod f (as ++ bs)) (Prod f (as ++ bs')) (Prod f bs) (Prod f bs')
pDrop l f (splitP l->(xs,ys)) = append' @_ @as @bs' xs <$> f ys

head_
    :: Tuple (a ': as)
    -> a
head_ (I x :< xs) = x

-- takeP
--     :: forall as bs f. ()
--     => Length as
--     -> Prod f (as ++ bs)
--     -> Prod f as
-- takeP = \case
--     LZ   -> const Ø
--     LS l -> \case
--       x :< xs -> x :< takeP @_ @bs l xs

-- dropP
--     :: forall as bs f. ()
--     => Length as
--     -> Prod f (as ++ bs)
--     -> Prod f bs
-- dropP = \case
--     LZ   -> id
--     LS l -> \case
--       x :< xs -> dropP l xs


