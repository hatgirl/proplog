{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module HW10 where

import Prelude (Show(..), Eq(..), ($), (.), flip)

modus_ponens :: (p -> q) -> p -> q
modus_ponens = ($)

-- Logical Disjunction
data p \/ q = Left p | Right q

-- Logical Conjunction
data p /\ q = Conj p q

data False

type Not p = p -> False
nnn
modus_tollens :: (p -> q) -> Not q -> Not p
modus_tollens pq not_q = not_q . pq

type p <-> q = ( p -> q ) /\ (q -> p)

admit :: assumption
admit = admit

excluded_middle :: p \/ Not p
excluded_middle = admit


absurd :: False -> p
absurd false = admit


double_negation :: p <-> Not (Not p)
double_negation = Conj (\p not_p -> not_p p) admit


material_implication :: (p -> q) <-> (Not p \/ q)
-- The proof has two parts, the forward direction (->) and
--   the backwards direction (<-)
material_implication = Conj dir1 dir2
    where 
      -- Case 1: (P -> Q) -> (~P \/ Q)
      dir1 p_imp_q =
          -- There are 2 cases, P and ~P
        case excluded_middle of
            -- SCase 1: P, then Q since P -> Q
            Left  p     -> Right $ p_imp_q p
            -- SCase 2: ~P, then ~P
            Right not_p -> Left not_p
      -- Case 2: (~P \/ Q) -> (P -> Q)
      -- SCase 1: ~P -> (P -> Q)
      dir2 (Left not_p) p =
          -- This is a contradiction since we have both
          -- P and ~P
          absurd $ not_p p
      -- SCase 2: Q -> (P -> Q)
      dir2 (Right q)    _ =
          -- q is a witness for the proposition Q,
          -- therefore we can just return it
          q


disjunctive_syllogism :: p \/ q -> Not p -> q
disjunctive_syllogism (Left p) not_p = absurd $ not_p p
disjunctive_syllogism (Right q) not_p = q  


composition :: (p -> q) \/ (p -> r) -> p -> (q \/ r)
composition (Left p_imp_q) p = Left (modus_ponens p_imp_q p)
composition (Right p_imp_r) p = Right (modus_ponens p_imp_r p)


reduce_double_negation :: Not (Not p) -> p
reduce_double_negation nnp = admit


add_double_negation :: p -> Not (Not p)
add_double_negation p = admit


transposition :: (p -> q) <-> (Not q -> Not p)
transposition = Conj forwd backwd
  where forwd p_imp_q = modus_tollens p_imp_q
        backwd nq_imp_np = reduce_double_negation . modus_tollens nq_imp_np . add_double_negation

{--
de_morgan :: Not (p \/ q) <-> (Not p /\ Not q)
de_morgan = Conj forwd backwd
  where forwd not_pvq = case p \/ q of
        Left p -> --}


