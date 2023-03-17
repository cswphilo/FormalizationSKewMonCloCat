{-# OPTIONS --rewriting #-}
module Main where

-- Some basic facts aobut lists
import Utilities

-- Formulae
import Formulae1

-- Sequent calculus 
import SeqCalc1

-- Focused calculus
import Focusing1

-- Equivalent proofs in sequent calculus are identical in focused calculus
-- f ≗ g → focus f ≡ focus g
import Eqfocus

-- Every sequent calculus proof is equivalent with its normal form
-- emb-c (focus f) ≗ f
import Embfocus

-- -- Normal form of a focused proof is identical to itself
-- -- focus (emb-c f) ≡ f
import Focusemb