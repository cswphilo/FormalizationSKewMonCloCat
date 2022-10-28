{-# OPTIONS --rewriting #-}

module FocusEmb where

open import Data.Maybe
open import Data.List renaming (map to mapList; fromMaybe to backlist)
open import Data.List.Relation.Unary.Any
open import Data.List.Properties
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
-- open import Data.List.Relation.Binary.Permutation.Propositional renaming (trans to transiff; swap to swapiff)
-- open import Data.List.Relation.Binary.Permutation.Propositional.Properties 
open ≡-Reasoning
open import Data.Bool renaming (Bool to Tag; true to ∙; false to ∘)

open import Formulae
open import SeqCalc renaming (_∙_ to _≗∙_)
open import Focusing
open import Utilities renaming (++? to ++??)
open import IsInter 
open import Eqfocus

focusemb-c : {S : Stp} {Γ Δ : Cxt} {C : Fma}
           (f : S ∣ Γ ؛ Δ ⊢c C) → 
           focus (emb-c f) ≡ f
focusemb-c : {S : Stp} {Γ Δ : Cxt} {C : Fma}
           (f : ∙ ∣ S ∣ Γ ؛ Δ ⊢c C) → 
           focus (emb-c∙ f) ≡ f 
focusemb-ri : {S : Stp} {Γ : Cxt} {C : Fma}
           (f : S ∣ Γ ⊢ri C) → 
           focus (emb-ri f) ≡ f
focusemb-ri• : {S : Stp} {Γ Ω : Cxt} {C : Fma}
           (f : ∙ ∣ S ∣ Γ ؛ Ω ⊢ri C) → 
           focus (emb-ri• f) ≡ ri•2ri f
focusemb-li : {S : Stp} {Γ : Cxt} {C : Pos}
           (f : S ∣ Γ ⊢li C) → 
           focus (emb-li f) ≡ li2ri f
focusemb-p : {S : Irr} {Γ : Cxt} {C : Pos}
           (f : S ∣ Γ ⊢p C) → 
           focus (emb-p f) ≡ li2ri (p2li f)
focusemb-p• : {S : Irr} {Γ Ω : Cxt} {C : Pos}
           (f : ∙ ∣ S ∣ Γ ؛ Ω ⊢p C) → 
           focus (emb-p• f) ≡ li2ri (p2li (p•2p f))
focusemb-f : {S : Irr} {Γ : Cxt} {C : Pos}
           (f : S ∣ Γ ⊢f C) → 
           focus (emb-f f) ≡ li2ri (p2li (f2p f))
focusemb-f• : {S : Irr} {Γ Ω : Cxt} {C : Pos}
           (f : ∙ ∣ S ∣ Γ ؛ Ω ⊢f C) → 
           focus (emb-f• f) ≡ li2ri (p2li (f2p (f•2f f)))