{-# OPTIONS --rewriting #-}

module Eqfocus where

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

-- focus function , maps each derivation in sequent calculus to focused calculus

focus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              S ∣ Γ ⊢ C → ∘ ∣ S ∣ Γ ؛ [] ⊢c C
focus ax = ax-c
focus (pass f) = pass-c (focus f)
focus Ir = Ir-c
focus (Il f) = Il-c (focus f)
focus (⊗l f) = ⊗l-c (focus f)
focus (⊗r f g) = ⊗r-c (focus f) (focus g)
focus (⊸l f g) = ⊸l-c (focus f) (focus g)
focus (⊸r f) = ⊸r-c (focus f)
focus (ex f) = ex-c _ (focus f)  


-- ===================
-- embedding

emb-c : {S : Stp} {Γ Δ : Cxt} {C : Fma} →
          S ∣ Γ ؛ Δ ⊢c C → S ∣ Γ ++ Δ ⊢ C
emb-c∙ : {S : Stp} {Γ Δ : TCxt} {C : Fma} →
       ∙ ∣ S ∣ Γ ؛ Δ ⊢c C → S ∣ ersL (Γ ++ Δ) ⊢ C
emb-ri : {S : Stp} {Γ : Cxt} {C : Fma} →
          S ∣ Γ ⊢ri C → S ∣ Γ ⊢ C
emb-ri∙ : {S : Stp} {Γ' : Cxt} {Γ : TCxt} {C : Fma} →
       ∙ ∣ S ∣ Γ ⊢ri C → (eq : Γ' ≡ ersL Γ) → S ∣ Γ' ⊢ C
emb-li : {S : Stp} {Γ : Cxt} {C : Pos} →
          S ∣ Γ ⊢li C → S ∣ Γ ⊢ pos C
emb-p : {S : Irr} {Γ : Cxt} {C : Pos} →
          S ∣ Γ ⊢p C → irr S ∣ Γ ⊢ pos C
emb-p∙ : {S : Irr} {Γ : TCxt} {C : Pos} →
       ∙ ∣ S ∣ Γ ⊢p C → irr S ∣ ersL Γ ⊢ pos C
emb-f : {S : Irr} {Γ : Cxt} {C : Pos} →
          S ∣ Γ ⊢f C → irr S ∣ Γ ⊢ pos C
emb-f∙ : {S : Irr} {Γ : TCxt} {C : Pos} →
       ∙ ∣ S ∣ Γ ⊢f C → irr S ∣ ersL Γ ⊢ pos C

emb-c (ex {Δ = Δ} f refl refl) = ex-cxt-fma Δ (emb-c f)
emb-c (ri2c f) = emb-ri f 

emb-c∙ (ex∙ {Δ = Δ} f refl refl) = ex-cxt-fma (ersL Δ) (emb-c∙ f)
emb-c∙ (ri2c f) = emb-ri∙ f refl

emb-ri {Γ = Γ} (⊸r f) = ⊸r (ex-fma-cxt {Γ = []} {Δ = []} Γ (emb-c f))
emb-ri (li2ri f) = emb-li f

emb-ri∙ {Γ = Γ} (⊸r∙ f) refl = ⊸r (ex-fma-cxt {Γ = []} {Δ = []} (ersL Γ) (emb-c∙ f))
emb-ri∙ (li2ri (p2li f)) refl = emb-p∙ f

emb-li (Il f) = Il (emb-li f)
emb-li (⊗l f) = ⊗l (emb-c f)
emb-li (p2li f) = emb-p f

emb-p (pass f) = pass (emb-li f)
emb-p (f2p f) = emb-f f

emb-p∙ (pass∙ f refl) = pass (emb-li f)
emb-p∙ (f2p f) = emb-f∙ f

emb-f ax = ax
emb-f Ir = Ir
emb-f {S} (⊗r {Γ = Γ} f g refl) = ⊗r (emb-ri∙ f (sym (tagErs Γ))) (emb-ri g)
emb-f (⊸l f g) = ⊸l (emb-ri f) (emb-li g)

emb-f∙ ax = ax
emb-f∙ Ir = Ir
emb-f∙ (⊗r∙ {Γ = Γ} {Δ = Δ} f g refl refl) = ⊗r (emb-ri∙ f (sym (whiteErs Γ))) (emb-ri g)
emb-f∙ (⊸l∙ f g refl refl refl) = ⊸l (emb-ri f) (emb-li g)

-- ̄≗ equivalent derivations are equal in focused calculus
⊸rpass-c' : {Ω Λ Λ₀ Λ₁ : Cxt} {A B C : Fma} 
    → (f : just A ∣ Ω ؛ Λ ⊢c C) (eq : Λ ≡ Λ₀ ++ B ∷ Λ₁)
    → ⊸r-c' (pass-c' f refl) eq ≡ pass-c' (⊸r-c' f eq) refl
⊸rpass-c : {Ω Γ Λ : Cxt} {A B C : Fma} 
    → (f : just A ∣ Ω ؛ Λ ⊢c C) (eq : Ω ≡ Γ ++ B ∷ [])
    → ⊸r-c'' (pass-c f) (cong (_ ∷_) eq) ≡ pass-c (⊸r-c'' f eq)

⊸rpass-c' {Λ₀ = Λ₀} {Λ₁} (ex {Δ = Δ} {Λ} f refl refl) eq with cases++ Λ₀ Δ Λ₁ Λ eq
⊸rpass-c' {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} (ex {Δ = .(Λ₀ ++ _ ∷ Δ₀)} {Λ} f refl refl) refl | inj₁ (Δ₀ , refl , refl) = cong (λ x → ex {Δ = Λ₀ ++ Δ₀} x refl refl) (⊸rpass-c' f refl)
⊸rpass-c' {Λ₀ = .(Δ ++ Δ₀)} {Λ₁} (ex {Δ = Δ} {.(Δ₀ ++ _ ∷ Λ₁)} f refl refl) refl | inj₂ (Δ₀ , refl , refl) = cong (λ x → ex x refl refl) (⊸rpass-c' {Λ₀ = Δ ++ _ ∷ Δ₀} f refl)
⊸rpass-c' (ri2c (⊸r f)) refl = refl
⊸rpass-c' (ri2c (li2ri f)) refl = refl

⊸rpass-c {Γ = Γ₁} (ex {Γ = Γ} f refl refl) eq with snoc≡ Γ Γ₁ eq
⊸rpass-c {Γ = Γ₁} {B = B} (ex {Γ = Γ₁} f refl refl) refl | refl , refl rewrite snoc≡-refl Γ₁ B = ⊸rpass-c' f refl
⊸rpass-c {Γ = Γ} (ri2c f) eq = ⊥-elim ([]disj∷ Γ eq)


⊸rIl-c' : {Ω Λ Λ₀ Λ₁ : Cxt}{B C : Fma}
     → (f : - ∣ Ω ؛ Λ ⊢c C) (eq : Λ ≡ Λ₀ ++ B ∷ Λ₁)
     → ⊸r-c' (Il-c f) eq ≡ Il-c (⊸r-c' f eq)

⊸rIl-c : {Ω Γ Λ : Cxt}{B C : Fma}
     → (f : - ∣ Ω ؛ Λ ⊢c C) (eq : Ω ≡ Γ ++ B ∷ [])
     → ⊸r-c'' (Il-c f) eq ≡ Il-c (⊸r-c'' f eq) 

⊸rIl-c' {Λ₀ = Λ₀} {Λ₁} (ex {Δ = Δ} {Λ} f refl refl) eq with cases++ Λ₀ Δ Λ₁ Λ eq
⊸rIl-c' {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} (ex {Δ = .(Λ₀ ++ _ ∷ Δ₀)} {Λ} f refl refl) refl | inj₁ (Δ₀ , refl , refl) =  cong (λ x → ex {Δ = (Λ₀ ++ Δ₀)} x refl refl) (⊸rIl-c' f refl)
⊸rIl-c' {Λ₀ = .(Δ ++ Δ₀)} {Λ₁} (ex {Δ = Δ} {.(Δ₀ ++ _ ∷ Λ₁)} f refl refl) refl | inj₂ (Δ₀ , refl , refl) = cong (λ x → ex {Δ = Δ} x refl refl) (⊸rIl-c' {Λ₀ = Δ ++ _ ∷ Δ₀} f refl)
⊸rIl-c' (ri2c f) refl = refl

⊸rIl-c {Γ = Γ₁} (ex {Γ = Γ} f refl refl) eq with snoc≡ Γ Γ₁ eq
⊸rIl-c {Γ = Γ₁} (ex {Γ = .Γ₁} f refl refl) refl | refl , refl = ⊸rIl-c' f refl -- ⊸rIl-c' f refl
⊸rIl-c {Γ = Γ} (ri2c f) eq = ⊥-elim ([]disj∷ Γ eq)

⊸r⊸l-c'' : {Γ Ω Λ₀ Λ₁ : Cxt} {A B C D : Fma}   
       → (f : - ∣ Ω ؛ Γ ⊢c A) (g : just B ∣ Λ₀ ++ C ∷ Λ₁ ⊢ri D)
       → ⊸r-c' {Δ₀ = Γ ++ Λ₀} {Δ₁ = Λ₁} (⊸l-c-ri f g) refl
         ≡ ⊸l-c-ri {Δ = Λ₀ ++ Λ₁} f (⊸r (ex {Δ = Λ₀} {Λ₁} (ri2c g) refl refl))

⊸r⊸l-c' : {Γ Ω Λ Λ₀ Λ₁ : Cxt} {A B C D : Fma}
     → (f : - ∣ Γ ؛ [] ⊢c A) (g : just B ∣ Ω ؛ Λ ⊢c D) (eq : Λ ≡ Λ₀ ++ C ∷ Λ₁)
     → ⊸r-c' (⊸l-c f g) eq ≡ ⊸l-c f (⊸r-c' g eq)
     
⊸r⊸l-c : {Γ Δ Ω Λ : Cxt} {A B C D : Fma}
     → (f : - ∣ Γ ؛ [] ⊢c A) (g : just B ∣ Ω ؛ Λ ⊢c D) (eq : Ω ≡ Δ ++ C ∷ []) (eq' : Γ ++ Ω ≡ Γ ++ Δ ++ C ∷ [])
     → ⊸r-c'' {Γ = Γ ++ Δ} (⊸l-c f g) eq' ≡ ⊸l-c f (⊸r-c'' g eq)

⊸r⊸l-c'' {Λ₀ = Λ₀} {Λ₁} {C = C} (ex {Δ = Δ} {Λ} f refl refl) g
  rewrite cases++-inj₂ (Λ ++ Λ₀) Δ Λ₁ C = cong (λ x → ex x refl refl) (⊸r⊸l-c'' f g)
⊸r⊸l-c'' (ri2c f) g = refl

⊸r⊸l-c' {Λ₀ = Λ₀} {Λ₁} f (ex {Δ = Δ} {Λ} g refl refl) eq with cases++ Λ₀ Δ Λ₁ Λ eq
⊸r⊸l-c' {Γ = Γ₁} {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} f (ex {Γ = Γ} {Δ = .(Λ₀ ++ _ ∷ Δ₀)} {Λ} g refl refl) refl | inj₁ (Δ₀ , refl , refl) = cong (λ x → ex {Γ = Γ₁ ++ Γ} {Λ₀ ++ Δ₀} {Λ} x refl refl) (⊸r⊸l-c' f g refl) 
⊸r⊸l-c' {Γ = Γ₁} {Λ₀ = .(Δ ++ Δ₀)} {Λ₁} f (ex {Γ = Γ} {Δ = Δ} {.(Δ₀ ++ _ ∷ Λ₁)} {A = A} g refl refl) refl | inj₂ (Δ₀ , refl , refl) = cong (λ x → ex {Γ = Γ₁ ++ Γ} x refl refl) (⊸r⊸l-c' {Λ₀ = Δ ++ A ∷ Δ₀} f g refl)
⊸r⊸l-c' f (ri2c g) refl = ⊸r⊸l-c'' f g 


⊸r⊸l-c {Γ = Γ₁} {Δ = Δ} {C = C} f (ex {Γ = Γ} g refl refl) eq eq' with snoc≡ Γ Δ eq
⊸r⊸l-c {Γ = Γ₁} {Δ = Δ} {C = C} f (ex {Γ = .Δ} g refl refl) refl refl | refl , refl rewrite snoc≡-refl (Γ₁ ++ Δ) C = ⊸r⊸l-c' f g refl
⊸r⊸l-c {Δ = Δ} f (ri2c g) eq eq' = ⊥-elim ([]disj∷ Δ eq)


⊸r⊗l-c' : {Ω Γ Λ Λ₀ Λ₁ : Cxt} {A B C D : Fma} 
    → (f : just A ∣ Ω ؛ Λ ⊢c D) (eq : Ω ≡ B ∷ Γ) (eq' : Λ ≡ Λ₀ ++ C ∷ Λ₁)
    → ⊸r-c' (⊗l-c' {Γ = Γ} f eq) eq' ≡ ⊗l-c' (⊸r-c' f eq') eq
⊸r⊗l-c : {Ω Γ Λ : Cxt} {A B C D : Fma} 
    → (f : just A ∣ B ∷ Ω ؛ Λ ⊢c D) (eq : Ω ≡ Γ ++ C ∷ [])
    → ⊸r-c'' (⊗l-c f) eq ≡ ⊗l-c (⊸r-c'' f (cong (_ ∷_) eq))

⊸r⊗l-c' (ex {Γ = []} (ex {Γ = Γ} f eq''' eq₂) eq'' eq₁) eq eq' = ⊥-elim ([]disj∷ Γ eq''')
⊸r⊗l-c' (ex {Γ = []} (ri2c (⊸r (ex (ex {Γ = _ ∷ Γ} f refl refl) eq''' eq₂))) eq'' eq₁) eq eq'
  = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq''')))
⊸r⊗l-c' {Λ₀ = Λ₀} {Λ₁} {C = C} (ex {Γ = []} {Δ = Δ₁} {Λ₂}(ri2c (⊸r {B = B} (ex {Δ = Δ} {Λ} (ri2c f) refl refl))) refl eq') refl eq with cases++ Δ₁ Δ Λ₂ Λ eq'
⊸r⊗l-c' {Λ₀ = Λ₀} {Λ₁} {C = C} (ex {_} {[]} {Δ = Δ₁} {.(Γ₀ ++ Λ)} (ri2c (⊸r {B = _} (ex {Δ = .(Δ₁ ++ _ ∷ Γ₀)} {Λ} (ri2c f) refl refl))) refl eq') refl eq | inj₁ (Γ₀ , refl , refl) with cases++ Λ₀ Δ₁ Λ₁ (Γ₀ ++ Λ) eq
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Γ₀' ++ Γ₀ ++ Λ)} {B = B} {C = C} (ex {_} {[]} {Δ = .(Λ₀ ++ C ∷ Γ₀')} {.(Γ₀ ++ Λ)} (ri2c (⊸r {B = _} (ex {_} {_} {.((Λ₀ ++ C ∷ Γ₀') ++ _ ∷ Γ₀)} {Λ} (ri2c f) refl refl))) refl refl) refl refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ Γ₀' Λ₀ (Γ₀ ++ Λ) B |
          cases++-inj₁ (Λ₀ ++ C ∷ Γ₀') Γ₀ Λ B = refl
⊸r⊗l-c' {Λ₀ = .(Δ₁ ++ Γ₀')} {Λ₁} {C = C} (ex {_} {[]} {Δ = Δ₁} {.(Γ₀ ++ Λ)} (ri2c (⊸r {B = _} (ex {_} {_} {.(Δ₁ ++ _ ∷ Γ₀)} {Λ} (ri2c f) refl refl))) refl refl) refl eq | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , refl) with cases++ Γ₀' Γ₀ Λ₁ Λ p
⊸r⊗l-c' {_} {_} {_} {.(Δ₁ ++ Γ₀')} {.(Γ₀'' ++ Λ)} {B = B} {C = C} (ex {_} {[]} {Δ = Δ₁} {.((Γ₀' ++ C ∷ Γ₀'') ++ Λ)} (ri2c (⊸r {B = _} (ex {_} {_} {.(Δ₁ ++ _ ∷ Γ₀' ++ C ∷ Γ₀'')} {Λ} (ri2c f) refl refl))) refl refl) refl refl | inj₁ (.(Γ₀' ++ C ∷ Γ₀'') , refl , refl) | inj₂ (Γ₀' , refl , refl) | inj₁ (Γ₀'' , refl , refl) 
  rewrite cases++-inj₁ Δ₁ Γ₀' (Γ₀'' ++ Λ) B |
          cases++-inj₁ Δ₁ (Γ₀' ++ C ∷ Γ₀'') Λ B = refl
⊸r⊗l-c' {_} {_} {_} {.(Δ₁ ++ Γ₀ ++ Γ₀'')} {Λ₁} {B = B} {C = C} (ex {_} {[]} {Δ = Δ₁} {.(Γ₀ ++ Γ₀'' ++ C ∷ Λ₁)} (ri2c (⊸r {B = _} (ex {_} {_} {.(Δ₁ ++ _ ∷ Γ₀)} {.(Γ₀'' ++ C ∷ Λ₁)} (ri2c f) refl refl))) refl refl) refl refl | inj₁ (Γ₀ , refl , refl) | inj₂ (.(Γ₀ ++ Γ₀'') , refl , refl) | inj₂ (Γ₀'' , refl , refl) 
  rewrite cases++-inj₁ Δ₁ (Γ₀ ++ Γ₀'') Λ₁ B |
          cases++-inj₁ Δ₁ Γ₀ (Γ₀'' ++ C ∷ Λ₁) B = refl
⊸r⊗l-c' {Λ₀ = Λ₀} {Λ₁} {C = C} (ex {_} {[]} {Δ = .(Δ ++ Γ₀)} {Λ₂} (ri2c (⊸r {B = _} (ex {Δ = Δ} {.(Γ₀ ++ _ ∷ Λ₂)} (ri2c f) refl refl))) refl eq') refl eq | inj₂ (Γ₀ , refl , refl) 
  with cases++ Λ₀ (Δ ++ Γ₀) Λ₁ Λ₂ eq
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Γ₀' ++ Λ₂)} {B = B} {C = C} (ex {_} {[]} {.(Δ ++ Γ₀)} {Λ₂} (ri2c (⊸r {B = _} (ex {Δ = Δ} {.(Γ₀ ++ _ ∷ Λ₂)} (ri2c f) refl refl))) refl refl) refl eq | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , refl) with cases++ Λ₀ Δ Γ₀' Γ₀ p
⊸r⊗l-c' {Λ₀ = Λ₀} {.((Γ₀'' ++ Γ₀) ++ Λ₂)} {B = B} {C = C} (ex {_} {[]} {.((Λ₀ ++ C ∷ Γ₀'') ++ Γ₀)} {Λ₂} (ri2c (⊸r {B = _} (ex {Δ = .(Λ₀ ++ C ∷ Γ₀'')} {.(Γ₀ ++ B ∷ Λ₂)} (ri2c f) refl refl))) refl refl) refl refl | inj₂ (Γ₀ , refl , refl) | inj₁ (.(Γ₀'' ++ Γ₀) , refl , refl) | inj₁ (Γ₀'' , refl , refl)
  rewrite cases++-inj₂ (Γ₀'' ++ Γ₀) Λ₀ Λ₂ B |
          cases++-inj₂ Γ₀ (Λ₀ ++ C ∷ Γ₀'') Λ₂ B = refl
⊸r⊗l-c' {Λ₀ = .(Δ ++ Γ₀'')} {.(Γ₀' ++ Λ₂)} {B = B} {C = C} (ex {_} {[]} {.(Δ ++ Γ₀'' ++ C ∷ Γ₀')} {Λ₂} (ri2c (⊸r {B = _} (ex {Δ = Δ} {.((Γ₀'' ++ C ∷ Γ₀') ++ B ∷ Λ₂)} (ri2c f) refl refl))) refl refl) refl refl | inj₂ (.(Γ₀'' ++ C ∷ Γ₀') , refl , refl) | inj₁ (Γ₀' , refl , refl) | inj₂ (Γ₀'' , refl , refl)
  rewrite cases++-inj₂ Γ₀' (Δ ++ Γ₀'') Λ₂ B |
          cases++-inj₂ (Γ₀'' ++ C ∷ Γ₀') Δ Λ₂ B = refl
⊸r⊗l-c' {Λ₀ = .(Δ ++ Γ₀ ++ Γ₀')} {Λ₁} {B = B} {C = C} (ex {_} {[]} {.(Δ ++ Γ₀)} {.(Γ₀' ++ C ∷ Λ₁)} (ri2c (⊸r {B = _} (ex {Δ = Δ} {.(Γ₀ ++ _ ∷ Γ₀' ++ C ∷ Λ₁)} (ri2c f) refl refl))) refl refl) refl refl | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ (Δ ++ Γ₀) Γ₀' Λ₁ B |
          cases++-inj₂ Γ₀ Δ (Γ₀' ++ C ∷ Λ₁) B = refl
⊸r⊗l-c' {Λ₀ = Λ₀} {Λ₁} (ex {Γ = []} {Δ} {Λ} (ri2c (li2ri f)) refl refl) refl eq with cases++ Λ₀ Δ Λ₁ Λ eq
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Γ₀ ++ Λ)} {B = B} (ex {_} {[]} {.(Λ₀ ++ _ ∷ Γ₀)} {Λ} (ri2c (li2ri f)) refl refl) refl refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Λ₀ Λ B = refl 
⊸r⊗l-c' {Λ₀ = .(Δ ++ Γ₀)} {Λ₁} {B = B} (ex {_} {[]} {Δ} {.(Γ₀ ++ _ ∷ Λ₁)} (ri2c (li2ri f)) refl refl) refl refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₁ Δ Γ₀ Λ₁ B = refl
⊸r⊗l-c' {Λ₀ = Λ₀} {Λ₁} (ex {Γ = A' ∷ Γ} {Δ} {Λ} f refl refl) refl eq with cases++ Λ₀ Δ Λ₁ Λ eq
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Γ₀ ++ Λ)} (ex {_} {A' ∷ Γ} {.(Λ₀ ++ _ ∷ Γ₀)} {Λ} f refl refl) refl refl | inj₁ (Γ₀ , refl , refl) = cong (λ x → ex {Δ = Λ₀ ++ Γ₀} x refl refl) (⊸r⊗l-c' f refl refl)
⊸r⊗l-c' {Λ₀ = .(Δ ++ Γ₀)} {Λ₁} (ex {_} {A' ∷ Γ} {Δ} {.(Γ₀ ++ _ ∷ Λ₁)} f refl refl) refl refl | inj₂ (Γ₀ , refl , refl) = cong (λ x → ex x refl refl) (⊸r⊗l-c' {Λ₀ = Δ ++ _ ∷ Γ₀} f refl refl)


⊸r⊗l-c {Γ = Γ₁} {B = B} (ex {Γ = Γ} {A = A} f eq' refl) refl with snoc≡ (B ∷ Γ₁) Γ eq'
⊸r⊗l-c {Γ = Γ₁} {B = B} (ex {Γ = .(B ∷ Γ₁)} {A = A} f refl refl) refl | refl , refl rewrite snoc≡-refl Γ₁ A = ⊸r⊗l-c' f refl refl



⊗rpass-p : {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A : Pos} {A' B : Fma}
        → (f : just A' ∣ Γ ⊢li A) (g : - ∣ Δ ⊢ri B) (eq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁)
        → (gen⊗r-p Γ₁ (pass f) g (∷left' Γ₁' eq) peq) ≡ (pass (gen⊗r-li Γ₁ f g eq peq))

⊗rpass-p Γ₁ (Il f) g isInter[] peq with empty↭' peq
⊗rpass-p .[] (Il f) g isInter[] (empty refl) | refl = refl
⊗rpass-p Γ₁ (Il f) g []left peq = refl
⊗rpass-p Γ₁ (Il f) g []right peq with empty↭' peq
⊗rpass-p .[] (Il f) g []right (empty refl) | refl = refl
⊗rpass-p Γ₁ (Il f) g (∷left eq) peq = refl
⊗rpass-p Γ₁ (Il f) g (∷right eq) peq = refl
⊗rpass-p Γ₁ (⊗l f) g isInter[] peq with empty↭' peq
⊗rpass-p .[] (⊗l f) g isInter[] (empty refl) | refl = refl
⊗rpass-p Γ₁ (⊗l f) g []left peq = refl
⊗rpass-p Γ₁ (⊗l f) g []right peq with empty↭' peq
⊗rpass-p .[] (⊗l f) g []right (empty refl) | refl = refl
⊗rpass-p Γ₁ (⊗l f) g (∷left eq) peq = refl
⊗rpass-p Γ₁ (⊗l f) g (∷right eq) peq = refl
⊗rpass-p Γ₁ (p2li f) g isInter[] peq with empty↭' peq
⊗rpass-p .[] (p2li f) g isInter[] (empty refl) | refl = refl
⊗rpass-p Γ₁ (p2li f) g []left peq = refl
⊗rpass-p Γ₁ (p2li f) g []right peq with empty↭' peq
⊗rpass-p .[] (p2li f) g []right (empty refl) | refl = refl
⊗rpass-p Γ₁ (p2li f) g (∷left eq) peq = refl
⊗rpass-p Γ₁ (p2li f) g (∷right eq) peq = refl


⊗rpass-ri : {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A' A B : Fma}
         → (f : just A' ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B) (eq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁)
         → gen⊗r-ri Γ₁ (pass-ri f) g (∷left' Γ₁' eq) peq ≡ p2li (pass (gen⊗r-ri Γ₁ f g eq peq))

⊗rpass-ri Γ₁ (⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) g eq peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq'))) -- imposs
⊗rpass-ri {Γ₁' = []} Γ₁ (⊸r (ex {Δ = []} {.[]} (ri2c f) refl refl)) g isInter[] peq = ⊗rpass-ri (Γ₁ ++ _ ∷ []) f g []left (snoc↭' {xs₀ = []} {[]} refl peq)
⊗rpass-ri {Γ₁' = []} Γ₁ (⊸r (ex {Δ = []} {.(_ ∷ _)} (ri2c f) refl refl)) g []right peq = ⊗rpass-ri (Γ₁ ++ _ ∷ []) f g (∷right []right) (snoc↭' {xs₀ = []} {[]} refl peq)
⊗rpass-ri {Γ₁' = []} Γ₁ (⊸r (ex {Δ = x ∷ Δ} {[]} (ri2c f) refl refl)) g []right peq = ⊗rpass-ri (Γ₁ ++ _ ∷ []) f g  (∷left (isInter++l Δ (∷right' [] ([]right' [])))) (snoc↭' {xs₀ = []} {[]} refl peq)
⊗rpass-ri {Γ₁' = []} Γ₁ (⊸r (ex {Δ = x ∷ Δ} {x₁ ∷ Λ} (ri2c f) refl refl)) g []right peq = ⊗rpass-ri (Γ₁ ++ _ ∷ []) f g  (∷left (isInter++l Δ (∷right' (_ ∷ Λ) ([]right' (_ ∷ Λ))))) (snoc↭' {xs₀ = []} {[]} refl peq)
⊗rpass-ri {Γ₁' = x ∷ Γ₁'} Γ₁ (⊸r (ex {Δ = Δ} {Λ} (ri2c f) refl refl)) g eq peq with isInter++? Δ Λ refl eq
⊗rpass-ri {Γ₀ = _} {x ∷ Γ₁'} Γ₁ {A' = A'} (⊸r (ex {Δ = .[]} {Λ} (ri2c f) refl refl)) g eq peq | .[] , Γ₀₁ , [] , .(x ∷ Γ₁') , isInter[] , inTeq2 , refl , refl , refl = ⊗rpass-ri (Γ₁ ++ _ ∷ []) f g (∷right' Γ₀₁ inTeq2) (snoc↭' {xs₀ = []} {xs₁ = x ∷ Γ₁'} {ys = Γ₁} refl peq)
⊗rpass-ri {Γ₀ = _} {x ∷ Γ₁'} Γ₁ {A' = A'} (⊸r (ex {Δ = .(_ ∷ _)} {Λ} (ri2c f) refl refl)) g eq peq | (_ ∷ xs) , Γ₀₁ , [] , .(x ∷ Γ₁') , []right , inTeq2 , refl , refl , refl = ⊗rpass-ri (Γ₁ ++ _ ∷ []) f g (∷left (isInter++l xs (∷right' Γ₀₁ inTeq2))) (snoc↭' {xs₀ = []} {xs₁ = x ∷ Γ₁'} {ys = Γ₁} refl peq)
⊗rpass-ri {Γ₀ = _} {x ∷ .(Γ₁₀' ++ Γ₁₁')} Γ₁ {A' = A'} (⊸r (ex {Δ = Δ} {Λ} (ri2c f) refl refl)) g eq peq | Γ₀₀ , Γ₀₁ , .x ∷ Γ₁₀' , Γ₁₁' , inTeq1 , inTeq2 , refl , refl , refl = ⊗rpass-ri (Γ₁ ++ _ ∷ []) f g (isInter++ inTeq1 (∷right' Γ₀₁ inTeq2)) (snoc↭' {xs₀ = x ∷ Γ₁₀'} {xs₁ = Γ₁₁'} {ys = Γ₁} refl peq)
⊗rpass-ri Γ₁ (li2ri f) g eq peq = cong (λ x → p2li x) (⊗rpass-p Γ₁ f g eq peq)


⊗rpass-c-ri : {Γ Γ' Δ Ω : Cxt} {A' A B : Fma}
         → (f : just A' ∣ Γ ؛ Ω ⊢c A) (g : - ∣ Δ ⊢ri B) (eq : Γ' ≡ A' ∷ Γ)
         → ⊗r-c-ri (pass-c' f eq) g ≡ pass-c' (⊗r-c-ri f g) eq

⊗rpass-c-ri (ex f refl refl) g refl = cong (λ x → ex x refl refl) (⊗rpass-c-ri f g refl)
⊗rpass-c-ri {Ω = []} (ri2c (⊸r f)) g refl = cong (λ x → ex {Γ = []} {[]} (ri2c (li2ri x)) refl refl) (⊗rpass-ri [] (⊸r f) g isInter[] (empty refl))
⊗rpass-c-ri {Ω = x ∷ Ω} (ri2c (⊸r f)) g refl = cong (λ x → ex {Γ = []} {[]} (ri2c (li2ri x)) refl refl) (⊗rpass-ri [] (⊸r f) g []right (empty refl))
⊗rpass-c-ri {Ω = []} (ri2c (li2ri f)) g refl = refl
⊗rpass-c-ri {Ω = x ∷ Ω} (ri2c (li2ri f)) g refl = refl

⊗rpass-c : {Γ Γ' Δ Λ : Cxt} {A' A B : Fma}
        → (f : just A' ∣ Γ ؛ [] ⊢c A) (g : - ∣ Δ ؛ Λ ⊢c B) (eq : Γ' ≡ A' ∷ Γ)
        → ⊗r-c (pass-c' f eq) g ≡ pass-c' (⊗r-c f g) (cong (_++ Δ) eq)

⊗rpass-c f (ex g refl refl) refl = cong (λ x → ex x refl refl) (⊗rpass-c f g refl)
⊗rpass-c f (ri2c g) refl = ⊗rpass-c-ri f g refl



⊗rIl-ri : {Γ Γ₀ Γ₁' Δ : Cxt} (Γ₁ : Cxt) {A B : Fma}
       → (f : - ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B) (eq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁)
       → gen⊗r-ri Γ₁  (Il-ri f) g eq peq ≡ Il (gen⊗r-ri Γ₁ f g eq peq)

⊗rIl-c' : {Ω Γ Δ : Cxt} {A B : Fma}
       → (f : - ∣ Ω ؛ Γ ⊢c A) (g : - ∣ Δ ⊢ri B)
       → ⊗r-c-ri (Il-c f) g ≡ Il-c (⊗r-c-ri f g)

⊗rIl-c : {Ω Γ Δ : Cxt} {A B : Fma}
      → (f : - ∣ Ω ؛ [] ⊢c A) (g : - ∣ Γ ؛ Δ ⊢c B )
      → ⊗r-c (Il-c f) g ≡ Il-c (⊗r-c f g)

⊗rIl-ri Γ₁ (⊸r (ex (ex {Γ = D ∷ Γ} f refl refl) eq' eq₁)) g eq peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
⊗rIl-ri Γ₁ (⊸r (ex {Δ = Δ} {Λ} (ri2c f) refl refl)) g eq peq with isInter++? Δ Λ refl eq
... | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' ,  inTeq1 , inTeq2 , refl , refl , refl = ⊗rIl-ri (Γ₁ ++ _ ∷ []) f g (isInter++ inTeq1 (∷right' Γ₀₁ inTeq2)) (snoc↭' refl peq)
⊗rIl-ri Γ₁ (li2ri f) g eq peq = refl


⊗rIl-c' {Δ = Δ₁} (ex {Δ = Δ} {Λ} f refl refl) g = cong (λ x → ex {Δ = Δ} {Λ ++ Δ₁} x refl refl) (⊗rIl-c' f g)
⊗rIl-c' (ri2c f) g = cong (λ x → ri2c (li2ri x)) (⊗rIl-ri [] f g ([]right' _) (empty refl))

⊗rIl-c {Ω = Ω} f (ex {Γ = Γ} g refl refl) = cong (λ x → ex {Γ = Ω ++ Γ} x refl refl) (⊗rIl-c f g)
⊗rIl-c f (ri2c g) = ⊗rIl-c' f g

⊗r⊗l-ri : {Γ Γ₀ Γ₀' Γ₀₀ Γ₀₀' Γ₁₀' Γ₁₁' Δ : Cxt} {A B C D : Fma}
        → (Γ₁ : Cxt) (f : just A ∣ Γ ⊢ri C) (g : - ∣ Δ ⊢ri D) (eq : Γ ≡ Γ₀ ++ B ∷ Γ₀') (inTeq1 : isInter Γ₀₀ Γ₁₀' Γ₀) (inTeq2 : isInter Γ₀₀' Γ₁₁' Γ₀') (peq : Γ₁₀' ++ Γ₁₁' ↭' Γ₁) 
        → gen⊗r-ri Γ₁ (⊗l-ri f eq) g (isInter++ inTeq1 inTeq2) peq
          ≡ ⊗l (ex (ri2c (li2ri (gen⊗r-ri Γ₁ f g (subst (isInter (Γ₀₀ ++ B ∷ Γ₀₀') (Γ₁₀' ++ Γ₁₁')) (sym eq) ((isInter++ inTeq1 (∷left' Γ₁₁' inTeq2) ))) peq))) refl refl)

⊗r⊗l-ri Γ₁ (⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) g eq inTeq1 inTeq2 peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
⊗r⊗l-ri {Γ₀ = Γ₀} {Γ₀'} Γ₁ (⊸r (ex {Δ = Δ} {Λ} (ri2c f) refl refl)) g eq inTeq1 inTeq2 peq with cases++ Γ₀ Δ Γ₀' Λ eq 
⊗r⊗l-ri {Γ₀ = Γ₀} {.(Ω₀ ++ Λ)} {Γ₀₀' = Γ₀₀'} {Γ₁₁' = Γ₁₁'} {B = B} Γ₁ (⊸r {A = A} (ex {Δ = .(Γ₀ ++ _ ∷ Ω₀)} {Λ} (ri2c f) refl refl)) g refl inTeq1 inTeq2 peq | inj₁ (Ω₀ , refl , refl) with isInter++? Ω₀ Λ refl inTeq2
... | Ξ₀ , Ξ₁ , Ψ₀ , Ψ₁ , int₀ , int₁ , refl , refl , refl
  rewrite isInter++-assoc inTeq1 int₀ int₁ | isInter++-refl (isInter++ inTeq1 int₀) int₁ |
          (isInter++-∷left' {x = B} Ψ₀ int₀ int₁) |
          isInter++-assoc inTeq1 (∷left' {x = B} Ψ₀ int₀) int₁ | isInter++-refl (isInter++ inTeq1 (∷left' {x = B} Ψ₀ int₀)) int₁ |
          sym (isInter++-assoc inTeq1 int₀ (∷right' {x = A} Ξ₁ int₁)) |
          sym (isInter++-assoc inTeq1 (∷left' {x = B} Ψ₀ int₀) (∷right' {x = A} Ξ₁ int₁)) |
          sym (isInter++-∷left' {x = B} Ψ₀ int₀ (∷right' {x = A} Ξ₁ int₁)) =
            ⊗r⊗l-ri (Γ₁ ∷ʳ _) f g refl inTeq1 (isInter++ int₀ (∷right' Ξ₁ int₁)) _
⊗r⊗l-ri {Γ₀ = .(Δ ++ Ω₀)} {Γ₀'} {Γ₁₁' = Γ₁₁'} {B = B} Γ₁ (⊸r {A = A} (ex {Δ = Δ} {.(Ω₀ ++ _ ∷ Γ₀')} (ri2c f) refl refl)) g refl inTeq1 inTeq2 peq | inj₂ (Ω₀ , refl , refl) with isInter++? Δ Ω₀ refl inTeq1
... | Ξ₀ , Ξ₁ , Ψ₀ , Ψ₁ , int₀ , int₁ , refl , refl , refl
  rewrite sym (isInter++-assoc int₀ int₁ inTeq2) | isInter++-refl int₀ (isInter++ int₁ inTeq2) |
          sym (isInter++-assoc int₀ int₁ (∷left' {x = B} Γ₁₁' inTeq2)) |
          isInter++-refl int₀ (isInter++ int₁ (∷left' {x = B} Γ₁₁' inTeq2)) |
          sym (isInter++-∷right' {x = A} Ξ₁ int₁ inTeq2) |
          isInter++-assoc int₀ (∷right' {x = A} Ξ₁ int₁) inTeq2 |
          sym (isInter++-∷right' {x = A} Ξ₁ int₁ (∷left' {x = B} Γ₁₁' inTeq2)) |
          isInter++-assoc int₀ (∷right' {x = A} Ξ₁ int₁) (∷left' {x = B} Γ₁₁' inTeq2) =
            ⊗r⊗l-ri {Γ₀ = Δ ++ A ∷ Ω₀} (Γ₁ ∷ʳ _) f g refl (isInter++ int₀ (∷right' Ξ₁ int₁)) inTeq2 _
⊗r⊗l-ri Γ₁ (li2ri f) g refl inTeq1 inTeq2 peq
  rewrite isInter++-refl inTeq1 inTeq2 = refl

⊗r⊗l-c-ri : {Γ Γ' Ω Δ : Cxt} {A B C D : Fma}
          → (f : just A ∣ Γ' ؛ Ω ⊢c C) (g : - ∣ Δ ⊢ri D) (eq : Γ' ≡ B ∷ Γ)
          → ⊗r-c-ri (⊗l-c' f eq) g ≡ ⊗l-c' (⊗r-c-ri f g) eq

⊗r⊗l-c-ri (ex {Γ = []} (ex {Γ = []} f eq' eq₁) eq eq1) g eq2 = ⊥-elim ([]disj∷ [] eq')
⊗r⊗l-c-ri (ex {Γ = []} (ex {Γ = x ∷ Γ} f eq' eq₁) eq eq1) g eq2 = ⊥-elim ([]disj∷ (x ∷ Γ) eq')
⊗r⊗l-c-ri {B = B} (ex {Γ = []} {Δ = Δ} {[]} (ri2c f) refl refl) g refl
  rewrite sym (isInter++-[]right' Δ []) | sym (isInter++-[]right' Δ (B ∷ []))
    = cong (λ x → ri2c (li2ri x)) (⊗r⊗l-ri [] f g refl ([]right' Δ) isInter[] (empty refl))
⊗r⊗l-c-ri {B = B} (ex {Γ = []} {Δ = Δ} {x ∷ Λ} (ri2c f) refl refl) g refl 
  rewrite sym (isInter++-[]right' Δ (x ∷ Λ)) | sym (isInter++-[]right' Δ (B ∷ x ∷ Λ))
    = cong (λ x → ri2c (li2ri x)) (⊗r⊗l-ri [] f g refl ([]right' Δ) []right (empty refl))
⊗r⊗l-c-ri (ex {Γ = x ∷ Γ} f refl refl) g refl = cong (λ x → ex x refl refl) (⊗r⊗l-c-ri f g refl)


⊗r⊗l-c : {Γ Γ' Δ Λ : Cxt} {A B C D : Fma}
       → (f : just A ∣  Γ' ؛ [] ⊢c C) (g : - ∣ Δ ؛ Λ ⊢c D) (eq : Γ' ≡ B ∷ Γ)
       → ⊗r-c (⊗l-c' f eq) g ≡ ⊗l-c' (⊗r-c f g) (cong (_++ Δ) eq)
⊗r⊗l-c f (ex {Γ = Γ} {Δ} {Λ} g refl refl) refl = cong (λ x → ex {Γ = _ ++ Γ} {Δ} {Λ} x refl refl) (⊗r⊗l-c f g refl)
⊗r⊗l-c f (ri2c g) refl = ⊗r⊗l-c-ri f g refl

[]right'++ : {X : Set} → (xs ys : List X) → []right' (xs ++ ys) ≡ isInter++ ([]right' xs) ([]right' ys)
[]right'++ [] [] = refl
[]right'++ [] (x ∷ ys) = refl
[]right'++ (x ∷ xs) [] = refl
[]right'++ (x ∷ xs) (x₁ ∷ ys) = refl


⊗r⊸l-ri : {Δ Γ Γ₀ Γ₁' Λ : Cxt} (Γ₁ : Cxt) {A B C D : Fma}
        → (f : - ∣ Δ ⊢ri A) (g : just B ∣ Γ ⊢ri C) (h : - ∣ Λ ⊢ri D) (inTeq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁)
        → gen⊗r-ri {Γ₀ = Δ ++ Γ₀} Γ₁ (⊸l-ri f g) h (isInter++ (([]right' Δ)) inTeq) peq ≡ p2li (f2p (⊸l f (gen⊗r-ri Γ₁ g h inTeq peq)))

⊗r⊸l-ri Γ₁ f (⊸r (ex (ex {Γ = x ∷ Γ} g refl refl) eq' eq)) h inTeq peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq'))) -- imposs
⊗r⊸l-ri {Γ₀ = Γ₀} {Γ₁'} Γ₁ f (⊸r (ex {Δ = Δ} {Λ} (ri2c g) refl refl)) h inTeq peq with isInter++? Δ Λ refl inTeq
⊗r⊸l-ri {Δ₁} {Γ₀ = .(Ξ₀ ++ Ξ₁)} {.(Ψ₀ ++ Ψ₁)} Γ₁ f (⊸r (ex {Δ = Δ} {Λ} {A = A} (ri2c g) refl refl)) h .(isInter++ int₀ int₁) peq | Ξ₀ , Ξ₁ , Ψ₀ , Ψ₁ , int₀ , int₁ , refl , refl , refl 
  rewrite isInter++-assoc ([]right' Δ₁) int₀ int₁ | 
          isInter++-refl (isInter++ ([]right' Δ₁) int₀) int₁ | 
          sym (isInter++-assoc ([]right' Δ₁) int₀ (∷right' {x = A} Ξ₁ int₁)) = ⊗r⊸l-ri (Γ₁ ++ _ ∷ []) f g h (isInter++ int₀ (∷right' Ξ₁ int₁)) (snoc↭' refl peq)
⊗r⊸l-ri {Δ} Γ₁ f (li2ri g) h inTeq peq 
  rewrite isInter++-refl ([]right' Δ) inTeq |
          isInter-left[] ([]right' Δ) = refl

⊗r⊸l-c-ri : {Γ Δ Λ Ω : Cxt} {A B C D :  Fma}
         → (f : - ∣ Γ ؛ Δ ⊢c A) (g : just B ∣ Λ ⊢ri C) (h : - ∣ Ω ⊢ri D)
         → ⊗r-c-ri (⊸l-c-ri f g) h ≡ ⊸l-c-ri f (li2ri (gen⊗r-ri [] g h ([]right' Λ) (empty refl)))

⊗r⊸l-c-ri {Λ = Λ₁} {Ω} (ex {Γ = Γ} {Δ} {Λ} f refl refl) g h = cong (λ x → ex {Γ = Γ} {Δ} {Λ = Λ ++ Λ₁ ++ Ω} x refl refl) (⊗r⊸l-c-ri f g h)
⊗r⊸l-c-ri {Δ = Δ} {Λ} (ri2c f) g h 
       rewrite []right'++ Δ Λ = cong (λ x → ri2c (li2ri x)) (⊗r⊸l-ri [] f g h ([]right' Λ) (empty refl)) 

⊗r-c-ri-⊸l : {Γ Δ Λ Ω : Cxt} {A B C D : Fma}
         → (f : - ∣ Γ ؛ [] ⊢c A ) (g : just B ∣ Δ ؛ Λ ⊢c C) (h : - ∣ Ω ⊢ri D)
         → ⊗r-c-ri (⊸l-c f g) h ≡ ⊸l-c f (⊗r-c-ri g h)

⊗r-c-ri-⊸l {Γ = Γ₁} {Ω = Ω} f (ex {Γ = Γ} {Δ} {Λ} g refl refl) h = cong (λ x → ex {Γ = Γ₁ ++ Γ} {Δ} {Λ ++ Ω} x refl refl) (⊗r-c-ri-⊸l f g h)
⊗r-c-ri-⊸l f (ri2c g) h = ⊗r⊸l-c-ri f g h

⊗r⊸l-c : {Γ Δ Λ Ω : Cxt} {A B C D : Fma} 
      → (f : - ∣ Γ ؛ [] ⊢c A) (g : just B ∣ Δ ؛ [] ⊢c C) (h : - ∣ Λ ؛ Ω ⊢c D)
      → ⊗r-c (⊸l-c f g) h ≡ ⊸l-c f (⊗r-c g h)  
⊗r⊸l-c {Γ = Γ₁} {Δ₁} f g (ex {Γ = Γ} {Δ} {Λ} h refl refl) = cong (λ x → ex {Γ = Γ₁ ++ Δ₁ ++ Γ} {Δ} {Λ} x refl refl) (⊗r⊸l-c f g h)
⊗r⊸l-c f g (ri2c h) = ⊗r-c-ri-⊸l f g h



expass-c : {Γ Δ Λ₀ Λ₁ : Cxt}{A' A B C : Fma}
    → (f : just A' ∣ Γ ؛ Δ ⊢c C) (eq : Γ ≡ Λ₀ ++ A ∷ B ∷ Λ₁)
    → ex-c' (A' ∷ Λ₀) (pass-c' f refl) (cong (A' ∷_) eq) ≡ pass-c' (ex-c' Λ₀ f eq) refl

expass-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B = B} (ex {Γ = Γ} {A = A₁} f refl eq₁) eq with cases++ Γ Λ₀ [] (A ∷ B ∷ Λ₁) (sym eq)
... | inj₁ (Δ₀ , p , p') = ⊥-elim ([]disj∷ Δ₀ p') -- imposs
expass-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B = B} (ex {Γ = .(_ ++ _ ∷ [])} {A = A₁} (ex f refl refl) refl eq₁) eq | inj₂ (D ∷ [] , p , p') with inj∷ p
... | refl , q with inj∷ q
expass-c {Λ₀ = Λ₀} {.[]} {_} {D} {B = B} (ex {_} {.(Γ ++ _ ∷ [])} {Δ₁} {Λ₁} {A = B} (ex {Γ = Γ} {Δ} {Λ} f refl refl) refl eq₁) eq | inj₂ (D ∷ [] , refl , p') | refl , refl | refl , refl with snoc≡ Γ Λ₀ p' | cases++ Δ₁ Δ Λ₁ Λ eq₁
expass-c {Λ₀ = Λ₀} {.[]} {A'} {D} {B = B} (ex {_} {.(Λ₀ ++ _ ∷ [])} {Δ₁} {.(Γ₀ ++ Λ)} (ex {Γ = .Λ₀} {.(Δ₁ ++ B ∷ Γ₀)} {Λ} f refl refl) refl refl) refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | refl , refl | refl , refl | inj₁ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ (D ∷ []) Λ₀ [] B | 
          cases++-inj₁ Δ₁ Γ₀ Λ B | 
          snoc≡-refl Λ₀ D = refl
expass-c {Λ₀ = Λ₀} {.[]} {_} {D} {B = B} (ex {_} {.(Λ₀ ++ _ ∷ [])} {.(Δ ++ Γ₀)} {Λ₁} {A = B} (ex {Γ = Λ₀} {Δ} {.(Γ₀ ++ B ∷ Λ₁)} f refl refl) refl refl) refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | refl , refl | refl , refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ (D ∷ []) Λ₀ [] B | 
          cases++-inj₂ Γ₀ Δ Λ₁ B |
          snoc≡-refl Λ₀ D = refl
expass-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B = B} (ex {Γ = .[]} {A = A₁} (ri2c f) refl eq₁) eq | inj₂ (D ∷ [] , p , p') = ⊥-elim ([]disj∷ Λ₀ p')
expass-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B = B} (ex {Γ = .(Λ₀ ++ D ∷ E ∷ Δ₀)} {A = A₁} f refl refl) eq | inj₂ (D ∷ E ∷ Δ₀ , p , refl) with inj∷ p
... | refl , q with inj∷ q
expass-c {Λ₀ = Λ₀} {.(Δ₀ ++ A₁ ∷ [])} {A'} {D} {B = B} (ex {_} {.(Λ₀ ++ D ∷ B ∷ Δ₀)} {A = A₁} f refl refl) refl | inj₂ (D ∷ B ∷ Δ₀ , refl , refl) | refl , refl | refl , refl   
  rewrite cases++-inj₂ (Λ₀ ++ D ∷ B ∷ Δ₀) Λ₀ [] A₁ | 
          cases++-inj₂ (D ∷ B ∷ Δ₀) Λ₀ [] A₁ = cong (λ x → ex {Γ = A' ∷ Λ₀ ++ B ∷ D ∷ Δ₀} x refl refl) (expass-c f refl)
expass-c {Λ₀ = Λ₀} (ri2c f) eq = ⊥-elim ([]disj∷ Λ₀ eq)


exIl-c : {Γ Δ Λ₀ Λ₁ : Cxt}{A B C : Fma}
    → (f : - ∣ Γ ؛ Δ ⊢c C) (eq : Γ ≡ Λ₀ ++ A ∷ B ∷ Λ₁)
    → ex-c' Λ₀ (Il-c f) eq ≡ Il-c (ex-c' Λ₀ f eq)

exIl-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B} (ex {Γ = Γ} f refl eq₁) eq with cases++ Γ Λ₀ [] (A ∷ B ∷ Λ₁) (sym eq)
... | inj₁ (Δ₀ , p , p') = ⊥-elim ([]disj∷ Δ₀ p')
exIl-c {Λ₀ = Λ₀} {.[]} {A = A} {B} (ex {Γ = .(_ ++ _ ∷ [])} {Δ = Δ₁} {Λ₁} (ex {Γ = Γ} {Δ = Δ} {Λ} f refl refl) refl eq₁) eq | inj₂ (A ∷ [] , refl , p') with cases++ Δ₁ Δ Λ₁ Λ eq₁ | snoc≡ Γ Λ₀ p'
... | inj₁ (Γ₀ , refl , refl) | refl , refl = refl
... | inj₂ (Γ₀ , refl , refl) | refl , refl = refl
exIl-c {Λ₀ = Λ₀} {.[]} {A = A} {B} (ex {Γ = .[]} (ri2c f) refl eq₁) eq | inj₂ (A ∷ [] , refl , p') = ⊥-elim ([]disj∷ Λ₀ p')
exIl-c {Λ₀ = Λ₀} {.(Δ₀ ++ _ ∷ [])} {A = A} {B} (ex {Γ = .(Λ₀ ++ A ∷ B ∷ Δ₀)} f refl refl) refl | inj₂ (A ∷ B ∷ Δ₀ , refl , refl) = cong (λ x → ex {Γ = Λ₀ ++ _ ∷ _ ∷ Δ₀} x refl refl) (exIl-c f refl)
exIl-c {Λ₀ = Λ₀} (ri2c f) eq = ⊥-elim ([]disj∷ Λ₀ eq)

ex⊸r-c' : {S : Stp} {Γ Δ Λ₀ Λ₁ Δ₀ Δ₁ : Cxt} {A' A B C : Fma}
     → (f : S ∣ Γ ؛ Δ ⊢c C) (eq : Γ ≡ Λ₀ ++ A ∷ B ∷ Λ₁) (eq' : Δ ≡ Δ₀ ++ A' ∷ Δ₁)
     → ex-c' Λ₀ (⊸r-c' f eq') eq ≡ ⊸r-c' (ex-c' Λ₀ f eq) eq'

ex⊸r-c' {Λ₀ = Λ₀} {Λ₁} {A = A} {B} (ex {Γ = Γ} f refl eq₁) eq eq' with cases++ Γ Λ₀ [] (A ∷ B ∷ Λ₁) (sym eq)
... | inj₁ (Ω₀ , p , p') = ⊥-elim ([]disj∷ Ω₀ p')
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {Δ₀} {Δ₁} {A = A} {B} (ex {Γ = Γ} {Δ} {Λ} f refl eq₁) eq eq' | inj₂ (A ∷ [] , refl , p') with cases++ Δ₀ Δ Δ₁ Λ eq'
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {Δ₀} {.(Ω₁ ++ Λ)} {_} {A} {B} (ex {Γ = .(_ ++ _ ∷ [])} {.(Δ₀ ++ _ ∷ Ω₁)} {Λ} (ex {Γ = Γ} {Δ₁} {Λ₁} f refl refl) refl eq₁) eq eq' | inj₂ (A ∷ [] , refl , p') | inj₁ (Ω₁ , refl , refl) with snoc≡ Γ Λ₀ p' | cases++ (Δ₀ ++ _ ∷ Ω₁) Δ₁ Λ Λ₁ eq₁
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {Δ₀} {.(Ω₁ ++ Γ₀ ++ Λ₁)} {A'} {A} {B} (ex {_} {.(Λ₀ ++ _ ∷ [])} {.(Δ₀ ++ _ ∷ Ω₁)} {.(Γ₀ ++ Λ₁)} (ex {Γ = .Λ₀} {.(Δ₀ ++ _ ∷ Ω₁ ++ B ∷ Γ₀)} {Λ₁} f refl refl) refl refl) refl refl | inj₂ (A ∷ [] , refl , refl) | inj₁ (Ω₁ , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl) 
  rewrite cases++-inj₁ Δ₀ (Ω₁ ++ B ∷ Γ₀) Λ₁ A' |
          cases++-inj₂ (A ∷ []) Λ₀ [] B |
          cases++-inj₁ Δ₀ (Ω₁ ++ Γ₀) Λ₁ A' | 
          snoc≡-refl Λ₀ A | 
          cases++-inj₁ (Δ₀ ++ Ω₁) Γ₀ Λ₁ B | 
          cases++-inj₁ Δ₀ Ω₁ (Γ₀ ++ A ∷ Λ₁) A' = refl
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {Δ₀} {.(Ω₁ ++ Λ)} {_} {A} {B} (ex {_} {.(Λ₀ ++ _ ∷ [])} {.(Δ₀ ++ _ ∷ Ω₁)} {Λ} (ex {Γ = .Λ₀} {Δ₁} {.(Γ₀ ++ B ∷ Λ)} f refl refl) refl eq₁) eq refl | inj₂ (A ∷ [] , refl , refl) | inj₁ (Ω₁ , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , q') with cases++ Δ₀ Δ₁ Ω₁ Γ₀ (sym q')
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {Δ₀} {.((Γ₁ ++ Γ₀) ++ Λ)} {A'} {A} {B} (ex {_} {.(Λ₀ ++ A ∷ [])} {.(Δ₀ ++ _ ∷ Γ₁ ++ Γ₀)} {Λ} (ex {Γ = Λ₀} {.(Δ₀ ++ _ ∷ Γ₁)} {.(Γ₀ ++ B ∷ Λ)} {_} {_} {A} f refl refl) refl refl) refl refl | inj₂ (A ∷ [] , refl , refl) | inj₁ (.(Γ₁ ++ Γ₀) , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₁ , refl , refl) 
  rewrite cases++-inj₁ Δ₀ Γ₁ (Γ₀ ++ B ∷ Λ) A' |
          cases++-inj₂ (A ∷ []) Λ₀ [] B |
          cases++-inj₁ Δ₀ Γ₁ (Γ₀ ++ Λ) A' |
          snoc≡-refl Λ₀ A |
          cases++-inj₂ Γ₀ (Δ₀ ++ Γ₁) Λ B |
          cases++-inj₁ Δ₀ (Γ₁ ++ A ∷ Γ₀) Λ A' = refl
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {.(Δ₁ ++ Γ₁)} {.(Ω₁ ++ Λ)} {A'} {A} {B} (ex {_} {.(Λ₀ ++ A ∷ [])} {.((Δ₁ ++ Γ₁) ++ _ ∷ Ω₁)} {Λ} {_} (ex {Γ = Λ₀} {Δ₁} {.((Γ₁ ++ _ ∷ Ω₁) ++ B ∷ Λ)} {_} {_} {A} f refl refl) refl refl) refl refl | inj₂ (A ∷ [] , refl , refl) | inj₁ (Ω₁ , refl , refl) | refl , refl | inj₂ (.(Γ₁ ++ _ ∷ Ω₁) , refl , refl) | inj₂ (Γ₁ , refl , refl) 
  rewrite cases++-inj₂ Γ₁ Δ₁ (Ω₁ ++ B ∷ Λ) A' |
          cases++-inj₂ (A ∷ []) Λ₀ [] B |
          cases++-inj₂ Γ₁ Δ₁ (Ω₁ ++ Λ) A' |
          snoc≡-refl Λ₀ A |
          cases++-inj₂ (Γ₁ ++ Ω₁) Δ₁ Λ B |
          cases++-inj₁ (Δ₁ ++ A ∷ Γ₁) Ω₁ Λ A' = refl
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {Δ₀} {.(Ω₁ ++ Λ)} {_} {A} {B} (ex {Γ = .[]} {.(Δ₀ ++ _ ∷ Ω₁)} {Λ} (ri2c f) refl eq₁) eq eq' | inj₂ (A ∷ [] , refl , p') | inj₁ (Ω₁ , refl , refl) = ⊥-elim ([]disj∷ Λ₀ p') 
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {.(Δ ++ Ω₁)} {Δ₁} {A'} {A} {B} (ex {Γ = .(_ ++ _ ∷ [])} {Δ} {.(Ω₁ ++ _ ∷ Δ₁)} (ex {Γ = Γ} {Δ₂} {Λ₂} f refl refl) refl eq₁) eq eq' | inj₂ (A ∷ [] , refl , p') | inj₂ (Ω₁ , refl , refl) with snoc≡ Γ Λ₀ p' | cases++ Δ Δ₂ (Ω₁ ++ A' ∷ Δ₁) Λ₂ eq₁
... | refl , refl | inj₁ (Γ₀ , refl , q') with cases++ Ω₁ Γ₀ Δ₁ Λ₂ (sym q')
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {.(Δ ++ Ω₁)} {.(Γ₁ ++ Λ₂)} {A'} {A} {B} (ex {_} {.(Λ₀ ++ A ∷ [])} {Δ} {.(Ω₁ ++ A' ∷ Γ₁ ++ Λ₂)} (ex {Γ = Λ₀} {.(Δ ++ B ∷ Ω₁ ++ A' ∷ Γ₁)} {Λ₂} {_} {_} {A} f refl refl) refl refl) refl refl | inj₂ (A ∷ [] , refl , refl) | inj₂ (Ω₁ , refl , refl) | refl , refl | inj₁ (.(Ω₁ ++ A' ∷ Γ₁) , refl , refl) | inj₁ (Γ₁ , refl , refl)
  rewrite cases++-inj₁ (Δ ++ B ∷ Ω₁) Γ₁ Λ₂ A' |
          cases++-inj₂ (A ∷ []) Λ₀ [] B |
          cases++-inj₁ (Δ ++ Ω₁) Γ₁ Λ₂ A' |
          snoc≡-refl Λ₀ A |
          cases++-inj₁ Δ (Ω₁ ++ Γ₁) Λ₂ B |
          cases++-inj₂ Ω₁ Δ (Γ₁ ++ A ∷ Λ₂) A' = refl
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {.(Δ ++ Γ₀ ++ Γ₁)} {Δ₁} {A'} {A} {B} (ex {_} {.(Λ₀ ++ A ∷ [])} {Δ} {.((Γ₀ ++ Γ₁) ++ A' ∷ Δ₁)} (ex {Γ = Λ₀} {.(Δ ++ B ∷ Γ₀)} {.(Γ₁ ++ A' ∷ Δ₁)} {_} {_} {A} f refl refl) refl refl) refl refl | inj₂ (A ∷ [] , refl , refl) | inj₂ (.(Γ₀ ++ Γ₁) , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₁ , refl , refl) 
  rewrite cases++-inj₂ Γ₁ (Δ ++ B ∷ Γ₀) Δ₁ A' |
          cases++-inj₂ (A ∷ []) Λ₀ [] B |
          cases++-inj₂ Γ₁ (Δ ++ Γ₀) Δ₁ A' |
          snoc≡-refl Λ₀ A |
          cases++-inj₁ Δ Γ₀ (Γ₁ ++ Δ₁) B |
          cases++-inj₂ (Γ₀ ++ A ∷ Γ₁) Δ Δ₁ A' = refl
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {.((Δ₂ ++ Γ₀) ++ Ω₁)} {Δ₁} {A'} {A} {B} (ex {_} {.(Λ₀ ++ _ ∷ [])} {.(Δ₂ ++ Γ₀)} {.(Ω₁ ++ A' ∷ Δ₁)} (ex {Γ = Λ₀} {Δ₂} {.(Γ₀ ++ B ∷ Ω₁ ++ A' ∷ Δ₁)} f refl refl) refl refl) refl refl | inj₂ (A ∷ [] , refl , refl) | inj₂ (Ω₁ , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ (Γ₀ ++ B ∷ Ω₁) Δ₂ Δ₁ A' | 
          cases++-inj₂ (A ∷ []) Λ₀ [] B | 
          cases++-inj₂ (Γ₀ ++ Ω₁) Δ₂ Δ₁ A' |
          snoc≡-refl Λ₀ A |
          cases++-inj₂ Γ₀ Δ₂ (Ω₁ ++ Δ₁) B |
          cases++-inj₂ Ω₁ (Δ₂ ++ A ∷ Γ₀) Δ₁ A' = refl
ex⊸r-c' {Λ₀ = Λ₀} {.[]} {.(Δ ++ Ω₁)} {Δ₁} {_} {A} {B} (ex {Γ = .[]} {Δ} {.(Ω₁ ++ _ ∷ Δ₁)} (ri2c f) refl eq₁) eq eq' | inj₂ (A ∷ [] , refl , p') | inj₂ (Ω₁ , refl , refl) = ⊥-elim ([]disj∷ Λ₀ p') 
ex⊸r-c' {Λ₀ = Λ₀} {Λ₁} {Δ₀} {Δ₁} {A = A} {B} (ex {Γ = Γ} {Δ} {Λ} f refl eq₁) eq eq' | inj₂ (D ∷ E ∷ Ω₀ , p , p') with cases++ Δ₀ Δ Δ₁ Λ eq'
... | inj₁ (Ω₁ , refl , refl) with inj∷ p
... | refl , r with inj∷ r
ex⊸r-c' {Λ₀ = Λ₀} {.(Ω₀ ++ _ ∷ [])} {Δ₀} {.(Ω₁ ++ Λ)} {A'} {D} {B} (ex {Γ = .(Λ₀ ++ D ∷ B ∷ Ω₀)} {.(Δ₀ ++ _ ∷ Ω₁)} {Λ} {A = A} f refl refl) refl refl | inj₂ (D ∷ B ∷ Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | refl , refl | refl , refl 
  rewrite cases++-inj₂ (D ∷ B ∷ Ω₀) Λ₀ [] A |
          cases++-inj₁ Δ₀ Ω₁ Λ A' = cong (λ x → ex {Γ = Λ₀ ++ B ∷ D ∷ Ω₀} {Δ₀ ++ Ω₁} x refl refl) (ex⊸r-c' {Δ₀ = Δ₀} f refl refl)
ex⊸r-c' {Λ₀ = Λ₀} {Λ₁} {.(Δ ++ Ω₁)} {Δ₁} {A = A} {B} (ex {Γ = .(Λ₀ ++ D ∷ E ∷ Ω₀)} {Δ} {.(Ω₁ ++ _ ∷ Δ₁)} f refl refl) eq refl | inj₂ (D ∷ E ∷ Ω₀ , p , refl) | inj₂ (Ω₁ , refl , refl) with inj∷ p
... | refl , r with inj∷ r
ex⊸r-c' {Λ₀ = Λ₀} {.(Ω₀ ++ _ ∷ [])} {.(Δ ++ Ω₁)} {Δ₁} {A'} {D} {B} (ex {_} {.(Λ₀ ++ D ∷ B ∷ Ω₀)} {Δ} {.(Ω₁ ++ _ ∷ Δ₁)} {A = A} f refl refl) refl refl | inj₂ (D ∷ B ∷ Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | refl , refl | refl , refl 
  rewrite cases++-inj₂ (D ∷ B ∷ Ω₀) Λ₀ [] A |
          cases++-inj₂ Ω₁ Δ Δ₁ A' = cong (λ x → ex {Γ = Λ₀ ++ B ∷ D ∷ Ω₀} x refl refl) (ex⊸r-c' {Δ₀ = Δ ++ A ∷ Ω₁} f refl refl)
ex⊸r-c' {Λ₀ = Λ₀} (ri2c f) eq eq' = ⊥-elim ([]disj∷ Λ₀ eq)

ex⊸r-c : {S : Stp} {Γ Δ Λ₀ Λ₁ : Cxt} {A' A B C : Fma}
     → (f : S ∣ Γ ؛ Δ ⊢c C) (eq : Γ ≡ Λ₀ ++ A ∷ B ∷ Λ₁ ++ A' ∷ [])
     →  ex-c' Λ₀ {Ψ = Λ₁} {A = A} {B} (⊸r-c'' {Γ = Λ₀ ++ A ∷ B ∷ Λ₁} {A = A'} f eq) refl ≡ ⊸r-c'' {Γ = Λ₀ ++ B ∷ A ∷ Λ₁} (ex-c' Λ₀ {Ψ = Λ₁ ++ A' ∷ []} f eq) refl

ex⊸r-c {Λ₀ = Λ₀} {Λ₁} {A' = A'} {A = A} {B = B} (ex {Γ = Γ} f refl eq₁) eq with cases++ Γ Λ₀ [] (A ∷ B ∷ Λ₁ ++ A' ∷ []) (sym eq)
... | inj₁ (Ω₀ , p , p') = ⊥-elim ([]disj∷ Ω₀ p')
... | inj₂ (Ω₀ , p , p') with snoc≡ (A ∷ B ∷ Λ₁) Ω₀ p
ex⊸r-c {Λ₀ = Λ₀} {Λ₁} {A' = A'} {A = A} {B = B} (ex {Γ = .(Λ₀ ++ A ∷ B ∷ Λ₁)} f refl refl) refl | inj₂ (.(A ∷ B ∷ Λ₁) , refl , refl) | refl , refl 
  rewrite snoc≡-refl (Λ₀ ++ A ∷ B ∷ Λ₁) A' |
          snoc≡-refl (Λ₀ ++ B ∷ A ∷ Λ₁) A' = ex⊸r-c' f refl refl
ex⊸r-c {Λ₀ = Λ₀} (ri2c f) eq = ⊥-elim ([]disj∷ Λ₀ eq)

ex⊸l₁-c-ri : {Γ Δ Λ Λ₀ Λ₁ : Cxt} {A B A' B' C : Fma}
         → (f : - ∣ Γ ؛ Δ ⊢c A') (g : just B' ∣ Λ ⊢ri C) (eq : Γ ≡ Λ₀ ++ A ∷ B ∷ Λ₁)
         → ex-c' Λ₀ (⊸l-c-ri f g) eq ≡ ⊸l-c-ri (ex-c' Λ₀ f eq) g

ex⊸l₁-c-ri {Λ₀ = Λ₀} {Λ₁ = Λ₁} {A = A} {B} (ex {Γ = Γ} {A = A₁} f refl eq₁) g eq with cases++ Γ Λ₀ [] (A ∷ B ∷ Λ₁) (sym eq)
... | inj₁ (Ω₀ , p , p') = ⊥-elim ([]disj∷ Ω₀ p')
... | inj₂ (D ∷ [] , p , p') with inj∷ p 
... | refl , q with inj∷ q 
ex⊸l₁-c-ri {Λ₀ = Λ₀} {Λ₁ = .[]} {D} {B} (ex {Γ = Γ} {Δ₁} {Λ₁} {A = B} (ex {Δ = Δ} {Λ} f eq' eq₂) refl eq₁) g eq | inj₂ (D ∷ [] , refl , p') | refl , refl | refl , refl with snoc≡ Γ (Λ₀ ++ D ∷ []) eq | cases++ Δ₁ Δ Λ₁ Λ eq₁
ex⊸l₁-c-ri {Λ₀ = Λ₀} {.[]} {D} {B} (ex {Γ = .(Λ₀ ++ D ∷ [])} {Δ₁} {.(Ω₁ ++ Λ)} (ex {Γ = Γ} {Δ = .(Δ₁ ++ B ∷ Ω₁)} {Λ} f eq' eq₂) refl refl) g eq | inj₂ (D ∷ [] , refl , refl) | refl , refl | refl , refl | refl , refl | inj₁ (Ω₁ , refl , refl) with snoc≡ Λ₀ Γ eq'
ex⊸l₁-c-ri {Λ = Λ₁} {Λ₀ = Λ₀} {.[]} {D} {B} (ex {_} {.(Λ₀ ++ D ∷ [])} {Δ₁} {.(Ω₁ ++ Λ)} (ex {Γ = Λ₀} {.(Δ₁ ++ B ∷ Ω₁)} {Λ} f refl refl) refl refl) g refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | refl , refl | refl , refl | inj₁ (Ω₁ , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (D ∷ []) Λ₀ [] B |
          snoc≡-refl Λ₀ D |
          cases++-inj₁ Δ₁ Ω₁ Λ B |
          cases++-inj₁ Δ₁ Ω₁ (Λ ++ Λ₁) B = refl
ex⊸l₁-c-ri {Λ₀ = Λ₀} {.[]} {D} {B} (ex {Γ = .(Λ₀ ++ D ∷ [])} {.(Δ ++ Ω₁)} {Λ₁} (ex {Γ = Γ} {Δ = Δ} {.(Ω₁ ++ B ∷ Λ₁)} f eq' refl) refl refl) g refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | refl , refl | refl , refl | inj₂ (Ω₁ , refl , refl) with snoc≡ Λ₀ Γ eq'
ex⊸l₁-c-ri {Λ = Λ} {Λ₀ = Λ₀} {.[]} {D} {B} (ex {_} {.(Λ₀ ++ D ∷ [])} {.(Δ ++ Ω₁)} {Λ₁} (ex {Γ = .Λ₀} {Δ = Δ} {.(Ω₁ ++ B ∷ Λ₁)} f refl refl) refl refl) g refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | refl , refl | refl , refl | inj₂ (Ω₁ , refl , refl) | refl , refl 
  rewrite cases++-inj₂ (D ∷ []) Λ₀ [] B |
          snoc≡-refl Λ₀ D |
          cases++-inj₂ Ω₁ Δ Λ₁ B |
          cases++-inj₂ Ω₁ Δ (Λ₁ ++ Λ) B = refl
ex⊸l₁-c-ri {Λ₀ = Λ₀} {Λ₁ = .[]} {D} {B} (ex {Γ = .[]} {A = B} (ri2c f) refl eq₁) g eq | inj₂ (D ∷ [] , refl , p') | refl , refl | refl , refl = ⊥-elim ([]disj∷ Λ₀ p')
ex⊸l₁-c-ri {Λ₀ = Λ₀} {Λ₁ = Λ₁} {A = A} {B} (ex {Γ = Γ} {A = A₁} f refl eq₁) g eq | inj₂ (D ∷ E ∷ Ω₀ , p , refl) with inj∷ p
... | refl , q with inj∷ q 
ex⊸l₁-c-ri {Λ = Λ} {Λ₀ = Λ₀} {Λ₁ = .(Ω₀ ++ A₁ ∷ [])} {D} {B} (ex {_} {.(Λ₀ ++ D ∷ B ∷ Ω₀)} {A = A₁} f refl refl) g refl | inj₂ (D ∷ B ∷ Ω₀ , refl , refl) | refl , refl | refl , refl 
  rewrite cases++-inj₂ (D ∷ B ∷ Ω₀) Λ₀ [] A₁ = cong (λ x → ex {Γ = Λ₀ ++ B ∷ D ∷ Ω₀} x refl refl) (ex⊸l₁-c-ri f g refl)
ex⊸l₁-c-ri {Λ₀ = Λ₀} (ri2c f) g eq = ⊥-elim ([]disj∷ Λ₀ eq)

ex⊸l₁-c : {Λ₀ Λ₁ Ω Δ : Cxt} {A B A' B' C : Fma}
      → (f : - ∣ Λ₀ ++ A ∷ B ∷ Λ₁ ؛ [] ⊢c A') (g : just B' ∣ Ω ؛ Δ ⊢c C)
      → ex-c Λ₀ (⊸l-c f g) ≡ ⊸l-c (ex-c Λ₀ f) g


ex⊸l₁-c {Λ₀} {Λ₁} {A = A} {B = B} f (ex {Γ = Γ} {A = A'} g refl refl) 
  rewrite cases++-inj₂ (A ∷ B ∷ Λ₁ ++ Γ) Λ₀ [] A' = cong (λ x → ex {Γ = Λ₀ ++ B ∷ A ∷ Λ₁ ++ Γ} x refl refl) (ex⊸l₁-c f g)
ex⊸l₁-c f (ri2c g) = ex⊸l₁-c-ri f g refl

ex⊸l₂-c : {Γ Λ Λ₀ Λ₁ Δ : Cxt} {A B A' B' C : Fma}
      → (f : - ∣ Γ ؛ [] ⊢c A') (g : just B' ∣ Λ ؛ Δ ⊢c C) (eq : Λ ≡ Λ₀ ++ A ∷ B ∷ Λ₁)
      → ex-c' (Γ ++ Λ₀) (⊸l-c f g) (cong (Γ ++_) eq) ≡ ⊸l-c f (ex-c' Λ₀ g eq)

ex⊸l₂-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B = B} f (ex {Γ = Γ} {A = A₁} g refl eq₁) eq with  cases++ Γ Λ₀ [] (A ∷ B ∷ Λ₁) (sym eq)
... | inj₁ (Ω₀ , p , p') = ⊥-elim ([]disj∷ Ω₀ p')
ex⊸l₂-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B = B} f (ex {Γ = Γ} {A = A₁} (ex g eq' eq₂) refl eq₁) eq | inj₂ (D ∷ [] , p , p') with inj∷ p
... | refl , q with inj∷ q
ex⊸l₂-c {Λ₀ = Λ₀} {.[]} {_} {D} {B = B} f (ex {Γ = .(Λ₀ ++ D ∷ [])} {Δ₁} {Λ₁} {A = B} (ex {Γ = Γ} {Δ = Δ} {Λ} g eq' eq₂) refl eq₁) eq | inj₂ (D ∷ [] , refl , refl) | refl , refl | refl , refl with snoc≡ Λ₀ Γ eq' | cases++ Δ₁ Δ Λ₁ Λ eq₁
ex⊸l₂-c {Γ = Γ} {Λ₀ = Λ₀} {.[]} {_} {D} {B = B} f (ex {_} {.(Λ₀ ++ D ∷ [])} {Δ₁} {.(Ω₁ ++ Λ)} (ex {Γ = .Λ₀} {Δ = .(Δ₁ ++ B ∷ Ω₁)} {Λ} g refl refl) refl refl) refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | refl , refl | refl , refl | inj₁ (Ω₁ , refl , refl) 
  rewrite cases++-inj₂ (D ∷ []) (Γ ++ Λ₀) [] B |
          snoc≡-refl Λ₀ D |
          cases++-inj₁ Δ₁ Ω₁ Λ B |
          snoc≡-refl (Γ ++ Λ₀) D = refl
ex⊸l₂-c {Γ = Γ} {Λ₀ = Λ₀} {.[]} {_} {D} {B = B} f (ex {_} {.(Λ₀ ++ D ∷ [])} {.(Δ ++ Ω₁)} {Λ₁} (ex {Γ = .Λ₀} {Δ = Δ} {.(Ω₁ ++ B ∷ Λ₁)} g refl refl) refl refl) refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | refl , refl | refl , refl | inj₂ (Ω₁ , refl , refl) 
  rewrite cases++-inj₂ (D ∷ []) (Γ ++ Λ₀) [] B |
          snoc≡-refl (Γ ++ Λ₀) D |
          cases++-inj₂ Ω₁ Δ Λ₁ B |
          snoc≡-refl Λ₀ D |
          cases++-inj₂ Ω₁ Δ Λ₁ B = refl
ex⊸l₂-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B = B} f (ex {Γ = .[]} {A = A₁} (ri2c f₁) refl eq₁) eq | inj₂ (D ∷ [] , p , p') = ⊥-elim ([]disj∷ Λ₀ p')
ex⊸l₂-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B = B} f (ex {Γ = Γ} {A = A₁} g refl eq₁) eq | inj₂ (D ∷ E ∷ Ω₀ , p , p') with inj∷ p 
... | refl , q with inj∷ q 
ex⊸l₂-c {Γ = Γ} {Λ₀ = Λ₀} {.(Ω₀ ++ A₁ ∷ [])} {_} {D} {B = B} f (ex {Γ = .(Λ₀ ++ D ∷ B ∷ Ω₀)} {A = A₁} g refl refl) refl | inj₂ (D ∷ B ∷ Ω₀ , refl , refl) | refl , refl | refl , refl 
  rewrite cases++-inj₂ (D ∷ B ∷ Ω₀) (Γ ++ Λ₀) [] A₁ = cong (λ x → ex {Γ = Γ ++ Λ₀ ++ B ∷ D ∷ Ω₀} x refl refl) (ex⊸l₂-c f g refl)
ex⊸l₂-c {Λ₀ = Λ₀} f (ri2c g) eq = ⊥-elim ([]disj∷ Λ₀ eq)


ex⊗l-c : {Γ Δ Λ₀ Λ₁ : Cxt} {A' B' A B C : Fma}
      → (f : just A' ∣ Γ ؛ Δ ⊢c C) (eq : Γ ≡ B' ∷ Λ₀ ++ A ∷ B ∷ Λ₁ )
      → ex-c' Λ₀ (⊗l-c' f eq) refl ≡ ⊗l-c' (ex-c' (_ ∷ Λ₀) f eq) refl

ex⊗l-c {Λ₀ = Λ₀} {Λ₁} {B' = B'} {A} {B} (ex {Γ = Γ} {A = A₁} f refl eq₁) eq with cases++ Γ (B' ∷ Λ₀) [] (A ∷ B ∷ Λ₁) (sym eq)
... | inj₁ (Ω₀ , p , p') = ⊥-elim ([]disj∷ Ω₀ p')
ex⊗l-c {Λ₀ = Λ₀} {.[]} {B' = B'} {D} {B} (ex {Γ = .(Γ ++ _ ∷ [])} {Δ₁} {Λ₁} {A = B} (ex {Γ = Γ} {Δ} {Λ} f refl refl) refl eq₁) eq | inj₂ (D ∷ [] , refl , p') with snoc≡ Γ (B' ∷ Λ₀) p' | cases++ Δ₁ Δ Λ₁ Λ eq₁
ex⊗l-c {Λ₀ = Λ₀} {.[]} {B' = B'} {D} {B} (ex {_} {.((B' ∷ Λ₀) ++ _ ∷ [])} {Δ₁} {.(Ω₁ ++ Λ)} (ex {Γ = .(B' ∷ Λ₀)} {.(Δ₁ ++ B ∷ Ω₁)} {Λ} f refl refl) refl refl) refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | inj₁ (Ω₁ , refl , refl)
  rewrite cases++-inj₂ (D ∷ []) Λ₀ [] B |
          snoc≡-refl Λ₀ D |
          cases++-inj₁ Δ₁ Ω₁ Λ B = refl
ex⊗l-c {Λ₀ = Λ₀} {.[]} {B' = B'} {D} {B} (ex {_} {.((B' ∷ Λ₀) ++ _ ∷ [])} {.(Δ ++ Ω₁)} {Λ₁} (ex {Γ = .(B' ∷ Λ₀)} {Δ} {.(Ω₁ ++ B ∷ Λ₁)} f refl refl) refl refl) refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | inj₂ (Ω₁ , refl , refl) 
  rewrite cases++-inj₂ (D ∷ []) Λ₀ [] B |
          snoc≡-refl Λ₀ D |
          cases++-inj₂ Ω₁ Δ Λ₁ B = refl
ex⊗l-c {Λ₀ = Λ₀} {.(Ω₀ ++ A₁ ∷ [])} {B' = B'} {A} {B} (ex {Γ = .(B' ∷ Λ₀ ++ A ∷ B ∷ Ω₀)} {A = A₁} f refl refl) refl | inj₂ (A ∷ B ∷ Ω₀ , refl , refl) 
  rewrite cases++-inj₂ (A ∷ B ∷ Ω₀) Λ₀ [] A₁ = cong (λ x → ex {Γ = Λ₀ ++ B ∷ A ∷ Ω₀} x refl refl) (ex⊗l-c f refl)

ex⊗r₁-c-ri : {S : Stp} {Γ Λ₀ Λ₁ Δ Λ : Cxt} {A B C D : Fma}
      → (f : S ∣ Γ ؛ Δ ⊢c C) (g : - ∣ Λ ⊢ri D ) (eq : Γ ≡ Λ₀ ++ A ∷ B ∷ Λ₁)
      → ex-c' Λ₀ (⊗r-c-ri f g) eq ≡ ⊗r-c-ri (ex-c' Λ₀ f eq) g

ex⊗r₁-c-ri {Λ₀ = Λ₀} {Λ₁} {A = A} {B} (ex {Γ = Γ} {A = A₁} f refl eq₁) g eq with cases++ Γ Λ₀ [] (A ∷ B ∷ Λ₁) (sym eq)
... | inj₁ (Ω₀ , p , p') = ⊥-elim ([]disj∷ Ω₀ p')
ex⊗r₁-c-ri {Λ₀ = Λ₀} {.[]} {A = A} {B} (ex {Γ = .(Γ ++ _ ∷ [])} {Δ₁} {Λ₁} {A = B} (ex {Γ = Γ} {Δ} {Λ} f refl refl) refl eq₁) g eq | inj₂ (A ∷ [] , refl , p') with snoc≡ Γ Λ₀ p' | cases++ Δ₁ Δ Λ₁ Λ eq₁
ex⊗r₁-c-ri {Λ₀ = Λ₀} {.[]} {Λ = Λ₁} {A} {B} (ex {_} {.(Λ₀ ++ _ ∷ [])} {Δ₁} {.(Ω₀ ++ Λ)} (ex {Γ = .Λ₀} {.(Δ₁ ++ B ∷ Ω₀)} {Λ} f refl refl) refl refl) g refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₁ (Ω₀ , refl , refl) 
  rewrite cases++-inj₂ (A ∷ []) Λ₀ [] B |
          snoc≡-refl Λ₀ A |
          cases++-inj₁ Δ₁ Ω₀ (Λ ++ Λ₁) B = refl
ex⊗r₁-c-ri {Λ₀ = Λ₀} {.[]} {Λ = Λ} {A} {B} (ex {_} {.(Λ₀ ++ _ ∷ [])} {.(Δ ++ Ω₀)} {Λ₁} (ex {Γ = .Λ₀} {Δ} {.(Ω₀ ++ B ∷ Λ₁)} f refl refl) refl refl) g refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₂ (Ω₀ , refl , refl) 
  rewrite cases++-inj₂ (A ∷ []) Λ₀ [] B |
          snoc≡-refl Λ₀ A | 
          cases++-inj₂ Ω₀ Δ (Λ₁ ++ Λ) B = refl
ex⊗r₁-c-ri {Λ₀ = Λ₀} {.[]} {A = A} {B} (ex {Γ = .[]} {A = .B} (ri2c f) refl eq₁) g eq | inj₂ (A ∷ [] , refl , p') = ⊥-elim ([]disj∷ Λ₀ p')
ex⊗r₁-c-ri {Λ₀ = Λ₀} {.(Ω₀ ++ A₁ ∷ [])} {Λ = Λ} {A = A} {B} (ex {Γ = .(Λ₀ ++ A ∷ B ∷ Ω₀)} {A = A₁} f refl refl) g refl | inj₂ (A ∷ B ∷ Ω₀ , refl , refl) 
  rewrite cases++-inj₂ (A ∷ B ∷ Ω₀) Λ₀ [] A₁ = cong (λ x → ex {Γ = Λ₀ ++ B ∷ A ∷ Ω₀} x refl refl) (ex⊗r₁-c-ri f g refl)
ex⊗r₁-c-ri {Λ₀ = Λ₀} (ri2c f) g eq = ⊥-elim ([]disj∷ Λ₀ eq)

ex⊗r₁-c : {S : Stp} {Λ₀ Λ₁ Ω Δ : Cxt} {A B C D : Fma}
      → (f : S ∣ Λ₀ ++ A ∷ B ∷ Λ₁ ؛ [] ⊢c C) (g : - ∣ Ω ؛ Δ ⊢c D )
      → ex-c Λ₀ (⊗r-c f g) ≡ ⊗r-c (ex-c Λ₀ f) g

ex⊗r₁-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B = B} f (ex {Γ = Γ} {A = A'} g refl refl) 
  rewrite cases++-inj₂ (A ∷ B ∷ Λ₁ ++ Γ) Λ₀ [] A' = cong (λ x → ex {Γ = Λ₀ ++ B ∷ A ∷ Λ₁ ++ Γ} x refl refl) (ex⊗r₁-c f g)
ex⊗r₁-c f (ri2c g) = ex⊗r₁-c-ri f g refl

ex⊗r₂-c : {S : Stp} {Γ Λ Λ₀ Λ₁ Δ : Cxt} {A B C D : Fma}
       → (f : S ∣ Γ ؛ [] ⊢c C) (g : - ∣ Λ ؛ Δ ⊢c D) (eq : Λ ≡ Λ₀ ++ A ∷ B ∷ Λ₁)
       → ex-c' (Γ ++ Λ₀) (⊗r-c f g) (cong (Γ ++_) eq) ≡ ⊗r-c f (ex-c' Λ₀ g eq)
ex⊗r₂-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B} f (ex {Γ = Γ} {A = A₁} g refl eq₁) eq with cases++ Γ Λ₀ [] (A ∷ B ∷ Λ₁) (sym eq)
... | inj₁ (Ω₀ , p , p') = ⊥-elim ([]disj∷ Ω₀ p')
ex⊗r₂-c {Λ₀ = Λ₀} {.[]} {A = D} {B} f (ex {Γ = .(Γ ++ _ ∷ [])} {Δ₁} {Λ₁} {A = B} (ex {Γ = Γ} {Δ = Δ} {Λ} g refl refl) refl eq₁) eq | inj₂ (D ∷ [] , refl , p') with snoc≡ Γ Λ₀ p' | cases++ Δ₁ Δ Λ₁ Λ eq₁
ex⊗r₂-c {Γ = Γ} {Λ₀ = Λ₀} {.[]} {_} {D} {B} f (ex {_} {.(Λ₀ ++ _ ∷ [])} {Δ₁} {.(Ω₀ ++ Λ)} (ex {Γ = .Λ₀} {Δ = .(Δ₁ ++ B ∷ Ω₀)} {Λ} g refl refl) refl refl) refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | inj₁ (Ω₀ , refl , refl) 
  rewrite cases++-inj₂ (D ∷ []) (Γ ++ Λ₀) [] B |
          snoc≡-refl (Γ ++ Λ₀) D |
          cases++-inj₁ Δ₁ Ω₀ Λ B = refl
ex⊗r₂-c {Γ = Γ} {Λ₀ = Λ₀} {.[]} {_} {D} {B} f (ex {_} {.(Λ₀ ++ _ ∷ [])} {.(Δ ++ Ω₀)} {Λ₁} (ex {Γ = .Λ₀} {Δ = Δ} {.(Ω₀ ++ B ∷ Λ₁)} g refl refl) refl refl) refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | inj₂ (Ω₀ , refl , refl) 
  rewrite cases++-inj₂ (D ∷ []) (Γ ++ Λ₀) [] B |
          snoc≡-refl (Γ ++ Λ₀) D |
          cases++-inj₂ Ω₀ Δ Λ₁ B = refl
ex⊗r₂-c {Λ₀ = Λ₀} {Λ₁} {A = A} {B} f (ex {Γ = .[]} {A = A₁} (ri2c g) refl eq₁) eq | inj₂ (D ∷ [] , refl , p') = ⊥-elim ([]disj∷ Λ₀ p')
ex⊗r₂-c {Γ = Γ} {Λ₀ = Λ₀} {.(Ω₀ ++ A₁ ∷ [])} {A = A} {B} f (ex {Γ = .(Λ₀ ++ A ∷ B ∷ Ω₀)} {A = A₁} g refl refl) refl | inj₂ (A ∷ B ∷ Ω₀ , refl , refl) 
  rewrite cases++-inj₂ (A ∷ B ∷ Ω₀) (Γ ++ Λ₀) [] A₁ = cong (λ x → ex {Γ = Γ ++ Λ₀ ++ B ∷ A ∷ Ω₀} x refl refl) (ex⊗r₂-c f g refl)
ex⊗r₂-c {Λ₀ = Λ₀} f (ri2c g) eq = ⊥-elim ([]disj∷ Λ₀ eq)

exCexC' : ∀{S Φ₁ Φ₂ Φ₃ Λ Δ A B A' B' C} (f : S ∣ Λ ؛ Δ ⊢c C)
  → (eq : Λ ≡ Φ₁ ++ A ∷ B ∷ Φ₂ ++ A' ∷ B' ∷ Φ₃)
  → ex-c' (Φ₁ ++ B ∷ A ∷ Φ₂) (ex-c' Φ₁ f eq) refl
    ≡ ex-c' Φ₁ (ex-c' (Φ₁ ++ A ∷ B ∷ Φ₂) f eq) refl
exCexC' {Φ₁ = Φ₁} {Φ₂} {Φ₃} {A = A} {B} {A'} {B'} (ex {Γ = Φ} f refl eq') eq with cases++ Φ Φ₁ [] (A ∷ B ∷ Φ₂ ++ A' ∷ B' ∷ Φ₃) (sym eq)
... | inj₁ (Ψ₀ , p , q) = ⊥-elim ([]disj∷ Ψ₀ q)
... | inj₂ (x ∷ [] , p , q) = ⊥-elim ([]disj∷ Φ₂ (sym (inj∷ (inj∷ p .proj₂) .proj₂)))
... | inj₂ (x ∷ x₁ ∷ Ψ₀ , p , q) with cases++ Ψ₀ Φ₂ [] (A' ∷ B' ∷ Φ₃) (inj∷ (inj∷ p .proj₂) .proj₂)
... | inj₁ (Ψ₀' , p' , q') = ⊥-elim ([]disj∷ Ψ₀' q')
exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {A = x} {x₁} {A'} {B'} (ex {Γ = .(Φ ++ A ∷ [])} {Γ} {Δ} (ex {Γ = Φ} {Γ₁} {Δ₁} {A = A} f refl refl) refl eq') eq | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ []) , refl , q) | inj₂ (A' ∷ [] , refl , refl) with snoc≡ Φ (Φ₁ ++ _ ∷ _ ∷ Φ₂) q | cases++ Γ Γ₁ Δ Δ₁ eq'
exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {_} {_} {x} {x₁} {A'} {B'} (ex {_} {.((Φ₁ ++ x ∷ x₁ ∷ Φ₂) ++ A' ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Γ = .(Φ₁ ++ x ∷ x₁ ∷ Φ₂)} {.(Γ ++ B' ∷ Γ₀)} {Δ₁} {A = A'} f refl refl) refl refl) refl | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ []) , refl , refl) | inj₂ (A' ∷ [] , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x₁ ∷ x ∷ Φ₂) [] B' |
          cases++-inj₂ (x₁ ∷ x ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x ∷ x₁ ∷ Φ₂) [] B' |
          snoc≡-refl (Φ₁ ++ x₁ ∷ x ∷ Φ₂) A' | snoc≡-refl (Φ₁ ++ x ∷ x₁ ∷ Φ₂) A' |
          cases++-inj₁ Γ Γ₀ Δ₁ B' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂ ++ B' ∷ []) Φ₁ [] A' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] B' = refl
exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {_} {_} {x} {x₁} {A'} {B'} (ex {_} {.((Φ₁ ++ x ∷ x₁ ∷ Φ₂) ++ A' ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Γ = .(Φ₁ ++ x ∷ x₁ ∷ Φ₂)} {Γ₁} {.(Γ₀ ++ B' ∷ Δ)} {A = .A'} f refl refl) refl refl) refl | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ []) , refl , refl) | inj₂ (A' ∷ [] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x₁ ∷ x ∷ Φ₂) [] B' |
          cases++-inj₂ (x₁ ∷ x ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x ∷ x₁ ∷ Φ₂) [] B' |
          snoc≡-refl (Φ₁ ++ x₁ ∷ x ∷ Φ₂) A' | snoc≡-refl (Φ₁ ++ x ∷ x₁ ∷ Φ₂) A' |
          cases++-inj₂ Γ₀ Γ₁ Δ B' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂ ++ B' ∷ []) Φ₁ [] A' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] B' = refl
exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {A = A} {B} {A'} {B'} (ex {Γ = .[]} (ri2c f) refl eq') eq | inj₂ (x ∷ x₁ ∷ Ψ₀ , p , q) | inj₂ (A' ∷ [] , refl , q') = ⊥-elim ([]disj∷ Φ₁ q)
exCexC' {Φ₁ = Φ₁} {Φ₂} {.(Ψ₀' ++ A ∷ [])} {A = x} {x₁} {A'} {B'} (ex {Γ = .(Φ₁ ++ x ∷ x₁ ∷ Φ₂ ++ A' ∷ B' ∷ Ψ₀')} {Γ} {Δ} {A = A} f refl refl) refl | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ B' ∷ Ψ₀') , refl , refl) | inj₂ (A' ∷ B' ∷ Ψ₀' , refl , refl)
  rewrite cases++-inj₂ (A' ∷ B' ∷ Ψ₀') (Φ₁ ++ x ∷ x₁ ∷ Φ₂) [] A | cases++-inj₂ (x ∷ x₁ ∷ Φ₂ ++ B' ∷ A' ∷ Ψ₀') Φ₁ [] A |
          cases++-inj₂ (A' ∷ B' ∷ Ψ₀') (Φ₁ ++ x₁ ∷ x ∷ Φ₂) [] A | cases++-inj₂ (x₁ ∷ x ∷ Φ₂ ++ B' ∷ A' ∷ Ψ₀') Φ₁ [] A =
            cong (λ y → ex {Γ = Φ₁ ++ _ ∷ _ ∷ Φ₂ ++ _ ∷ _ ∷ Ψ₀'} {Γ} {Δ} y refl refl) (exCexC' f refl)
exCexC' {Φ₁ = Φ₁} (ri2c f) eq = ⊥-elim ([]disj∷ Φ₁ eq)

exC-iso' : ∀{S Φ Ψ Λ Δ A B C} (f : S ∣ Λ ؛ Δ ⊢c C)
  → (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
  → ex-c' Φ (ex-c' Φ f eq) refl ≡ subst (λ x → S ∣ x ؛ Δ ⊢c C) eq f
exC-iso' {Φ = Φ} {Ψ} {A = A} {B} (ex {Γ = Φ₁} f refl eq') eq with cases++ Φ₁ Φ [] (A ∷ B ∷ Ψ) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
exC-iso' {Φ = Φ} {A = A} {B} (ex {Δ = Γ} {Δ} (ex {Γ = Φ₁} {Δ = Γ₁} {Δ₁} f refl refl) refl eq') eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ Φ q | cases++ Γ Γ₁ Δ Δ₁ eq'
exC-iso' {Φ = Φ} {A = A} {B} (ex {Δ = Γ} (ex {Γ = Φ} {Λ = Δ₁} f refl refl) refl refl) refl | inj₂ (A ∷ [] , refl , q) | refl , refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (B ∷ []) Φ [] A | snoc≡-refl Φ B | cases++-inj₂ Γ₀ Γ Δ₁ A = refl
exC-iso' {Φ = Φ} {A = A} {B} (ex {Λ = Δ} (ex {Δ = Γ₁} f refl refl) refl refl) refl | inj₂ (A ∷ [] , refl , q) | refl , refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (B ∷ []) Φ [] A | snoc≡-refl Φ B | cases++-inj₁ Γ₁ Γ₀ Δ A = refl
exC-iso' {Φ = Φ} (ex (ri2c f) refl eq') eq | inj₂ (A ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
exC-iso' {Φ = Φ} {A = A} {B} (ex {A = A₁} f refl refl) refl | inj₂ (A ∷ B ∷ Φ₀ , refl , refl)
  rewrite cases++-inj₂ (B ∷ A ∷ Φ₀) Φ [] A₁ = cong (λ y → ex {Γ = Φ ++ A ∷ B ∷ Φ₀} y refl refl) (exC-iso' f refl)
exC-iso' {Φ = Φ} (ri2c f) eq = ⊥-elim ([]disj∷ Φ eq)

exC-iso : ∀{S Φ Ψ Δ A B C} (f : S ∣ Φ ++ A ∷ B ∷ Ψ ؛ Δ ⊢c C)
  → ex-c Φ (ex-c Φ f) ≡ f
exC-iso f = exC-iso' f refl

exC-braid : ∀{S Φ A B C Λ Ψ Δ D}
  → (f : S ∣ Λ ؛ Δ ⊢c D)
  → (eq : Λ ≡ Φ ++ A ∷ B ∷ C ∷ Ψ)
  → ex-c Φ (ex-c (Φ ++ B ∷ []) (ex-c' Φ f eq))
    ≡ ex-c (Φ ++ C ∷ []) (ex-c Φ (ex-c' (Φ ++ A ∷ []) f eq))
exC-braid {Φ = Φ} {A} {B} {C} {Ψ = Ψ} (ex {Γ = Φ₁} f refl eq₁) eq with cases++ Φ₁ Φ [] (A ∷ B ∷ C ∷ Ψ) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
exC-braid {Φ = Φ} {A} {B} {C} {Ψ = .[]} (ex {Γ = .((Φ₁ ++ _ ∷ []) ++ _ ∷ [])} (ex (ex {Γ = Φ₁} f refl refl) refl eq₂) refl eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , q) with snoc≡ (Φ₁ ++ _ ∷ []) (Φ ++ A ∷ []) q
... | q' , refl with snoc≡ Φ₁ Φ q'
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ _ ∷ []) ++ B ∷ [])} {Γ} {Δ} (ex {Δ = Γ₁} {Δ₁} (ex {Γ = Φ} f refl refl) refl eq₂) refl eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , refl) | q' , refl | refl , refl with cases++ Γ Γ₁ Δ Δ₁ eq₁
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Δ = .(Γ ++ C ∷ Γ₀)} {Δ₁} (ex {Γ = Φ} {Γ₁} {Δ} f refl refl) refl eq₂) refl refl) eq | inj₂ (A ∷ B ∷ [] , refl , refl) | q' , refl | refl , refl | inj₁ (Γ₀ , refl , refl) with cases++ (Γ ++ C ∷ Γ₀) Γ₁ Δ₁ Δ eq₂
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {Γ} {.(Γ₀ ++ Γ₀' ++ Δ)} (ex {_} {_} {.(Γ ++ C ∷ Γ₀)} {.(Γ₀' ++ Δ)} (ex {Γ = Φ} {.(Γ ++ C ∷ Γ₀ ++ B ∷ Γ₀')} {Δ} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C |
          snoc≡-refl Φ A | cases++-inj₁ (Γ ++ C ∷ Γ₀) Γ₀' Δ B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₁ Γ (Γ₀ ++ Γ₀') Δ C |
          cases++-inj₂ (B ∷ C ∷ []) Φ [] A | cases++-inj₂ (B ∷ []) Φ [] C |
          snoc≡-refl Φ B | cases++-inj₁ Γ Γ₀ (Γ₀' ++ A ∷ Δ) C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₁ Γ Γ₀ (Γ₀' ++ Δ) C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) Φ [] C | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B |
          snoc≡-refl Φ A | cases++-inj₁ Γ (Γ₀ ++ B ∷ Γ₀') Δ C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₁ (Γ ++ Γ₀) Γ₀' Δ B = refl
... | inj₂ (Γ₀' , refl , q) with cases++ Γ Γ₁ Γ₀ Γ₀' (sym q)
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {Γ} {.((Γ₀'' ++ Γ₀') ++ Δ₁)} (ex {_} {_} {.(Γ ++ C ∷ Γ₀'' ++ Γ₀')} {Δ₁} (ex {Γ = Φ} {.(Γ ++ C ∷ Γ₀'')} {.(Γ₀' ++ B ∷ Δ₁)} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₁ (.(Γ₀'' ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) | inj₁ (Γ₀'' , refl , refl) 
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C |
          snoc≡-refl Φ A | cases++-inj₂ Γ₀' (Γ ++ C ∷ Γ₀'') Δ₁ B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₁ Γ Γ₀'' (Γ₀' ++ Δ₁) C |
          cases++-inj₂ (B ∷ C ∷ []) Φ [] A | cases++-inj₂ (B ∷ []) Φ [] C |
          snoc≡-refl Φ B | cases++-inj₁ Γ (Γ₀'' ++ A ∷ Γ₀') Δ₁ C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₁ Γ (Γ₀'' ++ Γ₀') Δ₁ C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B | cases++-inj₂ (A ∷ []) Φ [] C |
          snoc≡-refl Φ A | cases++-inj₁ Γ Γ₀'' (Γ₀' ++ B ∷ Δ₁) C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₂ Γ₀' (Γ ++ Γ₀'') Δ₁ B = refl
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀'')} {.(Γ₀ ++ Δ₁)} (ex {_} {_} {.((Γ₁ ++ Γ₀'') ++ C ∷ Γ₀)} {Δ₁} (ex {Γ = Φ} {Γ₁} {.((Γ₀'' ++ C ∷ Γ₀) ++ B ∷ Δ₁)} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₁ (Γ₀ , refl , refl) | inj₂ (.(Γ₀'' ++ C ∷ Γ₀) , refl , refl) | inj₂ (Γ₀'' , refl , refl) 
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₂ (Γ₀'' ++ C ∷ Γ₀) Γ₁ Δ₁ B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₂ Γ₀'' Γ₁ (Γ₀ ++ Δ₁) C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
          cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₁ (Γ₁ ++ A ∷ Γ₀'') Γ₀ Δ₁ C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₁ (Γ₁ ++ Γ₀'') Γ₀ Δ₁ C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) Φ [] C | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B |
          snoc≡-refl Φ A | cases++-inj₂ Γ₀'' Γ₁ (Γ₀ ++ B ∷ Δ₁) C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₂ (Γ₀'' ++ Γ₀) Γ₁ Δ₁ B = refl
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Δ = Γ₁} {.(Γ₀ ++ C ∷ Δ)} (ex {Γ = Φ} {Γ} {Δ₁} f refl refl) refl eq₂) refl refl) eq | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (Γ₀ , refl , refl) with cases++ Γ₁ Γ (Γ₀ ++ C ∷ Δ) Δ₁ eq₂
... | inj₁ (Γ₀' , refl , q) with cases++ Γ₀ Γ₀' Δ Δ₁ (sym q)
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀)} {.(Γ₀'' ++ Δ₁)} (ex {Δ = Γ₁} {.(Γ₀ ++ C ∷ Γ₀'' ++ Δ₁)} (ex {Γ = Φ} {.(Γ₁ ++ B ∷ Γ₀ ++ C ∷ Γ₀'')} {Δ₁} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (Γ₀ , refl , refl) | inj₁ (.(Γ₀ ++ C ∷ Γ₀'') , refl , refl) | inj₁ (Γ₀'' , refl , refl) 
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₁ Γ₁ (Γ₀ ++ C ∷ Γ₀'') Δ₁ B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₁ (Γ₁ ++ Γ₀) Γ₀'' Δ₁ C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
          cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₂ Γ₀ Γ₁ (Γ₀'' ++ A ∷ Δ₁) C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₂ Γ₀ Γ₁ (Γ₀'' ++ Δ₁) C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B | cases++-inj₂ (A ∷ []) Φ [] C |
          snoc≡-refl Φ A | cases++-inj₁ (Γ₁ ++ B ∷ Γ₀) Γ₀'' Δ₁ C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₁ Γ₁ (Γ₀ ++ Γ₀'') Δ₁ B = refl
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀' ++ Γ₀'')} {Δ} (ex {Δ = Γ₁} {.((Γ₀' ++ Γ₀'') ++ C ∷ Δ)} (ex {Γ = Φ} {.(Γ₁ ++ B ∷ Γ₀')} {.(Γ₀'' ++ C ∷ Δ)} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (.(Γ₀' ++ Γ₀'') , refl , refl) | inj₁ (Γ₀' , refl , refl) | inj₂ (Γ₀'' , refl , refl)
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₁ Γ₁ Γ₀' (Γ₀'' ++ C ∷ Δ) B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₂ Γ₀'' (Γ₁ ++ Γ₀') Δ C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
          cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₂ (Γ₀' ++ A ∷ Γ₀'') Γ₁ Δ C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₂ (Γ₀' ++ Γ₀'') Γ₁ Δ C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) Φ [] C | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B |
          snoc≡-refl Φ A | cases++-inj₂ (Γ₀'') (Γ₁ ++ B ∷ Γ₀') Δ C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₁ Γ₁ Γ₀' (Γ₀'' ++ Δ) B = refl
exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.((Γ ++ Γ₀') ++ Γ₀)} {Δ} (ex {Δ = .(Γ ++ Γ₀')} {.(Γ₀ ++ C ∷ Δ)} (ex {Γ = Φ} {Γ} {.(Γ₀' ++ B ∷ Γ₀ ++ C ∷ Δ)} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) 
  rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₂ Γ₀' Γ (Γ₀ ++ C ∷ Δ) B |
          snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₂ (Γ₀' ++ Γ₀) Γ Δ C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
          cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₂ Γ₀ (Γ ++ A ∷ Γ₀') Δ C |
          cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₂ Γ₀ (Γ ++ Γ₀') Δ C |
          cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B | cases++-inj₂ (A ∷ []) Φ [] C |
          snoc≡-refl Φ A | cases++-inj₂ (Γ₀' ++ B ∷ Γ₀) Γ Δ C |
          snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₂ Γ₀' Γ (Γ₀ ++ Δ) B = refl
exC-braid {Φ = x ∷ Φ} {A} {B} {C} {Ψ = .[]} (ex {Γ = .([] ++ _ ∷ [])} (ex (ri2c f) refl eq₂) refl eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ (inj∷ q .proj₂))
exC-braid {Φ = Φ} {A} {B} {C} {Ψ = .[]} (ex {Γ = .[]} (ri2c f) refl eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
exC-braid {Φ = Φ} {A} {B} {C} {Ψ = .(Φ₀ ++ A₁ ∷ [])} (ex {Γ = .(Φ ++ A ∷ B ∷ C ∷ Φ₀)} {Γ} {Δ} {A = A₁} f refl refl) refl | inj₂ (A ∷ B ∷ C ∷ Φ₀ , refl , refl) 
  rewrite cases++-inj₂ (B ∷ C ∷ Φ₀) (Φ ++ A ∷ []) [] A₁ | cases++-inj₂ (A ∷ C ∷ B ∷ Φ₀) Φ [] A₁ |
          cases++-inj₂ (C ∷ A ∷ B ∷ Φ₀) (Φ ++ C ∷ []) [] A₁ | cases++-inj₂ (A ∷ C ∷ Φ₀) (Φ ++ B ∷ []) [] A₁ |
          cases++-inj₂ (B ∷ C ∷ A ∷ Φ₀) Φ [] A₁ | cases++-inj₂ (A ∷ B ∷ Φ₀) (Φ ++ C ∷ []) [] A₁ =
          cong (λ x → ex {Γ = Φ ++ C ∷ B ∷ A ∷ Φ₀} {Γ}{Δ} x refl refl) (exC-braid f refl)
exC-braid {Φ = Φ} (ri2c f) eq = ⊥-elim ([]disj∷ Φ eq)

-- ̄≗ equivalent derivations are equal in focused calculus

eqfocus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              {f g : S ∣ Γ ⊢ C} → f ≗ g → focus f ≡ focus g
eqfocus refl = refl
eqfocus (~ p) = sym (eqfocus p)
eqfocus (p ≗∙ p₁) = trans (eqfocus p) (eqfocus p₁)
eqfocus (pass p) = cong pass-c  (eqfocus p)
eqfocus (Il p) = cong Il-c (eqfocus p)
eqfocus (⊸r p) = cong ⊸r-c (eqfocus p)
eqfocus (⊸l p p₁) = cong₂ ⊸l-c (eqfocus p) (eqfocus p₁)
eqfocus (⊗l p) = cong ⊗l-c (eqfocus p)
eqfocus (⊗r p p₁) = cong₂ ⊗r-c (eqfocus p) (eqfocus p₁)
eqfocus axI = refl
eqfocus ax⊸ = refl
eqfocus ax⊗ = refl
eqfocus (⊸rpass {f = f}) = ⊸rpass-c (focus f) refl
eqfocus (⊸rIl {f = f}) = ⊸rIl-c (focus f) refl
eqfocus (⊸r⊸l {f = f} {g}) =  ⊸r⊸l-c (focus f) (focus g) refl refl
eqfocus (⊸r⊗l {f = f}) = ⊸r⊗l-c (focus f) refl
eqfocus (⊗rpass {f = f} {g}) = ⊗rpass-c (focus f) (focus g) refl -- 
eqfocus (⊗rIl {f = f} {g}) = ⊗rIl-c (focus f) (focus g)
eqfocus (⊗r⊗l {f = f} {g}) = ⊗r⊗l-c (focus f) (focus g) refl
eqfocus (⊗r⊸l {f = f} {g} {h}) = ⊗r⊸l-c (focus f) (focus g ) (focus h)
eqfocus (ex {Γ = Γ} p) = cong (ex-c Γ) (eqfocus p)
eqfocus (exex {f = f}) = exCexC' (focus f) refl
eqfocus (expass {f = f}) = expass-c (focus f) refl
eqfocus (exIl {f = f}) =  exIl-c (focus f) refl
eqfocus (ex⊸r {f = f}) = ex⊸r-c (focus f) refl
eqfocus (ex⊸l₁ {f = f} {g}) = ex⊸l₁-c (focus f) (focus g)
eqfocus (ex⊸l₂ {f = f} {g}) =  ex⊸l₂-c (focus f) (focus g) refl
eqfocus (ex⊗l {f = f}) = ex⊗l-c (focus f) refl
eqfocus (ex⊗r₁ {f = f} {g}) = ex⊗r₁-c (focus f) (focus g)
eqfocus (ex⊗r₂ {f = f} {g}) = ex⊗r₂-c (focus f) (focus g) refl
eqfocus (ex-iso {f = f}) =  exC-iso (focus f)
eqfocus (ex-braid {f = f}) = exC-braid (focus f) refl    
  