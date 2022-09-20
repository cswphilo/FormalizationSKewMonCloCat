{-# OPTIONS --rewriting #-}

module Focusing2 where

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
open import SeqCalc
open import Focusing
open import Utilities hiding (++?)

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
emb-ri∙ : {S : Stp} {Γ : TCxt} {C : Fma} →
       ∙ ∣ S ∣ Γ ⊢ri C → S ∣ ersL Γ ⊢ C
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
emb-c∙ (ri2c f) = emb-ri∙ f

emb-ri {Γ = Γ} (⊸r f) = ⊸r (ex-fma-cxt {Γ = []} {Δ = []} Γ (emb-c f))
emb-ri (li2ri f) = emb-li f

emb-ri∙ {Γ = Γ} (⊸r∙ f) = ⊸r (ex-fma-cxt {Γ = []} {Δ = []} (ersL Γ) (emb-c∙ f))
emb-ri∙ (li2ri (p2li f)) = emb-p∙ f

emb-li (Il f) = Il (emb-li f)
emb-li (⊗l f) = ⊗l (emb-c f)
emb-li (p2li f) = emb-p f

emb-p (pass f) = pass (emb-li f)
emb-p (f2p f) = emb-f f

emb-p∙ (pass∙ f) = pass (emb-li f)
emb-p∙ (f2p f) = emb-f∙ f

emb-f ax = ax
emb-f Ir = Ir
emb-f (⊗r f g) = ⊗r (emb-ri∙ f) (emb-ri g)
emb-f (⊸l f g) = ⊸l (emb-ri f) (emb-li g)

emb-f∙ ax = ax
emb-f∙ Ir = Ir
emb-f∙ (⊗r {Γ = Γ} {Δ} f g) rewrite whiteErs Γ = ⊗r {Γ = ersL (whiteL Γ)} {ersL Δ} (emb-ri∙ f) (emb-ri g)
emb-f∙ (⊸l∙ f g refl) = ⊸l (emb-ri f) (emb-li g)

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
⊸rIl-c' (ri2c f) eq = refl

⊸rIl-c {Γ = Γ₁} (ex {Γ = Γ} f refl refl) eq with snoc≡ Γ Γ₁ eq
... | refl , refl = ⊸rIl-c' f refl
⊸rIl-c {Γ = Γ} (ri2c f) eq = ⊥-elim ([]disj∷ Γ eq)


⊸r⊸l-c'' : {Γ Ω Λ Λ₀ Λ₁ : Cxt} {A B C D : Fma}   
       → (f : - ∣ Ω ؛ Γ ⊢c A) (g : just B ∣ Λ ⊢ri D) (eq : Λ ≡ Λ₀ ++ C ∷ Λ₁)
       → ⊸r-c' {Δ₀ = Γ ++ Λ₀} {Δ₁ = Λ₁} (⊸l-c-ri f g) ((cong (_ ++_) eq)) ≡ ⊸l-c-ri {Δ = Λ₀ ++ Λ₁} f (⊸r (ex {Δ = Λ₀} {Λ₁} (ri2c g) refl eq))

⊸r⊸l-c' : {Γ Ω Λ Λ₀ Λ₁ : Cxt} {A B C D : Fma}
     → (f : - ∣ Γ ؛ [] ⊢c A) (g : just B ∣ Ω ؛ Λ ⊢c D) (eq : Λ ≡ Λ₀ ++ C ∷ Λ₁)
     → ⊸r-c' (⊸l-c f g) eq ≡ ⊸l-c f (⊸r-c' g eq)
     
⊸r⊸l-c : {Γ Δ Ω Λ : Cxt} {A B C D : Fma}
     → (f : - ∣ Γ ؛ [] ⊢c A) (g : just B ∣ Ω ؛ Λ ⊢c D) (eq : Ω ≡ Δ ++ C ∷ []) (eq' : Γ ++ Ω ≡ Γ ++ Δ ++ C ∷ [])
     → ⊸r-c'' {Γ = Γ ++ Δ} (⊸l-c f g) eq' ≡ ⊸l-c f (⊸r-c'' g eq)

⊸r⊸l-c'' {Λ₀ = Λ₀} {Λ₁} {C = C} (ex {Δ = Δ} {Λ} {A = A} f refl refl) g refl rewrite cases++-inj₂ (Λ ++ Λ₀) Δ Λ₁ C = goal
  where TT : Set
        TT = _
        goal : TT
        goal rewrite cases++-inj₂ (Λ ++ Λ₀) Δ Λ₁ C = {!   !}
⊸r⊸l-c'' (ri2c f) g refl = refl

⊸r⊸l-c' {Λ₀ = Λ₀} {Λ₁} f (ex {Δ = Δ} {Λ} g refl refl) eq with cases++ Λ₀ Δ Λ₁ Λ eq
⊸r⊸l-c' {Γ = Γ₁} {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} f (ex {Γ = Γ} {Δ = .(Λ₀ ++ _ ∷ Δ₀)} {Λ} g refl refl) refl | inj₁ (Δ₀ , refl , refl) = cong (λ x → ex {Γ = Γ₁ ++ Γ} {Λ₀ ++ Δ₀} {Λ} x refl refl) (⊸r⊸l-c' f g refl) 
⊸r⊸l-c' {Γ = Γ₁} {Λ₀ = .(Δ ++ Δ₀)} {Λ₁} f (ex {Γ = Γ} {Δ = Δ} {.(Δ₀ ++ _ ∷ Λ₁)} {A = A} g refl refl) refl | inj₂ (Δ₀ , refl , refl) = cong (λ x → ex {Γ = Γ₁ ++ Γ} x refl refl) (⊸r⊸l-c' {Λ₀ = Δ ++ A ∷ Δ₀} f g refl)
⊸r⊸l-c' f (ri2c g) refl = ⊸r⊸l-c'' f g refl


⊸r⊸l-c {Γ = Γ₁} {Δ = Δ} {C = C} f (ex {Γ = Γ} g refl refl) eq eq' with snoc≡ Γ Δ eq
⊸r⊸l-c {Γ = Γ₁} {Δ = Δ} {C = C} f (ex {Γ = .Δ} g refl refl) refl refl | refl , refl rewrite snoc≡-refl (Γ₁ ++ Δ) C = ⊸r⊸l-c' f g refl
⊸r⊸l-c {Δ = Δ} f (ri2c g) eq eq' = ⊥-elim ([]disj∷ Δ eq)


-- ⊸r⊸l-c {Γ = Γ₁} {Δ = Δ₁} f (ex {Γ = Γ} {Δ} g refl refl) eq with snoc≡ (Γ₁ ++ Γ) (Γ₁ ++ Δ₁) (cong (Γ₁ ++_) eq) | snoc≡ Γ Δ₁ eq
-- ⊸r⊸l-c {Γ = Γ₁} {Δ = Δ} {C = C} f (ex {Γ = .Δ} g refl refl) refl | refl , refl | refl , refl rewrite snoc≡-refl (Γ₁ ++ Δ) C = {!   !}
-- ⊸r⊸l-c {Δ = Δ} f (ri2c g) eq = ⊥-elim ([]disj∷ Δ eq)



⊸r⊗l-c' : {Ω Γ Λ Λ₀ Λ₁ : Cxt} {A B C D : Fma} 
    → (f : just A ∣ Ω ؛ Λ ⊢c D) (eq : Ω ≡ B ∷ Γ) (eq' : Λ ≡ Λ₀ ++ C ∷ Λ₁)
    → ⊸r-c' (⊗l-c' f eq) eq' ≡ ⊗l-c' (⊸r-c' f eq') eq
⊸r⊗l-c : {Ω Γ Λ : Cxt} {A B C D : Fma} 
    → (f : just A ∣ B ∷ Ω ؛ Λ ⊢c D) (eq : Ω ≡ Γ ++ C ∷ [])
    → ⊸r-c'' (⊗l-c f) eq ≡ ⊗l-c (⊸r-c'' f (cong (_ ∷_) eq))


⊸r⊗l-c' {Λ₀ = Λ₀} {Λ₁} (ex {Δ = Δ} {Λ} f refl eq'') eq eq' with cases++ Λ₀ Δ Λ₁ Λ eq'
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} (ex {Γ = Γ} {Δ = .(Λ₀ ++ _ ∷ Δ₀)} {Λ} f refl eq'') eq refl | inj₁ (Δ₀ , refl , refl) with cases∷ Γ {ys = []} (sym eq)
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} {A} {B} {C} (ex {Γ = .[]} {.(Λ₀ ++ C ∷ Δ₀)} {Λ} (ex {Γ = Γ} f eq' eq) refl eq'') refl refl | inj₁ (Δ₀ , refl , refl) | inj₁ (refl , refl , refl) = ⊥-elim ([]disj∷ Γ eq')
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} {A} {B} {C} (ex {Γ = .[]} {.(Λ₀ ++ C ∷ Δ₀)} {Λ} (ri2c (⊸r f)) refl refl) refl refl | inj₁ (Δ₀ , refl , refl) | inj₁ (refl , refl , refl) = {!   !}
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} {A} {B} {C} (ex {Γ = .[]} {.(Λ₀ ++ C ∷ Δ₀)} {Λ} (ri2c (li2ri f)) refl refl) refl refl | inj₁ (Δ₀ , refl , refl) | inj₁ (refl , refl , refl) = {!   !}
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} {C = C} (ex {Γ = .(_ ∷ Δ₁)} {.(Λ₀ ++ C ∷ Δ₀)} {Λ} f refl refl) refl refl | inj₁ (Δ₀ , refl , refl) | inj₂ (Δ₁ , refl , refl) with cases++ Λ₀ (Λ₀ ++ C ∷ Δ₀) (Δ₀ ++ Λ) Λ refl
... | inj₁ (Δ₂ , p , q) with canc++ Δ₀ Δ₂ {ys = Λ} q
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} {C = C} (ex {_} {.(_ ∷ Δ₁)} {.(Λ₀ ++ C ∷ Δ₀)} {Λ} f refl refl) refl refl | inj₁ (Δ₀ , refl , refl) | inj₂ (Δ₁ , refl , refl) | inj₁ (.Δ₀ , refl , refl) | refl = cong (λ x → ex {Δ = Λ₀ ++ Δ₀} {Λ} x refl refl) (⊸r⊗l-c' f refl refl)
⊸r⊗l-c' {Λ₀ = Λ₀} {.(Δ₀ ++ Λ)} {C = C} (ex {Γ = .(_ ∷ Δ₁)} {.(Λ₀ ++ C ∷ Δ₀)} {Λ} f refl refl) refl refl | inj₁ (Δ₀ , refl , refl) | inj₂ (Δ₁ , refl , refl) | inj₂ (Δ₂ , p , q) = ⊥-elim (canc⊥2 Λ₀ q)
⊸r⊗l-c' {Λ₀ = .(Δ ++ Δ₀)} {Λ₁} (ex {Γ = Γ} {Δ = Δ} {.(Δ₀ ++ _ ∷ Λ₁)} f refl eq'') eq refl | inj₂ (Δ₀ , refl , refl) with cases∷ Γ {ys = []} (sym eq)
⊸r⊗l-c' {Γ = _} {_} {.(Δ ++ Δ₀)} {Λ₁} (ex {Γ = .[]} {Δ = Δ} {.(Δ₀ ++ _ ∷ Λ₁)} (ex {Γ = Γ} f eq' eq) refl eq'') refl refl | inj₂ (Δ₀ , refl , refl) | inj₁ (refl , refl , refl) = ⊥-elim ([]disj∷ Γ eq')
⊸r⊗l-c' {Γ = _} {_} {.(Δ ++ Δ₀)} {Λ₁} {B = B} (ex {Γ = .[]} {Δ = Δ} {.(Δ₀ ++ _ ∷ Λ₁)} (ri2c (⊸r f)) refl refl) refl refl | inj₂ (Δ₀ , refl , refl) | inj₁ (refl , refl , refl) rewrite cases++-inj₁ Δ Δ₀ Λ₁ B = {!   !}
⊸r⊗l-c' {Γ = _} {_} {.(Δ ++ Δ₀)} {Λ₁} (ex {Γ = .[]} {Δ = Δ} {.(Δ₀ ++ _ ∷ Λ₁)} (ri2c (li2ri f)) refl refl) refl refl | inj₂ (Δ₀ , refl , refl) | inj₁ (refl , refl , refl) = {!   !}
⊸r⊗l-c' {Γ = _} {_} {.(Δ ++ Δ₀)} {Λ₁} {C = C} (ex {Γ = .(_ ∷ Δ₁)} {Δ = Δ} {.(Δ₀ ++ C ∷ Λ₁)} f refl refl) refl refl | inj₂ (Δ₀ , refl , refl) | inj₂ (Δ₁ , refl , refl) with cases++ (Δ ++ Δ₀) Δ Λ₁ (Δ₀ ++ C ∷ Λ₁) refl
... | inj₁ (Δ₂ , p , q) = ⊥-elim (canc⊥4 Δ {ys = Δ₂} {Δ₀} p)
... | inj₂ (Δ₂ , p , q) with ++canc {xs = Δ₀} {Δ₂} Δ q
⊸r⊗l-c' {_} {.(Δ₁ ++ _ ∷ [])} {_} {.(Δ ++ Δ₀)} {Λ₁} {C = C} (ex {_} {.(_ ∷ Δ₁)} {Δ = Δ} {.(Δ₀ ++ C ∷ Λ₁)} f refl refl) refl refl | inj₂ (Δ₀ , refl , refl) | inj₂ (Δ₁ , refl , refl) | inj₂ (.Δ₀ , refl , refl) | refl = cong (λ x → ex {Δ = Δ} {Δ₀ ++ Λ₁} x refl refl) (⊸r⊗l-c' {Λ₀ = Δ ++ _ ∷ Δ₀} f refl refl)


⊸r⊗l-c {Γ = Γ₁} {B = B} (ex {Γ = Γ} {A = A} f eq' refl) refl with snoc≡ (B ∷ Γ₁) Γ eq'
⊸r⊗l-c {Γ = Γ₁} {B = B} (ex {Γ = .(B ∷ Γ₁)} {A = A} f refl refl) refl | refl , refl rewrite snoc≡-refl Γ₁ A = ⊸r⊗l-c' f refl refl


⊗rpass-c : {Γ Δ Λ : Cxt} {A' A B : Fma}
        →  (f : just A' ∣ Γ ؛ [] ⊢c A) (g : - ∣ Δ ؛ Λ ⊢c B)
        → ⊗r-c (pass-c f) g ≡ pass-c (⊗r-c f g)
⊗rpass-c f (ex (ex g eq' eq₁) refl eq) = {!   !}
⊗rpass-c f (ex (ri2c (⊸r f₁)) refl refl) = {!   !}
⊗rpass-c f (ex (ri2c (li2ri f₁)) refl refl) = {!   !}
⊗rpass-c f (ri2c g) = {!   !}

-- exCexC' : ∀{S Φ₁ Φ₂ Φ₃ Λ Δ A B A' B' C} (f : S ∣ Λ ؛ Δ ⊢c C)
--   → (eq : Λ ≡ Φ₁ ++ A ∷ B ∷ Φ₂ ++ A' ∷ B' ∷ Φ₃)
--   → ex-c' (Φ₁ ++ B ∷ A ∷ Φ₂) (ex-c' Φ₁ f eq) refl
--     ≡ ex-c' Φ₁ (ex-c' (Φ₁ ++ A ∷ B ∷ Φ₂) f eq) refl
-- exCexC' {Φ₁ = Φ₁} {Φ₂} {Φ₃} {A = A} {B} {A'} {B'} (ex {Γ = Φ} f refl eq') eq with cases++ Φ Φ₁ [] (A ∷ B ∷ Φ₂ ++ A' ∷ B' ∷ Φ₃) (sym eq)
-- ... | inj₁ (Ψ₀ , p , q) = ⊥-elim ([]disj∷ Ψ₀ q)
-- ... | inj₂ (x ∷ [] , p , q) = ⊥-elim ([]disj∷ Φ₂ (sym (inj∷ (inj∷ p .proj₂) .proj₂)))
-- ... | inj₂ (x ∷ x₁ ∷ Ψ₀ , p , q) with cases++ Ψ₀ Φ₂ [] (A' ∷ B' ∷ Φ₃) (inj∷ (inj∷ p .proj₂) .proj₂)
-- ... | inj₁ (Ψ₀' , p' , q') = ⊥-elim ([]disj∷ Ψ₀' q')
-- exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {A = x} {x₁} {A'} {B'} (ex {Γ = .(Φ ++ A ∷ [])} {Γ} {Δ} (ex {Γ = Φ} {Γ₁} {Δ₁} {A = A} f refl refl) refl eq') eq | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ []) , refl , q) | inj₂ (A' ∷ [] , refl , refl) with snoc≡ Φ (Φ₁ ++ _ ∷ _ ∷ Φ₂) q | cases++ Γ Γ₁ Δ Δ₁ eq'
-- exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {_} {_} {x} {x₁} {A'} {B'} (ex {_} {.((Φ₁ ++ x ∷ x₁ ∷ Φ₂) ++ A' ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Γ = .(Φ₁ ++ x ∷ x₁ ∷ Φ₂)} {.(Γ ++ B' ∷ Γ₀)} {Δ₁} {A = A'} f refl refl) refl refl) refl | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ []) , refl , refl) | inj₂ (A' ∷ [] , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl)
--   rewrite cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x₁ ∷ x ∷ Φ₂) [] B' |
--           cases++-inj₂ (x₁ ∷ x ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x ∷ x₁ ∷ Φ₂) [] B' |
--           snoc≡-refl (Φ₁ ++ x₁ ∷ x ∷ Φ₂) A' | snoc≡-refl (Φ₁ ++ x ∷ x₁ ∷ Φ₂) A' |
--           cases++-inj₁ Γ Γ₀ Δ₁ B' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂ ++ B' ∷ []) Φ₁ [] A' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] B' = refl
-- exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {_} {_} {x} {x₁} {A'} {B'} (ex {_} {.((Φ₁ ++ x ∷ x₁ ∷ Φ₂) ++ A' ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Γ = .(Φ₁ ++ x ∷ x₁ ∷ Φ₂)} {Γ₁} {.(Γ₀ ++ B' ∷ Δ)} {A = .A'} f refl refl) refl refl) refl | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ []) , refl , refl) | inj₂ (A' ∷ [] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl)
--   rewrite cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x₁ ∷ x ∷ Φ₂) [] B' |
--           cases++-inj₂ (x₁ ∷ x ∷ Φ₂) Φ₁ [] A' | cases++-inj₂ (A' ∷ []) (Φ₁ ++ x ∷ x₁ ∷ Φ₂) [] B' |
--           snoc≡-refl (Φ₁ ++ x₁ ∷ x ∷ Φ₂) A' | snoc≡-refl (Φ₁ ++ x ∷ x₁ ∷ Φ₂) A' |
--           cases++-inj₂ Γ₀ Γ₁ Δ B' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂ ++ B' ∷ []) Φ₁ [] A' | cases++-inj₂ (x ∷ x₁ ∷ Φ₂) Φ₁ [] B' = refl
-- exCexC' {Φ₁ = Φ₁} {Φ₂} {.[]} {A = A} {B} {A'} {B'} (ex {Γ = .[]} (ri2c f) refl eq') eq | inj₂ (x ∷ x₁ ∷ Ψ₀ , p , q) | inj₂ (A' ∷ [] , refl , q') = ⊥-elim ([]disj∷ Φ₁ q)
-- exCexC' {Φ₁ = Φ₁} {Φ₂} {.(Ψ₀' ++ A ∷ [])} {A = x} {x₁} {A'} {B'} (ex {Γ = .(Φ₁ ++ x ∷ x₁ ∷ Φ₂ ++ A' ∷ B' ∷ Ψ₀')} {Γ} {Δ} {A = A} f refl refl) refl | inj₂ (x ∷ x₁ ∷ .(Φ₂ ++ A' ∷ B' ∷ Ψ₀') , refl , refl) | inj₂ (A' ∷ B' ∷ Ψ₀' , refl , refl)
--   rewrite cases++-inj₂ (A' ∷ B' ∷ Ψ₀') (Φ₁ ++ x ∷ x₁ ∷ Φ₂) [] A | cases++-inj₂ (x ∷ x₁ ∷ Φ₂ ++ B' ∷ A' ∷ Ψ₀') Φ₁ [] A |
--           cases++-inj₂ (A' ∷ B' ∷ Ψ₀') (Φ₁ ++ x₁ ∷ x ∷ Φ₂) [] A | cases++-inj₂ (x₁ ∷ x ∷ Φ₂ ++ B' ∷ A' ∷ Ψ₀') Φ₁ [] A =
--             cong (λ y → ex {Γ = Φ₁ ++ _ ∷ _ ∷ Φ₂ ++ _ ∷ _ ∷ Ψ₀'} {Γ} {Δ} y refl refl) (exCexC' f refl)
-- exCexC' {Φ₁ = Φ₁} (ri2c f) eq = ⊥-elim ([]disj∷ Φ₁ eq)

-- exC-iso' : ∀{S Φ Ψ Λ Δ A B C} (f : S ∣ Λ ؛ Δ ⊢c C)
--   → (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
--   → ex-c' Φ (ex-c' Φ f eq) refl ≡ subst (λ x → S ∣ x ؛ Δ ⊢c C) eq f
-- exC-iso' {Φ = Φ} {Ψ} {A = A} {B} (ex {Γ = Φ₁} f refl eq') eq with cases++ Φ₁ Φ [] (A ∷ B ∷ Ψ) (sym eq)
-- ... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
-- exC-iso' {Φ = Φ} {A = A} {B} (ex {Δ = Γ} {Δ} (ex {Γ = Φ₁} {Δ = Γ₁} {Δ₁} f refl refl) refl eq') eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ Φ q | cases++ Γ Γ₁ Δ Δ₁ eq'
-- exC-iso' {Φ = Φ} {A = A} {B} (ex {Δ = Γ} (ex {Γ = Φ} {Λ = Δ₁} f refl refl) refl refl) refl | inj₂ (A ∷ [] , refl , q) | refl , refl | inj₁ (Γ₀ , refl , refl)
--   rewrite cases++-inj₂ (B ∷ []) Φ [] A | snoc≡-refl Φ B | cases++-inj₂ Γ₀ Γ Δ₁ A = refl
-- exC-iso' {Φ = Φ} {A = A} {B} (ex {Λ = Δ} (ex {Δ = Γ₁} f refl refl) refl refl) refl | inj₂ (A ∷ [] , refl , q) | refl , refl | inj₂ (Γ₀ , refl , refl)
--   rewrite cases++-inj₂ (B ∷ []) Φ [] A | snoc≡-refl Φ B | cases++-inj₁ Γ₁ Γ₀ Δ A = refl
-- exC-iso' {Φ = Φ} (ex (ri2c f) refl eq') eq | inj₂ (A ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
-- exC-iso' {Φ = Φ} {A = A} {B} (ex {A = A₁} f refl refl) refl | inj₂ (A ∷ B ∷ Φ₀ , refl , refl)
--   rewrite cases++-inj₂ (B ∷ A ∷ Φ₀) Φ [] A₁ = cong (λ y → ex {Γ = Φ ++ A ∷ B ∷ Φ₀} y refl refl) (exC-iso' f refl)
-- exC-iso' {Φ = Φ} (ri2c f) eq = ⊥-elim ([]disj∷ Φ eq)

-- exC-iso : ∀{S Φ Ψ Δ A B C} (f : S ∣ Φ ++ A ∷ B ∷ Ψ ؛ Δ ⊢c C)
--   → ex-c Φ (ex-c Φ f) ≡ f
-- exC-iso f = exC-iso' f refl

-- exC-braid : ∀{S Φ A B C Λ Ψ Δ D}
--   → (f : S ∣ Λ ؛ Δ ⊢c D)
--   → (eq : Λ ≡ Φ ++ A ∷ B ∷ C ∷ Ψ)
--   → ex-c Φ (ex-c (Φ ++ B ∷ []) (ex-c' Φ f eq))
--     ≡ ex-c (Φ ++ C ∷ []) (ex-c Φ (ex-c' (Φ ++ A ∷ []) f eq))
-- exC-braid {Φ = Φ} {A} {B} {C} {Ψ = Ψ} (ex {Γ = Φ₁} f refl eq₁) eq with cases++ Φ₁ Φ [] (A ∷ B ∷ C ∷ Ψ) (sym eq)
-- ... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
-- exC-braid {Φ = Φ} {A} {B} {C} {Ψ = .[]} (ex {Γ = .((Φ₁ ++ _ ∷ []) ++ _ ∷ [])} (ex (ex {Γ = Φ₁} f refl refl) refl eq₂) refl eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , q) with snoc≡ (Φ₁ ++ _ ∷ []) (Φ ++ A ∷ []) q
-- ... | q' , refl with snoc≡ Φ₁ Φ q'
-- exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ _ ∷ []) ++ B ∷ [])} {Γ} {Δ} (ex {Δ = Γ₁} {Δ₁} (ex {Γ = Φ} f refl refl) refl eq₂) refl eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , refl) | q' , refl | refl , refl with cases++ Γ Γ₁ Δ Δ₁ eq₁
-- exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Δ = .(Γ ++ C ∷ Γ₀)} {Δ₁} (ex {Γ = Φ} {Γ₁} {Δ} f refl refl) refl eq₂) refl refl) eq | inj₂ (A ∷ B ∷ [] , refl , refl) | q' , refl | refl , refl | inj₁ (Γ₀ , refl , refl) with cases++ (Γ ++ C ∷ Γ₀) Γ₁ Δ₁ Δ eq₂
-- exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {Γ} {.(Γ₀ ++ Γ₀' ++ Δ)} (ex {_} {_} {.(Γ ++ C ∷ Γ₀)} {.(Γ₀' ++ Δ)} (ex {Γ = Φ} {.(Γ ++ C ∷ Γ₀ ++ B ∷ Γ₀')} {Δ} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
--   rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C |
--           snoc≡-refl Φ A | cases++-inj₁ (Γ ++ C ∷ Γ₀) Γ₀' Δ B |
--           snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₁ Γ (Γ₀ ++ Γ₀') Δ C |
--           cases++-inj₂ (B ∷ C ∷ []) Φ [] A | cases++-inj₂ (B ∷ []) Φ [] C |
--           snoc≡-refl Φ B | cases++-inj₁ Γ Γ₀ (Γ₀' ++ A ∷ Δ) C |
--           cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₁ Γ Γ₀ (Γ₀' ++ Δ) C |
--           cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) Φ [] C | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B |
--           snoc≡-refl Φ A | cases++-inj₁ Γ (Γ₀ ++ B ∷ Γ₀') Δ C |
--           snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₁ (Γ ++ Γ₀) Γ₀' Δ B = refl
-- ... | inj₂ (Γ₀' , refl , q) with cases++ Γ Γ₁ Γ₀ Γ₀' (sym q)
-- exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {Γ} {.((Γ₀'' ++ Γ₀') ++ Δ₁)} (ex {_} {_} {.(Γ ++ C ∷ Γ₀'' ++ Γ₀')} {Δ₁} (ex {Γ = Φ} {.(Γ ++ C ∷ Γ₀'')} {.(Γ₀' ++ B ∷ Δ₁)} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₁ (.(Γ₀'' ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) | inj₁ (Γ₀'' , refl , refl) 
--   rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C |
--           snoc≡-refl Φ A | cases++-inj₂ Γ₀' (Γ ++ C ∷ Γ₀'') Δ₁ B |
--           snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₁ Γ Γ₀'' (Γ₀' ++ Δ₁) C |
--           cases++-inj₂ (B ∷ C ∷ []) Φ [] A | cases++-inj₂ (B ∷ []) Φ [] C |
--           snoc≡-refl Φ B | cases++-inj₁ Γ (Γ₀'' ++ A ∷ Γ₀') Δ₁ C |
--           cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₁ Γ (Γ₀'' ++ Γ₀') Δ₁ C |
--           cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B | cases++-inj₂ (A ∷ []) Φ [] C |
--           snoc≡-refl Φ A | cases++-inj₁ Γ Γ₀'' (Γ₀' ++ B ∷ Δ₁) C |
--           snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₂ Γ₀' (Γ ++ Γ₀'') Δ₁ B = refl
-- exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀'')} {.(Γ₀ ++ Δ₁)} (ex {_} {_} {.((Γ₁ ++ Γ₀'') ++ C ∷ Γ₀)} {Δ₁} (ex {Γ = Φ} {Γ₁} {.((Γ₀'' ++ C ∷ Γ₀) ++ B ∷ Δ₁)} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₁ (Γ₀ , refl , refl) | inj₂ (.(Γ₀'' ++ C ∷ Γ₀) , refl , refl) | inj₂ (Γ₀'' , refl , refl) 
--   rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₂ (Γ₀'' ++ C ∷ Γ₀) Γ₁ Δ₁ B |
--           snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₂ Γ₀'' Γ₁ (Γ₀ ++ Δ₁) C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
--           cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₁ (Γ₁ ++ A ∷ Γ₀'') Γ₀ Δ₁ C |
--           cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₁ (Γ₁ ++ Γ₀'') Γ₀ Δ₁ C |
--           cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) Φ [] C | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B |
--           snoc≡-refl Φ A | cases++-inj₂ Γ₀'' Γ₁ (Γ₀ ++ B ∷ Δ₁) C |
--           snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₂ (Γ₀'' ++ Γ₀) Γ₁ Δ₁ B = refl
-- exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀)} {Δ} (ex {Δ = Γ₁} {.(Γ₀ ++ C ∷ Δ)} (ex {Γ = Φ} {Γ} {Δ₁} f refl refl) refl eq₂) refl refl) eq | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (Γ₀ , refl , refl) with cases++ Γ₁ Γ (Γ₀ ++ C ∷ Δ) Δ₁ eq₂
-- ... | inj₁ (Γ₀' , refl , q) with cases++ Γ₀ Γ₀' Δ Δ₁ (sym q)
-- exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀)} {.(Γ₀'' ++ Δ₁)} (ex {Δ = Γ₁} {.(Γ₀ ++ C ∷ Γ₀'' ++ Δ₁)} (ex {Γ = Φ} {.(Γ₁ ++ B ∷ Γ₀ ++ C ∷ Γ₀'')} {Δ₁} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (Γ₀ , refl , refl) | inj₁ (.(Γ₀ ++ C ∷ Γ₀'') , refl , refl) | inj₁ (Γ₀'' , refl , refl) 
--   rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₁ Γ₁ (Γ₀ ++ C ∷ Γ₀'') Δ₁ B |
--           snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₁ (Γ₁ ++ Γ₀) Γ₀'' Δ₁ C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
--           cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₂ Γ₀ Γ₁ (Γ₀'' ++ A ∷ Δ₁) C |
--           cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₂ Γ₀ Γ₁ (Γ₀'' ++ Δ₁) C |
--           cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B | cases++-inj₂ (A ∷ []) Φ [] C |
--           snoc≡-refl Φ A | cases++-inj₁ (Γ₁ ++ B ∷ Γ₀) Γ₀'' Δ₁ C |
--           snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₁ Γ₁ (Γ₀ ++ Γ₀'') Δ₁ B = refl
-- exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.(Γ₁ ++ Γ₀' ++ Γ₀'')} {Δ} (ex {Δ = Γ₁} {.((Γ₀' ++ Γ₀'') ++ C ∷ Δ)} (ex {Γ = Φ} {.(Γ₁ ++ B ∷ Γ₀')} {.(Γ₀'' ++ C ∷ Δ)} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (.(Γ₀' ++ Γ₀'') , refl , refl) | inj₁ (Γ₀' , refl , refl) | inj₂ (Γ₀'' , refl , refl)
--   rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₁ Γ₁ Γ₀' (Γ₀'' ++ C ∷ Δ) B |
--           snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₂ Γ₀'' (Γ₁ ++ Γ₀') Δ C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
--           cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₂ (Γ₀' ++ A ∷ Γ₀'') Γ₁ Δ C |
--           cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₂ (Γ₀' ++ Γ₀'') Γ₁ Δ C |
--           cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) Φ [] C | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B |
--           snoc≡-refl Φ A | cases++-inj₂ (Γ₀'') (Γ₁ ++ B ∷ Γ₀') Δ C |
--           snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₁ Γ₁ Γ₀' (Γ₀'' ++ Δ) B = refl
-- exC-braid {Φ = Φ} {A} {B} {C} {_} {.[]} (ex {_} {.((Φ ++ A ∷ []) ++ B ∷ [])} {.((Γ ++ Γ₀') ++ Γ₀)} {Δ} (ex {Δ = .(Γ ++ Γ₀')} {.(Γ₀ ++ C ∷ Δ)} (ex {Γ = Φ} {Γ} {.(Γ₀' ++ B ∷ Γ₀ ++ C ∷ Δ)} f refl refl) refl refl) refl refl) refl | inj₂ (A ∷ B ∷ [] , refl , refl) | refl , refl | refl , refl | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) 
--   rewrite cases++-inj₂ (A ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ B ∷ []) [] C | snoc≡-refl Φ A | cases++-inj₂ Γ₀' Γ (Γ₀ ++ C ∷ Δ) B |
--           snoc≡-refl (Φ ++ B ∷ []) A | cases++-inj₂ (Γ₀' ++ Γ₀) Γ Δ C | cases++-inj₂ (B ∷ C ∷ []) Φ [] A |
--           cases++-inj₂ (B ∷ []) Φ [] C | snoc≡-refl Φ B | cases++-inj₂ Γ₀ (Γ ++ A ∷ Γ₀') Δ C |
--           cases++-inj₂ (B ∷ []) (Φ ++ A ∷ []) [] C | snoc≡-refl (Φ ++ A ∷ []) B | cases++-inj₂ Γ₀ (Γ ++ Γ₀') Δ C |
--           cases++-inj₂ (A ∷ C ∷ []) Φ [] B | cases++-inj₂ (A ∷ []) (Φ ++ C ∷ []) [] B | cases++-inj₂ (A ∷ []) Φ [] C |
--           snoc≡-refl Φ A | cases++-inj₂ (Γ₀' ++ B ∷ Γ₀) Γ Δ C |
--           snoc≡-refl (Φ ++ C ∷ []) A | cases++-inj₂ Γ₀' Γ (Γ₀ ++ Δ) B = refl
-- exC-braid {Φ = x ∷ Φ} {A} {B} {C} {Ψ = .[]} (ex {Γ = .([] ++ _ ∷ [])} (ex (ri2c f) refl eq₂) refl eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ (inj∷ q .proj₂))
-- exC-braid {Φ = Φ} {A} {B} {C} {Ψ = .[]} (ex {Γ = .[]} (ri2c f) refl eq₁) eq | inj₂ (A ∷ B ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
-- exC-braid {Φ = Φ} {A} {B} {C} {Ψ = .(Φ₀ ++ A₁ ∷ [])} (ex {Γ = .(Φ ++ A ∷ B ∷ C ∷ Φ₀)} {Γ} {Δ} {A = A₁} f refl refl) refl | inj₂ (A ∷ B ∷ C ∷ Φ₀ , refl , refl) 
--   rewrite cases++-inj₂ (B ∷ C ∷ Φ₀) (Φ ++ A ∷ []) [] A₁ | cases++-inj₂ (A ∷ C ∷ B ∷ Φ₀) Φ [] A₁ |
--           cases++-inj₂ (C ∷ A ∷ B ∷ Φ₀) (Φ ++ C ∷ []) [] A₁ | cases++-inj₂ (A ∷ C ∷ Φ₀) (Φ ++ B ∷ []) [] A₁ |
--           cases++-inj₂ (B ∷ C ∷ A ∷ Φ₀) Φ [] A₁ | cases++-inj₂ (A ∷ B ∷ Φ₀) (Φ ++ C ∷ []) [] A₁ =
--           cong (λ x → ex {Γ = Φ ++ C ∷ B ∷ A ∷ Φ₀} {Γ}{Δ} x refl refl) (exC-braid f refl)
-- exC-braid {Φ = Φ} (ri2c f) eq = ⊥-elim ([]disj∷ Φ eq)


eqfocus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              {f g : S ∣ Γ ⊢ C} → f ≗ g → focus f ≡ focus g
eqfocus refl = refl
eqfocus (~ p) = sym (eqfocus p)
eqfocus (p ∙ p₁) = trans (eqfocus p) (eqfocus p₁)
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
eqfocus (⊸r⊸l {f = f} {g}) = ⊸r⊸l-c (focus f) (focus g) refl refl
eqfocus ⊸r⊗l = {!   !}
eqfocus ⊗rpass = {!   !}
eqfocus ⊗rIl = {!   !}
eqfocus ⊗r⊗l = {!   !}
eqfocus ⊗r⊸l = {!   !}
eqfocus (ex {Γ = Γ} p) = cong (ex-c Γ) (eqfocus p)
eqfocus (exex {f = f}) = {!   !} -- exCexC' (focus f) refl
eqfocus expass = {!   !}
eqfocus exIl = {!   !}
eqfocus ex⊸r = {!   !}
eqfocus ex⊸l₁ = {!   !}
eqfocus ex⊸l₂ = {!   !}
eqfocus ex⊗l = {!   !}
eqfocus ex⊗r₁ = {!   !}
eqfocus ex⊗r₂ = {!   !}
eqfocus (ex-iso {f = f}) = {!   !} -- exC-iso (focus f)
eqfocus (ex-braid {f = f}) = {!   !} --  exC-braid (focus f) refl    