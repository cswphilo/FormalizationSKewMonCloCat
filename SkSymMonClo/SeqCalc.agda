{-# OPTIONS --rewriting #-}

module SeqCalc (At : Set) where

open import Data.Maybe
open import Data.List
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Formulae At
open import Utilities
-- 

-- Sequent Calculus

infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A
  pass : {Γ : Cxt} → {A C : Fma} → 
              just A ∣ Γ ⊢ C → - ∣ A ∷ Γ ⊢ C
  Ir : - ∣ [] ⊢ I
  Il : {Γ : Cxt} → {C : Fma} →
            - ∣ Γ ⊢ C → just I ∣ Γ ⊢ C
  ⊗l : {Γ : Cxt} → {A B C : Fma} →
           just A ∣ B ∷ Γ ⊢ C → just (A ⊗ B) ∣ Γ ⊢ C 
  ⊗r : {Γ Δ : Cxt} → {S : Stp} → {A B : Fma} → 
           S ∣ Γ ⊢ A → - ∣ Δ ⊢ B → S ∣ Γ ++ Δ ⊢ A ⊗ B
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} → 
           - ∣ Γ ⊢ A → just B ∣ Δ ⊢ C → just (A ⊸ B) ∣ Γ ++ Δ ⊢ C
  ⊸r : {Γ : Cxt} → {S : Stp} → {A B : Fma} →
           S ∣ Γ ++ A ∷ [] ⊢ B → S ∣ Γ ⊢ A ⊸ B
  ex : {S : Stp} → {Γ Δ : Cxt} → {A B C : Fma} →
           S ∣ Γ ++ A ∷ B ∷ Δ ⊢ C → S ∣ Γ ++ B ∷ A ∷ Δ ⊢ C

subst-cxt : {S : Stp} → {Γ₀ Γ₁ : Cxt} → {A : Fma} → 
               Γ₀ ≡ Γ₁ → S ∣ Γ₀ ⊢ A → S ∣ Γ₁ ⊢ A
subst-cxt refl f = f

-- other general admissible form of exchange

ex-fma-cxt : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} → 
              S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C → S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C 
ex-fma-cxt [] f = f
ex-fma-cxt {Γ = Γ} (B ∷ Λ) f = ex-fma-cxt {Γ = Γ ++ B ∷ []} Λ (ex f) 

ex-cxt-cxt1 : {S : Stp} → {Γ Δ : Cxt} (Λ₁ Λ₂ : Cxt) → {C : Fma} → 
              S ∣ Γ ++ Λ₁ ++ Λ₂ ++ Δ ⊢ C → S ∣ Γ ++ Λ₂ ++ Λ₁ ++ Δ ⊢ C 
ex-cxt-cxt1 {Γ = Γ} [] Λ₂ f = f
ex-cxt-cxt1 {Γ = Γ} {Δ} (A ∷ Λ₁) Λ₂ f =
  ex-fma-cxt {Γ = Γ} Λ₂ (ex-cxt-cxt1 {Γ = Γ ++ A ∷ []} {Δ} Λ₁ Λ₂ f)

ex-cxt-fma : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {A C : Fma} → 
              S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C  → S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C
ex-cxt-fma {Γ = Γ} [] f = f
ex-cxt-fma {Γ = Γ} (B ∷ Λ) f = ex (ex-cxt-fma {Γ = Γ ++ B ∷ []} Λ f)

ex-cxt-cxt2 : {S : Stp} → {Γ Δ : Cxt} (Λ₁ Λ₂ : Cxt) → {C : Fma} → 
              S ∣ Γ ++ Λ₁ ++ Λ₂ ++ Δ ⊢ C → S ∣ Γ ++ Λ₂ ++ Λ₁ ++ Δ ⊢ C 
ex-cxt-cxt2 Λ₁ [] f = f
ex-cxt-cxt2 {Γ = Γ} {Δ} Λ₁ (A ∷ Λ₂) f =
  ex-cxt-cxt2 {Γ = Γ ++ A ∷ []}{Δ} Λ₁ Λ₂ (ex-cxt-fma {Γ = Γ}{Λ₂ ++ Δ} Λ₁ f) 

ex-cxt-cxt2[] : {S : Stp} → {Γ Δ : Cxt} (Λ : Cxt) → {C : Fma}
  → (f : S ∣ Γ ++ Λ ++ Δ ⊢ C)
  → ex-cxt-cxt2 {Γ = Γ}{Δ} [] Λ f ≡ f
ex-cxt-cxt2[] [] f = refl
ex-cxt-cxt2[] {Γ = Γ}{Δ} (x ∷ Λ) f = ex-cxt-cxt2[] {Γ = Γ ++ x ∷ []}{Δ} Λ f

-- Invertible rules

Il-1 : {Γ : Cxt} → {C : Fma} → just I ∣ Γ ⊢ C → - ∣ Γ ⊢ C
Il-1 ax = Ir
Il-1 (Il f) = f
Il-1 (⊗r f f₁) = ⊗r (Il-1 f) f₁
Il-1 (⊸r f) = ⊸r (Il-1 f)
Il-1 (ex f) = ex (Il-1 f)

⊗l-1 : {Γ : Cxt} → {A B C : Fma} → just (A ⊗ B) ∣ Γ ⊢ C → just A ∣ B ∷ Γ ⊢ C
⊗l-1 ax = ⊗r ax (pass ax)
⊗l-1 (⊗l f) = f
⊗l-1 (⊗r f f₁) = ⊗r (⊗l-1 f) f₁
⊗l-1 (⊸r f) = ⊸r (⊗l-1 f)
⊗l-1 (ex {Γ = Γ} f) = ex {Γ = _ ∷ Γ} (⊗l-1 f)

⊸r-1 : {S : Stp} → {Γ : Cxt} → {A B : Fma} → S ∣ Γ ⊢ A ⊸ B → S ∣ Γ ++ A ∷ [] ⊢ B
⊸r-1 ax = ⊸l (pass ax) ax
⊸r-1 (pass f) = pass (⊸r-1 f)
⊸r-1 (Il f) = Il (⊸r-1 f)
⊸r-1 (⊗l f) = ⊗l (⊸r-1 f)
⊸r-1 (⊸l f f₁) = ⊸l f (⊸r-1 f₁)
⊸r-1 (⊸r f) = f
⊸r-1 {A = A} (ex {Γ = Γ} {Δ} f) = ex (⊸r-1 {Γ = Γ ++ _ ∷ _ ∷ Δ} f)

-- Cut Elimination

scut : {S : Stp} {Γ Δ : Cxt} {A C : Fma} 
        (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ C)  →
     ------------------------------------------
        S ∣ Γ ++ Δ ⊢ C

ccut : {T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A C : Fma}
       (f : - ∣ Γ ⊢ A)  (g : T ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ') →
       -----------------------------------------------------------------
                     T ∣ Δ₀ ++ Γ ++ Δ' ⊢ C

scut ax g = g
scut (pass f) g = pass (scut f g)
scut Ir ax = Ir
scut Ir (Il g) = g
scut Ir (⊗r g g₁) = ⊗r (scut Ir g) g₁
scut Ir (⊸r g) = ⊸r (scut Ir g)
scut Ir (ex g) = ex (scut Ir g)
scut (Il f) g = Il (scut f g)
scut (⊗l f) g = ⊗l (scut f g)
scut (⊗r f f₁) ax = ⊗r f f₁
scut (⊗r f f₁) (⊗l g) = scut f (ccut [] f₁ g refl)
scut (⊗r f f₁) (⊗r g g₁) = ⊗r (scut (⊗r f f₁) g) g₁
scut (⊗r f f₁) (⊸r g) = ⊸r (scut (⊗r f f₁) g)
scut (⊗r {Γ = Γ}{Δ} f f₁) (ex {Γ = Γ₁} g) = ex {Γ = Γ ++ Δ ++ Γ₁} (scut (⊗r f f₁) g)
scut (⊸l f f₁) g = ⊸l f (scut f₁ g)
scut (⊸r f) ax = ⊸r f
scut (⊸r f) (⊗r g g₁) = ⊗r (scut (⊸r f) g) g₁
scut (⊸r {Γ = Γ} f) (⊸l g g₁) = scut (ccut Γ g f refl) g₁
scut (⊸r f) (⊸r g) = ⊸r (scut (⊸r f) g)
scut (⊸r {Γ = Γ} f) (ex {Γ = Γ₁} g) = ex {Γ = Γ ++ Γ₁} (scut (⊸r f) g)
scut (ex f) g = ex (scut f g)
ccut Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
ccut Δ₀ f (pass g) p with cases∷ Δ₀ p
ccut .[] f (pass g) p | inj₁ (refl , refl , refl) = scut f g
ccut .(_ ∷ Δ₀) f (pass g) p | inj₂ (Δ₀ , r , refl) =  pass (ccut Δ₀ f g r)
ccut Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
ccut Δ₀ f (Il g) p = Il (ccut Δ₀ f g p)
ccut Δ₀ f (⊗l {B = B} g) p = ⊗l (ccut (B ∷ Δ₀) f g (cong (_∷_ B) p))
ccut Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g₁) p with cases++ Δ₀ Γ Δ' Δ p
ccut Δ₀ f (⊗r g g') p | inj₁ (Γ₀ , refl , refl) = ⊗r (ccut Δ₀ f g refl) g'
ccut ._ f (⊗r g g') p | inj₂ (Γ₀ , refl , refl) = ⊗r g (ccut Γ₀  f g' refl) 
ccut Δ₀ {Δ'} f (⊸l {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
ccut Δ₀ f (⊸l g g') p | inj₁ (Γ₀ , r , refl) = ⊸l (ccut Δ₀ f g r) g'
ccut ._ f (⊸l g g') p | inj₂ (Γ₀ , refl , refl) = ⊸l g (ccut Γ₀ f g' refl)
ccut Δ₀ f (⊸r g) refl = ⊸r (ccut Δ₀ f g refl)
ccut Δ₀ {Δ'} f (ex {Γ = Γ}{Δ}{A}{B} g) p with cases++2 Δ₀ Γ Δ' Δ p
ccut {Γ = Γ} Δ₀ f (ex g) p | inj₁ (Γ₀ , refl , refl) = ex {Γ = Δ₀ ++ Γ ++ Γ₀} (ccut Δ₀ f g refl)
ccut ._ {Δ'} f (ex {Γ = Γ} {_} {A} {B} g) p | inj₂ (inj₁ (Γ₀ , refl , refl)) = ex {Γ = Γ} (ccut (Γ ++ A ∷ B ∷ Γ₀) f g refl)
ccut {Γ = Γ} Δ₀ {Δ'} f (ex {Δ = Δ} {A} {B} g) p | inj₂ (inj₂ (inj₁ (refl , refl , refl)))
    = ex-fma-cxt Γ (ccut (Δ₀ ++ A ∷ []) f g refl)
ccut {Γ = Γ'} Δ₀ f (ex {Γ = Γ} {Δ} {A} {B} g) p | inj₂ (inj₂ (inj₂ (refl , refl , refl)))
    = ex-cxt-fma Γ' (ccut Γ f g refl)

-- Equality of Proofs

data _≗_ : {S : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h
  pass : ∀{Γ}{A}{C}{f g : just A ∣ Γ ⊢ C} → f ≗ g → (pass f) ≗ (pass g)
  Il : ∀{Γ}{A}{f g : - ∣ Γ ⊢ A} → f ≗ g → Il f ≗ Il g
  ⊸r : ∀{S}{Γ}{A}{C}{f g : S ∣ Γ ++ A ∷ [] ⊢ C} → f ≗ g → ⊸r f ≗ ⊸r g
  ⊸l : ∀{Γ}{Δ}{A}{B}{C}{f g : nothing ∣ Γ ⊢ A}{f' g' : just B ∣ Δ ⊢ C}
    → f ≗ g → f' ≗ g' → ⊸l f f' ≗ ⊸l g g'
  axI : ax ≗ Il Ir
  ax⊸ : {A B : Fma} → ax {A ⊸ B} ≗ ⊸r (⊸l (pass ax) ax)
  ⊸rpass : {Γ : Cxt}{A B C : Fma} {f : just A ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (pass f) ≗ pass (⊸r f)
  ⊸rIl : {Γ : Cxt}{B C : Fma} {f : nothing ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (Il f) ≗ Il (⊸r f)
  ⊸r⊸l : {Γ Δ : Cxt}{A B C D : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : just B ∣ Δ ++ C ∷ [] ⊢ D}
    → ⊸r {Γ = Γ ++ Δ} (⊸l f g) ≗ ⊸l f (⊸r g)
  ex : ∀{S Γ Δ A B C}{f g : S ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → f ≗ g → ex f ≗ ex g
  exex : {S : Stp}{Γ₁ Γ₂ Γ₃ : Cxt} {A B A' B' C : Fma}
    → {f : S ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ++ A' ∷ B' ∷ Γ₃ ⊢ C}
    → ex {Γ = Γ₁ ++ B ∷ A ∷ Γ₂} (ex {Γ = Γ₁} f)
         ≗ ex {Γ = Γ₁} (ex {Γ = Γ₁ ++ A ∷ B ∷ Γ₂} f)
  expass : {Γ Δ : Cxt}{A' A B C : Fma}
    → {f : just A' ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → ex {Γ = A' ∷ Γ} (pass f) ≗ pass (ex f)  
  exIl : {Γ Δ : Cxt}{A B C : Fma}
    → {f : nothing ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → ex (Il f) ≗ Il (ex f)
  ex⊸r : {S : Stp} {Γ Δ : Cxt}{A' B' A B : Fma}
    → {f : S ∣ Γ ++ A ∷ B ∷ Δ ∷ʳ A' ⊢ B'}
    → ex (⊸r f) ≗ ⊸r (ex f)
  ex⊸l₁ : {Γ₁ Γ₂ Δ : Cxt}{A A' B B' C : Fma}
    → {f : nothing ∣ Γ₁ ++ A ∷ B ∷ Γ₂ ⊢ A'}{g : just B' ∣ Δ ⊢ C}
    → ex (⊸l f g) ≗ ⊸l (ex f) g
  ex⊸l₂ : {Γ Δ₁ Δ₂ : Cxt}{A B A' B' C : Fma}
    → {f : nothing ∣ Γ ⊢ A'}{g : just B' ∣ Δ₁ ++ A ∷ B ∷ Δ₂ ⊢ C}
    → ex {Γ = Γ ++ Δ₁} (⊸l f g) ≗ ⊸l f (ex g)
  ex-iso : ∀{S Γ Δ A B C} {f : S ∣ Γ ++ A ∷ B ∷ Δ ⊢ C}
    → ex {Γ = Γ} (ex {Γ = Γ} f) ≗ f
  ex-braid : ∀{S Γ Δ A B C D} {f : S ∣ Γ ++ A ∷ B ∷ C ∷ Δ ⊢ D}
    → ex {Γ = Γ} (ex {Γ = Γ ++ B ∷ []} (ex {Γ = Γ} f))
      ≗ ex {Γ = Γ ++ C ∷ []} (ex {Γ = Γ} (ex {Γ = Γ ++ A ∷ []} f))

≡-to-≗ : ∀{S}{Γ}{A}{f f' : S ∣ Γ ⊢ A} → f ≡ f' → f ≗ f'
≡-to-≗ refl = refl