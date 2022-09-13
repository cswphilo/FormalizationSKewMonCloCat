{-# OPTIONS --rewriting #-}

module Focusing where

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
open import Utilities hiding (++?)

-- 
-- 
-- The focused sequent calculus of skew symmetric monoidal closed categories

-- Tagged formulae
TFma : Set
TFma = (Tag × Fma)

TFmaEQ : TFma → TFma → Tag
TFmaEQ (∘ , A) (∘ , B) = fmaEQ A B
TFmaEQ (∙ , A) (∙ , B) = fmaEQ A B
TFmaEQ (∘ , A) (∙ , B) = ∘
TFmaEQ (∙ , A) (∘ , B) = ∘

TFma? : (x : Tag) → Set
TFma? ∘ = Fma
TFma? ∙ = TFma

-- Tagged contexts
TCxt : Set
TCxt = List (Tag × Fma)

TCxt? : Tag → Set
TCxt? x = List (TFma? x)

inTCxt : TFma → TCxt → Tag
inTCxt A [] = ∘
inTCxt A (B ∷ Γ) with TFmaEQ A B
... | ∘ = inTCxt A Γ
... | ∙ = ∙ 

-- White function for TFma and TCxt
whiteF : TFma → TFma
whiteF (t , y) = (∘ , y)

whiteL : TCxt → TCxt
whiteL [] = []
whiteL ((t , x) ∷ xs) = (∘ , x) ∷ whiteL xs

white++ : (Γ Δ : TCxt) → whiteL (Γ ++ Δ) ≡ whiteL Γ ++ whiteL Δ
white++ [] Δ = refl
white++ ((t , x) ∷ Γ) Δ = cong ((∘ , x) ∷_)  (white++ Γ Δ)

{-# REWRITE white++ #-}

-- Tag adding function for Fma and Cxt
tagF : Fma → TFma
tagF x = (∘ , x)

tagL : Cxt → TCxt
tagL [] = []
tagL (x ∷ x₁) = (∘ , x) ∷ tagL x₁

tagL++ : (Γ Δ : Cxt) → tagL Γ ++ tagL Δ ≡ tagL (Γ ++ Δ)
tagL++ [] Δ = refl
tagL++ (x ∷ Γ) Δ = cong ((∘ , x) ∷_) (tagL++ Γ Δ)

{-# REWRITE tagL++ #-}

tagL++₁ : (Γ Δ : Cxt) → tagL (Γ ++ Δ) ≡ tagL Γ ++ tagL Δ
tagL++₁ [] Δ = refl
tagL++₁ (x ∷ Γ) Δ = cong ((∘ , x) ∷_) (tagL++₁ Γ Δ)



-- tag erasing
ersF : TFma → Fma
ersF A = proj₂ A

ersL : TCxt → Cxt
ersL [] = []
ersL (x ∷ Γ) = proj₂ x ∷ ersL Γ

ersL++ : (Γ Δ : TCxt) → ersL (Γ ++ Δ) ≡ ersL Γ ++ ersL Δ
ersL++ [] Δ = refl
ersL++ (x ∷ Γ) Δ = cong (proj₂ x ∷_) (ersL++ Γ Δ)

{-# REWRITE ersL++ #-}

ersL? : (x : Tag) → TCxt? x → Cxt
ersL? ∘ Γ = Γ
ersL? ∙ Γ = ersL Γ

whiteL? : (x : Tag) → TCxt? x → TCxt
whiteL? ∘ Γ = tagL Γ
whiteL? ∙ Γ = whiteL Γ

whiteL₂ : Cxt → TCxt
whiteL₂ [] = []
whiteL₂ (x ∷ Γ) = (∘ , x) ∷ (whiteL₂ Γ)

black : Cxt → TCxt
black [] = []
black (x ∷ Γ) = (∙ , x) ∷ (black Γ)

black++ : (Γ Δ : Cxt) → black (Γ ++ Δ) ≡ black Γ ++ black Δ
black++ [] Δ = refl
black++ (x ∷ Γ) Δ = cong ((∙ , x) ∷_)  (black++ Γ Δ)

{-# REWRITE black++ #-}

blackErs : (Γ : Cxt) → ersL (black Γ) ≡ Γ
blackErs [] = refl
blackErs (x ∷ Γ) = cong (x ∷_) (blackErs Γ)

tagErs : (Γ : Cxt) → ersL (tagL Γ) ≡ Γ
tagErs [] = refl
tagErs (x ∷ Γ) = cong (x ∷_) (tagErs Γ)

whiteErs : (Γ : TCxt) →  ersL Γ ≡ ersL (whiteL Γ)
whiteErs [] = refl
whiteErs ((x , y) ∷ Γ) = cong (y ∷_) (whiteErs Γ)

{-# REWRITE blackErs #-}
{-# REWRITE tagErs #-}

white-tag : (Γ : Cxt) → whiteL (tagL Γ) ≡ tagL Γ
white-tag [] = refl
white-tag (x ∷ xs) = cong ((∘ , x) ∷_) (white-tag xs)

{-# REWRITE white-tag #-}

white-black-tag : (Γ : Cxt) →  whiteL (black Γ) ≡ tagL Γ
white-black-tag [] = refl
white-black-tag (x ∷ Γ) = cong ((∘ , x) ∷_) (white-black-tag Γ)

{-# REWRITE white-black-tag #-}
-- Sequents have 5 phases

-- c = context phase
data _∣_∣_؛_⊢c_ : (x : Tag) → Stp → TCxt? x → TCxt? x → Fma → Set

-- ri = right invertible phase
data _∣_∣_⊢ri_ : (x : Tag) → Stp → TCxt? x → Fma → Set

-- li = left invertible phase
data _∣_∣_⊢li_ : (x : Tag) → Stp → TCxt? x → Pos → Set

-- p = passivation phase
data _∣_∣_⊢p_ : (x : Tag) → Irr → TCxt? x → Pos → Set

-- f = focusing phase
data _∣_∣_⊢f_ : (x : Tag) → Irr → TCxt? x → Pos → Set

data _∣_∣_؛_⊢c_ where
  ex : {S : Stp} {Γ Δ Λ Ω Γ' : Cxt} {A : Fma} {C : Fma} → 
      (f :  ∘ ∣ S ∣ Γ ؛ Ω ⊢c C) (eq' : Γ' ≡ Γ ++ A ∷ []) (eq : Ω ≡ Δ ++ A ∷ Λ) → 
      ---------------------------------
       ∘ ∣ S ∣ Γ' ؛ Δ ++ Λ ⊢c C
  
  ex∙ : {S : Stp} {Γ Δ Λ Ω Γ' : TCxt} {A : Fma} {C : Fma} → 
      (f :  ∙ ∣ S ∣ Γ ؛ Ω ⊢c C) (eq' : Γ' ≡ Γ ++ (∙ , A) ∷ []) (eq : Ω ≡ Δ ++ (∙ , A) ∷ Λ) → 
      ---------------------------------
       ∙ ∣ S ∣ Γ' ؛ Δ ++ Λ ⊢c C

  ri2c : {x : Tag} {S : Stp} {Γ : TCxt? x} {C : Fma} →
         (f :  x ∣ S ∣ Γ ⊢ri C) → 
         ---------------------
          x ∣ S ∣ [] ؛ Γ ⊢c C

data _∣_∣_⊢ri_ where
  ⊸r : {S : Stp} {Γ : Cxt} {A : Fma} {B : Fma} → 
       (f :  ∘ ∣ S ∣  A ∷ [] ؛ Γ ⊢c B) →
       ---------------------------------
        ∘ ∣ S ∣ Γ ⊢ri A ⊸ B

  ⊸r∙ : {S : Stp} {Γ : TCxt} {A B : Fma} → 
        (f :  ∙ ∣ S ∣ (∙ , A) ∷ [] ؛ Γ ⊢c B) →
        -------------------------------
         ∙ ∣ S ∣ Γ ⊢ri A ⊸ B

  li2ri : {x : Tag} {S : Stp} {Γ : TCxt? x} {C : Pos} → 
          (f :  x ∣ S ∣ Γ ⊢li C) → 
          -----------------------
           x ∣ S ∣ Γ ⊢ri pos C

data _∣_∣_⊢li_ where
  Il : {Γ : Cxt} {C : Pos} → 
       (f :  ∘ ∣ - ∣ Γ ⊢li C) → 
       ----------------
        ∘ ∣ just I ∣ Γ ⊢li C

  ⊗l : {Γ : Cxt} {A B : Fma} {C : Pos} → 
       (f :  ∘ ∣ just A ∣ B ∷ [] ؛ Γ ⊢c pos C) → 
       --------------------------------
        ∘ ∣ just (A ⊗ B) ∣ Γ ⊢li C
  
  p2li : {x : Tag} {S : Irr} {Γ : TCxt? x} {C : Pos} →
         (f :  x ∣ S ∣ Γ ⊢p C) →
         ----------------------
          x ∣ irr S ∣ Γ ⊢li C

data _∣_∣_⊢p_ where
  pass : {Γ : Cxt} {A : Fma} {C : Pos} → 
         (f :  ∘ ∣ just A ∣ Γ ⊢li C) → 
         -----------------------
          ∘ ∣ (- , _) ∣ A ∷ Γ ⊢p C

  pass∙ : {Γ : TCxt} {A : Fma} {C : Pos} → 
          (f :  ∘ ∣ just A ∣ ersL Γ ⊢li C) → 
          -----------------------------
           ∙ ∣ (- , _) ∣ (∙ , A) ∷ Γ ⊢p C
  f2p : {x : Tag} {S : Irr} {Γ : TCxt? x} {C : Pos} → 
         (f : x ∣ S ∣ Γ ⊢f C) → 
         ----------------------
           x ∣ S ∣ Γ ⊢p C

data _∣_∣_⊢f_ where
  ax : {x : Tag} {X : At} → 
        x ∣ (just (` X) , _) ∣ [] ⊢f (` X , _)
  
  Ir : {x : Tag} → 
        x ∣ (- , _) ∣ [] ⊢f (I , _)
  
  ⊗r : {x : Tag} {S : Irr} {Γ Δ : TCxt? x} {A B : Fma} → 
       (f :  ∙ ∣ irr S ∣ whiteL? x Γ ⊢ri A) → (g :  ∘ ∣ - ∣ ersL? x Δ ⊢ri B) → 
       ---------------------------------------------------------------
        x ∣ S ∣ Γ ++ Δ ⊢f (A ⊗ B , _)
    
  ⊸l : {Γ Δ : Cxt} {A B : Fma} {C : Pos} →
       (f :  ∘ ∣ - ∣ Γ ⊢ri A) → (g :  ∘ ∣ just B ∣ Δ ⊢li C) → 
       -----------------------------------------------------------
        ∘ ∣ (just (A ⊸ B) , _) ∣  Γ ++ Δ ⊢f C

  ⊸l∙ : {Γ Λ Δ : TCxt} {A B : Fma} {D : Fma} {C : Pos} →
       (f :  ∘ ∣ - ∣ ersL (Γ ++ ((∙ , D) ∷ Λ)) ⊢ri A) → (g :  ∘ ∣ just B ∣ ersL Δ ⊢li C) → 
       -----------------------------------------------------------
        ∙ ∣ (just (A ⊸ B) , _) ∣ Γ ++ ((∙ , D) ∷ Λ) ++ Δ ⊢f C

--======================================================
-- We could not have syntactic sugar for white sequent because
-- Agda doesn't know how eq transported by tagL.

infix 15 _∣_∣_⊢ri_ _∣_∣_؛_⊢c_ _∣_∣_⊢li_ 
-- We don't display the white phase
_∣_؛_⊢c_ : Stp → Cxt → Cxt → Fma → Set
S ∣ Γ ؛ Δ ⊢c C =  ∘ ∣ S ∣ Γ ؛ Δ ⊢c C

_∣_⊢ri_ : Stp → Cxt → Fma → Set
S ∣ Γ ⊢ri C =  ∘ ∣ S ∣ Γ ⊢ri C

_∣_⊢li_ : Stp → Cxt → Pos → Set
S ∣ Γ ⊢li C =  ∘ ∣ S ∣ Γ  ⊢li C

_∣_⊢p_ : Irr → Cxt → Pos → Set
S ∣ Γ ⊢p C =  ∘ ∣ S ∣ Γ ⊢p C

_∣_⊢f_ : Irr → Cxt → Pos → Set
S ∣ Γ ⊢f C =  ∘ ∣ S ∣ Γ ⊢f C

--=======================================================

-- exchange rule in phase c
ex-c' : ∀{S} Φ {Ψ Γ Λ A B C} → S ∣ Λ ؛ Γ ⊢c C → Λ ≡ Φ ++ A ∷ B ∷ Ψ
  → S ∣ Φ ++ B ∷ A ∷ Ψ ؛ Γ ⊢c C 
ex-c' Φ {Ψ} {A = A} {B} (ex {Γ = Φ'} {A = A'} f refl eq') eq with cases++ Φ' Φ [] (A ∷ B ∷ Ψ) (sym eq)
... | inj₁ (Ψ₀ , p , q) = ⊥-elim ([]disj∷ Ψ₀ q) -- ex-c' formula is in the right context of exchanged formula A', which is impossible
ex-c' Φ {.[]} {A = A} {B} (ex {Γ = .(Φ₁ ++ _ ∷ [])} {Γ} {Δ} {A = B} (ex {Γ = Φ₁} {Γ₁} {Δ₁} f refl refl) refl eq') eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ Φ q | cases++ Γ Γ₁ Δ Δ₁ eq' -- ex-c' formula is in the left context of exchanged formula A'
... | refl , refl | inj₁ (Γ₀ , refl , refl) = ex {Γ = Φ ++ B ∷ []} {Γ ++ Γ₀} (ex {Γ = Φ} {Γ} f refl refl) refl refl
... | refl , refl | inj₂ (Γ₀ , refl , refl) = ex {Γ = Φ ++ B ∷ []} {Γ₁} (ex {Γ = Φ}{Γ₁ ++ A ∷ Γ₀} f refl refl) refl refl
ex-c' Φ {.[]} {A = A} {B} (ex {Γ = .[]} {A = .B} (ri2c f) refl eq') eq | inj₂ (A ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
ex-c' Φ {A = A} {B} (ex {Γ = .(Φ ++ A ∷ B ∷ Ψ₀)} {Γ} {A = A'} f refl refl) eq | inj₂ (A ∷ B ∷ Ψ₀ , refl , refl) = ex {Γ = Φ ++ _ ∷ _ ∷ Ψ₀} {Γ} (ex-c' _ f refl) refl refl
ex-c' Φ (ri2c f) eq = ⊥-elim ([]disj∷ Φ eq)

ex-c : ∀{S} Φ {Ψ Γ A B C} → S ∣ Φ ++ A ∷ B ∷ Ψ ؛ Γ ⊢c C
  → S ∣ Φ ++ B ∷ A ∷ Ψ ؛ Γ ⊢c C 
ex-c Φ f = ex-c' Φ f refl


-- ⊸r rule in phase c
⊸r-c' : {S : Stp} {Γ Λ Δ₀ Δ₁ : Cxt} {A : Fma} {B : Fma} → 
       (f : S ∣ Γ ؛ Λ ⊢c B) (eq : Λ ≡ Δ₀ ++ A ∷ Δ₁) → 
       -----------------------------------
          S ∣ Γ ؛ Δ₀ ++ Δ₁ ⊢c A ⊸ B
⊸r-c' {Δ₀ = Δ₀} {Δ₁ = Δ₁} (ex {Δ = Δ} {Λ = Λ} f refl eq1) eq with cases++ Δ₀ Δ Δ₁ Λ eq
⊸r-c' {Δ₀ = Δ₁} {_} (ex {Δ = _} {Λ = Λ} f refl refl) refl | inj₁ (Δ₀ , refl , refl) = ex {Δ = (Δ₁ ++ Δ₀)} (⊸r-c' f refl) refl refl
--                                                                               exchaged formula is in the right context of ⊸r-c' formula
⊸r-c' {Δ₀ = _} {_} (ex {Δ = Δ} {_} f refl refl) refl | inj₂ (Δ₀ , refl , refl) = ex (⊸r-c' {Δ₀ = (Δ ++ _ ∷ Δ₀)} f refl) refl refl
--                                                                               exchaged formula is in the left context of ⊸r-c' formula
⊸r-c' (ri2c f) eq = ri2c (⊸r (ex (ri2c f) refl eq))

⊸r-c'' : {S : Stp} {Γ Γ' Δ : Cxt} {A B : Fma} → 
       (f : S ∣ Γ' ؛ Δ ⊢c B) (eq : Γ' ≡ Γ ++ A ∷ []) →
       -----------------------------------------
           S ∣ Γ ؛ Δ ⊢c A ⊸ B
⊸r-c'' {Γ = Γ₁} (ex {Γ = Γ} f refl refl) eq with snoc≡ Γ Γ₁ eq
... | refl , refl = ⊸r-c' f refl
⊸r-c'' {Γ = Γ} (ri2c f) eq = ⊥-elim ([]disj∷ Γ eq)

⊸r-c : {S : Stp} {Γ Δ : Cxt} {A B : Fma} → 
       (f : S ∣ Γ ++ A ∷ [] ؛ Δ ⊢c B) →
       -----------------------------------------
           S ∣ Γ ؛ Δ ⊢c A ⊸ B
⊸r-c f = ⊸r-c'' f refl

⊸r-ex-c : {S : Stp} {Γ₀ Γ₁ : Cxt} {A : Fma} {B : Fma} → 
          (f : S ∣ [] ؛ Γ₀ ++ A ∷ Γ₁ ⊢c B) →
          ------------------------------------
             S ∣ Γ₀ ++ Γ₁ ⊢ri A ⊸ B
⊸r-ex-c f = ⊸r (ex f refl refl)

-- ⊗l rule in phase c
⊗l-ri : {Γ Δ Ω : Cxt} {A B C : Fma} → 
          (f : just A ∣ Ω ⊢ri C) (eq : Ω ≡ Δ ++ B ∷ Γ) → 
             just (A ⊗ B) ∣ Δ ++ Γ ⊢ri C
⊗l-ri (⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq₀ eq)) p = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq₀)))
⊗l-ri {Γ} {Δ₁} (⊸r (ex {Δ = Δ} {Λ} (ri2c f) refl refl)) p with cases++ Δ₁ Δ Γ Λ p
... | inj₁ (Δ₀ , refl , refl) = ⊸r (ex {Δ = Δ₁ ++ Δ₀} (ri2c (⊗l-ri f refl)) refl refl) 
... | inj₂ (Δ₀ , refl , refl) = ⊸r (ex {Δ = Δ} (ri2c (⊗l-ri {Δ = Δ ++ _ ∷ Δ₀} f refl)) refl refl)
⊗l-ri (li2ri {C = C} f) refl = li2ri {C = C} (⊗l (ex (ri2c (li2ri f)) refl refl))

⊗l-c' : ∀ {Γ Γ' Δ A B C} (f : just A ∣ Γ' ؛ Δ ⊢c C) (p : Γ' ≡ B ∷ Γ) → 
                             just (A ⊗ B) ∣ Γ ؛ Δ ⊢c C
⊗l-c' (ex {Γ = []} (ex {Γ = Γ} f eq'' eq₂) eq' eq) eq₁ = ⊥-elim ([]disj∷ Γ eq'')
⊗l-c' (ex {Γ = []} (ri2c f) refl refl) refl = ri2c (⊗l-ri f refl)
⊗l-c' (ex {Γ = A' ∷ Φ} f refl refl) refl = ex (⊗l-c' f refl) refl refl



⊗l-c : ∀ {Γ Δ A B C} → just A ∣ B ∷ Γ ؛ Δ ⊢c C → just (A ⊗ B) ∣ Γ ؛ Δ ⊢c C
⊗l-c f = ⊗l-c' f refl

-- -- Il rule in phase c
Il-c : {Γ Δ : Cxt} {C : Fma} →
         (f : - ∣ Γ ؛ Δ ⊢c C) → 
         -------------------------
              just I ∣ Γ ؛ Δ ⊢c C
Il-ri : {Γ : Cxt} {C : Fma} → 
        (f : - ∣ Γ ⊢ri C) →
        --------------------
             just I ∣ Γ ⊢ri C

Il-c (ex f refl eq) = ex (Il-c f) refl eq
Il-c (ri2c f) = ri2c (Il-ri f)
Il-ri (⊸r f) = ⊸r (Il-c f)
Il-ri (li2ri f) = li2ri (Il f)

-- pass rule in phase c


pass-c' : {Γ Δ Γ' : Cxt} {A C : Fma} → 
          (f : just A ∣ Γ ؛ Δ ⊢c C) (eq : Γ' ≡ A ∷ Γ) → 
          ------------------------------
               - ∣ Γ' ؛ Δ ⊢c C
pass-ri : {Γ : Cxt} {A C : Fma} → 
          (f : just A ∣ Γ ⊢ri C) → 
          ------------------------------
              - ∣ A ∷ Γ ⊢ri C
pass-c : {Γ Δ : Cxt} {A C : Fma} → 
          (f : just A ∣ Γ ؛ Δ ⊢c C) → 
          ------------------------------
              - ∣ A ∷ Γ ؛ Δ ⊢c C
pass-c' {A = A'} (ex {Γ = Γ} {Δ} {Λ} {A = A} f refl refl) eq = ex {Γ = A' ∷ Γ} {Δ} {Λ} {A = A} (pass-c' f refl) eq refl
pass-c' {Δ = Δ} {A = A} (ri2c (⊸r f)) refl = ex {Γ = []} {Δ = []} (ri2c (pass-ri (⊸r f))) refl refl
pass-c' {Δ = Δ} {A = A} (ri2c (li2ri f)) refl = ex {Γ = []} {Δ = []} (ri2c (li2ri (p2li (pass f)))) refl refl
pass-ri {Γ = .(_)} {A = A'} (⊸r {A = A} (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq)) = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
pass-ri {Γ = .(_)} {A = A'} (⊸r {A = A} (ex {Δ = Δ} {Λ = Λ} (ri2c f) refl refl)) = ⊸r (ex {Γ = []} {Δ = A' ∷ Δ} {Λ = Λ} (ri2c (pass-ri f)) refl refl)  -- ⊸r (act [] (ex-c [] (pass-c f refl)) refl refl)
pass-ri (li2ri f) = li2ri (p2li (pass f))

pass-c f = pass-c' f refl
-- ⊸l in phase c

⊸l-c : {Γ Δ Ω : Cxt} {A B C : Fma} →
       (f : - ∣ Γ ؛ [] ⊢c A) (g : just B ∣ Ω ؛ Δ ⊢c C) → 
       -----------------------------------------------
             just (A ⊸ B) ∣ Γ ++ Ω ؛ Δ ⊢c C
⊸l-c-ri : {Γ Δ Ω : Cxt} {A B C : Fma} →
       (f : - ∣ Ω ؛ Γ ⊢c A) (g : just B ∣ Δ ⊢ri C) → 
       -----------------------------------------------
             just (A ⊸ B) ∣ Ω ؛ Γ ++ Δ ⊢c C
⊸l-ri : {Γ Δ : Cxt} {A B C : Fma} →
        (f : - ∣ Γ ⊢ri A) (g : just B ∣ Δ ⊢ri C) →
        ------------------------------------------------
             just (A ⊸ B) ∣ Γ ++ Δ ⊢ri C
⊸l-ri-c : {Γ Δ Ω : Cxt} {A B C : Fma} →
        (f : - ∣ Γ ⊢ri A) (g : just B ∣ Ω ؛ Δ ⊢c C) →
        ------------------------------------------------
              just (A ⊸ B) ∣ Ω ؛ Γ ++ Δ ⊢c C
⊸l-c f (ex g refl refl) = ex (⊸l-c f g) refl refl
⊸l-c f (ri2c g) = ⊸l-c-ri f g

⊸l-c-ri (ex f refl refl) g = ex (⊸l-c-ri f g) refl refl
⊸l-c-ri (ri2c f) g = ri2c (⊸l-ri f g)

⊸l-ri f (⊸r g) = ⊸r (⊸l-ri-c f g)
⊸l-ri f (li2ri g) = li2ri (p2li (f2p (⊸l f g)))

⊸l-ri-c {Γ = Γ} f (ex {Δ = Δ} {Λ} g refl refl) = ex {Δ = Γ ++ Δ} {Λ} (⊸l-ri-c f g) refl refl
⊸l-ri-c f (ri2c g) = ri2c (⊸l-ri f g)
-- ex {Γ = Γ} {Δ} {Λ} (⊸l-c {Γ} {Δ = Δ ++ _ ∷ Λ} f g) refl refl
-- ⊸l-c (ex {Γ = Γ} f eq' eq) (ri2c g) = ⊥-elim ([]disj∷ Γ eq')
-- ⊸l-c (ri2c f) (ri2c g) = ri2c (⊸l-ri f g) 
-- ⊸l-ri {Γ} f (⊸r {A = A} (ex (ex {Γ = x ∷ Γ₁} g refl refl) eq' eq)) = ⊥-elim ([]disj∷ Γ₁ (proj₂ (inj∷ eq')))
-- ⊸l-ri {Γ} f (⊸r {A = A} (ex {Δ = Δ} {Λ = Λ} (ri2c g) refl refl)) = ⊸r (ex {Γ = []} {Δ = Γ ++ Δ} {Λ = Λ} (ri2c (⊸l-ri {Γ = Γ} {Δ = Δ ++ _ ∷ Λ} f g)) refl refl) 
-- ⊸l-ri {Γ} {Δ} f (li2ri {C = C} g) = li2ri {C = C} (p2li (f2p (⊸l {Γ = Γ} {Δ = Δ} f g)))


-- ⊗r rule in phase c


{-
The isInter data type aims to capture the nature of context in ⊸r⋆ and gen⊗rs.
Context Γ splits into Γ₀ and ­Γ­₁ where the order of formulas in Γ₀ should keep the same.
-}
data isInter {A : Set} : List A → List A → List A → Set where
  isInter[] : isInter [] [] []
  []left : {x : A} → {xs : List A} → isInter [] (x ∷ xs) (x ∷ xs)
  []right : {x : A} →  {xs : List A} → isInter (x ∷ xs) [] (x ∷ xs)
  ∷left : {x y : A} {xs ys zs : List A} → isInter xs (y ∷ ys) zs → isInter (x ∷ xs) (y ∷ ys) (x ∷ zs)
  ∷right : {x y : A} {xs ys zs : List A} → isInter (x ∷ xs) ys zs → isInter (x ∷ xs) (y ∷ ys) (y ∷ zs)

isInter-sym : {X : Set} → {xs ys zs : List X} → isInter xs ys zs → isInter ys xs zs
isInter-sym isInter[] = isInter[]
isInter-sym []left = []right
isInter-sym []right = []left
isInter-sym (∷left eq) = ∷right (isInter-sym eq)
isInter-sym (∷right eq) = ∷left (isInter-sym eq)

isInter-left[] : {X : Set} → {xs zs : List X} → (eq : isInter xs [] zs) → xs ≡ zs
isInter-left[] isInter[] = refl
isInter-left[] []right = refl

isInter-right[] : {X : Set} → {ys zs : List X} → (eq : isInter [] ys zs) → ys ≡ zs
isInter-right[] isInter[] = refl
isInter-right[] []left = refl

isInter-end[] : {X : Set} → {xs ys : List X} → (eq : isInter xs ys []) → [] ≡ xs ++ ys
isInter-end[] isInter[] = refl

[]right' : {A : Set} → (xs : List A) → isInter xs [] xs
[]right' [] = isInter[]
[]right' (x ∷ xs) = []right

∷left' : {A : Set} → {x : A} → {xs zs : List A} → (ys : List A) → isInter xs ys zs → isInter (x ∷ xs) ys (x ∷ zs)
∷left' [] eq with isInter-left[] eq
... | refl = []right
∷left' (x ∷ ys) eq = ∷left eq

∷right' : {A : Set} → {x : A} → {ys zs : List A} → (xs : List A) → isInter xs ys zs → isInter xs (x ∷ ys) (x ∷ zs)
∷right' xs eq = isInter-sym (∷left' xs (isInter-sym eq))


isInter++r : {X : Set} → {xs' ys' zs' : List X} → (ys : List X) → isInter xs' ys' zs' → isInter (xs') (ys ++ ys') (ys ++ zs')
isInter++r [] eq = eq
isInter++r {xs' = []} (x ∷ ys) eq with isInter-left[] (isInter-sym eq)
... | refl = []left
isInter++r {xs' = x₁ ∷ xs'} (x ∷ ys) eq = ∷right (isInter++r ys eq)

isInter++l : {X : Set} → {xs' ys' zs' : List X} → (ys : List X) → isInter xs' ys' zs' → isInter (ys ++ xs') (ys') (ys ++ zs')
isInter++l ys inTeq = isInter-sym (isInter++r ys (isInter-sym inTeq))

isInter-split : {X : Set} → {xs ys₀ ys₁ zs ys : List X} → {y : X} → (ys ≡ ys₀ ++ y ∷ ys₁) → isInter xs ys zs → 
             Σ (List X) (λ xs₀ → Σ (List X) (λ xs₁ → Σ (List X) (λ zs₀ → Σ (List X) (λ zs₁ → 
             xs ≡ xs₀ ++ xs₁ × zs ≡ zs₀ ++ y ∷ zs₁ × isInter xs₀ ys₀ zs₀ × isInter xs₁ ys₁ zs₁
             ))))
isInter-split {ys₀ = ys₀} eq isInter[] = ⊥-elim ([]disj∷ ys₀ eq) -- imposs
isInter-split {ys₀ = ys₀} {ys₁} eq []left = ([] , [] , ys₀ , ys₁ , (refl , eq , isInter-sym ([]right' ys₀) , isInter-sym ([]right' ys₁)))
isInter-split {ys₀ = ys₀} eq []right = ⊥-elim ([]disj∷ ys₀ eq) -- imposs
isInter-split eq (∷left eq') with isInter-split eq eq'
... | xs₀ , xs₁ , zs₀ , zs₁ , refl , refl , inTeq , inTeq' = ((_ ∷ xs₀) , xs₁ , (_ ∷ zs₀) , zs₁ , refl , refl , ∷left' _ inTeq , inTeq')
isInter-split {ys₀ = []} refl (∷right {x} {xs = xs} {zs = zs} eq') = ([] , (x ∷ xs) , [] , zs , refl , refl , isInter[] , eq')
isInter-split {ys₀ = x ∷ ys₀} refl (∷right eq') with isInter-split refl eq'
... | xs₀ , xs₁ , zs₀ , zs₁ , eq₀ , refl , inTeq , inTeq' = (xs₀ , xs₁ , (_ ∷ zs₀) , zs₁ , eq₀ , refl , isInter++r (_ ∷ []) inTeq , inTeq')


isInter-split-left : {X : Set} → {xs xs₀ xs₁ zs ys : List X} → {x : X} → (xs ≡ xs₀ ++ x ∷ xs₁) → isInter xs ys zs → 
             Σ (List X) (λ ys₀ → Σ (List X) (λ ys₁ → Σ (List X) (λ zs₀ → Σ (List X) (λ zs₁ → 
             ys ≡ ys₀ ++ ys₁ × zs ≡ zs₀ ++ x ∷ zs₁ × isInter xs₀ ys₀ zs₀ × isInter xs₁ ys₁ zs₁
             ))))
isInter-split-left eq inTeq with isInter-split eq (isInter-sym inTeq)
... | ys₀ , ys₁ , zs₀ , zs₁ , refl , refl , inTeq₀ , inTeq₁ = ys₀ , ys₁ , zs₀ , zs₁ , refl , refl , isInter-sym inTeq₀ , isInter-sym inTeq₁

isInter++ : {X : Set} → {xs xs' ys ys' zs zs' : List X} → isInter xs ys zs → isInter xs' ys' zs' → isInter (xs ++ xs') (ys ++ ys') (zs ++ zs')
isInter++ isInter[] eq' = eq'
isInter++ ([]left {x} {xs}) eq' = isInter++r (x ∷ xs) eq'
isInter++ ([]right {x} {xs}) eq' = isInter-sym (isInter++r ((x ∷ xs)) (isInter-sym eq'))
isInter++ (∷left eq) eq' = ∷left (isInter++ eq eq')
isInter++ (∷right eq) eq' = ∷right (isInter++ eq eq')


[]++ : {X : Set} → {xs ys : List X} → [] ≡ xs ++ ys → xs ≡ [] × ys ≡ []
[]++ {xs = xs} {ys} eq = ++-conicalˡ xs ys (sym eq) , ++-conicalʳ xs ys (sym eq)

isInter++? : {X : Set} → {xs ys zs : List X} → (zs₀ zs₁ : List X) → zs ≡ zs₀ ++ zs₁ → isInter xs ys zs → 
                         Σ (List X) (λ xs₀ → Σ (List X) (λ xs₁ → Σ (List X) (λ ys₀ → Σ (List X) (λ ys₁ → xs ≡ xs₀ ++ xs₁ × ys ≡ ys₀ ++ ys₁ × isInter xs₀ ys₀ zs₀ × isInter xs₁ ys₁ zs₁))))
isInter++? zs₀ zs₁ eq isInter[] with []++ {xs = zs₀} {zs₁} eq
... | refl , refl = [] , [] , [] , [] , refl , refl , isInter[] , isInter[]
isInter++? [] (x ∷ zs₁) refl []left = [] , [] , [] , (x ∷ zs₁) , refl , refl , isInter[] , []left
isInter++? (x ∷ zs₀) zs₁ refl []left = []  , [] , (x ∷ zs₀) , zs₁ , refl , refl , []left , isInter-sym ([]right' zs₁)
isInter++? [] (x ∷ zs₁) refl []right = [] , (x ∷ zs₁)  , [] , [] , refl , refl , isInter[] , []right
isInter++? (x ∷ zs₀) zs₁ refl []right = (x ∷ zs₀) , zs₁ , [] , [] , refl , refl , []right , []right' zs₁
isInter++? [] (x ∷ zs₁) refl (∷left {y = y} {xs} {ys = ys} inTeq) = [] , (x ∷ xs) , [] , (y ∷ ys) , refl , refl , isInter[] , ∷left inTeq
isInter++? (x ∷ zs₀) zs₁ refl (∷left inTeq) with isInter++? zs₀ zs₁ refl inTeq
... | xs₀' , xs₁' , ys₀' , ys₁' , refl , eq₁ , inTeq' , inTeq'' = (x ∷ xs₀') , xs₁' , ys₀' , ys₁' , refl , eq₁ , ∷left' ys₀' inTeq' , inTeq''
isInter++? [] (x ∷ zs₁) refl (∷right {x₁} {xs = xs} {ys} inTeq) = [] , (x₁ ∷ xs) , [] , (x ∷ ys) , refl , refl , isInter[] , ∷right inTeq
isInter++? (x ∷ zs₀) zs₁ refl (∷right inTeq) with isInter++? zs₀ zs₁ refl inTeq
... | xs₀' , xs₁' , ys₀' , ys₁' , eq₀ , refl , inTeq' , inTeq'' = xs₀' , xs₁' , (x ∷ ys₀') , ys₁' , eq₀ , refl , isInter-sym (∷left' xs₀' (isInter-sym inTeq')) , inTeq''


infix 3 _↭'_

data _↭'_ {A : Set} : List A → List A → Set where
  empty  : ∀ {xs} → xs ≡ []  → xs ↭' []
  cons : ∀ {xs xs₀ xs₁ y ys} → xs ≡ xs₀ ++ y ∷ xs₁ → (xs₀ ++ xs₁) ↭' ys → xs ↭' (y ∷ ys)


snoc↭' : {A : Set} → {xs xs₀ xs₁ ys : List A} → {y : A} → xs ≡ xs₀ ++ y ∷ xs₁ → (xs₀ ++ xs₁) ↭' ys → xs ↭' ys ∷ʳ y
snoc↭' {xs₀ = xs₀} {xs₁} eq (empty x) with []++ {xs = xs₀} {xs₁} (sym x)
snoc↭' {xs₀ = .[]} {.[]} refl (empty x) | refl , refl = cons {xs₀ = []} {[]} refl (empty x)
snoc↭' {xs₀ = xs₂} {xs₃} refl (cons {xs₀ = xs₀} {xs₁} x eq') with cases++ xs₀ xs₂ xs₁ xs₃ x
... | inj₁ (ys₀ , refl , refl) = cons {xs₀ = xs₀} {ys₀ ++ _ ∷ xs₃} refl (snoc↭' {xs₀ = xs₀ ++ ys₀} {xs₃} refl eq')
... | inj₂ (zs₀ , refl , refl) = cons {xs₀ = xs₂ ++ _ ∷ zs₀} {xs₁} refl (snoc↭' {xs₀ = xs₂} {zs₀ ++ xs₁} refl eq')
-- trans↭' : {A : Set} → {xs ys zs : List A} → xs ↭' ys → ys ↭' zs → xs ↭' zs
-- trans↭' (empty refl) eq' = eq'
-- trans↭' (cons x eq) (cons x₁ eq') = {!   !}

⊸r⋆ : {S : Stp} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {A : Fma} →
      (f : S ∣ Γ ⊢ri A) (eq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁) → 
      ----------------------------------------
           S ∣ Γ₀ ⊢ri Γ₁ ⊸⋆ A
⊸r⋆ .[] f eq (empty refl) with isInter-left[] eq
... | refl = f
⊸r⋆ (D ∷ Γ₁) f eq (cons {xs₀ = Γ₀₁'} {Γ₁₁'} refl peq) with isInter-split refl eq
... | Γ₀₀ , Γ₀₁ , Λ₀ , Λ₁ , refl , refl , inTeq , inTeq' = ⊸r (ex {Δ = Γ₀₀} {Γ₀₁} (ri2c (⊸r⋆ Γ₁ f (isInter++ inTeq inTeq'') peq)) refl refl)
  where inTeq'' : isInter (D ∷ Γ₀₁) (Γ₁₁') (D ∷ Λ₁)
        inTeq'' = isInter++l (D ∷ []) inTeq'


⊸r⋆∙ : {S : Stp} {Γ Γ₀ : TCxt} → {Γ₁' : Cxt} (Γ₁ : Cxt) {A : Fma} →
      (f : ∙ ∣ S ∣ Γ ⊢ri A) (eq : isInter Γ₀ (black Γ₁') Γ) (peq : Γ₁' ↭' Γ₁) → 
      ----------------------------------------
      ∙ ∣ S ∣ Γ₀ ⊢ri Γ₁ ⊸⋆ A
⊸r⋆∙ {Γ₁' = Γ₁'} [] f eq (empty refl) with isInter-left[] eq
... | refl = f
⊸r⋆∙ (D ∷ Γ₁) f eq (cons {xs₀ = Γ₀₁'} {Γ₁₁'} refl peq) with isInter-split (black++ Γ₀₁' (D ∷ Γ₁₁')) eq
... | Γ₀₀ , Γ₀₁ , Λ₀ , Λ₁ , refl , refl , inTeq , inTeq' = ⊸r∙ (ex∙ {Δ = Γ₀₀} {Γ₀₁} (ri2c (⊸r⋆∙ Γ₁ f (isInter++ inTeq inTeq'') peq)) refl refl)
  where inTeq'' : isInter ((∙ , D) ∷ Γ₀₁) (black Γ₁₁') ((∙ , D) ∷ Λ₁)
        inTeq'' = isInter++l ((∙ , D) ∷ []) inTeq'



-- ⊗r-c-c : {S : Stp} {Ω Γ Δ : Cxt} {A B : Fma} → 
--           (f : ∘ ∣ S ∣ Ω ؛ [] ⊢c A) (g : ∘ ∣ - ∣ Γ ؛ Δ ⊢c B) → 
--           ----------------------------------------------
--           ∘ ∣ S ∣ Ω ++ Γ ؛ Δ ⊢c A ⊗ B
-- ⊗r-c-ri : {S : Stp} {Ω Γ Δ : Cxt} {A B : Fma} → 
--        (f : ∘ ∣ S ∣ Ω ؛ Γ ⊢c A) (g : ∘ ∣ - ∣ Δ ⊢ri B)  → 
--        ------------------------------------------------
--        ∘ ∣ S ∣ Ω ؛ Γ ++ Δ ⊢c A ⊗ B 

-- ⊗r-c-c f (ex g refl refl) = ex (⊗r-c-c f g) refl refl
-- ⊗r-c-c f (ri2c g) = ⊗r-c-ri f g

-- ⊗r-c-ri (ex f refl refl) g = ex (⊗r-c-ri f g) refl refl
-- ⊗r-c-ri (ri2c f) g = ri2c (li2ri (gen⊗r-ri [] f g refl))

empty↭' : {A : Set} → {xs : List A} → [] ↭' xs → xs ≡ []
empty↭' (empty x) = refl
empty↭' (cons {xs₀ = xs₀} x peq) = ⊥-elim ([]disj∷ xs₀ x)

tag-lem : {Γ₀ Γ₁ Γ : Cxt} → isInter Γ₀ Γ₁ Γ → Σ (TCxt) (λ Γ' → isInter (tagL Γ₀) (black Γ₁) Γ' × ersL Γ' ≡ Γ)
tag-lem isInter[] = [] , isInter[] , refl
tag-lem ([]left {x} {xs}) = ((black (x ∷ xs)) , []left , cong (x ∷_) (blackErs xs))
tag-lem ([]right {x} {xs}) = ((tagL (x ∷ xs)) , []right , cong (x ∷_) (tagErs xs))
tag-lem (∷left {x = x} eq) with tag-lem eq
... | Γ' , eq' , refl = ((∘ , x) ∷ Γ') , ∷left eq' , refl
tag-lem (∷right {x} {y} eq) with tag-lem eq
... | Γ' , eq' , refl = (∙ , y) ∷ Γ' , ∷right eq' , refl

tag-isInter : {Γ₀ Γ₁ Γ : Cxt} → isInter Γ₀ Γ₁ Γ → TCxt
tag-isInter {.[]} {.[]} {.[]} isInter[] = []
tag-isInter {.[]} {Γ₁} {Γ₁} []left = black Γ₁
tag-isInter {Γ₀} {.[]} {Γ₀} []right = tagL Γ₀
tag-isInter {A ∷ Γ₀} {.(_ ∷ _)} {A ∷ Γ} (∷left eq) = (∘ , A) ∷ (tag-isInter eq )
tag-isInter {.(_ ∷ _)} {A ∷ Γ₁} {A ∷ Γ} (∷right eq) = (∙ , A) ∷ (tag-isInter eq)

tag-lem' :  {Γ₀ Γ₁ Γ : Cxt} → (eq : isInter Γ₀ Γ₁ Γ) → Σ (TCxt) (λ Γ' → isInter (tagL Γ₀) (black Γ₁) Γ' × Γ' ≡ tag-isInter eq)
tag-lem' isInter[] = [] , isInter[] , refl
tag-lem' ([]left {x} {xs}) = black (x ∷ xs) , []left , refl
tag-lem' ([]right {x} {xs}) = tagL (x ∷ xs) , []right , refl
tag-lem' (∷left {x} eq) with tag-lem' eq
... | .(tag-isInter eq) , eq₀ , refl = (∘ , x) ∷ tag-isInter eq , ∷left eq₀ , refl
tag-lem' (∷right {x} {y} eq) with tag-lem' eq
... | .(tag-isInter eq) , eq₀ , refl = (∙ , y) ∷ tag-isInter eq , ∷right eq₀ , refl

tag-lem-left[] : {Γ₀ Γ : Cxt} → (eq : isInter Γ₀ [] Γ) → Σ (TCxt) (λ Γ' → isInter (tagL Γ₀) [] Γ' × Γ' ≡ tagL Γ₀)
tag-lem-left[] isInter[] = [] , isInter[] , refl
tag-lem-left[] ([]right {x} {xs}) = (∘ , x) ∷ tagL xs , []right , refl

tag-lem-right[] : {Γ₀ Γ : Cxt} → (eq : isInter [] Γ₀ Γ) → Σ (TCxt) (λ Γ' → isInter [] (black Γ₀) Γ' × Γ' ≡ black Γ₀)
tag-lem-right[] isInter[] = [] , isInter[] , refl
tag-lem-right[] ([]left {x} {xs}) = (∙ , x) ∷ black xs , []left , refl

tagers-isInter : {Γ₀ Γ₁ Γ : Cxt} → (eq : isInter Γ₀ Γ₁ Γ) → ersL (tag-isInter eq) ≡ Γ
tagers-isInter isInter[] = refl
tagers-isInter []left = refl
tagers-isInter ([]right {x} {xs}) = cong (x ∷_) (tagErs xs)
tagers-isInter (∷left {x} eq) with tagers-isInter eq
... | eq' = cong (x ∷_) eq'
tagers-isInter (∷right {y = y} eq) with tagers-isInter eq
... | eq' = cong (y ∷_) eq'

{-# REWRITE tagers-isInter #-}

whiteL-isInter : {Γ₀ Γ₁ Γ : Cxt} → (eq : isInter Γ₀ Γ₁ Γ) → whiteL (tag-isInter eq) ≡ tagL Γ
whiteL-isInter isInter[] = refl
whiteL-isInter []left = refl
whiteL-isInter []right = refl
whiteL-isInter (∷left {x} eq) with whiteL-isInter eq 
... | eq' = cong ((∘ , x) ∷_) eq'
whiteL-isInter (∷right {y = y} eq) with whiteL-isInter eq 
... | eq' = cong ((∘ , y) ∷_) eq'

{-# REWRITE whiteL-isInter #-}

⊗r-c-ri : {S : Stp} {Ω Γ Δ : Cxt} {A B : Fma} → 
       (f : S ∣ Ω ؛ Γ ⊢c A) (g : - ∣ Δ ⊢ri B)  → 
       ------------------------------------------------
            S ∣ Ω ؛ Γ ++ Δ ⊢c A ⊗ B 

gen⊗r-ri : {S : Stp} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A : Fma} {B : Fma} → 
            (f : S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B) (eq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁) →
        -----------------------------------------------------------
                    S ∣ Γ₀ ++ Δ ⊢li (((Γ₁ ⊸⋆ A) ⊗ B) , _)

gen⊗r-li : {S : Stp} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A : Pos} {B : Fma} → 
            (f : S ∣ Γ ⊢li A) (g : - ∣ Δ ⊢ri B) (eq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁) →
        -----------------------------------------------------------
                    S ∣ Γ₀ ++ Δ ⊢li ((Γ₁ ⊸⋆ (pos A)) ⊗ B , _)

gen⊗r-p : {S : Irr} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A : Pos} {B : Fma} → 
            (f : S ∣ Γ ⊢p A) (g : - ∣ Δ ⊢ri B) (eq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁) →
        -----------------------------------------------------------
                    S ∣ Γ₀ ++ Δ ⊢p ((Γ₁ ⊸⋆ (pos A)) ⊗ B , _)

gen⊗r-f : {S : Irr} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A : Pos} {B : Fma} → 
            (f : S ∣ Γ ⊢f A) (g : - ∣ Δ ⊢ri B) (eq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁) →
        -----------------------------------------------------------
                    S ∣ Γ₀ ++ Δ ⊢f ((Γ₁ ⊸⋆ (pos A)) ⊗ B , _)


⊗r-c-ri {Δ = Δ₁} (ex {Δ = Δ} {Λ} f refl refl) g = ex {Δ = Δ} {Λ ++ Δ₁} (⊗r-c-ri f g) refl refl
⊗r-c-ri {Γ = Γ} {Δ} (ri2c f) g = ri2c (li2ri (gen⊗r-ri {Γ = Γ} {Γ} {[]} [] {Δ} f g ([]right' Γ) (empty refl)))

gen⊗r-ri Γ₁ (⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) g eq peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
gen⊗r-ri Γ₁ {Δ = Δ₁} (⊸r (ex {Δ = Δ} {Λ} (ri2c f) refl refl)) g eq peq with isInter++? Δ Λ refl eq
... | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , refl , refl , inTeq' , inTeq'' = gen⊗r-ri (Γ₁ ∷ʳ _) f g ((isInter++ inTeq' (∷right' Γ₀₁ inTeq''))) ((snoc↭' refl peq))
gen⊗r-ri Γ₁ (li2ri f) g eq peq = gen⊗r-li Γ₁ f g eq peq

gen⊗r-li Γ₁ (Il f) g eq peq = Il (gen⊗r-li Γ₁ f g eq peq)
gen⊗r-li Γ₁ (⊗l (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) g eq peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
gen⊗r-li Γ₁ {Δ = Δ₁} (⊗l {B = B} (ex {Δ = Δ} {Λ} (ri2c (li2ri f)) refl refl)) g eq peq with isInter++? Δ Λ refl eq
... | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , refl , refl , inTeq' , inTeq'' = ⊗l (ex {Δ = Γ₀₀} {Γ₀₁ ++ Δ₁} (ri2c (li2ri (gen⊗r-li Γ₁ f g (isInter++ inTeq' (∷left' Γ₁₁' inTeq'')) peq))) refl refl)
gen⊗r-li Γ₁ (p2li f) g eq peq = p2li (gen⊗r-p Γ₁ f g eq peq)


gen⊗r-p Γ₁ (pass {Γ} f) g []left peq = f2p (⊗r (⊸r⋆∙ {Γ₀ = []} Γ₁ (li2ri (p2li (pass∙ f))) []left peq) g)
gen⊗r-p Γ₁ (pass {Γ = Γ} f) g []right peq with empty↭' peq
... | refl = pass (gen⊗r-li [] f g ([]right' Γ) (empty refl))
gen⊗r-p Γ₁ (pass f) g (∷left eq) peq = pass (gen⊗r-li Γ₁ f g eq peq)
gen⊗r-p Γ₁ (pass f) g (∷right {A'} {xs = Γ₀} eq) peq with tag-lem eq
... | Γ' , eq' , refl = f2p (⊗r {Γ = A' ∷ Γ₀} (⊸r⋆∙ Γ₁ (li2ri (p2li (pass∙ f))) (∷right eq') peq) g)
gen⊗r-p Γ₁ (f2p f) g eq peq = f2p (gen⊗r-f Γ₁ f g eq peq)

-- gen⊗r-f ax , Ir
gen⊗r-f {Γ₀ = Γ₀} {Γ₁'} Γ₁ ax g eq peq with []++ {xs = Γ₀} {Γ₁'} (isInter-end[] eq )
... | refl , refl with empty↭' peq
... | refl = ⊗r (li2ri (p2li (f2p ax))) g

gen⊗r-f {Γ₀ = Γ₀} {Γ₁'} Γ₁ Ir g eq peq with []++ {xs = Γ₀} {Γ₁'} (isInter-end[] eq )
... | refl , refl with empty↭' peq
... | refl = ⊗r (li2ri (p2li (f2p Ir))) g

-- gen⊗r-f ⊸l
gen⊗r-f  Γ₁ (⊸l {Γ} {Δ} f f') g eq peq with isInter++? Γ Δ refl eq
... | [] , Γ₀₁ , [] , Γ₁₁' , refl , refl , isInter[] , inTeq' = ⊸l f (gen⊗r-li Γ₁ f' g inTeq' peq)
gen⊗r-f  Γ₁ (⊸l {Γ} {Δ} f f') g eq peq | [] , Γ₀₁ , D ∷ Λ , Γ₁₁' , refl , refl , []left , inTeq' with tag-lem' inTeq'
... | .(tag-isInter inTeq') , eq₀ , refl with tag-lem eq
... | Γ' , eq₁ , eq₂ = ⊗r (⊸r⋆∙ Γ₁ (li2ri (p2li (f2p (⊸l∙ {Γ = []} {black Λ} {tag-isInter inTeq'} f f')))) (isInter++ []left  eq₀) peq) g
gen⊗r-f  Γ₁ (⊸l {Γ} {Δ} f f') g eq peq | .(_ ∷ _) , Γ₀₁ , [] , Γ₁₁' , refl , refl , []right , inTeq' = ⊸l f (gen⊗r-li Γ₁ f' g inTeq' peq)
gen⊗r-f  Γ₁ (⊸l {Γ} {Δ} f f') g eq peq | A ∷ Γ₀₀ , Γ₀₁ , D ∷ Λ , Γ₁₁' , refl , refl , ∷left inTeq , inTeq' with tag-lem' inTeq'
... | .(tag-isInter inTeq') , eq₀ , refl with tag-lem' inTeq
... | .(tag-isInter inTeq) , eq₁ , refl with isInter-split {ys₀ = []} {Λ} refl inTeq
... | xs₀ , xs₁ , zs₀ , zs₁ , refl , refl , inTeq₀ , inTeq₁ with isInter-left[] inTeq₀
... | refl with tag-lem' inTeq₁
... | .(tag-isInter inTeq₁) , eq₂ , refl with tag-lem-left[] inTeq₀
... | .(tagL xs₀) , eq₃ , refl = ⊗r (⊸r⋆∙ {Γ = (∘ , A) ∷ tagL zs₀ ++ (∙ , D) ∷ tag-isInter inTeq₁ ++ tag-isInter inTeq'} {tagL (A ∷ Γ₀₀ ++ Γ₀₁)} Γ₁ (li2ri (p2li (f2p (⊸l∙ {Γ = (∘ , A) ∷ tagL xs₀} {tag-isInter inTeq₁}
 {tag-isInter inTeq'} {D = D} f f')))) (∷left (isInter++ eq₃ (∷right' {x = (∙ , D)} (tagL (xs₁ ++ Γ₀₁)) (isInter++ eq₂ eq₀)))) peq) g
gen⊗r-f  Γ₁ (⊸l {Γ} {Δ} f f') g eq peq | A ∷ Γ₀₀ , Γ₀₁ , D ∷ Λ , Γ₁₁' , refl , refl , ∷right inTeq , inTeq' with tag-lem' inTeq'
... | .(tag-isInter inTeq') , eq₀ , refl with tag-lem' inTeq
... | .(tag-isInter inTeq) , eq₁ , refl with isInter-split-left {xs₀ = []} {Γ₀₀} refl inTeq
... | ys₀ , ys₁ , zs₀ , zs₁ , refl , refl , inTeq₀ , inTeq₁ with isInter-right[] inTeq₀
... | refl with tag-lem' inTeq₁
... | .(tag-isInter inTeq₁) , eq₂ , refl with tag-lem-right[] inTeq₀
... | .(black ys₀) , eq₃ , refl = ⊗r (⊸r⋆∙ {Γ = (∙ , D) ∷ black ys₀ ++ (∘ , A) ∷ tag-isInter inTeq₁ ++ tag-isInter inTeq'} {tagL (A ∷ Γ₀₀ ++ Γ₀₁)} Γ₁ (li2ri (p2li (f2p (⊸l∙ {Γ = []} {black ys₀ ++ (∘ , A) ∷ tag-isInter inTeq₁}
 {tag-isInter inTeq'} {D = D} f f')))) (∷right {y = (∙ , D)} (isInter++ eq₃ (∷left' {x = (∘ , A)} (black ys₁ ++ black Γ₁₁') (isInter++ eq₂ eq₀)))) peq) g

-- gen⊗r-f ⊗r
gen⊗r-f Γ₁ (⊗r {S = S} {Γ} {Δ} f f') g eq peq with isInter++? Γ Δ refl eq
... | [] , Γ₀₁ , [] , Γ₁₁' , refl , refl , isInter[] , inTeq' with tag-lem' inTeq'
... | .(tag-isInter inTeq') , eq₀ , refl = ⊗r (⊸r⋆∙ {Γ = tag-isInter inTeq'} {Γ₀ = tagL Γ₀₁} Γ₁ (li2ri (p2li {S = S} (f2p (⊗r {Γ = []} {tag-isInter inTeq'} f f')))) eq₀ peq) g
gen⊗r-f Γ₁ (⊗r {S = S} {Γ} {Δ} f f') g eq peq | [] , Γ₀₁ , D ∷ Λ , Γ₁₁' , refl , refl , []left , inTeq' with tag-lem' inTeq'
... | .(tag-isInter inTeq') , eq₀ , refl with tag-lem' ([]left {x = D} {Λ})
... | .((∙ , D) ∷ black Λ) , eq₁ , refl  = ⊗r (⊸r⋆∙ {Γ = (∙ , D) ∷ black Λ ++ tag-isInter inTeq'} {Γ₀ = tagL Γ₀₁} Γ₁ (li2ri (p2li {S = S} (f2p (⊗r {Γ = (∙ , D) ∷ black Λ} {tag-isInter inTeq'} f f')))) (isInter++ eq₁ eq₀) peq) g
gen⊗r-f Γ₁ (⊗r {S = S} {Γ} {Δ} f f') g eq peq | A ∷ Γ₀₀ , Γ₀₁ , [] , Γ₁₁' , refl , refl , []right , inTeq' with tag-lem' inTeq'
... | .(tag-isInter inTeq') , eq₀ , refl = ⊗r (⊸r⋆∙ {Γ = (∘ , A) ∷ tagL Γ₀₀ ++ tag-isInter inTeq'} {Γ₀ = (∘ , A) ∷ tagL Γ₀₀ ++ tagL Γ₀₁} Γ₁ (li2ri (p2li {S = S} (f2p (⊗r {Γ = (∘ , A) ∷ tagL Γ₀₀} {tag-isInter inTeq'} f f')))) (isInter++ ([]right {x = (∘ , A)} {tagL Γ₀₀})  eq₀) peq) g
gen⊗r-f Γ₁ (⊗r {S = S} {Γ} {Δ} f f') g eq peq | A ∷ Γ₀₀ , Γ₀₁ , D ∷ Λ , Γ₁₁' , refl , refl , ∷left inTeq , inTeq' with tag-lem' inTeq'
... | .(tag-isInter inTeq') , eq₀ , refl with tag-lem' inTeq
... | .(tag-isInter inTeq) , eq₁ , refl with isInter-split {ys₀ = []} {Λ} refl inTeq
... | xs₀ , xs₁ , zs₀ , zs₁ , refl , refl , inTeq₀ , inTeq₁ with isInter-left[] inTeq₀
... | refl with tag-lem' inTeq₁
... | .(tag-isInter inTeq₁) , eq₂ , refl with tag-lem-left[] inTeq₀
... | .(tagL xs₀) , eq₃ , refl rewrite tagL++₁ xs₀ (D ∷ zs₁) = ⊗r (⊸r⋆∙ {Γ = (∘ , A) ∷ tagL zs₀ ++ (∙ , D) ∷ tag-isInter inTeq₁ ++ tag-isInter inTeq'} {tagL (A ∷ Γ₀₀ ++ Γ₀₁)} Γ₁ (li2ri (p2li {S = S} (f2p (⊗r {Γ = (∘ , A) ∷ tagL xs₀ ++ (∙ , D) ∷ tag-isInter inTeq₁} {tag-isInter inTeq'} f f')))) (∷left (isInter++ eq₃ (∷right' {x = (∙ , D)} (tagL (xs₁ ++ Γ₀₁)) (isInter++ eq₂ eq₀)))) peq) g
gen⊗r-f Γ₁ (⊗r {S = S} {Γ} {Δ} f f') g eq peq | A ∷ Γ₀₀ , Γ₀₁ , D ∷ Λ , Γ₁₁' , refl , refl , ∷right inTeq , inTeq' with tag-lem' inTeq'
... | .(tag-isInter inTeq') , eq₀ , refl with tag-lem' inTeq
... | .(tag-isInter inTeq) , eq₁ , refl with isInter-split-left {xs₀ = []} {Γ₀₀} refl inTeq
... | ys₀ , ys₁ , zs₀ , zs₁ , refl , refl , inTeq₀ , inTeq₁ with isInter-right[] inTeq₀
... | refl with tag-lem' inTeq₁
... | .(tag-isInter inTeq₁) , eq₂ , refl with tag-lem-right[] inTeq₀
... | .(black ys₀) , eq₃ , refl rewrite tagL++₁ ys₀ (A ∷ zs₁) = ⊗r (⊸r⋆∙ {Γ = (∙ , D) ∷ black ys₀ ++ (∘ , A) ∷ tag-isInter inTeq₁ ++ tag-isInter inTeq'} {tagL (A ∷ Γ₀₀ ++ Γ₀₁)} Γ₁ (li2ri (p2li {S = S} (f2p (⊗r {Γ = (∙ , D) ∷ black ys₀ ++ (∘ , A) ∷ tag-isInter inTeq₁} {tag-isInter inTeq'} f f')))) ((∷right {y = (∙ , D)} (isInter++ eq₃ (∷left' {x = (∘ , A)} (black ys₁ ++ black Γ₁₁') (isInter++ eq₂ eq₀))))) peq) g
-- tag-isInter inTeq₁ =  tagged zs₁ tag-isInter inTeq' = tagged Δ
{-
Notes on how to prove case ⊸l and ⊗r:
We use isInter++? in the beginning to analyze the structure of Γ ++ Δ, then
do case analysis on inTeq : isInter Γ₀₀ Γ₁₀' Γ to have a fine-grained structure of Γ, 
and use tag-lem' to construct the tagged Δ (tag-isInter inTeq')
Then depending on the structure of inTeq, either there is a black formula or white formula
as the head of Γ.
For the case which the head of Γ is black, we use tag-lem' to construct tagged version of tail Γ,
then we use isInter-split-left to obtain the finer structure of Γ.
isInter-right[] inTeq₀ tag-lem-right[] inTeq₀ are used to rewrite isInter xs₀ [] zs₀.
Finnaly, we have enough ingredients to construct the desiring sequent.
-}


-- ⊗r in phase c
⊗r-c : {S : Stp} {Ω Γ Δ : Cxt} {A B : Fma} → 
          (f : S ∣ Ω ؛ [] ⊢c A) (g : - ∣ Γ ؛ Δ ⊢c B) → 
          ----------------------------------------------
             S ∣ Ω ++ Γ ؛ Δ ⊢c A ⊗ B
⊗r-c f (ex {Δ = Δ} {Λ} g refl refl) = ex {Δ = Δ} {Λ} (⊗r-c f g) refl refl
⊗r-c f (ri2c g) = ⊗r-c-ri f g

-- ⊗r in phase li
⊗r-li : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
        (f : S ∣ Γ  ⊢ri A) (g : - ∣ Δ ⊢ri B) →
      -----------------------------------------
               S ∣ Γ ++ Δ ⊢li (A ⊗ B , _)
⊗r-li {Γ = Γ} {Δ} f g = gen⊗r-ri {Γ = Γ} {Γ} [] {Δ} f g ([]right' Γ) (empty refl)

-- ax in phase c
ax-c : {A : Fma} → ∘ ∣ just A ∣ [] ؛ [] ⊢c A
ax-c {` x} = ri2c (li2ri (p2li (f2p ax)))
ax-c {I} = ri2c (li2ri (Il (p2li (f2p Ir))))
ax-c {A ⊗ B} = ⊗l-c (⊗r-c ax-c (pass-c ax-c))
ax-c {A ⊸ B} = ⊸r-c (⊸l-c (pass-c ax-c) ax-c)

-- Ir in phase c

Ir-c : - ∣ [] ؛ [] ⊢c I
Ir-c = ri2c (li2ri (p2li (f2p Ir)))

-- ====================
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
emb-f∙ (⊸l∙ f g) = ⊸l (emb-ri f) (emb-li g)

-- ̄≗ equivalent derivations are equal in focused calculus

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
eqfocus ⊸rpass = {!   !}
eqfocus ⊸rIl = {!   !}
eqfocus ⊸r⊸l = {!   !}
eqfocus ⊗rpass = {!   !}
eqfocus ⊗rIl = {!   !}
eqfocus ⊗r⊗l = {!   !}
eqfocus (ex p) = {!   !}
eqfocus exex = {!   !}
eqfocus expass = {!   !}
eqfocus exIl = {!   !}
eqfocus ex⊸r = {!   !}
eqfocus ex⊸l₁ = {!   !}
eqfocus ex⊸l₂ = {!   !}
eqfocus ex⊗l = {!   !}
eqfocus ex⊗r₁ = {!   !}
eqfocus ex⊗r₂ = {!   !}
eqfocus ex-iso = {!   !}
eqfocus ex-braid = {!   !} 