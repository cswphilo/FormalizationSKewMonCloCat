{-# OPTIONS --rewriting #-}

module Focusing (At : Set) where

open import Data.Maybe
open import Data.List renaming (map to mapList; fromMaybe to backlist)
open import Data.List.Relation.Unary.Any
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.List.Relation.Binary.Permutation.Propositional renaming (trans to transiff)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties 
open ≡-Reasoning
open import Data.Bool renaming (Bool to Tag; true to ∙; false to ∘)

open import Formulae At
open import SeqCalc At
open import Utilities hiding (++?)

open PermutationReasoning
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
whiteF (x , y) = (∘ , y)

whiteL : TCxt → TCxt
whiteL x = mapList whiteF x


-- Tag adding function for Fma and Cxt
tagF : Fma → TFma 
tagF x = (∘ , x)

tagL : Cxt → TCxt
tagL x = mapList tagF x

-- tag erasing
ersF : TFma → Fma
ersF A = proj₂ A

ersL : TCxt → Cxt
ersL Γ = mapList ersF Γ

ersL? : (x : Tag) → TCxt? x → Cxt
ersL? ∘ Γ = Γ
ersL? ∙ Γ = ersL Γ

whiteL? : (x : Tag) → TCxt? x → TCxt
whiteL? ∘ Γ = tagL Γ
whiteL? ∙ Γ = whiteL Γ

--

-- []? : (x : Tag) → TCxt? x
-- []? ∘ = []
-- []? ∙ = [] 

-- ++? : (x : Tag) → TCxt? x → TCxt? x → TCxt? x
-- ++? ∘ Γ Δ = Γ ++ Δ
-- ++? ∙ Γ Δ = Γ ++ Δ

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

-- infix 15 _∣_∣_⊢ri_ _∣_∣_؛_⊢c_ _∣_∣_⊢li_ 
-- -- We don't display the white phase
-- _∣_؛_⊢c_ : Stp → Cxt → Cxt → Fma → Set
-- S ∣ Γ ؛ Δ ⊢c C =  ∘ ∣ S ∣ tagL Γ ؛ tagL Δ ⊢c C

-- _∣_⊢ri_ : Stp → Cxt → Fma → Set
-- S ∣ Γ ⊢ri C =  ∘ ∣ S ∣ tagL Γ ⊢ri C

-- _∣_⊢li_ : Stp → Cxt → Pos → Set
-- S ∣ Γ ⊢li C =  ∘ ∣ S ∣ tagL Γ  ⊢li C

-- _∣_⊢p_ : Irr → Cxt → Pos → Set
-- S ∣ Γ ⊢p C =  ∘ ∣ S ∣ tagL Γ ⊢p C

-- _∣_⊢f_ : Irr → Cxt → Pos → Set
-- S ∣ Γ ⊢f C =  ∘ ∣ S ∣ tagL Γ ⊢f C

--=======================================================
-- ex-c' : {S : Stp} (Δ : TCxt) {Λ Ω Γ : TCxt} {A B C : Fma} → 
--         (f : ∘ ∣ S ∣ Λ ؛ Γ ⊢c C) → (eq : Λ ≡ Δ ++ (∘ , A) ∷ (∘ , B) ∷ Ω) → 
--         ----------------------------------------------------
--         ∘ ∣ S ∣ Δ ++ (∘ , B) ∷ (∘ , A) ∷ Ω ؛ Γ ⊢c C
-- ex-c' Δ (ex f eq₁) eq = {!   !}
-- ex-c' Δ (ri2c f) eq = {!   !}


-- exchange rule in phase c
ex-c' : ∀{S} Φ {Ψ Γ Λ A B C} → ∘ ∣ S ∣ Λ ؛ Γ ⊢c C → Λ ≡ Φ ++ A ∷ B ∷ Ψ
  → ∘ ∣ S ∣ Φ ++ B ∷ A ∷ Ψ ؛ Γ ⊢c C 
ex-c' Φ {Ψ} {A = A} {B} (ex {Γ = Φ'} {A = A'} f refl eq') eq with cases++ Φ' Φ [] (A ∷ B ∷ Ψ) (sym eq)
... | inj₁ (Ψ₀ , p , q) = ⊥-elim ([]disj∷ Ψ₀ q) -- ex-c' formula is in the right context of exchanged formula A', which is impossible
ex-c' Φ {.[]} {A = A} {B} (ex {Γ = .(Φ₁ ++ _ ∷ [])} {Γ} {Δ} {A = B} (ex {Γ = Φ₁} {Γ₁} {Δ₁} f refl refl) refl eq') eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ Φ q | cases++ Γ Γ₁ Δ Δ₁ eq' -- ex-c' formula is in the left context of exchanged formula A'
... | refl , refl | inj₁ (Γ₀ , refl , refl) = ex {Γ = Φ ++ B ∷ []} {Γ ++ Γ₀} (ex {Γ = Φ} {Γ} f refl refl) refl refl
... | refl , refl | inj₂ (Γ₀ , refl , refl) = ex {Γ = Φ ++ B ∷ []} {Γ₁} (ex {Γ = Φ}{Γ₁ ++ A ∷ Γ₀} f refl refl) refl refl
ex-c' Φ {.[]} {A = A} {B} (ex {Γ = .[]} {A = .B} (ri2c f) refl eq') eq | inj₂ (A ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
ex-c' Φ {A = A} {B} (ex {Γ = .(Φ ++ A ∷ B ∷ Ψ₀)} {Γ} {A = A'} f refl refl) eq | inj₂ (A ∷ B ∷ Ψ₀ , refl , refl) = ex {Γ = Φ ++ _ ∷ _ ∷ Ψ₀} {Γ} (ex-c' _ f refl) refl refl
ex-c' Φ (ri2c f) eq = ⊥-elim ([]disj∷ Φ eq)

ex-c : ∀{S} Φ {Ψ Γ A B C} → ∘ ∣ S ∣ Φ ++ A ∷ B ∷ Ψ ؛ Γ ⊢c C
  → ∘ ∣ S ∣ Φ ++ B ∷ A ∷ Ψ ؛ Γ ⊢c C 
ex-c Φ f = ex-c' Φ f refl


-- ⊸r rule in phase c
⊸r-c' : {S : Stp} {Γ Λ Δ₀ Δ₁ : Cxt} {A : Fma} {B : Fma} → 
       (f : ∘ ∣ S ∣ Γ ؛ Λ ⊢c B) (eq : Λ ≡ Δ₀ ++ A ∷ Δ₁) → 
       -----------------------------------
       ∘ ∣ S ∣ Γ ؛ Δ₀ ++ Δ₁ ⊢c A ⊸ B
⊸r-c' {Δ₀ = Δ₀} {Δ₁ = Δ₁} (ex {Δ = Δ} {Λ = Λ} f refl eq1) eq with cases++ Δ₀ Δ Δ₁ Λ eq
⊸r-c' {Δ₀ = Δ₁} {_} (ex {Δ = _} {Λ = Λ} f refl refl) refl | inj₁ (Δ₀ , refl , refl) = ex {Δ = (Δ₁ ++ Δ₀)} (⊸r-c' f refl) refl refl
--                                                                               exchaged formula is in the right context of ⊸r-c' formula
⊸r-c' {Δ₀ = _} {_} (ex {Δ = Δ} {_} f refl refl) refl | inj₂ (Δ₀ , refl , refl) = ex (⊸r-c' {Δ₀ = (Δ ++ _ ∷ Δ₀)} f refl) refl refl
--                                                                               exchaged formula is in the left context of ⊸r-c' formula
⊸r-c' (ri2c f) eq = ri2c (⊸r (ex (ri2c f) refl eq))

⊸r-c : {S : Stp} {Γ : Cxt} (Δ : Cxt) {A B : Fma} → 
       (f : ∘ ∣ S ∣ Γ ؛ Δ ++ A ∷ [] ⊢c B) →
       -----------------------------------------
       ∘ ∣ S ∣ Γ ؛ Δ ⊢c A ⊸ B
⊸r-c Δ f = ⊸r-c' {Δ₀ = Δ} f refl

⊸r-ex-c : {S : Stp} {Γ₀ Γ₁ : Cxt} {A : Fma} {B : Fma} → 
          (f : ∘ ∣ S ∣ [] ؛ Γ₀ ++ A ∷ Γ₁ ⊢c B) →
          ------------------------------------
          ∘ ∣ S ∣ Γ₀ ++ Γ₁ ⊢ri A ⊸ B
⊸r-ex-c f = ⊸r (ex f refl refl)


-- ers and ⊸⋆
-- ersappend : (Γ : TCxt) (Δ : TCxt) → ersL (Γ ++ Δ) ≡ ersL Γ ++ (ersL Δ)
-- ersappend [] Δ = refl
-- ersappend (x ∷ Γ) Δ = cong₂ _∷_ refl (ersappend Γ Δ) 


-- iterated ⊸r-c rule
-- ⊸r-c⋆ : {S : Stp} {Δ Γ₁ Γ₂ Γ : TCxt} {B : Fma} →
--         (f : ∘ ∣ S ∣ Δ ؛ Γ ⊢c B) (eq : Γ ≡ Γ₁ ++ Γ₂) → 
--         ---------------------------
--         ∘ ∣ S ∣ Δ ؛ Γ₁ ⊢c ersL Γ₂ ⊸⋆ B
-- ⊸r-ri⋆ : {S : Stp} {Γ₁ Γ : TCxt} {B : Fma} →
--           (Γ₂ : TCxt) (f : ∘ ∣ S ∣ Γ ⊢ri B) (eq : Γ ≡ Γ₁ ++ Γ₂) →
--          -----------------------------
--           ∘ ∣ S ∣ Γ₁ ⊢ri ersL Γ₂ ⊸⋆ B
-- ⊸ex : {S : Stp} {Γ : TCxt} {A B : Fma} {C : Fma} → 
--      (f : ∘ ∣ S ∣ Γ ⊢ri A ⊸ (B ⊸ C))  → 
--      ----------------------------------------------
--      ∘ ∣ S ∣ Γ ⊢ri B ⊸ (A ⊸ C)
-- ⊸ex (⊸r (ex {Γ = []} (ex f eq' refl) refl eq)) = ⊥-elim ([]disj∷ _ eq')
-- ⊸ex (⊸r (ex {Γ = []} {Δ₁} {Λ₁} (ri2c (⊸r (ex {Γ = []} {Δ} {Λ} f refl refl))) refl eq)) with cases++ Δ₁ Δ Λ₁ Λ eq
-- ... | inj₁ (Δ₀ , refl , refl) = ⊸r (ex {Δ = Δ₁ ++ Δ₀} {Λ = Λ} (ri2c (⊸r (ex {Δ = Δ₁} {Λ = Δ₀ ++ _ ∷ Λ} f refl refl))) refl refl)
-- ... | inj₂ (Δ₀ , refl , refl) = ⊸r (ex {Δ = Δ} {Λ = Δ₀ ++ Λ₁} (ri2c (⊸r (ex {Δ = Δ ++ _ ∷ Δ₀} {Λ = Λ₁} f refl refl))) refl refl)
-- ⊸ex (⊸r (ex {Γ = []} (ri2c (⊸r (ex {Γ = x ∷ Γ} f eq₂ eq₁))) eq eq')) = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq₂ )))
-- ⊸ex (⊸r (ex {Γ = x ∷ Γ} f eq' eq)) = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq' )))
--

-- unlist : {X : Set} → (xs : List (List X)) → List X
-- unlist [] = []
-- unlist (xs ∷ xs₁) = xs ++ (unlist xs₁)
-- ∷++ : {X : Set} → {Γ Δ Λ : List X} {A : X} → (eq : A ∷ Γ ≡ Δ ++ Λ) → Γ ≡ unlist (backlist (tail (Δ ++ Λ)))
-- ∷++ {Δ = []} {x ∷ Λ} eq = proj₂ (inj∷ eq)
-- ∷++ {Δ = x ∷ Δ} {Λ} eq = proj₂ (inj∷ eq)


-- ⊗l rule in phase c
⊗l-ri : {Γ Δ Ω : Cxt} {A B C : Fma} → 
          (f : ∘ ∣ just A ∣ Ω ⊢ri C) (eq : Ω ≡ Δ ++ B ∷ Γ) → 
           ∘ ∣ just (A ⊗ B) ∣ Δ ++ Γ ⊢ri C
⊗l-ri (⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq₀ eq)) p = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq₀)))
⊗l-ri {Γ} {Δ₁} (⊸r (ex {Δ = Δ} {Λ} (ri2c f) refl refl)) p with cases++ Δ₁ Δ Γ Λ p
... | inj₁ (Δ₀ , refl , refl) = ⊸r (ex {Δ = Δ₁ ++ Δ₀} (ri2c (⊗l-ri f refl)) refl refl) 
... | inj₂ (Δ₀ , refl , refl) = ⊸r (ex {Δ = Δ} (ri2c (⊗l-ri {Δ = Δ ++ _ ∷ Δ₀} f refl)) refl refl)
⊗l-ri (li2ri {C = C} f) refl = li2ri {C = C} (⊗l (ex (ri2c (li2ri f)) refl refl))

⊗l-c' : ∀ {Γ Γ' Δ A B C} (f : ∘ ∣ just A ∣ Γ' ؛ Δ ⊢c C) (p : Γ' ≡ B ∷ Γ) → 
                             ∘ ∣ just (A ⊗ B) ∣ Γ ؛ Δ ⊢c C
⊗l-c' (ex {Γ = []} (ex {Γ = Γ} f eq'' eq₂) eq' eq) eq₁ = ⊥-elim ([]disj∷ Γ eq'')
⊗l-c' (ex {Γ = []} (ri2c f) refl refl) refl = ri2c (⊗l-ri f refl)
⊗l-c' (ex {Γ = A' ∷ Φ} f refl refl) refl = ex (⊗l-c' f refl) refl refl



⊗l-c : ∀ {Γ Δ A B C} → ∘ ∣ just A ∣ B ∷ Γ ؛ Δ ⊢c C → ∘ ∣ just (A ⊗ B) ∣ Γ ؛ Δ ⊢c C
⊗l-c f = ⊗l-c' f refl

-- -- Il rule in phase c
Il-c : {Γ Δ : Cxt} {C : Fma} →
         (f : ∘ ∣ - ∣ Γ ؛ Δ ⊢c C) → 
         -------------------------
         ∘ ∣ just I ∣ Γ ؛ Δ ⊢c C
Il-ri : {Γ : Cxt} {C : Fma} → 
        (f : ∘ ∣ - ∣ Γ ⊢ri C) →
        --------------------
        ∘ ∣ just I ∣ Γ ⊢ri C

Il-c (ex f refl eq) = ex (Il-c f) refl eq
Il-c (ri2c f) = ri2c (Il-ri f)
Il-ri (⊸r f) = ⊸r (Il-c f)
Il-ri (li2ri f) = li2ri (Il f)

-- pass rule in phase c
-- white-subs-c : {S : Stp} {Γ₀ Γ₁ : TCxt} (Γ : TCxt) {C : Fma} (f : ∘ ∣ S ∣ Γ₀ ++ whiteL Γ ++ Γ₁ ⊢ri C) → 
--              -----------------------------
--              ∘ ∣ S ∣ Γ₀ ++ Γ ++ Γ₁ ⊢ri C
-- white-subs-ri : {S : Stp} {Γ₀ Γ₁ : TCxt} (Γ : TCxt) {C : Fma} → 
--                 (f : ∘ ∣ S ∣ Γ₀ ++ Γ ++ Γ₁ ⊢ri C) → 
--                 -----------------------------
--                 ∘ ∣ S ∣ Γ₀ ++ whiteL Γ ++ Γ₁ ⊢ri C
-- white-subs-ri [] f = f
-- white-subs-ri {Γ₀ = Γ₀} {Γ₁ = Γ₁} (x ∷ Γ) f = white-subs-ri {Γ₀ = Γ₀} {Γ₁ = (whiteL Γ) ++ Γ₁} (x ∷ []) (white-subs-ri {Γ₀ = Γ₀ ++ x ∷ []} {Γ₁ = Γ₁} Γ f)

-- postulate
--   permute-eq-ri : ∀ (x : Tag) (S : Stp) (Γ Γ' : TCxt) (C : Fma) (eq : Γ ↭ Γ') → x ∣ S ∣ Γ ⊢ri C ≡ x ∣ S ∣ Γ' ⊢ri C
--   permute-eq-p : ∀ (x : Tag) (S : Irr) (Γ Γ' : TCxt) (C : Pos) (eq : Γ ↭ Γ') → x ∣ S ∣ Γ ⊢p C ≡ x ∣ S ∣ Γ' ⊢p C
--   whiteCxt-eq-ri : ∀ (S : Stp) (Γ : TCxt) (C : Fma) → ∘ ∣ S ∣ Γ ⊢ri C ≡ ∘ ∣ S ∣ whiteL Γ ⊢ri C
--   whiteCxt-eq-li : ∀ (S : Stp) (Γ : TCxt) (C : Pos) → ∘ ∣ S ∣ Γ ⊢li C ≡ ∘ ∣ S ∣ whiteL Γ ⊢li C
--   whiteCxt-eq-p : ∀ (S : Irr) (Γ : TCxt) (C : Pos) → ∘ ∣ S ∣ Γ ⊢p C ≡ ∘ ∣ S ∣ whiteL Γ ⊢p C
--   context-perm : {A : Set} {x : A} (xs ys zs : List A) (eq : x ∷ xs ↭ ys ++ zs) → Σ (List A) (λ ys' → Σ (List A) (λ zs' → xs ↭ ys' ++ zs' × ((x ∷ ys' ↭ ys × zs' ↭ zs) ⊎ (ys' ↭ ys × x ∷ zs' ↭ zs))))

pass-c : {Γ Δ Γ' : Cxt} {A C : Fma} → 
          (f : ∘ ∣ just A ∣ Γ ؛ Δ ⊢c C) (eq : Γ' ≡ A ∷ Γ) → 
          ------------------------------
          ∘ ∣ - ∣ Γ' ؛ Δ ⊢c C
pass-ri : {Γ : Cxt} {A C : Fma} → 
          (f : ∘ ∣ just A ∣ Γ ⊢ri C) → 
          ------------------------------
          ∘ ∣ - ∣ A ∷ Γ ⊢ri C
pass-c {A = A'} (ex {Γ = Γ} {Δ} {Λ} {A = A} f refl refl) eq = ex {Γ = A' ∷ Γ} {Δ} {Λ} {A = A} (pass-c f refl) eq refl
pass-c {Δ = Δ} {A = A} (ri2c (⊸r f)) refl = ex {Γ = []} {Δ = []} (ri2c (pass-ri (⊸r f))) refl refl
pass-c {Δ = Δ} {A = A} (ri2c (li2ri f)) refl = ex {Γ = []} {Δ = []} (ri2c (li2ri (p2li (pass f)))) refl refl
pass-ri {Γ = .(_)} {A = A'} (⊸r {A = A} (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq)) = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
pass-ri {Γ = .(_)} {A = A'} (⊸r {A = A} (ex {Δ = Δ} {Λ = Λ} (ri2c f) refl refl)) = ⊸r (ex {Γ = []} {Δ = A' ∷ Δ} {Λ = Λ} (ri2c (pass-ri f)) refl refl)  -- ⊸r (act [] (ex-c [] (pass-c f refl)) refl refl)
pass-ri (li2ri f) = li2ri (p2li (pass f))

-- ⊸l in phase c

⊸l-c : {Γ Δ Ω : Cxt} {A B C : Fma} →
       (f : ∘ ∣ - ∣ [] ؛ Γ ⊢c A) (g : ∘ ∣ just B ∣ Ω ؛ Δ ⊢c C) → 
       -----------------------------------------------
       ∘ ∣ just (A ⊸ B) ∣ Ω ؛ Γ ++ Δ ⊢c C
⊸l-ri : {Γ Δ : Cxt} {A B C : Fma} →
        (f : ∘ ∣ - ∣ Γ ⊢ri A) (g : ∘ ∣ just B ∣ Δ ⊢ri C) →
        ------------------------------------------------
        ∘ ∣ just (A ⊸ B) ∣ Γ ++ Δ ⊢ri C
⊸l-c {Γ} f (ex {Δ = Δ} {Λ = Λ} g refl refl) = ex {Δ = Γ ++ Δ} {Λ = Λ} (⊸l-c {Γ} {Δ = Δ ++ _ ∷ Λ} f g) refl refl
⊸l-c (ex {Γ = Γ} f eq' eq) (ri2c g) = ⊥-elim ([]disj∷ Γ eq')
⊸l-c (ri2c f) (ri2c g) = ri2c (⊸l-ri f g) 
⊸l-ri {Γ} f (⊸r {A = A} (ex (ex {Γ = x ∷ Γ₁} g refl refl) eq' eq)) = ⊥-elim ([]disj∷ Γ₁ (proj₂ (inj∷ eq')))
⊸l-ri {Γ} f (⊸r {A = A} (ex {Δ = Δ} {Λ = Λ} (ri2c g) refl refl)) = ⊸r (ex {Γ = []} {Δ = Γ ++ Δ} {Λ = Λ} (ri2c (⊸l-ri {Γ = Γ} {Δ = Δ ++ _ ∷ Λ} f g)) refl refl) 
⊸l-ri {Γ} {Δ} f (li2ri {C = C} g) = li2ri {C = C} (p2li (f2p (⊸l {Γ = Γ} {Δ = Δ} f g)))


-- ⊗r rule in phase c

--
whiteL₂ : Cxt → TCxt
whiteL₂ [] = []
whiteL₂ (x ∷ Γ) = (∘ , x) ∷ (whiteL₂ Γ)

whiteL₂append : (Γ Δ : Cxt) → whiteL₂ Γ ++ whiteL₂ Δ ≡ whiteL₂ (Γ ++ Δ)
whiteL₂append [] Δ = refl
whiteL₂append (A ∷ Γ) Δ = cong (_∷_ ((∘ , A))) (whiteL₂append Γ Δ)

whiteLappend : (Γ Δ : TCxt) → whiteL Γ ++ whiteL Δ ≡ whiteL (Γ ++ Δ)
whiteLappend [] Δ = refl
whiteLappend (x ∷ Γ) Δ = cong ((whiteF x) ∷_) (whiteLappend Γ Δ)


black : Cxt → TCxt
black [] = []
black (x ∷ Γ) = (∙ , x) ∷ (black Γ)


-- ≡-ri : {x : Tag} {S : Stp} {Γ Γ' : TCxt} {C : Fma} (f : x ∣ S ∣ Γ ⊢ri C) → 
--         (eq : Γ ≡ Γ') → (x ∣ S ∣ Γ' ⊢ri C)
-- ≡-ri f refl = f


-- ↭-ri : {x : Tag} {S : Stp} {Γ Γ' : TCxt} {C : Fma} → 
--        (f : x ∣ S ∣ Γ ⊢ri C) → (eq : Γ ↭ Γ') → x ∣ S ∣ Γ' ⊢ri C
-- ↭-ri {x} {S} {Γ} {Γ'} {C} f eq rewrite permute-eq-ri x S Γ Γ' C eq = f

-- ↭-p : {x : Tag} {S : Irr} {Γ Γ' : TCxt} {C : Pos} → 
--        (f : x ∣ S ∣ Γ ⊢p C) → (eq : Γ ↭ Γ') → x ∣ S ∣ Γ' ⊢p C
-- ↭-p {x} {S} {Γ} {Γ'} {C} f eq rewrite permute-eq-p x S Γ Γ' C eq = f


-- whiteCxt-sub-ri : {S : Stp} (Γ : TCxt) {C : Fma} → (f : ∘ ∣ S ∣ Γ ⊢ri C) → ∘ ∣ S ∣ whiteL Γ ⊢ri C
-- whiteCxt-sub-ri [] f = f
-- whiteCxt-sub-ri {S} (x ∷ Γ) {C} f rewrite whiteCxt-eq-ri S (x ∷ Γ) C = f

-- whiteCxt-sub-li : {S : Stp} (Γ : TCxt) {C : Pos} → (f : ∘ ∣ S ∣ Γ ⊢li C) → ∘ ∣ S ∣ whiteL Γ ⊢li C
-- whiteCxt-sub-li [] f = f
-- whiteCxt-sub-li {S} (A ∷ Γ) {C} f rewrite whiteCxt-eq-li S (A ∷ Γ) C = f

-- whiteCxt-sub-p : {S : Irr} (Γ : TCxt) {C : Pos} → (f : ∘ ∣ S ∣ Γ ⊢p C) → ∘ ∣ S ∣ whiteL Γ ⊢p C
-- whiteCxt-sub-p [] f = f
-- whiteCxt-sub-p {S} (A ∷ Γ) {C} f rewrite whiteCxt-eq-p S (A ∷ Γ) C = f

-- whiteCxt-sub-c : {S : Stp} {Γ Δ : TCxt} {C : Fma} → (f : ∘ ∣ S ∣ Γ ؛ Δ ⊢c C) → ∘ ∣ S ∣ whiteL Γ ؛ whiteL Δ ⊢c C 
-- whiteCxt-sub-ri : {S : Stp} {Γ : TCxt} {C : Fma} → (f : ∘ ∣ S ∣ Γ ⊢ri C) → ∘ ∣ S ∣ whiteL Γ ⊢ri C
-- whiteCxt-sub-li : {S : Stp} {Γ : TCxt} {C : Pos} → (f : ∘ ∣ S ∣ Γ ⊢li C) → ∘ ∣ S ∣ whiteL Γ ⊢li C
-- whiteCxt-sub-p : {S : Irr} {Γ : TCxt} {C : Pos} → (f : ∘ ∣ S ∣ Γ ⊢p C) → ∘ ∣ S ∣ whiteL Γ ⊢p C
-- whiteCxt-sub-f : {S : Irr} {Γ : TCxt} {C : Pos} → (f : ∘ ∣ S ∣ Γ ⊢f C) → ∘ ∣ S ∣ whiteL Γ ⊢f C

-- whiteCxt-sub-c (ex {Γ = Γ} {A = A} f eq' eq) = ex (whiteCxt-sub-c f) (trans (cong whiteL eq') (sym (whiteLappend Γ (A ∷ [])))) {!   !}
-- whiteCxt-sub-c (ri2c f) = ri2c (whiteCxt-sub-ri f)


-- whiteCxt-sub-l Γ (Il f) = Il (whiteCxt-sub-li Γ f)
-- whiteCxt-sub-li Γ (⊗l f) = {!   !}
-- whiteCxt-sub-li Γ (p2li f) = {!   !}

-- data isInter {A : Set} : List A → List A → List A → Set where
--   []left : {xs : List A} → isInter [] xs xs
--   []right : {xs : List A} → isInter xs [] xs
--   ∷left : {x y : A} {xs ys zs : List A} → isInter xs (y ∷ ys) zs → isInter (x ∷ xs) (y ∷ ys) (x ∷ zs)
--   ∷right : {x y : A} {xs ys zs : List A} → isInter (x ∷ xs) ys zs → isInter (x ∷ xs) (y ∷ ys) (y ∷ zs)

data isInter {A : Set} : List A → List A → List A → Set where
  []left : {xs zs : List A} → (xs ↭ zs) → isInter [] xs zs
  []right : {xs : List A} → isInter xs [] xs
  ∷left : {x y : A} {xs ys zs : List A} → isInter xs (y ∷ ys) zs → isInter (x ∷ xs) (y ∷ ys) (x ∷ zs)
  ∷right : {x y : A} {xs ys ys' ys'' zs : List A} →  ys'' ≡ ys ++ y ∷ ys' → isInter (x ∷ xs) (ys ++ ys') zs → isInter (x ∷ xs) ys'' (y ∷ zs)

isInter∷right : {A : Set} (xs ys zs : List A) {x : A} → isInter xs (x ∷ ys) zs → Σ (List A) (λ xs₀ → Σ (List A) (λ xs₁ → Σ (List A) (λ zs' → xs ≡ xs₀ ++ xs₁ × zs ≡ xs₀ ++ x ∷ zs' × isInter xs₁ ys zs')))
isInter∷right .[] ys zs ([]left x) = {! ([] , [] , )  !}
isInter∷right .(_ ∷ _) ys .(_ ∷ _) (∷left eq) = {!   !}
isInter∷right .(_ ∷ _) ys .(_ ∷ _) (∷right x eq) = {!   !}
-- .[] ys ys' _ ([]left eq) = ? -- ([] , [] , ys , refl , refl , []left)
-- isInter∷right (x ∷ xs) ys ys' (x ∷ zs) (∷left eq) = {! isInter∷right  !}
-- isInter∷right .(_ ∷ _) ys ys' .(_ ∷ _) (∷right eq) = {!   !}

⊸r⋆∙ : {S : Stp} {Γ Γ₀ : TCxt} (Γ₁ : Cxt) {A : Fma} → 
       (f : ∙ ∣ S ∣ Γ ⊢ri A) (eq : isInter Γ₀ (tagL Γ₁) Γ) → 
       --------------------------------------------
       ∙ ∣ S ∣ Γ₀ ⊢ri Γ₁ ⊸⋆ A
⊸r⋆∙ [] f ([]left x) = {!   !}
⊸r⋆∙ [] f []right = {!   !}
⊸r⋆∙ [] f (∷right x eq) = {!   !}
⊸r⋆∙ (A' ∷ Γ₁) f eq with isInter∷right _ _ _ eq 
... | Γ₀' , Γ₀'' , Γ' , refl , refl , eq'' = ⊸r∙ (ex∙ {Γ = []} {Γ₀'} {Γ₀''} (ri2c (⊸r⋆∙ Γ₁ f {!   !})) refl refl)

⊸r⋆∙' : {S : Stp} {Γ Γ₀ : TCxt} (Γ₁ : Cxt) {A : Fma} → 
       (f : ∙ ∣ S ∣ Γ ⊢ri A) (eq : Γ ↭ Γ₀ ++ tagL Γ₁) → 
       --------------------------------------------
       ∙ ∣ S ∣ Γ₀ ⊢ri Γ₁ ⊸⋆ A
⊸r⋆∙' [] f eq = {!   !}
⊸r⋆∙' (x ∷ Γ₁) f eq = {!   !}
-- ⊸r⋆∙ {S} {Γ} {.Γ} [] {A} f []right = f 
-- ⊸r⋆∙ [] f ([]left eq') = ?
-- -- ↭-ri f eq
-- ⊸r⋆∙ {Γ₀ = Γ₀} (A' ∷ Γ₁) f eq with isInter∷right _ _ _ _ eq
-- ... | Γ₀' , Γ₀'' , Γ' , refl , eq₁ , eq'' = ? 
-- ⊸r∙ (ex∙ {Γ = []} {Γ₀'} {Γ₀''} (ri2c (⊸r⋆∙ {!   !} Γ₁ f {!   !} {!   !})) refl refl)
-- ⊸r∙ (ex∙ {Γ = []} {Δ = Γ₀} {[]} (ri2c (⊸r⋆∙ {Γ₀ = Γ₀ ++ (∙ , x) ∷ []} Γ₁ f eq)) refl refl)
{-
-- gen-pass : {x : Tag} {Γ Γ' : TCxt} {A : Fma} {C : Pos} → 
--            (f : ∘ ∣ just A ∣ Γ ⊢li C) (eq : (x , A) ∷ Γ ↭ Γ') → 
--            --------------------------------
--            x ∣ (- , _) ∣ Γ' ⊢p C
-- gen-pass (Il f) eq = {!   !}
-- gen-pass (⊗l f) eq = {!   !}
-- gen-pass (p2li f) eq = {!   !}
-- gen-pass {x} {Γ} f eq with x
-- ... | ∘ = ↭-p (pass f) eq
-- ... | ∙ = ↭-p (pass∙ (whiteCxt-sub-li f)) eq

-- inTCxt-structure : ∀ (A : TFma) (Γ : TCxt) → ⊥ ⊎ Σ (TCxt) (λ Γ₀ → (Σ (TCxt) (λ Γ₁ → (Σ (TFma) (λ B → (A ≡ B) × (Γ ≡ Γ₀ ++ A ∷ Γ₁))))))
-- inTCxt-structure A [] = inj₁ _
-- inTCxt-structure A (x ∷ Γ) with inTCxt A Γ
-- ... | ∘ = inj₁ _
-- ... | ∙ with TFmaEQ A x 
-- inTCxt-structure A (x ∷ Γ) | ∙ | ∘ = {!   !}
-- inTCxt-structure A (x ∷ Γ) | ∙ | ∙ = inj₂ ([] , (Γ , (A , (refl , {! re!}))))


-- ⊗r-c-ri : {S : Stp} {Ω Γ Δ : TCxt} {A B : Fma} → 
--        (f : ∘ ∣ S ∣ Ω ؛ Γ ⊢c A) (g : ∘ ∣ - ∣ Δ ⊢ri B)  → 
--        ------------------------------------------------
--        ∘ ∣ S ∣ Ω ؛ Γ ++ Δ ⊢c A ⊗ B 
-- gen⊗r-ri : {S : Stp} {Γ Γ₀ : TCxt} (Γ₁ : Cxt) (Γ₁' : Cxt) {Δ : TCxt} {A B : Fma} → 
--             (f : ∘ ∣ S ∣ Γ ⊢ri A) (g : ∘ ∣ - ∣ Δ ⊢ri B) (eq : isInter Γ₀ Γ₁ Γ) (eq' : Γ₁ ↭ Γ₁') →
--         -----------------------------------------------------------
--                     (∘ ∣ S ∣ Γ₀ ++ Δ ⊢li ((Γ₁' ⊸⋆ A) ⊗ B , _))
-- gen⊗r-li : {S : Stp} {Γ Γ₀ : TCxt} (Γ₁ Γ₁' : Cxt)  {Δ : TCxt} {A : Pos} {B : Fma} → 
--             (f : ∘ ∣ S ∣ Γ ⊢li A) (g : ∘ ∣ - ∣ Δ ⊢ri B) (eq : isInter Γ₀ Γ₁ Γ) (eq' : Γ₁ ↭ Γ₁') →
--         -----------------------------------------------------------
--                     (∘ ∣ S ∣ Γ₀ ++ Δ ⊢li ((Γ₁' ⊸⋆ (pos A)) ⊗ B , _))
-- gen⊗r-p : {S : Irr} {Γ Γ₀ : TCxt} (Γ₁ Γ₁' : Cxt) {Δ : TCxt} {A : Pos} {B : Fma} → 
--             (f : ∘ ∣ S ∣ Γ ⊢p A) (g : ∘ ∣ - ∣ Δ ⊢ri B) (eq : isInter Γ₀ Γ₁ Γ) (eq' : Γ₁ ↭ Γ₁') →
--         -----------------------------------------------------------
--                     (∘ ∣ S ∣ Γ₀ ++ Δ ⊢p ((Γ₁' ⊸⋆ (pos A)) ⊗ B , _))

-- ⊗r-c-ri (ex f refl refl) g = ex (⊗r-c-ri f g) refl refl
-- ⊗r-c-ri (ri2c f) g = ri2c (li2ri (gen⊗r-ri [] f g refl))

-- gen⊗r-ri Γ₁ (⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) g eq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
-- gen⊗r-ri {Γ₀ = Γ₀} Γ₁ (⊸r {A = A} (ex {Δ = Δ} {Λ = Λ} (ri2c f) refl refl)) g eq = gen⊗r-ri {Γ₀ = Γ₀} (Γ₁ ∷ʳ A) f g (transiff (++⁺ˡ Δ {(∘ , A) ∷ Λ} (++-comm ((∘ , A) ∷ []) Λ)) (transiff (++⁺ʳ {xs = Δ ++ Λ} ((∘ , A) ∷ []) eq) (↭-reflexive (cong (Γ₀ ++_) (whiteL₂append Γ₁ (A ∷ [])))))) -- gen⊗r-ri {! !} {!   !} {!   !} {!   !}
-- gen⊗r-ri Γ₁ (li2ri f) g eq = gen⊗r-li Γ₁ f g eq 

-- gen⊗r-li Γ₁ (Il f) g eq = Il (gen⊗r-li Γ₁ f g eq)
-- gen⊗r-li Γ₁ (⊗l (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) g eq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
-- gen⊗r-li {Γ₀ = Γ₀} Γ₁ {Δ = Δ'} (⊗l {B = B} (ex {Δ = Δ} {Λ} (ri2c (li2ri f)) refl refl)) g eq = ⊗l (ex {Γ = []} {Δ = []} {Λ = Γ₀ ++ Δ'} (ri2c (li2ri (gen⊗r-li Γ₁ f g (transiff (++⁺ʳ {xs = Δ ++ (∘ , B) ∷ []} Λ (++-comm Δ ((∘ , B) ∷ []))) (++⁺ˡ ((∘ , B) ∷ []) {ys = Δ ++ Λ} {zs = Γ₀ ++ whiteL₂ Γ₁} eq))))) refl refl)
-- gen⊗r-li Γ₁ (p2li f) g eq = p2li (gen⊗r-p Γ₁ f g eq)

-- gen⊗r-p {Γ₀ = Γ₀} Γ₁ {Δ = Δ} (pass {Γ = Γ} {A = A} f) g eq with context-perm Γ Γ₀ (whiteL₂ Γ₁) eq
-- ... | (ys' , zs' , eq' , inj₁ (eq₀ , eq₁)) = {!   !}
-- ... | (Γ₀' , Γ₁' , eq' , inj₂ (eq₀ , eq₁)) = f2p (⊗r {Γ = Γ₀} {Δ = Δ} (⊸r⋆∙ {Γ = (∙ , A) ∷ Γ} {whiteL Γ₀} Γ₁ (li2ri (p2li (pass∙ (whiteCxt-sub-li f)))) {!   !}) (whiteCxt-sub-ri g))
-- -- with inTCxt (∘ , A) Γ₀
-- -- gen⊗r-p {Γ₀ = Γ₀} Γ₁ {Δ = Δ} (pass {Γ = Γ} {A = A} f) g eq | ∘ = {!   !}
-- -- gen⊗r-p {Γ₀ = Γ₀} Γ₁ {Δ = Δ} (pass {Γ = Γ} {A = A} f) g eq | ∙ = {!   !}

-- gen⊗r-p Γ₁ (f2p f) g eq = {!   !}








-- ⊗r-c : {S : Stp} {Ω₁ Ω₂ Γ : TCxt} {A B : Fma} → 
--        (f : ∘ ∣ S ∣ Ω₁ ؛ [] ⊢c A) (g : ∘ ∣ - ∣ Ω₂ ؛ Γ ⊢c B) → 
--        ------------------------------------------------
--        ∘ ∣ S ∣ Ω₁ ++ Ω₂ ؛ Γ ⊢c A ⊗ B -- what is the intuition behind this rule?
-- ⊗r-c {Ω₁ = Ω₁} f (ex {Γ = Ω₂} g refl refl) = ex {Γ = Ω₁ ++ Ω₂} (⊗r-c f g) refl refl
-- ⊗r-c f (ri2c g) = ⊗r-c-ri f g   
     -}