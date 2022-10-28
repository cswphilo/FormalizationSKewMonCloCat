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
open import IsInter
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

tagL++ : (Γ Δ : Cxt) →  tagL (Γ ++ Δ) ≡ tagL Γ ++ tagL Δ
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
ersL ((x , A) ∷ Γ) = A ∷ ersL Γ

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

whiteErs : (Γ : TCxt) →  ersL (whiteL Γ) ≡ ersL Γ
whiteErs [] = refl
whiteErs ((x , y) ∷ Γ) = cong (y ∷_) (whiteErs Γ)
{-# REWRITE whiteErs #-}

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

  ⊸l∙ : {Γ Γ' Λ Δ : TCxt} {A B : Fma} {D : Fma} {C : Pos} →
       (f :  ∘ ∣ - ∣ ersL Γ' ⊢ri A) → (g :  ∘ ∣ just B ∣ ersL Δ ⊢li C) → (eq : Γ' ≡ Γ ++ ((∙ , D) ∷ Λ)) → 
       -----------------------------------------------------------
        ∙ ∣ (just (A ⊸ B) , _) ∣ Γ' ++ Δ ⊢f C

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
⊗l-ri : {Γ' Γ₀ Γ₁ : Cxt} {A B C : Fma} (f : just A ∣ Γ' ⊢ri C) (eq : Γ' ≡ Γ₀ ++ B ∷ Γ₁) → 
            just (A ⊗ B) ∣ Γ₀ ++ Γ₁ ⊢ri C
⊗l-ri (⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) eq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
⊗l-ri {Γ₀ = Γ₀} {Γ₁} (⊸r (ex {Δ = Δ} {Λ} (ri2c f) refl refl)) eq with cases++ Γ₀ Δ Γ₁ Λ eq
⊗l-ri {Γ₀ = Γ₀} {.(Ω₀ ++ Λ)} (⊸r (ex {Δ = .(Γ₀ ++ _ ∷ Ω₀)} {Λ} (ri2c f) refl refl)) refl | inj₁ (Ω₀ , refl , refl) = ⊸r (ex {Δ = Γ₀ ++ Ω₀} {Λ} (ri2c (⊗l-ri f refl)) refl refl)
⊗l-ri {Γ₀ = .(Δ ++ Ω₀)} {Γ₁} (⊸r (ex {Δ = Δ} {.(Ω₀ ++ _ ∷ Γ₁)} (ri2c f) refl refl)) refl | inj₂ (Ω₀ , refl , refl) = ⊸r (ex {Δ = Δ} {Ω₀ ++ Γ₁} (ri2c (⊗l-ri {Γ₀ = Δ ++ _ ∷ Ω₀} f refl)) refl refl)
⊗l-ri {Γ₀ = Γ₀} (li2ri {C = C} f) refl = li2ri {C = C} (⊗l (ex {Δ = Γ₀} (ri2c (li2ri f)) refl refl))

⊗l-c' : ∀ {Γ Γ' Δ A B C} (f : just A ∣ Γ' ؛ Δ ⊢c C) (p : Γ' ≡ B ∷ Γ) → 
                             just (A ⊗ B) ∣ Γ ؛ Δ ⊢c C
⊗l-c' (ex {Γ = []} (ex {Γ = Γ} f eq'' eq₂) eq' eq) eq₁ = ⊥-elim ([]disj∷ Γ eq'')
⊗l-c' (ex {Γ = []} (ri2c f) refl eq') refl = ri2c (⊗l-ri f eq')
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
pass-ri {Γ = .(_)} {A = A'} (⊸r {A = A} (ex {Δ = Δ} {Λ = Λ} (ri2c f) refl refl)) = ⊸r (ex {Γ = []} {Δ = A' ∷ Δ} {Λ = Λ} (ri2c (pass-ri f)) refl refl) 
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
⊸l-c f (ex g refl refl) = ex (⊸l-c f g) refl refl
⊸l-c f (ri2c g) = ⊸l-c-ri f g

⊸l-c-ri (ex f refl refl) g = ex (⊸l-c-ri f g) refl refl
⊸l-c-ri (ri2c f) g = ri2c (⊸l-ri f g)

⊸l-ri f (⊸r (ex (ex {Γ = x ∷ Γ} g refl refl) eq' eq)) = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
⊸l-ri {Γ = Γ} f (⊸r (ex {Δ = Δ} {Λ} (ri2c g) refl refl)) = ⊸r (ex {Δ = Γ ++ Δ} {Λ} (ri2c (⊸l-ri f g)) refl refl) -- ⊸r (⊸l-ri-c f g)
⊸l-ri f (li2ri g) = li2ri (p2li (f2p (⊸l f g)))

-- ⊗r rule in phase c



-- isInter++? : {X : Set} → {xs ys zs : List X} → (zs₀ zs₁ : List X) → zs ≡ zs₀ ++ zs₁ → isInter xs ys zs → 
--                          Σ (List X) (λ xs₀ → Σ (List X) (λ xs₁ → Σ (List X) (λ ys₀ → Σ (List X) (λ ys₁ → xs ≡ xs₀ ++ xs₁ × ys ≡ ys₀ ++ ys₁ × isInter xs₀ ys₀ zs₀ × isInter xs₁ ys₁ zs₁))))
-- isInter++? zs₀ zs₁ eq isInter[] with []++ {xs = zs₀} {zs₁} eq
-- ... | refl , refl = [] , [] , [] , [] , refl , refl , isInter[] , isInter[]
-- isInter++? [] (x ∷ zs₁) refl []left = [] , [] , [] , (x ∷ zs₁) , refl , refl , isInter[] , []left
-- isInter++? (x ∷ zs₀) zs₁ refl []left = []  , [] , (x ∷ zs₀) , zs₁ , refl , refl , []left , isInter-sym ([]right' zs₁)
-- isInter++? [] (x ∷ zs₁) refl []right = [] , (x ∷ zs₁)  , [] , [] , refl , refl , isInter[] , []right
-- isInter++? (x ∷ zs₀) zs₁ refl []right = (x ∷ zs₀) , zs₁ , [] , [] , refl , refl , []right , []right' zs₁
-- isInter++? [] (x ∷ zs₁) refl (∷left {y = y} {xs} {ys = ys} inTeq) = [] , (x ∷ xs) , [] , (y ∷ ys) , refl , refl , isInter[] , ∷left inTeq
-- isInter++? (x ∷ zs₀) zs₁ refl (∷left inTeq) with isInter++? zs₀ zs₁ refl inTeq
-- ... | xs₀' , xs₁' , ys₀' , ys₁' , refl , eq₁ , inTeq' , inTeq'' = (x ∷ xs₀') , xs₁' , ys₀' , ys₁' , refl , eq₁ , ∷left' ys₀' inTeq' , inTeq''
-- isInter++? [] (x ∷ zs₁) refl (∷right {x₁} {xs = xs} {ys} inTeq) = [] , (x₁ ∷ xs) , [] , (x ∷ ys) , refl , refl , isInter[] , ∷right inTeq
-- isInter++? (x ∷ zs₀) zs₁ refl (∷right inTeq) with isInter++? zs₀ zs₁ refl inTeq
-- ... | xs₀' , xs₁' , ys₀' , ys₁' , eq₀ , refl , inTeq' , inTeq'' = xs₀' , xs₁' , (x ∷ ys₀') , ys₁' , eq₀ , refl , ∷right' xs₀' inTeq' , inTeq''

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

tag-lem' :  {Γ₀ Γ₁ Γ : Cxt} → (eq : isInter Γ₀ Γ₁ Γ) → isInter (tagL Γ₀) (black Γ₁) (tag-isInter eq)
tag-lem' isInter[] = isInter[]
tag-lem' ([]left {x} {xs}) = []left
tag-lem' ([]right {x} {xs}) = []right
tag-lem' (∷left {x} eq) = ∷left (tag-lem' eq)
tag-lem' (∷right {x} {y} eq) = ∷right (tag-lem' eq)

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

⊸r⋆ : {S : Stp} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {A : Fma} →
      (f : S ∣ Γ ⊢ri A) (eq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁) → 
      ----------------------------------------
           S ∣ Γ₀ ⊢ri Γ₁ ⊸⋆ A
⊸r⋆ .[] f eq (empty refl) with isInter-left[] eq
... | refl = f
⊸r⋆ (D ∷ Γ₁) f eq (cons {xs₀ = Γ₀₁'} {Γ₁₁'} refl peq) with isInter-split-r Γ₀₁' Γ₁₁' refl eq
... | Γ₀₀ , Γ₀₁ , Λ₀ , Λ₁ , inTeq1 , inTeq2 , refl , refl , refl = ⊸r (ex {Δ = Γ₀₀} {Γ₀₁} (ri2c (⊸r⋆ Γ₁ f (isInter++ inTeq1 (∷left' Γ₁₁' inTeq2)) peq)) refl refl)


⊸r⋆∙ : {S : Stp} {Γ Γ₀ : TCxt} → {Γ₁' : Cxt} (Γ₁ : Cxt) {A : Fma} →
      (f : ∙ ∣ S ∣ Γ ⊢ri A) (eq : isInter Γ₀ (black Γ₁') Γ) (peq : Γ₁' ↭' Γ₁) → 
      ----------------------------------------
      ∙ ∣ S ∣ Γ₀ ⊢ri Γ₁ ⊸⋆ A
⊸r⋆∙ {Γ₁' = Γ₁'} [] f eq (empty refl) with isInter-left[] eq
... | refl = f
⊸r⋆∙ (D ∷ Γ₁) f eq (cons {xs₀ = Γ₀₁'} {Γ₁₁'} refl peq) with isInter-split-r (black Γ₀₁') (black Γ₁₁') refl eq
... | Γ₀₀ , Γ₀₁ , Λ₀ , Λ₁ , inTeq1 , inTeq2 , refl , refl , refl = ⊸r∙ (ex∙ {Δ = Γ₀₀} {Γ₀₁} (ri2c (⊸r⋆∙ Γ₁ f (isInter++ inTeq1 (∷left' {x = (∙ , D)} (black Γ₁₁') inTeq2)) peq)) refl refl)


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
... | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , inTeq' , inTeq'' , refl , refl , _ = gen⊗r-ri (Γ₁ ∷ʳ _) f g ((isInter++ inTeq' (∷right' Γ₀₁ inTeq''))) ((snoc↭' refl peq))
gen⊗r-ri Γ₁ (li2ri f) g eq peq = gen⊗r-li Γ₁ f g eq peq

gen⊗r-li Γ₁ (Il f) g eq peq = Il (gen⊗r-li Γ₁ f g eq peq)
gen⊗r-li Γ₁ (⊗l (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) g eq peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
gen⊗r-li Γ₁ {Δ = Δ₁} (⊗l {B = B} (ex {Δ = Δ} {Λ} (ri2c (li2ri f)) refl refl)) g eq peq with isInter++? Δ Λ refl eq
... | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , inTeq' , inTeq'' , refl , refl , refl = ⊗l (ex {Δ = Γ₀₀} {Γ₀₁ ++ Δ₁} (ri2c (li2ri (gen⊗r-li Γ₁ f g (isInter++ inTeq' (∷left' Γ₁₁' inTeq'')) peq))) refl refl)
gen⊗r-li Γ₁ (p2li f) g eq peq = p2li (gen⊗r-p Γ₁ f g eq peq)


gen⊗r-p Γ₁ (pass {Γ} f) g []left peq = f2p (⊗r (⊸r⋆∙ {Γ₀ = []} Γ₁ (li2ri (p2li (pass∙ f))) []left peq) g)
gen⊗r-p Γ₁ (pass {Γ = Γ} f) g []right peq with empty↭' peq
... | refl = pass (gen⊗r-li [] f g ([]right' Γ) (empty refl))
gen⊗r-p Γ₁ (pass f) g (∷left eq) peq = pass (gen⊗r-li Γ₁ f g eq peq)
gen⊗r-p Γ₁ (pass f) g (∷right {A'} {xs = Γ₀} eq) peq = f2p (⊗r {Γ = A' ∷ Γ₀} (⊸r⋆∙ Γ₁ (li2ri (p2li (pass∙ f))) (∷right (tag-lem' eq)) peq) g)
-- with tag-lem eq
-- ... | Γ' , eq' , refl = f2p (⊗r {Γ = A' ∷ Γ₀} (⊸r⋆∙ Γ₁ (li2ri (p2li (pass∙ f))) (∷right eq') peq) g)
gen⊗r-p Γ₁ (f2p f) g eq peq = f2p (gen⊗r-f Γ₁ f g eq peq)

-- gen⊗r-f ax , Ir
gen⊗r-f {Γ₀ = Γ₀} {Γ₁'} Γ₁ ax g eq peq with []++ {xs = Γ₀} {Γ₁'} (isInter-end[] eq )
... | refl , refl with empty↭' peq
... | refl = ⊗r (li2ri (p2li (f2p ax))) g

gen⊗r-f {Γ₀ = Γ₀} {Γ₁'} Γ₁ Ir g eq peq with []++ {xs = Γ₀} {Γ₁'} (isInter-end[] eq )
... | refl , refl with empty↭' peq
... | refl = ⊗r (li2ri (p2li (f2p Ir))) g

-- gen⊗r-f ⊸l
gen⊗r-f  Γ₁ {Δ = Δ₁} (⊸l {Γ} {Δ} f f') g eq peq with isInter++? Γ Δ refl eq
... | Γ₀₀ , Γ₀₁ , [] , Γ₁₁' , inTeq , inTeq' , refl , refl , refl with isInter-left[] inTeq
... | refl = ⊸l {Γ = Γ} {Γ₀₁ ++ Δ₁} f (gen⊗r-li Γ₁ f' g inTeq' peq)
gen⊗r-f  Γ₁ (⊸l {Γ} {Δ} f f') g eq peq | Γ₀₀ , Γ₀₁ , D ∷ Λ , Γ₁₁' , inTeq , inTeq' , refl , refl , refl with isInter-split-r [] Λ  refl inTeq
... | Γ₀₀₀ , Γ₀₀₁ , Γ'' , Γ''' , inTeq1 , inTeq2 , refl , refl , refl with isInter-left[] inTeq1
... | refl with tag-lem-left[] inTeq1
... | .(tagL Γ₀₀₀) , inTeq1' , refl = ⊗r {Γ = Γ₀₀₀ ++ Γ₀₀₁ ++ Γ₀₁} (⊸r⋆∙ {Γ = tagL Γ₀₀₀ ++ (∙ , D) ∷ tag-isInter inTeq2 ++ tag-isInter inTeq'} Γ₁ (li2ri (p2li (f2p (⊸l∙ {Γ' = tagL Γ₀₀₀ ++ (∙ , D) ∷ tag-isInter inTeq2} {Λ = tag-isInter inTeq2} {Δ = tag-isInter inTeq'} f f' refl)))) (isInter++l (tagL Γ₀₀₀) (∷right' {x = (∙ , D)} ((tagL Γ₀₀₁) ++ (tagL Γ₀₁)) (isInter++ (tag-lem' inTeq2) (tag-lem' inTeq')))) peq) g





-- ⊗r (⊸r⋆∙ Γ₁ {!   !} {!  (isInter++ (isInter++l Γ₀₀₀ (∷right' Γ₀₀₁ inTeq2)) inTeq')  !}  peq) g
-- with isInter-consL inTeq
-- ... | Γ₀₀₀ , Γ₀₀₁ , Γ'' , refl , refl , inTeq₁ = 
--       ⊗r {Γ = Γ₀₀ ++ Γ₀₁} (⊸r⋆∙ {Γ = tagL Γ₀₀₀ ++ (∙ , D) ∷ tag-isInter inTeq₁ ++ tag-isInter inTeq'} Γ₁ (li2ri (p2li (f2p (⊸l∙ {Γ = tagL Γ₀₀₀}
--       {Γ' = tagL Γ₀₀₀ ++ (∙ , D) ∷ tag-isInter inTeq₁} {Λ = tag-isInter inTeq₁}
--       {Δ = tag-isInter inTeq'} f f' refl)))) ((isInter++l {xs' = tagL Γ₀₀₁ ++ tagL Γ₀₁} {zs' = (∙ , D) ∷ tag-isInter inTeq₁ ++ tag-isInter inTeq'} (tagL Γ₀₀₀) (∷right' (tagL Γ₀₀₁ ++ tagL Γ₀₁) (isInter++ (tag-lem' inTeq₁) (tag-lem' inTeq'))))) peq) g

-- gen⊗r-f ⊗

gen⊗r-f Γ₁ (⊗r {S = S} {Γ} {Δ} f f') g eq peq with isInter++? Γ Δ refl eq
... | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , inTeq , inTeq' , refl , refl , refl = ⊗r {Γ = Γ₀₀ ++ Γ₀₁} (⊸r⋆∙ {Γ = tag-isInter inTeq ++ tag-isInter inTeq'} Γ₁ (li2ri (p2li {S = S} (f2p (⊗r {Γ = tag-isInter inTeq} {tag-isInter inTeq'} f f')))) (isInter++ (tag-lem' inTeq) (tag-lem' inTeq')) peq) g

-- ⊗r in phase c
⊗r-c : {S : Stp} {Ω Γ Δ : Cxt} {A B : Fma} → 
          (f : S ∣ Ω ؛ [] ⊢c A) (g : - ∣ Γ ؛ Δ ⊢c B) → 
          ----------------------------------------------
             S ∣ Ω ++ Γ ؛ Δ ⊢c A ⊗ B
⊗r-c f (ex g refl refl) = ex (⊗r-c f g) refl refl
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
  