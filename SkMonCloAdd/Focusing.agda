{-# OPTIONS --rewriting #-}

module Focusing where

open import Data.List renaming (map to mapList)
open import Data.List.Relation.Unary.All
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])
open import Data.Bool hiding (_∧_; _∨_)

open import Utilities
open import Formulae 

data Tag : Set where
  E : Tag
  L : Tag
  R : Tag


-- Tagged context 
-- TCxt : List Tag → Set
-- TCxt [] = {!   !}
-- TCxt (x ∷ T₁) = {!   !}

-- tcxt : (x : Tag) → TCxt x → Cxt
-- tcxt ∘ Ω = []
-- tcxt ∙ Ω = Ω

-- T[] : (x : Tag) → TCxt x
-- T[] ∘ = tt
-- T[] ∙ = []

-- {- ====================================================== -}
-- -- Inference rules of focused seqent calculus

-- -- Sequents have 4 phases:

-- ri = right invertible
data _∣_⊢ri_ : Stp → Cxt → Fma → Set

data _∣_∣_؛_⊢riT_ : (l : List Tag) → Irr → Cxt → Cxt → Fma → Set

-- l = left phase 
data _∣_⊢li_ : Stp → Cxt → Pos → Set
data _∣_∣_؛_⊢liT_ : (l : List Tag) → Irr → Cxt → Cxt → Pos → Set

-- p = passviation
data _∣_⊢p_ : Irr → Cxt → Pos → Set
data _∣_∣_؛_⊢pT_ : (l : List Tag) → Irr → Cxt → Cxt → Pos → Set

-- f = focusing
data _∣_⊢f_ : Irr → Cxt → Pos → Set
data _∣_∣_؛_⊢fT_ : (l : List Tag) → Irr → Cxt → Cxt → Pos → Set

data _∣_⊢ri_ where
  ⊸r : {S : Stp} {Γ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ∷ʳ A ⊢ri B) 
    ------------------------
    →      S ∣ Γ ⊢ri A ⊸ B
  ∧r : {S : Stp} {Γ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ⊢ri A) (g : S ∣ Γ ⊢ri B)
    ---------------------------------------
    →          S ∣ Γ ⊢ri A ∧ B
  li2ri : {S : Stp} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢li C)
    ------------------------
    →      S ∣ Γ ⊢ri pos C

data _∣_∣_؛_⊢riT_ where
  ⊸rT : {l : List Tag} {S : Irr} {Γ Ω : Cxt} {A B : Fma}
    → (f : l ∣ S ∣ Γ ؛ Ω ∷ʳ A ⊢riT B)
    ------------------------------------
    →      l ∣ S ∣ Γ ؛ Ω ⊢riT B
  ∧rT : {l l' : List Tag} {S : Irr} {Γ Ω : Cxt} {A B : Fma}
    → (f : l ∣ S ∣ Γ ؛ Ω ⊢riT A) (g : l' ∣ S ∣ Γ ؛ Ω ⊢riT B)
    ---------------------------------------------------------
    →             (l ++ l') ∣ S ∣ Γ ؛ Ω ⊢riT A ∧ B
  li2ri : {l : List Tag} {S : Irr} {Γ Ω : Cxt} {C : Pos}
    → (f : l ∣ S ∣ Γ ؛ Ω ⊢liT C)
    ------------------------
    →    l ∣ S ∣ Γ ؛ Ω ⊢riT pos C
data _∣_⊢li_ where
  ⊗l : {Γ : Cxt} {A B : Fma} {C : Pos}
       (f : just A ∣ B ∷ Γ ⊢li C) →
    -------------------------------------
          just (A ⊗ B) ∣ Γ ⊢li C
  Il : {Γ : Cxt} {C : Pos}
       (f : - ∣ Γ ⊢li C) →
    -------------------------
            just I ∣ Γ ⊢li C 
  ∨l : {Γ : Cxt} {A B : Fma} {C : Fma} {PC PC' : isPos C}
        (f : just A ∣ Γ ⊢li (C , PC)) (g : just B ∣ Γ ⊢li (C , PC')) → 
      ------------------------------------
             just (A ∨ B) ∣ Γ ⊢li (C , PC)
  p2li : {S : Irr} {Γ : Cxt} {C : Pos}
        (f : S ∣ Γ ⊢p C) →
        --------------------------
             irr S ∣ Γ ⊢li C 
data _∣_∣_؛_⊢liT_ where
  p2liT : {l : List Tag} {S : Irr} {Γ Ω : Cxt} {C : Pos}
          (f : l ∣ S ∣ Γ ؛ Ω ⊢pT C) → 
               l ∣ S ∣ Γ ؛ Ω ⊢liT C
data _∣_⊢p_ where
  pass : {Γ : Cxt} {A : Fma} {C : Pos}
         (f : just A ∣ Γ ⊢li C) → 
         --------------------------------
              (- , _) ∣ A ∷ Γ ⊢p C
  f2p : {S : Irr} {Γ : Cxt} {C : Pos}
          (f : S ∣ Γ ⊢f C) → 
          ----------------------------
               S ∣ Γ ⊢p C
data _∣_∣_؛_⊢pT_ where
  passT : {Ω : Cxt} {A : Fma} {C : Pos}
           (f : just A ∣ Ω ⊢li C) → 
           -------------------------------
               [] ∣ (- , _) ∣ [] ؛ A ∷ Ω ⊢pT C
  f2pT : {l : List Tag} {S : Irr} {Γ Ω : Cxt} {C : Pos}
           (f : l ∣ S ∣ Γ ؛ Ω ⊢fT C) → 
                l ∣ S ∣ Γ ؛ Ω ⊢pT C
data _∣_⊢f_ where
  ax : {X : At} → 
       (just (` X) , _) ∣ [] ⊢f (` X , _)
  Ir : (- , _) ∣ [] ⊢f (I , _)
  ⊗r : {l : List Tag} {S : Irr} {Γ Δ : Cxt} {A B : Fma} → 
         (f : l ∣ S ∣ Γ ؛ [] ⊢riT A) (g : - ∣ Δ  ⊢ri B) → 
         -----------------------------------
              S ∣ Γ ++ Δ ⊢f (A ⊗ B , _)
  ⊸l : {Γ Δ : Cxt} {A B : Fma} {C : Pos} → 
        (f : - ∣ Γ ⊢ri A) (g : just B ∣ Δ ⊢li C) → 
        ------------------------------------
             (just (A ⊸ B) , _) ∣ Γ ++ Δ ⊢f C
  ∨r₁ : {l : List Tag} {S : Irr} {Γ : Cxt} {A B : Fma} → 
          (f : l ∣ S ∣ Γ ؛ [] ⊢riT A) → 
         ------------------------------------------
               S ∣ Γ ⊢f (A ∨ B , _)
  ∨r₂ : {l : List Tag} {S : Irr} {Γ : Cxt} {A B : Fma} → 
          (f : l ∣ S ∣ Γ ؛ [] ⊢riT B) → 
         ------------------------------------------
               S ∣ Γ ⊢f (A ∨ B , _)
  ∧l₁ : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just A ∣ Γ ⊢li C) → 
        --------------------------------
             (just (A ∧ B) , _) ∣ Γ ⊢f C
  ∧l₂ : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just B ∣ Γ ⊢li C) → 
        --------------------------------
             (just (A ∧ B) , _) ∣ Γ ⊢f C
data _∣_∣_؛_⊢fT_ where 
  ax : {X : At} → 
       [] ∣ (just (` X) , _) ∣ [] ؛ [] ⊢fT (` X , _)
  Ir :  [] ∣ (- , _) ∣ [] ؛ [] ⊢fT (I , _)
  ⊗rT : {l : List Tag} {S : Irr} {Γ Δ Ω : Cxt} {A B : Fma} → 
         (f : l ∣ S ∣ Γ ؛ [] ⊢riT A) (g : - ∣ Δ ++ Ω ⊢ri B) → 
         -----------------------------------
              [ E ] ∣ S ∣ Γ ++ Δ ؛ Ω ⊢fT (A ⊗ B , _)
  ⊗rT2 : {l : List Tag} {S : Irr} {Γ Δ Ω : Cxt} {A B D : Fma} →
          (f : l ∣ S ∣ Γ ++ D ∷ Δ ؛ [] ⊢riT A) (g : - ∣ Ω ⊢ri B) → 
          ----------------------------------
               [ E ] ∣ S ∣ Γ ؛ D ∷ Δ ++ Ω ⊢fT (A ⊗ B , _)
  ⊸lT : {Γ Δ Ω : Cxt} {A B D : Fma} {C : Pos} → 
         (f : - ∣ Γ ++ D ∷ Δ ⊢ri A) (g : just B ∣ Ω ⊢li C) →
         -----------------------------------
              [] ∣ (just (A ⊸ B) , _) ∣ Γ ؛ D ∷ Δ ++ Ω ⊢fT C
  ∨r₁T : {l : List Tag} {S : Irr} {Γ Ω : Cxt} {A B : Fma} → 
          (f : l ∣ S ∣ Γ ++ Ω ؛ [] ⊢riT A) → 
         ------------------------------------------
               [ E ] ∣ S ∣ Γ ؛ Ω ⊢fT (A ∨ B , _)
  ∨r₂T : {l : List Tag} {S : Irr} {Γ Ω : Cxt} {A B : Fma} → 
          (f : l ∣ S ∣ Γ ++ Ω ؛ [] ⊢riT B) → 
         ------------------------------------------
               [ E ] ∣ S ∣ Γ ؛ Ω ⊢fT (A ∨ B , _)
  ∧l₁T : {Γ Ω : Cxt} {A B : Fma} {C : Pos}
        (f : just A ∣ Γ ++ Ω ⊢li C) → 
        --------------------------------
             [ L ] ∣ (just (A ∧ B) , _) ∣ Γ ؛ Ω ⊢fT C
  ∧l₂T : {Γ Ω : Cxt} {A B : Fma} {C : Pos}
        (f : just B ∣ Γ ++ Ω ⊢li C) → 
        --------------------------------
             [ R ] ∣ (just (A ∧ B) , _) ∣ Γ ؛ Ω ⊢fT C


-- data _؛_⇒_ : List (Cxt × Pos) → List (Cxt × Fma) → Fma → Set where 
--   stop' : {Φ : List (Cxt × Pos)}{A : Fma} → Φ ؛ [] ⇒ A
--   conj' : {Φ : List (Cxt × Pos)} {Ψ₀ Ψ₁ : List (Cxt × Fma)} {Γ' : Cxt} {A A' B' : Fma} 
--     → Φ ؛ Ψ₀ ++ (Γ' , A') ∷ (Γ' , B') ∷ Ψ₁ ⇒ A
--     → Φ ؛ Ψ₀ ++ (Γ' , A' ∧ B') ∷ Ψ₁ ⇒ A
--   impl' : {Φ : List (Cxt × Pos)} {Ψ₀ Ψ₁ : List (Cxt × Fma)} {Γ' : Cxt} {A A' B' : Fma}
--     → Φ ؛ Ψ₀ ++ (Γ' ++ A' ∷ [] , B') ∷ Ψ₁ ⇒ A
--     → Φ ؛ Ψ₀ ++ (Γ' , A' ⊸ B') ∷ Ψ₁ ⇒ A

-- -- Big Step Rule BSR

-- BSR : {S : Stp} {Γ Γ' Γ'' : Cxt} {A A' : Fma} {Φ : List (Cxt × Pos)} {Ψ₀ Ψ₁ : List (Cxt × Fma)}
--   → (f : S ∣ Γ'' ⊢ri A') (RS : Φ ؛ Ψ₀ ++ (Γ' , A') ∷ Ψ₁ ⇒ A)
--   → (eq : Γ'' ≡ Γ ++ Γ')
--   ---------------------------------------------------------------
--   → S ∣ Γ ⊢ri A
-- BSR (⊸r f) RS refl = {! RS  !}
-- BSR (∧r f f₁) RS eq = {!   !}
-- BSR {Ψ₀ = []} (li2ri f) RS eq = {!   !}
-- BSR {Ψ₀ = x ∷ Ψ₀} (li2ri f) RS eq = {!   !}
data Relation : List (Cxt × Fma) → Fma → Set where
  conj : {Φ Ψ : List (Cxt × Fma)} {A B : Fma} → 
      Relation Φ A → Relation Ψ B → 
      Relation (Φ ++ Ψ) (A ∧ B)
  impl : {Φ Θ : List (Cxt × Fma)} {A B : Fma} → 
      Relation Φ B → Θ ≡ mapList (λ ΔC → A ∷ proj₁ ΔC , proj₂ ΔC) Φ → 
      Relation Θ (A ⊸ B)
  stop : {A : Fma} → 
       Relation [ ([] , A) ]  A

-- module _ {A B C D E : Fma} where
--   Re : Relation (([] , A) ∷ ([ B ] , C) ∷ ((B ∷ D ∷ []) , E) ∷ []) (A ∧ (B ⊸ (C ∧ (D ⊸ E))))
--   Re = conj stop (impl (conj stop (impl stop)))

-- Match-ri : (S : Stp) (Γ : Cxt) → (Cxt × Fma) × Cxt → Set
-- Match-ri S Γ ((Γ' , A) , Δ') = Δ' ≡ Γ ++ Γ' × S ∣ Δ' ⊢ri A
Match-li' : (S : Stp) (Γ : Cxt) → (Cxt × Fma) → Set
Match-li' S Γ (Γ' , A) = Σ (isPos A) λ p → S ∣ Γ ++ Γ' ⊢li (A , p)

Match-li : (S : Stp) (Γ : Cxt) → (Cxt × Pos) → Set
Match-li S Γ (Γ' , A) = S ∣ Γ ++ Γ' ⊢li A
Match-p : (S : Irr) (Γ : Cxt) → (Cxt × Pos) → Set
Match-p S Γ (Γ' , A) = S ∣ Γ ++ Γ' ⊢p A
Match-f : (S : Irr) (Γ : Cxt) → (Cxt × Pos) → Set
Match-f S Γ (Γ' , A) = S ∣ Γ ++ Γ' ⊢f A
lem : {A B : Set} {f : A → B} (xs : List A) (ys₀ ys₁ : List B) 
  → (eq : mapList f xs ≡ ys₀ ++ ys₁) 
  → Σ (List A) λ xs₀ → Σ (List A) λ xs₁ →  xs ≡ xs₀ ++ xs₁ × mapList f xs₀ ≡ ys₀ × mapList f xs₁ ≡ ys₁ 
lem xs [] ys₁ eq = [] , xs , refl , refl , eq
lem (x₁ ∷ xs) (x ∷ ys₀) ys₁ eq with lem xs ys₀ ys₁ (proj₂ (inj∷ eq)) 
... | xs₀ , xs₁ , refl , refl , refl = x₁ ∷ xs₀ , xs₁ , refl , cong (λ x → x ∷ mapList _ xs₀) (proj₁ (inj∷ eq)) , refl
-- mapList++ : {A B : Set} {f : A → B} (xs ys : List A) 
--   → mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
-- {-# REWRITE mapList++ #-}

-- Realation⊸r : {Γ' : Cxt} {Θ Θ' Θ'' : List (Cxt × Fma)} {A B C : Fma}
--   → Relation Θ'' C 
--   → (Θ'' ≡ Θ' ++ (Γ' , A ⊸ B) ∷ Θ) → Relation (Θ' ++ (Γ' ++ A ∷ [] , B) ∷ Θ) C
-- Realation⊸r (conj RS RS₁) eq = {!   !}
-- Realation⊸r {Θ' = []} (impl {(fst , .(_ ⊸ _)) ∷ Φ} RS refl) refl = impl (Realation⊸r {Γ' = fst} {Θ = Φ} {Θ' = []} RS refl) refl
-- Realation⊸r {Θ = Θ} {Θ' = x ∷ Θ'} (impl {x₁ ∷ Φ} RS refl) eq with inj∷ eq
-- ... | refl , eq' with lem Φ Θ' (_ ∷ Θ) eq'
-- ... | Φ₀ , (Γ' , .(_ ⊸ _)) ∷ Φ₁ , refl , refl , refl = impl {Φ = x₁ ∷ Φ₀ ++ ((Γ' ++ _ ∷ []) , _) ∷ Φ₁} (Realation⊸r {Θ' = x₁ ∷ Φ₀} RS refl) (cong (λ x → (_ ∷ proj₁ x₁ , proj₂ x₁) ∷ x) (sym (mapList++ Φ₀ (((Γ' ++ _ ∷ []) , _) ∷ Φ₁))))
-- Realation⊸r {Θ' = []} stop refl = impl stop refl -- impl stop
-- Realation⊸r {Θ' = x ∷ Θ'} stop eq = ⊥-elim ([]disj∷ Θ' (proj₂ (inj∷ eq))) -- imposs
-- Relation∧r : {Γ' : Cxt} {Θ Θ' Θ'' : List (Cxt × Fma)} {A B C : Fma}
--   → Relation Θ'' C 
--   → (Θ'' ≡ Θ' ++ (Γ' , A ∧ B) ∷ Θ) → Relation (Θ' ++ (Γ' , A) ∷ (Γ' , B) ∷ Θ) C
-- All-snoc : {A : Set} {P : A → Set} {xs : List A} (ps : All P xs) {x : A} (p : P x)
--   → All P (xs ++ x ∷ [])
-- All-snoc [] p = p ∷ []
-- All-snoc (px ∷ ps) p = px ∷ All-snoc ps p
-- gen∨r₁-ri : {S : Stp} {Γ Γ' Γ'' : Cxt} {A B A' : Fma}
--   → (Θr : List ((Cxt × Fma) × Cxt))
--   → (Θl : List ((Cxt × Pos) × Cxt))
--   → Relation (mapList (λ x → proj₁ (proj₁ x) , proj₁ (proj₂ (proj₁ x))) Θl ++ (Γ'' , A') ∷ mapList proj₁ Θr) A
--   → All (Match-li S Γ) Θl
--   → S ∣ Γ' ⊢ri A' 
--   → Γ' ≡ Γ ++ Γ''
--   → All (Match-ri S Γ) Θr
--   → S ∣ Γ ⊢ri A ∨ B
-- gen∨r₁-ri {Γ = Γ} {Γ'' = Γ''} Θr Θl RS FS (⊸r f) eq GS = gen∨r₁-ri Θr Θl (Realation⊸r RS refl) FS f (cong (λ x → x ++ _ ∷ []) {y = Γ ++ Γ''} eq) GS
-- gen∨r₁-ri {Γ = Γ} {Γ'' = Γ''} Θr Θl RS FS (∧r f f₁) refl GS = gen∨r₁-ri (((Γ'' , _) , Γ ++ Γ'') ∷ Θr) Θl (Relation∧r RS refl) FS f refl ({!   !} ∷ {!   !}) -- gen∨r₁ (_ ∷ Θr) Θl {!   !} FS f refl ((refl , f₁) ∷ GS)
-- gen∨r₁-ri [] Θl RS FS (li2ri f) refl GS = {!   !}
-- gen∨r₁-ri {Γ = Γ} {Γ'' = Γ''} (((_ , _) , _) ∷ Θr) Θl RS FS (li2ri {C = A''} f) refl ((eq , g) ∷ GS) =
--   gen∨r₁-ri Θr (Θl ++ ((Γ'' , A'') , (Γ ++ Γ'')) ∷ []) RS (All-snoc FS (refl , f)) g eq GS

ri⋆ : {S : Stp} {Γ : Cxt} {A : Fma} {Θ : List (Cxt × Fma)}
  → (RS : Relation Θ A)
  → (FS : All (Match-li' S Γ) Θ)
  → S ∣ Γ ⊢ri A
ri⋆ (conj RS RS₁) FS = ∧r {!   !} {!   !}
ri⋆ (impl RS refl) FS = ⊸r (ri⋆ RS {!   !})
ri⋆ stop ((p , f) ∷ []) = li2ri f
riT⋆ : {l : List Tag} {S : Irr} {Γ Δ : Cxt} {A : Fma} {Θ : List (Cxt × Fma)}
  → (RS : Relation Θ A)
  → (FS : All (Match-li' (proj₁ S) (Γ ++ Δ)) Θ)
  → l ∣ S ∣ Γ ؛ Δ ⊢riT A
riT⋆ RS FS = {!   !}
match-li-⊗ : {Γ : Cxt} {A B : Fma} {Θ : List (Cxt × Pos)}
  → All (Match-li (just (A ⊗ B)) Γ) Θ 
  → All (Match-li (just A) (B ∷ Γ)) Θ
match-li-⊗ [] = []
match-li-⊗ (⊗l f ∷ FS) = f ∷ match-li-⊗ FS
match-li-∨₁ : {Γ : Cxt} {A B : Fma} {Θ : List (Cxt × Pos)}
  → All (Match-li (just (A ∨ B)) Γ) Θ 
  → All (Match-li (just A) Γ) Θ
match-li-∨₁ [] = []
match-li-∨₁ (∨l f f₁ ∷ FS) = f ∷ match-li-∨₁ FS
match-li-∨₂ : {Γ : Cxt} {A B : Fma} {Θ : List (Cxt × Pos)}
  → All (Match-li (just (A ∨ B)) Γ) Θ 
  → All (Match-li (just B) Γ) Θ
match-li-∨₂ [] = []
match-li-∨₂ (∨l f f₁ ∷ FS) = {!  f₁ !} ∷ match-li-∨₂ FS -- f₁ ∷ match-li-∨₂ FS

gen∨r₁-li : {S : Stp} {Γ Δ : Cxt} (Γ' : Cxt) {A B : Fma} {A' : Pos}
  → {Θ : List (Cxt × Pos)}
  → Relation ((Γ' , proj₁ A') ∷ (mapList (λ x → proj₁ x , proj₁ (proj₂ x)) Θ)) A
  → (f : S ∣ Δ ⊢li A')
  → (eq : Δ ≡ Γ ++ Γ')
  → All (Match-li S Γ) Θ
  → S ∣ Γ ⊢li (A ∨ B , _)
gen∨r₁-p-li : {Γ : Cxt} {A B A' : Fma}
  → (Θl Θp : List (Cxt × Pos)) 
  → Relation (mapList (λ x → proj₁ x , proj₁ (proj₂ x)) (Θl ++ Θp)) A
  → All (Match-li (just A') Γ) Θl
  → All (Match-p (- , _) (A' ∷ Γ)) Θp
  → (- , _) ∣ A' ∷ Γ ⊢p (A ∨ B , _)
gen∨r₁-p-f : {S : Irr} {Γ : Cxt} {A B : Fma}
  → (Θf Θp : List (Cxt × Pos)) 
  → Relation (mapList (λ x → proj₁ x , proj₁ (proj₂ x)) (Θf ++ Θp)) A
  → All (Match-f S Γ) Θf
  → All (Match-p S Γ) Θp
  → S ∣ Γ ⊢f (A ∨ B , _)
gen∨r₁-li Γ' RS (⊗l f) refl FS = ⊗l (gen∨r₁-li Γ' RS f refl (match-li-⊗ FS))
gen∨r₁-li Γ' RS (Il f) refl FS = {!   !}
gen∨r₁-li Γ' RS (∨l f f₁) refl FS = ∨l (gen∨r₁-li Γ' RS f refl (match-li-∨₁ FS)) ((gen∨r₁-li Γ' RS f₁ refl (match-li-∨₂ FS)))
gen∨r₁-li {Γ = []} .(_ ∷ _) RS (p2li (pass f)) refl FS = p2li (f2p (∨r₁ {!   !}))
gen∨r₁-li {Γ = x ∷ Γ} Γ' {Θ = Θ} RS (p2li (pass f)) refl FS = 
  p2li (gen∨r₁-p-li ((Γ' , _ ) ∷ []) Θ RS (f ∷ []) {!   !})
gen∨r₁-li Γ' {Θ = Θ} RS (p2li (f2p f)) refl FS = 
  p2li (f2p (gen∨r₁-p-f ((Γ' , _ ) ∷ []) Θ RS (f ∷ []) {!   !})) -- p2li (gen∨r₁-p  ((Γ' , A') ∷ Θ) RS (f ∷ {!   !}))
-- gen∨r₁ [] RS Fs = {!   !}
-- gen∨r₁ {Γ = Γ} (((Γ' , .(_ ⊸ _)) , Δ') ∷ Θ) RS ((eq , ⊸r f) ∷ Fs) = {! lem  !}
--   where
--     lem : {!   !} 
--     lem = gen∨r₁ ((((Γ' ++ _ ∷ []) , _ ) , Δ' ++ _ ∷ []) ∷ Θ) (Realation⊸r RS refl) ((cong (λ x → x ++ _ ∷ []) {y = Γ ++ Γ'} eq , f) ∷ Fs)
-- gen∨r₁ (((Γ' , .(_ ∧ _)) , Δ') ∷ Θ) RS ((eq , ∧r f f₁) ∷ Fs) = {!   !}
-- gen∨r₁ (((Γ' , .(pos _)) , Δ') ∷ Θ) RS ((eq , li2ri f) ∷ Fs) = {!   !}
-- admissible rules
Il-ri : {Γ : Cxt} {C : Fma}
        (f : - ∣ Γ ⊢ri C) →
    ------------------------
        just I ∣ Γ ⊢ri C 

Il-ri (⊸r f) = ⊸r (Il-ri f)
Il-ri (∧r f f₁) = ∧r (Il-ri f) (Il-ri f₁)
Il-ri (li2ri f) = li2ri (Il f)

⊗l-ri : {Γ : Cxt} {A B C : Fma}
        (f : just A ∣ B ∷ Γ ⊢ri C) →
      --------------------------------
           just (A ⊗ B) ∣ Γ ⊢ri C 

⊗l-ri (⊸r f) = ⊸r (⊗l-ri f)
⊗l-ri (∧r f f₁) = ∧r (⊗l-ri f) (⊗l-ri f₁)
⊗l-ri (li2ri f) = li2ri (⊗l f)

∨l-ri : {Γ : Cxt} {A B C : Fma} 
        (f : just A ∣ Γ ⊢ri C) (g : just B ∣ Γ ⊢ri C) → 
            just (A ∨ B) ∣ Γ ⊢ri C
∨l-ri (⊸r f) (⊸r g) = ⊸r (∨l-ri f g)
∨l-ri (∧r f f₁) (∧r g g₁) = ∧r (∨l-ri f g) (∨l-ri f₁ g₁)
∨l-ri (li2ri f) (li2ri f₁) = li2ri (∨l f f₁) 

pass-ri : {Γ : Cxt} {A C : Fma}
          (f : just A ∣ Γ ⊢ri C) →
     --------------------------------
              - ∣ A ∷ Γ ⊢ri C 

pass-ri (⊸r f) = ⊸r (pass-ri f)
pass-ri (∧r f f₁) = ∧r (pass-ri f) (pass-ri f₁)
pass-ri (li2ri f) = li2ri (p2li (pass f))

Ir-ri : - ∣ [] ⊢ri I
Ir-ri = li2ri (p2li (f2p Ir))

⊸l-ri : {Γ Δ : Cxt} {A B C : Fma} 
        (f : - ∣ Γ ⊢ri A) (g : just B ∣ Δ ⊢ri C) →
      ---------------------------------------------
         just (A ⊸ B) ∣ Γ ++ Δ ⊢ri C

⊸l-ri f (⊸r g) = ⊸r (⊸l-ri f g)
⊸l-ri f (∧r g g₁) = ∧r (⊸l-ri f g) (⊸l-ri f g₁)
⊸l-ri f (li2ri g) = li2ri (p2li (f2p (⊸l f g)))

∧l₁-ri : {Γ : Cxt} {A B C : Fma}
         (f : just A ∣ Γ ⊢ri C) → 
              just (A ∧ B) ∣ Γ ⊢ri C
∧l₁-ri (⊸r f) = ⊸r (∧l₁-ri f)
∧l₁-ri (∧r f f₁) = ∧r (∧l₁-ri f) (∧l₁-ri f₁)
∧l₁-ri (li2ri f) = li2ri (p2li (f2p (∧l₁ f)))

∧l₂-ri : {Γ : Cxt} {A B C : Fma}
         (f : just B ∣ Γ ⊢ri C) → 
              just (A ∧ B) ∣ Γ ⊢ri C
∧l₂-ri (⊸r f) = ⊸r (∧l₂-ri f)
∧l₂-ri (∧r f f₁) = ∧r (∧l₂-ri f) (∧l₂-ri f₁)
∧l₂-ri (li2ri f) = li2ri (p2li (f2p (∧l₂ f)))

-- ⊗r-ri : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
--          (f : S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B) → 
--                S ∣ Γ ++ Δ ⊢ri A ⊗ B


   