{-# OPTIONS --rewriting #-}

module Focusing1 where

open import Data.List renaming (map to mapList; zip to zipList)
open import Data.List.Relation.Unary.All renaming (map to mapAll)
open import Data.List.Properties
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])
open import Data.Bool hiding (_∧_; _∨_)

open import Utilities
open import Formulae1 
-- Seq-p : Set
-- Seq-p = Irr × Cxt × Pos
-- Seq-ri : Set
-- Seq-ri = Irr × Cxt × Fma
-- data hyper-ri : Irr → Cxt → List Pos → List Fma → Set
-- data hyper-p : Irr → Cxt → List Pos → List Pos → Set
-- -- data hyper-p-conj :  

-- data _∣_⊢ri_ : Stp → Cxt → Fma → Set


-- -- l = left phase 
-- data _∣_⊢li_ : Stp → Cxt → Pos → Set

-- -- p = passviation
-- data _∣_⊢p_ : Irr → Cxt → Pos → Set

-- -- f = focusing
-- data _∣_⊢f_ : Irr → Cxt → Pos → Set

-- data _∣_⊢ri_ where
--   ∧r : {S : Stp} {Γ : Cxt} {A B : Fma}
--     → (f : S ∣ Γ ⊢ri A) (g : S ∣ Γ ⊢ri B)
--     ---------------------------------------
--     →          S ∣ Γ ⊢ri A ∧ B
--   li2ri : {S : Stp} {Γ : Cxt} {C : Pos}
--     → (f : S ∣ Γ ⊢li C)
--     ------------------------
--     →      S ∣ Γ ⊢ri pos C

-- data hyper-ri where
--   ∧r : {S : Irr} {Γ : Cxt} {A B : Fma}
--    {Θp : List Pos} {Θri : List Fma}
--    → hyper-ri S Γ Θp (A ∷ B ∷ Θri) 
--    → hyper-ri S Γ Θp (A ∧ B ∷ Θri)
--   p2riT : {S : Irr} {Γ : Cxt} {P : Pos}
--    {Θp : List Pos} {Θri : List Fma}
--    → hyper-ri S Γ (Θp ++ P ∷ []) Θri
--    → hyper-ri S Γ Θp ((pos P) ∷ Θri)
--   hp2ri : {S : Irr} {Γ : Cxt} {Θp : List Pos} 
--    → hyper-p S Γ [] Θp
--    → hyper-ri S Γ Θp []
  
-- data hyper-p where
--   pass : {A : Fma} {Γ : Cxt} {P : Pos}
--    {Θli : List Pos} {Θp : List Pos}
--    → hyper-p (- , _) (A ∷ Γ) (Θli ++ P ∷ []) Θp
--    → hyper-p (- , _) (A ∷ Γ) Θli (P ∷ Θp)
--   f2p-emp : {A : Fma} {Γ : Cxt} {P : Pos}
--    {Θli : List Pos} {Θp : List Pos}
--    → All (λ P' → just A ∣ Γ ⊢li P') Θli 
--    → (- , _) ∣ A ∷ Γ ⊢f P 
--    → All (λ P' → (- , _) ∣ A ∷ Γ ⊢p P') Θp
--    → hyper-p (- , _) (A ∷ Γ) Θli (P ∷ Θp)
-- data _∣_⊢li_ where
--   ⊗l : {Γ : Cxt} {A B : Fma} {C : Pos}
--        (f : just A ∣ B ∷ Γ ⊢li C) →
--     -------------------------------------
--           just (A ⊗ B) ∣ Γ ⊢li C
--   Il : {Γ : Cxt} {C : Pos}
--        (f : - ∣ Γ ⊢li C) →
--     -------------------------
--             just I ∣ Γ ⊢li C 
--   p2li : {S : Irr} {Γ : Cxt} {C : Pos}
--         (f : S ∣ Γ ⊢p C) →
--         --------------------------
--              irr S ∣ Γ ⊢li C 

-- data _∣_⊢p_ where
--   pass : {Γ : Cxt} {A : Fma} {C : Pos}
--          (f : just A ∣ Γ ⊢li C) → 
--          --------------------------------
--               (- , _) ∣ A ∷ Γ ⊢p C
--   f2p : {S : Irr} {Γ : Cxt} {C : Pos}
--           (f : S ∣ Γ ⊢f C) → 
--           ----------------------------
--                S ∣ Γ ⊢p C

-- data _∣_⊢f_ where
--   ax : {X : At} → 
--        (just (` X) , _) ∣ [] ⊢f (` X , _)
--   Ir : (- , _) ∣ [] ⊢f (I , _)
--   ⊗r : {S : Irr} {Γ Δ : Cxt} {A B : Fma} → 
--          (f : hyper-ri S Γ [] (A ∷ [])) (g : - ∣ Δ  ⊢ri B) → 
--          -----------------------------------
--               S ∣ Γ ++ Δ ⊢f (A ⊗ B , _)
--   ∧l₁ : {Γ : Cxt} {A B : Fma} {C : Pos}
--         (f : just A ∣ Γ ⊢li C) → 
--         --------------------------------
--              (just (A ∧ B) , _) ∣ Γ ⊢f C
--   ∧l₂ : {Γ : Cxt} {A B : Fma} {C : Pos}
--         (f : just B ∣ Γ ⊢li C) → 
--         --------------------------------
--              (just (A ∧ B) , _) ∣ Γ ⊢f C

data Tag : Set where
  E : Tag
  L : Tag
  R : Tag
  P : Tag
--   NP : Tag


-- -- {- ====================================================== -}
-- -- -- Inference rules of focused seqent calculus

-- -- -- Sequents have 4 phases:

isOKL : List Tag → Set
isOKL (R ∷ l) = ⊤
isOKL (E ∷ l) = ⊤
isOKL (L ∷ l) = isOKL l
isOKL _ = ⊥

isOKR : List Tag → Set
isOKR (L ∷ l) = ⊤
isOKR (E ∷ l) = ⊤
isOKR (R ∷ l) = isOKR l
isOKR _ = ⊥

isOK : List Tag → Set
isOK [] = ⊥
isOK (E ∷ l) = ⊤
isOK (L ∷ l) = isOKL l
isOK (R ∷ l) = isOKR l
isOK (P ∷ l) = isOK l 

isOKeq : {t t' : List Tag} (eq : t ≡ t')
  → isOK t → isOK t'
isOKeq refl ok = ok 

-- ri = right invertible
data _∣_⊢ri_ : Stp → Cxt → Fma → Set

data _∣_∣_⊢riT_ : (l : List Tag) → Irr → Cxt → Fma → Set

-- l = left phase 
data _∣_⊢li_ : Stp → Cxt → Pos → Set

-- p = passviation
data _∣_⊢p_ : Irr → Cxt → Pos → Set
data _∣_∣_⊢pT_ : (t : Tag) → Irr → Cxt → Pos → Set

-- f = focusing
data _∣_⊢f_ : Irr → Cxt → Pos → Set
data _∣_∣_⊢fT_ : (t : Tag) → Irr → Cxt → Pos → Set

data _∣_⊢ri_ where
  ∧r : {S : Stp} {Γ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ⊢ri A) (g : S ∣ Γ ⊢ri B)
    ---------------------------------------
    →          S ∣ Γ ⊢ri A ∧ B
  li2ri : {S : Stp} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢li C)
    ------------------------
    →      S ∣ Γ ⊢ri pos C

data _∣_∣_⊢riT_ where
  ∧rT : {l l' : List Tag} {S : Irr} {Γ : Cxt} {A B : Fma}
    → (f : l ∣ S ∣ Γ ⊢riT A) (g : l' ∣ S ∣ Γ ⊢riT B)
    ---------------------------------------------------------
    →             (l ++ l') ∣ S ∣ Γ ⊢riT A ∧ B
  p2riT : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : t ∣ S ∣ Γ ⊢pT C)
    ------------------------
    →    [ t ] ∣ S ∣ Γ ⊢riT pos C
data _∣_⊢li_ where
  ⊗l : {Γ : Cxt} {A B : Fma} {C : Pos}
       (f : just A ∣ B ∷ Γ ⊢li C) →
    -------------------------------------
          just (A ⊗ B) ∣ Γ ⊢li C
  Il : {Γ : Cxt} {C : Pos}
       (f : - ∣ Γ ⊢li C) →
    -------------------------
            just I ∣ Γ ⊢li C 
  p2li : {S : Irr} {Γ : Cxt} {C : Pos}
        (f : S ∣ Γ ⊢p C) →
        --------------------------
             irr S ∣ Γ ⊢li C 
data _∣_⊢p_ where
  pass : {Γ : Cxt} {A : Fma} {C : Pos}
         (f : just A ∣ Γ ⊢li C) → 
         --------------------------------
              (- , _) ∣ A ∷ Γ ⊢p C
  f2p : {S : Irr} {Γ : Cxt} {C : Pos}
          (f : S ∣ Γ ⊢f C) → 
          ----------------------------
               S ∣ Γ ⊢p C
data _∣_∣_⊢pT_ where
  passT : {Ω : Cxt} {A : Fma} {C : Pos}
           (f : just A ∣ Ω ⊢li C) → 
           -------------------------------
               P ∣ (- , _) ∣ A ∷ Ω ⊢pT C
  f2pT : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
           (f : t ∣ S ∣ Γ ⊢fT C) → 
                t ∣ S ∣ Γ ⊢pT C
--   f2pT1 : {S : Irr} {Γ : Cxt} {C : Pos}
--            (f : S ∣ Γ ⊢f C) → 
--            NP ∣ S ∣ Γ ⊢pT C
data _∣_⊢f_ where
  ax : {X : At} → 
       (just (` X) , _) ∣ [] ⊢f (` X , _)
  Ir : (- , _) ∣ [] ⊢f (I , _)
  ⊗r : (l : List Tag) {S : Irr} {Γ Δ Γ' : Cxt} {A B : Fma} →
         (ok : isOK l) (eq : Γ' ≡ Γ ++ Δ) →  
         (f : l ∣ S ∣ Γ ⊢riT A) (g : - ∣ Δ  ⊢ri B) → 
         -----------------------------------
              S ∣ Γ' ⊢f (A ⊗ B , _)
  ∧l₁ : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just A ∣ Γ ⊢li C) → 
        --------------------------------
             (just (A ∧ B) , _) ∣ Γ ⊢f C
  ∧l₂ : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just B ∣ Γ ⊢li C) → 
        --------------------------------
             (just (A ∧ B) , _) ∣ Γ ⊢f C
data _∣_∣_⊢fT_ where 
  ax : {X : At} → 
       E ∣ (just (` X) , _) ∣ [] ⊢fT (` X , _)
  Ir :  E ∣ (- , _) ∣ [] ⊢fT (I , _)
  ⊗rT : (l : List Tag) {S : Irr} {Γ Δ Γ' : Cxt} {A B : Fma} →
         (ok : isOK l) (eq : Γ' ≡ Γ ++ Δ)→ 
         (f : l ∣ S ∣ Γ ⊢riT A) (g : - ∣ Δ ⊢ri B) → 
         -----------------------------------
              E ∣ S ∣ Γ' ⊢fT (A ⊗ B , _)
  ∧l₁T : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just A ∣ Γ ⊢li C) → 
        --------------------------------
              L ∣ (just (A ∧ B) , _) ∣ Γ ⊢fT C
  ∧l₂T : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just B ∣ Γ ⊢li C) → 
        --------------------------------
             R ∣ (just (A ∧ B) , _) ∣ Γ ⊢fT C


-- Tests for the focused calculus

-- test : {X Y Z : At} → just (` X ∧ ` Y) ∣ ` Z ∷ [] ⊢ri (` X ∧ ` Y) ⊗ ` Z
-- test = li2ri (p2li (f2p (⊗r _ _ (∧rT {Γ = []} (p2riT (f2pTL (∧l₁T (p2li (f2p ax))))) (p2riT (f2pTR (∧l₂T (p2li (f2p ax)))))) (li2ri (p2li (pass (p2li (f2p ax))))))))

-- sym-test : {X Y Z : At} → just (` X ∧ ` Y) ∣ ` Z ∷ [] ⊢ri (` Y ∧ ` X) ⊗ ` Z
-- sym-test = li2ri (p2li (f2p (⊗r (R ∷ L ∷ []) tt (∧rT {Γ = []} (p2riT (f2pTR (∧l₂T (p2li (f2p ax))))) (p2riT (f2pTL (∧l₁T (p2li (f2p ax)))))) (li2ri (p2li (pass (p2li (f2p ax))))))))

-- test' : {X Y Z : At} → just (` X ∧ ` Y) ∣ ` Z ∷ [] ⊢ri ` X ⊗ ` Z
-- test' = li2ri (p2li (f2p (⊗r {!   !} {!   !} (p2riT (f2pT (∧l₁T (p2li (f2p ax))))) ((li2ri (p2li (pass (p2li (f2p ax)))))))))


-- Tests for the focused calculus

data SubFmas : List Fma → Fma → Set where
  conj : {Φ Ψ : List Fma} {A A' B B' : Fma} → 
      SubFmas (A' ∷ Φ) A → SubFmas (B' ∷ Ψ) B → 
      SubFmas (A' ∷ Φ ++ B' ∷ Ψ) (A ∧ B)
  stop : {A : Fma} → 
       SubFmas [ A ]  A

mapList++ : {A B : Set} {f : A → B} (xs ys : List A) 
  → mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
mapList++ [] ys = refl
mapList++ {f = f} (x ∷ xs) ys = cong (f x ∷_) (mapList++ xs ys)
{-# REWRITE mapList++ #-}


-- A lemma helps to prove ∧rT*
fsDist : {S : Irr} {Γ : Cxt} 
  → (Φ Ψ : List Fma) (fs : List (Σ Tag (λ t₁ → Σ (Σ Fma isPos) (_∣_∣_⊢pT_ t₁ S Γ)))) (eq : Φ ++ Ψ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs)
  → Σ (List (Σ Tag (λ t₁ → Σ (Σ Fma isPos) (_∣_∣_⊢pT_ t₁ S Γ)))) (λ fs' → Σ (List (Σ Tag (λ t₁ → Σ (Σ Fma isPos) (_∣_∣_⊢pT_ t₁ S Γ)))) (λ fs'' 
    → fs ≡ fs' ++ fs'' × Φ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs' × Ψ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs''))
fsDist [] [] [] refl = [] , ([] , refl , refl , refl)
fsDist [] .(mapList (λ x₁ → pos (proj₁ (proj₂ x₁))) (x ∷ fs)) (x ∷ fs) refl = [] , ((x ∷ fs) , (refl , (refl , refl)))
fsDist (x₁ ∷ Φ) Ψ (x ∷ fs) eq with inj∷ eq
... | refl , eq1 with fsDist Φ Ψ fs eq1
... | fs' , fs'' , refl , refl , refl = x ∷ fs' , fs'' , refl , refl , refl

∧rT* : {l : List Tag} {S : Irr} {Γ : Cxt} {A : Fma}
  → {Φ : List Fma}
  → (SF : SubFmas Φ A)
  → (fs : List (Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢pT_ t S Γ))))
  → (eq1 : Φ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs)
  → (eq2 : l ≡ mapList proj₁ fs)
  → l ∣ S ∣ Γ ⊢riT A
∧rT* () [] refl refl
∧rT* (conj {Φ} {Ψ} {A' = A'} {B' = B'} SF SF₁) ((t , C , f) ∷ fs) eq1 refl with fsDist (A' ∷ Φ) (B' ∷ Ψ) ((t , C , f) ∷ fs) eq1
... | (t , .C , .f) ∷ fs' , x₁ ∷ fs'' , refl , refl , refl = ∧rT (∧rT* SF ((t , C , f) ∷ fs') refl refl) ((∧rT* SF₁ (x₁ ∷ fs'') refl refl))
∧rT* stop ((t , C , f) ∷ []) refl refl = p2riT f

⊗l-inv-all : {A B : Fma} {Γ : Cxt} (Θ : List Pos)
  → All (λ P → just (A ⊗ B) ∣ Γ ⊢li P) Θ
  → All (λ P → just A ∣ B ∷ Γ ⊢li P) Θ
⊗l-inv-all [] RS = []
⊗l-inv-all (x ∷ Θ) (⊗l f ∷ RS) = f ∷ ⊗l-inv-all Θ RS

Il-inv-all : {Γ : Cxt} (Θ : List Pos)
  → All (λ P → just I ∣ Γ ⊢li P) Θ
  → All (λ P → - ∣ Γ ⊢li P) Θ
Il-inv-all [] RS = []
Il-inv-all (x ∷ Θ) (Il f ∷ RS) = f ∷ Il-inv-all Θ RS

All-snoc : {A : Set} {P : A → Set} {xs : List A} (ps : All P xs) {x : A} (p : P x)
  → All P (xs ++ x ∷ [])
All-snoc [] p = p ∷ []
All-snoc (px ∷ ps) p = px ∷ All-snoc ps p

All-++ : {A : Set} {P : A → Set} {xs ys : List A} 
  → (ps1 : All P xs) (ps2 : All P ys)
  → All P (xs ++ ys)
All-++ [] ps2 = ps2
All-++ (px ∷ ps1) ps2 = px ∷ All-++ ps1 ps2

untagF : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
  → t ∣ S ∣ Γ ⊢fT C
  → S ∣ Γ ⊢f C
untagF ax = ax
untagF Ir = Ir
untagF (⊗rT l ok refl f g) = ⊗r l ok refl f g
untagF (∧l₁T f) = ∧l₁ f
untagF (∧l₂T f) = ∧l₂ f

untagP : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
  → t ∣ S ∣ Γ ⊢pT C
  → S ∣ Γ ⊢p C
untagP (passT f) = pass f
untagP (f2pT f) = f2p (untagF f)

untagP' :  {S : Irr} {Γ : Cxt}
  → Σ Tag (λ t → Σ Pos (λ C → t ∣ S ∣ Γ ⊢pT C)) 
  → Σ Pos (λ C → S ∣ Γ ⊢p C)
untagP' (t , A , f) = A , untagP f

pass' : {Γ : Cxt} {A : Fma}
 → Σ Pos (λ C → just A ∣ Γ ⊢li C) 
 → Σ Pos (λ C → (- , tt) ∣ A ∷ Γ ⊢p C)
pass' (C , f) = C , pass f

passT' : {Γ : Cxt} {A : Fma}
 → Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ) 
 → Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢pT_ t (- , tt) (A ∷ Γ)))
passT' (C , f) = P , (C , (passT f))

give-tag : {S : Irr} {Γ : Cxt} {C : Pos}
  → (f : S ∣ Γ ⊢f C)
  → Tag
give-tag ax = E
give-tag Ir = E
give-tag (⊗r l ok refl f g) = E
give-tag (∧l₁ f) = L
give-tag (∧l₂ f) = R

tag-seq : {S : Irr} {Γ : Cxt} {C : Pos}
  → (f : S ∣ Γ ⊢f C)
  → (give-tag f) ∣ S ∣ Γ ⊢fT C
tag-seq ax = ax
tag-seq Ir = Ir
tag-seq (⊗r l ok refl f g) = ⊗rT l ok refl f g
tag-seq (∧l₁ f) = ∧l₁T f
tag-seq (∧l₂ f) = ∧l₂T f

tag-seq-eq : {S : Irr} {Γ : Cxt} {C : Pos}
  → (f : S ∣ Γ ⊢f C)
  → f ≡ untagF (tag-seq f)
tag-seq-eq ax = refl
tag-seq-eq Ir = refl
tag-seq-eq (⊗r l ok refl f g) = refl
tag-seq-eq (∧l₁ f) = refl
tag-seq-eq (∧l₂ f) = refl

give-tag-empty : {Γ : Cxt} {C : Pos}
  → (f : (- , tt) ∣ Γ ⊢f C)
  → E ≡ give-tag f
give-tag-empty Ir = refl
give-tag-empty (⊗r l ok refl f g) = refl

give-tag-At : {X : At} {Γ : Cxt} {C : Pos}
  → (f : (just (` X) , tt) ∣ Γ ⊢f C)
  → (eq : Γ ≡ [])
  → E ≡ give-tag f
give-tag-At ax refl = refl
give-tag-At (⊗r l {Γ = []} ok refl f g) refl = refl
p2li' : {S : Irr} {Γ : Cxt}
  → Σ Pos (λ C → S ∣ Γ ⊢p C) 
  → Σ Pos (λ C → irr S ∣ Γ ⊢li C)
p2li' (C , f) = (C , p2li f)

f2pT' : {S : Irr} {Γ : Cxt}
  → Σ Tag (λ t → Σ Pos (λ C → t ∣ S ∣ Γ ⊢fT C))
  → Σ Tag (λ t → Σ Pos (λ C → t ∣ S ∣ Γ ⊢pT C))
f2pT' (t , C , f) = t , C , f2pT f

f2p' : {S : Irr} {Γ : Cxt}
  → Σ Pos (λ C → S ∣ Γ ⊢f C)
  → Σ Pos (λ C → S ∣ Γ ⊢p C)
f2p' (C , f) = C , f2p f

∧l₁' : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just A ∣ Γ ⊢li C)
  → Σ Pos (λ C → (just (A ∧ B) , _) ∣ Γ ⊢f C)
∧l₁' (C , f) = C , ∧l₁ f

∧l₂' : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just B ∣ Γ ⊢li C)
  → Σ Pos (λ C → (just (A ∧ B) , _) ∣ Γ ⊢f C)
∧l₂' (C , f) = C , ∧l₂ f

∧l₁T' : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just A ∣ Γ ⊢li C)
  → Σ Tag (λ t → Σ Pos (λ C → t ∣ (just (A ∧ B) , _) ∣ Γ ⊢fT C))
∧l₁T' (C , f) = L , (C , (∧l₁T f))

∧l₂T' : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just B ∣ Γ ⊢li C)
  → Σ Tag (λ t → Σ Pos (λ C → t ∣ (just (A ∧ B) , _) ∣ Γ ⊢fT C))
∧l₂T' (C , f) = R , (C , (∧l₂T f))

-- All-pass? : {Γ : Cxt} {A : Fma}
--   → (fs : List (Σ Pos (λ C → - ∣ A ∷ Γ ⊢li C)))
--   → (Σ (List (Σ Pos (λ C → just A ∣ Γ ⊢li C))) (λ fs' → fs ≡ mapList (λ x → p2li' (pass' x)) fs'))
--      ⊎
--     (Σ (List (Σ Tag (λ t → Σ Pos (λ C → t ∣ (- , _) ∣ A ∷ Γ ⊢pT C)))) (λ fs' → fs ≡ mapList (λ x → p2li' (untagP' x)) fs' × isOK (mapList proj₁ fs')))
-- All-pass? [] = inj₁ ([] , refl)
-- All-pass? ((C , p2li f) ∷ fs) with All-pass? fs
-- All-pass? ((C , p2li (pass f)) ∷ ._) | inj₁ (fs' , refl) = inj₁ (((C , f) ∷ fs') , refl)
-- All-pass? ((C , p2li (f2p f)) ∷ ._) | inj₁ (fs' , refl) = inj₂ (((give-tag f , C , f2pT (tag-seq f)) ∷ mapList passT' fs') , (cong₂ _∷_ (cong (λ x → C , p2li (f2p x)) (tag-seq-eq f)) (map-compose fs') , isOKeq (cong (λ x → x ∷ mapList proj₁ (mapList passT' fs')) (give-tag-empty f)) tt))
-- All-pass? ((C , p2li (pass f)) ∷ ._) | inj₂ (fs' , refl , ok) = inj₂ (((P , (C , (passT f))) ∷ fs') , (refl , ok))
-- All-pass? ((C , p2li (f2p f)) ∷ ._) | inj₂ (fs' , refl , ok) = inj₂ (((give-tag f) , (C , (f2pT (tag-seq f)))) ∷ fs' , (cong₂ _∷_ (cong (λ x → C , p2li (f2p x)) (tag-seq-eq f)) refl , isOKeq (cong (λ x → x ∷ mapList proj₁ fs') (give-tag-empty f)) tt))

⊗l-inv-fs : {A B : Fma} {Γ : Cxt}
  → List (Σ Pos (λ P → just (A ⊗ B) ∣ Γ ⊢li P))
  → List (Σ Pos (λ P → just A ∣ B ∷ Γ ⊢li P))
⊗l-inv-fs [] = []
⊗l-inv-fs ((C , ⊗l f) ∷ fs) = (C , f) ∷ ⊗l-inv-fs fs

Il-inv-fs : {Γ : Cxt}
  → List (Σ Pos (λ P → just I ∣ Γ ⊢li P))
  → List (Σ Pos (λ P → - ∣ Γ ⊢li P))
Il-inv-fs [] = []
Il-inv-fs ((C , Il f) ∷ fs) = (C , f) ∷ Il-inv-fs fs

⊗l-inv-fs-eq : {A' B' : Fma} {Γ : Cxt}
  → (fs : List (Σ Pos (λ C → just (A' ⊗ B') ∣ Γ ⊢li C)))
  → mapList (λ x → pos (proj₁ x)) fs ≡ mapList (λ x → pos (proj₁ x)) (⊗l-inv-fs fs)
⊗l-inv-fs-eq [] = refl
⊗l-inv-fs-eq ((C , ⊗l f) ∷ fs) = cong (pos C ∷_) (⊗l-inv-fs-eq fs)

Il-inv-fs-eq : {Γ : Cxt}
  → (fs : List (Σ Pos (λ C → just I ∣ Γ ⊢li C)))
  → mapList (λ x → pos (proj₁ x)) fs ≡ mapList (λ x → pos (proj₁ x)) (Il-inv-fs fs)
Il-inv-fs-eq [] = refl
Il-inv-fs-eq ((C , Il f) ∷ fs) = cong (pos C ∷_) (Il-inv-fs-eq fs)

p2li-pass-fs-eq : {A : Fma} {Γ : Cxt}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList (λ x → pos (proj₁ x)) (mapList (λ x → proj₁ x , p2li (pass (proj₂ x))) fs) ≡ mapList (λ x → pos (proj₁ x)) fs
p2li-pass-fs-eq [] = refl
p2li-pass-fs-eq ((C , f) ∷ fs) = cong (pos C ∷_) (p2li-pass-fs-eq fs)

p2li-f2p-∧l₁-fs-eq : {A B : Fma} {Γ : Cxt}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList (λ x → proj₁ (proj₁ x)) (mapList (λ x → proj₁ x , p2li (f2p (∧l₁ {B = B} (proj₂ x)))) fs) ≡ mapList (λ x → pos (proj₁ x)) fs
p2li-f2p-∧l₁-fs-eq [] = refl
p2li-f2p-∧l₁-fs-eq (x ∷ fs) = cong (proj₁ (proj₁ x) ∷_) (p2li-f2p-∧l₁-fs-eq fs)

p2li-f2p-∧l₂-fs-eq : {A B : Fma} {Γ : Cxt}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just B) Γ)))
  → mapList (λ x → proj₁ (proj₁ x)) (mapList (λ x → proj₁ x , p2li (f2p (∧l₂ {A = A} (proj₂ x)))) fs) ≡ mapList (λ x → pos (proj₁ x)) fs
p2li-f2p-∧l₂-fs-eq [] = refl
p2li-f2p-∧l₂-fs-eq (x ∷ fs) = cong (proj₁ (proj₁ x) ∷_) (p2li-f2p-∧l₂-fs-eq fs)

irr-eq : (S : Stp) (p : isIrr S) → irr (S , p) ≡ S
irr-eq (just (` x)) tt = refl
irr-eq (just (x ∧ x₁)) tt = refl
irr-eq - tt = refl

isIrr-unique : (S : Stp) (p q : isIrr S) → p ≡ q 
isIrr-unique (just (` x)) p q = refl
isIrr-unique (just (x ∧ x₁)) p q = refl
isIrr-unique - p q = refl

check-focus : {S : Irr} {Γ : Cxt}
  → (f : Σ Pos (λ C → irr S ∣ Γ ⊢li C))
  → (fs : List (Σ Pos (λ C → irr S ∣ Γ ⊢li C)))
  → (Σ Fma (λ A → Σ Fma (λ B → (Σ (List (Σ Pos (λ C → just A ∣ Γ ⊢li C))) (λ fs' → Σ (irr S ≡ just (A ∧ B)) (λ eq →
      subst (λ x → List (Σ Pos (λ C → x ∣ Γ ⊢li C))) eq (f ∷ fs) ≡ mapList (λ x → p2li' (f2p' (∧l₁' {B = B} x))) fs')))))
    ⊎
    Σ Fma (λ A → Σ Fma (λ B → (Σ (List (Σ Pos (λ C → just B ∣ Γ ⊢li C))) (λ fs' → Σ (irr S ≡ just (A ∧ B)) (λ eq →
      subst (λ x → List (Σ Pos (λ C → x ∣ Γ ⊢li C))) eq (f ∷ fs) ≡ mapList (λ x → p2li' (f2p' (∧l₂' {A = A} x))) fs')))))
    ⊎ 
    Σ Fma (λ A → Σ Cxt (λ Γ' → Σ (List (Σ Pos (λ C → just A ∣ Γ' ⊢li C))) (λ fs' → Σ (irr S ≡ -) (λ eq1 → Σ (Γ ≡ A ∷ Γ') (λ eq2 
      → subst₂ (λ x → λ y → List (Σ Pos (λ C → x ∣ y ⊢li C))) eq1 eq2 (f ∷ fs) ≡ mapList (λ x → p2li' (pass' x)) fs'))))))
    ⊎
    (Σ (List (Σ Tag (λ t → Σ Pos (λ C → t ∣ S ∣ Γ ⊢pT C)))) (λ fs' → f ∷ fs ≡ mapList (λ x → p2li' (untagP' x)) fs' × isOK (mapList proj₁ fs')))
check-focus (C , p2li (pass {Γ = Γ} {A}  f)) [] = inj₁ (inj₂ (inj₂ (A , (Γ , ((C , f) ∷ []) , (refl , (refl , refl))))))
check-focus (.(` X , tt) , p2li (f2p (ax {X}))) [] = inj₂ (((E , ((` X , tt) , f2pT ax)) ∷ []) , refl , tt)
check-focus (.(I , tt) , p2li (f2p Ir)) [] = inj₂ (((E , ((I , tt) , (f2pT Ir))) ∷ []) , (refl , tt))
check-focus {S , q} (.(A ⊗ B , tt) , p2li {.(irr (S , q)) , p} (f2p (⊗r l {A = A} {B} ok refl f g))) [] 
  rewrite irr-eq S p | isIrr-unique S p q = inj₂ (((E , ((A ⊗ B , tt) , f2pT (⊗rT l ok refl f g))) ∷ []) , refl , tt)
check-focus (C , p2li (f2p (∧l₁ {A = A} {B} f))) [] = inj₁ (inj₁ (A , B , (((C , f) ∷ []) , (refl , refl))))
check-focus (C , p2li (f2p (∧l₂ {A = A} {B} f))) [] = inj₁ (inj₂ (inj₁ (A , (B , (((C , f) ∷ []) , (refl , refl))))))
check-focus (C , p2li (pass f)) (f' ∷ fs) with check-focus f' fs
... | inj₁ (inj₂ (inj₂ (A , Γ' , x ∷ fs' , refl , refl , refl))) = inj₁ (inj₂ (inj₂ (A , (Γ' , (((C , f) ∷ x ∷ fs') , (refl , (refl , refl)))))))
... | inj₂ (fs' , eq , ok) = inj₂ (((P , (C , (passT f))) ∷ fs') , (cong ((C , p2li (pass f)) ∷_) eq , ok))
check-focus (.(` X , tt) , p2li (f2p (ax {X}))) (f' ∷ fs) with check-focus f' fs
... | inj₁ (inj₂ (inj₁ ()))
... | inj₁ (inj₂ (inj₂ ()))
... | inj₂ (fs' , eq , ok) = inj₂ (((E , ((` X , tt) , (f2pT ax))) ∷ fs') , (cong (((` X , tt) , p2li (f2p ax)) ∷_) eq) , tt)
check-focus (.(I , tt) , p2li (f2p Ir)) (f' ∷ fs) with check-focus f' fs
... | inj₁ (inj₂ (inj₁ ()))
... | inj₁ (inj₂ (inj₂ ()))
... | inj₂ (fs' , eq , ok) = inj₂ (((E , ((I , tt) , (f2pT Ir))) ∷ fs') , (cong (((I , tt) , p2li (f2p Ir)) ∷_) eq , tt))
check-focus {S} (.(A ⊗ B , tt) , p2li (f2p (⊗r l {A = A} {B} ok refl f g))) (f' ∷ fs) with check-focus {S} f' fs
... | inj₁ (inj₁ (A' , B' , fs' , refl , eq2)) = inj₂ ((E , ((A ⊗ B , tt) , (f2pT (⊗rT l ok refl f g)))) ∷ mapList (λ x → f2pT' (∧l₁T' x)) fs' , (cong (((A ⊗ B , tt) , p2li (f2p (⊗r l ok refl f g))) ∷_) (trans eq2 (map-compose fs'))) , tt) 
... | inj₁ (inj₂ (inj₁ (A' , B' , fs' , refl , eq2))) = inj₂ ((E , ((A ⊗ B , tt) , (f2pT (⊗rT l ok refl f g)))) ∷ mapList (λ x → f2pT' (∧l₂T' x)) fs' , (cong (((A ⊗ B , tt) , p2li (f2p (⊗r l ok refl f g))) ∷_) (trans eq2 (map-compose fs'))) , tt)
check-focus {.- , snd} (.(A ⊗ B , tt) , p2li (f2p (⊗r l {Γ = []} {A = A} {B} ok refl f g))) (f' ∷ fs) | inj₁ (inj₂ (inj₂ (A' , Γ' , fs' , refl , refl , eq3))) = 
  inj₂ (((E , ((A ⊗ B , tt) , (f2pT (⊗rT l ok refl f g)))) ∷ mapList passT' fs') , ((cong (((A ⊗ B , tt) , p2li (f2p (⊗r l ok refl f g))) ∷_) (trans eq3 (map-compose fs'))) , tt))
check-focus {.- , snd} (.(A ⊗ B , tt) , p2li (f2p (⊗r l {Γ = x ∷ Γ} {Δ} {A = A} {B} ok refl f g))) (f' ∷ fs) | inj₁ (inj₂ (inj₂ (.x , .(Γ ++ Δ) , fs' , refl , refl , eq3))) = 
  inj₂ (((E , ((A ⊗ B , tt) , (f2pT (⊗rT l ok refl f g)))) ∷ mapList passT' fs') , ((cong (((A ⊗ B , tt) , p2li (f2p (⊗r l ok refl f g))) ∷_) (trans eq3 (map-compose fs'))) , tt))
check-focus {just (` x) , snd} (.(A ⊗ B , tt) , p2li (f2p (⊗r l {A = A} {B} ok refl f g))) (f' ∷ fs) | inj₂ (fs' , eq , ok') = 
  inj₂ (((E , ((A ⊗ B , tt) , (f2pT (⊗rT l ok refl f g)))) ∷ fs') , (cong (((A ⊗ B , tt) , p2li (f2p (⊗r l ok refl f g))) ∷_) eq) , tt)
check-focus {just (x ∧ x₁) , snd} (.(A ⊗ B , tt) , p2li (f2p (⊗r l {A = A} {B} ok refl f g))) (f' ∷ fs) | inj₂ (fs' , eq , ok') = 
  inj₂ (((E , ((A ⊗ B , tt) , (f2pT (⊗rT l ok refl f g)))) ∷ fs') , (cong (((A ⊗ B , tt) , p2li (f2p (⊗r l ok refl f g))) ∷_) eq) , tt)
check-focus { - , snd} (.(A ⊗ B , tt) , p2li (f2p (⊗r l {A = A} {B} ok refl f g))) (f' ∷ fs) | inj₂ (fs' , eq , ok') = 
  inj₂ (((E , ((A ⊗ B , tt) , (f2pT (⊗rT l ok refl f g)))) ∷ fs') , (cong (((A ⊗ B , tt) , p2li (f2p (⊗r l ok refl f g))) ∷_) eq) , tt)
check-focus (C , p2li (f2p (∧l₁ f))) (f' ∷ fs) with check-focus f' fs
... | inj₁ (inj₁ (A , B , fs' , refl , eq2)) = inj₁ (inj₁ (A , B , (C , f) ∷ fs' , refl , cong ((C , p2li (f2p (∧l₁ f))) ∷_) eq2))
... | inj₁ (inj₂ (inj₁ (A , B , x ∷ fs' , refl , eq2))) = inj₂ (((L , (C , (f2pT (∧l₁T f)))) ∷ mapList (λ x → f2pT' (∧l₂T' x)) (x ∷ fs')) , ((cong ((C , p2li (f2p (∧l₁ f))) ∷_) (trans eq2 (map-compose (x ∷ fs')))) , tt))
check-focus (C , p2li (f2p (∧l₁ f))) (f' ∷ fs) | inj₂ ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l {A = A} {B} ok₁ refl f₁ g)) ∷ fs' , eq , ok) = 
  inj₂ (((L , (C , (f2pT (∧l₁T f)))) ∷ (E , (A ⊗ B , tt) , f2pT (⊗rT l {A = A} {B} ok₁ refl f₁ g)) ∷ fs') , (cong ((C , p2li (f2p (∧l₁ f))) ∷_) eq , tt))
... | inj₂ ((.L , C' , f2pT (∧l₁T f₁)) ∷ fs' , eq , ok) = 
  inj₂ (((L , (C , (f2pT (∧l₁T f)))) ∷ (L , C' , f2pT (∧l₁T f₁)) ∷ fs') , (cong ((C , p2li (f2p (∧l₁ f))) ∷_) eq , ok))
... | inj₂ ((.R , C' , f2pT (∧l₂T f₁)) ∷ fs' , eq , ok) = 
  inj₂ (((L , (C , (f2pT (∧l₁T f)))) ∷ (R , C' , f2pT (∧l₂T f₁)) ∷ fs') , (cong ((C , p2li (f2p (∧l₁ f))) ∷_) eq , tt))
check-focus (C , p2li (f2p (∧l₂ f))) (f' ∷ fs) with check-focus f' fs
... | inj₁ (inj₁ (A , B , x ∷ fs' , refl , eq2)) = inj₂ (((R , (C , (f2pT (∧l₂T f)))) ∷ mapList (λ x → f2pT' (∧l₁T' x)) (x ∷ fs')) , (cong ((C , p2li (f2p (∧l₂ f))) ∷_) (trans eq2 (map-compose (x ∷ fs'))) , tt))
... | inj₁ (inj₂ (inj₁ (A , B , fs' , refl , eq2))) = inj₁ (inj₂ (inj₁ (A , B , (C , f) ∷ fs' , refl , cong ((C , p2li (f2p (∧l₂ f))) ∷_) eq2)))
check-focus (C , p2li (f2p (∧l₂ f))) (f' ∷ fs) | inj₂ ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l {A = A} {B} ok₁ refl f₁ g)) ∷ fs' , eq , ok) = 
  inj₂ (((R , (C , (f2pT (∧l₂T f)))) ∷ (E , (A ⊗ B , tt) , f2pT (⊗rT l {A = A} {B} ok₁ refl f₁ g)) ∷ fs') , (cong ((C , p2li (f2p (∧l₂ f))) ∷_) eq , tt))
... | inj₂ ((.L , C' , f2pT (∧l₁T f₁)) ∷ fs' , eq , ok) = 
  inj₂ (((R , (C , (f2pT (∧l₂T f)))) ∷ (L , C' , f2pT (∧l₁T f₁)) ∷ fs') , (cong ((C , p2li (f2p (∧l₂ f))) ∷_) eq , tt))
... | inj₂ ((.R , C' , f2pT (∧l₂T f₁)) ∷ fs' , eq , ok) = 
  inj₂ (((R , (C , (f2pT (∧l₂T f)))) ∷ (R , C' , f2pT (∧l₂T f₁)) ∷ fs') , (cong ((C , p2li (f2p (∧l₂ f))) ∷_) eq , ok))



gen⊗r-li : {S : Stp} {Γ Δ : Cxt} {A B : Fma} {C : Pos}
  → (f : S ∣ Γ ⊢li C)
  → (fs : List (Σ Pos (λ C → S ∣ Γ ⊢li C)))
  → SubFmas (pos C ∷ mapList (λ x → pos (proj₁ x)) fs) A
  → - ∣ Δ ⊢ri B
  → S ∣ Γ ++ Δ ⊢li (A ⊗ B , _)
gen⊗r-li (⊗l f) fs RS g rewrite ⊗l-inv-fs-eq fs = ⊗l (gen⊗r-li f (⊗l-inv-fs fs) RS g)
gen⊗r-li (Il f) fs RS g rewrite Il-inv-fs-eq fs = Il (gen⊗r-li f (Il-inv-fs fs) RS g)
gen⊗r-li {C = C} (p2li (pass f)) fs RS g with check-focus (C , p2li (pass f)) fs
... | inj₁ (inj₂ (inj₂ (A' , Γ' , (C , f) ∷ fs' , refl , refl , refl))) 
  rewrite p2li-pass-fs-eq fs' = p2li (pass (gen⊗r-li f fs' RS g))
gen⊗r-li {C = .C'} (p2li (pass f)) .(mapList (λ x → proj₁ (proj₂ x) , p2li (untagP (proj₂ (proj₂ x)))) fs') RS g | inj₂ ((.P , C' , passT .f) ∷ fs' , refl , ok) = 
  p2li (f2p (⊗r (P ∷ mapList proj₁ fs') ok refl (∧rT* RS ((P , C' , passT f) ∷ fs') (cong (pos C' ∷_) (sym (map-compose fs'))) refl) g))
gen⊗r-li (p2li (f2p (ax {X}))) fs RS g with check-focus ((` X , tt) , p2li (f2p (ax))) fs
... | inj₁ (inj₂ (inj₁ ()))
... | inj₁ (inj₂ (inj₂ ()))
... | inj₂ ((.E , (` X , tt) , f2pT ax) ∷ fs' , refl , ok) = 
  p2li (f2p (⊗r (E ∷ mapList proj₁ fs') tt refl (∧rT* RS ((E , (` X , tt) , f2pT ax) ∷ fs') (cong (` X ∷_) (sym (map-compose fs'))) refl) g))
gen⊗r-li (p2li (f2p Ir)) fs RS g with check-focus ((I , tt) , p2li (f2p Ir)) fs
... | inj₁ (inj₂ (inj₁ ()))
... | inj₁ (inj₂ (inj₂ ()))
... | inj₂ ((.E , (I , tt) , f2pT Ir) ∷ fs' , refl , ok) = 
  p2li (f2p (⊗r (E ∷ mapList proj₁ fs') tt refl (∧rT* RS ((E , (I , tt) , f2pT Ir) ∷ fs') (cong (I ∷_) (sym (map-compose fs'))) refl) g))
gen⊗r-li (p2li (f2p (⊗r l {S = S} {A = A} {B} ok eq f g₁))) fs RS g with check-focus {S = S} ((A ⊗ B , tt) , (p2li (f2p (⊗r l {A = A} {B} ok eq f g₁)))) fs
... | inj₁ (inj₁ (A' , B' , [] , refl , ()))
... | inj₁ (inj₁ (A' , B' , x ∷ fs' , refl , ()))
... | inj₁ (inj₂ (inj₁ (A' , B' , [] , refl , ())))
... | inj₁ (inj₂ (inj₁ (A' , B' , x ∷ fs' , refl , ())))
gen⊗r-li (p2li (f2p (⊗r l {_} {[]} {A = _} {_} ok refl f g₁))) fs RS g | inj₁ (inj₂ (inj₂ (A' , Γ' , [] , refl , refl , ())))
gen⊗r-li (p2li (f2p (⊗r l {_} {[]} {A = _} {_} ok refl f g₁))) fs RS g | inj₁ (inj₂ (inj₂ (A' , Γ' , x ∷ fs' , refl , refl , ())))
gen⊗r-li (p2li (f2p (⊗r l {_} {x ∷ Γ} {Δ} {_} {_} ok refl f g₁))) fs RS g | inj₁ (inj₂ (inj₂ (.x , .(Γ ++ Δ) , [] , refl , refl , ())))
gen⊗r-li (p2li (f2p (⊗r l {_} {x ∷ Γ} {Δ} {_} {_} ok refl f g₁))) fs RS g | inj₁ (inj₂ (inj₂ (.x , .(Γ ++ Δ) , x₁ ∷ fs' , refl , refl , ())))
gen⊗r-li (p2li {S , snd} (f2p (⊗r l {S , snd} {Γ = []} {A = A} {B} ok refl f g₁))) .(mapList (λ x → proj₁ (proj₂ x) , p2li (untagP (proj₂ (proj₂ x)))) fs') RS g | inj₂ ((.E , .(A ⊗ B , tt) , f2pT (⊗rT .l .ok refl .f .g₁)) ∷ fs' , refl , ok') = 
  p2li (f2p (⊗r (E ∷ (mapList proj₁ fs')) tt refl (∧rT* RS ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok refl f g₁)) ∷ fs') (cong (A ⊗ B ∷_) (sym (map-compose fs'))) refl) g))
gen⊗r-li (p2li {S , snd} (f2p (⊗r l {S , snd} {Γ = x ∷ Γ} {A = A} {B} ok .refl f g₁))) .(mapList (λ x₁ → proj₁ (proj₂ x₁) , p2li (untagP (proj₂ (proj₂ x₁)))) fs') RS g | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT .l .ok refl .f .g₁)) ∷ fs' , refl , ok') = 
  p2li (f2p (⊗r (E ∷ (mapList proj₁ fs')) tt refl (∧rT* RS ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok refl f g₁)) ∷ fs') (cong (A ⊗ B ∷_) (sym (map-compose fs'))) refl) g))
gen⊗r-li {C = C} (p2li (f2p (∧l₁ f))) fs RS g with check-focus (C , (p2li (f2p (∧l₁ f)))) fs
... | inj₁ (inj₁ (A , B , (C' , .f) ∷ fs' , refl , refl)) 
  rewrite p2li-f2p-∧l₁-fs-eq {B = B} fs' = p2li (f2p (∧l₁ (gen⊗r-li f fs' RS g)))
... | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq))) with inj∷ eq
... | () , eq2
gen⊗r-li {C = C} (p2li (f2p (∧l₁ f))) fs RS g | inj₂ ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l {A = A} {B} ok₁ refl f₁ g₁)) ∷ fs' , () , ok)
gen⊗r-li {C = .C'} (p2li (f2p (∧l₁ f))) .(mapList (λ x → proj₁ (proj₂ x) , p2li (untagP (proj₂ (proj₂ x)))) fs') RS g | inj₂ ((.L , C' , f2pT (∧l₁T .f)) ∷ fs' , refl , ok) = 
  p2li (f2p (⊗r (L ∷ (mapList proj₁ fs')) ok refl (∧rT* RS ((L , C' , f2pT (∧l₁T f)) ∷ fs') (cong (pos C' ∷_) (sym (map-compose fs'))) refl) g))
gen⊗r-li {C = C} (p2li (f2p (∧l₂ f))) fs RS g with check-focus (C , (p2li (f2p (∧l₂ f)))) fs
... | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq)) with inj∷ eq
... | () , eq2
gen⊗r-li {C = C} (p2li (f2p (∧l₂ f))) fs RS g | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , refl))) 
  rewrite p2li-f2p-∧l₂-fs-eq {A = A} fs' = p2li (f2p (∧l₂ (gen⊗r-li f fs' RS g)))
gen⊗r-li {C = C} (p2li (f2p (∧l₂ f))) fs RS g | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f₁ g₁)) ∷ fs' , () , ok)
gen⊗r-li {C = .C'} (p2li (f2p (∧l₂ f))) .(mapList (λ x → proj₁ (proj₂ x) , p2li (untagP (proj₂ (proj₂ x)))) fs') RS g | inj₂ ((.R , C' , f2pT (∧l₂T .f)) ∷ fs' , refl , ok) = 
  p2li (f2p (⊗r (R ∷ (mapList proj₁ fs')) ok refl (∧rT* RS ((R , C' , f2pT (∧l₂T f)) ∷ fs') (cong (pos C' ∷_) (sym (map-compose fs'))) refl) g))
   