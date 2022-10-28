{-# OPTIONS --rewriting #-}

module IsInter where

open import Data.List renaming (map to mapList; fromMaybe to backlist)
open import Data.List.Relation.Unary.Any
open import Data.List.Properties
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Data.Product
open import Data.Sum 
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities 

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

[]left' : {A : Set} → (xs : List A) → isInter [] xs xs
[]left' [] = isInter[]
[]left' (x ∷ xs) = []left

∷left' : {A : Set} → {x : A} → {xs zs : List A} → (ys : List A) → isInter xs ys zs → isInter (x ∷ xs) ys (x ∷ zs)
∷left' [] eq with isInter-left[] eq
... | refl = []right
∷left' (x ∷ ys) eq = ∷left eq


∷right' : {A : Set} → {x : A} → {ys zs : List A} → (xs : List A) → isInter xs ys zs → isInter xs (x ∷ ys) (x ∷ zs)
∷right' [] eq with isInter-right[] eq
... | refl = []left
∷right' (x ∷ xs) eq = ∷right eq


isInter++r : {X : Set} → {xs' ys' zs' : List X} → (ys : List X) → isInter xs' ys' zs' → isInter (xs') (ys ++ ys') (ys ++ zs')
isInter++r [] eq = eq
isInter++r {xs' = []} (x ∷ ys) eq with isInter-right[] eq
... | refl = []left
isInter++r {xs' = x₁ ∷ xs'} (x ∷ ys) eq = ∷right (isInter++r ys eq)

isInter++l : {X : Set} → {xs' ys' zs' : List X} → (ys : List X) → isInter xs' ys' zs' → isInter (ys ++ xs') (ys') (ys ++ zs')
-- isInter++l [] inTeq = inTeq
-- isInter++l {ys' = ys'} (x ∷ ys) inTeq = ∷left' ys' (isInter++l ys inTeq)
isInter++l [] inTeq = inTeq
isInter++l {ys' = []} (x ∷ ys) isInter[] = []right
isInter++l {ys' = []} (x ∷ ys) []right = []right
-- with isInter-left[] inTeq
-- ... | refl = []right
isInter++l {ys' = x₁ ∷ ys'} (x ∷ ys) inTeq = ∷left (isInter++l ys inTeq)

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
isInter++ ([]right {x} {xs}) eq' = isInter++l (x ∷ xs) eq'
isInter++ (∷left eq) eq' = ∷left (isInter++ eq eq')
isInter++ (∷right eq) eq' = ∷right (isInter++ eq eq')


[]++ : {X : Set} → {xs ys : List X} → [] ≡ xs ++ ys → xs ≡ [] × ys ≡ []
[]++ {xs = xs} {ys} eq = ++-conicalˡ xs ys (sym eq) , ++-conicalʳ xs ys (sym eq)

isInter++? : {X : Set} → {xs ys zs : List X} → (zs₀ zs₁ : List X) (eq : zs ≡ zs₀ ++ zs₁)  (inTeq : isInter xs ys zs) → 
                         Σ (List X) (λ xs₀ → Σ (List X) (λ xs₁ → Σ (List X) (λ ys₀ → Σ (List X) (λ ys₁ →
                           Σ (isInter xs₀ ys₀ zs₀) λ inTeq1 → Σ (isInter xs₁ ys₁ zs₁) λ inTeq2 →
                             Σ (xs ≡ xs₀ ++ xs₁) λ eq1 → Σ (ys ≡ ys₀ ++ ys₁) λ eq2 →
                               subst (isInter (xs₀ ++ xs₁) (ys₀ ++ ys₁)) eq (subst₂ (λ a b → isInter a b zs) eq1 eq2 inTeq) ≡ isInter++ inTeq1 inTeq2))))
isInter++? zs₀ zs₁ eq isInter[] with []++ {xs = zs₀} {zs₁} eq
isInter++? .[] .[] refl isInter[] | refl , refl = [] , [] , [] , [] , isInter[] , isInter[] , refl , refl , refl
isInter++? [] (x ∷ zs₁) refl []left = [] , [] , [] , (x ∷ zs₁) , isInter[] , []left , refl , refl , refl
isInter++? (x ∷ zs₀) [] refl []left = []  , [] , (x ∷ zs₀) , [] , []left , isInter[] , refl , refl , refl
isInter++? (x ∷ zs₀) (x₁ ∷ zs₁) refl []left = []  , [] , (x ∷ zs₀) , (x₁ ∷ zs₁) , []left , []left , refl , refl , refl
isInter++? [] (x ∷ zs₁) refl []right = [] , (x ∷ zs₁)  , [] , [] , isInter[] , []right , refl , refl , refl
isInter++? (x ∷ zs₀) [] refl []right = (x ∷ zs₀) , [] , [] , [] , []right , isInter[] , refl , refl , refl
isInter++? (x ∷ zs₀) (x₁ ∷ zs₁) refl []right = (x ∷ zs₀) , (x₁ ∷ zs₁) , [] , [] , []right , []right , refl , refl , refl
isInter++? [] (x ∷ zs₁) refl (∷left {y = y} {xs} {ys = ys} inTeq) = [] , (x ∷ xs) , [] , (y ∷ ys) , isInter[] , ∷left inTeq , refl , refl , refl
isInter++? (x ∷ zs₀) zs₁ refl (∷left inTeq)  with isInter++? zs₀ zs₁ refl inTeq
... | .[] , xs₁' , [] , .(_ ∷ _) , isInter[] , inTeq'' , refl , refl , refl = (x ∷ []) , xs₁' , [] , _ , []right , inTeq'' , refl , refl , refl
... | .(_ ∷ _) , xs₁' , [] , .(_ ∷ _) , []right , inTeq'' , refl , refl , refl = _ , _ , [] , _ , []right , inTeq'' , refl , refl , refl
... | xs₀' , xs₁' , x₁ ∷ ys₀' , ys₁' , inTeq' , inTeq'' , refl , refl , refl = x ∷ xs₀' , xs₁' , x₁ ∷ ys₀' , ys₁' , ∷left inTeq' , inTeq'' , refl , refl , refl
isInter++? [] (x ∷ zs₁) refl (∷right {x₁} {xs = xs} {ys} inTeq) = [] , (x₁ ∷ xs) , [] , (x ∷ ys) , isInter[] , ∷right inTeq , refl , refl , refl
isInter++? (x ∷ zs₀) zs₁ refl (∷right inTeq) with isInter++? zs₀ zs₁ refl inTeq
... | [] , .(_ ∷ _) , .[] , ys₁' , isInter[] , inTeq'' , refl , refl , refl = _ , _ , _ , _ , []left , inTeq'' , refl , refl , refl
... | [] , .(_ ∷ _) , .(_ ∷ _) , ys₁' , []left , inTeq'' , refl , refl , refl = _ , _ , _ , _ , []left , inTeq'' , refl , refl , refl
... | x₁ ∷ xs₀' , xs₁' , ys₀' , ys₁' , inTeq' , inTeq'' , refl , refl , refl = x₁ ∷ xs₀' , xs₁' , x ∷ ys₀' , ys₁' , ∷right inTeq' , inTeq'' , refl , refl , refl

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


empty↭' : {A : Set} → {xs : List A} → [] ↭' xs → xs ≡ []
empty↭' (empty x) = refl
empty↭' (cons {xs₀ = xs₀} x peq) = ⊥-elim ([]disj∷ xs₀ x)



[]++? : {X : Set} → {xs ys : List X} → [] ≡ xs ++ ys → xs ≡ [] × ys ≡ []
[]++? {xs = []} {[]} eq = refl , refl


isInter++-++l-refl : {X : Set} → {xs : List X} → {xs₁ ys₁ zs₁ : List X} 
  → (inTeq : isInter xs [] xs) → (inTeq2 : isInter xs₁ ys₁ zs₁) 
  → isInter++l xs inTeq2 ≡ isInter++ inTeq inTeq2
isInter++-++l-refl isInter[] inTeq2 = refl
isInter++-++l-refl []right inTeq2 = refl

isInter++-∷left' : {X : Set} → {x : X} → (ys : List X) → {xs zs xs1 ys1 zs1 : List X} → (inTeq : isInter xs ys zs) → (inTeq2 : isInter xs1 ys1 zs1)
  → ∷left' (ys ++ ys1) (isInter++ inTeq inTeq2) ≡ isInter++ (∷left' {x = x} ys inTeq) inTeq2
isInter++-∷left' [] inTeq inTeq2 with isInter-left[] inTeq
isInter++-∷left' [] inTeq isInter[] | refl with isInter-left[] (isInter++ inTeq isInter[])
... | refl = refl
isInter++-∷left' [] inTeq ([]left {x = x} {xs = xs}) | refl 
  rewrite isInter++-++l-refl inTeq ([]left {x = x} {xs = xs}) = refl
isInter++-∷left' [] inTeq ([]right {x = x} {xs = xs}) | refl with isInter-left[] (isInter++ inTeq ([]right {x = x} {xs = xs}))
... | refl = refl
isInter++-∷left' [] inTeq (∷left {x = x} inTeq2) | refl 
  rewrite isInter++-++l-refl inTeq (∷left {x = x} inTeq2) = refl
isInter++-∷left' [] {xs = xs} inTeq (∷right {y = y} inTeq2) | refl 
  rewrite isInter++-++l-refl inTeq (∷right {y = y} inTeq2) = refl
isInter++-∷left' (x ∷ ys) inTeq inTeq2 = refl



isInter++-++r-refl : {X : Set} → {xs : List X} → {xs₁ ys₁ zs₁ : List X}
   → (inTeq : isInter [] xs xs) → (inTeq2 : isInter xs₁ ys₁ zs₁) 
   → isInter++r xs inTeq2 ≡ isInter++ inTeq inTeq2
isInter++-++r-refl isInter[] inTeq2 = refl
isInter++-++r-refl []left inTeq2 = refl

isInter++-∷right' : {X : Set} → {x : X} → (xs : List X) → {ys zs xs1 ys1 zs1 : List X} → (inTeq : isInter xs ys zs) → (inTeq2 : isInter xs1 ys1 zs1)
  → isInter++ (∷right' {x = x} xs inTeq) inTeq2 ≡ ∷right' (xs ++ xs1) (isInter++ inTeq inTeq2)
isInter++-∷right' [] inTeq inTeq2 with isInter-right[] inTeq
isInter++-∷right' [] inTeq isInter[] | refl with isInter-right[] (isInter++ inTeq isInter[])
... | refl = refl
isInter++-∷right' [] inTeq ([]left {x = x} {xs = xs}) | refl with isInter-right[] (isInter++ inTeq ([]left {x = x} {xs = xs}))
... | refl = refl
isInter++-∷right' [] inTeq ([]right {x = x} {xs = xs}) | refl 
  rewrite isInter++-++r-refl inTeq ([]right {x = x} {xs = xs}) = refl
isInter++-∷right' [] inTeq (∷left {x = x} inTeq2) | refl 
  rewrite isInter++-++r-refl inTeq (∷left {x = x} inTeq2) = refl
isInter++-∷right' [] inTeq (∷right {y = y} inTeq2) | refl 
  rewrite isInter++-++r-refl inTeq (∷right {y = y} inTeq2) = refl
isInter++-∷right' (x ∷ xs) inTeq inTeq2 = refl

isInter++-[]right' : {X : Set} (xs ys : List X) → isInter++ ([]right' xs) ([]right' ys) ≡ []right' (xs ++ ys)
isInter++-[]right' [] _ = refl
isInter++-[]right' (x ∷ xs) [] = refl
isInter++-[]right' (x ∷ xs) (x₁ ∷ ys) = refl

isInter++-[] : {X : Set} {xs ys zs : List X} → (inTeq : isInter xs ys zs) → isInter++ inTeq isInter[] ≡ inTeq
isInter++-[] isInter[] = refl
isInter++-[] []left = refl
isInter++-[] []right = refl
isInter++-[] (∷left inTeq) rewrite isInter++-[] inTeq = refl
isInter++-[] (∷right inTeq) rewrite isInter++-[] inTeq = refl

{-# REWRITE isInter++-[] #-}

isInter++r-refl : {X : Set} → {x : X} → {xs xs₁ ys₁ zs₁ : List X} → (inTeq : isInter xs₁ ys₁ zs₁) → isInter++? (x ∷ xs) zs₁ refl (isInter++r (x ∷ xs) inTeq) ≡ ([] , xs₁ , x ∷ xs , ys₁ , []left , inTeq , refl , refl , refl)
isInter++r-refl isInter[] = refl
isInter++r-refl []left = refl
isInter++r-refl {xs = []} ([]right {x₁} {xs₁}) = refl
isInter++r-refl {xs = x ∷ xs} ([]right {x₁} {xs₁}) 
  rewrite isInter++r-refl {x = x} {xs = xs} ([]right {x = x₁} {xs₁}) = refl
isInter++r-refl {xs = []} (∷left {x = x₁} {xs = xs₁} inTeq) = refl
isInter++r-refl {xs = x ∷ xs} (∷left {x = x₁} {xs = xs₁} inTeq) 
  rewrite isInter++r-refl {x = x} {xs = xs} (∷left {x = x₁} {xs = xs₁} inTeq) = refl
isInter++r-refl {xs = []} (∷right {x = x₁} {xs = xs₁} inTeq) = refl
isInter++r-refl {xs = x ∷ xs} (∷right {x = x₁} {y = y} {xs = xs₁} inTeq) 
  rewrite isInter++r-refl {x = x} {xs = xs} (∷right {x = x₁} {y = y} {xs = xs₁} inTeq) = refl

isInter++l-refl : {X : Set} → {x : X} → {xs xs₁ ys₁ zs₁ : List X} → (inTeq : isInter xs₁ ys₁ zs₁) → isInter++? (x ∷ xs) zs₁ refl (isInter++l (x ∷ xs) inTeq) ≡ (x ∷ xs , xs₁ , [] , ys₁ , []right , inTeq , refl , refl , refl)

isInter++l-refl isInter[] = refl
isInter++l-refl {xs = []} ([]left {xs = xs₁}) = refl
isInter++l-refl {xs = x ∷ xs} ([]left {x = x₁} {xs = xs₁}) 
  rewrite isInter++l-refl {x = x} {xs = xs} ([]left {x = x₁} {xs = xs₁}) = refl
isInter++l-refl []right = refl
isInter++l-refl {xs = []} (∷left {x = x₁} {xs = xs₁} inTeq) = refl
isInter++l-refl {xs = x ∷ xs} (∷left {x = x₁} {xs = xs₁} inTeq) 
  rewrite isInter++l-refl {x = x} {xs = xs} (∷left {x = x₁} {xs = xs₁} inTeq) = refl
isInter++l-refl {xs = []} (∷right {y = y} {zs = zs} inTeq) = refl
isInter++l-refl {xs = x ∷ xs} (∷right {y = y} {zs = zs} inTeq) 
  rewrite isInter++l-refl {x = x} {xs = xs} (∷right {y = y} {zs = zs} inTeq) = refl



isInter++-refl : {X : Set} → {xs₀ ys₀ zs₀ xs₁ ys₁ zs₁ : List X} → (inTeq1 : isInter xs₀ ys₀ zs₀) (inTeq2 : isInter xs₁ ys₁ zs₁) →  isInter++? zs₀ zs₁ refl (isInter++ inTeq1 inTeq2) ≡ (xs₀ , xs₁ , ys₀ , ys₁ , inTeq1 , inTeq2 , refl , refl , refl)
isInter++-refl isInter[] isInter[] = refl
isInter++-refl isInter[] []left = refl
isInter++-refl isInter[] []right = refl
isInter++-refl isInter[] (∷left inTeq2) = refl
isInter++-refl isInter[] (∷right inTeq2) = refl
isInter++-refl ([]left {x} {xs}) inTeq2 = isInter++r-refl {x = x} {xs} inTeq2
isInter++-refl ([]right {x} {xs}) inTeq2 = isInter++l-refl {x = x} {xs} inTeq2 -- isInter++l-refl {x = x} {xs} inTeq2
isInter++-refl (∷left inTeq1) inTeq2 
  rewrite isInter++-refl inTeq1 inTeq2 = refl
isInter++-refl (∷right inTeq1) inTeq2 
  rewrite isInter++-refl inTeq1 inTeq2 = refl

isInter++r-assoc' : {X : Set} {xs xs₁ xs' ys' zs' : List X}
  → (inTeq : isInter xs' ys' zs')
  → isInter++r xs (isInter++r xs₁ inTeq) ≡ isInter++r (xs ++ xs₁) inTeq
isInter++r-assoc' {xs = []} inTeq = refl
isInter++r-assoc' {xs = x ∷ xs} {[]} inTeq = refl
isInter++r-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} isInter[] = refl
isInter++r-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} []left = refl
isInter++r-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} ([]right {x = y} {xs = ys}) 
  rewrite isInter++r-assoc' {xs = xs} {x₁ ∷ xs₁} ([]right {x = y} {xs = ys}) = refl
isInter++r-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} (∷left {x = y} inTeq) 
  rewrite isInter++r-assoc' {xs = xs} {x₁ ∷ xs₁} (∷left {x = y} inTeq) = refl
isInter++r-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} (∷right {y = y} inTeq) 
  rewrite isInter++r-assoc' {xs = xs} {x₁ ∷ xs₁} (∷right {y = y} inTeq) = refl

isInter++r-assoc : {X : Set} {xs₁ xs xs' ys ys' zs zs' : List X}
  → (inTeq : isInter xs ys zs) (inTeq' : isInter xs' ys' zs')
  → isInter++r xs₁ (isInter++ inTeq inTeq') ≡ isInter++ (isInter++r xs₁ inTeq) inTeq'
isInter++r-assoc {xs₁ = []} inTeq inTeq' = refl
isInter++r-assoc {xs₁ = x ∷ xs₁} isInter[] inTeq' = refl
isInter++r-assoc {xs₁ = x ∷ xs₁} []left inTeq' = isInter++r-assoc' {xs = x ∷ xs₁} inTeq'
isInter++r-assoc {xs₁ = x ∷ xs₁} ([]right {x = x₁} {xs}) inTeq' 
  rewrite isInter++r-assoc {xs₁ = xs₁} ([]right {x = x₁} {xs}) inTeq' = refl
isInter++r-assoc {xs₁ = x ∷ xs₁} (∷left {x = x₁} inTeq) inTeq' 
  rewrite isInter++r-assoc {xs₁ = xs₁} (∷left {x = x₁} inTeq) inTeq' = refl
isInter++r-assoc {xs₁ = x ∷ xs₁} (∷right {y = y} inTeq) inTeq' 
  rewrite isInter++r-assoc {xs₁ = xs₁} (∷right {y = y} inTeq) inTeq' = refl


isInter++l-assoc' : {X : Set} {xs xs₁ xs' ys' zs' : List X}
  → (inTeq : isInter xs' ys' zs')
  → isInter++l xs (isInter++l xs₁ inTeq) ≡ isInter++l (xs ++ xs₁) inTeq
isInter++l-assoc' {xs = []} inTeq = refl
isInter++l-assoc' {xs = x ∷ xs} {[]} inTeq = refl
isInter++l-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} isInter[] = refl
isInter++l-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} ([]left {x = y} {xs = ys}) 
  rewrite isInter++l-assoc' {xs = xs} {x₁ ∷ xs₁} ([]left {x = y} {xs = ys}) = refl
isInter++l-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} []right = refl
isInter++l-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} (∷left {x = y} inTeq) 
  rewrite isInter++l-assoc' {xs = xs} {x₁ ∷ xs₁} (∷left {x = y} inTeq) = refl
isInter++l-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} (∷right {y = y} inTeq) 
  rewrite isInter++l-assoc' {xs = xs} {x₁ ∷ xs₁} (∷right {y = y} inTeq) = refl


isInter++l-assoc : {X : Set} {xs₁ xs xs' ys ys' zs zs' : List X}
  → (inTeq : isInter xs ys zs) (inTeq' : isInter xs' ys' zs')
  → isInter++l xs₁ (isInter++ inTeq inTeq') ≡ isInter++ (isInter++l xs₁ inTeq) inTeq'
isInter++l-assoc {xs₁ = []} inTeq inTeq' = refl
isInter++l-assoc {xs₁ = x ∷ xs₁} isInter[] inTeq' = refl
isInter++l-assoc {xs₁ = x ∷ xs₁} ([]left {x = x₁} {xs = xs}) inTeq' 
  rewrite isInter++l-assoc {xs₁ = xs₁} (([]left {x = x₁} {xs = xs})) inTeq' = refl
isInter++l-assoc {xs₁ = x ∷ xs} ([]right {x₁} {xs₁}) inTeq' = isInter++l-assoc' {xs = x ∷ xs} {x₁ ∷ xs₁} inTeq'
isInter++l-assoc {xs₁ = x ∷ xs₁} (∷left {x = x₁} inTeq) inTeq' 
  rewrite isInter++l-assoc {xs₁ = xs₁} (∷left {x = x₁} inTeq) inTeq' = refl
isInter++l-assoc {xs₁ = x ∷ xs₁} (∷right {y = y} inTeq) inTeq' 
  rewrite isInter++l-assoc {xs₁ = xs₁} (∷right {y = y} inTeq) inTeq' = refl


isInter++-assoc : {X : Set} {xs xs' xs'' ys ys' ys'' zs zs' zs'' : List X}
  → (inTeq : isInter xs ys zs) (inTeq' : isInter xs' ys' zs') (inTeq'' : isInter xs'' ys'' zs'')
  → isInter++ inTeq (isInter++ inTeq' inTeq'') ≡ isInter++ (isInter++ inTeq inTeq') inTeq''
isInter++-assoc isInter[] intEq' intEq'' = refl
isInter++-assoc []left intEq' intEq'' = isInter++r-assoc intEq' intEq''
isInter++-assoc []right intEq' intEq'' = isInter++l-assoc intEq' intEq''
isInter++-assoc (∷left inTeq) intEq' intEq'' = cong ∷left (isInter++-assoc inTeq intEq' intEq'')
isInter++-assoc (∷right inTeq) intEq' intEq'' = cong ∷right (isInter++-assoc inTeq intEq' intEq'')

isInter-snoc-left : {X : Set} → {x : X} {xs ys zs : List X} → (inTeq : isInter xs ys zs) → isInter (xs ++ x ∷ []) ys (zs ++ x ∷ [])
isInter-snoc-left isInter[] = []right
isInter-snoc-left ([]left {xs = xs}) = ∷right (isInter-snoc-left {xs = []} ([]left' xs))
isInter-snoc-left []right = []right
isInter-snoc-left (∷left inTeq) = ∷left (isInter-snoc-left inTeq)
isInter-snoc-left (∷right inTeq) = ∷right (isInter-snoc-left inTeq)

isInter-snoc-right : {X : Set} → {x : X} {xs ys zs : List X} → (inTeq : isInter xs ys zs) → isInter xs (ys ++ x ∷ []) (zs ++ x ∷ [])
isInter-snoc-right isInter[] = []left
isInter-snoc-right []left = []left
isInter-snoc-right ([]right {xs = xs}) = ∷left (isInter-snoc-right {ys = []} ([]right' xs))
isInter-snoc-right (∷left inTeq) = ∷left (isInter-snoc-right inTeq)
isInter-snoc-right (∷right inTeq) = ∷right (isInter-snoc-right inTeq)


isInter++[]right' : {X : Set} → {xs xs₁ ys₁ zs : List X} → (inTeq1 : isInter xs [] xs) (inTeq2 : isInter xs₁ ys₁ zs)
    → isInter++ inTeq1 inTeq2 ≡ isInter++l xs inTeq2
isInter++[]right' isInter[] isInter[] = refl
isInter++[]right' isInter[] []left = refl
isInter++[]right' isInter[] []right = refl
isInter++[]right' isInter[] (∷left inTeq2) = refl
isInter++[]right' isInter[] (∷right inTeq2) = refl
isInter++[]right' []right isInter[] = refl
isInter++[]right' []right []left = refl
isInter++[]right' []right []right = refl
isInter++[]right' []right (∷left inTeq2) = refl
isInter++[]right' []right (∷right inTeq2) = refl

isInter++[]left' : {X : Set} → {xs xs₁ ys₁ zs : List X} → (inTeq1 : isInter [] xs xs) (inTeq2 : isInter xs₁ ys₁ zs)
    → isInter++ inTeq1 inTeq2 ≡ isInter++r xs inTeq2
isInter++[]left' isInter[] isInter[] = refl
isInter++[]left' isInter[] []left = refl
isInter++[]left' isInter[] []right = refl
isInter++[]left' isInter[] (∷left inTeq2) = refl
isInter++[]left' isInter[] (∷right inTeq2) = refl
isInter++[]left' []left isInter[] = refl
isInter++[]left' []left []left = refl
isInter++[]left' []left []right = refl
isInter++[]left' []left (∷left inTeq2) = refl
isInter++[]left' []left (∷right inTeq2) = refl

∷right'[]right' : {X : Set} {x : X} {xs : List X} → (inTeq : isInter xs [] xs) 
    → (∷right' {x = x} xs inTeq) ≡ ∷right' xs ([]right' xs)
∷right'[]right' isInter[] = refl
∷right'[]right' []right = refl

{-# REWRITE isInter++[]right' #-}
{-# REWRITE isInter++[]left' #-}

isInter-split-r : {X : Set} → {xs ys zs : List X} {y : X} → (ys₀ ys₁ : List X) → (eq : ys ≡ ys₀ ++ y ∷ ys₁) → (inTeq : isInter xs ys zs) 
              → Σ (List X) (λ xs₀ → Σ (List X) (λ xs₁ → Σ (List X) (λ zs₀ → Σ (List X) (λ zs₁ →
                           Σ (isInter xs₀ ys₀ zs₀) λ inTeq1 → Σ (isInter xs₁ ys₁ zs₁) λ inTeq2 →
                             Σ (xs ≡ xs₀ ++ xs₁) λ eq1 → Σ (zs ≡ zs₀ ++ y ∷ zs₁) λ eq2 →
                               subst (λ x → isInter (xs₀ ++ xs₁) x (zs₀ ++ y ∷ zs₁)) eq (subst₂ (λ a b → isInter a ys b) eq1 eq2 inTeq) ≡ isInter++ inTeq1 (∷right' xs₁ inTeq2)))))
isInter-split-r ys₀ ys₁ eq isInter[] = ⊥-elim ([]disj∷ ys₀ eq)
isInter-split-r {y = y} [] [] refl []left = [] , [] , [] , [] , isInter[] , isInter[] , refl , refl , refl
isInter-split-r [] (x ∷ ys₁) refl []left = [] , [] , [] , x ∷ ys₁ , isInter[] , []left , refl , refl , refl
isInter-split-r (x ∷ ys₀) [] refl []left = [] , [] , x ∷ ys₀ , [] , []left , isInter[] , refl , refl , refl
isInter-split-r (x ∷ ys₀) (x₁ ∷ ys₁) refl []left = [] , [] , x ∷ ys₀ , x₁ ∷ ys₁ , []left , []left , refl , refl , refl
isInter-split-r ys₀ ys₁ eq []right = ⊥-elim ([]disj∷ ys₀ eq)
isInter-split-r [] ys₁ refl (∷left {x = x} inTeq) with isInter-split-r [] ys₁ refl inTeq
isInter-split-r {y = y} [] [] refl (∷left {x = x} .(isInter++ inTeq1 (∷right' xs₁ inTeq2))) | xs₀ , xs₁ , zs₀ , zs₁ , inTeq1 , inTeq2 , refl , refl , refl with isInter-left[] inTeq1 | isInter-left[] inTeq2
... | refl | refl 
  rewrite ∷right'[]right' {x = y} inTeq2 = 
    x ∷ xs₀ , xs₁ , x ∷ xs₀ , xs₁ , []right , []right' xs₁ , refl , refl , refl
isInter-split-r [] (x ∷ ys₁) refl (∷left {x = x₁} .(isInter++ inTeq1 (∷right' xs₁ inTeq2))) | xs₀ , xs₁ , zs₀ , zs₁ , inTeq1 , inTeq2 , refl , refl , refl with isInter-left[] inTeq1
... | refl = 
  x₁ ∷ xs₀ , xs₁ , x₁ ∷ xs₀ , zs₁ , []right , inTeq2 , refl , refl , refl
isInter-split-r (x ∷ ys₀) ys₁ refl (∷left {x = x₁} inTeq) with isInter-split-r (x ∷ ys₀) ys₁ refl inTeq
... | xs₀ , xs₁ , zs₀ , zs₁ , inTeq1 , inTeq2 , refl , refl , refl = 
  x₁ ∷ xs₀ , xs₁ , x₁ ∷ zs₀ , zs₁ , ∷left inTeq1 , inTeq2 , refl , refl , refl
isInter-split-r [] [] refl (∷right {x = x} {xs = xs} inTeq) with isInter-left[] inTeq
... | refl = [] , x ∷ xs , [] , x ∷ xs , isInter[] , inTeq , refl , refl , refl
isInter-split-r [] (x ∷ ys₁) refl (∷right inTeq) with isInter-split-r [] ys₁ refl inTeq
... | [] , x₁ ∷ xs₁ , .[] , zs₁ , isInter[] , inTeq2 , refl , refl , refl = 
  [] , x₁ ∷ xs₁ , [] , x ∷ zs₁ , isInter[] , ∷right inTeq2 , refl , refl , refl
... | x₁ ∷ xs₀ , xs₁ , zs₀ , zs₁ , inTeq1 , inTeq2 , refl , refl , refl with isInter-left[] inTeq1
... | refl = [] , x₁ ∷ xs₀ ++ xs₁ , [] , x₁ ∷ xs₀ ++ x ∷ zs₁ , isInter[] , isInter++ inTeq1 (∷right' {x = x} xs₁ inTeq2) , refl , refl , refl
isInter-split-r (x ∷ ys₀) ys₁ refl (∷right {x = x₁} inTeq) with isInter-split-r  ys₀ ys₁ refl inTeq
isInter-split-r (x ∷ ys₀) ys₁ refl (∷right {x = x₁} inTeq) | [] , x₁ ∷ xs , zs₀ , zs₁ , inTeq1 , inTeq2 , refl , refl , refl with isInter-right[] inTeq1
... | refl =  [] , x₁ ∷ xs , x ∷ zs₀ , zs₁ , []left , inTeq2 , refl , refl , refl
isInter-split-r (x ∷ ys₀) ys₁ refl (∷right {x = x₁} inTeq) | x₁ ∷ xs₀ , xs₁ , zs₀ , zs₁ , inTeq1 , inTeq2 , refl , refl , refl = 
  x₁ ∷ xs₀ , xs₁ , x ∷ zs₀ , zs₁ , ∷right inTeq1 , inTeq2 , refl , refl , refl

isInter-split-r-++-refl : {X : Set} → {xs₀ xs₁ ys₀ ys₁ zs₀ zs₁ : List X} → {x : X} → (inTeq1 : isInter xs₀ ys₀ zs₀) (inTeq2 : isInter xs₁ ys₁ zs₁) → 
             isInter-split-r ys₀ ys₁ refl (isInter++ inTeq1 (∷right' {x = x} xs₁ inTeq2)) ≡ (xs₀ , xs₁ , zs₀ , zs₁ , inTeq1 , inTeq2 , refl , refl , refl)
isInter-split-r-++-refl isInter[] isInter[] = refl
isInter-split-r-++-refl isInter[] []left = refl
isInter-split-r-++-refl isInter[] []right = refl
isInter-split-r-++-refl {x = x} isInter[] (∷left {ys = ys} inTeq2) with isInter-split-r [] ys refl inTeq2
... | .[] , .[] , .[] , .[] , isInter[] , isInter[] , refl , refl , refl = refl
... | .[] , .[] , .[] , .(_ ∷ _) , isInter[] , []left , refl , refl , refl = refl
... | .[] , .(_ ∷ _) , .[] , .(_ ∷ _) , isInter[] , []right , refl , refl , refl = refl
... | .[] , .(_ ∷ _) , .[] , .(_ ∷ _) , isInter[] , ∷left inTeq4 , refl , refl , refl = refl
... | .[] , .(_ ∷ _) , .[] , .(_ ∷ _) , isInter[] , ∷right inTeq4 , refl , refl , refl = refl
... | .(_ ∷ _) , .[] , .(_ ∷ _) , .[] , []right , isInter[] , refl , refl , refl = refl
... | .(_ ∷ _) , .[] , .(_ ∷ _) , .(_ ∷ _) , []right , []left , refl , refl , refl = refl
... | .(_ ∷ _) , .(_ ∷ _) , .(_ ∷ _) , .(_ ∷ _) , []right , []right , refl , refl , refl = refl
... | .(_ ∷ _) , .(_ ∷ _) , .(_ ∷ _) , .(_ ∷ _) , []right , ∷left inTeq4 , refl , refl , refl = refl
... | .(_ ∷ _) , .(_ ∷ _) , .(_ ∷ _) , .(_ ∷ _) , []right , ∷right inTeq4 , refl , refl , refl = refl
isInter-split-r-++-refl {x = x} isInter[] (∷right {y = y} {ys = ys} inTeq2) with isInter-split-r {y = x} [] ys refl (∷right inTeq2)
... | .[] , .(_ ∷ _) , .[] , zs₁' , isInter[] , .inTeq2 , refl , refl , refl rewrite isInter-split-r-++-refl {x = y} isInter[] inTeq2 = refl
... | .(x ∷ _) , xs₁' , .(x ∷ _) , zs₁' , []right , inTeq4 , refl , refl , ()
isInter-split-r-++-refl {x = y} ([]left {x} {xs}) isInter[] = refl
isInter-split-r-++-refl {x = y} ([]left {x} {xs}) []left = refl
isInter-split-r-++-refl {x = y} ([]left {x = x₁} {xs = []}) ([]right {x = x} {xs}) = refl
isInter-split-r-++-refl {x = y} ([]left {x = x₁} {xs = x₂ ∷ xs₁}) ([]right {x = x} {xs}) 
    rewrite isInter-split-r-++-refl {x = y} ([]left {x = x₂} {xs = xs₁}) ([]right {x = x} {xs}) = refl
isInter-split-r-++-refl {x = y} ([]left {x} {[]}) (∷left {x = x₁} inTeq2) 
    rewrite isInter-split-r-++-refl {x = y} isInter[] (∷left {x = x₁} inTeq2) = refl
isInter-split-r-++-refl {x = y} ([]left {x} {x₁ ∷ xs}) (∷left {x = x₂} inTeq2) 
    rewrite isInter-split-r-++-refl {x = y} ([]left {x = x₁} {xs}) (∷left {x = x₂} inTeq2) = refl
isInter-split-r-++-refl {x = y} ([]left {x} {[]}) (∷right {y = y₁} inTeq2) 
    rewrite isInter-split-r-++-refl {x = y} isInter[] (∷right {y = y₁} inTeq2) = refl
isInter-split-r-++-refl {x = y} ([]left {x} {x₁ ∷ xs}) (∷right {y = y₁} inTeq2) 
    rewrite isInter-split-r-++-refl {x = y} ([]left {x = x₁} {xs}) (∷right {y = y₁} inTeq2) = refl
isInter-split-r-++-refl {xs₁ = .[]} {ys₁ = .[]} {x = y} ([]right {x} {[]}) isInter[] = refl
isInter-split-r-++-refl {xs₁ = .[]} {ys₁ = .(_ ∷ _)} {x = y} ([]right {x} {[]}) []left = refl
isInter-split-r-++-refl {xs₁ = .(_ ∷ _)} {ys₁ = .[]} {x = y} ([]right {x} {[]}) []right = refl
isInter-split-r-++-refl {xs₁ = .(_ ∷ _)} {ys₁ = .(_ ∷ _)} {x = y} ([]right {x} {[]}) (∷left {x = x₁} inTeq2)
    rewrite isInter-split-r-++-refl {x = y} isInter[] (∷left {x = x₁} inTeq2) = refl
isInter-split-r-++-refl {xs₁ = .(_ ∷ _)} {ys₁ = .(_ ∷ _)} {x = y} ([]right {x} {[]}) (∷right {y = x₁} inTeq2) 
    rewrite isInter-split-r-++-refl {x = y} isInter[] (∷right {y = x₁} inTeq2) = refl
isInter-split-r-++-refl {xs₁ = .[]} {ys₁ = .[]} {x = y} ([]right {x} {x₁ ∷ xs}) isInter[] 
    rewrite isInter-split-r-++-refl {x = y} ([]right {x = x₁} {xs}) isInter[] = refl
isInter-split-r-++-refl {xs₁ = .[]} {ys₁ = .(_ ∷ _)} {x = y} ([]right {x} {x₁ ∷ xs}) ([]left {x = x₂} {xs₂}) 
    rewrite isInter-split-r-++-refl {x = y} ([]right {x = x₁} {xs}) ([]left {x = x₂} {xs₂}) = refl
isInter-split-r-++-refl {xs₁ = .(_ ∷ _)} {ys₁ = .[]} {x = y} ([]right {x} {x₁ ∷ xs}) ([]right {x = x₂} {xs₂}) 
    rewrite isInter-split-r-++-refl {x = y} ([]right {x = x₁} {xs}) ([]right {x = x₂} {xs₂}) = refl
isInter-split-r-++-refl {xs₁ = .(_ ∷ _)} {ys₁ = .(_ ∷ _)} {x = y} ([]right {x} {x₁ ∷ xs}) (∷left {x = x₂} inTeq2) 
    rewrite isInter-split-r-++-refl {x = y} ([]right {x = x₁} {xs}) (∷left {x = x₂} inTeq2) = refl
isInter-split-r-++-refl {xs₁ = .(_ ∷ _)} {ys₁ = .(_ ∷ _)} {x = y} ([]right {x} {x₁ ∷ xs}) (∷right {y = x₂} inTeq2) 
    rewrite isInter-split-r-++-refl {x = y} ([]right {x = x₁} {xs}) (∷right {y = x₂} inTeq2) = refl
isInter-split-r-++-refl {x = x} (∷left inTeq1) inTeq2 
    rewrite isInter-split-r-++-refl {x = x} inTeq1 inTeq2 = refl
isInter-split-r-++-refl {x = x} (∷right inTeq1) inTeq2 
    rewrite isInter-split-r-++-refl {x = x} inTeq1 inTeq2 = refl

isInter++l-∷left' : {X : Set} {x : X} {xs ys zs : List X} (xs' : List X) (inTeq : isInter xs ys zs)
  → isInter++l (x ∷ xs') inTeq ≡ ∷left' ys (isInter++l xs' inTeq)
isInter++l-∷left' [] isInter[] = refl
isInter++l-∷left' [] []left = refl
isInter++l-∷left' [] []right = refl
isInter++l-∷left' [] (∷left inTeq) = refl
isInter++l-∷left' [] (∷right inTeq) = refl
isInter++l-∷left' (x ∷ xs') isInter[] = refl
isInter++l-∷left' (x ∷ xs') []left = refl
isInter++l-∷left' (x ∷ xs') []right = refl
isInter++l-∷left' (x ∷ xs') (∷left inTeq) = refl
isInter++l-∷left' (x ∷ xs') (∷right inTeq) = refl -- ⊸r⋆seq⊗l