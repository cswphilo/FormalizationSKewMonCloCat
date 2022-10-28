{-# OPTIONS --rewriting #-}

module Embfocus where

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

         
-- -- Every derivation in SeqCalc is ≗ to its normal form


embpass-ri : {Γ : Cxt} {A C : Fma}
      → (f : just A ∣ Γ ⊢ri C)
      → emb-ri (pass-ri f) ≗ pass (emb-ri f)
embpass-ri (⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq)) = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
embpass-ri {A = A} (⊸r (ex {Δ = Δ} {Λ} {A = A₁} (ri2c f) refl refl)) = 
  ⊸r (cong-ex-fma-cxt (Δ ++ Λ) (ex (ex (cong-ex-cxt-fma Δ (embpass-ri f))))) 
  ≗∙ (⊸r (cong-ex-fma-cxt (Δ ++ Λ) (ex-iso ≗∙ ex-cxt-fma-pass [] Δ) 
  ≗∙ ex-fma-cxt-pass [] (Δ ++ Λ) {Δ = []}) 
  ≗∙ ⊸rpass)
embpass-ri (li2ri f) = refl

embpass-c : {Γ Δ : Cxt} {A C : Fma}
      → (f : just A ∣ Γ ؛ Δ ⊢c C)
      → emb-c (pass-c' f refl) ≗ pass (emb-c f)
embpass-c (ex {Γ = Γ} {Δ = Δ} f refl refl) = cong-ex-cxt-fma Δ (embpass-c f) ≗∙ ex-cxt-fma-pass Γ Δ
embpass-c (ri2c (⊸r f)) = embpass-ri (⊸r f)
embpass-c (ri2c (li2ri f)) = refl

mutual
  embIl-ri : {Γ : Cxt} {C : Fma}
      → (f : - ∣ Γ ⊢ri C)
      → emb-ri (Il-ri f) ≗ Il (emb-ri f)
  embIl-ri {Γ} (⊸r {A = A} f) = ⊸r ((cong-ex-fma-cxt Γ (embIl-c f)) ≗∙ ex-fma-cxt-Il [] Γ) ≗∙ ⊸rIl -- ⊸r ((cong-ex-fma-cxt Γ (embIl-c f)) ∙ ex-fma-cxt-Il [] Λ) ∙ ⊸rIl
  embIl-ri (li2ri f) = refl

  embIl-c : {Γ Δ : Cxt} {C : Fma}
      → (f : - ∣ Γ ؛ Δ ⊢c C)
      → emb-c (Il-c f) ≗ Il (emb-c f)
  embIl-c (ex {Γ = Γ} {Λ} f refl refl) = cong-ex-cxt-fma Λ (embIl-c f) ≗∙ ex-cxt-fma-Il Γ Λ
  embIl-c (ri2c f) = embIl-ri f

emb⊗l-ri : {Γ₀ Γ₁ Γ' : Cxt} {A B C : Fma}
    → (f : just A ∣ Γ' ⊢ri C) (eq : Γ' ≡ Γ₀ ++ B ∷ Γ₁)
    → emb-ri (⊗l-ri f eq) ≗ ⊗l (ex-cxt-fma {Γ = []} Γ₀ (emb-ri (subst (λ x → just A ∣ x ⊢ri C) eq f)))
emb⊗l-ri (⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) eq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
emb⊗l-ri {Γ₀} {Γ₁} (⊸r (ex {Δ = Δ} {Λ} (ri2c f) refl refl)) eq with cases++ Γ₀ Δ Γ₁ Λ eq 
emb⊗l-ri {Γ₀} {.(Ω₀ ++ Λ)} {B = B} (⊸r (ex {Δ = .(Γ₀ ++ _ ∷ Ω₀)} {Λ} (ri2c f) refl refl)) refl | inj₁ (Ω₀ , refl , refl) = 
  ⊸r (cong-ex-fma-cxt (Γ₀ ++ Ω₀ ++ Λ) (cong-ex-cxt-fma (Γ₀ ++ Ω₀) (emb⊗l-ri f refl))) 
  ≗∙ ((⊸r (cong-ex-fma-cxt (Γ₀ ++ Ω₀ ++ Λ) (ex-cxt-fma-⊗l [] (Γ₀ ++ Ω₀)) 
  ≗∙ (ex-fma-cxt-⊗l [] (Γ₀ ++ Ω₀ ++ Λ) 
  ≗∙ ⊗l (≡-to-≗ (ex-fma-cxt++ (Γ₀ ++ Ω₀) Λ (ex-cxt-fma {Γ = B ∷ []} {Δ = Λ} (Γ₀ ++ Ω₀) (ex-cxt-fma {Γ = []} {Δ = Ω₀ ++ _ ∷ Λ} Γ₀ (emb-ri f)))) 
  ≗∙ (cong-ex-fma-cxt Λ (((cong-ex-fma-cxt (Γ₀ ++ Ω₀) (cong-ex-cxt-fma (Γ₀ ++ Ω₀) (cong-ex-cxt-fma Γ₀ refl)))) 
  ≗∙ ex-fma-cxt-iso2 (Γ₀ ++ Ω₀)) ≗∙ (((~ (cong-ex-fma-cxt Λ (cong-ex-cxt-fma Γ₀ (ex-fma-cxt-iso2 {Γ = []} {Δ = Λ} (Γ₀ ++ B ∷ Ω₀))))) ≗∙ ex-fma-cxt-ex-cxt-fma Γ₀ Λ)  
  ≗∙ (~ (cong-ex-cxt-fma Γ₀ (≡-to-≗ (ex-fma-cxt++ (Γ₀ ++ B ∷ Ω₀) Λ (ex-cxt-fma {Γ = []} {Δ = Λ} (Γ₀ ++ B ∷ Ω₀) (emb-ri f))))))))))) ≗∙  ⊸r⊗l) 
  ≗∙ (~ ⊗l (ex-cxt-fma-⊸r [] Γ₀ {Δ = Ω₀ ++ Λ})))
emb⊗l-ri {.(Δ ++ Ω₀)} {Γ₁} {B = B} (⊸r (ex {Δ = Δ} {.(Ω₀ ++ B ∷ Γ₁)} {A = A'} (ri2c f) refl refl)) refl | inj₂ (Ω₀ , refl , refl) = 
  ⊸r (cong-ex-fma-cxt (Δ ++ Ω₀ ++ Γ₁) (cong-ex-cxt-fma Δ {A = A'} (emb⊗l-ri {Γ₀ = Δ ++ A' ∷ Ω₀} f refl)))  
  ≗∙ (⊸r (cong-ex-fma-cxt (Δ ++ Ω₀ ++ Γ₁) (ex-cxt-fma-⊗l [] Δ))
  ≗∙ (⊸r (ex-fma-cxt-⊗l [] (Δ ++ Ω₀ ++ Γ₁)) 
  ≗∙ ((⊸r⊗l ≗∙ ⊗l (⊸r (≡-to-≗ (ex-fma-cxt++ Δ (Ω₀ ++ Γ₁) (ex-cxt-fma {Γ = B ∷ []} {Δ = Ω₀ ++ Γ₁} Δ (ex-cxt-fma {Γ = []} {Δ = Γ₁} (Δ ++ A' ∷ Ω₀) (emb-ri f)))) 
  ≗∙ (cong-ex-fma-cxt (Ω₀ ++ Γ₁) (ex-fma-cxt-iso2 Δ) 
  ≗∙ (((≡-to-≗ (ex-fma-cxt++ Ω₀ Γ₁ (ex-cxt-fma {Γ = []} (Δ ++ A' ∷ Ω₀) (emb-ri f))) 
  ≗∙ (cong-ex-fma-cxt Γ₁ (cong-ex-fma-cxt Ω₀ (≡-to-≗ (ex-cxt-fma++ {Γ = []} Δ (A' ∷ Ω₀) (emb-ri f)))) 
  ≗∙ (cong-ex-fma-cxt Γ₁ (ex-fma-cxt-ex-cxt-fma {Γ₁ = []} {Γ₂ = []} {Γ₃ = Γ₁} Δ Ω₀) 
  ≗∙ ((((ex-fma-cxt-ex-cxt-fma Δ Γ₁ 
  ≗∙ cong-ex-cxt-fma Δ (cong-ex-fma-cxt Γ₁ (ex-cxt-fma-ex-fma-cxt-braid Ω₀)))
  ≗∙ cong-ex-cxt-fma Δ (ex-fma-cxt-ex-cxt-fma Ω₀ Γ₁)) 
  ≗∙ (~ (≡-to-≗ (ex-cxt-fma++ Δ Ω₀ (ex-fma-cxt {Γ = Δ ++ Ω₀ ++ B ∷ []} Γ₁ (ex {Γ = Δ ++ Ω₀} {Δ = Γ₁} (ex-fma-cxt {Γ = Δ} Ω₀ (emb-ri f))))))))
  ≗∙ cong-ex-cxt-fma (Δ ++ Ω₀) (~ (≡-to-≗ (ex-fma-cxt++ Ω₀ (B ∷ Γ₁) (emb-ri f)))))))) 
  ≗∙ (~ (cong-ex-cxt-fma (Δ ++ Ω₀) (cong-ex-fma-cxt (Ω₀ ++ B ∷ Γ₁) (ex-fma-cxt-iso2 Δ))))) 
  ≗∙ cong-ex-cxt-fma (Δ ++ Ω₀) (~ (≡-to-≗ (ex-fma-cxt++ Δ (Ω₀ ++ B ∷ Γ₁) (ex-cxt-fma {Γ = []} {Δ = Ω₀ ++ B ∷ Γ₁} Δ (emb-ri f))))))))))  
  ≗∙ (⊗l (~ (ex-cxt-fma-⊸r [] (Δ ++ Ω₀)))))))
emb⊗l-ri (li2ri f) refl = refl



emb⊗l-c : {Γ Δ : Cxt} {A B C : Fma}
    → (f : just A ∣ B ∷ Γ ؛ Δ ⊢c C)
    → emb-c (⊗l-c' f refl) ≗ ⊗l (emb-c f)
emb⊗l-c (ex {Γ = []} (ex {Γ = Γ} f eq'' eq₁) eq' eq) = ⊥-elim ([]disj∷ Γ eq'')
emb⊗l-c (ex {Γ = []} (ri2c f) refl refl) = emb⊗l-ri f refl
emb⊗l-c (ex {Γ = x ∷ Γ} {Δ} f refl refl) = cong-ex-cxt-fma Δ (emb⊗l-c f) ≗∙ ex-cxt-fma-⊗l Γ Δ 

-- compatibility of ­⊸r⋆seq

⊸r⋆seq : {S : Stp} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {A : Fma}
  → (f : S ∣ Γ ⊢ A) (eq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁)
  → S ∣ Γ₀ ⊢ Γ₁ ⊸⋆ A
⊸r⋆seq [] f isInter[] (empty refl) = f
⊸r⋆seq [] f []right (empty refl) = f
⊸r⋆seq (D ∷ Γ₁) f eq (cons {xs₀ = xs₀} {xs₁} refl peq) with isInter-split-r xs₀ xs₁ refl eq
... | Γ₀₀ , Γ₀₁ , Λ₀ , Λ₁ , inTeq1 , inTeq2 , refl , refl , refl = ⊸r (ex-fma-cxt {Γ = Γ₀₀} {Δ = []} Γ₀₁ (⊸r⋆seq Γ₁ f (isInter++ inTeq1 (∷left' xs₁ inTeq2)) peq))

cong⊸r⋆seq : {S : Stp} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {A : Fma}
    → {f g : S ∣ Γ ⊢ A} {inTeq : isInter Γ₀ Γ₁' Γ} {peq : Γ₁' ↭' Γ₁}
    → f ≗ g → ⊸r⋆seq Γ₁ f inTeq peq ≗ ⊸r⋆seq Γ₁ g inTeq peq
cong⊸r⋆seq [] {inTeq = isInter[]} {peq = empty refl} eq' = eq'
cong⊸r⋆seq [] {inTeq = []right} {peq = empty refl} eq' = eq'
cong⊸r⋆seq (x ∷ Γ₁) {inTeq = inTeq} {cons {xs₀ = xs₀} {xs₁} refl peq} eq' with isInter-split-r xs₀ xs₁ refl inTeq
... | Γ₀₀ , Γ₀₁ , Λ₀ , Λ₁ , inTeq1 , inTeq2 , refl , refl , refl = ⊸r (cong-ex-fma-cxt Γ₀₁ (cong⊸r⋆seq Γ₁ eq'))

⊸r⋆seq[] : {S : Stp} {Γ : Cxt} {B : Fma}
    → {f : S ∣ Γ ⊢ B} {inTeq : isInter Γ [] Γ} {peq : [] ↭' []}
    → ⊸r⋆seq [] f inTeq peq ≗ f
⊸r⋆seq[] {inTeq = isInter[]} {peq = empty refl} = refl
⊸r⋆seq[] {inTeq = []right} {peq = empty refl} = refl

⊸r⋆seq⊸r : {S : Stp} {Γ₀₀ Γ₁₀' Γ Γ₀₁ Γ₁₁' Γ' : Cxt} (Γ₁ : Cxt) {A B : Fma}
    → {f : S ∣ Γ ++ A ∷ Γ' ⊢ B} {inTeq1 : isInter Γ₀₀ Γ₁₀' Γ} {inTeq2 : isInter Γ₀₁ Γ₁₁' Γ'} {peq : Γ₁₀' ++ Γ₁₁' ↭' Γ₁}
    → ⊸r⋆seq (Γ₁ ++ A ∷ []) f (isInter++ inTeq1 (∷right' Γ₀₁ inTeq2)) (snoc↭' refl peq) 
    ≗ ⊸r⋆seq Γ₁ (⊸r {Γ = Γ ++ Γ'} (ex-fma-cxt {Δ = []} Γ' f)) (isInter++ inTeq1 inTeq2) peq
⊸r⋆seq⊸r {Γ₁₀' = Γ₁₀'} {Γ₀₁ = Γ₀₁} {Γ₁₁'} [] {A} {inTeq1 = inTeq1} {inTeq2} {empty x} with  []++? {xs = Γ₁₀'} {Γ₁₁'} (sym x)
⊸r⋆seq⊸r {Γ₀₀ = Γ₀₀} {Γ₁₀' = .[]} {Γ₀₁ = .[]} {.[]} [] {A} {inTeq1 = inTeq1} {isInter[]} {empty refl} | refl , refl with isInter-left[] inTeq1
... | refl rewrite isInter-split-r-++-refl {x = A} inTeq1 isInter[] = 
  ⊸r (⊸r⋆seq[] {inTeq = (isInter++l Γ₀₀ []right)} {empty refl}) ≗∙ (~ (⊸r⋆seq[] {inTeq = inTeq1} {empty refl}))
⊸r⋆seq⊸r {Γ₁₀' = .[]} {Γ₀₁ = .(_ ∷ _)} {.[]} [] {A} {inTeq1 = inTeq1} {([]right {x = x} {xs = xs})} {empty refl} | refl , refl with isInter-left[] inTeq1
⊸r⋆seq⊸r {Γ₀₀ = Γ₀₀} {Γ₁₀' = .[]} {Γ₀₁ = .(_ ∷ _)} {.[]} [] {A} {inTeq1 = inTeq1} {([]right {x = x} {xs = xs})} {empty refl} | refl , refl | refl
  rewrite isInter-split-r-++-refl {x = A} inTeq1 ([]right {x = x} {xs = xs}) = 
  ⊸r (cong-ex-fma-cxt xs (ex (⊸r⋆seq[] {inTeq = (isInter++l Γ₀₀ []right)} {empty refl}))) 
  ≗∙ (~ (⊸r⋆seq[] {inTeq = (isInter++l Γ₀₀ []right)} {peq = empty refl}))
⊸r⋆seq⊸r {Γ₁₀' = Γ₁₀'} {Γ₁₁' = Γ₁₁'} (D ∷ Γ₁) {inTeq2 = inTeq2} {cons {xs₀ = xs₀} {xs₁} eq peq} with cases++ xs₀ Γ₁₀' xs₁ Γ₁₁' eq
⊸r⋆seq⊸r {Γ₁₀' = .(xs₀ ++ D ∷ Ω₀)} {Γ₀₁ = Γ₀₁} {Γ₁₁' = Γ₁₁'} (D ∷ Γ₁) {A = A} {inTeq1 = inTeq1} {inTeq2 = inTeq2} {cons {xs₀ = xs₀} {.(Ω₀ ++ Γ₁₁')} refl peq} | inj₁ (Ω₀ , refl , refl) with isInter-split-r xs₀ Ω₀ refl inTeq1
... | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq3 , inTeq4 , refl , refl , refl 
  rewrite sym (isInter++-assoc inTeq3 (∷right' {x = D} Λ₁ inTeq4) inTeq2) | 
          isInter++-∷right' {x = D} Λ₁ inTeq4 inTeq2 | 
          isInter-split-r-++-refl {x = D} inTeq3 (isInter++ inTeq4 inTeq2) |
          sym (isInter++-assoc inTeq3 (∷right' {x = D} Λ₁ inTeq4) (∷right' {x = A} Γ₀₁ inTeq2)) |
          isInter++-∷right' {x = D} Λ₁ inTeq4 (∷right' {x = A} Γ₀₁ inTeq2) |
          isInter-split-r-++-refl {x = D} inTeq3 (isInter++ inTeq4 (∷right' {x = A} Γ₀₁ inTeq2)) |
          sym (isInter++-∷left' {x = D} Ω₀ inTeq4 inTeq2) |
          sym (isInter++-∷left' {x = D} Ω₀ inTeq4 (∷right' {x = A} Γ₀₁ inTeq2)) |
          isInter++-assoc inTeq3 (∷left' {x = D} Ω₀ inTeq4) (∷right' {x = A} Γ₀₁ inTeq2) |
          isInter++-assoc inTeq3 (∷left' {x = D} Ω₀ inTeq4) inTeq2 |
          isInter++-∷left' {x = D} Ω₀ inTeq4 inTeq2 |
          isInter++-∷left' {x = D} Ω₀ inTeq4 (∷right' {x = A} Γ₀₁ inTeq2) |
          isInter++-assoc inTeq3 (∷left' {x = D} Ω₀ inTeq4) (∷right' {x = A} Γ₀₁ inTeq2) |
          isInter++-assoc inTeq3 (∷left' {x = D} Ω₀ inTeq4) inTeq2 = 
          ⊸r (cong-ex-fma-cxt (Λ₁ ++ Γ₀₁) (⊸r⋆seq⊸r Γ₁ {inTeq1 = isInter++ inTeq3 (∷left' Ω₀ inTeq4)} {inTeq2 = inTeq2}))
⊸r⋆seq⊸r {Γ₁₀' = Γ₁₀'} {Γ₁₁' = .(Ω₀ ++ D ∷ xs₁)} (D ∷ Γ₁) {A = A} {inTeq1 = inTeq1} {inTeq2 = inTeq2} {cons {xs₀ = .(Γ₁₀' ++ Ω₀)} {xs₁} refl peq} | inj₂ (Ω₀ , refl , refl) with isInter-split-r Ω₀ xs₁ refl inTeq2
... | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq3 , inTeq4 , refl , refl , refl 
  rewrite isInter++-assoc inTeq1 inTeq3 (∷right' {x = D} Λ₁ inTeq4) |
          isInter-split-r-++-refl {x = D} (isInter++ inTeq1 inTeq3) inTeq4 | 
          sym (isInter++-∷right' {x = A} Λ₀ inTeq3 (∷right' {x = D} Λ₁ inTeq4)) |
          isInter++-assoc inTeq1 (∷right' {x = A} Λ₀ inTeq3) (∷right' {x = D} Λ₁ inTeq4) | 
          isInter-split-r-++-refl {x = D} (isInter++ inTeq1 (∷right' {x = A} Λ₀ inTeq3)) inTeq4 |
          sym (isInter++-assoc inTeq1 inTeq3 (∷left' {x = D} xs₁ inTeq4)) |
          sym (isInter++-assoc inTeq1 (∷right' {x = A} Λ₀ inTeq3) (∷left' {x = D} xs₁ inTeq4)) | 
          isInter++-∷right' {x = A} Λ₀ inTeq3 (∷left' {x = D} xs₁ inTeq4) = 
          ⊸r (cong-ex-fma-cxt Λ₁ (⊸r⋆seq⊸r Γ₁ {inTeq1 = inTeq1} {inTeq2 = (isInter++ inTeq3 (∷left' {x = D} xs₁ inTeq4))}))

⊸r⋆seqIl : {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {B : Fma}
  → {f : - ∣ Γ ⊢ B} {inTeq : isInter Γ₀ Γ₁' Γ} {peq : Γ₁' ↭' Γ₁}
  → ⊸r⋆seq Γ₁ (Il f) inTeq peq ≗ Il (⊸r⋆seq Γ₁ f inTeq peq)
⊸r⋆seqIl {Γ₀ = Γ₀} [] {inTeq = inTeq} {empty refl} with isInter-left[] inTeq
... | refl = ⊸r⋆seq[] {inTeq = inTeq} {empty refl} ≗∙ Il (~ (⊸r⋆seq[] {inTeq = inTeq} {empty refl}))
⊸r⋆seqIl (A ∷ Γ₁) {inTeq = inTeq} {cons {xs₀ = xs₀} {xs₁} refl peq} with isInter-split-r xs₀ xs₁ refl inTeq
... | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq1 , inTeq2 , refl , refl , refl = 
  ⊸r (cong-ex-fma-cxt Λ₁ (⊸r⋆seqIl Γ₁ {inTeq = isInter++ inTeq1 (∷left' xs₁ inTeq2)} {peq})) 
  ≗∙ (⊸r (ex-fma-cxt-Il Λ₀ Λ₁ {Δ = []}) ≗∙ ⊸rIl)


⊸r⋆seq⊗l : {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {A B C : Fma}
  → {f : just A ∣ B ∷ Γ ⊢ C} {inTeq : isInter Γ₀ Γ₁' Γ} {peq : Γ₁' ↭' Γ₁}
  → ⊸r⋆seq Γ₁ (⊗l f) inTeq peq ≗ ⊗l (⊸r⋆seq Γ₁ f (∷left' Γ₁' inTeq) peq)
⊸r⋆seq⊗l [] {inTeq = inTeq} {empty refl} with isInter-left[] inTeq
... | refl = ⊸r⋆seq[] {inTeq = inTeq} {empty refl}
⊸r⋆seq⊗l (A ∷ Γ₁) {B = B} {inTeq = inTeq} {cons {xs₀ = xs₀} {xs₁} refl peq} with isInter-split-r xs₀ xs₁ refl (∷left' {x = B} (xs₀ ++ A ∷ xs₁) inTeq)
... | [] , .(A ∷ _) , [] , Ψ₁ , isInter[] , inTeq2 , refl , refl , ()
... | [] , .(B ∷ _) , B ∷ Ψ₀ , Ψ₁ , []left , inTeq2 , refl , refl , ()
... | B ∷ Λ₀ , Λ₁ , .B ∷ .Λ₀ , Ψ₁ , []right , inTeq2 , refl , refl , refl 
  rewrite isInter-split-r-++-refl {ys₀ = []} {x = A} ([]right' Λ₀) inTeq2 | isInter++l-∷left' {x = B} Λ₀ (∷left' {x = A} xs₁ inTeq2) = 
  ⊸r (cong-ex-fma-cxt Λ₁ (⊸r⋆seq⊗l Γ₁ {inTeq = isInter++l Λ₀ (∷left' xs₁ inTeq2)} {peq})) 
  ≗∙ (⊸r (ex-fma-cxt-⊗l Λ₀ Λ₁) 
  ≗∙ ⊸r⊗l)
⊸r⋆seq⊗l (A ∷ Γ₁) {B = B} {inTeq = .(isInter++ inTeq1 (∷right' Λ₁ inTeq2))} {cons {xs₀ = .(_ ∷ _)} {xs₁} refl peq} | B ∷ Λ₀ , Λ₁ , .B ∷ Ψ₀ , Ψ₁ , ∷left inTeq1 , inTeq2 , refl , refl , refl 
  rewrite isInter-split-r-++-refl {x = A} inTeq1 inTeq2 = 
  ⊸r (cong-ex-fma-cxt Λ₁ (⊸r⋆seq⊗l Γ₁ {inTeq = (isInter++ inTeq1 (∷left' xs₁ inTeq2))} {peq})) 
  ≗∙ (⊸r (ex-fma-cxt-⊗l Λ₀ Λ₁) 
  ≗∙ ⊸r⊗l)


ex-cxt-fma-⊸r⋆seq : {S : Stp} {Λ₀ Λ₁ Ψ₀ Ψ₁ : Cxt} (Γ₁ Δ Λ : Cxt) {A B : Fma} 
  → {f : S ∣ Δ ++ A ∷ Λ ⊢ B} {inTeq1 : isInter Λ₀ Ψ₀ Δ} {inTeq2 : isInter Λ₁ Ψ₁ Λ} {peq : Ψ₀ ++ Ψ₁ ↭' Γ₁}
  → ex-cxt-fma {Γ = []} Λ₀ (⊸r⋆seq Γ₁ f (isInter++ inTeq1 (∷left' {x = A} Ψ₁ inTeq2)) peq) 
    ≗ ⊸r⋆seq Γ₁ (ex-cxt-fma {Γ = []} Δ f) (∷left' (Ψ₀ ++ Ψ₁) (isInter++ inTeq1 inTeq2)) peq
ex-cxt-fma-⊸r⋆seq {Ψ₀ = Ψ₀} {Ψ₁} [] Δ Λ {peq = empty x} with  []++? {xs = Ψ₀} {Ψ₁} (sym x)
ex-cxt-fma-⊸r⋆seq {Ψ₀ = .[]} {.[]} [] Δ Λ {inTeq1 = inTeq1} {inTeq2} {empty refl} | refl , refl with isInter-left[] inTeq1 | isInter-left[] inTeq2 
... | refl | refl with isInter-left[] (isInter++l Δ inTeq2)
... | refl = cong-ex-cxt-fma Δ (⊸r⋆seq[] {inTeq = isInter++l Δ []right} {empty refl}) ≗∙ refl
ex-cxt-fma-⊸r⋆seq {Ψ₀ = Ψ₀} {Ψ₁} (D ∷ Γ₁) Δ Λ {inTeq1 = inTeq1} {inTeq2} {cons {xs₀ = xs₀} {xs₁} eq peq} with cases++ xs₀ Ψ₀ xs₁ Ψ₁ eq 
ex-cxt-fma-⊸r⋆seq {Λ₁ = Λ₁} {Ψ₀ = .(xs₀ ++ D ∷ Ω₀)} {Ψ₁} (D ∷ Γ₁) Δ Λ {A} {f = f} {inTeq1 = inTeq1} {inTeq2} {cons {xs₀ = xs₀} {.(Ω₀ ++ Ψ₁)} refl peq} | inj₁ (Ω₀ , refl , refl) with isInter-split-r xs₀ Ω₀ refl inTeq1
... | Φ₀ , Φ₁ , Ξ₀ , Ξ₁ , inTeq3 , inTeq4 , refl , refl , refl 
  rewrite sym (isInter++-assoc inTeq3 (∷right' {x = D} Φ₁ inTeq4) (∷left' {x = A} Ψ₁ inTeq2)) | 
          sym (isInter++-assoc inTeq3 (∷right' {x = D} Φ₁ inTeq4) inTeq2 ) |
          isInter++-∷left' {x = A} xs₀ inTeq3 (isInter++ (∷right' {x = D} Φ₁ inTeq4) inTeq2) | 
          isInter++-∷right' {x = D} Φ₁ inTeq4 (∷left' {x = A} Ψ₁ inTeq2) |
          isInter++-∷right' {x = D} Φ₁ inTeq4 inTeq2 |
          isInter-split-r-++-refl {x = D} inTeq3 (isInter++ inTeq4 (∷left' {x = A} Ψ₁ inTeq2)) |
          isInter-split-r-++-refl {x = D} (∷left' {x = A} xs₀ inTeq3) (isInter++ inTeq4 inTeq2) |
          sym (isInter++-∷left' {x = A} xs₀ inTeq3 (∷left' {x = D} (Ω₀ ++ Ψ₁) (isInter++ inTeq4 inTeq2))) |
          isInter++-∷left' {x = D} Ω₀ inTeq4 inTeq2 |
          isInter++-∷left' {x = D} Ω₀ inTeq4 (∷left' {x = A} Ψ₁ inTeq2) |
          isInter++-assoc inTeq3 (∷left' {x = D} Ω₀ inTeq4) inTeq2 |
          isInter++-assoc inTeq3 (∷left' {x = D} Ω₀ inTeq4) (∷left' {x = A} Ψ₁ inTeq2) =
          (ex-cxt-fma-⊸r [] (Φ₀ ++ Φ₁) 
          ≗∙ ⊸r (≡-to-≗ (ex-cxt-fma++ Φ₀ Φ₁ (ex-fma-cxt (Φ₁ ++ A ∷ Λ₁) (⊸r⋆seq Γ₁ f (isInter++ (isInter++ inTeq3 (∷left' Ω₀ inTeq4)) (∷left' Ψ₁ inTeq2)) peq))) 
          ≗∙ (cong-ex-cxt-fma Φ₀ (cong-ex-cxt-fma Φ₁ (≡-to-≗ (ex-fma-cxt++ Φ₁ (A ∷ Λ₁) (⊸r⋆seq Γ₁ f (isInter++ (isInter++ inTeq3 (∷left' Ω₀ inTeq4)) (∷left' Ψ₁ inTeq2)) peq)))) 
          ≗∙ (((((cong-ex-cxt-fma Φ₀ (~ (ex-fma-cxt-ex-cxt-fma Φ₁ Λ₁)) 
          ≗∙ (~ (ex-fma-cxt-ex-cxt-fma Φ₀ Λ₁))) 
          ≗∙ cong-ex-fma-cxt Λ₁ (cong-ex-cxt-fma Φ₀ (~ (ex-cxt-fma-ex-fma-cxt-braid Φ₁)))) 
          ≗∙ (~ (cong-ex-fma-cxt Λ₁ (ex-fma-cxt-ex-cxt-fma {Γ₂ = []} Φ₀ Φ₁)))) 
          ≗∙ (~ (cong-ex-fma-cxt Λ₁ (cong-ex-fma-cxt Φ₁ (≡-to-≗ (ex-cxt-fma++ Φ₀ (D ∷ Φ₁) (⊸r⋆seq Γ₁ f (isInter++ (isInter++ inTeq3 (∷left' Ω₀ inTeq4)) (∷left' Ψ₁ inTeq2)) peq))))))) 
          ≗∙ (~ (≡-to-≗ (ex-fma-cxt++ Φ₁ Λ₁ (ex-cxt-fma {Γ = []} (Φ₀ ++ D ∷ Φ₁) ((⊸r⋆seq Γ₁ f (isInter++ (isInter++ inTeq3 (∷left' Ω₀ inTeq4)) (∷left' Ψ₁ inTeq2)) peq)))))))))) 
          ≗∙ ⊸r (cong-ex-fma-cxt (Φ₁ ++ Λ₁) (ex-cxt-fma-⊸r⋆seq Γ₁ (Ξ₀ ++ D ∷ Ξ₁) Λ {inTeq1 = isInter++ inTeq3 (∷left' {x = D} Ω₀ inTeq4)} {inTeq2}))
ex-cxt-fma-⊸r⋆seq {Λ₀ = Λ₀} {Ψ₀ = Ψ₀} {.(Ω₀ ++ D ∷ xs₁)} (D ∷ Γ₁) Δ Λ {A} {inTeq1 = inTeq1} {inTeq2} {cons {xs₀ = .(Ψ₀ ++ Ω₀)} {xs₁} refl peq} | inj₂ (Ω₀ , refl , refl) with isInter-split-r Ω₀ xs₁ refl inTeq2
... | Φ₀ , Φ₁ , Ξ₀ , Ξ₁ , inTeq3 , inTeq4 , refl , refl , refl 
  rewrite isInter++-∷left' {x = A} Ω₀ inTeq3 (∷right' {x = D} Φ₁ inTeq4) |
          isInter++-∷left' {x = A} Ψ₀ inTeq1 (isInter++ inTeq3 (∷right' {x = D} Φ₁ inTeq4)) |
          isInter++-assoc inTeq1 (∷left' {x = A} Ω₀ inTeq3) (∷right' {x = D} Φ₁ inTeq4) |
          isInter++-assoc (∷left' {x = A} Ψ₀ inTeq1) inTeq3 (∷right' {x = D} Φ₁ inTeq4) |
          isInter-split-r-++-refl {x = D} (isInter++ inTeq1 (∷left' {x = A} Ω₀ inTeq3)) inTeq4 |
          isInter-split-r-++-refl {x = D} (isInter++ (∷left' {x = A} Ψ₀ inTeq1) inTeq3) inTeq4 |
          sym (isInter++-assoc (∷left' {x = A} Ψ₀ inTeq1) inTeq3 (∷left' {x = D} xs₁ inTeq4)) |
          sym (isInter++-assoc inTeq1 (∷left' {x = A} Ω₀ inTeq3) (∷left' {x = D} xs₁ inTeq4)) |
          sym (isInter++-∷left' {x = A} Ψ₀ inTeq1 (isInter++ inTeq3 (∷left' {x = D} xs₁ inTeq4))) | 
          sym (isInter++-∷left' {x = A} Ω₀ inTeq3 (∷left' {x = D} xs₁ inTeq4)) = 
          (ex-cxt-fma-⊸r [] Λ₀ ≗∙ ⊸r (~ (ex-fma-cxt-ex-cxt-fma Λ₀ Φ₁))) 
          ≗∙ ⊸r (cong-ex-fma-cxt Φ₁ (ex-cxt-fma-⊸r⋆seq Γ₁ Δ (Ξ₀ ++ D ∷ Ξ₁)  {inTeq1 = inTeq1} {(isInter++ inTeq3 (∷left' xs₁ inTeq4))} {peq}))

⊸r⋆seqpass : {Γ₀ Γ₁' Γ : Cxt} (Γ₁ : Cxt) {A B : Fma} 
  → {f : just A ∣ Γ ⊢ B} (inTeq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁)
  → ⊸r⋆seq Γ₁ (pass f) (∷left' Γ₁' inTeq) peq ≗ pass (⊸r⋆seq Γ₁ f inTeq peq)
⊸r⋆seqpass [] inTeq (empty refl) with isInter-left[] inTeq
... | refl = pass (~ (⊸r⋆seq[] {inTeq = inTeq} {empty refl}))
⊸r⋆seqpass (D ∷ Γ₁) {A} inTeq (cons {xs₀ = xs₀} {xs₁} refl peq) with isInter-split-r xs₀ xs₁ refl inTeq
... | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq1 , inTeq2 , refl , refl , refl 
  rewrite isInter++-∷left' {x = A} xs₀ inTeq1 (∷right' {x = D} Λ₁ inTeq2) |
  isInter-split-r-++-refl {x = D} (∷left' {x = A} xs₀ inTeq1) inTeq2 |
  sym (isInter++-∷left' {x = A} xs₀ inTeq1 (∷left' {x = D} xs₁ inTeq2)) = 
  ⊸r (cong-ex-fma-cxt Λ₁ (⊸r⋆seqpass Γ₁ (isInter++ inTeq1 (∷left' {x = D} xs₁ inTeq2)) peq) ≗∙ ex-fma-cxt-pass Λ₀ Λ₁) ≗∙ ⊸rpass
  
ersL-isInter : {Γ Γ₀ Γ₁' : TCxt} (inTeq : isInter Γ₀ Γ₁' Γ) → isInter (ersL Γ₀) (ersL Γ₁') (ersL Γ)
ersL-isInter isInter[] = isInter[]
ersL-isInter []left = []left
ersL-isInter []right = []right
ersL-isInter (∷left inTeq) = ∷left (ersL-isInter inTeq)
ersL-isInter (∷right inTeq) = ∷right (ersL-isInter inTeq)

ersL-isInter++l : {Γ₀ Γ₁ Γ : TCxt} → (Γ' : TCxt) (inTeq : isInter Γ₀ Γ₁ Γ) → ersL-isInter (isInter++l Γ' inTeq) ≡ isInter++l (ersL Γ') (ersL-isInter inTeq)
ersL-isInter++l [] inTeq = refl
ersL-isInter++l (A ∷ Γ') isInter[] = refl
ersL-isInter++l (A ∷ Γ') []left = cong ∷left (ersL-isInter++l  Γ' []left)
ersL-isInter++l (A ∷ Γ') []right = refl
ersL-isInter++l (A ∷ Γ') (∷left inTeq) = cong ∷left (ersL-isInter++l Γ' (∷left inTeq))
ersL-isInter++l (A ∷ Γ') (∷right inTeq) = cong ∷left (ersL-isInter++l Γ' (∷right inTeq)) 

ersL-isInter++r : {Γ₀ Γ₁ Γ : TCxt} → (Γ' : TCxt) (inTeq : isInter Γ₀ Γ₁ Γ) → ersL-isInter (isInter++r Γ' inTeq) ≡ isInter++r (ersL Γ') (ersL-isInter inTeq)
ersL-isInter++r [] inTeq = refl
ersL-isInter++r (A ∷ Γ') isInter[] = refl
ersL-isInter++r (A ∷ Γ') []left = refl
ersL-isInter++r (A ∷ Γ') []right = cong ∷right (ersL-isInter++r Γ' []right)
ersL-isInter++r (A ∷ Γ') (∷left inTeq) = cong ∷right (ersL-isInter++r Γ' (∷left inTeq))
ersL-isInter++r (A ∷ Γ') (∷right inTeq) = cong ∷right (ersL-isInter++r Γ' (∷right inTeq))

ersL-isInter++ : {Γ₀ Γ₁ Γ Δ₀ Δ₁ Δ : TCxt} → (inTeq1 : isInter Γ₀ Γ₁ Γ) (inTeq2 : isInter Δ₀ Δ₁ Δ)
    → ersL-isInter (isInter++ inTeq1 inTeq2) ≡ isInter++ (ersL-isInter inTeq1) (ersL-isInter inTeq2)
ersL-isInter++ isInter[] inTeq2 = refl
ersL-isInter++ ([]left {x} {xs}) inTeq2 = ersL-isInter++r (x ∷ xs) inTeq2
ersL-isInter++ ([]right {x} {xs}) inTeq2 = ersL-isInter++l (x ∷ xs) inTeq2
ersL-isInter++ (∷left inTeq1) inTeq2 = cong ∷left (ersL-isInter++ inTeq1 inTeq2)
ersL-isInter++ (∷right inTeq1) inTeq2 = cong ∷right (ersL-isInter++ inTeq1 inTeq2)
{-# REWRITE ersL-isInter++ #-}

ersL-∷right' : {Γ₀ Γ₁ Γ : TCxt} {x : Tag} {(x , A) : TFma} → (inTeq : isInter Γ₀ Γ₁ Γ) → ersL-isInter (∷right' {x = (x , A)} Γ₀ inTeq) ≡ ∷right' {x = A} (ersL Γ₀) (ersL-isInter inTeq)
ersL-∷right' isInter[] = refl
ersL-∷right' []left = refl
ersL-∷right' []right = refl
ersL-∷right' (∷left inTeq) = refl
ersL-∷right' (∷right inTeq) = refl

{-# REWRITE ersL-∷right' #-}

ersL-∷left' : {Γ₀ Γ₁ Γ : TCxt} {A : TFma} → (inTeq : isInter Γ₀ Γ₁ Γ) 
    →  ∷left' {x = proj₂ A} (ersL Γ₁) (ersL-isInter inTeq) ≡ ersL-isInter (∷left' {x = A} Γ₁ inTeq) 
ersL-∷left' isInter[] = refl
ersL-∷left' []left = refl
ersL-∷left' []right = refl
ersL-∷left' (∷left inTeq) = refl
ersL-∷left' (∷right inTeq) = refl



ersL-isInter-tag-lem' : {Γ Γ₀ Γ₁ : Cxt} (inTeq : isInter Γ₀ Γ₁ Γ) → ersL-isInter (tag-lem' inTeq) ≡ inTeq
ersL-isInter-tag-lem' isInter[] = refl
ersL-isInter-tag-lem' []left = refl
ersL-isInter-tag-lem' []right = refl
ersL-isInter-tag-lem' (∷left inTeq) = cong ∷left  (ersL-isInter-tag-lem' inTeq)
ersL-isInter-tag-lem' (∷right inTeq) = cong ∷right  (ersL-isInter-tag-lem' inTeq)

{-# REWRITE ersL-isInter-tag-lem' #-}

tag-isInter++l : {Γ₀ Γ₁ Γ : Cxt} → (Γ' : Cxt) (inTeq : isInter Γ₀ Γ₁ Γ) → tag-isInter (isInter++l Γ' inTeq) ≡ (tagL Γ') ++ (tag-isInter inTeq)
tag-isInter++l [] inTeq = refl
tag-isInter++l (A ∷ Γ') isInter[] = refl
tag-isInter++l (A ∷ Γ') []left = cong ((∘ , A) ∷_) (tag-isInter++l Γ' []left)
tag-isInter++l (A ∷ Γ') []right = refl
tag-isInter++l (A ∷ Γ') (∷left inTeq) = cong ((∘ , A) ∷_) (tag-isInter++l Γ' (∷left inTeq))
tag-isInter++l (A ∷ Γ') (∷right inTeq) = cong ((∘ , A) ∷_) (tag-isInter++l Γ' (∷right inTeq))

tag-isInter++r : {Γ₀ Γ₁ Γ : Cxt} → (Γ' : Cxt) (inTeq : isInter Γ₀ Γ₁ Γ) → tag-isInter (isInter++r Γ' inTeq) ≡ (black Γ') ++ (tag-isInter inTeq)
tag-isInter++r [] inTeq = refl
tag-isInter++r (A ∷ Γ') isInter[] = refl
tag-isInter++r (A ∷ Γ') []left = refl
tag-isInter++r (A ∷ Γ') []right = cong ((∙ , A) ∷_) (tag-isInter++r Γ' []right)
tag-isInter++r (A ∷ Γ') (∷left inTeq) = cong ((∙ , A) ∷_) (tag-isInter++r Γ' (∷left inTeq))
tag-isInter++r (A ∷ Γ') (∷right inTeq) = cong ((∙ , A) ∷_) (tag-isInter++r Γ' (∷right inTeq))

tag-isInter++ : {Γ₀ Γ₁ Γ Δ₀ Δ₁ Δ : Cxt} (inTeq1 : isInter Γ₀ Γ₁ Γ) (inTeq2 : isInter Δ₀ Δ₁ Δ) →  tag-isInter (isInter++ inTeq1 inTeq2) ≡ (tag-isInter inTeq1) ++ (tag-isInter inTeq2)
tag-isInter++ isInter[] inTeq2 = refl
tag-isInter++ ([]left {x} {xs}) inTeq2 = tag-isInter++r (x ∷ xs) inTeq2
tag-isInter++ ([]right {x} {xs}) inTeq2 = tag-isInter++l (x ∷ xs) inTeq2
tag-isInter++ (∷left {x = x} inTeq1) inTeq2 = cong ((∘ , x) ∷_) (tag-isInter++ inTeq1 inTeq2)
tag-isInter++ (∷right {y = y} inTeq1) inTeq2 = cong ((∙ , y) ∷_) (tag-isInter++ inTeq1 inTeq2)
{-# REWRITE tag-isInter++ #-}

isInter++l-tag-isInter : (Γ' : Cxt) {Γ₀ Γ₁ Γ : Cxt} → (inTeq : isInter Γ₀ Γ₁ Γ) → tag-isInter (isInter++l Γ' inTeq) ≡ tagL Γ' ++ (tag-isInter inTeq)
isInter++l-tag-isInter [] inTeq = refl
isInter++l-tag-isInter (x ∷ Γ') isInter[] = refl
isInter++l-tag-isInter (x ∷ Γ') []left = cong ((∘ , x) ∷_) (isInter++l-tag-isInter Γ' []left)
isInter++l-tag-isInter (x ∷ Γ') []right = refl
isInter++l-tag-isInter (x ∷ Γ') (∷left inTeq) = cong ((∘ , x) ∷_) (isInter++l-tag-isInter Γ' (∷left inTeq))
isInter++l-tag-isInter (x ∷ Γ') (∷right inTeq) = cong ((∘ , x) ∷_) (isInter++l-tag-isInter Γ' (∷right inTeq))
{-# REWRITE isInter++l-tag-isInter #-}

isInter++l-tag-lem' : (Γ' : Cxt) {Γ₀ Γ₁ Γ : Cxt} → (inTeq : isInter Γ₀ Γ₁ Γ) → isInter++l (tagL Γ') (tag-lem' inTeq) ≡ tag-lem' (isInter++l Γ' inTeq)
isInter++l-tag-lem' [] {Γ = Γ} inTeq = refl
isInter++l-tag-lem' (x ∷ Γ') {Γ = .[]} isInter[] = refl
isInter++l-tag-lem' (x ∷ Γ') {Γ = .(x₁ ∷ xs)} ([]left {x = x₁} {xs}) = cong ∷left (isInter++l-tag-lem' Γ' ([]left {x = x₁} {xs}))
isInter++l-tag-lem' (x ∷ Γ') {Γ = .(_ ∷ _)} []right = refl
isInter++l-tag-lem' (x ∷ Γ') {Γ = .(_ ∷ _)} (∷left inTeq) = cong ∷left (isInter++l-tag-lem' Γ' (∷left inTeq))
isInter++l-tag-lem' (x ∷ Γ') {Γ = .(_ ∷ _)} (∷right inTeq) = cong ∷left (isInter++l-tag-lem' Γ' (∷right inTeq)) -- need
-- {-# REWRITE isInter++l-tag-lem' #-}

isInter++r-tag-isInter : (Γ' : Cxt) {Γ₀ Γ₁ Γ : Cxt} → (inTeq : isInter Γ₀ Γ₁ Γ) → tag-isInter (isInter++r Γ' inTeq) ≡ black Γ' ++ (tag-isInter inTeq)
isInter++r-tag-isInter [] inTeq = refl
isInter++r-tag-isInter (x ∷ Γ') isInter[] = refl
isInter++r-tag-isInter (x ∷ Γ') []left = refl 
isInter++r-tag-isInter (x ∷ Γ') []right = cong ((∙ , x) ∷_) (isInter++r-tag-isInter Γ' []right) 
isInter++r-tag-isInter (x ∷ Γ') (∷left inTeq) = cong ((∙ , x) ∷_) (isInter++r-tag-isInter Γ' (∷left inTeq)) 
isInter++r-tag-isInter (x ∷ Γ') (∷right inTeq) = cong ((∙ , x) ∷_) (isInter++r-tag-isInter Γ' (∷right inTeq)) 
{-# REWRITE isInter++r-tag-isInter #-}

isInter++r-tag-lem' : (Γ' : Cxt) {Γ₀ Γ₁ Γ : Cxt} → (inTeq : isInter Γ₀ Γ₁ Γ) → isInter++r (black Γ') (tag-lem' inTeq) ≡ tag-lem' (isInter++r Γ' inTeq)
isInter++r-tag-lem' [] {Γ = Γ} inTeq = refl
isInter++r-tag-lem' (x ∷ Γ') {Γ = .[]} isInter[] = refl
isInter++r-tag-lem' (x ∷ Γ') {Γ = .(_ ∷ _)} []left = refl -- cong ∷left (isInter++l-tag-lem' Γ' ([]left {x = x₁} {xs}))
isInter++r-tag-lem' (x ∷ Γ') {Γ = .(x₁ ∷ xs)} ([]right {x = x₁} {xs}) = cong ∷right (isInter++r-tag-lem' Γ' ([]right)) -- refl
isInter++r-tag-lem' (x ∷ Γ') {Γ = .(_ ∷ _)} (∷left inTeq) = cong ∷right (isInter++r-tag-lem' Γ' (∷left inTeq)) 
isInter++r-tag-lem' (x ∷ Γ') {Γ = .(_ ∷ _)} (∷right inTeq) = cong ∷right (isInter++r-tag-lem' Γ' (∷right inTeq))  -- need

isInter++-tag-lem' : {Γ₀ Γ₁ Γ Δ₀ Δ₁ Δ : Cxt} → (inTeq1 : isInter Γ₀ Γ₁ Γ) (inTeq2 : isInter Δ₀ Δ₁ Δ) → isInter++ (tag-lem' inTeq1) (tag-lem' inTeq2) ≡ tag-lem' (isInter++ inTeq1 inTeq2)
isInter++-tag-lem' isInter[] inTeq2 = refl
isInter++-tag-lem' ([]left {x} {xs}) inTeq2 = isInter++r-tag-lem' (x ∷ xs) inTeq2
isInter++-tag-lem' ([]right {x} {xs}) inTeq2 = isInter++l-tag-lem' (x ∷ xs) inTeq2
isInter++-tag-lem' (∷left inTeq1) inTeq2 = cong ∷left (isInter++-tag-lem' inTeq1 inTeq2)
isInter++-tag-lem' (∷right inTeq1) inTeq2 = cong ∷right (isInter++-tag-lem' inTeq1 inTeq2)
{-# REWRITE isInter++-tag-lem' #-}


tag-isInter-∷right' :  (Γ₀ : Cxt) {Γ₁ Γ : Cxt} {A : Fma} → (inTeq : isInter Γ₀ Γ₁ Γ) →  tag-isInter (∷right' {x = A} Γ₀ inTeq) ≡ (∙ , A) ∷ (tag-isInter inTeq)
tag-isInter-∷right' [] isInter[] = refl
tag-isInter-∷right' [] []left = refl
tag-isInter-∷right' (x ∷ Γ₀) inTeq = refl
{-# REWRITE tag-isInter-∷right' #-}

tag-lem'-∷right' : {Γ₀ Γ₁ Γ : Cxt} {A : Fma} → (inTeq : isInter Γ₀ Γ₁ Γ) → ∷right' {x = (∙ , A)} (tagL Γ₀) (tag-lem' inTeq)  ≡ tag-lem' (∷right' {x = A} Γ₀ inTeq)
tag-lem'-∷right' isInter[] = refl
tag-lem'-∷right' []left = refl
tag-lem'-∷right' []right = refl
tag-lem'-∷right' (∷left inTeq) = refl
tag-lem'-∷right' (∷right inTeq) = refl -- need

isInter-split-r-++-ersL-refl : {xs₀ xs₁ zs₀ zs₁ : TCxt} {ys₀ ys₁ : Cxt} → {A : Fma} → (inTeq1 : isInter xs₀ (black ys₀) zs₀) (inTeq2 : isInter xs₁ (black ys₁) zs₁) 
        →  isInter-split-r ys₀ ys₁ refl (isInter++ (ersL-isInter inTeq1) (∷right' {x =  A} (ersL xs₁) (ersL-isInter inTeq2))) 
            ≡ (ersL xs₀ , ersL xs₁ , ersL zs₀ , ersL zs₁ , ersL-isInter inTeq1 , ersL-isInter inTeq2 , refl , refl , refl)
isInter-split-r-++-ersL-refl {xs₁ = xs₁} inTeq1 inTeq2 = isInter-split-r-++-refl  (ersL-isInter inTeq1) (ersL-isInter inTeq2)

⊸r⋆seq⊸l :  {Γ Δ Δ₀ Δ₁' : Cxt} (Δ₁ : Cxt) {A B C : Fma}
    → (f : - ∣ Γ ⊢ A) (g : just B ∣ Δ ⊢ C) (inTeq : isInter Δ₀ Δ₁' Δ) (peq : Δ₁' ↭' Δ₁)
    → ⊸r⋆seq Δ₁ (⊸l f g) (isInter++l Γ inTeq) peq ≗ ⊸l f (⊸r⋆seq Δ₁ g inTeq peq)
⊸r⋆seq⊸l {Γ} [] f g isInter[] (empty refl) = ⊸r⋆seq[] {inTeq = (isInter++l Γ isInter[])} {empty refl}
⊸r⋆seq⊸l {Γ} [] f g []right (empty refl) = ⊸r⋆seq[] {inTeq = (isInter++l Γ []right)} {empty refl}
⊸r⋆seq⊸l {Γ} (D ∷ Δ₁) f g inTeq (cons {xs₀ = xs₀} {xs₁} refl peq) with isInter-split-r xs₀ xs₁ refl inTeq
... | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq1 , inTeq2 , refl , refl , refl 
    rewrite isInter++l-assoc {xs₁ = Γ} inTeq1 (∷right' {x = D} Λ₁ inTeq2) | 
            isInter-split-r-++-refl {x = D} (isInter++l Γ inTeq1) inTeq2 |
            sym (isInter++l-assoc {xs₁ = Γ} inTeq1 (∷left' {x = D} xs₁ inTeq2)) = 
        ⊸r (cong-ex-fma-cxt Λ₁ (⊸r⋆seq⊸l Δ₁ f g (isInter++ inTeq1 (∷left' xs₁ inTeq2)) peq)) 
        ≗∙ (⊸r (ex-fma-cxt-⊸l₂ Λ₀ Λ₁) 
        ≗∙ ⊸r⊸l {Γ = Γ} {Λ₀ ++ Λ₁})

-- Important for emb⊗r-f, ⊗r , ⊸l , and pass case
⊸r⋆seq-ersL-isInter-tag-lem' : {S : Stp} {Γ Γ₀ : Cxt} {Γ₁' : Cxt} (Γ₁ : Cxt) {A : Fma} 
    → (f : S ∣ Γ ⊢ A) (inTeq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁) 
    → ⊸r⋆seq Γ₁ f (ersL-isInter (tag-lem' inTeq)) peq ≗ ⊸r⋆seq Γ₁ f inTeq peq
⊸r⋆seq-ersL-isInter-tag-lem' Γ₁ f inTeq peq = refl

mutual
  emb⊸r⋆-ri∙' : {S : Stp} {Γ Γ₀ : TCxt} {Γ₁' : Cxt} (Γ₁ : Cxt) {A : Fma}
      → (f : ∙ ∣ S ∣ Γ ⊢ri A)  (inTeq : isInter Γ₀ (black Γ₁') Γ) (peq : Γ₁' ↭' Γ₁)
      → emb-ri∙ (⊸r⋆∙ Γ₁ f inTeq peq) ≗ ⊸r⋆seq Γ₁ (emb-ri∙ f) (ersL-isInter inTeq) peq
  emb⊸r⋆-ri∙' [] f isInter[] (empty refl) = refl
  emb⊸r⋆-ri∙' [] f []right (empty refl) = refl
  emb⊸r⋆-ri∙' {S = S} (D ∷ Γ₁) f inTeq (cons {xs₀ = xs₀} {xs₁} refl peq) with isInter-split-r (black xs₀) (black xs₁) refl inTeq
  ... | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq1 , inTeq2 , refl , refl , refl 
    rewrite isInter-split-r-++-ersL-refl {ys₀ = xs₀} {xs₁} {A = D} inTeq1 inTeq2 | ersL-∷left' {A = (∙ , D)} inTeq2 = 
        ⊸r (cong-ex-fma-cxt (ersL Λ₀ ++ ersL Λ₁) (cong-ex-cxt-fma (ersL Λ₀) (emb⊸r⋆-ri∙' Γ₁ f (isInter++ inTeq1 (∷left' (black xs₁) inTeq2)) peq))) 
        ≗∙ ⊸r (≡-to-≗ (ex-fma-cxt++ (ersL Λ₀) (ersL Λ₁) (ex-cxt-fma {Γ = []} (ersL Λ₀) (⊸r⋆seq Γ₁ (emb-ri∙ f) (isInter++ (ersL-isInter inTeq1) (ersL-isInter (∷left' (black xs₁) inTeq2))) peq))) 
        ≗∙ cong-ex-fma-cxt {Δ = []} (ersL Λ₁) (ex-fma-cxt-iso2 (ersL Λ₀) ≗∙ refl))

  emb⊗r-f∙ : {S : Irr} {Γ : TCxt} {Δ : TCxt} {A B : Fma}
      → (f : ∙ ∣ irr S ∣ whiteL Γ ⊢ri A) (g : - ∣ ersL Δ ⊢ri B)
      → emb-f∙ {S = S} (⊗r {Γ = Γ} {Δ = Δ} f g) ≗ ⊗r {Γ = ersL (whiteL Γ)} {ersL Δ} (emb-ri∙ f) (emb-ri g)
  emb⊗r-f∙ {Γ = Γ} f g rewrite sym (whiteErs Γ) = refl 
  
  emb⊗r-f : {S : Irr} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A : Pos} {B : Fma}
      → (f : S ∣ Γ ⊢f A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁)
      → emb-f (gen⊗r-f Γ₁ f g inTeq peq) ≗ ⊗r (⊸r⋆seq Γ₁ (emb-f f) inTeq peq) (emb-ri g)
  emb⊗r-f {Γ₀ = Γ₀} {Γ₁'} Γ₁ ax g inTeq peq with []++ {xs = Γ₀} {Γ₁'} (isInter-end[] inTeq)
  ... | refl , refl with empty↭' peq
  ... | refl = ⊗r (~ (⊸r⋆seq[] {inTeq = inTeq} {peq})) refl
  emb⊗r-f {Γ₀ = Γ₀} {Γ₁'} Γ₁ Ir g inTeq peq with []++ {xs = Γ₀} {Γ₁'} (isInter-end[] inTeq)
  ... | refl , refl with empty↭' peq
  ... | refl = ⊗r (~ (⊸r⋆seq[] {inTeq = inTeq} {peq})) refl
  emb⊗r-f Γ₁ (⊗r {Γ = Γ} {Δ} f g) h inTeq peq with isInter++? Γ Δ refl inTeq
  ... | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , inTeq , inTeq' , refl , refl , refl 
    rewrite sym (whiteErs (tag-isInter {Γ = Γ} inTeq)) = 
        ⊗r (emb⊸r⋆-ri∙' Γ₁ (li2ri (p2li (f2p (⊗r {Γ = tag-isInter inTeq} {tag-isInter inTeq'} f g)))) (tag-lem' (isInter++ inTeq inTeq')) peq 
        ≗∙ (cong⊸r⋆seq Γ₁ (emb⊗r-f∙ {Γ = tag-isInter inTeq} {Δ = tag-isInter inTeq'} f g) ≗∙ ⊸r⋆seq-ersL-isInter-tag-lem' Γ₁ (⊗r (emb-ri∙ f) (emb-ri g)) (isInter++ inTeq inTeq') peq)) refl

  emb⊗r-f Γ₁ (⊸l {Γ} {Δ} f g) h inTeq peq with isInter++? Γ Δ refl inTeq
  ... | Γ₀₀ , Γ₀₁ , [] , Γ₁₁' , inTeq1 , inTeq2 , refl , refl , refl with isInter-left[] inTeq1
  ... | refl = ⊸l refl (emb⊗r-li Γ₁ g h inTeq2 peq) ≗∙ ((~ ⊗r⊸l) ≗∙ (~ (⊗r (⊸r⋆seq⊸l Γ₁ (emb-ri f) (emb-li g) (inTeq2) peq) refl)))
  emb⊗r-f Γ₁ (⊸l {Γ} {Δ} f g) h inTeq peq | Γ₀₀ , Γ₀₁ , D ∷ Γ₁₀' , Γ₁₁' , inTeq1 , inTeq2 , refl , refl , refl with isInter-split-r [] Γ₁₀' refl inTeq1
  ... | Γ₀₀₀ , Γ₀₀₁ , Γ'' , Γ''' , inTeq3 , inTeq4 , refl , refl , refl with isInter-left[] inTeq3
  ... | refl with tag-lem-left[] inTeq3
  ... | .(tagL Γ₀₀₀) , inTeq3' , refl 
    rewrite tag-lem'-∷right' {A = D} (isInter++ inTeq4 inTeq2) |
            isInter++l-tag-lem' Γ₀₀₀ (∷right' {x = D} (Γ₀₀₁ ++ Γ₀₁) (isInter++ inTeq4 inTeq2)) |
            sym (isInter++l-assoc {xs₁ = Γ₀₀₀} (∷right' {x = D} Γ₀₀₁ inTeq4) inTeq2) |
            isInter++-∷right' {x = D} Γ₀₀₁ inTeq4 inTeq2 = 
            ⊗r (emb⊸r⋆-ri∙' Γ₁ (li2ri (p2li (f2p (⊸l∙ {Γ' = tagL Γ₀₀₀ ++ (∙ , D) ∷ tag-isInter inTeq4} {Λ = tag-isInter inTeq4} {Δ = tag-isInter inTeq2} f g refl)))) (tag-lem' (isInter++l Γ₀₀₀ (∷right' (Γ₀₀₁ ++ Γ₀₁) (isInter++ inTeq4 inTeq2)))) peq 
            ≗∙ ⊸r⋆seq-ersL-isInter-tag-lem' Γ₁ (⊸l (emb-ri f) (emb-li g)) (isInter++l Γ₀₀₀ (∷right' (Γ₀₀₁ ++ Γ₀₁) (isInter++ inTeq4 inTeq2))) peq) refl

  emb⊗r-p : {S : Irr} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A : Pos} {B : Fma}
      → (f : S ∣ Γ ⊢p A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁)
      → emb-p (gen⊗r-p Γ₁ f g inTeq peq) ≗ ⊗r (⊸r⋆seq Γ₁ (emb-p f) inTeq peq) (emb-ri g)
  emb⊗r-p Γ₁ (pass f) g []left peq = ⊗r (emb⊸r⋆-ri∙' Γ₁ (li2ri (p2li (pass∙ f))) []left peq) refl 
  emb⊗r-p Γ₁ (pass f) g []right peq with empty↭' peq
  emb⊗r-p {Γ = A ∷ Γ} .[] (pass f) g []right (empty refl) | refl = 
    pass (emb⊗r-li [] f g ([]right' Γ) (empty refl)) 
    ≗∙ ((~ ⊗rpass) ≗∙ ⊗r (pass (⊸r⋆seq[] {inTeq = []right' Γ} {empty refl})) refl)
  emb⊗r-p Γ₁ (pass f) g (∷left inTeq) peq = 
    pass (emb⊗r-li Γ₁ f g inTeq peq) ≗∙ ((~ ⊗rpass) ≗∙ ⊗r (~ (⊸r⋆seqpass Γ₁ inTeq peq)) refl)
  emb⊗r-p Γ₁ (pass f) g (∷right {y = A'} inTeq) peq 
     = ⊗r (emb⊸r⋆-ri∙' Γ₁ (li2ri (p2li (pass∙ f))) (tag-lem' (∷right inTeq)) peq ≗∙ ⊸r⋆seq-ersL-isInter-tag-lem' Γ₁ (pass (emb-li f)) (∷right inTeq) peq) refl 
  emb⊗r-p Γ₁ (f2p f) g inTeq peq = emb⊗r-f Γ₁ f g inTeq peq

  emb⊗r-li : {S : Stp} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A : Pos} {B : Fma}
      → (f : S ∣ Γ ⊢li A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁)
      → emb-li (gen⊗r-li Γ₁ f g inTeq peq) ≗ ⊗r (⊸r⋆seq Γ₁ (emb-li f) inTeq peq) (emb-ri g)
  emb⊗r-li Γ₁ (Il f) g inTeq peq = Il (emb⊗r-li Γ₁ f g inTeq peq) 
    ≗∙ ((~ (⊗rIl)) 
    ≗∙ (~ (⊗r (⊸r⋆seqIl Γ₁ {inTeq = inTeq} {peq}) refl)))
  emb⊗r-li Γ₁ (⊗l (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) g inTeq peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
  emb⊗r-li Γ₁ (⊗l (ex {Δ = Δ} {Λ} (ri2c (li2ri f)) refl refl)) g inTeq peq with isInter++? Δ Λ refl inTeq
  ... | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq1 , inTeq2 , refl , refl , refl = 
    ⊗l (cong-ex-cxt-fma Λ₀ (emb⊗r-li Γ₁ f g (isInter++ inTeq1 (∷left' Ψ₁ inTeq2)) peq)) 
    ≗∙ (⊗l (ex-cxt-fma-⊗r₁ [] Λ₀) ≗∙ (((~ ⊗r⊗l) 
    ≗∙ ⊗r (⊗l (ex-cxt-fma-⊸r⋆seq Γ₁ Δ Λ {inTeq1 = inTeq1} {inTeq2} {peq})) refl) 
    ≗∙ ⊗r (~ (⊸r⋆seq⊗l Γ₁ {inTeq = (isInter++ inTeq1 inTeq2)} {peq})) refl))
  emb⊗r-li Γ₁ (p2li f) g inTeq peq = emb⊗r-p Γ₁ f g inTeq peq

emb⊗r-ri : {S : Stp} {Γ Γ₀ Γ₁' : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter Γ₀ Γ₁' Γ) (peq : Γ₁' ↭' Γ₁)
    → emb-li (gen⊗r-ri Γ₁ f g inTeq peq) ≗ ⊗r (⊸r⋆seq Γ₁ (emb-ri f) inTeq peq) (emb-ri g)
emb⊗r-ri Γ₁ (⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁)) ginT eq peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
emb⊗r-ri Γ₁ (⊸r (ex {Δ = Δ} {Λ} (ri2c f) refl refl)) g inTeq peq with isInter++? Δ Λ refl inTeq
... | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , inTeq' , inTeq'' , refl , refl , refl = 
  emb⊗r-ri (Γ₁ ++ _ ∷ []) f g (isInter++ inTeq' (∷right' Γ₀₁ inTeq'')) (snoc↭' refl peq) 
  ≗∙ ⊗r ((⊸r⋆seq⊸r Γ₁ {inTeq1 = inTeq'} {inTeq''} {peq}
  ≗∙ (~ (cong⊸r⋆seq Γ₁ {inTeq = isInter++ inTeq' inTeq''} {peq} (⊸r (cong-ex-fma-cxt Λ (ex-fma-cxt-iso2 Δ)))))) 
  ≗∙ (~ (cong⊸r⋆seq Γ₁ {inTeq = isInter++ inTeq' inTeq''} {peq} (⊸r (≡-to-≗ ((ex-fma-cxt++ Δ Λ (ex-cxt-fma {Γ = []} Δ (emb-ri f))))))))) refl
emb⊗r-ri Γ₁ (li2ri f) g inTeq peq = emb⊗r-li Γ₁ f g inTeq peq

emb⊗r-c-ri : {S : Stp} {Γ Δ Λ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ؛ Δ ⊢c A) (g : - ∣ Λ ⊢ri B)
    → emb-c (⊗r-c-ri f g) ≗ ⊗r (emb-c f) (emb-ri g)
emb⊗r-c-ri (ex {Γ = Γ} {Δ} {Λ} f refl refl) g = cong-ex-cxt-fma Δ (emb⊗r-c-ri f g) ≗∙ ex-cxt-fma-⊗r₁ Γ Δ
emb⊗r-c-ri {Δ = Δ} (ri2c f) g with isInter-left[] ([]right' Δ) 
... | refl = emb⊗r-ri [] f g ([]right' Δ) (empty refl) ≗∙ ⊗r (⊸r⋆seq[] {inTeq = []right' Δ} {empty refl}) refl

emb⊗r-c : {S : Stp} {Γ Δ Λ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ؛ [] ⊢c A) (g : - ∣ Δ ؛ Λ ⊢c B)
    → emb-c (⊗r-c f g) ≗ ⊗r (emb-c f) (emb-c g)
emb⊗r-c {Γ = Γ₁} f (ex {Γ = Γ} {Δ} g refl refl) = cong-ex-cxt-fma {Γ = Γ₁ ++ Γ} Δ (emb⊗r-c f g) ≗∙ ex-cxt-fma-⊗r₂ Γ Δ 
emb⊗r-c f (ri2c g) = emb⊗r-c-ri f g

emb⊸l-ri : {Γ Δ : Cxt} {A B C : Fma}
    → (f : - ∣ Γ ⊢ri A) (g : just B ∣ Δ ⊢ri C)
    → emb-ri (⊸l-ri f g) ≗ ⊸l (emb-ri f) (emb-ri g)
emb⊸l-ri f (⊸r (ex (ex {Γ = x ∷ Γ} g refl refl) eq' eq)) = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
emb⊸l-ri {Γ = Γ} f (⊸r (ex {Δ = Δ} {Λ} (ri2c g) refl refl)) = 
  ⊸r (cong-ex-fma-cxt (Γ ++ Δ ++ Λ) (cong-ex-cxt-fma (Γ ++ Δ) (emb⊸l-ri f g))) 
  ≗∙ (⊸r (≡-to-≗ (ex-fma-cxt++ {Γ = []} (Γ ++ Δ) Λ (ex-cxt-fma {Γ = []} (Γ ++ Δ) (⊸l (emb-ri f) (emb-ri g)))) 
  ≗∙ (cong-ex-fma-cxt Λ (ex-fma-cxt-iso2 (Γ ++ Δ)) ≗∙ ((ex-fma-cxt-⊸l₂ Δ Λ {Δ = []} 
  ≗∙ (refl ≗∙ (~ (⊸l {f = (emb-ri f)} refl (cong-ex-fma-cxt Λ (ex-fma-cxt-iso2 Δ)))))) 
  ≗∙ (⊸l {f = (emb-ri f)} refl (~ (≡-to-≗ (ex-fma-cxt++ {Γ = []} {Δ = []} Δ Λ (ex-cxt-fma {Γ = []} Δ (emb-ri g))))))))) 
  ≗∙ ⊸r⊸l {Δ = Δ ++ Λ})
emb⊸l-ri f (li2ri g) = refl

emb⊸l-c-ri : {Γ Δ Λ : Cxt} {A B C : Fma}
    → (f : - ∣ Γ ؛ Δ ⊢c A) (g : just B ∣ Λ ⊢ri C)
    → emb-c (⊸l-c-ri f g) ≗ ⊸l (emb-c f) (emb-ri g)
emb⊸l-c-ri {Λ = Λ₁} (ex {Γ = Γ} {Δ} {Λ} f refl refl) g = cong-ex-cxt-fma {Δ = Λ ++ Λ₁} Δ (emb⊸l-c-ri f g) ≗∙ ex-cxt-fma-⊸l₁ Γ Δ
emb⊸l-c-ri (ri2c f) g = emb⊸l-ri f g

emb⊸l-c : {Γ Δ Λ : Cxt} {A B C : Fma}
    → (f : - ∣ Γ ؛ [] ⊢c A) (g : just B ∣ Δ ؛ Λ ⊢c C)
    → emb-c (⊸l-c f g) ≗ ⊸l (emb-c f) (emb-c g)
emb⊸l-c {Γ = Γ₁} f (ex {Γ = Γ} {Δ} g refl refl) = cong-ex-cxt-fma {Γ = Γ₁ ++ Γ} Δ (emb⊸l-c f g) ≗∙ ex-cxt-fma-⊸l₂ Γ Δ
emb⊸l-c f (ri2c g) = emb⊸l-c-ri f g

emb⊸r-c' : {S : Stp} {Γ Λ Δ₀ Δ₁ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ؛ Λ ⊢c B) (eq : Λ ≡ Δ₀ ++ A ∷ Δ₁)
    → emb-c (⊸r-c' f eq) ≗ ⊸r (ex-fma-cxt {Γ = Γ ++ Δ₀} Δ₁ (emb-c (subst (λ x → S ∣ Γ ؛ x ⊢c B) eq f)))
emb⊸r-c' {Δ₀ = Δ₀} {Δ₁} (ex {Δ = Δ} {Λ} f refl eq₁) eq with cases++ Δ₀ Δ Δ₁ Λ eq
emb⊸r-c' {Δ₀ = Δ₀} {.(Ω₀ ++ Λ)} {A'} (ex {Γ = Γ} {Δ = .(Δ₀ ++ A' ∷ Ω₀)} {Λ} {A = A} f refl refl) refl | inj₁ (Ω₀ , refl , refl) = 
  cong-ex-cxt-fma (Δ₀ ++ Ω₀) (emb⊸r-c' f refl) 
  ≗∙ (ex-cxt-fma-⊸r Γ (Δ₀ ++ Ω₀) 
  ≗∙ ⊸r (cong-ex-cxt-fma (Δ₀ ++ Ω₀) (≡-to-≗ (ex-fma-cxt++ {Γ = Γ ++ Δ₀} Ω₀ (A ∷ Λ) (emb-c f))) 
  ≗∙ (≡-to-≗ (ex-cxt-fma++ {Γ = Γ} {Δ = Λ ++ A' ∷ []} Δ₀ Ω₀ (ex-fma-cxt {Γ = Γ ++ Δ₀ ++ Ω₀ ++ A ∷ []} Λ (ex {Γ = Γ ++ Δ₀ ++ Ω₀} {Δ = Λ} (ex-fma-cxt {Γ = Γ ++ Δ₀} {Δ = A ∷ Λ} Ω₀ (emb-c f))))) 
  ≗∙ ((((cong-ex-cxt-fma Δ₀ ((~ (ex-fma-cxt-ex-cxt-fma {Γ₁ = Γ ++ Δ₀} {Γ₂ = []} Ω₀ Λ)) 
  ≗∙ cong-ex-fma-cxt Λ (~ (ex-cxt-fma-ex-fma-cxt-braid {Γ = Γ ++ Δ₀} Ω₀))) 
  ≗∙ (~ (ex-fma-cxt-ex-cxt-fma Δ₀ Λ))) 
  ≗∙ cong-ex-fma-cxt Λ (~ (ex-fma-cxt-ex-cxt-fma {Γ₂ = []} Δ₀ Ω₀))) 
  ≗∙ cong-ex-fma-cxt Λ (cong-ex-fma-cxt Ω₀ (~ (≡-to-≗ (ex-cxt-fma++ Δ₀ (A' ∷ Ω₀) (emb-c f)))))) 
  ≗∙ (~ (≡-to-≗ (ex-fma-cxt++ {Γ = Γ ++ A ∷ Δ₀} {Δ = []} Ω₀ Λ (((ex-cxt-fma {Γ = Γ} (Δ₀ ++ A' ∷ Ω₀) (emb-c f)))))))))))
emb⊸r-c' {Δ₀ = .(Δ ++ Ω₀)} {Δ₁} {A'} (ex {Γ = Γ} {Δ = Δ} {.(Ω₀ ++ A' ∷ Δ₁)} {A = A} f refl refl) refl | inj₂ (Ω₀ , refl , refl) = 
  cong-ex-cxt-fma Δ (emb⊸r-c' {Δ₀ = Δ ++ A ∷ Ω₀} f refl) 
  ≗∙ (ex-cxt-fma-⊸r Γ Δ {Δ = Ω₀ ++ Δ₁} 
  ≗∙ ⊸r (~ (ex-fma-cxt-ex-cxt-fma Δ Δ₁)))
emb⊸r-c' {Δ₀ = Δ₀} {Δ₁} (ri2c f) refl = 
  ⊸r (≡-to-≗ (ex-fma-cxt++ Δ₀ Δ₁ (ex-cxt-fma {Γ = []} Δ₀ (emb-ri f)))) 
  ≗∙ (⊸r (cong-ex-fma-cxt Δ₁ (ex-fma-cxt-iso2 Δ₀)) 
  ≗∙ refl)

emb⊸r-c : {S : Stp} {Γ Γ' Δ : Cxt} {A B : Fma}
    → (f : S ∣ Γ' ؛ Δ ⊢c B) (eq : Γ' ≡ Γ ++ A ∷ [])
    → emb-c (⊸r-c'' f eq) ≗ ⊸r (ex-fma-cxt Δ (emb-c (subst (λ x → S ∣ x ؛ Δ ⊢c B) eq f)))
emb⊸r-c {Γ = Γ₁} (ex {Γ = Γ} f refl refl) eq with snoc≡ Γ Γ₁ eq
emb⊸r-c {Γ = Γ₁} (ex {Γ = Γ₁} {Δ} {Λ} f refl refl) refl | refl , refl =  
  (emb⊸r-c' f refl 
  ≗∙ ⊸r (cong-ex-fma-cxt Λ (~ (ex-fma-cxt-iso2 Δ)))) 
  ≗∙ ⊸r (~ (≡-to-≗ (ex-fma-cxt++ Δ Λ (ex-cxt-fma Δ (emb-c f)))))
emb⊸r-c {Γ = Γ} (ri2c f) eq = ⊥-elim ([]disj∷ Γ eq)

embex-c : ∀{S Φ Ψ Δ Λ A B C}
  → (f : S ∣ Λ ؛ Δ ⊢c C)
  → (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
  → emb-c (ex-c' Φ f eq) ≗ ex {Γ = Φ} (emb-c (subst (λ x → S ∣ x ؛ Δ ⊢c C) eq f))
embex-c {Φ = Φ} {Ψ} {A = A} {B} (ex {Γ = Φ₁} f refl eq') eq with cases++ Φ₁ Φ [] (A ∷ B ∷ Ψ) (sym eq)
... | inj₁ (Φ₀ , p , q) = ⊥-elim ([]disj∷ Φ₀ q)
embex-c {Φ = Φ} {.[]} {A = A} {B} (ex {Γ = .(Φ₁ ++ _ ∷ [])} {Γ} {Δ} (ex {Γ = Φ₁} {Γ₁} {Δ₁} f refl refl) refl eq') eq | inj₂ (A ∷ [] , refl , q) with snoc≡ Φ₁ Φ q | cases++ Γ Γ₁ Δ Δ₁ eq'
embex-c {Φ = Φ} {.[]} {_} {_} {A} {B} (ex {_} {.(Φ ++ _ ∷ [])} {Γ} {.(Γ₀ ++ Δ₁)} (ex {Γ = Φ} {.(Γ ++ B ∷ Γ₀)} {Δ₁} f refl refl) refl refl) refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl) =
  proof≗
    ex-cxt-fma {Γ = Φ ++ B ∷ []} (Γ ++ Γ₀) (ex-cxt-fma {Γ = Φ} Γ (emb-c f)) 
  ≗〈 ≡-to-≗ (ex-cxt-fma++ {Γ = Φ ++ B ∷ []} Γ Γ₀ _) 〉
    ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma {Γ = Φ ++ B ∷ Γ} Γ₀ (ex-cxt-fma {Γ = Φ} Γ (emb-c f)))
  ≗〈 cong-ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma-ex-cxt-fma Γ Γ₀) 〉
    ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma {Γ = Φ} Γ (ex-cxt-fma {Γ = Φ ++ Γ ++ B ∷ []} Γ₀ (emb-c f)))
  ≗〈 cong-ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (cong-ex-cxt-fma {Γ = Φ} Γ (~ (ex-iso {Γ = Φ ++ Γ}))) 〉
    ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma {Γ = Φ} Γ (ex {Γ = Φ ++ Γ} (ex {Γ = Φ ++ Γ} (ex-cxt-fma {Γ = Φ ++ Γ ++ B ∷ []} Γ₀ (emb-c f)))))
  ≗〈 ~ ex-cxt-fma-braid {Γ = Φ} Γ 〉
    ex (ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ (ex-cxt-fma {Γ = Φ} Γ (ex {Γ = Φ ++ Γ} (ex-cxt-fma {Γ = Φ ++ Γ ++ B ∷ []} Γ₀ (emb-c f)))))
  ≗〈 ≡-to-≗ (sym (cong ex (cong (ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ) (ex-cxt-fma++ {Γ = Φ} Γ (B ∷ Γ₀) _)))) 〉
    ex (ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ (ex-cxt-fma {Γ = Φ} (Γ ++ B ∷ Γ₀) (emb-c f)))
  qed≗
embex-c {Φ = Φ} {.[]} {_} {_} {A} {B} (ex {_} {.(Φ ++ _ ∷ [])} {.(Γ ++ Γ₀)} {Δ} (ex {Γ = Φ} {Γ} {.(Γ₀ ++ B ∷ Δ)} f refl refl) refl refl) refl | inj₂ (A ∷ [] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl) = 
  proof≗
    ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma {Γ = Φ} (Γ ++ A ∷ Γ₀) (emb-c f))
  ≗〈 ≡-to-≗ (cong (ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ) (ex-cxt-fma++ {Γ = Φ} Γ (A ∷ Γ₀) _)) 〉 
    ex-cxt-fma {Γ = Φ ++ B ∷ []} Γ (ex-cxt-fma {Γ = Φ} Γ (ex {Γ = Φ ++ Γ} (ex-cxt-fma {Γ = Φ ++ Γ ++ A ∷ []} Γ₀ (emb-c f))))
  ≗〈 ~ ex-cxt-fma-braid {Γ = Φ} Γ 〉 
    ex (ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ (ex-cxt-fma {Γ = Φ} Γ (ex-cxt-fma {Γ = Φ ++ Γ ++ A ∷ []} Γ₀ (emb-c f))) )
  ≗〈 ex (cong-ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ (~ ex-cxt-fma-ex-cxt-fma Γ Γ₀)) 〉 
    ex (ex-cxt-fma {Γ = Φ ++ A ∷ []} Γ (ex-cxt-fma {Γ = Φ ++ A ∷ Γ} Γ₀ (ex-cxt-fma {Γ = Φ} Γ (emb-c f))))
  ≗〈 ≡-to-≗ (sym (cong ex (ex-cxt-fma++ {Γ = Φ ++ A ∷ []} Γ Γ₀ _))) 〉 
    ex (ex-cxt-fma {Γ = Φ ++ A ∷ []} (Γ ++ Γ₀) (ex-cxt-fma {Γ = Φ} Γ (emb-c f)))
  qed≗
embex-c {Φ = Φ} {.[]} {A = A} {B} (ex {Γ = .[]} (ri2c f) refl eq') eq | inj₂ (A ∷ [] , refl , q) = ⊥-elim ([]disj∷ Φ q)
embex-c {Φ = Φ} {.(Φ₀ ++ _ ∷ [])} {A = A} {B} (ex {Γ = .(Φ ++ A ∷ B ∷ Φ₀)} {Γ} {Δ} f refl refl) refl | inj₂ (A ∷ B ∷ Φ₀ , refl , refl) =
  cong-ex-cxt-fma {Γ = Φ ++ _ ∷ _ ∷ Φ₀} Γ (embex-c f refl) ≗∙ ex-cxt-fma-ex Γ
embex-c {Φ = Φ} (ri2c f) eq = ⊥-elim ([]disj∷ Φ eq)

embax-c : {A : Fma}
      → emb-c (ax-c {A = A}) ≗ ax
embax-c {` x} = refl
embax-c {I} = ~ axI
embax-c {A ⊗ B} = 
  (emb⊗l-c (⊗r-c ax-c (pass-c ax-c)) 
  ≗∙ ⊗l (emb⊗r-c ax-c (pass-c ax-c) 
  ≗∙ ⊗r embax-c (embpass-c ax-c ≗∙ pass embax-c))) 
  ≗∙ (~ (ax⊗))
embax-c {A ⊸ B} = 
  (emb⊸r-c {Γ = []} ((⊸l-c (pass-c ax-c) ax-c)) refl 
  ≗∙ ⊸r (emb⊸l-c (pass-c ax-c) ax-c 
  ≗∙ ⊸l (embpass-c ax-c ≗∙ pass embax-c) embax-c)) 
  ≗∙ (~ (ax⊸))

embfocus : {S : Stp} {Γ : Cxt} {C : Fma}
       → (f : S ∣ Γ ⊢ C)
       → emb-c (focus f) ≗ f
embfocus ax = embax-c
embfocus (pass f) = embpass-c (focus f) ≗∙ (pass (embfocus f))
embfocus Ir = refl
embfocus (Il f) = embIl-c (focus f) ≗∙ Il (embfocus f)  
embfocus (⊗l f) = emb⊗l-c (focus f) ≗∙ ⊗l (embfocus f) 
embfocus (⊗r f g) = emb⊗r-c (focus f) (focus g) ≗∙ ⊗r (embfocus f) (embfocus g)
embfocus (⊸l f g) = emb⊸l-c (focus f) (focus g) ≗∙ ⊸l (embfocus f) (embfocus g)
embfocus (⊸r f) = emb⊸r-c (focus f) refl ≗∙ ⊸r (embfocus f)
embfocus (ex f) = embex-c (focus f) refl ≗∙ ex (embfocus f)                                     