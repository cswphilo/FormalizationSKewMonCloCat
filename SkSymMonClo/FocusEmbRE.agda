{-# OPTIONS --rewriting #-}

module FocusEmbRE where

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
open import FocusingRE
open import Utilities renaming (++? to ++??)
open import IsInter 
open import EqfocusRE
open import EmbfocusRE


act : {S : Stp} (Φ : Cxt) {Γ : Cxt} {A C : Fma}
  → (f : S ∣ Φ ؛ A ∷ Γ ⊢c C)
  → S ∣ Φ ++ A ∷ [] ؛ Γ ⊢c C
act Φ f = ex {Δ = []} f refl refl

act⋆ : {S : Stp} (Φ Γ : Cxt) {Δ : Cxt} {C : Fma}
  → (f : S ∣ Φ ؛ Γ ++ Δ ⊢c C)
  → S ∣ Φ ++ Γ ؛ Δ ⊢c C
act⋆ Φ [] f = f 
act⋆ Φ (A ∷ Γ) f = act⋆ (Φ ++ A ∷ []) Γ (act Φ f) 

ex-cxt-fma-c : {S : Stp} {Γ Δ Ω : Cxt} (Λ : Cxt) {A C : Fma}
    → (f : S ∣ Γ ++ Λ ++ A ∷ Δ ؛ Ω ⊢c C)
    → S ∣ Γ ++ A ∷ Λ ++ Δ ؛ Ω ⊢c C
ex-cxt-fma-c [] f = f
ex-cxt-fma-c {Γ = Γ} {Δ} (A ∷ Λ) f = ex-c Γ {Ψ = Λ ++ Δ} (ex-cxt-fma-c {Γ = Γ ++ A ∷ []} Λ f)

ex-fma-cxt-c : {S : Stp} {Γ Δ Ω : Cxt} (Λ : Cxt) {A C : Fma}
    → (f : S ∣ Γ ++ A ∷ Λ ++ Δ ؛ Ω ⊢c C)
    → S ∣ Γ ++ Λ ++ A ∷ Δ ؛ Ω ⊢c C
ex-fma-cxt-c [] f = f
ex-fma-cxt-c {Γ = Γ} {Δ} (A ∷ Λ) f = ex-fma-cxt-c {Γ = Γ ++ A ∷ []} Λ (ex-c Γ f)

focus-ex-cxt-fma : {S : Stp} {Γ Δ : Cxt} (Λ : Cxt) {A C : Fma}
    → (f : S ∣ Γ ++ Λ ++ A ∷ Δ ⊢ C)
    → focus (ex-cxt-fma {Γ = Γ} Λ f) ≡ ex-cxt-fma-c {Γ = Γ} {Ω = []} Λ (focus f)
focus-ex-cxt-fma [] f = refl
focus-ex-cxt-fma {Γ = Γ} {Δ} (A ∷ Λ) f = cong (λ x → ex-c Γ x) (focus-ex-cxt-fma {Γ = Γ ++ A ∷ []} Λ f)

focus-ex-fma-cxt : {S : Stp} {Γ Δ : Cxt} (Λ : Cxt) {A C : Fma}
    → (f : S ∣ Γ ++ A ∷ Λ ++ Δ ⊢ C)
    → focus (ex-fma-cxt {Γ = Γ} {Δ} Λ f) ≡ ex-fma-cxt-c {Γ = Γ} {Ω = []} Λ (focus f)
focus-ex-fma-cxt [] f = refl
focus-ex-fma-cxt {Γ = Γ} {Δ} (A ∷ Λ) f = focus-ex-fma-cxt {Γ = Γ ++ A ∷ []} Λ (ex f) 

mutual
    c∙2c : {S : Stp} {Γ Δ : TCxt} {C : Fma} 
        → (f : ∙ ∣ S ∣ Γ ؛ Δ ⊢c C)
        → S ∣ ersL Γ ؛ ersL Δ ⊢c C
    c∙2c (ex∙ f refl refl) = ex (c∙2c f) refl refl
    c∙2c (ri2c f) = ri2c (ri∙2ri f)  
    ri∙2ri : {S : Stp} {Γ : TCxt} {C : Fma}
        → (f : ∙ ∣ S ∣ Γ ⊢ri C)
        → S ∣ ersL Γ ⊢ri C
    ri∙2ri (⊸r∙ (ex∙ (ex∙ {Γ = x ∷ Γ} f refl refl) eq' eq)) = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
    ri∙2ri (⊸r∙ (ex∙ (ri2c f) refl refl)) = ⊸r (ex (ri2c (ri∙2ri f)) refl refl)
    ri∙2ri (li2ri f) = li2ri (li∙2li f)
    li∙2li : {S : Stp} {Γ : TCxt} {C : Pos}
        → (f : ∙ ∣ S ∣ Γ ⊢li C)
        → S ∣ ersL Γ ⊢li C
    li∙2li (p2li f) = p2li (p∙2p f)
    p∙2p : {S : Irr} {Γ : TCxt} {C : Pos}
        → (f : ∙ ∣ S ∣ Γ ⊢p C)
        → S ∣ ersL Γ ⊢p C
    p∙2p (pass∙ f) = pass f
    p∙2p (f2p f) = f2p (f∙2f f)
    f∙2f : {S : Irr} {Γ : TCxt} {C : Pos}
        → (f : ∙ ∣ S ∣ Γ ⊢f C)
        → S ∣ ersL Γ ⊢f C
    f∙2f ax = ax
    f∙2f Ir = Ir
    f∙2f (⊗r∙ f g) = ⊗r f g -- ⊗r f g
    f∙2f (⊸l∙ f g refl refl) = ⊸l f g

act⋆-Il-c : (Φ Γ : Cxt) {Δ : Cxt} {C : Fma} {f : - ∣ Φ ؛ Γ ++ Δ ⊢c C}
    → Il-c (act⋆ Φ Γ {Δ} f) ≡ act⋆ Φ Γ (Il-c f)
act⋆-Il-c Φ [] = refl
act⋆-Il-c Φ (A ∷ Γ) = act⋆-Il-c (Φ ++ A ∷ []) Γ

ex-c-act : {S : Stp} (Φ : Cxt) {Γ Ψ : Cxt} {A A' B C : Fma}
    → (f : S ∣ Φ ++ A ∷ B ∷ Ψ ؛ A' ∷ Γ ⊢c C)
    → act (Φ ++ B ∷ A ∷ Ψ) (ex-c Φ f) ≡ ex-c Φ (act (Φ ++ A ∷ B ∷ Ψ) f)
ex-c-act Φ {Ψ = Ψ} {A} {A'} {B} f rewrite cases++-inj₂ (A ∷ B ∷ Ψ) Φ [] A' = refl
-- cases++-inj₂ (A ∷ B ∷ Ψ) Φ [] A'
ex-c-act⋆ : {S : Stp} (Φ Γ : Cxt) {Ψ Δ : Cxt} {A B C : Fma}
    → (f : S ∣ Φ ++ A ∷ B ∷ Ψ ؛ Γ ++ Δ ⊢c C)
    → ex-c Φ {Γ = Δ} (act⋆ (Φ ++ A ∷ B ∷ Ψ) Γ f) ≡ act⋆ (Φ ++ B ∷ A ∷ Ψ) Γ (ex-c Φ f)
ex-c-act⋆ Φ [] f = refl
ex-c-act⋆ Φ (A' ∷ Γ) {Ψ} {Δ} {A} {B} f with ex-c-act⋆ Φ (Γ) {Ψ ++ A' ∷ []} {Δ} (act (Φ ++ A ∷ B ∷ Ψ) f)
... | eq rewrite cases++-inj₂ (A ∷ B ∷ Ψ) Φ [] A' = eq

act⋆-ex-cxt-fma : {S : Stp} {Λ : Cxt} (Γ Δ : Cxt) {A C : Fma}
    → (f : S ∣ Γ ؛ Δ ++ A ∷ Λ ⊢c C)
    → ex-cxt-fma-c {Ω = []} Δ (act⋆ Γ (Δ ++ A ∷ Λ) f) ≡ act⋆ (Γ ++ A ∷ []) (Δ ++ Λ) (ex f refl refl)
act⋆-ex-cxt-fma {Λ = Λ} Γ [] {A} f = refl
act⋆-ex-cxt-fma {Λ = Λ} Γ (A ∷ Δ) {A₁} f =
    trans (cong (λ x → ex-c Γ x) (act⋆-ex-cxt-fma (Γ ++ A ∷ []) Δ (act Γ f))) 
    (trans (ex-c-act⋆ Γ (Δ ++ Λ) (ex (act Γ f) refl refl)) (cong (act⋆ (Γ ++ A₁ ∷ A ∷ []) (Δ ++ Λ) {Δ = []}) lem))
    where lem : (ex-c Γ (ex (act Γ f) refl refl)) ≡ (act (Γ ++ A₁ ∷ []) (ex {Δ = A ∷ Δ} f refl refl))
          lem rewrite cases++-inj₂ (A ∷ []) Γ [] A₁ |
                      snoc≡-refl Γ A = refl
                      
act⋆⊗l-c : (Φ Γ : Cxt) {Δ : Cxt} {A B : Fma} {C : Pos} {f : just A ∣ B ∷ Φ ؛ Γ ++ Δ ⊢c pos C}
    → ⊗l-c {Δ = Δ} (act⋆ (B ∷ Φ) Γ f) ≡ act⋆ Φ Γ (⊗l-c f)
act⋆⊗l-c Φ [] = refl
act⋆⊗l-c Φ (A ∷ Γ) {C = C} = act⋆⊗l-c (Φ ++ A ∷ []) Γ {C = C}

PosEq : (C : Pos) → {snd : isPos (proj₁ C)} → proj₂ C ≡ snd
PosEq (` x , snd) = refl
PosEq (I , snd) = refl
PosEq (fst ⊗ fst₁ , snd) = refl


⊗l-c-eq : {Φ Γ : Cxt} {A B : Fma} {C : Pos}
    → (f : just A ∣ Φ ؛ Γ ⊢c pos C)
    → (eq : Φ ≡ B ∷ [])
    → ⊗l-c' f eq ≡ ri2c (li2ri {C = C} (⊗l (subst (λ x → just A ∣ x ؛ Γ ⊢c pos C) eq f)))
⊗l-c-eq (ex {Γ = []} (ex {Γ = Γ} f eq'' eq₂) eq' eq₁) eq = ⊥-elim ([]disj∷ Γ eq'')
⊗l-c-eq {C = .(pos (` x , snd₁)) , snd} (ex {Γ = []} (ri2c (li2ri {C = ` x , snd₁} f)) refl refl) refl = refl
⊗l-c-eq {C = .(pos (I , snd₁)) , snd} (ex {Γ = []} (ri2c (li2ri {C = I , snd₁} f)) refl refl) refl = refl
⊗l-c-eq {C = .(pos (C ⊗ C₁ , snd₁)) , snd} (ex {Γ = []} (ri2c (li2ri {C = C ⊗ C₁ , snd₁} f)) refl refl) refl = refl
⊗l-c-eq (ex {Γ = x ∷ Γ} f refl refl) eq = ⊥-elim ([]disj∷ Γ (sym ((proj₂ (inj∷ eq)))))

act⋆pass-c : (Φ Γ : Cxt) {Φ' Δ : Cxt} {A C : Fma}
    → (f : just A ∣ Φ ؛ Γ ++ Δ ⊢c C) (eq : Φ' ≡ A ∷ Φ)
    → pass-c' {Δ = Δ} (act⋆ Φ Γ f) (cong (_++ Γ) eq)  ≡ act⋆ Φ' Γ (pass-c' f eq)
act⋆pass-c Φ [] f refl = refl
act⋆pass-c Φ (A ∷ Γ) f refl = act⋆pass-c (Φ ++ A ∷ []) Γ (act Φ f) refl

act⋆⊸l-c : (Φ Φ' Γ' : Cxt) {Δ' : Cxt} {A B C : Fma}
    → (f : - ∣ [] ؛ Φ ⊢c A) (g : just B ∣ Φ' ؛ Γ' ++ Δ' ⊢c C)
    → ⊸l-c {Δ = Δ'} (act⋆ [] Φ f) (act⋆ Φ' Γ' g) ≡ act⋆ (Φ ++ Φ') Γ' (⊸l-c (act⋆ [] Φ f) g)
act⋆⊸l-c Φ Φ' [] f g = refl
act⋆⊸l-c Φ Φ' (A ∷ Γ') f g = act⋆⊸l-c Φ (Φ' ++ A ∷ []) Γ' f (act Φ' g)

act⋆⊸l-c-ri : (Φ Γ : Cxt) {Δ Δ' : Cxt} {A B C : Fma}
    → (f : - ∣ Φ ؛ Γ ++ Δ ⊢c A) (g : just B ∣ Δ' ⊢ri C)
    → ⊸l-c-ri {Γ = Δ} (act⋆ Φ Γ f) g ≡ act⋆ Φ Γ (⊸l-c-ri f g)
act⋆⊸l-c-ri Φ [] f g = refl
act⋆⊸l-c-ri Φ (A ∷ Γ) f g = act⋆⊸l-c-ri (Φ ++ A ∷ []) Γ (act Φ f) g

act⋆act⋆ : {S : Stp} (Φ Γ Δ : Cxt) {Δ' : Cxt} {C : Fma}
    → {f : S ∣ Φ ؛ Γ ++ Δ ++ Δ' ⊢c C}
    → act⋆ (Φ ++ Γ) Δ {Δ = Δ'} (act⋆ Φ Γ f) ≡ act⋆ Φ (Γ ++ Δ) f
act⋆act⋆ Φ [] Δ = refl
act⋆act⋆ Φ (A ∷ Γ) Δ = act⋆act⋆ (Φ ++ A ∷ []) Γ Δ

act⋆⊗r-c : {S : Stp} (Φ Φ' Γ' : Cxt) {Δ' : Cxt} {A B : Fma}
    → (f : S ∣ [] ؛ Φ ⊢c A) (g : - ∣ Φ' ؛ Γ' ++ Δ' ⊢c B)
    → ⊗r-c {Δ = Δ'} (act⋆ [] Φ f) (act⋆ Φ' Γ' g) ≡ act⋆ (Φ ++ Φ') Γ' (⊗r-c (act⋆ [] Φ f) g)
act⋆⊗r-c Φ Φ' [] f g = refl
act⋆⊗r-c Φ Φ' (A ∷ Γ') f g = act⋆⊗r-c Φ (Φ' ++ A ∷ []) Γ' f (act Φ' g)

act⋆⊗r-c-ri : {S : Stp} (Φ Γ : Cxt) {Δ Δ' : Cxt} {A B : Fma}
    → (f : S ∣ Φ ؛ Γ ++ Δ ⊢c A) (g : - ∣ Δ' ⊢ri B)
    → ⊗r-c-ri {Γ = Δ} (act⋆ Φ Γ f) g ≡ act⋆ Φ Γ (⊗r-c-ri f g)
act⋆⊗r-c-ri Φ [] f g = refl
act⋆⊗r-c-ri Φ (A ∷ Γ) f g = act⋆⊗r-c-ri (Φ ++ A ∷ []) Γ (act Φ f) g



tagL++? : (Γ₀ Γ₁ : TCxt) → (Γ : Cxt)
    → (eq : tagL Γ ≡ Γ₀ ++ Γ₁) → Σ (Cxt) λ Γ₀' → Σ (Cxt) λ Γ₁' → Γ ≡ Γ₀' ++ Γ₁' × Γ₀ ≡ tagL Γ₀'  × Γ₁ ≡ tagL Γ₁'
tagL++? Γ₀ Γ₁ [] eq with []++? {xs = Γ₀} {Γ₁} eq
tagL++? .[] .[] [] refl | refl , refl = [] , [] , refl , refl , refl
tagL++? [] .(tagL (x ∷ Γ)) (x ∷ Γ) refl = [] , (x ∷ Γ) , refl , refl , refl
tagL++? (x₁ ∷ Γ₀) Γ₁ (x ∷ Γ) eq with inj∷ eq
... | refl , eq1 with tagL++? Γ₀ Γ₁ Γ eq1
... | Γ₀' , Γ₁' , refl , refl , refl = x ∷ Γ₀' , Γ₁' , refl , refl , refl 

black++? : (Γ₀ Γ₁ : TCxt) → (Γ : Cxt)
    → (eq : black Γ ≡ Γ₀ ++ Γ₁) → Σ (Cxt) λ Γ₀' → Σ (Cxt) λ Γ₁' → Γ ≡ Γ₀' ++ Γ₁' × Γ₀ ≡ black Γ₀'  × Γ₁ ≡ black Γ₁'
black++? Γ₀ Γ₁ [] eq with []++? {xs = Γ₀} {Γ₁} eq
black++? .[] .[] [] refl | refl , refl = [] , [] , refl , refl , refl
black++? [] .(black (x ∷ Γ)) (x ∷ Γ) refl = [] , (x ∷ Γ) , refl , refl , refl
black++? (x₁ ∷ Γ₀) Γ₁ (x ∷ Γ) eq with inj∷ eq
... | refl , eq1 with black++? Γ₀ Γ₁ Γ eq1
... | Γ₀' , Γ₁' , refl , refl , refl = x ∷ Γ₀' , Γ₁' , refl , refl , refl


ersL-isInter-Cxt : (Γ₀ Γ₁ : Cxt) (Γ : TCxt) → (inTeq : isInter (tagL Γ₀) (black Γ₁) Γ) → Cxt
ersL-isInter-Cxt [] [] .[] isInter[] = []
ersL-isInter-Cxt [] (x ∷ Γ₁) .((∙ , x) ∷ black Γ₁) []left = x ∷ Γ₁
ersL-isInter-Cxt (x ∷ Γ₀) [] .((∘ , x) ∷ tagL Γ₀) []right = x ∷ Γ₀
ersL-isInter-Cxt (x ∷ Γ₀) (x₁ ∷ Γ₁) .((∘ , x) ∷ _) (∷left inTeq) = x ∷ (ersL-isInter-Cxt Γ₀ (x₁ ∷ Γ₁) _ inTeq)
ersL-isInter-Cxt (x ∷ Γ₀) (x₁ ∷ Γ₁) .((∙ , x₁) ∷ _) (∷right inTeq) = x₁ ∷ (ersL-isInter-Cxt (x ∷ Γ₀) Γ₁ _ inTeq)


ersL-isInter-Cxt-eq : (Γ₀ Γ₁ : Cxt) (Γ : TCxt) → (inTeq : isInter (tagL Γ₀) (black Γ₁) Γ) → ersL-isInter-Cxt Γ₀ Γ₁ Γ inTeq ≡ ersL Γ
ersL-isInter-Cxt-eq [] [] .[] isInter[] = refl
ersL-isInter-Cxt-eq [] (x ∷ Γ₁) .((∙ , x) ∷ black Γ₁) []left = refl
ersL-isInter-Cxt-eq (x ∷ Γ₀) [] .((∘ , x) ∷ tagL Γ₀) []right = refl
ersL-isInter-Cxt-eq (x ∷ Γ₀) (x₁ ∷ Γ₁) .((∘ , x) ∷ _) (∷left inTeq) = cong (x ∷_) (ersL-isInter-Cxt-eq Γ₀ (x₁ ∷ Γ₁) _ inTeq)
ersL-isInter-Cxt-eq (x ∷ Γ₀) (x₁ ∷ Γ₁) .((∙ , x₁) ∷ _) (∷right inTeq) = cong (x₁ ∷_) (ersL-isInter-Cxt-eq (x ∷ Γ₀) Γ₁ _ inTeq)
{-# REWRITE ersL-isInter-Cxt-eq #-}

ersL-isInter' : (Γ₀ Γ₁ : Cxt) (Γ : TCxt) → (inTeq : isInter (tagL Γ₀) (black Γ₁) Γ) 
    → isInter Γ₀ Γ₁ (ersL-isInter-Cxt Γ₀ Γ₁ Γ inTeq)
ersL-isInter' [] [] .[] isInter[] = isInter[]
ersL-isInter' [] (x ∷ Γ₁) .((∙ , x) ∷ black Γ₁) []left = []left
ersL-isInter' (x ∷ Γ₀) [] .((∘ , x) ∷ tagL Γ₀) []right = []right
ersL-isInter' (x ∷ Γ₀) (x₁ ∷ Γ₁) ((∘ , x) ∷ Γ) (∷left inTeq) = ∷left (ersL-isInter' Γ₀ (x₁ ∷ Γ₁) Γ inTeq)
ersL-isInter' (x ∷ Γ₀) (x₁ ∷ Γ₁) ((∙ , x₁) ∷ Γ) (∷right inTeq) = ∷right (ersL-isInter' (x ∷ Γ₀) Γ₁ Γ inTeq)

ersL-isInter'-∷right'∙ : {x : Fma} (Γ₀ Γ₁ : Cxt) {Γ : TCxt} → (inTeq : isInter (tagL Γ₀) (black Γ₁) Γ)
    → ersL-isInter' Γ₀ (x ∷ Γ₁) ((∙ , x) ∷ Γ) (∷right' {x = (∙ , x)} (tagL Γ₀) inTeq) ≡ ∷right' {x = x} Γ₀ (ersL-isInter' Γ₀ Γ₁ Γ inTeq)
ersL-isInter'-∷right'∙ [] [] isInter[] = refl
ersL-isInter'-∷right'∙ [] (x ∷ Γ₁) []left = refl
ersL-isInter'-∷right'∙ (x ∷ Γ₀) [] inTeq = refl
ersL-isInter'-∷right'∙ (x ∷ Γ₀) (x₁ ∷ Γ₁) inTeq = refl

tag-isInter-ersL-isInter-refl' : (Γ₀ Γ₁ : Cxt) (Γ : TCxt) → (inTeq : isInter (tagL Γ₀) (black Γ₁) Γ) 
    → tag-isInter (ersL-isInter' Γ₀ Γ₁ Γ inTeq) ≡ Γ
tag-isInter-ersL-isInter-refl' [] [] .[] isInter[] = refl
tag-isInter-ersL-isInter-refl' [] (x ∷ Γ₁) .((∙ , x) ∷ black Γ₁) []left = refl
tag-isInter-ersL-isInter-refl' (x ∷ Γ₀) [] .((∘ , x) ∷ tagL Γ₀) []right = refl
tag-isInter-ersL-isInter-refl' (x ∷ Γ₀) (x₁ ∷ Γ₁) ((∘ , x) ∷ Γ) (∷left inTeq) = 
    cong ((∘ , x) ∷_) (tag-isInter-ersL-isInter-refl' Γ₀ (x₁ ∷ Γ₁) Γ inTeq)
tag-isInter-ersL-isInter-refl' (x ∷ Γ₀) (x₁ ∷ Γ₁) ((∙ , x₁) ∷ Γ) (∷right inTeq) = 
    cong ((∙ , x₁) ∷_) (tag-isInter-ersL-isInter-refl' (x ∷ Γ₀) Γ₁ Γ inTeq)
{-# REWRITE tag-isInter-ersL-isInter-refl' #-}


tag-lem-ersL-refl' : (Γ₀ Γ₁ : Cxt) (Γ : TCxt) →  (inTeq : isInter (tagL Γ₀) (black Γ₁) Γ) 
    → tag-lem' (ersL-isInter' Γ₀ Γ₁ Γ inTeq) ≡ inTeq
tag-lem-ersL-refl' [] [] .[] isInter[] = refl
tag-lem-ersL-refl' [] (x ∷ Γ₁) .((∙ , x) ∷ black Γ₁) []left = refl
tag-lem-ersL-refl' (x ∷ Γ₀) [] .((∘ , x) ∷ tagL Γ₀) []right = refl
tag-lem-ersL-refl' (x ∷ Γ₀) (x₁ ∷ Γ₁) ((∘ , x) ∷ Γ) (∷left inTeq) = cong ∷left (tag-lem-ersL-refl' Γ₀ (x₁ ∷ Γ₁) Γ inTeq) 
tag-lem-ersL-refl' (x ∷ Γ₀) (x₁ ∷ Γ₁) ((∙ , x₁) ∷ Γ) (∷right inTeq) = cong ∷right (tag-lem-ersL-refl' (x ∷ Γ₀) Γ₁ Γ inTeq)  

ersL-isInter++'-r : {x : Fma} (Γ₀ Δ₀ Δ₁ : Cxt) {Δ : TCxt} (inTeq : isInter (tagL Δ₀) (black Δ₁) Δ)
    → ersL-isInter' Δ₀ (x ∷ Γ₀ ++ Δ₁) ((∙ , x) ∷ black Γ₀ ++ Δ) (isInter++r ((∙ , x) ∷ black Γ₀) inTeq)
        ≡ isInter++r (x ∷ Γ₀) (ersL-isInter' Δ₀ Δ₁ Δ inTeq)
ersL-isInter++'-r [] [] [] isInter[] = refl
ersL-isInter++'-r [] [] (x ∷ Δ₁) []left = refl
ersL-isInter++'-r [] (x ∷ Δ₀) [] inTeq = refl
ersL-isInter++'-r [] (x ∷ Δ₀) (x₁ ∷ Δ₁) inTeq = refl
ersL-isInter++'-r (x ∷ Γ₀) [] [] isInter[] = refl
ersL-isInter++'-r (x ∷ Γ₀) [] (x₁ ∷ Δ₁) []left = refl
ersL-isInter++'-r (x ∷ Γ₀) (x₁ ∷ Δ₀) [] []right = cong ∷right (ersL-isInter++'-r Γ₀ (x₁ ∷ Δ₀) [] []right)
ersL-isInter++'-r (x ∷ Γ₀) (x₁ ∷ Δ₀) (x₂ ∷ Δ₁) inTeq = cong ∷right (ersL-isInter++'-r Γ₀ (x₁ ∷ Δ₀) (x₂ ∷ Δ₁) inTeq)

ersL-isInter++'-l : {x : Fma} (Γ₀ Δ₀ Δ₁ : Cxt) {Δ : TCxt} (inTeq : isInter (tagL Δ₀) (black Δ₁) Δ)
    → ersL-isInter' (x ∷ Γ₀ ++ Δ₀) Δ₁ ((∘ , x) ∷ tagL Γ₀ ++ Δ) (isInter++l ((∘ , x) ∷ tagL Γ₀) inTeq)
        ≡ isInter++l (x ∷ Γ₀) (ersL-isInter' Δ₀ Δ₁ Δ inTeq)
ersL-isInter++'-l [] [] [] isInter[] = refl
ersL-isInter++'-l [] [] (x ∷ Δ₁) inTeq = refl
ersL-isInter++'-l [] (x ∷ Δ₀) [] []right = refl
ersL-isInter++'-l [] (x ∷ Δ₀) (x₁ ∷ Δ₁) inTeq = refl
ersL-isInter++'-l (x ∷ Γ₀) [] [] isInter[] = refl
ersL-isInter++'-l (x ∷ Γ₀) [] (x₁ ∷ Δ₁) inTeq = cong ∷left (ersL-isInter++'-l Γ₀ [] (x₁ ∷ Δ₁) inTeq)
ersL-isInter++'-l (x ∷ Γ₀) (x₁ ∷ Δ₀) [] []right = refl
ersL-isInter++'-l (x ∷ Γ₀) (x₁ ∷ Δ₀) (x₂ ∷ Δ₁) inTeq = cong ∷left (ersL-isInter++'-l Γ₀ (x₁ ∷ Δ₀) (x₂ ∷ Δ₁) inTeq)

-- ==========
ersL-isInter++'-l₁ : (Γ₀ Δ₀ Δ₁ : Cxt) {Δ : TCxt} (inTeq : isInter (tagL Δ₀) (black Δ₁) Δ)
    → ersL-isInter' (Γ₀ ++ Δ₀) Δ₁ (tagL Γ₀ ++ Δ) (isInter++l (tagL Γ₀) inTeq)
        ≡ isInter++l (Γ₀) (ersL-isInter' Δ₀ Δ₁ Δ inTeq)
ersL-isInter++'-l₁ [] [] [] inTeq = refl
ersL-isInter++'-l₁ [] [] (x ∷ Δ₁) inTeq = refl
ersL-isInter++'-l₁ [] (x ∷ Δ₀) [] inTeq = refl
ersL-isInter++'-l₁ [] (x ∷ Δ₀) (x₁ ∷ Δ₁) inTeq = refl
ersL-isInter++'-l₁ (x ∷ Γ₀) [] [] isInter[] = refl
ersL-isInter++'-l₁ (x ∷ Γ₀) [] (x₁ ∷ Δ₁) []left = cong ∷left (ersL-isInter++'-l₁ Γ₀ [] (x₁ ∷ Δ₁) []left)
ersL-isInter++'-l₁ (x ∷ Γ₀) (x₁ ∷ Δ₀) [] []right = refl
ersL-isInter++'-l₁ (x ∷ Γ₀) (x₁ ∷ Δ₀) (x₂ ∷ Δ₁) inTeq = cong ∷left (ersL-isInter++'-l₁ Γ₀ (x₁ ∷ Δ₀) (x₂ ∷ Δ₁) inTeq)
-- ==========

ersL-isInter++' : (Γ₀ Γ₁ Δ₀ Δ₁ : Cxt) {Γ Δ : TCxt}
    → (inTeq1 : isInter (tagL Γ₀) (black Γ₁) Γ) (inTeq2 : isInter (tagL Δ₀) (black Δ₁) Δ)
    → ersL-isInter' (Γ₀ ++ Δ₀) (Γ₁ ++ Δ₁) (Γ ++ Δ) (isInter++ inTeq1 inTeq2) 
        ≡ isInter++ (ersL-isInter' Γ₀ Γ₁ Γ inTeq1) (ersL-isInter' Δ₀ Δ₁ Δ inTeq2)
ersL-isInter++' [] [] Δ₀ Δ₁ isInter[] inTeq2 = refl
ersL-isInter++' [] (x ∷ Γ₁) Δ₀ Δ₁ []left inTeq2 = ersL-isInter++'-r Γ₁ Δ₀ Δ₁ inTeq2
ersL-isInter++' (x ∷ Γ₀) [] Δ₀ Δ₁ []right inTeq2 = ersL-isInter++'-l Γ₀ Δ₀ Δ₁ inTeq2
ersL-isInter++' (x ∷ Γ₀) (x₁ ∷ Γ₁) Δ₀ Δ₁ (∷left inTeq1) inTeq2 = cong ∷left (ersL-isInter++' Γ₀ (x₁ ∷ Γ₁) Δ₀ Δ₁ inTeq1 inTeq2 )
ersL-isInter++' (x ∷ Γ₀) (x₁ ∷ Γ₁) Δ₀ Δ₁ (∷right inTeq1) inTeq2 = cong ∷right (ersL-isInter++' (x ∷ Γ₀) Γ₁ Δ₀ Δ₁ inTeq1 inTeq2 )



ersL-isInter-[]right'-refl : (Γ : Cxt) → ersL-isInter ([]right' (tagL Γ)) ≡ []right' Γ
ersL-isInter-[]right'-refl [] = refl
ersL-isInter-[]right'-refl (x ∷ Γ) = refl
{-# REWRITE ersL-isInter-[]right'-refl #-}

ersL-isInter-[]right'-whiteL-refl : (Γ : TCxt) → ersL-isInter ([]right' (whiteL Γ)) ≡ []right' (ersL Γ)
ersL-isInter-[]right'-whiteL-refl [] = refl
ersL-isInter-[]right'-whiteL-refl ((∘ , A) ∷ Γ) = refl
ersL-isInter-[]right'-whiteL-refl ((∙ , A) ∷ Γ) = refl
{-# REWRITE ersL-isInter-[]right'-whiteL-refl #-}

⊸r⋆∙[] : {S : Stp} {Γ : TCxt} {A : Fma}
    → (f : ∙ ∣ S ∣ Γ ⊢ri A) (inTeq : isInter Γ [] Γ)
    → ⊸r⋆∙ [] f inTeq (empty refl) refl ≡ f
⊸r⋆∙[] f isInter[] = refl
⊸r⋆∙[] f []right = refl

⊸r⋆∙⊸r∙ : {S : Stp} {Δ₀ Δ Λ₀ Λ Ω : TCxt} {Δ₁ Λ₁ : Cxt} (Γ₁ : Cxt) {A C : Fma}
    → (f : ∙ ∣ S ∣ Ω ⊢ri C) (eq : Ω ≡ Δ ++ (∙ , A) ∷ Λ) (inTeq1 : isInter Δ₀ (black Δ₁) Δ) (inTeq2 : isInter Λ₀ (black Λ₁) Λ) (peq : Δ₁ ++ Λ₁ ↭' Γ₁)
    → ⊸r⋆∙ {Γ₁' = Δ₁ ++ A ∷ Λ₁} (Γ₁ ++ A ∷ []) f (subst (λ x → isInter (Δ₀ ++ Λ₀) (black Δ₁ ++ (∙ , A) ∷ black Λ₁) x) (sym eq) (isInter++ inTeq1 (∷right' {x = (∙ , A)} Λ₀ inTeq2))) ((snoc↭' {xs₀ = Δ₁} {Λ₁} refl peq)) refl ≡ ⊸r⋆∙ Γ₁ (⊸r∙ (ex∙ (ri2c f) refl eq)) (isInter++ inTeq1 inTeq2) peq refl
⊸r⋆∙⊸r∙ {Δ₁ = Δ₁} {Λ₁} [] f refl inTeq1 inTeq2 (empty x) with []++? {xs = Δ₁} {Λ₁} (sym x)
⊸r⋆∙⊸r∙ {Δ₁ = .[]} {.[]} [] f refl isInter[] isInter[] (empty refl) | refl , refl = refl
⊸r⋆∙⊸r∙ {Δ₁ = .[]} {.[]} [] f refl isInter[] []right (empty refl) | refl , refl = refl
⊸r⋆∙⊸r∙ {Δ₁ = .[]} {.[]} [] {A} f refl ([]right {x = x} {xs = xs}) isInter[] (empty refl) | refl , refl 
    rewrite isInter-split-r-++-refl {x = (∙ , A)} ([]right {x = x} {xs = xs}) isInter[] = refl
⊸r⋆∙⊸r∙ {Δ₁ = .[]} {.[]} [] {A} f refl ([]right {x = x₁} {xs₁}) ([]right {x = x} {xs}) (empty refl) | refl , refl 
    rewrite isInter-split-r-++-refl {x = (∙ , A)} ([]right {x = x₁} {xs = xs₁}) ([]right {x = x} {xs}) = refl
⊸r⋆∙⊸r∙ {Δ₁ = Δ₁} {Λ₁} (A' ∷ Γ₁) {A} f eq inTeq1 inTeq2 (cons {xs₀ = Φ₀} {Φ₁} eq1 peq) with cases++ Φ₀ Δ₁ Φ₁ Λ₁ eq1
⊸r⋆∙⊸r∙ {Λ₀ = Λ₀} {Δ₁ = .(Φ₀ ++ A' ∷ Ω₀)} {Λ₁} (A' ∷ Γ₁) {A} f refl inTeq1 inTeq2 (cons {xs₀ = Φ₀} {.(Ω₀ ++ Λ₁)} refl peq) | inj₁ (Ω₀ , refl , refl) with isInter-split-r (black Φ₀) (black Ω₀) refl inTeq1
... | Ξ₀ , Ξ₁ , Ψ₀ , Ψ₁ , inTeq' , inTeq'' , refl , refl , refl 
    rewrite sym (isInter++-assoc inTeq' (∷right' {x = (∙ , A')} Ξ₁ inTeq'') inTeq2) |
            isInter++-∷right' {x = (∙ , A')} Ξ₁ inTeq'' inTeq2 |
            isInter-split-r-++-refl {x = (∙ , A')} inTeq' (isInter++ inTeq'' inTeq2) |
            sym (isInter++-assoc inTeq' (∷right' {x = (∙ , A')} Ξ₁ inTeq'') (∷right' {x = (∙ , A)} Λ₀ inTeq2)) |
            isInter++-∷right' {x = (∙ , A')} Ξ₁ inTeq'' (∷right' {x = (∙ , A)} Λ₀ inTeq2) |
            isInter-split-r-++-refl {x = (∙ , A')} inTeq' (isInter++ inTeq'' (∷right' {x = (∙ , A)} Λ₀ inTeq2)) |
            isInter++-∷left' {x = (∙ , A')} (black Ω₀) inTeq'' (∷right' {x = (∙ , A)} Λ₀ inTeq2) |
            isInter++-assoc inTeq' (∷left' {x = (∙ , A')} (black Ω₀) inTeq'') (∷right' {x = (∙ , A)} Λ₀ inTeq2) |
            isInter++-∷left' {x = (∙ , A')} (black Ω₀) inTeq'' inTeq2 |
            isInter++-assoc inTeq' (∷left' {x = (∙ , A')} (black Ω₀) inTeq'') inTeq2 |
            ⊸r⋆∙⊸r∙ {Δ = Ψ₀ ++ (∙ , A') ∷ Ψ₁} {Δ₁ = Φ₀ ++ Ω₀} {Λ₁ = Λ₁} Γ₁ f refl (isInter++ inTeq' (∷left' {x = (∙ , A')} (black Ω₀) inTeq'')) inTeq2 peq = refl
⊸r⋆∙⊸r∙ {Δ = Δ} {Δ₁ = Δ₁} {.(Ω₀ ++ A' ∷ Φ₁)} (A' ∷ Γ₁) {A} f refl inTeq1 inTeq2 (cons {xs₀ = .(Δ₁ ++ Ω₀)} {Φ₁} refl peq) | inj₂ (Ω₀ , refl , refl) with isInter-split-r (black Ω₀) (black Φ₁) refl inTeq2
... | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq' , inTeq'' , refl , refl , refl 
    rewrite isInter++-assoc inTeq1 inTeq' (∷right' {x = (∙ , A')} Λ₁ inTeq'') |
            isInter-split-r-++-refl {x = (∙ , A')} (isInter++ inTeq1 inTeq') inTeq'' | 
            sym (isInter++-∷right' {x = (∙ , A)} Λ₀ inTeq' (∷right' {x = (∙ , A')} Λ₁ inTeq'')) |
            isInter++-assoc inTeq1 (∷right' {x = (∙ , A)} Λ₀ inTeq') (∷right' {x = (∙ , A')} Λ₁ inTeq'') |
            isInter-split-r-++-refl {x = (∙ , A')} (isInter++ inTeq1 (∷right' {x = (∙ , A)} Λ₀ inTeq')) inTeq'' | 
            sym (isInter++-assoc inTeq1 (∷right' {x = (∙ , A)} Λ₀ inTeq') (∷left' {x = (∙ , A')} (black Φ₁) inTeq'')) |
            sym (isInter++-assoc inTeq1 inTeq' (∷left' {x = (∙ , A')} (black Φ₁) inTeq'')) | 
            isInter++-∷right' {x = (∙ , A)} Λ₀ inTeq' (∷left' {x = (∙ , A')} (black Φ₁) inTeq'') |
            ⊸r⋆∙⊸r∙ {Δ₁ = Δ₁} {Λ₁ = Ω₀ ++ Φ₁} Γ₁ f refl inTeq1 (isInter++ inTeq' (∷left' {x = (∙ , A')} (black Φ₁) inTeq'')) peq = refl


tag-isInter⊥ : (Γ₀ Γ₁ Γ₁' Γ : Cxt) {A : Fma} → (inTeq : isInter (tagL Γ₀) (black Γ₁ ++ (∙ , A) ∷ black Γ₁') (tagL Γ)) → ⊥
tag-isInter⊥ [] [] Γ₁' [] ()
tag-isInter⊥ [] [] Γ₁' (x ∷ Γ) ()
tag-isInter⊥ (x ∷ Γ₀) [] Γ₁' (.x ∷ Γ) (∷left inTeq) = tag-isInter⊥ Γ₀ [] Γ₁' Γ inTeq
tag-isInter⊥ (x₁ ∷ Γ₀) (x ∷ Γ₁) Γ₁' (.x₁ ∷ Γ) (∷left inTeq) = tag-isInter⊥ Γ₀ (x ∷ Γ₁) Γ₁' Γ inTeq

tag-isInter[]⊥ : (Γ₀ Γ : Cxt) (Γ' : TCxt) {A : Fma} → (inTeq : isInter (tagL Γ₀) [] (tagL Γ ++ (∙ , A) ∷ Γ')) → ⊥
tag-isInter[]⊥  [] [] Γ' ()
tag-isInter[]⊥ (x ∷ Γ₀) [] Γ' ()
tag-isInter[]⊥ (x ∷ Γ₀) (x₁ ∷ Γ) Γ' inTeq with isInter++? ((∘ , x₁) ∷ tagL Γ) ((∙ , _) ∷ Γ') refl inTeq
... | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq1 , inTeq2 , eq1 , eq2 , eq3 with tagL++? Λ₀ Λ₁ (x ∷ Γ₀) eq1
tag-isInter[]⊥ (x ∷ Γ₀) (x₁ ∷ Γ) Γ' inTeq | .(tagL []) , .(tagL (x ∷ Γ₀)) , .((∘ , x₁) ∷ tagL Γ) , Ψ₁ , []left , inTeq2 , refl , eq2 , eq3 | [] , .(x ∷ Γ₀) , refl , refl , refl = []disj∷ [] (sym (proj₁ ([]++? {xs = ((∘ , x₁) ∷ tagL Γ)} {Ψ₁} eq2)) )
tag-isInter[]⊥ (x ∷ .(Λ₀' ++ Λ₁')) (x₁ ∷ Γ) Γ' inTeq | .(tagL (x ∷ Λ₀')) , .(tagL Λ₁') , Ψ₀ , Ψ₁ , inTeq1 , inTeq2 , refl , eq2 , eq3 | .x ∷ Λ₀' , Λ₁' , refl , refl , refl with []++? {xs = Ψ₀} {Ψ₁} eq2
tag-isInter[]⊥ (x ∷ .(Λ₀' ++ [])) (x₁ ∷ Γ) Γ' .(isInter++ {xs' = []} {zs' = (∙ , _) ∷ Γ'} inTeq1 _) | .(tagL (x ∷ Λ₀')) , .(tagL []) , .[] , .[] , inTeq1 , () , refl , refl , refl | .x ∷ Λ₀' , [] , refl , refl , refl | refl , refl
tag-isInter[]⊥ (x ∷ .(Λ₀' ++ x₂ ∷ Λ₁')) (x₁ ∷ Γ) Γ' .(isInter++ {xs' = (∘ , x₂) ∷ tagL Λ₁'} {zs' = (∙ , _) ∷ Γ'} inTeq1 _) | .(tagL (x ∷ Λ₀')) , .(tagL (x₂ ∷ Λ₁')) , .[] , .[] , inTeq1 , () , refl , refl , refl | .x ∷ Λ₀' , x₂ ∷ Λ₁' , refl , refl , refl | refl , refl

-- =============
tag-isInter[]⊥₁ : (Γ₁ Γ : Cxt) (Γ' : TCxt) {A B : Fma} (inTeq : isInter [] (black Γ₁) ((∘ , B) ∷ tagL Γ ++ (∙ , A) ∷ Γ')) → ⊥
tag-isInter[]⊥₁ [] [] Γ' ()
tag-isInter[]⊥₁ [] (x ∷ Γ) Γ' ()
tag-isInter[]⊥₁ (x ∷ Γ₁) [] Γ' ()
tag-isInter[]⊥₁ (x ∷ Γ₁) (x₁ ∷ Γ) Γ' ()

isInter++r-∷right' : {X : Set} → {x : X} → {xs ys zs : List X} → (ys₀ : List X) (inTeq : isInter xs ys zs)
    → isInter++r (x ∷ ys₀) inTeq ≡ ∷right' {x = x} xs (isInter++r ys₀ inTeq)
isInter++r-∷right' [] isInter[] = refl
isInter++r-∷right' [] []left = refl
isInter++r-∷right' [] []right = refl
isInter++r-∷right' [] (∷left inTeq) = refl
isInter++r-∷right' [] (∷right inTeq) = refl
isInter++r-∷right' (x ∷ ys₀) isInter[] = refl
isInter++r-∷right' (x ∷ ys₀) []left = refl
isInter++r-∷right' (x ∷ ys₀) []right = refl
isInter++r-∷right' (x ∷ ys₀) (∷left inTeq) = refl
isInter++r-∷right' (x ∷ ys₀) (∷right inTeq) = refl
-- ==============


gen⊗r-eq-f' : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ : TCxt} (Γ₁ : Cxt) {A : Pos} {B : Fma} 
    → (f : ∙ ∣ S ∣ Γ ⊢f A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter (tagL Γ₀) (black Γ₁') Γ) (peq : Γ₁' ↭' Γ₁)
    → gen⊗r-f Γ₁ (f∙2f f) g (ersL-isInter' Γ₀ Γ₁' Γ inTeq) peq 
        ≡ ⊗r (⊸r⋆∙ Γ₁ (li2ri (p2li (f2p f))) inTeq peq refl) g
gen⊗r-eq-f' {Γ₀ = []} {[]} .[] ax g isInter[] (empty refl) = refl
gen⊗r-eq-f' {Γ₀ = []} {[]} .(_ ∷ _) ax g isInter[] (cons {xs₀ = xs₀} x peq) = ⊥-elim ([]disj∷ xs₀ x)
gen⊗r-eq-f' {Γ₀ = []} {[]} .[] Ir g isInter[] (empty refl) = refl
gen⊗r-eq-f' {Γ₀ = []} {[]} .(_ ∷ _) Ir g isInter[] (cons {xs₀ = xs₀} x peq) = ⊥-elim ([]disj∷ xs₀ x)
gen⊗r-eq-f' Γ₁ (⊗r∙ {Γ = Γ} {Δ} f g) h inTeq peq with isInter++? Γ Δ refl inTeq 
gen⊗r-eq-f' {Γ₀ = Γ₀} {Γ₁'} Γ₁ (⊗r∙ {Γ = Γ} {Δ} f g) h inTeq peq | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq1 , inTeq2 , eq1 , eq2 , eq3 with tagL++? Λ₀ Λ₁ Γ₀ eq1 | black++? Ψ₀ Ψ₁ Γ₁' eq2 
gen⊗r-eq-f' {Γ₀ = .(Λ₀' ++ Λ₁')} {.(Ψ₀' ++ Ψ₁')} Γ₁ (⊗r∙ {Γ = Γ} {Δ} f g) h .(isInter++ inTeq1 inTeq2) peq | .(tagL Λ₀') , .(tagL Λ₁') , .(black Ψ₀') , .(black Ψ₁') , inTeq1 , inTeq2 , refl , refl , refl | Λ₀' , Λ₁' , refl , refl , refl | Ψ₀' , Ψ₁' , refl , refl , refl 
    rewrite ersL-isInter++' Λ₀' Ψ₀' Λ₁' Ψ₁' inTeq1 inTeq2 | 
            isInter++-refl (ersL-isInter' Λ₀' Ψ₀' Γ inTeq1) (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) |
            tag-lem-ersL-refl' Λ₀' Ψ₀' Γ inTeq1 |
            tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2 = refl
gen⊗r-eq-f' {Γ₀ = Γ₀} {Γ₁'} Γ₁ (⊸l∙ {Γ} {Λ = Λ} {Δ} {D = D} f g refl refl) h inTeq peq with isInter++? (Γ ++ (∙ , D) ∷ Λ) Δ refl inTeq
... | Λ₀ , Λ₁ , Ψ₀ , Ψ₁ , inTeq1 , inTeq2 , eq1 , eq2 , eq3 with tagL++? Λ₀ Λ₁ Γ₀ eq1 | black++? Ψ₀ Ψ₁ Γ₁' eq2
gen⊗r-eq-f' {Γ₀ = .([] ++ Λ₁')} {.((x ∷ []) ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL [])} {Γ'' = []} {Λ = .(black [])} {Δ} {D = x} f g refl refl) h .(isInter++ []left inTeq2) peq | .(tagL []) , .(tagL ([] ++ Λ₁')) , .(black (x ∷ [])) , .(black Ψ₁') , []left , inTeq2 , refl , refl , refl | [] , Λ₁' , refl , refl , refl | x ∷ [] , Ψ₁' , refl , refl , refl 
    rewrite ersL-isInter++' [] (x ∷ []) Λ₁' Ψ₁' []left inTeq2 |
            isInter++-refl ([]left {x = x} {[]}) (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) |
            tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2 | 
            isInter++r-∷right' {x = (∙ , x)} [] inTeq2 = refl
gen⊗r-eq-f' {Γ₀ = .([] ++ Λ₁')} {.((x ∷ x₁ ∷ Ψ₀') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL [])} {Γ'' = []} {Λ = .(black (x₁ ∷ Ψ₀'))} {Δ} {D = x} f g refl refl) h .(isInter++ []left inTeq2) peq | .(tagL []) , .(tagL ([] ++ Λ₁')) , .(black (x ∷ x₁ ∷ Ψ₀')) , .(black Ψ₁') , []left , inTeq2 , refl , refl , refl | [] , Λ₁' , refl , refl , refl | x ∷ x₁ ∷ Ψ₀' , Ψ₁' , refl , refl , refl 
    rewrite ersL-isInter++' [] (x ∷ x₁ ∷  Ψ₀') Λ₁' Ψ₁' []left inTeq2 |
            isInter++-refl ([]left {x = x} {x₁ ∷ Ψ₀'}) (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) |
            tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2 |
            isInter++r-∷right' {x = (∙ , x)} ((∙ , x₁) ∷ black Ψ₀') inTeq2 = refl

gen⊗r-eq-f' {Γ₀ = .((x ∷ Λ₀') ++ Λ₁')} {.((x₁ ∷ Ψ₀') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL [])} {Γ'' = []} {Λ = Λ} {Δ} {D = .x₁} f g refl refl) h .(isInter++ (∷right inTeq1) inTeq2) peq | .(tagL (x ∷ Λ₀')) , .(tagL Λ₁') , .(black (x₁ ∷ Ψ₀')) , .(black Ψ₁') , ∷right inTeq1 , inTeq2 , refl , refl , refl | x ∷ Λ₀' , Λ₁' , refl , refl , refl | x₁ ∷ Ψ₀' , Ψ₁' , refl , refl , refl 
    rewrite ersL-isInter++' (x ∷ Λ₀') Ψ₀' Λ₁' Ψ₁' inTeq1 inTeq2 |
            isInter++-refl (ersL-isInter' (x ∷ Λ₀') Ψ₀' Λ inTeq1) (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) |
            isInter-split-r-++-refl {x = x₁} isInter[] (ersL-isInter' (x ∷ Λ₀') Ψ₀' Λ inTeq1) |
            tag-lem-ersL-refl' (x ∷ Λ₀') Ψ₀' Λ inTeq1 |
            tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2 = refl
gen⊗r-eq-f' {Γ₀ = .((x₁ ∷ Λ₀') ++ Λ₁')} {.([] ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x ∷ Γ''))} {Γ'' = x ∷ Γ''} {Λ = Λ} {Δ} {D = D} f g refl refl) h .(isInter++ inTeq1 inTeq2) peq | .(tagL (x₁ ∷ Λ₀')) , .(tagL Λ₁') , .(black []) , .(black ([] ++ Ψ₁')) , inTeq1 , inTeq2 , refl , refl , refl | x₁ ∷ Λ₀' , Λ₁' , refl , refl , refl | [] , Ψ₁' , refl , refl , refl = ⊥-elim (tag-isInter[]⊥ (x₁ ∷ Λ₀') (x ∷ Γ'') Λ inTeq1) -- imposs
gen⊗r-eq-f' {Γ₀ = .([] ++ fst)} {.(fst₁ ++ fst₂)} Γ₁ (⊸l∙ {.(tagL (x ∷ Γ''))} {Γ'' = x ∷ Γ''} {Λ} {Δ} {D = D} f g refl refl) h .(isInter++ inTeq1 inTeq2) peq | .(tagL []) , .(tagL ([] ++ fst)) , .(black fst₁) , .(black fst₂) , inTeq1 , inTeq2 , refl , refl , refl | [] , fst , refl , refl , refl | fst₁ , fst₂ , refl , refl , refl = ⊥-elim (tag-isInter[]⊥₁ fst₁  Γ'' Λ inTeq1) 
gen⊗r-eq-f' {Γ₀ = .((x₂ ∷ Λ₀') ++ Λ₁')} {.((x₁ ∷ Ψ₀') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ Γ''))} {Γ'' = .x₂ ∷ Γ''} {Λ = Λ} {Δ} {D = D} f g refl refl) h .(isInter++ (∷left inTeq1) inTeq2) peq | .(tagL (x₂ ∷ Λ₀')) , .(tagL Λ₁') , .(black (x₁ ∷ Ψ₀')) , .(black Ψ₁') , ∷left inTeq1 , inTeq2 , refl , refl , refl | x₂ ∷ Λ₀' , Λ₁' , refl , refl , refl | x₁ ∷ Ψ₀' , Ψ₁' , refl , refl , refl with isInter++? (tagL Γ'') ((∙ , D) ∷ Λ) refl inTeq1
... | Ω₀ , Ω₁ , [] , .((∙ , x₁) ∷ black Ψ₀') , inTeq1' , inTeq1'' , eq4 , refl , eq6 with tagL++? Ω₀ Ω₁ Λ₀' eq4
gen⊗r-eq-f' {_} {.((x₂ ∷ Ω₀') ++ Λ₁')} {.((x₁ ∷ Ψ₀') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ Γ''))} {_} {.x₂ ∷ Γ''} {Λ = .(black Ψ₀')} {Δ} {D = .x₁} f g refl refl) h .(isInter++ (∷left (isInter++ inTeq1' []left)) inTeq2) peq | .(tagL (x₂ ∷ Ω₀')) , .(tagL Λ₁') , .(black (x₁ ∷ Ψ₀')) , .(black Ψ₁') , ∷left .(isInter++ inTeq1' []left) , inTeq2 , refl , refl , refl | x₂ ∷ .Ω₀' , Λ₁' , refl , refl , refl | x₁ ∷ Ψ₀' , Ψ₁' , refl , refl , refl | .(tagL Ω₀') , .(tagL []) , [] , .((∙ , x₁) ∷ black Ψ₀') , inTeq1' , []left , refl , refl , refl | Ω₀' , [] , refl , refl , refl with isInter-left[] (ersL-isInter' Ω₀' [] (tagL Γ'') inTeq1') 
gen⊗r-eq-f' {_} {.((x₂ ∷ []) ++ Λ₁')} {.((x₁ ∷ []) ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ []))} {_} {.x₂ ∷ .[]} {.(black [])} {Δ} {_} {_} {x₁} f g refl refl) h .(isInter++ (∷left (isInter++ isInter[] []left)) inTeq2) peq | .(tagL (x₂ ∷ [])) , .(tagL Λ₁') , .(black (x₁ ∷ [])) , .(black Ψ₁') , ∷left .(isInter++ isInter[] []left) , inTeq2 , refl , refl , refl | x₂ ∷ [] , Λ₁' , refl , refl , refl | x₁ ∷ [] , Ψ₁' , refl , refl , refl | .(tagL []) , .(tagL []) , [] , .((∙ , x₁) ∷ black []) , isInter[] , []left , refl , refl , refl | [] , [] , refl , refl , refl | refl 
    rewrite ersL-isInter++'-r {x = x₁} [] Λ₁' Ψ₁' inTeq2 |
            isInter++-refl ([]left {x = x₁} {[]}) (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) |
            tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2 = refl
gen⊗r-eq-f' {_} {.((x₂ ∷ []) ++ Λ₁')} {.((x₁ ∷ x ∷ Ψ₀') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ []))} {_} {.x₂ ∷ .[]} {.(black (x ∷ Ψ₀'))} {Δ} {_} {_} {x₁} f g refl refl) h .(isInter++ (∷left (isInter++ isInter[] []left)) inTeq2) peq | .(tagL (x₂ ∷ [])) , .(tagL Λ₁') , .(black (x₁ ∷ x ∷ Ψ₀')) , .(black Ψ₁') , ∷left .(isInter++ isInter[] []left) , inTeq2 , refl , refl , refl | x₂ ∷ [] , Λ₁' , refl , refl , refl | x₁ ∷ x ∷ Ψ₀' , Ψ₁' , refl , refl , refl | .(tagL []) , .(tagL []) , [] , .((∙ , x₁) ∷ black (x ∷ Ψ₀')) , isInter[] , []left , refl , refl , refl | [] , [] , refl , refl , refl | refl 
    rewrite ersL-isInter++'-r {x = x₁} (x ∷ Ψ₀') Λ₁' Ψ₁' inTeq2 |
            isInter++-refl ([]left {x = x₁} {x ∷ Ψ₀'}) (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) |
            tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2 = refl
            
gen⊗r-eq-f' {_} {.((x₂ ∷ x ∷ []) ++ Λ₁')} {.((x₁ ∷ []) ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ x ∷ []))} {_} {.x₂ ∷ .(x ∷ [])} {.(black [])} {Δ} {_} {_} {x₁} f g refl refl) h .(isInter++ (∷left (isInter++ ([]right {x = ∘ , x} {xs = tagL []}) []left)) inTeq2) peq | .(tagL (x₂ ∷ x ∷ [])) , .(tagL Λ₁') , .(black (x₁ ∷ [])) , .(black Ψ₁') , ∷left .(isInter++ ([]right {x = ∘ , x} {xs = tagL []}) []left) , inTeq2 , refl , refl , refl | x₂ ∷ x ∷ [] , Λ₁' , refl , refl , refl | x₁ ∷ [] , Ψ₁' , refl , refl , refl | .(tagL (x ∷ [])) , .(tagL []) , [] , .((∙ , x₁) ∷ black []) , []right , []left , refl , refl , refl | x ∷ [] , [] , refl , refl , refl | refl 
    rewrite ersL-isInter++' [] (x₁ ∷ []) Λ₁' Ψ₁' ([]left {x = (∙ , x₁)}) inTeq2 |
            isInter++-refl ([]left {x = x₁} {[]}) (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) |
            tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2  = refl
gen⊗r-eq-f' {_} {.((x₂ ∷ x ∷ x₃ ∷ Ω₀') ++ Λ₁')} {.((x₁ ∷ []) ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ x ∷ x₃ ∷ Ω₀'))} {_} {.x₂ ∷ .(x ∷ x₃ ∷ Ω₀')} {.(black [])} {Δ} {_} {_} {x₁} f g refl refl) h .(isInter++ (∷left (isInter++ ([]right {x = ∘ , x} {xs = tagL (x₃ ∷ Ω₀')}) []left)) inTeq2) peq | .(tagL (x₂ ∷ x ∷ x₃ ∷ Ω₀')) , .(tagL Λ₁') , .(black (x₁ ∷ [])) , .(black Ψ₁') , ∷left .(isInter++ ([]right {x = ∘ , x} {xs = tagL (x₃ ∷ Ω₀')}) []left) , inTeq2 , refl , refl , refl | x₂ ∷ x ∷ x₃ ∷ Ω₀' , Λ₁' , refl , refl , refl | x₁ ∷ [] , Ψ₁' , refl , refl , refl | .(tagL (x ∷ x₃ ∷ Ω₀')) , .(tagL []) , [] , .((∙ , x₁) ∷ black []) , []right , []left , refl , refl , refl | x ∷ x₃ ∷ Ω₀' , [] , refl , refl , refl | refl 
 rewrite ersL-isInter++' Ω₀' (x₁ ∷ []) Λ₁' Ψ₁' (isInter++l (tagL Ω₀') ([]left {x = (∙ , x₁)})) inTeq2 |
        isInter++-refl (ersL-isInter' Ω₀' (x₁ ∷ []) (tagL Ω₀' ++ (∙ , x₁) ∷ []) (isInter++l (tagL Ω₀') []left)) (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) |
        ersL-isInter++'-l₁ Ω₀' [] (x₁ ∷ []) []left |
        isInter-split-r-++-refl {x = x₁} ([]right {x = x₃} {Ω₀'}) isInter[] |
        tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2 = refl

gen⊗r-eq-f' {_} {.((x₂ ∷ x ∷ Ω₀') ++ Λ₁')} {.((x₁ ∷ x₃ ∷ Ψ₀') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ x ∷ Ω₀'))} {_} {.x₂ ∷ .(x ∷ Ω₀')} {.(black (x₃ ∷ Ψ₀'))} {Δ} {_} {_} {x₁} f g refl refl) h .(isInter++ (∷left (isInter++ ([]right {x = ∘ , x} {xs = tagL Ω₀'}) []left)) inTeq2) peq | .(tagL (x₂ ∷ x ∷ Ω₀')) , .(tagL Λ₁') , .(black (x₁ ∷ x₃ ∷ Ψ₀')) , .(black Ψ₁') , ∷left .(isInter++ ([]right {x = ∘ , x} {xs = tagL Ω₀'}) []left) , inTeq2 , refl , refl , refl | x₂ ∷ x ∷ Ω₀' , Λ₁' , refl , refl , refl | x₁ ∷ x₃ ∷ Ψ₀' , Ψ₁' , refl , refl , refl | .(tagL (x ∷ Ω₀')) , .(tagL []) , [] , .((∙ , x₁) ∷ black (x₃ ∷ Ψ₀')) , []right , []left , refl , refl , refl | x ∷ Ω₀' , [] , refl , refl , refl | refl 
    rewrite ersL-isInter++' Ω₀' (x₁ ∷ x₃ ∷ Ψ₀') Λ₁' Ψ₁' (isInter++l (tagL Ω₀') []left) inTeq2 | 
            isInter++-refl (ersL-isInter' Ω₀' (x₁ ∷ x₃ ∷ Ψ₀') (tagL Ω₀' ++ (∙ , x₁) ∷ (∙ , x₃) ∷ black Ψ₀')  (isInter++l (tagL Ω₀') []left)) (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) | 
            ersL-isInter++'-l₁ Ω₀' [] (x₁ ∷ x₃ ∷ Ψ₀') []left |
            isInter-split-r-++-refl {x = x₁} ([]right {x = x₂} {x ∷ Ω₀'}) ([]left {x = x₃} {Ψ₀'}) |
            tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2 = refl
gen⊗r-eq-f' {_} {.((x₂ ∷ [] ++ x ∷ Ω₁') ++ Λ₁')} {.((x₁ ∷ Ψ₀') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ []))} {_} {.x₂ ∷ []} {Λ = Λ} {Δ} {D = x₁} f g refl refl) h .(isInter++ (∷left (isInter++ isInter[] (∷right inTeq1''))) inTeq2) peq | .(tagL (x₂ ∷ [] ++ x ∷ Ω₁')) , .(tagL Λ₁') , .(black (x₁ ∷ Ψ₀')) , .(black Ψ₁') , ∷left .(isInter++ isInter[] (∷right inTeq1'')) , inTeq2 , refl , refl , refl | x₂ ∷ .([] ++ x ∷ Ω₁') , Λ₁' , refl , refl , refl | x₁ ∷ Ψ₀' , Ψ₁' , refl , refl , refl | .(tagL []) , .(tagL ([] ++ x ∷ Ω₁')) , [] , .((∙ , x₁) ∷ black Ψ₀') , isInter[] , ∷right inTeq1'' , refl , refl , refl | [] , x ∷ Ω₁' , refl , refl , refl 
    rewrite ersL-isInter++' (x ∷ Ω₁') Ψ₀' Λ₁' Ψ₁' inTeq1'' inTeq2 |
            isInter++-refl (ersL-isInter' (x ∷ Ω₁') Ψ₀' Λ inTeq1'') (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) |
            isInter-split-r-++-refl {x = x₁} ([]right {x = x₂} {[]}) (ersL-isInter' (x ∷ Ω₁') Ψ₀' Λ inTeq1'') |
            isInter-split-r-++-refl {x = x₁} isInter[] (ersL-isInter' (x ∷ Ω₁') Ψ₀' Λ inTeq1'') |
            tag-lem-ersL-refl' (x ∷ Ω₁') Ψ₀' Λ inTeq1'' |
            tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2 = refl
gen⊗r-eq-f' {_} {.((x₂ ∷ (x₄ ∷ Ω₀') ++ x ∷ Ω₁') ++ Λ₁')} {.((x₁ ∷ Ψ₀') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ x₃ ∷ Γ''))} {_} {.x₂ ∷ x₃ ∷ Γ''} {Λ = Λ} {Δ} {D = x₁} f g refl refl) h .(isInter++ (∷left (isInter++ inTeq1' (∷right inTeq1''))) inTeq2) peq | .(tagL (x₂ ∷ (x₄ ∷ Ω₀') ++ x ∷ Ω₁')) , .(tagL Λ₁') , .(black (x₁ ∷ Ψ₀')) , .(black Ψ₁') , ∷left .(isInter++ inTeq1' (∷right inTeq1'')) , inTeq2 , refl , refl , refl | x₂ ∷ .((x₄ ∷ Ω₀') ++ x ∷ Ω₁') , Λ₁' , refl , refl , refl | x₁ ∷ Ψ₀' , Ψ₁' , refl , refl , refl | .(tagL (x₄ ∷ Ω₀')) , .(tagL (x ∷ Ω₁')) , [] , .((∙ , x₁) ∷ black Ψ₀') , inTeq1' , ∷right inTeq1'' , refl , refl , refl | x₄ ∷ Ω₀' , x ∷ Ω₁' , refl , refl , refl with isInter-left[] (ersL-isInter' (x₄ ∷ Ω₀') [] ((∘ , x₃) ∷ tagL Γ'') inTeq1') 
gen⊗r-eq-f' {_} {.((x₂ ∷ (x₄ ∷ Ω₀') ++ x ∷ Ω₁') ++ Λ₁')} {.((x₁ ∷ Ψ₀') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ x₄ ∷ Ω₀'))} {_} {.x₂ ∷ .x₄ ∷ .Ω₀'} {Λ = Λ} {Δ} {_} {_} {x₁} f g refl refl) h .(isInter++ (∷left (isInter++ ([]right {x = ∘ , x₄} {xs = tagL Ω₀'}) (∷right inTeq1''))) inTeq2) peq | .(tagL (x₂ ∷ (x₄ ∷ Ω₀') ++ x ∷ Ω₁')) , .(tagL Λ₁') , .(black (x₁ ∷ Ψ₀')) , .(black Ψ₁') , ∷left .(isInter++ ([]right {x = ∘ , x₄} {xs = tagL Ω₀'}) (∷right inTeq1'')) , inTeq2 , refl , refl , refl | x₂ ∷ .((x₄ ∷ Ω₀') ++ x ∷ Ω₁') , Λ₁' , refl , refl , refl | x₁ ∷ Ψ₀' , Ψ₁' , refl , refl , refl | .(tagL (x₄ ∷ Ω₀')) , .(tagL (x ∷ Ω₁')) , [] , .((∙ , x₁) ∷ black Ψ₀') , []right , ∷right inTeq1'' , refl , refl , refl | x₄ ∷ Ω₀' , x ∷ Ω₁' , refl , refl , refl | refl 
    rewrite ersL-isInter++' (Ω₀' ++ x ∷ Ω₁') (x₁ ∷ Ψ₀') Λ₁' Ψ₁' (isInter++l (tagL Ω₀') (∷right inTeq1'')) inTeq2 |
            isInter++-refl (ersL-isInter' (Ω₀' ++ x ∷ Ω₁') (x₁ ∷ Ψ₀') (tagL Ω₀' ++ (∙ , x₁) ∷ Λ) (isInter++l (tagL Ω₀') (∷right inTeq1''))) (ersL-isInter' Λ₁' Ψ₁' Δ inTeq2) |
            ersL-isInter++' Ω₀' [] (x ∷ Ω₁') (x₁ ∷ Ψ₀') ([]right' (tagL Ω₀')) (∷right inTeq1'') |
            isInter-split-r-++-refl {x = x₁} ([]right {x = x₂} {x₄ ∷ Ω₀'}) (ersL-isInter' (x ∷ Ω₁') Ψ₀' Λ inTeq1'') |
            tag-lem-ersL-refl' (x ∷ Ω₁') Ψ₀' Λ inTeq1'' |
            tag-lem-ersL-refl' Λ₁' Ψ₁' Δ inTeq2 = refl

gen⊗r-eq-f' {Γ₀ = .((x₂ ∷ Λ₀') ++ Λ₁')} {.((x₁ ∷ Ψ₀') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ Γ''))} {Γ'' = .x₂ ∷ Γ''} {Λ = Λ} {Δ} {D = D} f g refl refl) h .(isInter++ (∷left inTeq1) inTeq2) peq | .(tagL (x₂ ∷ Λ₀')) , .(tagL Λ₁') , .(black (x₁ ∷ Ψ₀')) , .(black Ψ₁') , ∷left inTeq1 , inTeq2 , refl , refl , refl | x₂ ∷ Λ₀' , Λ₁' , refl , refl , refl | x₁ ∷ Ψ₀' , Ψ₁' , refl , refl , refl | Ω₀ , Ω₁ , x ∷ Φ₀ , Φ₁ , inTeq1' , inTeq1'' , eq4 , eq5 , eq6 with tagL++? Ω₀ Ω₁ Λ₀' eq4 | black++? (x ∷ Φ₀) Φ₁ (x₁ ∷ Ψ₀') eq5
gen⊗r-eq-f' {_} {.((x₂ ∷ Ω₀' ++ Ω₁') ++ Λ₁')} {.((x₁ ∷ Φ₀' ++ Φ₁') ++ Ψ₁')} Γ₁ (⊸l∙ {.(tagL (x₂ ∷ Γ''))} {_} {.x₂ ∷ Γ''} {Λ = Λ} {Δ} {D = D} f g refl refl) h .(isInter++ (∷left (isInter++ inTeq1' inTeq1'')) inTeq2) peq | .(tagL (x₂ ∷ Ω₀' ++ Ω₁')) , .(tagL Λ₁') , .(black (x₁ ∷ Φ₀' ++ Φ₁')) , .(black Ψ₁') , ∷left .(isInter++ inTeq1' inTeq1'') , inTeq2 , refl , refl , refl | x₂ ∷ .(Ω₀' ++ Ω₁') , Λ₁' , refl , refl , refl | x₁ ∷ .(Φ₀' ++ Φ₁') , Ψ₁' , refl , refl , refl | .(tagL Ω₀') , .(tagL Ω₁') , .(∙ , x₁) ∷ .(black Φ₀') , .(black Φ₁') , inTeq1' , inTeq1'' , refl , refl , refl | Ω₀' , Ω₁' , refl , refl , refl | .x₁ ∷ Φ₀' , Φ₁' , refl , refl , refl = ⊥-elim (tag-isInter⊥ Ω₀' [] Φ₀' Γ'' inTeq1') -- imposs


gen⊗r-eq-p' : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ : TCxt} (Γ₁ : Cxt) {A : Pos} {B : Fma} 
    → (f : ∙ ∣ S ∣ Γ ⊢p A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter (tagL Γ₀) (black Γ₁') Γ) (peq : Γ₁' ↭' Γ₁)
    → gen⊗r-p Γ₁ (p∙2p f) g (ersL-isInter' Γ₀ Γ₁' Γ inTeq) peq 
        ≡ f2p (⊗r (⊸r⋆∙ {Γ = Γ} Γ₁ (li2ri (p2li f)) inTeq peq refl) g)
gen⊗r-eq-p' {Γ₀ = []} {x ∷ Γ₁'} Γ₁ (pass∙ f) g []left peq = refl
gen⊗r-eq-p' {Γ₀ = x ∷ Γ₀} {x₁ ∷ Γ₁'} Γ₁ (pass∙ f) g (∷right inTeq) peq 
    rewrite tag-lem-ersL-refl' (x ∷ Γ₀) Γ₁' _ inTeq  = refl
gen⊗r-eq-p' Γ₁ (f2p f) g inTeq peq = cong f2p (gen⊗r-eq-f' Γ₁ f g inTeq peq)

gen⊗r-eq-li' : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ : TCxt} (Γ₁ : Cxt) {A : Pos} {B : Fma} 
    → (f : ∙ ∣ irr S ∣ Γ ⊢li A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter (tagL Γ₀) (black Γ₁') Γ) (peq : Γ₁' ↭' Γ₁)
    → gen⊗r-li Γ₁ (li∙2li f) g (ersL-isInter' Γ₀ Γ₁' Γ inTeq) peq 
        ≡ p2li {S = S} (f2p (⊗r (⊸r⋆∙ Γ₁ (li2ri f) inTeq peq refl) g))
gen⊗r-eq-li' {.(irr (just (` x) , tt)) , tt} Γ₁ (p2li {S = just (` x) , tt} f) g inTeq peq = cong p2li (gen⊗r-eq-p' Γ₁ f g inTeq peq)
gen⊗r-eq-li' {.(irr (just (x ⊸ x₁) , snd₁)) , snd} Γ₁ (p2li {S = just (x ⊸ x₁) , snd₁} f) g inTeq peq = cong p2li (gen⊗r-eq-p' Γ₁ f g inTeq peq)
gen⊗r-eq-li' {.(irr (- , tt)) , tt} Γ₁ (p2li {S = - , tt} f) g inTeq peq = cong p2li (gen⊗r-eq-p' Γ₁ f g inTeq peq)
gen⊗r-eq' : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ : TCxt} (Γ₁ : Cxt) {A B : Fma} 
    → (f : ∙ ∣ irr S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter (tagL Γ₀) (black Γ₁') Γ) (peq : Γ₁' ↭' Γ₁)
    → gen⊗r-ri Γ₁ (ri∙2ri f) g (ersL-isInter' Γ₀ Γ₁' Γ inTeq) peq 
        ≡ p2li {S = S} (f2p (⊗r (⊸r⋆∙ Γ₁ f inTeq peq refl) g))
gen⊗r-eq' Γ₁ (⊸r∙ (ex∙ (ex∙ {Γ = x ∷ Γ} f refl refl) eq' eq)) g inTeq peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
gen⊗r-eq' Γ₁ (⊸r∙ (ex∙ {Δ = Δ} {Λ} (ri2c f) refl refl)) g inTeq peq with isInter++? Δ Λ refl inTeq
gen⊗r-eq' {Γ₀ = Γ₀} {Γ₁'} Γ₁ (⊸r∙ (ex∙ {Δ = Δ} {Λ} (ri2c f) refl refl)) g inTeq peq | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , inTeq' , inTeq'' , eq1 , eq2 , eq3 with tagL++? Γ₀₀ Γ₀₁ Γ₀ eq1 | black++? Γ₁₀' Γ₁₁' Γ₁' eq2 
gen⊗r-eq' {S = S} {Γ₀ = .(Φ₀ ++ Φ₁)} {.(Ψ₀ ++ Ψ₁)} {Δ₁} Γ₁ (⊸r∙ {A = A} (ex∙ {Δ = Δ} {Λ} (ri2c f) refl refl)) g .(isInter++ inTeq' inTeq'') peq | .(tagL Φ₀) , .(tagL Φ₁) , .(black Ψ₀) , .(black Ψ₁) , inTeq' , inTeq'' , refl , refl , refl | Φ₀ , Φ₁ , refl , refl , refl | Ψ₀ , Ψ₁ , refl , refl , refl 
    rewrite ersL-isInter++' Φ₀ Ψ₀ Φ₁ Ψ₁ inTeq' inTeq'' |
            isInter++-refl (ersL-isInter' Φ₀ Ψ₀ Δ inTeq') (ersL-isInter' Φ₁ Ψ₁ Λ inTeq'') |
            sym (ersL-isInter'-∷right'∙ {x = A} Φ₁ Ψ₁ inTeq'') |
            sym (ersL-isInter++' Φ₀ Ψ₀ Φ₁ (A ∷ Ψ₁) inTeq' (∷right' (tagL Φ₁) inTeq'')) = 
            trans (gen⊗r-eq' {S = S} {Γ₀ = Φ₀ ++ Φ₁} (Γ₁ ++ A ∷ []) f g (isInter++ inTeq' (∷right' {x = (∙ , A)} (tagL Φ₁) inTeq'')) (snoc↭' {xs₀ = Ψ₀} {Ψ₁} refl peq)) 
            (cong (λ x → p2li (f2p x)) (subst (λ x → ⊗r {Γ = Φ₀ ++ Φ₁} x g ≡ ⊗r {Γ = Φ₀ ++ Φ₁} (⊸r⋆∙ Γ₁ (⊸r∙ {A = A} (ex∙ {Δ = Δ} {Λ} (ri2c f) refl refl)) (isInter++ inTeq' inTeq'') peq refl) g) (sym (⊸r⋆∙⊸r∙ {Δ₁ = Ψ₀} {Ψ₁} Γ₁ f refl inTeq' inTeq'' peq)) refl))
gen⊗r-eq' Γ₁ (li2ri f) g inTeq peq = gen⊗r-eq-li' Γ₁ f g inTeq peq


-- ==========
{- eq and eq1 serve for ex, eq2 serve for ⊸r-c'', and eq3 serve for ex-c' -}
⊸r-c''-ex : {S : Stp} {Γ' Γ'' Γ Δ Λ Ω : Cxt} {A A' C : Fma}
    → (f : S ∣ Γ'' ؛ Ω ⊢c C) (eq : Γ' ≡ Γ'' ++ A' ∷ []) (eq1 : Ω ≡ Δ ++ A' ∷ Λ) (eq2 : Γ'' ≡ Γ ++ A ∷ []) (eq3 : Γ' ≡ Γ ++ A ∷ A' ∷ [])
    → ⊸r-c'' {Γ = Γ ++ A' ∷ []} (ex-c' Γ {Ψ = []} {Λ = Γ'} (ex f eq eq1) eq3) refl ≡ ex (⊸r-c'' f eq2) refl eq1
⊸r-c''-ex {Γ = Γ₁} (ex {Γ = Γ} f refl refl) eq eq1 eq2 eq3 with snoc≡ Γ Γ₁ eq2
⊸r-c''-ex {Γ = Γ₁} {Δ = Δ₁} {Λ₁} (ex {Γ = Γ₁} {Δ} {Λ} f refl refl) refl eq1 refl refl | refl , refl with cases++ Δ₁ Δ Λ₁ Λ eq1 -- checking where is A
⊸r-c''-ex {Γ = Γ₁} {Δ = Δ₁} {.(Ω₀ ++ Λ)} {A = A} {A'} (ex {Γ = Γ₁} {.(Δ₁ ++ A' ∷ Ω₀)} {Λ} f refl refl) refl refl refl refl | refl , refl | inj₁ (Ω₀ , refl , refl) 
    rewrite cases++-inj₂ (A ∷ []) Γ₁ [] A' |
            snoc≡-refl Γ₁ A | 
            cases++-inj₁ Δ₁ Ω₀ Λ A' |
            snoc≡-refl (Γ₁ ++ A' ∷ []) A |
            cases++-inj₂ Ω₀ Δ₁ Λ A = refl
⊸r-c''-ex {Γ = Γ₁} {Δ = .(Δ ++ Ω₀)} {Λ₁} {A = A} {A'} (ex {Γ = Γ₁} {Δ} {.(Ω₀ ++ A' ∷ Λ₁)} f refl refl) refl refl refl refl | refl , refl | inj₂ (Ω₀ , refl , refl) 
    rewrite cases++-inj₂ (A ∷ []) Γ₁ [] A' | 
            snoc≡-refl Γ₁ A | 
            cases++-inj₂ Ω₀ Δ Λ₁ A' | 
            snoc≡-refl (Γ₁ ++ A' ∷ []) A |
            cases++-inj₁ Δ Ω₀ Λ₁ A = refl
⊸r-c''-ex {Γ = Γ} (ri2c f) eq eq1 eq2 eq3 = ⊥-elim ([]disj∷ Γ eq2)

act⋆-⊸r-c'' : {S : Stp} (Φ Γ : Cxt) {Φ' Δ : Cxt} {A B : Fma}
    → (f : S ∣ Φ' ؛ Γ ++ Δ ⊢c B) (eq : Φ' ≡ Φ ++ A ∷ [])
    → ⊸r-c'' {Γ = Φ ++ Γ} {Δ = Δ} (ex-fma-cxt-c Γ (act⋆ (Φ ++ A ∷ []) Γ (subst (λ x → S ∣ x ؛ Γ ++ Δ ⊢c B) eq f))) refl ≡ act⋆ Φ Γ (⊸r-c'' f eq)
act⋆-⊸r-c'' Φ [] f refl = refl
act⋆-⊸r-c'' Φ (A' ∷ Γ) {A = A} f refl rewrite cases++-inj₂ (A ∷ []) Φ [] A' = 
    trans (cong (λ x → ⊸r-c'' {Γ = Φ ++ A' ∷ Γ} (ex-fma-cxt-c {Γ = Φ ++ A' ∷ []} Γ x) refl) (ex-c-act⋆ Φ Γ (act (Φ ++ A ∷ []) f))) 
    (trans (act⋆-⊸r-c'' (Φ ++ A' ∷ []) Γ (ex-c Φ (act (Φ ++ A ∷ []) f)) refl) 
    (cong (λ x → act⋆ (Φ ++ A' ∷ []) Γ x) (⊸r-c''-ex f refl refl refl refl)))

⊸r-c''-⊸r : {S : Stp} {Γ Γ' : Cxt} {A B : Fma}
    → (f : S ∣ Γ' ؛ Γ ⊢c B) (eq : Γ' ≡ A ∷ [])
    → ⊸r-c'' f eq ≡ ri2c (⊸r (subst (λ x → S ∣ x ؛ Γ ⊢c B) eq f))
⊸r-c''-⊸r (ex (ex {Γ = x ∷ Γ} f refl refl) eq' eq₁) refl = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
⊸r-c''-⊸r (ex (ri2c f) refl refl) refl = refl

⊸r-⊸r∙ : {S : Stp} {Γ : TCxt} {A B : Fma}
    → (f : ∙ ∣ S ∣ (∙ , A) ∷ [] ؛ Γ ⊢c B)
    → ⊸r (c∙2c f) ≡ ri∙2ri (⊸r∙ f)
⊸r-⊸r∙ (ex∙ (ex∙ {Γ = x ∷ Γ} f refl refl) eq' eq) = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
⊸r-⊸r∙ (ex∙ (ri2c f) refl refl) = refl

ersL-isInter'-[]right' : (Γ : TCxt)
    → ersL-isInter' (ersL Γ) [] (whiteL Γ) ([]right' (whiteL Γ)) ≡ []right' (ersL Γ)
ersL-isInter'-[]right' [] = refl
ersL-isInter'-[]right' ((∘ , snd) ∷ Γ) = refl
ersL-isInter'-[]right' ((∙ , snd) ∷ Γ) = refl

ersL-isInter'-[]right'₂ : (Γ : Cxt)
    → ersL-isInter' Γ [] (tagL Γ) ([]right' (tagL Γ)) ≡ []right' Γ
ersL-isInter'-[]right'₂ [] = refl
ersL-isInter'-[]right'₂ (x ∷ Γ) = refl
mutual
    focusemb-c : {S : Stp} {Γ Δ : Cxt} {C : Fma}
            (f : S ∣ Γ ؛ Δ ⊢c C) → 
            focus (emb-c f) ≡ act⋆ Γ Δ f
    focusemb-c (ex {Γ = Γ} {Δ} {Λ} f refl refl) = 
        trans (focus-ex-cxt-fma Δ (emb-c f)) 
        (trans (cong ( λ x → ex-cxt-fma-c Δ x) (focusemb-c f)) (act⋆-ex-cxt-fma {Λ = Λ} Γ Δ f))
    focusemb-c (ri2c f) = focusemb-ri f
    focusemb-c∙ : {S : Stp} {Γ Δ : TCxt} {C : Fma}
            (f : ∙ ∣ S ∣ Γ ؛ Δ ⊢c C) → 
            focus (emb-c∙ f) ≡ act⋆ (ersL Γ) (ersL Δ) (c∙2c f) 
    focusemb-c∙ (ex∙ {Γ = Γ} {Δ} {Λ} f refl refl) = 
        trans (focus-ex-cxt-fma (ersL Δ) (emb-c∙ f)) 
        (trans (cong ( λ x → ex-cxt-fma-c (ersL Δ) x) (focusemb-c∙ f)) (act⋆-ex-cxt-fma {Λ = ersL Λ} (ersL Γ) (ersL Δ) (c∙2c f)))
    focusemb-c∙ (ri2c f) = focusemb-ri∙ f
    focusemb-ri : {S : Stp} {Γ : Cxt} {C : Fma} 
            (f : S ∣ Γ ⊢ri C) → 
            focus (emb-ri f) ≡ act⋆ [] Γ (ri2c f)
    focusemb-ri {Γ = Γ} (⊸r f) = 
        trans (cong  ⊸r-c (focus-ex-fma-cxt Γ (emb-c f))) 
        (trans (cong (λ x → ⊸r-c (ex-fma-cxt-c {Γ = []} Γ x)) (focusemb-c f )) 
        (trans (act⋆-⊸r-c'' [] Γ f refl) (cong (λ x → act⋆ [] Γ x) (⊸r-c''-⊸r f refl))))
    focusemb-ri (li2ri f) = focusemb-li f
    focusemb-ri∙ : {S : Stp} {Γ : TCxt} {C : Fma}
            (f : ∙ ∣ S ∣ Γ ⊢ri C) → 
            focus (emb-ri∙ f refl) ≡ act⋆ [] (ersL Γ) (ri2c (ri∙2ri f))
    focusemb-ri∙ {Γ = Γ} (⊸r∙ f) = 
        trans (cong  ⊸r-c (focus-ex-fma-cxt (ersL Γ) (emb-c∙ f))) 
        (trans (cong (λ x → ⊸r-c (ex-fma-cxt-c {Γ = []} (ersL Γ) x)) (focusemb-c∙ f)) 
        (trans (act⋆-⊸r-c'' [] (ersL Γ) (c∙2c f) refl) (cong (λ x → act⋆ [] (ersL Γ) x) 
        (trans (⊸r-c''-⊸r (c∙2c f) refl) (cong ri2c (⊸r-⊸r∙ f))))))
    focusemb-ri∙ (li2ri (p2li f)) = focusemb-p∙ f
    focusemb-li : {S : Stp} {Γ : Cxt} {C : Pos}
            (f : S ∣ Γ ⊢li C) → 
            focus (emb-li f) ≡ act⋆ [] Γ (ri2c (li2ri f))
    focusemb-li (Il {Γ = Γ} f) = trans (cong Il-c  (focusemb-li f)) (act⋆-Il-c [] Γ)
    focusemb-li {Γ = Γ} {C = C} (⊗l f) = 
        trans (cong ⊗l-c (focusemb-c f)) 
        (trans (act⋆⊗l-c [] Γ {C = C}) (cong (act⋆ [] Γ {Δ = []}) (⊗l-c-eq f refl)))
    focusemb-li (p2li f) = focusemb-p f
    focusemb-p : {S : Irr} {Γ : Cxt} {C : Pos}
            (f : S ∣ Γ ⊢p C) → 
            focus (emb-p f) ≡ act⋆ [] Γ (ri2c (li2ri (p2li f)))
    focusemb-p (pass {Γ} {A} {C} f) = 
        trans (cong pass-c (focusemb-li f)) (trans (act⋆pass-c [] Γ (ri2c (li2ri f)) refl) (cong (act⋆ (A ∷ []) Γ) refl))
    focusemb-p (f2p f) = focusemb-f f
    focusemb-p∙ : {S : Irr} {Γ : TCxt} {C : Pos}
            (f : ∙ ∣ S ∣ Γ ⊢p C) → 
            focus (emb-p∙ f) ≡ act⋆ [] (ersL Γ) (ri2c (li2ri (p2li (p∙2p f))))
    focusemb-p∙ (pass∙ {Γ} {A} f) = 
        trans (cong pass-c (focusemb-li f)) (trans (act⋆pass-c [] (ersL Γ) (ri2c (li2ri f)) refl) (cong (act⋆ (A ∷ []) (ersL Γ)) refl))
    focusemb-p∙ (f2p f) = focusemb-f∙ f
    focusemb-f : {S : Irr} {Γ : Cxt} {C : Pos}
            (f : S ∣ Γ ⊢f C) → 
            focus (emb-f f) ≡ act⋆ [] Γ (ri2c (li2ri (p2li (f2p f))))
    focusemb-f ax = refl
    focusemb-f Ir = refl
    focusemb-f {S = S} (⊗r {Γ = Γ} {Δ} f g) = 
        trans (cong₂ (λ x → λ y → ⊗r-c x y) (focusemb-ri∙ f) (focusemb-ri g)) 
        (trans (act⋆⊗r-c Γ [] Δ (ri2c (ri∙2ri f)) (ri2c g)) 
        (trans (cong (act⋆ Γ Δ) (act⋆⊗r-c-ri [] Γ (ri2c (ri∙2ri f)) g)) 
        (trans (act⋆act⋆ [] Γ Δ) (cong (λ x → act⋆ [] (Γ ++ Δ) (ri2c (li2ri x))) 
        (trans (sym (cong (λ x →  gen⊗r-ri [] (ri∙2ri f) g x (empty refl)) (ersL-isInter'-[]right'₂ Γ))) 
        (trans (gen⊗r-eq' {Γ₀ = Γ} [] f g ([]right' (tagL Γ)) (empty refl)) 
        (cong (λ x → p2li (f2p x)) (cong (λ x → ⊗r x g) (⊸r⋆∙[] f ([]right' (tagL Γ)))))))))))
    focusemb-f (⊸l {Γ} {Δ} f g) = 
        trans (cong₂ (λ x → λ y → ⊸l-c x y) (focusemb-ri f) (focusemb-li g)) 
        (trans (act⋆⊸l-c Γ [] Δ (ri2c f) (ri2c (li2ri g))) 
        (trans (cong (act⋆ Γ Δ) (act⋆⊸l-c-ri [] Γ (ri2c f) (li2ri g))) (act⋆act⋆ [] Γ Δ)))
    focusemb-f∙ : {S : Irr} {Γ : TCxt} {C : Pos}
            (f : ∙ ∣ S ∣ Γ ⊢f C) → 
            focus (emb-f∙ f) ≡ act⋆ [] (ersL Γ) (ri2c (li2ri (p2li (f2p (f∙2f f)))))
    focusemb-f∙ ax = refl
    focusemb-f∙ Ir = refl
    focusemb-f∙ {S = S} (⊗r∙ {Γ = Γ} {Δ} f g) = 
         trans (cong₂ (λ x → λ y → ⊗r-c x y) (focusemb-ri∙ f) (focusemb-ri g)) 
        (trans (act⋆⊗r-c (ersL Γ) [] (ersL Δ) (ri2c (ri∙2ri f)) (ri2c g)) 
        (trans (cong (act⋆ (ersL Γ) (ersL Δ)) (act⋆⊗r-c-ri [] (ersL Γ) (ri2c (ri∙2ri f)) g)) 
        (trans (act⋆act⋆ [] (ersL Γ) (ersL Δ)) (cong (λ x → act⋆ [] (ersL Γ ++ ersL Δ) (ri2c (li2ri x))) 
        (trans (sym (cong (λ x → gen⊗r-ri [] (ri∙2ri f) g x (empty refl)) (ersL-isInter'-[]right' Γ))) 
        (trans (gen⊗r-eq' {Γ₀ = ersL Γ} [] f g ([]right' (whiteL Γ)) (empty refl)) 
        (cong p2li (cong f2p (cong (λ x → ⊗r x g) (⊸r⋆∙[] f ([]right' (whiteL Γ))))))))))))
    focusemb-f∙ (⊸l∙ {Γ} {Λ = Λ} {Δ = Δ} f g refl refl) = 
        trans (cong₂ (λ x → λ y → ⊸l-c x y) (focusemb-ri f) (focusemb-li g)) 
        (trans (act⋆⊸l-c (ersL Γ ++ _ ∷ ersL Λ) [] (ersL Δ) (ri2c f) (ri2c (li2ri g))) 
        (trans (cong (act⋆ (ersL Γ ++ _ ∷ ersL Λ) (ersL Δ)) (act⋆⊸l-c-ri [] (ersL Γ ++ _ ∷ ersL Λ) (ri2c f) (li2ri g))) 
        ((act⋆act⋆ [] (ersL Γ ++ _ ∷ ersL Λ) (ersL Δ)))))      

                                  