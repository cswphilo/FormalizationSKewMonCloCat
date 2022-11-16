{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module FocusEmb where

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
open import Embfocus


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

-- act⋆-ex-cxt-fma-c : 
-- mutual
--     c∙2c : {S : Stp} {Γ Δ : TCxt} {C : Fma} 
--         → (f : ∙ ∣ S ∣ Γ ؛ Δ ⊢c C)
--         → S ∣ ersL Γ ؛ ersL Δ ⊢c C
--     c∙2c (ex∙ f refl refl) = ex (c∙2c f) refl refl
--     c∙2c (ri2c f) = ri2c (ri∙2ri f)  
--     ri∙2ri : {S : Stp} {Γ : TCxt} {C : Fma}
--         → (f : ∙ ∣ S ∣ Γ ⊢ri C)
--         → S ∣ ersL Γ ⊢ri C
--     ri∙2ri (⊸r∙ (ex∙ (ex∙ {Γ = x ∷ Γ} f refl refl) eq' eq)) = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq')))
--     ri∙2ri (⊸r∙ (ex∙ (ri2c f) refl refl)) = ⊸r (ex (ri2c (ri∙2ri f)) refl refl)
--     ri∙2ri (li2ri f) = li2ri (li∙2li f)
--     li∙2li : {S : Stp} {Γ : TCxt} {C : Pos}
--         → (f : ∙ ∣ S ∣ Γ ⊢li C)
--         → S ∣ ersL Γ ⊢li C
--     li∙2li (p2li f) = p2li (p∙2p f)
--     p∙2p : {S : Irr} {Γ : TCxt} {C : Pos}
--         → (f : ∙ ∣ S ∣ Γ ⊢p C)
--         → S ∣ ersL Γ ⊢p C
--     p∙2p (pass∙ f) = pass f
--     p∙2p (f2p f) = f2p (f∙2f f)
--     f∙2f : {S : Irr} {Γ : TCxt} {C : Pos}
--         → (f : ∙ ∣ S ∣ Γ ⊢f C)
--         → S ∣ ersL Γ ⊢f C
--     f∙2f ax = ax
--     f∙2f Ir = Ir
--     f∙2f (⊗r f g) = ⊗r f g
--     f∙2f (⊸l∙ f g refl) = ⊸l f g

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
    -- trans (ex-c-act⋆ Φ Γ (act (Φ ++ _ ∷ _ ∷ _) f)) {! cong (act⋆ (Φ ++ _ ∷ _ ∷ _ ++ A ∷ []) Γ) (ex-c-act⋆ Φ (A ∷ []) f) !}

-- ex-act : {S : Stp} 

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
... | Γ₀' , Γ₁' , refl , refl , refl = x ∷ Γ₀' , Γ₁' , refl , refl , refl -- x ∷ Γ , Γ₁' , {!   !} , {!   !} , {!   !}

black++? : (Γ₀ Γ₁ : TCxt) → (Γ : Cxt)
    → (eq : black Γ ≡ Γ₀ ++ Γ₁) → Σ (Cxt) λ Γ₀' → Σ (Cxt) λ Γ₁' → Γ ≡ Γ₀' ++ Γ₁' × Γ₀ ≡ black Γ₀'  × Γ₁ ≡ black Γ₁'
black++? Γ₀ Γ₁ [] eq with []++? {xs = Γ₀} {Γ₁} eq
black++? .[] .[] [] refl | refl , refl = [] , [] , refl , refl , refl
black++? [] .(black (x ∷ Γ)) (x ∷ Γ) refl = [] , (x ∷ Γ) , refl , refl , refl
black++? (x₁ ∷ Γ₀) Γ₁ (x ∷ Γ) eq with inj∷ eq
... | refl , eq1 with black++? Γ₀ Γ₁ Γ eq1
... | Γ₀' , Γ₁' , refl , refl , refl = x ∷ Γ₀' , Γ₁' , refl , refl , refl

tag-isInter-ersL-isInter-refl : (Γ₀ Γ₁ : Cxt) (Γ : TCxt) → (inTeq : isInter (tagL Γ₀) (black Γ₁) Γ) → tag-isInter (ersL-isInter inTeq) ≡ Γ
tag-isInter-ersL-isInter-refl [] [] [] isInter[] = refl
tag-isInter-ersL-isInter-refl [] (x₁ ∷ Γ₁) (.(∙ , x₁) ∷ .(black Γ₁)) []left = refl
tag-isInter-ersL-isInter-refl (x₁ ∷ Γ₀) [] (.(∘ , x₁) ∷ .(tagL Γ₀)) []right = refl
tag-isInter-ersL-isInter-refl (x₁ ∷ Γ₀) (x₂ ∷ Γ₁) (.(∘ , x₁) ∷ Γ) (∷left inTeq) = cong ((∘ , x₁) ∷_) (tag-isInter-ersL-isInter-refl Γ₀ (x₂ ∷ Γ₁) Γ inTeq)
tag-isInter-ersL-isInter-refl (x₁ ∷ Γ₀) (x₂ ∷ Γ₁) (.(∙ , x₂) ∷ Γ) (∷right inTeq) 
    rewrite tag-isInter-ersL-isInter-refl (x₁ ∷ Γ₀) Γ₁ Γ inTeq = refl  -- cong ((∙ , x₂) ∷_) (tag-isInter-ersL-isInter-refl (x₁ ∷ Γ₀)  Γ₁ Γ inTeq)
-- {-# REWRITE tag-isInter-ersL-isInter-refl #-}

-- tag-lem-ersL-refl : (Γ₀ Γ₁ : Cxt) (Γ : TCxt) →  (inTeq : isInter (tagL Γ₀) (black Γ₁) Γ) → tag-lem' (ersL-isInter inTeq) ≡ inTeq
-- tag-lem-ersL-refl [] [] [] isInter[] = refl
-- tag-lem-ersL-refl [] (x₁ ∷ Γ₁) (.(∙ , x₁) ∷ .(black Γ₁)) []left = refl
-- tag-lem-ersL-refl (x₁ ∷ Γ₀) [] (.(∘ , x₁) ∷ .(tagL Γ₀)) []right = refl
-- tag-lem-ersL-refl (x₁ ∷ Γ₀) (x₂ ∷ Γ₁) (.(∘ , x₁) ∷ Γ) (∷left inTeq) = {!cong ∷left (tag-lem-ersL-refl Γ₀ (x₂ ∷ Γ₁) Γ inTeq)  !}  
-- tag-lem-ersL-refl (x₁ ∷ Γ₀) (x₂ ∷ Γ₁) (.(∙ , x₂) ∷ Γ) (∷right inTeq) = {!cong ∷right (tag-lem-ersL-refl (x₁ ∷ Γ₀) Γ₁ Γ inTeq) !}
-- {-# REWRITE tag-lem-ersL-refl #-}


ersL-isInter-[]right'-refl : (Γ : Cxt) → ersL-isInter ([]right' (tagL Γ)) ≡ []right' Γ
ersL-isInter-[]right'-refl [] = refl
ersL-isInter-[]right'-refl (x ∷ Γ) = refl
{-# REWRITE ersL-isInter-[]right'-refl #-}

ersL-isInter-[]right'-whiteL-refl : (Γ : TCxt) → ersL-isInter ([]right' (whiteL Γ)) ≡ []right' (ersL Γ)
ersL-isInter-[]right'-whiteL-refl [] = refl
ersL-isInter-[]right'-whiteL-refl (x ∷ Γ) = refl
{-# REWRITE ersL-isInter-[]right'-whiteL-refl #-}

⊸r⋆∙[] : {S : Stp} {Γ : TCxt} {A : Fma}
    → (f : ∙ ∣ S ∣ Γ ⊢ri A) (inTeq : isInter Γ [] Γ)
    → ⊸r⋆∙ [] f inTeq (empty refl) ≡ f
⊸r⋆∙[] f isInter[] = refl
⊸r⋆∙[] f []right = refl

⊸r⋆∙⊸r∙ : {S : Stp} {Δ₀ Δ Λ₀ Λ Ω : TCxt} {Δ₁ Λ₁ : Cxt} (Γ₁ : Cxt) {A C : Fma}
    → (f : ∙ ∣ S ∣ Ω ⊢ri C) (eq : Ω ≡ Δ ++ (∙ , A) ∷ Λ) (inTeq1 : isInter Δ₀ (black Δ₁) Δ) (inTeq2 : isInter Λ₀ (black Λ₁) Λ) (peq : Δ₁ ++ Λ₁ ↭' Γ₁)
    → ⊸r⋆∙ {Γ₁' = Δ₁ ++ A ∷ Λ₁} (Γ₁ ++ A ∷ []) f (subst (λ x → isInter (Δ₀ ++ Λ₀) (black Δ₁ ++ (∙ , A) ∷ black Λ₁) x) (sym eq) (isInter++ inTeq1 (∷right' {x = (∙ , A)} Λ₀ inTeq2))) ((snoc↭' {xs₀ = Δ₁} {Λ₁} refl peq)) ≡ ⊸r⋆∙ Γ₁ (⊸r∙ (ex∙ (ri2c f) refl eq)) (isInter++ inTeq1 inTeq2) peq
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

-- isInter-split-r-[]-refl : {X : Set} → {xs ys zs : List X} → {y : X} → (inTeq : isInter xs (y ∷ ys) zs)  → isInter-split-r [] ys refl inTeq ≡ ([] , xs , [] , (y ∷ zs) , isInter[] , {!   !} , {!   !} , {!   !} , {!   !})

gen⊗r-eq-f : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ' : TCxt} (Γ₁ : Cxt) {A : Pos} {B : Fma} 
    → (f : ∙ ∣ S ∣ Γ' ⊢f A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter (tagL Γ₀) (black Γ₁') Γ') (peq : Γ₁' ↭' Γ₁)
    → gen⊗r-f Γ₁ (f∙2f f) g (ersL-isInter inTeq) peq 
        ≡ ⊗r (⊸r⋆∙ Γ₁ (li2ri (p2li (f2p f))) inTeq peq) g
gen⊗r-eq-f {Γ₀ = []} {[]} .[] ax g isInter[] (empty refl) = refl
gen⊗r-eq-f {Γ₀ = []} {[]} .(_ ∷ _) ax g isInter[] (cons {xs₀ = xs₀} x peq) = ⊥-elim ([]disj∷ xs₀ x)
gen⊗r-eq-f {Γ₀ = []} {[]} .[] Ir g isInter[] (empty refl) = refl
gen⊗r-eq-f {Γ₀ = []} {[]} .(_ ∷ _) Ir g isInter[] (cons {xs₀ = xs₀} x peq) = ⊥-elim ([]disj∷ xs₀ x)
gen⊗r-eq-f Γ₁ (⊗r {Γ = Γ} {Δ} f g) h inTeq peq with isInter++? Γ Δ refl inTeq 
gen⊗r-eq-f {Γ₀ = Γ₀} {Γ₁'} Γ₁ (⊗r {Γ = Γ} {Δ} f g) h inTeq peq | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , inTeq' , inTeq'' , eq1 , eq2 , eq3 with tagL++? Γ₀₀ Γ₀₁ Γ₀ eq1 | black++? Γ₁₀' Γ₁₁' Γ₁' eq2
gen⊗r-eq-f {Γ₀ = .(Φ₀ ++ Φ₁)} {.(Ψ₀ ++ Ψ₁)} Γ₁ (⊗r {Γ = Γ} {Δ} f g) h .(isInter++ inTeq' inTeq'') peq | .(tagL Φ₀) , .(tagL Φ₁) , .(black Ψ₀) , .(black Ψ₁) , inTeq' , inTeq'' , refl , refl , refl | Φ₀ , Φ₁ , refl , refl , refl | Ψ₀ , Ψ₁ , refl , refl , refl 
    rewrite ersL-isInter++ inTeq' inTeq'' | isInter++-refl (ersL-isInter inTeq') (ersL-isInter inTeq'') | isInter++-tag-lem' (ersL-isInter inTeq') (ersL-isInter inTeq'') = {!   !}
gen⊗r-eq-f Γ₁ (⊸l∙ {Γ} {Γ'} {Λ} {Δ = Δ} {D = D} f g eq) h inTeq peq with isInter++? Γ' Δ refl inTeq
gen⊗r-eq-f {Γ₀ = Γ₀} {Γ₁'} Γ₁ (⊸l∙ {Γ} {Γ'} {Λ} {Δ = Δ} {D = D} f g eq) h inTeq peq | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , inTeq' , inTeq'' , eq1 , eq2 , eq3 with tagL++? Γ₀₀ Γ₀₁ Γ₀ eq1 | black++? Γ₁₀' Γ₁₁' Γ₁' eq2
gen⊗r-eq-f {Γ₀ = .(Φ₀ ++ Φ₁)} {.([] ++ Ψ₁)} Γ₁ (⊸l∙ {Γ} {.(Γ ++ (∙ , D) ∷ Λ)} {Λ} {Δ = Δ} {D = D} f g refl) h .(isInter++ inTeq' inTeq'') peq | .(tagL Φ₀) , .(tagL Φ₁) , .(black []) , .(black Ψ₁) , inTeq' , inTeq'' , refl , refl , refl | Φ₀ , Φ₁ , refl , refl , refl | [] , Ψ₁ , refl , refl , refl 
    rewrite  ersL-isInter++ inTeq' inTeq'' | isInter++-refl (ersL-isInter inTeq') (ersL-isInter inTeq'')  = {!  !} -- imposs

gen⊗r-eq-f {Γ₀ = .(Φ₀ ++ Φ₁)} {.((x ∷ Ψ₀) ++ Ψ₁)} Γ₁ (⊸l∙ {Γ} {.(Γ ++ (∙ , D) ∷ Λ)} {Λ} {Δ = Δ} {D = D} f g refl) h .(isInter++ inTeq' inTeq'') peq | .(tagL Φ₀) , .(tagL Φ₁) , .(black (x ∷ Ψ₀)) , .(black Ψ₁) , inTeq' , inTeq'' , refl , refl , refl | Φ₀ , Φ₁ , refl , refl , refl | x ∷ Ψ₀ , Ψ₁ , refl , refl , refl  with isInter-split-r [] (black Ψ₀) refl inTeq'
... | Ξ₀ , Ξ₁ , Ω₀ , Ω₁ , inTeq1 , inTeq2 , eq4 , eq5 , eq6 with tagL++? Ξ₀ Ξ₁ Φ₀ eq4 
gen⊗r-eq-f {_} {.((Ξ₀' ++ Ξ₁') ++ Φ₁)} {.((x ∷ Ψ₀) ++ Ψ₁)} Γ₁ (⊸l∙ {Γ} {.(Γ ++ (∙ , D) ∷ Λ)} {Λ} {Δ = Δ} {D = D} f g refl) h .(isInter++ inTeq' inTeq'') peq | .(tagL (Ξ₀' ++ Ξ₁')) , .(tagL Φ₁) , .(black (x ∷ Ψ₀)) , .(black Ψ₁) , inTeq' , inTeq'' , refl , refl , refl | .(Ξ₀' ++ Ξ₁') , Φ₁ , refl , refl , refl | x ∷ Ψ₀ , Ψ₁ , refl , refl , refl | .(tagL Ξ₀') , .(tagL Ξ₁') , Ω₀ , Ω₁ , inTeq1 , inTeq2 , refl , eq5 , eq6 | Ξ₀' , Ξ₁' , refl , refl , refl with cases++ Ω₀ Γ Ω₁ ((∙ , D) ∷ Λ) eq5
gen⊗r-eq-f {_} {.((Ξ₀' ++ Ξ₁') ++ Φ₁)} {.((x ∷ Ψ₀) ++ Ψ₁)} Γ₁ (⊸l∙ {.(Ω₀ ++ (∙ , x) ∷ Θ₀)} {.((Ω₀ ++ (∙ , x) ∷ Θ₀) ++ (∙ , D) ∷ Λ)} {Λ} {Δ = Δ} {D = D} f g refl) h .(isInter++ (isInter++ inTeq1 (∷right' (tagL Ξ₁') inTeq2)) inTeq'') peq | .(tagL (Ξ₀' ++ Ξ₁')) , .(tagL Φ₁) , .(black (x ∷ Ψ₀)) , .(black Ψ₁) , .(isInter++ inTeq1 (∷right' (tagL Ξ₁') inTeq2)) , inTeq'' , refl , refl , refl | .(Ξ₀' ++ Ξ₁') , Φ₁ , refl , refl , refl | x ∷ Ψ₀ , Ψ₁ , refl , refl , refl | .(tagL Ξ₀') , .(tagL Ξ₁') , Ω₀ , .(Θ₀ ++ (∙ , D) ∷ Λ) , inTeq1 , inTeq2 , refl , refl , refl | Ξ₀' , Ξ₁' , refl , refl , refl | inj₁ (Θ₀ , refl , refl) with isInter-left[] inTeq1
... | refl with tag-lem-left[] ([]right' Ξ₀')
gen⊗r-eq-f {_} {.(([] ++ Ξ₁') ++ Φ₁)} {.((x ∷ Ψ₀) ++ Ψ₁)} Γ₁ (⊸l∙ {.(tagL [] ++ (∙ , x) ∷ Θ₀)} {.((tagL [] ++ (∙ , x) ∷ Θ₀) ++ (∙ , D) ∷ Λ)} {Λ} {Δ = Δ} {D = D} f g refl) h .(isInter++ (isInter++ isInter[] (∷right' (tagL Ξ₁') inTeq2)) inTeq'') peq | .(tagL ([] ++ Ξ₁')) , .(tagL Φ₁) , .(black (x ∷ Ψ₀)) , .(black Ψ₁) , .(isInter++ isInter[] (∷right' (tagL Ξ₁') inTeq2)) , inTeq'' , refl , refl , refl | .([] ++ Ξ₁') , Φ₁ , refl , refl , refl | x ∷ Ψ₀ , Ψ₁ , refl , refl , refl | .(tagL []) , .(tagL Ξ₁') , .(tagL []) , .(Θ₀ ++ (∙ , D) ∷ Λ) , isInter[] , inTeq2 , refl , refl , refl | [] , Ξ₁' , refl , refl , refl | inj₁ (Θ₀ , refl , refl) | refl | .(tagL []) , isInter[] , refl 
    rewrite ersL-isInter++ (∷right'{x = (∙ , x)} (tagL Ξ₁') inTeq2) inTeq'' |
            isInter++-refl (∷right' {x = x} Ξ₁' (ersL-isInter inTeq2)) (ersL-isInter inTeq'') |
            isInter-split-r-++-refl {x = x} isInter[] (ersL-isInter inTeq2) = {! isInter++-tag-lem' (ersL-isInter inTeq2) (ersL-isInter inTeq'') !}
gen⊗r-eq-f {_} {.(((x₁ ∷ Ξ₀') ++ Ξ₁') ++ Φ₁)} {.((x ∷ Ψ₀) ++ Ψ₁)} Γ₁ (⊸l∙ {.(tagL (x₁ ∷ Ξ₀') ++ (∙ , x) ∷ Θ₀)} {.((tagL (x₁ ∷ Ξ₀') ++ (∙ , x) ∷ Θ₀) ++ (∙ , D) ∷ Λ)} {Λ} {Δ = Δ} {D = D} f g refl) h .(isInter++ (isInter++ ([]right {x = ∘ , x₁} {xs = tagL Ξ₀'}) (∷right' (tagL Ξ₁') inTeq2)) inTeq'') peq | .(tagL ((x₁ ∷ Ξ₀') ++ Ξ₁')) , .(tagL Φ₁) , .(black (x ∷ Ψ₀)) , .(black Ψ₁) , .(isInter++ ([]right {x = ∘ , x₁} {xs = tagL Ξ₀'}) (∷right' (tagL Ξ₁') inTeq2)) , inTeq'' , refl , refl , refl | .((x₁ ∷ Ξ₀') ++ Ξ₁') , Φ₁ , refl , refl , refl | x ∷ Ψ₀ , Ψ₁ , refl , refl , refl | .(tagL (x₁ ∷ Ξ₀')) , .(tagL Ξ₁') , .(tagL (x₁ ∷ Ξ₀')) , .(Θ₀ ++ (∙ , D) ∷ Λ) , []right , inTeq2 , refl , refl , refl | x₁ ∷ Ξ₀' , Ξ₁' , refl , refl , refl | inj₁ (Θ₀ , refl , refl) | refl | .(tagL (x₁ ∷ Ξ₀')) , []right , refl = {!   !}
    -- rewrite ersL-isInter++ (isInter++l (tagL Ξ₀') (∷right' {x = (∙ , x)} (tagL Ξ₁') inTeq2)) inTeq'' |
    --         isInter++-refl (ersL-isInter (isInter++l (tagL Ξ₀') (∷right' {x = (∙ , x)} (tagL Ξ₁') inTeq2))) (ersL-isInter inTeq'') |
    --         ersL-isInter++l (tagL Ξ₀') (∷right' {x = (∙ , x)} (tagL Ξ₁') inTeq2) |
    --         isInter-split-r-++-refl {x = x} ([]right' Ξ₀') (ersL-isInter inTeq2) |
    --         isInter-left[] ([]right' Ξ₀') = {! tag-lem-left[] ([]right' Ξ₀') !}
-- isInter++-refl (ersL-isInter (isInter++l (tagL Ξ₀') (∷right' (tagL Ξ₁') inTeq2))) (ersL-isInter inTeq'')
gen⊗r-eq-f {_} {.((Ξ₀' ++ Ξ₁') ++ Φ₁)} {.((x ∷ Ψ₀) ++ Ψ₁)} Γ₁ (⊸l∙ {Γ} {.(Γ ++ (∙ , x) ∷ Λ)} {Λ} {Δ = Δ} {D = .x} f g refl) h .(isInter++ (isInter++ inTeq1 (∷right' (tagL Ξ₁') inTeq2)) inTeq'') peq | .(tagL (Ξ₀' ++ Ξ₁')) , .(tagL Φ₁) , .(black (x ∷ Ψ₀)) , .(black Ψ₁) , .(isInter++ inTeq1 (∷right' (tagL Ξ₁') inTeq2)) , inTeq'' , refl , refl , refl | .(Ξ₀' ++ Ξ₁') , Φ₁ , refl , refl , refl | x ∷ Ψ₀ , Ψ₁ , refl , refl , refl | .(tagL Ξ₀') , .(tagL Ξ₁') , Γ , Λ , inTeq1 , inTeq2 , refl , refl , refl | Ξ₀' , Ξ₁' , refl , refl , refl | inj₂ ([] , refl , refl) with isInter-left[] inTeq1
gen⊗r-eq-f {_} {.(([] ++ Ξ₁') ++ Φ₁)} {.((x ∷ Ψ₀) ++ Ψ₁)} Γ₁ (⊸l∙ {.(tagL [])} {.(tagL [] ++ (∙ , x) ∷ Λ)} {Λ} {Δ = Δ} {_} {_} {x} f g refl) h .(isInter++ (isInter++ isInter[] (∷right' (tagL Ξ₁') inTeq2)) inTeq'') peq | .(tagL ([] ++ Ξ₁')) , .(tagL Φ₁) , .(black (x ∷ Ψ₀)) , .(black Ψ₁) , .(isInter++ isInter[] (∷right' (tagL Ξ₁') inTeq2)) , inTeq'' , refl , refl , refl | .([] ++ Ξ₁') , Φ₁ , refl , refl , refl | x ∷ Ψ₀ , Ψ₁ , refl , refl , refl | .(tagL []) , .(tagL Ξ₁') , .(tagL []) , Λ , isInter[] , inTeq2 , refl , refl , refl | [] , Ξ₁' , refl , refl , refl | inj₂ ([] , refl , refl) | refl 
    rewrite ersL-isInter++ (∷right' {x = (∙ , x)} (tagL Ξ₁') inTeq2) inTeq'' | 
            isInter++-refl (∷right' {x = x} Ξ₁' (ersL-isInter inTeq2)) (ersL-isInter inTeq'') |
            isInter-split-r-++-refl {x = x} isInter[] (ersL-isInter inTeq2) |
            sym (isInter++-∷right' {x = (∙ , x)} (tagL Ξ₁') (tag-lem' (ersL-isInter inTeq2)) (tag-lem' (ersL-isInter inTeq''))) = {!tag-isInter-ersL-isInter-refl Ξ₁' Ψ₀ Λ inTeq2   !} -- tag-isInter-ersL-isInter problem
gen⊗r-eq-f {_} {.(((x₁ ∷ Ξ₀') ++ Ξ₁') ++ Φ₁)} {.((x ∷ Ψ₀) ++ Ψ₁)} Γ₁ (⊸l∙ {.(tagL (x₁ ∷ Ξ₀'))} {.(tagL (x₁ ∷ Ξ₀') ++ (∙ , x) ∷ Λ)} {Λ} {Δ = Δ} {_} {_} {x} f g refl) h .(isInter++ (isInter++ inTeq1 (∷right' (tagL Ξ₁') inTeq2)) inTeq'') peq | .(tagL ((x₁ ∷ Ξ₀') ++ Ξ₁')) , .(tagL Φ₁) , .(black (x ∷ Ψ₀)) , .(black Ψ₁) , .(isInter++ inTeq1 (∷right' (tagL Ξ₁') inTeq2)) , inTeq'' , refl , refl , refl | .((x₁ ∷ Ξ₀') ++ Ξ₁') , Φ₁ , refl , refl , refl | x ∷ Ψ₀ , Ψ₁ , refl , refl , refl | .(tagL (x₁ ∷ Ξ₀')) , .(tagL Ξ₁') , .(tagL (x₁ ∷ Ξ₀')) , Λ , inTeq1 , inTeq2 , refl , refl , refl | x₁ ∷ Ξ₀' , Ξ₁' , refl , refl , refl | inj₂ ([] , refl , refl) | refl = {!   !}
gen⊗r-eq-f {_} {.((Ξ₀' ++ Ξ₁') ++ Φ₁)} {.((x ∷ Ψ₀) ++ Ψ₁)} Γ₁ (⊸l∙ {Γ} {.(Γ ++ (∙ , D) ∷ Θ₀ ++ (∙ , x) ∷ Ω₁)} {.(Θ₀ ++ (∙ , x) ∷ Ω₁)} {Δ = Δ} {D = D} f g refl) h .(isInter++ (isInter++ inTeq1 (∷right' (tagL Ξ₁') inTeq2)) inTeq'') peq | .(tagL (Ξ₀' ++ Ξ₁')) , .(tagL Φ₁) , .(black (x ∷ Ψ₀)) , .(black Ψ₁) , .(isInter++ inTeq1 (∷right' (tagL Ξ₁') inTeq2)) , inTeq'' , refl , refl , refl | .(Ξ₀' ++ Ξ₁') , Φ₁ , refl , refl , refl | x ∷ Ψ₀ , Ψ₁ , refl , refl , refl | .(tagL Ξ₀') , .(tagL Ξ₁') , .(Γ ++ (∙ , D) ∷ Θ₀) , Ω₁ , inTeq1 , inTeq2 , refl , refl , refl | Ξ₀' , Ξ₁' , refl , refl , refl | inj₂ (.(∙ , D) ∷ Θ₀ , refl , refl) = {! inTeq1  !} -- imposs


-- with isInter-split-r [] (black Ψ₀) refl inTeq'
-- ... | Ξ₀ , Ξ₁ , Ω₀ , Ω₁ , inTeq1 , inTeq2 , eq4 , eq5 , eq6    = {! eq5  !}
-- rewrite  ersL-isInter++ inTeq' inTeq'' | isInter++-refl (ersL-isInter inTeq') (ersL-isInter inTeq'')
-- isInter++-refl (ersL-isInter inTeq') (ersL-isInter inTeq'')
-- with isInter++? Γ ((∙ , D) ∷ Λ) refl inTeq'
-- ... | Ξ₀ , Ξ₁ , Ω₀ , Ω₁ , inTeq1 , inTeq2 , eq4 , eq5 , eq6 with tagL++? Ξ₀ Ξ₁ Φ₀ eq4 | black++? Ω₀ Ω₁ Ψ₀ eq5
-- gen⊗r-eq-f {_} {.((Φ₀' ++ Φ₁') ++ Φ₁)} {.((Ψ₀' ++ Ψ₁') ++ Ψ₁)} Γ₁ (⊸l∙ {Γ} {.(Γ ++ (∙ , D) ∷ Λ)} {Λ} {Δ = Δ} {D = D} f g refl) h .(isInter++ (isInter++ inTeq1 inTeq2) inTeq'') peq | .(tagL (Φ₀' ++ Φ₁')) , .(tagL Φ₁) , .(black (Ψ₀' ++ Ψ₁')) , .(black Ψ₁) , .(isInter++ inTeq1 inTeq2) , inTeq'' , refl , refl , refl | .(Φ₀' ++ Φ₁') , Φ₁ , refl , refl , refl | .(Ψ₀' ++ Ψ₁') , Ψ₁ , refl , refl , refl | .(tagL Φ₀') , .(tagL Φ₁') , .(black Ψ₀') , .(black Ψ₁') , inTeq1 , inTeq2 , refl , refl , refl | Φ₀' , Φ₁' , refl , refl , refl | Ψ₀' , Ψ₁' , refl , refl , refl 
--     rewrite ersL-isInter++ (isInter++ inTeq1 inTeq2) inTeq'' |
--             isInter++-refl (isInter++ (ersL-isInter inTeq1) (ersL-isInter inTeq2)) (ersL-isInter inTeq'') = {!    !}


    -- rewrite ersL-isInter++ inTeq' inTeq'' | isInter++-refl (ersL-isInter inTeq') (ersL-isInter inTeq'') = {! Γ₁₀'  !}
-- with isInter++? Γ' Δ refl inTeq
-- gen⊗r-eq-f {Γ₀ = Γ₀} {Γ₁'} Γ₁ (⊸l∙ {Γ} {Γ'} {Δ = Δ} f g eq) h inTeq peq | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , inTeq' , inTeq'' , eq1 , eq2 , eq3 with tagL++? Γ₀₀ Γ₀₁ Γ₀ eq1 | black++? Γ₁₀' Γ₁₁' Γ₁' eq2 
-- gen⊗r-eq-f {Γ₀ = .(Φ₀ ++ Φ₁)} {.(Ψ₀ ++ Ψ₁)} Γ₁ (⊸l∙ {Γ} {.(Γ ++ (∙ , _) ∷ _)} {Δ = Δ} f g refl) h .(isInter++ inTeq' inTeq'') peq | .(tagL Φ₀) , .(tagL Φ₁) , .(black Ψ₀) , .(black Ψ₁) , inTeq' , inTeq'' , refl , refl , refl | Φ₀ , Φ₁ , refl , refl , refl | Ψ₀ , Ψ₁ , refl , refl , refl 
--     rewrite ersL-isInter++ inTeq' inTeq'' | isInter++-refl (ersL-isInter inTeq') (ersL-isInter inTeq'') = {!   !}
-- isInter++-refl (ersL-isInter inTeq') (ersL-isInter inTeq'')

-- ⊸r⋆∙-eq : {S : Stp} {Γ Γ' Γ₀ : TCxt} → {Γ₁' : Cxt} (Γ₁ : Cxt) {A' A : Fma} →
--       (f :  just A' ∣ ersL Γ ⊢li A) (eq : ersL Γ ≡ ersL Γ') (inTeq1 : isInter Γ₀ (black Γ₁') Γ) (inTeq2 : isInter Γ₀ (black Γ₁') Γ') (peq : Γ₁' ↭' Γ₁) → 
--       ----------------------------------------
--       ⊸r⋆∙ Γ₁ (li2ri (p2li (pass∙ f))) inTeq1 peq ≡ ⊸r⋆∙ Γ₁ (subst (λ x → ∙ ∣ S ∣ x ⊢ri A)  eq f) inTeq2 peq

gen⊗r-eq-p : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ' : TCxt} (Γ₁ : Cxt) {A : Pos} {B : Fma} 
    → (f : ∙ ∣ S ∣ Γ' ⊢p A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter (tagL Γ₀) (black Γ₁') Γ') (peq : Γ₁' ↭' Γ₁)
    → gen⊗r-p Γ₁ (p∙2p f) g (ersL-isInter inTeq) peq 
        ≡ f2p (⊗r (⊸r⋆∙ {Γ = Γ'} Γ₁ (li2ri (p2li f)) inTeq peq) g)
gen⊗r-eq-p {Γ₀ = []} {Γ₁' = []} Γ₁ (pass∙ f) g () peq
gen⊗r-eq-p {Γ₀ = x ∷ Γ₀} {Γ₁' = []} Γ₁ (pass∙ f) g () peq
gen⊗r-eq-p {Γ₀ = []} {Γ₁' = x ∷ Γ₁'} Γ₁ (pass∙ f) g []left peq = refl
gen⊗r-eq-p {Γ₀ = x₁ ∷ Γ₀} {Γ₁' = x ∷ Γ₁'} Γ₁ (pass∙ {Γ} f) g (∷right inTeq) peq =
-- cong f2p (cong (λ x → ⊗r {Γ = x₁ ∷ Γ₀} x g) {! sym (⊸r⋆∙-eq Γ₁ (li2ri (p2li (pass∙ f))) (cong (λ y → (∙ , x) ∷ y) (sym (tag-isInter-ersL-isInter-refl (x₁ ∷ Γ₀) Γ₁' Γ inTeq))) (∷right inTeq) (∷right (tag-lem' (ersL-isInter inTeq)))  peq) !})
--   rewrite sym (tag-isInter-ersL-isInter-refl (x₁ ∷ Γ₀) Γ₁' Γ inTeq) = 
  begin
    f2p (⊗r {Γ = x₁ ∷ Γ₀} (⊸r⋆∙ {Γ = (∙ , x) ∷ tag-isInter (ersL-isInter inTeq)} Γ₁ (li2ri (p2li {Γ = (∙ , x) ∷ tag-isInter (ersL-isInter inTeq)} (pass∙ {Γ = tag-isInter (ersL-isInter inTeq)} f))) (∷right (tag-lem' (ersL-isInter inTeq))) peq) g)
  ≡⟨ cong (λ x → f2p (⊗r {Γ = x₁ ∷ Γ₀} x g)) {!   !} ⟩
    f2p (⊗r {Γ = x₁ ∷ Γ₀} (⊸r⋆∙ {Γ = (∙ , x) ∷ Γ} Γ₁ (li2ri (p2li (pass∙ f))) (∷right inTeq) peq) g)
  ∎ 
    -- rewrite tag-lem-ersL-refl (x₁ ∷ Γ₀) Γ₁' Γ inTeq = ?
    -- cong f2p (cong (λ x → ⊗r (⊸r⋆∙ Γ₁ (li2ri (p2li (pass∙ f))) (∷right x) peq) g) {!   !}) -- rewrite tag-lem-ersL-refl (x₁ ∷ Γ₀) Γ₁' Γ inTeq = ?
gen⊗r-eq-p Γ₁ (f2p f) g inTeq peq = cong f2p (gen⊗r-eq-f Γ₁ f g inTeq peq)

gen⊗r-eq-p' : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ' : TCxt} (Γ₁ : Cxt) {A : Pos} {B : Fma} 
    → (f : ∙ ∣ S ∣ Γ' ⊢p A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter (tagL Γ₀) (black Γ₁') Γ') (peq : Γ₁' ↭' Γ₁)
    → p2li (gen⊗r-p Γ₁ (p∙2p f) g (ersL-isInter inTeq) peq) 
        ≡ p2li {S = S} (f2p (⊗r (⊸r⋆∙ Γ₁ (li2ri (p2li f)) inTeq peq) g))
gen⊗r-eq-p' Γ₁ f g inTeq peq = {!   !}
gen⊗r-eq-li : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ' : TCxt} (Γ₁ : Cxt) {A : Pos} {B : Fma} 
    → (f : ∙ ∣ irr S ∣ Γ' ⊢li A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter (tagL Γ₀) (black Γ₁') Γ') (peq : Γ₁' ↭' Γ₁)
    → gen⊗r-li Γ₁ (li∙2li f) g (ersL-isInter inTeq) peq 
        ≡ p2li {S = S} (f2p (⊗r (⊸r⋆∙ Γ₁ (li2ri f) inTeq peq) g))
gen⊗r-eq-li {.(irr (just (` x) , snd)) , snd₁} {Γ₀ = Γ₀} Γ₁ (p2li {S = just (` x) , snd} f) g inTeq peq = cong p2li (gen⊗r-eq-p Γ₁ f g inTeq peq)
gen⊗r-eq-li {.(irr (just (x ⊸ x₁) , snd)) , snd₁} {Γ₀ = Γ₀} Γ₁ (p2li {S = just (x ⊸ x₁) , snd} f) g inTeq peq = cong p2li {!   !}
gen⊗r-eq-li {.(irr (- , snd)) , snd₁} {Γ₀ = Γ₀} Γ₁ (p2li {S = - , snd} f) g inTeq peq = {! snd  !}
-- cong {!  λ x → p2li x !} (gen⊗r-eq-p {S = fst , snd} {Γ₀ = Γ₀} Γ₁ {!   !} g inTeq peq) 

gen⊗r-eq : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ' : TCxt} (Γ₁ : Cxt) {A B : Fma} 
    → (f : ∙ ∣ irr S ∣ Γ' ⊢ri A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter (tagL Γ₀) (black Γ₁') Γ') (peq : Γ₁' ↭' Γ₁)
    → gen⊗r-ri Γ₁ (ri∙2ri f) g (ersL-isInter inTeq) peq 
        ≡ p2li {S = S} (f2p (⊗r (⊸r⋆∙ Γ₁ f inTeq peq) g))
gen⊗r-eq Γ₁ (⊸r∙ (ex∙ (ex∙ {Γ = x ∷ Γ} f refl refl) eq' eq)) g inTeq peq = ⊥-elim ([]disj∷ Γ (proj₂ (inj∷ eq'))) -- imposs
gen⊗r-eq Γ₁ (⊸r∙ (ex∙ {Δ = Δ} {Λ} (ri2c f) refl refl)) g inTeq peq with isInter++? Δ Λ refl inTeq
gen⊗r-eq {Γ₀ = Γ₀} {Γ₁'} Γ₁ (⊸r∙ (ex∙ {Δ = Δ} {Λ} (ri2c f) refl refl)) g inTeq peq | Γ₀₀ , Γ₀₁ , Γ₁₀' , Γ₁₁' , inTeq' , inTeq'' , eq1 , eq2 , eq3 with tagL++? Γ₀₀ Γ₀₁ Γ₀ eq1 | black++? Γ₁₀' Γ₁₁' Γ₁' eq2 
gen⊗r-eq {S = S} {Γ₀ = .(Φ₀ ++ Φ₁)} {.(Ψ₀ ++ Ψ₁)} {Δ₁} Γ₁ (⊸r∙ {A = A} (ex∙ {Δ = Δ} {Λ} (ri2c f) refl refl)) g .(isInter++ inTeq' inTeq'') peq | .(tagL Φ₀) , .(tagL Φ₁) , .(black Ψ₀) , .(black Ψ₁) , inTeq' , inTeq'' , refl , refl , refl | Φ₀ , Φ₁ , refl , refl , refl | Ψ₀ , Ψ₁ , refl , refl , refl 
    rewrite isInter++-refl (ersL-isInter inTeq') (ersL-isInter inTeq'') |
            ⊸r⋆∙⊸r∙ {Δ₁ = Ψ₀} {Ψ₁} Γ₁ f refl inTeq' inTeq'' peq = {!   !}
        -- trans (gen⊗r-eq {S = S} {Γ₀ = Φ₀ ++ Φ₁} {Ψ₀ ++ A ∷ Ψ₁} {Δ = Δ₁} (Γ₁ ++ A ∷ []) f g (isInter++ inTeq' (∷right' {x = (∙ , A)} (tagL Φ₁) inTeq'')) (snoc↭' {xs₀ = Ψ₀} {Ψ₁} refl peq)) 
        -- (cong (λ x → p2li (f2p x)) ((subst (λ x → ⊗r {Γ = Φ₀ ++ Φ₁} x g ≡ ⊗r {Γ = Φ₀ ++ Φ₁} (⊸r⋆∙ Γ₁ (⊸r∙ {A = A} (ex∙ {Δ = Δ} {Λ} (ri2c f) refl refl)) (isInter++ inTeq' inTeq'') peq) g) (sym (⊸r⋆∙⊸r∙ {Δ₁ = Ψ₀} {Ψ₁} Γ₁ f refl inTeq' inTeq'' peq)) refl)))
        
gen⊗r-eq Γ₁ (li2ri f) g inTeq peq = gen⊗r-eq-li Γ₁ f g inTeq peq



-- gen⊗r-eq' : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ' : TCxt} (Γ₁ : Cxt) {A B : Fma} 
--     → (f : ∙ ∣ irr S ∣ Γ' ⊢ri A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter Γ₀ Γ₁' (ersL Γ')) (peq : Γ₁' ↭' Γ₁)
--     → gen⊗r-ri Γ₁ (ri∙2ri f) g inTeq peq 
--         ≡ p2li {S = S} (f2p (⊗r (⊸r⋆∙ Γ₁ f {!   !} peq) g))

-- gen⊗r-eq' : {S : Irr} {Γ₀ Γ₁' Δ : Cxt} {Γ' : TCxt} (Γ₁ : Cxt) {A B : Fma} 
--     → (f : ∙ ∣ irr S ∣ Γ' ⊢ri A) (g : - ∣ Δ ⊢ri B) (inTeq : isInter (tagL Γ₀) (black Γ₁') Γ') (peq : Γ₁' ↭' Γ₁)
--     → gen⊗r-ri Γ₁ (ri∙2ri f) g (ersL-isInter inTeq) peq 
--         ≡ p2li {S = S} (f2p (⊗r (⊸r⋆∙ Γ₁ f inTeq peq) g))


-- ex-c-iso : {S : Stp} {Λ Φ Ψ Γ : Cxt} {A B C : Fma}
--     → (f : S ∣ Λ ؛ Γ ⊢c C) (eq : Λ ≡ Φ ++ A ∷ B ∷ Ψ)
--     → ex-c' Φ (ex-c' Φ f eq) refl ≡ subst (λ x → S ∣ x ؛ Γ ⊢c C) eq f
-- ex-c-iso {Φ = Φ} {Ψ} {A = A} {B} (ex {Γ = Γ} {A = A'} f refl eq₁) eq with cases++ Γ Φ [] (A ∷ B ∷ Ψ) (sym eq)
-- ... | inj₁ (Ω₀ , p , p') = ⊥-elim ([]disj∷ Ω₀ p') -- imposs
-- ex-c-iso {Φ = Φ} {.[]} {A = D} {B} (ex {Γ = .(_ ++ _ ∷ [])} {Δ₁} {Λ₁} {A = B} (ex {Γ = Γ} {Δ = Δ} {Λ} f refl refl) refl eq₁) eq | inj₂ (D ∷ [] , refl , p') with snoc≡ Γ Φ p' | cases++ Δ₁ Δ Λ₁ Λ eq₁
-- ex-c-iso {Φ = Φ} {.[]} {_} {D} {B} (ex {_} {.(Φ ++ _ ∷ [])} {Δ₁} {.(Ω₁ ++ Λ)} (ex {Γ = .Φ} {Δ = .(Δ₁ ++ B ∷ Ω₁)} {Λ} f refl refl) refl refl) refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | inj₁ (Ω₁ , refl , refl) 
--     rewrite cases++-inj₂ (B ∷ []) Φ [] D | cases++-inj₂ Ω₁ Δ₁ Λ D | snoc≡-refl Φ B = refl
-- ex-c-iso {Φ = Φ} {.[]} {_} {D} {B} (ex {_} {.(Φ ++ _ ∷ [])} {.(Δ ++ Ω₁)} {Λ₁} (ex {Γ = .Φ} {Δ = Δ} {.(Ω₁ ++ B ∷ Λ₁)} f refl refl) refl refl) refl | inj₂ (D ∷ [] , refl , refl) | refl , refl | inj₂ (Ω₁ , refl , refl) 
--     rewrite cases++-inj₂ (B ∷ []) Φ [] D | cases++-inj₁ Δ Ω₁ Λ₁ D | snoc≡-refl Φ B = refl
-- ex-c-iso {Φ = Φ} {Ψ} {A = A} {B} (ex {Γ = .[]} {A = A'} (ri2c f) refl eq₁) eq | inj₂ (D ∷ [] , p , p') = ⊥-elim ([]disj∷ Φ p') -- imposs
-- ex-c-iso {Φ = Φ} {.(Ω₀ ++ A' ∷ [])} {A = A} {B} (ex {Γ = .(Φ ++ A ∷ B ∷ Ω₀)} {A = A'} f refl refl) refl | inj₂ (A ∷ B ∷ Ω₀ , refl , refl) rewrite cases++-inj₂ (B ∷ A ∷ Ω₀) Φ [] A' = cong (λ x → ex {Γ = Φ ++ A ∷ B ∷ Ω₀} x refl refl) (ex-c-iso f refl)
-- ex-c-iso {Φ = Φ} (ri2c f) eq = ⊥-elim ([]disj∷ Φ eq) -- imposs

-- ex-fma-cxt-c-iso2 : {S : Stp} → {Γ Δ Ω : Cxt} (Λ : Cxt) → {A C : Fma}
--   → {f : S ∣ Γ ++ Λ ++ A ∷ Δ ؛ Ω ⊢c C}
--   → ex-fma-cxt-c {Γ = Γ}{Δ} Λ (ex-cxt-fma-c {Γ = Γ} Λ f) ≡ f
-- ex-fma-cxt-c-iso2 [] = refl
-- ex-fma-cxt-c-iso2 {Γ = Γ} {Δ} (A' ∷ Λ) {f = f} = 
--     trans (cong (ex-fma-cxt-c Λ) (ex-c-iso {Φ = Γ} {Λ ++ Δ} (ex-cxt-fma-c {Γ = Γ ++ A' ∷ []} Λ f) refl)) (ex-fma-cxt-c-iso2 Λ)

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
            focus (emb-ri∙ f) ≡ act⋆ [] (ersL Γ) (ri2c (ri∙2ri f))
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
        (trans {!   !} -- (gen⊗r-eq {S = S} {Δ = Δ} [] f g ([]right' (tagL Γ)) (empty refl)) 
        (cong (λ x → p2li (f2p x)) 
        (subst (λ x → ⊗r x g ≡ ⊗r f g) (sym (⊸r⋆∙[] f ([]right' (tagL Γ)))) refl)))))))
    focusemb-f (⊸l {Γ} {Δ} f g) = 
        trans (cong₂ (λ x → λ y → ⊸l-c x y) (focusemb-ri f) (focusemb-li g)) 
        (trans (act⋆⊸l-c Γ [] Δ (ri2c f) (ri2c (li2ri g))) 
        (trans (cong (act⋆ Γ Δ) (act⋆⊸l-c-ri [] Γ (ri2c f) (li2ri g))) (act⋆act⋆ [] Γ Δ)))
    focusemb-f∙ : {S : Irr} {Γ : TCxt} {C : Pos}
            (f : ∙ ∣ S ∣ Γ ⊢f C) → 
            focus (emb-f∙ f) ≡ act⋆ [] (ersL Γ) (ri2c (li2ri (p2li (f2p (f∙2f f)))))
    focusemb-f∙ ax = refl
    focusemb-f∙ Ir = refl
    focusemb-f∙ {S = S} (⊗r {Γ = Γ} {Δ} f g) 
        rewrite sym (whiteErs Γ) = 
            trans (cong₂ (λ x → λ y → ⊗r-c x y) (focusemb-ri∙ f) (focusemb-ri g)) 
            (trans (act⋆⊗r-c (ersL Γ) [] (ersL Δ) (ri2c (ri∙2ri f)) (ri2c g)) 
            (trans (cong (act⋆ (ersL Γ) (ersL Δ)) (act⋆⊗r-c-ri [] (ersL Γ) (ri2c (ri∙2ri f)) g)) 
            (trans (act⋆act⋆ [] (ersL Γ) (ersL Δ)) (cong (λ x → act⋆ [] (ersL Γ ++ ersL Δ) (ri2c (li2ri x))) 
            (trans (gen⊗r-eq {S = S} [] f g ([]right' (whiteL Γ)) (empty refl)) (cong (λ x → p2li (f2p x)) 
            (subst (λ x → ⊗r x g ≡ ⊗r f g) (sym (⊸r⋆∙[] f ([]right' (whiteL Γ)))) refl)))))))
    focusemb-f∙ (⊸l∙ {Γ} {Λ = Λ} {Δ = Δ} f g refl) = 
        trans (cong₂ (λ x → λ y → ⊸l-c x y) (focusemb-ri f) (focusemb-li g)) 
        (trans (act⋆⊸l-c (ersL Γ ++ _ ∷ ersL Λ) [] (ersL Δ) (ri2c f) (ri2c (li2ri g))) 
        (trans (cong (act⋆ (ersL Γ ++ _ ∷ ersL Λ) (ersL Δ)) (act⋆⊸l-c-ri [] (ersL Γ ++ _ ∷ ersL Λ) (ri2c f) (li2ri g))) 
        ((act⋆act⋆ [] (ersL Γ ++ _ ∷ ersL Λ) (ersL Δ)))))      

                    