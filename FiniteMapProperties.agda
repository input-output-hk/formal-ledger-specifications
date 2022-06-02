{-# OPTIONS --safe #-}

open import DecEq
open import Data.List
open import FiniteMap
open import Data.Product hiding (map)
open import Utilities.ListProperties renaming (_∈_ to _∈l_)
open import Utilities.Logic hiding (DecEq)
open import Function
open import Data.Sum hiding (map)
open import Relation.Nullary
open import Data.List.Properties
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Function.Properties.Equivalence
open import Level
open import Relation.Binary.PropositionalEquality using (subst; sym; refl; _≡_; inspect; [_]; cong; trans) --maybe not nceccessary

module FiniteMapProperties {X : Set}{Y : Set}{{eq : DecEq X}}{{eq' : DecEq Y}} where

open import FinMap2

private
  variable
    a b : X × Y
    l : List (X × Y)
    s s' s''  : FinMap X Y {{eq}} {{eq'}}


∈⇒∈l : a ∈ᵐ s → a ∈l (listOfᵐ s)
∈⇒∈l = id

∈l⇒∈ : a ∈l (listOfᵐ s) → a ∈ᵐ s
∈l⇒∈ = id

--the from list proofs are no longer needed for filter because filter no long uses from list
--∈l⇒∈fromList : a ∈l l → NoDupInd (map proj₁ l) → a ∈ᵐ fromList' l
--∈l⇒∈fromList h = {!!}

∈fromList⇒∈l : a ∈ᵐ fromList' l → a ∈l l
∈fromList⇒∈l h = remDupCompleteᵐ (eq2in _) _ _ h

∈∪⇒∈⊎ : a ∈ᵐ s ∪ᵐ s' → a ∈ᵐ s ⊎ a ∈ᵐ s'
∈∪⇒∈⊎ h = ∈-split (remDupCompleteᵐ (eq2in _) _ _ h)

∪ᵐʳ : a ∈ᵐ s → a ∈ᵐ s' ∪ᵐ s
∪ᵐʳ {a} {fs-nojunk els {p}} {fs-nojunk els₁} xin
  = dup∈ʳ (eq2in _) a els els₁ xin
          (NoDupInd-corr2 (map proj₁ els)
          (∥-∥-prop3 _ p))

∪ᵐˡ : a ∈ᵐ s' × a ∉ᵖᵐ s → a ∈ᵐ s' ∪ᵐ s
∪ᵐˡ {a} {fs-nojunk els {p}} {fs-nojunk els₁} (xin , notin)
  = dup∈ˡ (eq2in _) a els₁ els xin notin (NoDupInd-corr2 (map proj₁ els) (∥-∥-prop3 _ p))

∈⊎⇒∈∪ : (a ∈ᵐ s × a ∉ᵖᵐ s') ⊎ a ∈ᵐ s' → a ∈ᵐ s ∪ᵐ s'
∈⊎⇒∈∪ {a} {s} {s'} (inj₁ x) = ∪ᵐˡ {a} {s} {s'} x
∈⊎⇒∈∪ {a} {s} {s'} (inj₂ y) = ∪ᵐʳ {a} {s'} {s} y


∪ᵐʳ⁻Helper : a ∈ᵐ s → a ∈ᵖᵐ s' → ¬ a ∈ᵐ s' → ¬ a ∈ᵐ s ∪ᵐ s'
∪ᵐʳ⁻Helper {a} {fs-nojunk els'} {fs-nojunk els {prf}} h h₁ h₃ with getPair (proj₁ a) els h₁
... | ans with (_≟_ {{eq'}}) (getValue (proj₁ a) els h₁) (proj₂ a)
... | yes refl = ⊥-elim (h₃ ans)
... | no ¬p with dup∈ʳ (eq2in _) _ els els' ans
                       (NoDupInd-corr2 (map proj₁ els) (∥-∥-prop3 _ prf))
... | res = NoDupProjUnique (proj₁ a) _ (proj₂ a) _ res
                            (NoDupInd-corr2 _ (remDupCorrectᵐ (eq2in (_≟_ {{eq}})) (els' ++ els))) ¬p


∪ᵐʳ⁻ : a ∈ᵐ s ∪ᵐ s' → a ∈ᵖᵐ s' → a ∈ᵐ s → a ∈ᵐ s'
∪ᵐʳ⁻ {a} {s} {fs-nojunk els {prf}} h h' h'' with eq2inᵖ eq eq' a els
... | yes p = p
... | no ¬p = ⊥-elim (∪ᵐʳ⁻Helper {a} {s} {fs-nojunk els {prf}} h'' h' ¬p h)


∈∪⇒∈⊎' : a ∈ᵐ s ∪ᵐ s' → (a ∈ᵐ s × a ∉ᵖᵐ s') ⊎ a ∈ᵐ s'
∈∪⇒∈⊎' {a} {s} {fs-nojunk els' {prf}} h with eq2inᵐ eq (proj₁ a) (map proj₁ els')
                                                | ∈∪⇒∈⊎ {a} {s} {(fs-nojunk els' {prf})} h
... | no ¬p | inj₁ x = inj₁ (x , ¬p)
... | yes p | inj₁ x = inj₂ (∪ᵐʳ⁻ {a} {s} {fs-nojunk els' {prf}} h p x) -- if → a ∈ᵐ s ∪ᵐ s' → proj₁ a ∈ ys → a ∈ ys
... | no ¬p | inj₂ y = inj₂ y
... | yes p | inj₂ y = inj₂ y

∈⊎⇔∈∪ : ((a ∈ᵐ s × a ∉ᵖᵐ s') ⊎ a ∈ᵐ s') ⇔ a ∈ᵐ s ∪ᵐ s'
∈⊎⇔∈∪ {s = s} {s'} = mk⇔ (∈⊎⇒∈∪ {s = s} {s' = s'}) (∈∪⇒∈⊎' {s = s} {s' = s'})

∈-⊎↔∪≡ : (∀ a → ((a ∈ᵐ s × a ∉ᵖᵐ s') ⊎ a ∈ᵐ s') ⇔ a ∈ᵐ s'') → s ∪ᵐ s' ≡ᵐ s''
∈-⊎↔∪≡ {s} {s'} {s''} h a =
       begin
         a ∈ᵐ s ∪ᵐ s'       ≈˘⟨ ∈⊎⇔∈∪ {s = s} {s' = s'} ⟩
         ((a ∈ᵐ s × a ∉ᵖᵐ s') ⊎ a ∈ᵐ s') ≈⟨ h a ⟩
         a ∈ᵐ s''          ∎
         where open SetoidReasoning (⇔-setoid 0ℓ)

{-
∈×⇒∈∩ : (a ∈ s × a ∈ s') → a ∈ s ∩ s'
∈×⇒∈∩ {a} {s} {s'} (h₁ , h₂) =
  set-monad-ht a s (λ x → for y ∈ s' as true , if ⌊ x ≟ y ⌋ then return {b = true} x) a false h₁ $
    set-monad-ht a s' (λ y → if ⌊ a ≟ y ⌋ then return {b = true} a) a true h₂ $
      subst (λ b → a ∈l listOf (if b then return a)) (sym $ ≡ᵇ-refl {a = a}) (here refl)

∈∩⇒∈× : a ∈ s ∩ s' → a ∈ s × a ∈ s'
∈∩⇒∈× {a} {s} {s'} h with set-monad-th a s (λ x → for y ∈ s' as true , if ⌊ x ≟ y ⌋ then return {b = true} x) false h
... | a₁ , h₁ , h₂ with set-monad-th a s' (λ y → if ⌊ a₁ ≟ y ⌋ then return {b = true} a₁) true h₂
... | a₂ , h'₁ , h'₂ with a₁ ≟ a₂
... | no ¬p = case h'₂ of λ ()
... | yes p with h'₂
... | (here refl) = (h₁ , subst (λ x → x ∈l listOf s') (sym p) h'₁)

∈×⇔∈∩ : (a ∈ s × a ∈ s') ⇔ a ∈ s ∩ s'
∈×⇔∈∩ {s = s} {s'} = mk⇔ (∈×⇒∈∩ {s = s} {s' = s'}) (∈∩⇒∈× {s = s} {s' = s'})

∈-×↔∩≡ : (∀ a → (a ∈ s × a ∈ s') ⇔ a ∈ s'') → s ∩ s' ≡ᵉ s''
∈-×↔∩≡ {s} {s'} {s''} h a = begin
  a ∈ s ∩ s'       ≈˘⟨ ∈×⇔∈∩ {s = s} {s' = s'} ⟩
  (a ∈ s × a ∈ s') ≈⟨ h a ⟩
  a ∈ s''          ∎
  where open SetoidReasoning (⇔-setoid 0ℓ)


omelkonian.github.io

record lift

All' Any'

Prelude.Sets.AsUniqueLists.html

sum over all values and sum has to be commutative

https://omelkonian.github.io/formal-prelude/Prelude.Sets.AsUniqueLists.html

-}

∈→filter' : {P : (X × Y) → Set} → (P? : ∀ a → Dec (P a)) → (a : (X × Y)) → a ∈l l → P a → a ∈l filter P? l
∈→filter' {x ∷ l} P? .x (here refl) h' rewrite filter-accept P? {xs = l} h' = here refl
∈→filter' {x ∷ l} P? a (there h) h' with P? x
... | no ¬p = ∈→filter' P? a h h'
... | yes p = there $ ∈→filter' P? a h h'

∈→filter : {P : (X × Y) → Set} → (P? : ∀ a → Dec (P a)) → (a : (X × Y))
              → a ∈ᵐ s → P a
              → a ∈ᵐ filterᵐ P? s
∈→filter {fs-nojunk els {prf}} P? a h h' = ∈→filter' P? a h h'

filter→∈' : {P : (X × Y) → Set} → (P? : ∀ a → Dec (P a)) → (a : (X × Y))
            → a ∈l filter P? l
            → a ∈l l × P a
filter→∈' {x ∷ l} P? a h with P? x
... | no ¬p = Data.Product.map₁ there (filter→∈' P? a h)
filter→∈' {x ∷ l} P? .x (here refl) | yes p = here refl , p
filter→∈' {x ∷ l} P? a (there h) | yes p = Data.Product.map₁ there (filter→∈' P? a h)

filter→∈ : {P : (X × Y) → Set} → (P? : ∀ a → Dec (P a)) → (a : (X × Y)) → a ∈ᵐ filterᵐ P? s → a ∈ᵐ s × P a
filter→∈ {fs-nojunk els} P? a h = filter→∈' P? a h

∈filter : {P : (X × Y) → Set} → (P? : ∀ a → Dec (P a)) → (a : (X × Y)) → (a ∈ᵐ s × P a) ⇔ a ∈ᵐ filterᵐ P? s
∈filter {s} P? a = mk⇔ (λ { (h , h') → ∈→filter {s = s} P? a h h' }) (filter→∈ {s = s} P? a)

∈-∅ : ∀ {x} → ¬ x ∈ᵐ (∅ {{eq}} {{eq'}})
∈-∅ ()

open import Agda.Builtin.Nat

helpMe : List (Nat × Nat)
helpMe = (1 , 2) ∷ (3 , 4) ∷ (4 , 5) ∷ []

helpMe2 : List (Nat × Nat)
helpMe2 = (1 , 22) ∷ []

test2 : FinMap Nat Nat
test2 = (fromListᵐ helpMe) ∪ᵐ (fromListᵐ helpMe2)
