{-# OPTIONS --safe #-}

open import Data.List
open import Data.Maybe hiding (map; _>>=_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; curry; uncurry)
open import Data.Product.Properties
open import Agda.Builtin.Sigma
open import Function hiding (Inverse)
open import Relation.Nullary
open import Utilities.ListProperties
open import Utilities.ListsAddition
open import Utilities.Logic hiding (⊥-elim)
open import Data.Bool hiding (_≟_)
open import Agda.Builtin.Unit
open import Data.Empty
open import Utilities.ListMonad renaming (return to return')
open import FiniteSubset hiding (_∪_; _∩_; fromList)
open import Data.List.Relation.Unary.AllPairs hiding (map) renaming (_∷_ to _::_ ; head to headPair)
open import Relation.Binary using (Decidable)

module FiniteMap where

data FiniteMap (X : Set)(Y : Set)(eq : DecEq X)(eq' : DecEq Y) : Set where
  fs-nojunk : (els : List (X × Y)) → {nd :  ∥ nodupDec eq (Data.List.map proj₁ els) ∥}
            → FiniteMap X Y eq eq'


remDupM  : {X Y : Set} → DecIn X → List (X × Y) → List (X × Y)
remDupM ∈? xs = foldr (λ e res → if isYes (∈? (proj₁ e) (map proj₁ res))
                                 then res else e ∷ res) [] xs

remDupCorrectM : {X Y : Set} → (∈?M : DecIn X) → (xs : List (X × Y)) → NoDup (map proj₁ (remDupM ∈?M xs))
remDupCorrectM ∈?M (x ∷ xs) x₁ x₂  with ∈?M (proj₁ x) (map proj₁ (remDupM ∈?M xs))
... | yes p with remDupCorrectM ∈?M xs x₁ x₂
... | o1 , o2 , o3 , o4 , o5 = o1 , o2 , o3 , o4 , o5
remDupCorrectM ∈?M (x ∷ xs) x₁ (here refl) | no ¬p = [] , (_ , (_≡_.refl , (λ ()) , ¬p))
remDupCorrectM ∈?M (x ∷ xs) x₁ (there x₂) | no ¬p with remDupCorrectM ∈?M xs x₁ x₂  | in2eq ∈?M x₁ (proj₁ x)
... | o1 , o2 , o3 , o4 , o5 | yes refl rewrite o3 = ⊥-elim (¬p (++⁺ʳ o1 (here _≡_.refl)))
remDupCorrectM {X} ∈? (x ∷ xs) x₁ (there x₂)
  | no ¬p₁
  | o1 , o2 , o3 , o4 , o5
  | no ¬p
  = ((proj₁ x) ∷ o1) , (o2 , cong (_∷_ (proj₁ x)) o3 , h (proj₁ x) x₁ ¬p o4 , o5)
  where
   h : (x x₁ : X) → ¬ x₁ ≡ x → ¬ x₁ ∈ o1  → ¬ x₁ ∈ (x ∷ o1)
   h x1 .x1 pr1 pr2 (here refl) = pr1 _≡_.refl
   h x1 x₃  pr1 pr2 (there pr) = pr2 pr

fromListM : {K V : Set}{eq : DecEq K}{eq' : DecEq V} → List (K × V) → FiniteMap K V eq eq'
fromListM {eq = eq} xs = fs-nojunk (remDupM (eq2in eq) xs)  {∥-∥-prop2 (remDupCorrectM  (eq2in eq) xs) _}

filter' : {K V : Set}{P : K → Set} → (∀ a → Dec (P a)) → List (K × V) → List (K × V)
filter' P? [] = []
filter' P? (x ∷ xs) with does (P? (proj₁ x))
... | false = filter' P? xs
... | true = x ∷ filter' P? xs

listOfM : {K V : Set}{eq : DecEq K}{eq' : DecEq V} → FiniteMap K V eq eq' → List (K × V)
listOfM (fs-nojunk els) = els

filterM : {K V : Set}{eq : DecEq K}{eq' : DecEq V}{P : K → Set} → (∀ a → Dec (P a)) → FiniteMap K V eq eq' → FiniteMap K V eq eq'
filterM P? s = fromListM (filter' P? $ listOfM s)

returnM : {K V : Set}{eq : DecEq K}{eq' : DecEq V} → K × V → FiniteMap K V eq eq'
returnM x = fs-nojunk ((x ∷ [])) {tt}

bindM : {K V K₁ V₁ : Set}{eq : DecEq K}{eq' : DecEq V}{eq₁ : DecEq K₁}{eq₁' : DecEq V₁}
          → FiniteMap K V eq eq'
          → (K × V → FiniteMap K₁ V₁ eq₁ eq₁')
          → FiniteMap K₁ V₁ eq₁ eq₁'
bindM f c = fromListM $ ((listOfM f) >>= λ x → listOfM $ c x)

mzeroM : {K V : Set}{eq : DecEq K}{eq' : DecEq V} → FiniteMap K V eq eq'
mzeroM = fs-nojunk []

syntax bindM A (λ x → t) = for x ∈ A , t

_∪M_ : {K V : Set}{eq : DecEq K}{eq' : DecEq V} → FiniteMap K V eq eq' → FiniteMap K V eq eq' → FiniteMap K V eq eq'
_∪M_ m n = fromListM (listOfM m ++ listOfM n)

_∈M_ : {K V : Set}{eq : DecEq K}{eq' : DecEq V} → (K × V) → FiniteMap K V eq eq' → Set
a ∈M m = a ∈ (listOfM m)

∈M? : {K V : Set}{eq : DecEq K}{eq' : DecEq V} → (a : (K × V)) → (m : FiniteMap K V eq eq') → Dec (a ∈M m)
∈M? {k} {v} {eq} {eq'} a s = eq2in (≡-dec eq eq') a (listOfM s)

infix 4 _≡ᵐ_
_≡ᵐ_ : {K V : Set}{eq : DecEq K}{eq' : DecEq V} → FiniteMap K V eq eq' → FiniteMap K V eq eq' → Set
s ≡ᵐ s' = ∀ a → a ∈M s ⇔ a ∈M s'

NoDupIndCons : {X : Set} → (xs : List X) → (x : X) → (x ∉ xs) → NoDupInd xs → NoDupInd (x ∷ xs)
NoDupIndCons xs x x₁ x₂ = ¬Any⇒All¬ xs x₁ :: x₂

NoDupProj=>NoDup : {K V : Set} → (∈? : DecIn (K × V)) → (xs : List (K × V)) → NoDup (map proj₁ xs) → NoDup xs
NoDupProj=>NoDup ∈? (x ∷ xs) p x₁ x₂ with ∈? x xs
... | yes p₁ with NoDupInd-corr2 (map proj₁ (x ∷ xs)) p
NoDupProj=>NoDup ∈? (x ∷ xs) p x₁ x₂ | yes p₁ | ans = ⊥-elim (All¬⇒¬Any (headPair ans) (∃-after-map x xs proj₁ p₁))
NoDupProj=>NoDup ∈? (x ∷ xs) p x₁ x₂ | no ¬p = NoDupInd-corr (x ∷ xs)
                                    (NoDupIndCons xs x ¬p
                                      (NoDupInd-corr2 xs (NoDupProj=>NoDup ∈? xs (NoDupInd-corr2' _ _ p))))
                                    x₁ x₂

FinMap=>FinSet : {K V : Set}{eq : DecEq K}{eq' : DecEq V} → (f : FiniteMap K V eq eq')
                                                          → FiniteSubSet (K × V) (≡-dec eq eq') false
FinMap=>FinSet {K} {V} {eq} {eq'} (fs-nojunk els {nd}) = fs-nojunk els {∥-∥-prop2
     (NoDupProj=>NoDup (eq2in (≡-dec eq eq')) els (∥-∥-prop3 _ nd)) _}
