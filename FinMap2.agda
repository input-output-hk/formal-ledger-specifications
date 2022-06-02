{-# OPTIONS --safe #-}

open import Data.List using (List; []; head; map)
open import Data.Maybe hiding (map)
open import Data.Product using (_×_; _,_; proj₁; proj₂; curry; uncurry)
open import Function hiding (Inverse)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import DecEq
open import FiniteSubset hiding (_∪_; _∩_)
open import FinSet hiding (∅; map; indexedSum; _∈_)

module FinMap2 where

open import FiniteMap

FinMap : (K V : Set) → {{DecEq K}} → {{DecEq V}} → Set
FinMap K V {{eq}} {{eq'}} = FiniteMap K V eq eq'

module _ {K V : Set} {{_ : DecEq K}} {{_ : DecEq V}} where

  ∅ : FinMap K V
  ∅ = fs-nojunk []

  _◃_ : FinSet K → FinMap K V → FinMap K V
  set ◃ map = filterᵐ (λ x → proj₁ x ∈? set) map

  chooseM : FinMap K V → Maybe (K × V)
  chooseM = head ∘ listOfᵐ

  lookupM : FinMap K V → K → Maybe V
  lookupM m k = Data.Maybe.map proj₂ $ chooseM $ return k ◃ m

  _⋪_ : FinSet K → FinMap K V → FinMap K V
  set ⋪ map = filterᵐ (λ x → ¬? (proj₁ x ∈? set)) map

  values : FinMap K V → List V
  values m = map proj₂ $ listOfᵐ m

  insert : K → V → FinMap K V → FinMap K V
  insert k v m = m ∪ᵐ returnᵐ (k , v)

  dom : FinMap K V → FinSet K
  dom (fs-nojunk els {nd}) = fs-nojunk (map proj₁ els) {nd}

  mapKeys : {K' : Set} → {{_ : DecEq.DecEq K'}} → (K → K') → FinMap K V → FinMap K' V
  mapKeys f m = for x ∈ m , returnᵐ (Data.Product.map₁ f x)

  fromList' : List (K × V) → FinMap K V
  fromList' xs = fromListᵐ xs
