{-# OPTIONS --safe #-}

open import Data.List using (List; []; head; map)
open import Data.Maybe hiding (map)
open import Data.Product using (_×_; _,_; proj₁; proj₂; curry; uncurry)
open import Data.Product.Function.NonDependent.Propositional
open import Data.Bool using (false; not)
open import Level
open import Algebra
open import Function hiding (Inverse)
open import Function.Equivalence as Eq using (_⇔_; ⇔-setoid; equivalence)
open import Data.Sum using (_⊎_; fromDec; toDec)
open import Data.Sum.Algebra using (⊎-comm)
open import Data.Sum.Function.Propositional
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Product.Algebra
import Function.Inverse as Inv
--open import FinSet.Properties
open import Data.Empty.Polymorphic
open import Function.Related using (fromRelated; toRelated)
import Relation.Binary.Reasoning.Preorder as P-Reasoning
open import DecEq
open import FiniteSubset hiding (_∪_; _∩_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
open import Function.Bundles.Related
open import FinSet hiding (∅; map; indexedSum; _∈_)
open import Function.Properties.Inverse

open CommutativeMonoid {{...}}

module FinMapProofs {X : Set}{Y : Set}{{eq : DecEq X}}{{eq' : DecEq Y}} where

open import FiniteMap
open import FinMap2
open import FiniteMapProperties {X} {Y} {{eq}} {{eq'}}

open import Relation.Binary.PropositionalEquality

private
  variable
    a b : X × Y
    l : List (X × Y)
    s s' : FinSet X {{eq}}
    m m' m''  : FinMap X Y {{eq}} {{eq'}}


dom-res-ex-∪ : (s ⋪ m) ∪ᵐ (s ◃ m) ≡ᵐ m
dom-res-ex-∪ {s} {m} = ∈-⊎↔∪≡ {s = s ⋪ m} {s' = s ◃ m} {s'' = m} λ a →
              --(a ∈ᵐ s ⋪ m ⊎ a ∈ᵐ s ◃ m)
              --Need to desugar before using u-cong
              (a ∈ᵐ (s ⋪ m) × (a ∉ᵖᵐ (s ◃ m)) ⊎ a ∈ᵐ (s ◃ m))
              ∼⟨ SK-sym (fromRelated (toRelated {!!} ⊎-cong Eq.id)) ⟩
              (a ∈ᵐ (s ⋪ m) ⊎ a ∈ᵐ (s ◃ m))
              ∼⟨ {!!} ⟩
              (a ∈ᵐ m)
              ∎
              where open EquationalReasoning

{-
 ((Relation.Binary.PropositionalEquality.setoid
        (Data.Product.Σ X (λ x → Y))
        Data.List.Membership.Setoid.∈ a)
       (listOfᵐ (s ⋪ m))
       × (a ∉ᵖᵐ (s ◃ m))
       ⊎
       (Relation.Binary.PropositionalEquality.setoid
        (Data.Product.Σ X (λ x → Y))
        Data.List.Membership.Setoid.∈ a)
       (listOfᵐ (s ◃ m)))
      Function.⇔ Data.List.Relation.Unary.Any.Any (_≡_ a) (listOfᵐ m)
-}

{-
dom-res-ex-∪ : (s ⋪ m) ∪ᵐ (s ◃ m) ≡ᵐ m
dom-res-ex-∪ {s} {m} = ∈-⊎↔∪≡ {s = s ⋪ m} {s' = s ◃ m} {s'' = m} λ a →
    (a ∈ᵐ s ⋪ m ⊎ a ∈ᵐ s ◃ m)
      ∼⟨ SK-sym (fromRelated ((toRelated (∈filter {s = m} (λ x → ¬? (proj₁ x ∈? s)) a)) ⊎-cong (toRelated (∈filter {s = m} (λ x → proj₁ x ∈? s) a)))) ⟩
    (a ∈ᵐ m × ¬ proj₁ a ∈ s ⊎ a ∈ᵐ m × proj₁ a ∈ s)
      ⤖⟨ SK-sym (↔⇒⤖ (×-distribˡ-⊎ 0ℓ (a ∈ᵐ m) (¬ proj₁ a ∈ s) (proj₁ a ∈ s))) ⟩
    (a ∈ᵐ m × (¬ proj₁ a ∈ s ⊎ proj₁ a ∈ s))
      ⤖⟨ fromRelated (_×-cong_ Inv.id (toRelated (↔⇒⤖ (⊎-comm (¬ proj₁ a ∈ s) (proj₁ a ∈ s))))) ⟩
    (a ∈ᵐ m × (proj₁ a ∈ s ⊎ ¬ proj₁ a ∈ s))
      ∼⟨ fromRelated (_×-cong_ Eq.id (Eq.equivalence toDec fromDec)) ⟩
    (a ∈ᵐ m × Dec (proj₁ a ∈ s))
      ∼⟨ mk⇔ proj₁ (λ h → (h , proj₁ a ∈? s)) ⟩
    (a ∈ᵐ m) ∎
    where open EquationalReasoning
-}

{-
{-
  dom-res-ex-∪ : ∀ s m → (s ⋪ m) ∪ (s ◃ m) ≡ᵉ m
  dom-res-ex-∪ s m = ∈-⊎↔∪≡ {s = s ⋪ m} {s' = s ◃ m} {s'' = m} λ a →
    (a ∈ s ⋪ m ⊎ a ∈ s ◃ m)
      ∼⟨ SK-sym (fromRelated ((toRelated (∈filter {s = m} (λ x → ¬? (proj₁ x ∈? s)) a)) ⊎-cong (toRelated (∈filter {s = m} (λ x → proj₁ x ∈? s) a)))) ⟩
    (a ∈ m × ¬ proj₁ a ∈ s ⊎ a ∈ m × proj₁ a ∈ s)
      ⤖⟨ SK-sym (↔⇒⤖ (×-distribˡ-⊎ 0ℓ (a ∈ m) (¬ proj₁ a ∈ s) (proj₁ a ∈ s))) ⟩
    (a ∈ m × (¬ proj₁ a ∈ s ⊎ proj₁ a ∈ s))
      ⤖⟨ fromRelated (_×-cong_ Inv.id (toRelated (↔⇒⤖ (⊎-comm (¬ proj₁ a ∈ s) (proj₁ a ∈ s))))) ⟩
    (a ∈ m × (proj₁ a ∈ s ⊎ ¬ proj₁ a ∈ s))
      ∼⟨ fromRelated (_×-cong_ Eq.id (Eq.equivalence toDec fromDec)) ⟩
    (a ∈ m × Dec (proj₁ a ∈ s))
      ∼⟨ mk⇔ proj₁ (λ h → (h , proj₁ a ∈? s)) ⟩
    (a ∈ m) ∎
    where open EquationalReasoning
-}


{-∈-⊎↔∪≡ {s = s ⋪ m} {s' = s ◃ m} {s'' = m} λ a →
    (a ∈ s ⋪ m ⊎ a ∈ s ◃
      ∼⟨ SK-sym (fromRelated ((toRelated (∈filter {s = m} (λ x → ¬? (proj₁ x ∈? s)) a)) ⊎-cong (toRelated (∈filter {s = m} (λ x → proj₁ x ∈? s) a)))) ⟩
    (a ∈ m × ¬ proj₁ a ∈ s ⊎ a ∈ m × proj₁ a ∈ s)
      ⤖⟨ SK-sym (↔⇒⤖ (×-distribˡ-⊎ 0ℓ (a ∈ m) (¬ proj₁ a ∈ s) (proj₁ a ∈ s))) ⟩
    (a ∈ m × (¬ proj₁ a ∈ s ⊎ proj₁ a ∈ s))
      ⤖⟨ fromRelated (_×-cong_ Inv.id (toRelated (↔⇒⤖ (⊎-comm (¬ proj₁ a ∈ s) (proj₁ a ∈ s))))) ⟩
    (a ∈ m × (proj₁ a ∈ s ⊎ ¬ proj₁ a ∈ s))
      ∼⟨ fromRelated (_×-cong_ Eq.id (Eq.equivalence toDec fromDec)) ⟩
    (a ∈ m × Dec (proj₁ a ∈ s))
      ∼⟨ mk⇔ proj₁ (λ h → (h , proj₁ a ∈? s)) ⟩
    (a ∈ m) ∎
    where open EquationalReasoning -}



  {-
  remDupᵐ⁺ : {X Y : Set} → (∈? : DecIn X) → (x : X × Y)
    → (xs xs' : List (X × Y))
    → x .proj₁ ∉ map proj₁ xs'
    → x ∈ remDupᵐ ∈? (xs ++ x ∷ xs')
-}



{-
  dup∈ : {X Y : Set} → (∈? : DecIn X) → (x : (X × Y)) → (xs ys : List (X × Y))
                   → x ∈ xs
                   → NoDupInd (map proj₁ xs)
                   → x ∈ (remDupᵐ ∈? (ys ++ xs))
-}



  --remDupM (xs ++ xs)
  --remDupM (xs' ++ x :: xs')
  --at this point we want a lemma that cnaj
    --overrideProof a (fs-nojunk {!!}) (fs-nojunk {!!}) {!!}



{-
with overrideProof a (fs-nojunk xs
                                       {∥-∥-prop2 (NoDupInd-corr2' (map proj₁ xs) (proj₁ x) (∥-∥-prop3 _ prf)) _})
                                       s' h
  ... | ans = {!!}
-}

  {-
∈⊎⇒∈∪' : a ∈M s → a ∈M s' ∪M s
∈⊎⇒∈∪' {a} {fs-nojunk .(_ ∷ _)} {s'} (here px) = {!!}
∈⊎⇒∈∪' {a} {fs-nojunk (x ∷ xs)} {s'} (there h) with ∈⊎⇒∈∪' h
... | ans = ans
-}

  open import Data.Product.Properties

  test : FinMap K V → FinSet (K × V)
  test m = FinMap=>FinSet m



{-
  _◃_ : FinSet K → FinMap K V → FinMap K V
  set ◃ map = filterM (λ x → x ∈? set) map

  _⋪_ : FinSet K → FinMap K V → FinMap K V
  set ⋪ map = filterM (λ x → ¬? (x ∈? set)) map
-}



{-
  dom-res-ex-∪ : ∀ s m → (s ⋪ m) ∪M (s ◃ m) ≡ᵐ m
  dom-res-ex-∪ s m = ∈-⊎↔∪≡ {s = s ⋪ m} {s' = s ◃ m} {s'' = m} λ a →
    (a ∈ s ⋪ m ⊎ a ∈ s ◃
      ∼⟨ SK-sym (fromRelated ((toRelated (∈filter {s = m} (λ x → ¬? (proj₁ x ∈? s)) a)) ⊎-cong (toRelated (∈filter {s = m} (λ x → proj₁ x ∈? s) a)))) ⟩
    (a ∈ m × ¬ proj₁ a ∈ s ⊎ a ∈ m × proj₁ a ∈ s)
      ⤖⟨ SK-sym (↔⇒⤖ (×-distribˡ-⊎ 0ℓ (a ∈ m) (¬ proj₁ a ∈ s) (proj₁ a ∈ s))) ⟩
    (a ∈ m × (¬ proj₁ a ∈ s ⊎ proj₁ a ∈ s))
      ⤖⟨ fromRelated (_×-cong_ Inv.id (toRelated (↔⇒⤖ (⊎-comm (¬ proj₁ a ∈ s) (proj₁ a ∈ s))))) ⟩
    (a ∈ m × (proj₁ a ∈ s ⊎ ¬ proj₁ a ∈ s))
      ∼⟨ fromRelated (_×-cong_ Eq.id (Eq.equivalence toDec fromDec)) ⟩
    (a ∈ m × Dec (proj₁ a ∈ s))
      ∼⟨ mk⇔ proj₁ (λ h → (h , proj₁ a ∈? s)) ⟩
    (a ∈ m) ∎
    where open EquationalReasoning -}

{-
  dom-res-ex-∪ : ∀ s m → (s ⋪ m) ∪ (s ◃ m) ≡ᵉ m
  dom-res-ex-∪ s m = ∈-⊎↔∪≡ {s = s ⋪ m} {s' = s ◃ m} {s'' = m} λ a →
    (a ∈ s ⋪ m ⊎ a ∈ s ◃ m)
      ∼⟨ SK-sym (fromRelated ((toRelated (∈filter {s = m} (λ x → ¬? (proj₁ x ∈? s)) a)) ⊎-cong (toRelated (∈filter {s = m} (λ x → proj₁ x ∈? s) a)))) ⟩
    (a ∈ m × ¬ proj₁ a ∈ s ⊎ a ∈ m × proj₁ a ∈ s)
      ⤖⟨ SK-sym (↔⇒⤖ (×-distribˡ-⊎ 0ℓ (a ∈ m) (¬ proj₁ a ∈ s) (proj₁ a ∈ s))) ⟩
    (a ∈ m × (¬ proj₁ a ∈ s ⊎ proj₁ a ∈ s))
      ⤖⟨ fromRelated (_×-cong_ Inv.id (toRelated (↔⇒⤖ (⊎-comm (¬ proj₁ a ∈ s) (proj₁ a ∈ s))))) ⟩
    (a ∈ m × (proj₁ a ∈ s ⊎ ¬ proj₁ a ∈ s))
      ∼⟨ fromRelated (_×-cong_ Eq.id (Eq.equivalence toDec fromDec)) ⟩
    (a ∈ m × Dec (proj₁ a ∈ s))
      ∼⟨ mk⇔ proj₁ (λ h → (h , proj₁ a ∈? s)) ⟩
    (a ∈ m) ∎
    where open EquationalReasoning
-}



{-
  mapKeys : {KM : Set} → {{_ : DecEq KM}} → (K → KM) → FinMap K V → FinMap KM V
  mapKeys f m = for x ∈ m as false , return {b = false} (Data.Product.map₁ f x)

  dom-res-ex-∪ : ∀ s m → (s ⋪ m) ∪ (s ◃ m) ≡ᵉ m
  dom-res-ex-∪ s m = ∈-⊎↔∪≡ {s = s ⋪ m} {sM = s ◃ m} {sMM = m} λ a →
    (a ∈ s ⋪ m ⊎ a ∈ s ◃ m)
      ∼⟨ SK-sym (fromRelated ((toRelated (∈filter {s = m} (λ x → ¬? (proj₁ x ∈? s)) a)) ⊎-cong (toRelated (∈filter {s = m} (λ x → proj₁ x ∈? s) a)))) ⟩
    (a ∈ m × ¬ proj₁ a ∈ s ⊎ a ∈ m × proj₁ a ∈ s)
      ⤖⟨ SK-sym (↔⇒⤖ (×-distribˡ-⊎ 0ℓ (a ∈ m) (¬ proj₁ a ∈ s) (proj₁ a ∈ s))) ⟩
    (a ∈ m × (¬ proj₁ a ∈ s ⊎ proj₁ a ∈ s))
      ⤖⟨ fromRelated (_×-cong_ Inv.id (toRelated (↔⇒⤖ (⊎-comm (¬ proj₁ a ∈ s) (proj₁ a ∈ s))))) ⟩
    (a ∈ m × (proj₁ a ∈ s ⊎ ¬ proj₁ a ∈ s))
      ∼⟨ fromRelated (_×-cong_ Eq.id (Eq.equivalence toDec fromDec)) ⟩
    (a ∈ m × Dec (proj₁ a ∈ s))
      ∼⟨ mk⇔ proj₁ (λ h → (h , proj₁ a ∈? s)) ⟩
    (a ∈ m) ∎
    where open EquationalReasoning


  dom-res-ex-∩ : ∀ s m → (s ⋪ m) ∩ (s ◃ m) ≡ᵉ ∅
  dom-res-ex-∩ s m = ∈-×↔∩≡ {s = s ⋪ m} {sM = s ◃ m} {sMM = ∅} λ a →
    (a ∈ s ⋪ m × a ∈ s ◃ m)
      ∼⟨ SK-sym (fromRelated (_×-cong_ (toRelated $ ∈filter {s = m} (λ x → ¬? (proj₁ x ∈? s)) a) (toRelated $ ∈filter {s = m} (λ x → proj₁ x ∈? s) a))) ⟩
    ((a ∈ m × (¬ proj₁ a ∈ s)) × (a ∈ m × proj₁ a ∈ s))
      ∼⟨ mk⇔ (λ { ((a₁ , a₂) , (a₃ , a₄)) → (a₁ , a₂ , a₄)}) (λ { (a₁ , a₂ , a₃) → ((a₁ , a₂) , a₁ , a₃)}) ⟩
    (a ∈ m × ¬ proj₁ a ∈ s × proj₁ a ∈ s)
      ∼⟨ fromRelated (_×-cong_ Eq.id (Eq.equivalence (uncurry (λ x y → case x y of λ ())) ⊥-elim)) ⟩
    (a ∈ m × ⊥)
      ↔⟨ ×-zeroʳ 0ℓ (a ∈ m) ⟩
    ⊥
      ∼⟨ mk⇔ ⊥-elim (λ ()) ⟩
    (a ∈ ∅) ∎
    where open EquationalReasoning

  ⋪⇒⊆ : ∀ m → (s ⋪ m) ⊆ m
  ⋪⇒⊆ {s} m a∈s⋪m = proj₁ $ filter→∈ {s = m} (λ x → ¬? (proj₁ x ∈? s)) _ a∈s⋪m

  dom-res-∩-empty : ∀ s m → (mM : FinMap K V) → m ∩ mM ≡ᵉ ∅ → (s ⋪ m) ∩ mM ≡ᵉ ∅
  dom-res-∩-empty s m mM h with ∩-OrderHomomorphismˡ {K × V} {s = mM}
  ... | record { cong = _ ; mono = mono } = ∅-least {s = (s ⋪ m) ∩ mM} (begin
    ((s ⋪ m) ∩ mM) ∼⟨ mono {s ⋪ m} {m} (⋪⇒⊆ {s} m) ⟩
    (m ∩ mM) ≈⟨ h ⟩
    FinSet.∅ ∎)
    where open P-Reasoning (⊆-PreorderM {K × V})
-}

-}
