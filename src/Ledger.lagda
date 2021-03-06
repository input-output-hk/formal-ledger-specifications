\documentclass{article}
\usepackage{unicode-math}
\setsansfont{XITSMath-Regular.otf}

\usepackage{newunicodechar}
\newunicodechar{ᵇ}{\ensuremath{^b}}
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
\newunicodechar{σ}{\ensuremath{\sigma}}

\usepackage{float}
\floatstyle{boxed}
\restylefloat{figure}

\usepackage{iohk}

\usepackage[hidelinks]{hyperref}
\usepackage[links]{agda}

\newcommand{\N}{\ensuremath{\mathbb{N}}}
\newcommand{\TxBody}{\type{TxBody}}
\newcommand{\TxWitness}{\type{TxWitness}}
\newcommand{\Tx}{\type{Tx}}
\newcommand{\Ix}{\type{Ix}}
\newcommand{\TxId}{\type{TxId}}
\newcommand{\Addr}{\type{Addr}}
\newcommand{\UTxO}{\type{UTxO}}
\newcommand{\Coin}{\type{Coin}}
\newcommand{\TxIn}{\type{TxIn}}
\newcommand{\TxOut}{\type{TxOut}}
\newcommand{\UTxOEnv}{\type{UTxOEnv}}
\newcommand{\UTxOState}{\ensuremath{\type{UTxOState}}}

%%
%% Functions
%%
\newcommand{\txins}[1]{\fun{txins}~ \var{#1}}
\newcommand{\txouts}[1]{\fun{txouts}~ \var{#1}}
\newcommand{\txid}[1]{\fun{txid}~ \var{#1}}
\newcommand{\outs}[1]{\fun{outs}~ \var{#1}}
\newcommand{\balance}[1]{\fun{balance}~ \var{#1}}
\newcommand{\txfee}[1]{\fun{txfee}~ \var{#1}}

\newcommand{\wcard}[0]{\rule[-.5mm]{2mm}{.2mm}}
\newcommand{\leteq}{\ensuremath{\mathrel{\mathop:}=}}

\newtheorem{property}{Property}[section]


\begin{document}

\begin{code}[hide]

{-# OPTIONS --safe #-}
{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS -v allTactics:100 #-}

open import Prelude

open import Algebra using (CommutativeMonoid)

import Function.Related.Propositional as FP

open import Data.List.Membership.Propositional renaming (_∈_ to _∈'_)
open import Data.List.Relation.Unary.All using (All; all?)
open import Data.Maybe.Properties using (just-injective)
open import Data.Maybe.Relation.Unary.Any using (dec)
open import Data.Nat using (_≤?_; _≤_)
open import Data.Nat.Properties using (+-0-commutativeMonoid; +-0-monoid; +-comm)
open import Data.Product.Properties

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import DecEq
open import Interface.Decidable.Instance
open import FinMap renaming (FinMap to _↦_)
open import FinSet hiding (∅) renaming (FinSet to ℙ_)
open import FinSet.Properties
open import FinSet.Properties.Equality

open import Tactic.Helpers
open import Tactic.MonoidSolver
open import Tactic.EquationalReasoning
open import Tactic.DeriveComp

open import MyDebugOptions
--open import Tactic.Defaults

open import PreludeImports

open import ComputationalRelation

module Ledger (
\end{code}

\section{Transactions}
\label{sec:transactions}

Transactions are defined in Figure~\ref{fig:defs:utxo-shelley}.
A transaction is made up of three pieces:

\begin{itemize}
  \item A set of transaction inputs.
    This derived type identifies an output from a previous transaction.
    It consists of a transaction id and an index to uniquely identify the output.
  \item An indexed collection of transaction outputs.
    The $\TxOut$ type is an address paired with a coin value.
  \item A transaction fee. This value will be added to the fee pot.
\end{itemize}

Finally, $\fun{txid}$ computes the transaction id of a given transaction.
This function must produce a unique id for each unique transaction body.
\textbf{We assume that} $\fun{txid}$ \textbf{is injective.}

\AgdaTarget{Ix, TxId, Addr, Coin, TxIn, TxOut, UTxO, Tx, txins, txouts, txfee, txid}
\begin{figure*}[h]
\emph{Abstract types}
\begin{code}
  Ix           -- index
  TxId         -- transaction id
  Addr         -- address
  VKey         -- verifying key
  Sig          -- signature
\end{code}
\emph{Derived types}
\begin{code}[hide]
  : Set) {{_ : DecEq TxId}} {{_ : DecEq Ix}} {{_ : DecEq Addr}} ⦃ _ : DecEq VKey ⦄ ⦃ _ : DecEq Sig ⦄ where
_≤ᵇ_ : ℕ → ℕ → Bool
n ≤ᵇ m = ⌊ n ≤? m ⌋

_≠_ : {A : Set} → A → A → Set
a ≠ b = ¬ a ≡ b

_⟨$⟩_ : {A B : Set} → A ↣ B → A → B
_⟨$⟩_ = FP.⇒→ {k = FP.injection}

instance
  _ = +-0-commutativeMonoid
  _ = Decidable²⇒Dec _≤?_

  -- Sub? : ∀ {a} {A : Set a} ⦃ _ : DecEq A ⦄ → {x y : List A} → Dec (∀ {z} → z ∈' x → z ∈' y)
  -- Sub? {x = x} {y} = {!!}

Coin Slot TxIn TxOut UTxO : Set
\end{code}
\begin{code}
Coin    = ℕ
Slot    = ℕ -- TODO: make this abstract?
TxIn    = TxId × Ix
TxOut   = Addr × Coin
UTxO    = TxIn ↦ TxOut

record PParams : Set where
  field
    a : ℕ
    b : ℕ
    maxTxSize : ℕ
\end{code}
\emph{Transaction types}
\begin{code}
record TxBody : Set where
  field
    txins  : ℙ TxIn
    txouts : Ix ↦ TxOut
    txfee  : Coin
    txvldt : Maybe ℕ × Maybe ℕ
    txsize : ℕ

record TxWitnesses : Set where
  field
    vkSigs : VKey ↦ Sig

record Tx : Set where
  field
    body : TxBody
    wits : TxWitnesses
\end{code}
\emph{Abstract functions}
\begin{code}[hide]
open TxBody
open TxWitnesses
open Tx
module _
\end{code}
  -- TODO: how to fix parentheses here?
\begin{code}
  (txid : TxBody ↣ TxId) -- an injective function
  (paymentK : Addr → VKey) -- TODO: should be the hash
  (isSigned : VKey → TxBody → Sig → Set)
\end{code}
\begin{code}[hide]
  where
\end{code}
\caption{Definitions used in the UTxO transition system}
\label{fig:defs:utxo-shelley}
\end{figure*}

\section{UTxO}
\label{sec:utxo}

Figure~\ref{fig:functions:utxo} defines functions needed for the UTxO transition system.
Figure~\ref{fig:ts-types:utxo-shelley} defines the types needed for the UTxO transition system.
The UTxO transition system is given in Figure~\ref{fig:rules:utxo-shelley}.

\begin{itemize}

  \item
    The function $\fun{outs}$ creates the unspent outputs generated by a transaction.
    It maps the transaction id and output index to the output.

  \item
    The $\fun{balance}$ function calculates sum total of all the coin in a given UTxO.
\end{itemize}

\AgdaTarget{outs, minfee, inInterval, balance}
\begin{figure*}[h]
\begin{code}
  outs : TxBody → UTxO
  outs tx = mapKeys (txid ⟨$⟩ tx ,_) $ txouts tx

  minfee : PParams → TxBody → Coin
  minfee pp tx = a * txsize tx + b
    where open PParams pp

  -- this has to be a type definition for inference to work
  data inInterval (slot : Slot) : (Maybe Slot × Maybe Slot) → Set where
    both  : ∀ {l r} → l ≤ slot × slot ≤ r  →  inInterval slot (just l  , just r)
    lower : ∀ {l}   → l ≤ slot             →  inInterval slot (just l  , nothing)
    upper : ∀ {r}   → slot ≤ r             →  inInterval slot (nothing , just r)
    none  :                                   inInterval slot (nothing , nothing)

  balance : UTxO → Coin
  balance utxo = Σ[ v ← utxo ] proj₂ (proj₂ v)
\end{code}
\caption{Functions used in UTxO rules}
\label{fig:functions:utxo}
\end{figure*}

\AgdaTarget{UTxOEnv, UTxOState, \_⊢\_⇀⦇\_,UTXO⦈\_}
\begin{figure*}[h]
\emph{UTxO environment}
\begin{code}[hide]
  UTxOEnv UTxOState : Set
\end{code}
\begin{code}
  UTxOEnv = Slot
          × PParams
\end{code}
\emph{UTxO states}
\begin{code}
  UTxOState = UTxO -- UTxO
            × Coin -- fee pot
\end{code}
\emph{UTxO transitions}

\begin{code}[hide]
  variable
    tx : TxBody
    utxo utxo' utxo1 utxo2 : UTxO
    fee fee' fees fees' : Coin
    utxoState utxoState' utxoState1 utxoState2 : UTxOState
    Γ : UTxOEnv
    s s' : UTxOState

  ⟦_⟧ : {A : Set} → A → A
  ⟦_⟧ = id

  instance
    _ = ≟-∅

    Dec-inInterval : {slot : Slot} {I : Maybe Slot × Maybe Slot} → Dec (inInterval slot I)
    Dec-inInterval {slot} {just x  , just y } with x ≤? slot | slot ≤? y
    ... | no ¬p₁ | _      = no λ where (both (h₁ , h₂)) → ¬p₁ h₁
    ... | yes p₁ | no ¬p₂ = no λ where (both (h₁ , h₂)) → ¬p₂ h₂
    ... | yes p₁ | yes p₂ = yes (both (p₁ , p₂))
    Dec-inInterval {slot} {just x  , nothing} with x ≤? slot
    ... | no ¬p = no  (λ where (lower h) → ¬p h)
    ... | yes p = yes (lower p)
    Dec-inInterval {slot} {nothing , just x } with slot ≤? x
    ... | no ¬p = no  (λ where (upper h) → ¬p h)
    ... | yes p = yes (upper p)
    Dec-inInterval {slot} {nothing , nothing} = yes none
  data
\end{code}
\begin{code}
    _⊢_⇀⦇_,UTXO⦈_ : UTxOEnv → UTxOState → TxBody → UTxOState → Set
\end{code}
\caption{UTxO transition-system types}
\label{fig:ts-types:utxo-shelley}
\end{figure*}

\begin{figure*}[h]
\begin{code}[hide]
  data _⊢_⇀⦇_,UTXO⦈_ where
\end{code}
\begin{code}
    UTXO-inductive :
      ∀ {Γ} {s} {tx}
      → let slot = proj₁ Γ
            pp   = proj₂ Γ
            utxo = proj₁ s
            fees = proj₂ s
        in
        txins tx ≠ ∅
      → inInterval slot (txvldt tx)
      -- → txins tx ⊆ dom utxo
      -- this is currently broken because of https://github.com/agda/agda/issues/5982
      → let f = txfee tx in minfee pp tx ≤ f
      → balance (txins tx ◃ utxo) ≡ balance (outs tx) + f
      → txsize tx ≤ PParams.maxTxSize pp
      ────────────────────────────────
      Γ
        ⊢ s
        ⇀⦇ tx ,UTXO⦈
        ((txins tx ⋪ utxo) ∪ outs tx , fees + f)
\end{code}
\caption{UTXO inference rules}
\label{fig:rules:utxo-shelley}
\end{figure*}

\begin{code}[hide]
  unquoteDecl Computational-UTXO = deriveComputational (quote _⊢_⇀⦇_,UTXO⦈_) Computational-UTXO

  balance-∪ : utxo ∩ utxo' ≡ᵉ ∅ → balance (utxo ∪ utxo') ≡ balance utxo + balance utxo'
  balance-∪ {utxo} {utxo'} = indexedSum-∪ {s = utxo} {s' = utxo'}

  balance-cong : utxo ≡ᵉ utxo' → balance utxo ≡ balance utxo'
  balance-cong {utxo} {utxo'} = indexedSum-cong {s = utxo} {s' = utxo'}

  open Tactic.EquationalReasoning.≡-Reasoning {A = ℕ} (solve-macro (quoteTerm +-0-monoid))
\end{code}

\begin{property}[\textbf{Preserve Balance}]
For all $\var{env}\in\UTxOEnv$, $\var{utxo},\var{utxo'}\in\UTxO$, $\var{fee},\var{fee'}\in\Coin$ and $\var{tx}\in\TxBody$, if
\begin{code}[hide]
  pov :
\end{code}
\begin{code}[inline*]
    utxo ∩ outs tx ≡ ∅
\end{code}
and
\begin{code}[hide]
    →
\end{code}
\begin{code}[inline*]
        Γ ⊢ (utxo , fee) ⇀⦇ tx ,UTXO⦈ (utxo' , fee')
\end{code}
then
\begin{code}[hide]
    →
\end{code}
\begin{code}
        balance utxo + fee ≡ balance utxo' + fee'
\end{code}
\begin{code}[hide]
  pov {utxo} {tx} {_} {fee} h' (UTXO-inductive _ _ _ bal-eq _) =
    let
      h : utxo ∩ outs tx ≡ᵉ ∅
      h = subst ((utxo ∩ outs tx) ≡ᵉ_) h' (IsEquivalence.refl ≡ᵉ-isEquivalence {utxo ∩ outs tx})

      balance-eq : balance utxo ≡ balance ((txins tx ⋪ utxo) ∪ outs tx) + txfee tx
      balance-eq = begin
        balance utxo
          ≡˘⟨ balance-cong {utxo = (txins tx ⋪ utxo) ∪ (txins tx ◃ utxo)} {utxo' = utxo} (dom-res-ex-∪ (txins tx) utxo) ⟩
        balance ((txins tx ⋪ utxo) ∪ (txins tx ◃ utxo))
          ≡⟨ balance-∪ {txins tx ⋪ utxo} {txins tx ◃ utxo} (dom-res-ex-∩ (txins tx) utxo) ⟩
        balance (txins tx ⋪ utxo) + balance (txins tx ◃ utxo)
          ≡tʳ⟨ cong (balance (txins tx ⋪ utxo) +_) bal-eq ⟩
        balance (txins tx ⋪ utxo) + balance (outs tx) + txfee tx
          ≡˘⟨ cong (_+ txfee tx) (balance-∪ {txins tx ⋪ utxo} {outs tx} (dom-res-∩-empty (txins tx) utxo (outs tx) h)) ⟩
        balance ((txins tx ⋪ utxo) ∪ outs tx) + txfee tx ∎
    in begin
    balance utxo + fee                                        ≡tʳ⟨ cong (_+ fee) balance-eq ⟩
    balance ((txins tx ⋪ utxo) ∪ outs tx) + (txfee tx + fee)
              ≡˘⟨ cong (balance ((txins tx ⋪ utxo) ∪ outs tx) +_) (+-comm fee (txfee tx)) ⟩
    balance ((txins tx ⋪ utxo) ∪ outs tx) + (fee + txfee tx) ∎
\end{code}
\end{property}

\pagebreak
Note that this is not a function, but a relation. To make this
definition executable, we need to define a function that computes
the transition. We also prove that this indeed computes the
relation. Luckily, this can be automated.

\begin{figure*}[h]
\begin{code}
  UTXO-step : UTxOEnv → UTxOState → TxBody → Maybe UTxOState
  UTXO-step = Computational.compute Computational-UTXO

  UTXO-step-computes-UTXO :
    UTXO-step Γ utxoState tx ≡ just utxoState'
    ⇔ Γ ⊢ utxoState ⇀⦇ tx ,UTXO⦈ utxoState'
  UTXO-step-computes-UTXO =
    Computational.≡-just⇔STS Computational-UTXO
\end{code}
\caption{Computing the UTXO transition system}
\end{figure*}

\begin{figure*}[h]
\begin{code}
  witsVKeyNeeded : UTxO → TxBody → ℙ VKey
  witsVKeyNeeded utxo txb = FinSet.map (paymentK ∘ proj₁) (utxo ⟪$⟫ txins txb)
\end{code}
\caption{Functions used for witnessing}
\label{fig:functions:utxow}
\end{figure*}

\begin{figure*}[h]
\begin{code}[hide]
  instance
    Computational⇒DecInst : ∀ {C S Sig c s sig s'} ⦃ _ : DecEq S ⦄
      {STS : C → S → Sig → S → Set} ⦃ comp : Computational STS ⦄ → Dec (STS c s sig s')
    Computational⇒DecInst ⦃ comp = comp ⦄ = Computational⇒Dec comp

    import Relation.Unary as U
    FSall? : {A : Set} {P : A → Set} {P? : U.Decidable P} ⦃ _ : DecEq A ⦄ {s : FinSet.FinSet A}
           → Dec (FinSet.All P s)
    FSall? {P? = P?} {s} = FinSet.all? P? s

  data
\end{code}
\begin{code}
    _⊢_⇀⦇_,UTXOW⦈_ : UTxOEnv → UTxOState → Tx → UTxOState → Set
\end{code}
\caption{UTxOW transition-system types}
\label{fig:ts-types:utxow}
\end{figure*}

\begin{figure*}[h]
\begin{code}[hide]
  data _⊢_⇀⦇_,UTXOW⦈_ where
\end{code}
\begin{code}
    UTXOW-inductive :
      ∀ {Γ} {s} {tx} {s'}
      → let utxo = proj₁ s
            txb = body tx
            txw = wits tx
            witsKeys = dom (vkSigs txw)
        in
        FinSet.All (λ { (vk , σ) → isSigned vk txb σ }) (vkSigs txw)
      → witsVKeyNeeded utxo txb ⊆ witsKeys
      → Γ ⊢ s ⇀⦇ txb ,UTXO⦈ s'
      ────────────────────────────────
      Γ ⊢ s ⇀⦇ tx ,UTXOW⦈ s'
\end{code}
\caption{UTXOW inference rules}
\label{fig:rules:utxow}
\end{figure*}

\begin{code}[hide]
  --unquoteDecl Computational-UTXOW = deriveComputational (quote _⊢_⇀⦇_,UTXOW⦈_) Computational-UTXOW
\end{code}

\end{document}
