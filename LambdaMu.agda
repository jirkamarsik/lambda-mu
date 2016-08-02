module LambdaMu (Atomic : Set) (ι ο ⊥ : Atomic) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_; lookup)

import NumberFin

infixr 7 _⇒_
infixl 8 _∨_
infixl 9 _∧_
data Type : Set where
  base : Atomic → Type
  _⇒_ : (a b : Type) → Type
  _∧_ : (a b : Type) → Type
  _∨_ : (a b : Type) → Type

¬_ : Type → Type
¬ a = a ⇒ base ⊥

Context : ℕ → Set
Context n = Vec Type n

mutual
  data Term {n m} (Γ : Context n) (Δ : Context m) : Type → Set where
    var : (x : Fin n) → Term Γ Δ (lookup x Γ)
    μ : {A : Type} → (c : Command Γ (A ∷ Δ)) → Term Γ Δ A
    lam : {A B : Type} → (t : Term (A ∷ Γ) Δ B) → Term Γ Δ (A ⇒ B)
    _,_ : {A₁ A₂ : Type} → (t₁ : Term Γ Δ A₁) → (t₂ : Term Γ Δ A₂) → Term Γ Δ (A₁ ∧ A₂)
    inj₁ : {A₁ A₂ : Type} → (e : Term Γ Δ A₁) → Term Γ Δ (A₁ ∨ A₂)
    inj₂ : {A₁ A₂ : Type} → (e : Term Γ Δ A₂) → Term Γ Δ (A₁ ∨ A₂)

  data Continuation {n m} (Γ : Context n) (Δ : Context m) : Type → Set where
    var : (x : Fin m) → Continuation Γ Δ (lookup x Δ)
    μ : {A : Type} → (c : Command (A ∷ Γ) Δ) → Continuation Γ Δ A
    _∷_ : {A B : Type} → (t : Term Γ Δ A) → (e : Continuation Γ Δ B) → Continuation Γ Δ (A ⇒ B)
    _,_ : {A₁ A₂ : Type} → (e₁ : Continuation Γ Δ A₁) → (e₂ : Continuation Γ Δ A₂) → Continuation Γ Δ (A₁ ∨ A₂)
    inj₁ : {A₁ A₂ : Type} → (e : Continuation Γ Δ A₁) → Continuation Γ Δ (A₁ ∧ A₂)
    inj₂ : {A₁ A₂ : Type} → (e : Continuation Γ Δ A₂) → Continuation Γ Δ (A₁ ∧ A₂)

  data Command {n m} (Γ : Context n) (Δ : Context m) : Set where
    <_∣_> : {A : Type} → (t : Term Γ Δ A) → (e : Continuation Γ Δ A) → Command Γ Δ

devil : ∀ {a : Type} → Term [] [] (a ∨ ¬ a)
devil = μ < inj₂ (lam (μ < inj₁ (var 0) ∣ var 1 >)) ∣ var 0 >
