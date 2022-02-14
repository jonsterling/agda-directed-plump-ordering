{-# OPTIONS --rewriting #-}

module Preamble where

open import Level public
open import Function public
open import Data.Unit using (⊤; tt) public
open import Data.Bool using (Bool; true; false) public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public

coe : {l k : _} {A : Set l} (P : A → Set k) {a b : A} → a ≡ b → P a → P b
coe P refl x = x

data Acc {A : Set} (R : A → A → Set) (a : A) : Set where
  acc : ((b : A) → R b a → Acc R b) → Acc R a

un-acc : {A : Set} {R : A → A → Set} {a : A} → Acc R a → (b : A) → R b a → Acc R b
un-acc (acc f) = f


is-wf : {A : Set} (R : A → A → Set) → Set
is-wf R = (a : _) → Acc R a

record _≅_ {l k} (A : Set l) (B : Set k) : Set (l ⊔ k) where
  field
    fwd : A → B
    bwd : B → A
    fwd-bwd : ∀ x → fwd (bwd x) ≡ x
    bwd-fwd : ∀ x → bwd (fwd x) ≡ x

open _≅_ public

record W {l k} (A : Set l) (B : A → Set k) : Set (l ⊔ k) where
  inductive
  pattern
  constructor ub
  field
    lbl : A
    sub : B lbl → W A B

open W public

record RegularUniverse ℓ : Set (suc ℓ) where
  field
    tp : Set ℓ
    el : tp → Set ℓ
    `unit : tp
    `Σ : (α : tp) → (el α → tp) → tp
    el/`unit : ⊤ ≅ el `unit
    el/`Σ : ∀ {α} {β} → Σ (el α) (el ∘ β) ≅ el (`Σ α β)

infix 11 _▷_
infix 11 _[_]
record Fam {l k} (𝒰 : RegularUniverse l) (A : Set k) : Set (l ⊔ k) where
  constructor _▷_
  open RegularUniverse 𝒰
  field
    size : tp
  ix = el size
  field
    elt : ix → A

open Fam public
∣_∣ = Fam.size
_[_] = Fam.elt

push : ∀ {l k m} {𝒰 : RegularUniverse l} {A : Set k} {B : Set m} → (A → B) → Fam 𝒰 A → Fam 𝒰 B
push f S = _ ▷ λ x → f (S [ x ])


record Container ℓ : Set (suc ℓ) where
  field
    𝒮 : Set ℓ
    𝒫 : 𝒮 → Set ℓ

μ : {ℓ : _} → Container ℓ → Set ℓ
μ 𝒞 = let open Container 𝒞 in W 𝒮 𝒫


module 𝔽+ where
  data 𝔽+ : Set
  el : 𝔽+ → Set

  data 𝔽+ where
    `unit : 𝔽+
    `bool : 𝔽+
    `Σ : (α : 𝔽+) → (el α → 𝔽+) → 𝔽+

  el `unit = ⊤
  el `bool = Bool
  el (`Σ α β) = Σ (el α) λ i → el (β i)

  module RU = RegularUniverse

  𝒰 : RegularUniverse zero
  RU.tp 𝒰 = 𝔽+
  RU.el 𝒰 = el

  RU.`unit 𝒰 = `unit
  RU.`Σ 𝒰 = `Σ

  fwd (RU.el/`unit 𝒰) _ = tt
  bwd (RU.el/`unit 𝒰) _ = tt
  fwd-bwd (RU.el/`unit 𝒰) _ = refl
  bwd-fwd (RU.el/`unit 𝒰) _ = refl

  fwd (RU.el/`Σ 𝒰) p = p
  bwd (RU.el/`Σ 𝒰) p = p
  fwd-bwd (RU.el/`Σ 𝒰) _ = refl
  bwd-fwd (RU.el/`Σ 𝒰) _ = refl
