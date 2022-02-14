{-# OPTIONS --rewriting --confluence #-}

module Ordering where

open import Preamble

-- A join structure for a container consists of an operation on
-- families of shapes whose set of positions of the coproduct of the
-- positions.
record JoinStructure {l k} (𝒰 : RegularUniverse l) (𝒞 : Container k) : Set (l ⊔ k) where
  open Container 𝒞
  field
    join : Fam 𝒰 𝒮 → 𝒮
    𝒫/join : {S : Fam 𝒰 𝒮} → Σ (ix S) (λ i → 𝒫 (S [ i ])) ≅ 𝒫 (join S)


-- In addition to a container 𝒞, this module should be parameterized
-- in a join structure for 𝒞. We instead make this assumption into a
-- postulates in order to enable Agda's REWRITE mechanism.

module Ordinals (𝒞 : Container zero) where

  -- We open the regular universe of non-empty lists
  open 𝔽+

  -- Think of this as a parameter
  postulate
    𝒞/join : JoinStructure 𝔽+.𝒰 𝒞

  infixr 10 ⨆_

  open Container 𝒞
  open JoinStructure 𝒞/join

  𝒯 = μ 𝒞

  List+ : Set → Set
  List+ X = Fam 𝒰 X

  𝒫/join/bwd-fwd = λ {S} → bwd-fwd (𝒫/join {S})
  {-# REWRITE 𝒫/join/bwd-fwd #-}

  ⨆_ : List+ 𝒯 → 𝒯
  ⨆ S = ub (join (_ ▷ (lbl ∘ S [_]))) λ b → let (i , j) = bwd 𝒫/join b in sub (S [ i ]) j

  infix 9 _≤_ _≺_
  record _≺_ (u v : 𝒯) : Set
  record _≤_ (u v : 𝒯) : Set

  record _≺_ u v where
    inductive
    pattern
    constructor make
    field
      pofam : List+ (𝒫 (lbl v))
      is-ub : u ≤ ⨆ push (sub v) pofam

  record _≤_ u v where
    inductive
    pattern
    constructor make
    field
      out : (b : 𝒫 (lbl u)) → sub u b ≺ v


  open _≺_ public
  open _≤_ public


  ≤/lub-unit/r : (u : 𝒯) → u ≤ ⨆ `unit ▷ (λ _ → u)
  ≤/lub-unit/r (ub a v) =
   make λ b →
   make
    (`unit ▷ λ _ →
     fwd 𝒫/join
      (tt , b))
    (≤/lub-unit/r (v b))

  ≤/lub-unit/l : (u : 𝒯) → (⨆ `unit ▷ λ _ → u) ≤ u
  ≤/lub-unit/l (ub a v) =
    make λ b →
    let j = bwd 𝒫/join b .snd in
    make
     (`unit ▷ λ _ → j)
     (≤/lub-unit/r (v j))

  ≤/refl : (u : 𝒯) → u ≤ u
  ≤/refl u =
    make λ b →
    make
     (`unit ▷ λ _ → b)
     (≤/lub-unit/r (sub u b))


  ≤/trans : {u v w : 𝒯} → u ≤ v → v ≤ w → u ≤ w
  ≺/rflex : {u v w : 𝒯} → u ≺ v → v ≤ w → u ≺ w

  ≤/trans (make uv) vw =
     make λ b →
     ≺/rflex (uv b) vw

  ≺/rflex {u} {v} {w} (make (n ▷ bv) uv) (make vw) =
    make (m ▷ bw) (≤/trans uv lem)
    where
      m = `Σ n λ i → ∣ vw (bv i) .pofam ∣

      bw : el m → 𝒫 (lbl w)
      bw x = let (i , j) = x in vw (bv i) .pofam [ j ]

      lem : (⨆ n ▷ (λ i → sub v (bv i))) ≤ ⨆ m ▷ λ ij → sub w (bw ij)
      lem =
        make λ ij →
         let (i , j) = bwd 𝒫/join ij in
         let p = vw (bv i) .is-ub .out j in
         make
           (_ ▷ λ x →
            let k , l = bwd 𝒫/join (p .pofam [ x ]) in
            fwd 𝒫/join ((i , k) , l))
           (p .is-ub)


  ≺/lflex : {u v w : 𝒯} → u ≤ v → v ≺ w → u ≺ w
  ≺/lflex uv vw = make (vw .pofam) (≤/trans uv (vw .is-ub))


  ≺≤ : {u v : 𝒯} → u ≺ v → u ≤ v
  ≺≤ {u} {v} (make pofam (uv @ (make uv'))) =
    make λ b' →
    make pofam (≺≤ (uv .out b'))

  ≺/trans : {u v w : 𝒯} → u ≺ v → v ≺ w → u ≺ w
  ≺/trans {u} {v} {w} uv vw = ≺/rflex uv (≺≤ vw)


  Lub/elim/≤/bwd : (U : List+ 𝒯) {v : 𝒯} → ⨆ U ≤ v → (i : ix U) → U [ i ] ≤ v
  Lub/elim/≤/bwd U {v} uv i =
    make λ b →
    uv .out (fwd 𝒫/join (i , b))


  Lub/elim/≤ : (U : List+ 𝒯) {v : 𝒯} → ((i : ix U) → U [ i ] ≤ v) → ⨆ U ≤ v
  Lub/elim/≤ U {v} uv =
    make λ b →
    let i , x = bwd 𝒫/join b in
    uv i .out x

  Lub/elim/≺ : (U : List+ 𝒯) {v : 𝒯} → ((i : ix U) → U [ i ] ≺ v) → ⨆ U ≺ v
  Lub/elim/≺ U {v} uv =
    make (m ▷ b) p

    where
      m : 𝔽+
      m = `Σ ∣ U ∣ λ i → ∣ uv i .pofam ∣

      b : el m → 𝒫 (lbl v)
      b x =
        let (i , j) = x in
        uv i .pofam [ j ]

      p : ⨆ U ≤ ⨆ m ▷ (λ i → sub v (b i))
      p =
        make λ b' →
        let (i , j) = bwd 𝒫/join b' in
        ≺/rflex
         (uv i .is-ub .out j)
         (Lub/elim/≤ (_ ▷ λ j → sub v (b (i , j))) λ k →
          make λ b' →
          ≤/refl (⨆ m ▷ (λ k → sub v (b k))) .out (fwd 𝒫/join ((i , k) , b')))


  infix 10 _<_

  data _<_ : 𝒯 → 𝒯 → Set where
    make : (u : 𝒯) (b : 𝒫 (lbl u)) → u .sub b < u

  <-wf : is-wf _<_
  <-wf u@(ub i v) =
    acc λ where
    .(v b) (make .(ub i v) b) →
      <-wf (v b)

  record _⊏_ (xs ys : List+ 𝒯) : Set where
    constructor make
    field
      ren : ix xs → ix ys
      lt : (i : ix xs) → xs [ i ] < ys [ ren i ]

  open _⊏_


  module ≺-wf
    (R : List+ 𝒯 → List+ 𝒯 → Set)
    (R-wf : is-wf R)
    (R/make
      : (ws : List+ 𝒯)
      → (b : List+ (Σ (ix ws) λ i → 𝒫 (lbl (ws [ i ]))))
      → ((z : ix b) → (ws [ fst (b [ z ]) ]) .sub (snd (b [ z ])) < ws [ fst (b [ z ]) ])
      → R (push (λ z → (ws [ fst z ]) .sub (snd z)) b) ws)
    where

    ≺-wf-lemma : (u : 𝒯) (ws : List+ 𝒯) (hws : Acc R ws) (let w = ⨆ ws) → u ≤ w → Acc _≺_ u
    ≺-wf-lemma u ws hws@(acc hws') uw@(make uw') =
      let w = ⨆ ws in
      acc λ where
      v vu@(make po-vu' bdy-vu') →
        let
          vw : v ≺ w
          vw = ≺/rflex vu uw

          b : List+ (𝒫 (lbl w))
          b = vw .pofam

          b' = push (bwd 𝒫/join) b

          w's : List+ 𝒯
          w's = push (sub w) b

          w's⊏ws : R w's ws
          w's⊏ws = R/make ws _ λ z → make _ (snd (b' [ z ]))

          hw's : Acc R w's
          hw's = hws' w's w's⊏ws
        in
        ≺-wf-lemma v w's hw's (vw .is-ub)

    ≺-wf : is-wf _≺_
    ≺-wf u = ≺-wf-lemma u (`unit ▷ λ _ → u) (R-wf _) (≤/lub-unit/r u)


  ≺-wf : is-wf _⊏_ → is-wf _≺_
  ≺-wf ⊏-wf = ≺-wf.≺-wf _⊏_ ⊏-wf λ ws b x → make (fst ∘ b [_]) λ i → make _ (snd (b [ i ]))
