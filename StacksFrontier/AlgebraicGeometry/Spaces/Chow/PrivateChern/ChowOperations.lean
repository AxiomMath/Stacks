module

public import Mathlib.Algebra.DirectSum.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence

/-!
# Operations on the Chow homology of a good algebraic space

In Situation 0EDT let `X/B` be good. Its *Chow homology* is the graded abelian group
`CH_*(X) = ⨁_k CH_k(X)`. The operations of chapter 82 that enter the definition of Chern
classes are all induced by homomorphisms of cycle groups which respect rational equivalence:

* flat pullback `f^* : Z_k(Y) ⟶ Z_{k+r}(X)` along a flat morphism of relative dimension `r`
  (Stacks 0EP8), which respects rational equivalence by Stacks 0EQB;
* proper pushforward `p_* : Z_k(X) ⟶ Z_k(Y)` (Stacks 0EP1), by Stacks 0EQC;
* the cap product `c₁(ℒ) ∩ - : Z_{k+1}(X) ⟶ Z_k(X)` with the first Chern class of an invertible
  module, read at the canonical component cycles of Stacks 0EQJ, by Stacks 0EQY.

This file records the passage from such a homomorphism of cycle groups to the operation it
induces on Chow groups, and the operations themselves, on `CH_*`, as homogeneous homomorphisms
of the graded groups.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.chowHomology`: `CH_*(X) = ⨁_k CH_k(X)`.
* `AlgebraicGeometry.Space.PrivateChern.chowDescend`: the homomorphism `CH_k(X) ⟶ CH_m(Y)`
  induced by a homomorphism `Z_k(X) ⟶ Z_m(Y)` carrying cycles rationally equivalent to zero to
  cycles rationally equivalent to zero.
* `AlgebraicGeometry.Space.PrivateChern.chowGroupDegreeCongr`: the identification of
  `CH_a(X)` with `CH_b(X)` for `a = b`.
* `AlgebraicGeometry.Space.PrivateChern.gradedChowMap`: the homomorphism of Chow homologies
  assembled from homomorphisms `CH_k(X) ⟶ CH_{k+s}(Y)`, homogeneous of degree `s`.
* `AlgebraicGeometry.Space.PrivateChern.flatPullbackChow`,
  `AlgebraicGeometry.Space.PrivateChern.properPushforwardChow` and
  `AlgebraicGeometry.Space.PrivateChern.firstChernCapChow`: the three operations above on
  `CH_*`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chowDescend_chowClass`: on the class of a cycle, the
  induced homomorphism is the class of the image cycle.
* `AlgebraicGeometry.Space.PrivateChern.gradedChowMap_of`: the graded homomorphism on a
  homogeneous element.

## Implementation notes

`AlgebraicGeometry.Space.PrivateChern.chowDescend` is defined for every homomorphism of cycle
groups: it is the induced homomorphism when the condition holds and zero otherwise. For each of
the three operations of this file the condition is a theorem of chapter 82 (Stacks 0EQB, 0EQC
and 0EQY), so the definition is the induced operation itself; the case distinction only
separates the construction of the operations from the proofs of those three theorems, and every
computation with the operations goes through
`AlgebraicGeometry.Space.PrivateChern.chowDescend_chowClass`, which takes the condition as its
hypothesis.

## References

* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X Y : D.Ambient}

/-! ### Chow homology and induced homomorphisms -/

/-- **The Chow homology** `CH_*(X) = ⨁_k CH_k(X)` of a good algebraic space over the base. -/
abbrev chowHomology (sX : X ⟶ D.space) (hX : D.IsGood sX) : Type (u + 1) :=
  DirectSum ℤ fun k => chowGroup.{v} D sX hX k

/-- A homomorphism of cycle groups *respects rational equivalence* when it carries every cycle
rationally equivalent to zero to a cycle rationally equivalent to zero. -/
def RespectsRationalEquivalence (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {k m : ℤ} (φ : CycleGroup D sX k →+ CycleGroup D sY m) : Prop :=
  rationalEquivalences.{v} D sX hX k ≤ (rationalEquivalences.{v} D sY hY m).comap φ

open Classical in
/-- **The homomorphism of Chow groups induced by a homomorphism of cycle groups.** When `φ`
respects rational equivalence this is the induced homomorphism `CH_k(X) ⟶ CH_m(Y)`; otherwise it
is zero (see the implementation notes). -/
def chowDescend (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {k m : ℤ} (φ : CycleGroup D sX k →+ CycleGroup D sY m) :
    chowGroup.{v} D sX hX k →+ chowGroup.{v} D sY hY m :=
  if h : RespectsRationalEquivalence.{u, v} D sX hX sY hY φ then
    QuotientAddGroup.map _ _ φ h
  else 0

/-- On the class of a cycle, the homomorphism induced by a homomorphism respecting rational
equivalence is the class of the image. -/
theorem chowDescend_chowClass (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {k m : ℤ} (φ : CycleGroup D sX k →+ CycleGroup D sY m)
    (hφ : RespectsRationalEquivalence.{u, v} D sX hX sY hY φ) (α : CycleGroup D sX k) :
    chowDescend.{u, v} D sX hX sY hY φ (chowClass.{v} D sX hX k α) =
      chowClass.{v} D sY hY m (φ α) := by
  rw [chowDescend, dif_pos hφ]
  rfl

/-- The identification of `CH_a(X)` with `CH_b(X)` along an equality of degrees `a = b`. -/
def chowGroupDegreeCongr (sX : X ⟶ D.space) (hX : D.IsGood sX) {a b : ℤ} (h : a = b) :
    chowGroup.{v} D sX hX a ≃+ chowGroup.{v} D sX hX b := by
  subst h
  exact AddEquiv.refl _

/-- Along the reflexive equality `a = a`, the identification `chowGroupDegreeCongr` is the
identity. -/
@[simp]
theorem chowGroupDegreeCongr_rfl (sX : X ⟶ D.space) (hX : D.IsGood sX) (a : ℤ)
    (α : chowGroup.{v} D sX hX a) :
    chowGroupDegreeCongr.{u, v} D sX hX (rfl : a = a) α = α :=
  rfl

/-- **A homogeneous homomorphism of Chow homologies of degree `s`**, assembled from
homomorphisms `CH_k(X) ⟶ CH_{k+s}(Y)`, one for each `k`. -/
def gradedChowMap (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (s : ℤ) (φ : ∀ k : ℤ, chowGroup.{v} D sX hX k →+ chowGroup.{v} D sY hY (k + s)) :
    chowHomology.{u, v} D sX hX →+ chowHomology.{u, v} D sY hY :=
  DirectSum.toAddMonoid fun k => (DirectSum.of (fun k => chowGroup.{v} D sY hY k) (k + s)).comp
    (φ k)

/-- On the summand `CH_k(X)`, the graded homomorphism `gradedChowMap` sends `α` to `φ k α` in
the summand `CH_{k+s}(Y)`. -/
@[simp]
theorem gradedChowMap_of (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (s : ℤ)
    (φ : ∀ k : ℤ, chowGroup.{v} D sX hX k →+ chowGroup.{v} D sY hY (k + s)) (k : ℤ)
    (α : chowGroup.{v} D sX hX k) :
    gradedChowMap.{u, v} D sX hX sY hY s φ (DirectSum.of _ k α) =
      DirectSum.of (fun k => chowGroup.{v} D sY hY k) (k + s) (φ k α) :=
  DirectSum.toAddMonoid_of _ _ _

/-! ### The three operations -/

/-- **Flat pullback on Chow homology** along a flat morphism `f : X ⟶ Y` of good algebraic
spaces over the base of relative dimension `r`: on `CH_k(Y)` it is the homomorphism
`CH_k(Y) ⟶ CH_{k+r}(X)` induced by flat pullback of cycles (Stacks 0EP8; it respects rational
equivalence by Stacks 0EQB). -/
def flatPullbackChow (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) :
    chowHomology.{u, v} D sY hY →+ chowHomology.{u, v} D sX hX :=
  gradedChowMap.{u, v} D sY hY sX hX r fun k =>
    chowDescend.{u, v} D sY hY sX hX
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + r) rfl)

/-- **Proper pushforward on Chow homology** along a proper morphism `p : X ⟶ Y` of good
algebraic spaces over the base: on `CH_k(X)` it is the homomorphism `CH_k(X) ⟶ CH_k(Y)`
induced by proper pushforward of cycles (Stacks 0EP1; it respects rational equivalence by
Stacks 0EQC). -/
def properPushforwardChow (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (p : X ⟶ Y) (hbase : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) :
    chowHomology.{u, v} D sX hX →+ chowHomology.{u, v} D sY hY :=
  gradedChowMap.{u, v} D sX hX sY hY 0 fun k =>
    (chowGroupDegreeCongr.{u, v} D sY hY (add_zero k).symm).toAddMonoidHom.comp
      (chowDescend.{u, v} D sX hX sY hY
        (properCyclePushforward D sX hX sY hY hbase hp.2.1.2 k))

/-- **The cap product with the first Chern class on Chow homology**: for an invertible module
`𝒩` on a good algebraic space `X`, on `CH_k(X)` it is the homomorphism `CH_k(X) ⟶ CH_{k-1}(X)`
induced by the cap product `c₁(𝒩) ∩ - : Z_k(X) ⟶ Z_{k-1}(X)` of Stacks 0EQJ at the canonical
component cycles (`AlgebraicGeometry.Space.canonicalFirstChernRule`), which respects rational
equivalence by Stacks 0EQY. -/
def firstChernCapChow (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N) :
    chowHomology.{u, v} D sX hX →+ chowHomology.{u, v} D sX hX :=
  gradedChowMap.{u, v} D sX hX sX hX (-1) fun k =>
    (chowDescend.{u, v} D sX hX sX hX
        (firstChernCapCycleMap D sX hX (k + -1)
          (canonicalFirstChernRule D sX hX N hN (k + -1)))).comp
      (chowGroupDegreeCongr.{u, v} D sX hX (by omega : k = k + -1 + 1)).toAddMonoidHom

end AlgebraicGeometry.Space.PrivateChern

end
