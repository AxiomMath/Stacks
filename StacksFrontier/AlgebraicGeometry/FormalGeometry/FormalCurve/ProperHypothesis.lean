module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.Algebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The properness hypothesis of Tag 0E7R cannot be dropped

The statement of [Stacks, Tag 0E7R] on the Stacks project website reads "If `dim(X₁) ≤ 1`, then
there exists a projective morphism of schemes `X ⟶ S` and isomorphisms `Xₙ ≅ X ×_S Sₙ`"; its
proof opens with "Hence `X₁` is a proper scheme of dimension `≤ 1` over `κ`", and the statement as
formalized in this library carries the hypothesis
"`X₁ ⟶ S₁` is proper". This file proves that the hypothesis is needed: without it the statement
is false already for schemes, over a field, for the constant tower of affine lines.

Indeed, an algebraization `X ⟶ S` which is projective is proper, so its base change
`X₁ = X ×_S S₁` would be proper over `S₁`; but `𝔸¹_k ⟶ Spec k` is affine, so properness would make
it finite, and `k[x]` is not a finite `k`-module.

## Main results

* `Stacks.FormalCurve.FormalCurveAlgebraizationWithoutProperness` — the statement with the
  properness hypothesis removed, for towers of schemes.
* `Stacks.FormalCurve.not_formalCurveAlgebraizationWithoutProperness` — its negation.

## References

* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.FormalCurve

/-- The scheme form of [Stacks, Tag 0E7R] **without** the hypothesis that `X₁ ⟶ S₁` is proper:
for every complete local Noetherian ring `A` and every cartesian tower of schemes over the
thickenings `Spec (A / 𝔪 ^ (n + 1))` with `dim X₀ ≤ 1`, there is a projective `X ⟶ Spec A`
exhibiting every member of the tower as its base change. This is false; see
`not_formalCurveAlgebraizationWithoutProperness`. -/
def FormalCurveAlgebraizationWithoutProperness : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (Xn : ℕ → Scheme.{u})
    (q : ∀ n, Xn n ⟶ adicThickening A (maximalIdeal A) n) (i : ∀ n, Xn n ⟶ Xn (n + 1)),
    (∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A (maximalIdeal A) n)) →
    topologicalKrullDim (Xn 0 : Type u) ≤ 1 →
    ∃ (X : Scheme.{u}) (fX : X ⟶ Spec (.of A)), IsProjective fX ∧
      ∃ k : ∀ n, Xn n ⟶ X, (∀ n, i n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A (maximalIdeal A) n)

section Counterexample

variable (k : Type u) [Field k]

/-- The structure map `k / 𝔪 ^ (n + 1) ⟶ k[x]` of the affine line over a field, the maximal ideal
being zero. -/
def lineStructureMap (n : ℕ) : (k ⧸ maximalIdeal k ^ (n + 1)) →+* Polynomial k :=
  Polynomial.C.comp (Ideal.Quotient.lift _ (RingHom.id k) fun a ha => by
    rw [maximalIdeal_eq_bot, Submodule.bot_pow (Nat.succ_ne_zero n)] at ha
    simpa using ha)

/-- `lineStructureMap k n` sends the class of `a : k` to the constant polynomial `C a`. -/
lemma lineStructureMap_mk (n : ℕ) (a : k) :
    lineStructureMap k n (Ideal.Quotient.mk _ a) = Polynomial.C a := rfl

/-- The structure maps `lineStructureMap k n` are compatible with the transition maps
`k / 𝔪 ^ (n + 2) ⟶ k / 𝔪 ^ (n + 1)`. -/
lemma lineStructureMap_comp (n : ℕ) :
    (lineStructureMap k n).comp (Ideal.Quotient.factorPow (maximalIdeal k) (Nat.le_succ (n + 1))) =
      lineStructureMap k (n + 1) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

/-- For a field `k`, the transition map `k / 𝔪 ^ (n + 2) ⟶ k / 𝔪 ^ (n + 1)` is bijective. -/
lemma bijective_factorPow (n : ℕ) :
    Function.Bijective (Ideal.Quotient.factorPow (maximalIdeal k) (Nat.le_succ (n + 1))) := by
  refine ⟨?_, Ideal.Quotient.factor_surjective _⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, maximalIdeal_eq_bot,
    Submodule.bot_pow (Nat.succ_ne_zero n)] at hx
  rw [show a = 0 by simpa using hx, map_zero]

/-- For a field `k`, the closed immersions between consecutive thickenings
`Spec (k / 𝔪 ^ (n + 1)) ⟶ Spec (k / 𝔪 ^ (n + 2))` are isomorphisms. -/
instance isIso_adicThickeningSucc_field (n : ℕ) :
    IsIso (adicThickeningSucc k (maximalIdeal k) n) := by
  have : IsIso (CommRingCat.ofHom
      (Ideal.Quotient.factorPow (maximalIdeal k) (Nat.le_succ (n + 1)))) :=
    (RingEquiv.ofBijective _ (bijective_factorPow k n)).toCommRingCatIso.isIso_hom
  exact inferInstanceAs (IsIso (Spec.map _))

/-- The constant tower of affine lines over the thickenings of a field. -/
abbrev lineTower (n : ℕ) : Scheme.{u} := Spec (.of (Polynomial k))

/-- Its structure maps. -/
def lineTowerHom (n : ℕ) : lineTower k n ⟶ adicThickening k (maximalIdeal k) n :=
  Spec.map (CommRingCat.ofHom (lineStructureMap k n))

/-- The constant tower of affine lines is cartesian: each square formed by the identity of
`lineTower k n`, the structure morphisms and `adicThickeningSucc` is a pullback. -/
lemma isPullback_lineTower (n : ℕ) :
    IsPullback (𝟙 (lineTower k n)) (lineTowerHom k n) (lineTowerHom k (n + 1))
      (adicThickeningSucc k (maximalIdeal k) n) := by
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  rw [Category.id_comp, lineTowerHom, lineTowerHom, adicThickeningSucc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, lineStructureMap_comp]

/-- The affine line `lineTower k 0` over a field has dimension at most one. -/
lemma topologicalKrullDim_lineTower : topologicalKrullDim (lineTower k 0 : Type u) ≤ 1 := by
  show topologicalKrullDim (PrimeSpectrum (Polynomial k)) ≤ 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  refine Polynomial.ringKrullDim_le.trans ?_
  rw [ringKrullDim_eq_zero_of_field]
  norm_num

end Counterexample

/-- **The properness hypothesis of [Stacks, Tag 0E7R] is necessary.** Over a field `k`, the
constant tower of affine lines is cartesian of dimension one, but it has no projective
algebraization: the base change of a projective morphism is proper, and `𝔸¹_k ⟶ Spec k` is not,
being affine with `k[x]` not finite over `k`. -/
theorem not_formalCurveAlgebraizationWithoutProperness :
    ¬ FormalCurveAlgebraizationWithoutProperness.{u} := by
  intro h
  let k := ULift.{u} ℚ
  obtain ⟨X, fX, hfX, kk, -, hpb⟩ := h k (lineTower k) (lineTowerHom k) (fun _ => 𝟙 _)
    (isPullback_lineTower k) (topologicalKrullDim_lineTower k)
  have : IsProper fX := hfX.isProper
  have : IsProper (lineTowerHom k 0) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpb 0) inferInstance
  have hfin : IsFinite (lineTowerHom k 0) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  rw [lineTowerHom, IsFinite.SpecMap_iff] at hfin
  have hcomp : (lineStructureMap k 0).comp (Ideal.Quotient.mk (maximalIdeal k ^ (0 + 1))) =
      algebraMap k (Polynomial k) := RingHom.ext fun _ => rfl
  have hC : (algebraMap k (Polynomial k)).Finite := by
    rw [← hcomp]
    exact hfin.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
  exact Polynomial.not_finite (R := k) (RingHom.finite_algebraMap.1 hC)

end Stacks.FormalCurve

end
