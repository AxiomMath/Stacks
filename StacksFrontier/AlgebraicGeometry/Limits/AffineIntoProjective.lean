module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom

/-!
# The standard affine chart of projective space

Projective `n`-space over a base `S` is covered by `n + 1` copies of affine `n`-space over `S`.
This file constructs the chart at the first coordinate,
`AlgebraicGeometry.ProjectiveSpace.affineChart`, as an open immersion `𝔸ⁿ_S ⟶ ℙⁿ_S` over `S`.

Over the integers the chart is Mathlib's `AlgebraicGeometry.Proj.awayι`, the open immersion
`Spec (A_f)₀ ⟶ Proj A` at a homogeneous element `f` of positive degree, taken at `f = X 0`. What
this file supplies is the identification of the degree-zero part of the away-localization with a
polynomial ring, `AlgebraicGeometry.ProjectiveSpace.awayChartEquiv`, i.e. the statement that
dehomogenizing at `X 0` is a bijection from the fractions `a / X 0 ^ d` with `a` homogeneous of
degree `d` onto the polynomial ring in the remaining `n` variables. The chart over a general
base is then the base change of the integral chart along `S ⟶ Spec ℤ`, which is an open
immersion because open immersions are stable under base change: both `𝔸ⁿ_S` and `ℙⁿ_S` are by
construction pullbacks over the terminal scheme of their integral models.

The point of the chart is `AlgebraicGeometry.HasChowModification.of_isAffine`: for an affine
scheme of finite type over an affine base, the conclusion of Chow's lemma (Stacks 0202) holds
outright, with the identity as the modification. A morphism of affine schemes locally of finite
type factors as a closed immersion into an affine space over the target
(`AlgebraicGeometry.exists_isClosedImmersion_affineSpace`), and composing that closed immersion
with the chart gives an immersion into a projective space over the target, which is what
`AlgebraicGeometry.HasChowModification` asks for.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpace.dehomogenize` sets the first variable of a polynomial ring
  to `1`.
* `AlgebraicGeometry.ProjectiveSpace.awayChartEquiv` identifies the polynomial ring in `n`
  variables with the degree-zero part of the localization of the polynomial ring in `n + 1`
  variables away from its first variable.
* `AlgebraicGeometry.ProjectiveSpace.affineChartZ` is the standard affine chart of the integral
  model of projective space.
* `AlgebraicGeometry.ProjectiveSpace.affineChart` is the standard affine chart `𝔸ⁿ_S ⟶ ℙⁿ_S`.

## Main results

* `AlgebraicGeometry.ProjectiveSpace.affineChart_over`: the chart is a morphism over `S`.
* `AlgebraicGeometry.ProjectiveSpace.isPullback_affineChart`: the chart is the base change of the
  integral chart, whence it is an open immersion.
* `AlgebraicGeometry.HasChowModification.of_isAffine`: Chow's lemma holds for an affine scheme of
  finite type over an affine base.

## Implementation notes

The chart is stated against `AlgebraicGeometry.ProjectiveSpace`, the model of projective space
used by `AlgebraicGeometry.HasChowModification`, and against `AlgebraicGeometry.AffineSpace`
indexed by `ULift (Fin n)`, which is the index type produced by
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace`. Variables of the integral model are
indexed by `Fin (n + 1)`, and the chart is taken at the variable `X 0`.

That the dehomogenization map is bijective is proved without any homogenization: it has a
one-sided inverse `awayChartInv` by a computation on generators, and `awayChartInv` is surjective
because Mathlib's `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top` exhibits generators of
the away-localization that visibly lie in its range.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
-/

@[expose] public section

open CategoryTheory Limits HomogeneousLocalization MvPolynomial

noncomputable section

namespace AlgebraicGeometry

universe u

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (R : Type u) [CommRing R]

/-- **Dehomogenization at the first variable.** The ring map that sends `X 0` to `1` and
`X (i + 1)` to the `i`-th variable of the polynomial ring in `n` variables. On a form of degree
`d` it computes the numerator of the fraction `a / X 0 ^ d` in the chart. -/
def dehomogenize : MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
  eval₂Hom C (fun i => Fin.cases (motive := fun _ => MvPolynomial (Fin n) R) 1 X i)

/-- A variable is homogeneous of degree one. -/
theorem X_mem_homogeneousSubmodule (i : Fin (n + 1)) :
    (X i : MvPolynomial (Fin (n + 1)) R) ∈ homogeneousSubmodule (Fin (n + 1)) R 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X R _)

/-- A variable is homogeneous of degree `1 • 1`, the form in which `Away.mk` wants it. -/
theorem X_mem_homogeneousSubmodule_smul (i : Fin (n + 1)) :
    (X i : MvPolynomial (Fin (n + 1)) R) ∈ homogeneousSubmodule (Fin (n + 1)) R (1 • 1) := by
  simpa using X_mem_homogeneousSubmodule n R i

/-- A constant is homogeneous of degree `0 • 1`, the form in which `Away.mk` wants it. -/
theorem C_mem_homogeneousSubmodule_smul (r : R) :
    (C r : MvPolynomial (Fin (n + 1)) R) ∈ homogeneousSubmodule (Fin (n + 1)) R (0 • 1) := by
  simp

/-- Dehomogenization sends the first variable to `1`, which is a unit; this is what makes it
factor through the localization away from that variable. -/
theorem isUnit_dehomogenize_X_zero : IsUnit (dehomogenize n R (X (0 : Fin (n + 1)))) := by
  simp [dehomogenize]

/-- **The chart map.** Dehomogenization extends to the degree-zero part of the localization away
from `X 0`, because it inverts `X 0`. -/
def awayChartHom :
    Away (homogeneousSubmodule (Fin (n + 1)) R) (X 0) →+* MvPolynomial (Fin n) R :=
  (Localization.awayLift (dehomogenize n R) (X 0) (isUnit_dehomogenize_X_zero n R)).comp
    (algebraMap _ _)

/-- **The inverse chart map.** The ring map sending the `i`-th variable to the fraction
`X (i + 1) / X 0`. -/
def awayChartInv : MvPolynomial (Fin n) R →+*
    Away (homogeneousSubmodule (Fin (n + 1)) R) (X 0) :=
  eval₂Hom ((fromZeroRingHom _ _).comp (algebraMap R _))
    (fun i => Away.mk _ (X_mem_homogeneousSubmodule n R 0) 1 (X i.succ)
      (X_mem_homogeneousSubmodule_smul n R i.succ))

/-- The chart map takes the fraction `a / X 0 ^ j` to the dehomogenization of `a`. -/
theorem awayChartHom_mk (j : ℕ) (a : MvPolynomial (Fin (n + 1)) R)
    (ha : a ∈ homogeneousSubmodule (Fin (n + 1)) R (j • 1)) :
    awayChartHom n R (Away.mk _ (X_mem_homogeneousSubmodule n R 0) j a ha) =
      dehomogenize n R a := by
  have h1 : dehomogenize n R (X 0) * 1 = 1 := by simp [dehomogenize]
  rw [awayChartHom, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.awayLift_mk (dehomogenize n R) _ a 1 h1 j]
  simp

/-- The inverse chart map takes a constant to the fraction `C r / X 0 ^ 0`. -/
theorem awayChartInv_C (r : R) : awayChartInv n R (C r) =
    Away.mk _ (X_mem_homogeneousSubmodule n R 0) 0 (C r) (C_mem_homogeneousSubmodule_smul n R r) :=
  by
  apply HomogeneousLocalization.val_injective
  rw [awayChartInv, eval₂Hom_C, Away.val_mk]
  change (HomogeneousLocalization.mk _).val = _
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]

/-- **Dehomogenizing undoes the inverse chart map.** Both maps are determined by their values on
constants and on the variables, where the computation is immediate. -/
theorem awayChartHom_comp_awayChartInv :
    (awayChartHom n R).comp (awayChartInv n R) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [awayChartInv_C, awayChartHom_mk, dehomogenize]
  · simp [awayChartInv, awayChartHom_mk, dehomogenize]

/-- A polynomial ring is generated by its variables as an algebra over the degree-zero part of
its total-degree grading, that part consisting of the constants. -/
theorem adjoin_range_X_homogeneousSubmodule_zero :
    Algebra.adjoin ↥(homogeneousSubmodule (Fin (n + 1)) R 0)
      (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)) = ⊤ := by
  have key : ∀ p : MvPolynomial (Fin (n + 1)) R,
      p ∈ Algebra.adjoin ↥(homogeneousSubmodule (Fin (n + 1)) R 0)
        (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
        exact Subalgebra.algebraMap_mem _
          (⟨C r, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_C (Fin (n + 1)) r)⟩ :
            ↥(homogeneousSubmodule (Fin (n + 1)) R 0))
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  exact eq_top_iff.2 fun p _ => key p

/-- **The inverse chart map hits the generators of the away-localization.** A monomial of degree
`a` divided by `X 0 ^ a` is the product of the fractions `X (i + 1) / X 0`, the factor `X 0` of
the monomial cancelling against the denominator. -/
theorem awayChartInv_prod_X (a : ℕ) (ai : Fin (n + 1) → ℕ) (hai : ∑ i, ai i • 1 = a • 1)
    (h : (∏ i, (X i : MvPolynomial (Fin (n + 1)) R) ^ ai i) ∈
      homogeneousSubmodule (Fin (n + 1)) R (a • 1)) :
    awayChartInv n R (∏ j : Fin n, (X j : MvPolynomial (Fin n) R) ^ ai j.succ) =
      Away.mk _ (X_mem_homogeneousSubmodule n R 0) a (∏ i, X i ^ ai i) h := by
  have hsum : ai 0 + ∑ j : Fin n, ai j.succ = a := by
    simpa [Fin.sum_univ_succ] using hai
  apply HomogeneousLocalization.val_injective
  rw [map_prod]
  simp only [map_pow, awayChartInv, eval₂Hom_X']
  rw [← HomogeneousLocalization.algebraMap_apply, map_prod]
  simp only [map_pow, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_pow, Localization.mk_prod]
  rw [Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [SubmonoidClass.coe_pow, pow_one, Finset.prod_pow_eq_pow_sum, Fin.prod_univ_succ]
  rw [← hsum]
  ring

/-- The range of the inverse chart map contains the degree-zero part, over which the generators
of the away-localization are taken. -/
theorem awayChartInv_algebraMap_mem_range
    (b : ↥(homogeneousSubmodule (Fin (n + 1)) R 0)) :
    algebraMap _ (Away (homogeneousSubmodule (Fin (n + 1)) R) (X 0)) b ∈
      Set.range (awayChartInv n R) := by
  refine ⟨C ((gradeZeroEquiv (Fin (n + 1)) R).symm b), ?_⟩
  rw [awayChartInv, eval₂Hom_C, HomogeneousLocalization.algebraMap_eq]
  change (fromZeroRingHom _ _) ((algebraMap R _) _) = (fromZeroRingHom _ _) b
  congr 1
  exact (gradeZeroEquiv (Fin (n + 1)) R).apply_symm_apply b

/-- The range of the inverse chart map, as an algebra over the degree-zero part. -/
def awayChartInvRange : Subalgebra ↥(homogeneousSubmodule (Fin (n + 1)) R 0)
    (Away (homogeneousSubmodule (Fin (n + 1)) R) (X 0)) :=
  { (awayChartInv n R).range.toSubsemiring with
    algebraMap_mem' := awayChartInv_algebraMap_mem_range n R }

/-- **The inverse chart map is surjective.** Mathlib generates the away-localization at a
homogeneous element of degree `d` by the fractions `(∏ vᵢ ^ aᵢ) / f ^ a` for generators `vᵢ` of
the graded ring; for `f = X 0` of degree one and the variables as generators, every such
fraction is a product of the fractions `X (i + 1) / X 0`. -/
theorem awayChartInv_surjective : Function.Surjective (awayChartInv n R) := by
  intro x
  have h := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (X_mem_homogeneousSubmodule n R 0) (Fin (n + 1))
    (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (adjoin_range_X_homogeneousSubmodule_zero n R) (fun _ => 1)
    (X_mem_homogeneousSubmodule n R)
  have hx : x ∈ awayChartInvRange n R := by
    refine Algebra.adjoin_le ?_ (h.symm.le Algebra.mem_top)
    rintro y ⟨a, ai, hai, -, rfl⟩
    exact ⟨_, awayChartInv_prod_X n R a ai hai _⟩
  exact hx

/-- **The standard affine chart of projective space, on rings.** The degree-zero part of the
localization of `R[X₀, …, Xₙ]` away from `X₀` is the polynomial ring `R[Y₁, …, Yₙ]`, the variable
`Yᵢ` corresponding to the fraction `Xᵢ / X₀`. -/
def awayChartEquiv : MvPolynomial (Fin n) R ≃+*
    Away (homogeneousSubmodule (Fin (n + 1)) R) (X 0) :=
  RingEquiv.ofBijective (awayChartInv n R)
    ⟨Function.LeftInverse.injective (g := awayChartHom n R) fun p => by
      rw [← RingHom.comp_apply, awayChartHom_comp_awayChartInv, RingHom.id_apply],
      awayChartInv_surjective n R⟩

/-- The ring isomorphism `awayChartEquiv` over `ULift ℤ`, with the polynomial variables indexed by
`ULift (Fin n)`. -/
def awayChartEquivZ (n : ℕ) : MvPolynomial (ULift.{u} (Fin n)) (ULift.{u} ℤ) ≃+*
    Away (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X 0) :=
  ((MvPolynomial.renameEquiv (ULift.{u} ℤ) (Equiv.ulift (α := Fin n))).toRingEquiv).trans
    (awayChartEquiv n (ULift.{u} ℤ))

/-- **The standard affine chart of the integral model of projective space.** It is Mathlib's
chart `Spec (A_{X₀})₀ ⟶ Proj A` at the variable `X₀`, read through the identification of
`(A_{X₀})₀` with a polynomial ring. -/
def affineChartZ (n : ℕ) : Spec (CommRingCat.of
    (MvPolynomial (ULift.{u} (Fin n)) (ULift.{u} ℤ))) ⟶ ProjectiveSpaceZ.{u} n :=
  Spec.map (awayChartEquivZ.{u} n).symm.toCommRingCatIso.hom ≫
    Proj.awayι _ (X 0) (X_mem_homogeneousSubmodule n (ULift.{u} ℤ) 0) Nat.one_pos

/-- The integral affine chart `affineChartZ` is an open immersion. -/
instance isOpenImmersion_affineChartZ : IsOpenImmersion (affineChartZ.{u} n) := by
  have hf : IsOpenImmersion
      (Spec.map (awayChartEquivZ.{u} n).symm.toCommRingCatIso.hom) := inferInstance
  have hg : IsOpenImmersion (Proj.awayι (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (X 0) (X_mem_homogeneousSubmodule n (ULift.{u} ℤ) 0) Nat.one_pos) := inferInstance
  exact MorphismProperty.comp_mem _ _ _ hf hg

variable (S : Scheme.{u})

/-- **The standard affine chart of projective space.** Affine `n`-space over `S` is the open
subscheme of projective `n`-space over `S` where the first coordinate is invertible; this is the
base change of `affineChartZ` along `S ⟶ Spec ℤ`. -/
def affineChart : AffineSpace (ULift.{u} (Fin n)) S ⟶ ProjectiveSpace n S :=
  pullback.lift (AffineSpace (ULift.{u} (Fin n)) S ↘ S)
    (AffineSpace.toSpecMvPoly (ULift.{u} (Fin n)) S ≫ affineChartZ.{u} n)
    (terminal.hom_ext _ _)

/-- The chart is a morphism over `S`. -/
@[reassoc (attr := simp)]
theorem affineChart_over : affineChart n S ≫ (ProjectiveSpace n S ↘ S) =
    AffineSpace (ULift.{u} (Fin n)) S ↘ S :=
  pullback.lift_fst _ _ _

/-- The chart is compatible with the projections to the integral models. -/
theorem toSpecMvPoly_affineChartZ :
    AffineSpace.toSpecMvPoly (ULift.{u} (Fin n)) S ≫ affineChartZ.{u} n =
      affineChart n S ≫ toProjectiveSpaceZ n S :=
  (pullback.lift_snd _ _ _).symm

/-- **The chart over `S` is the base change of the integral chart.** Both `𝔸ⁿ_S` and `ℙⁿ_S` are
pullbacks of their integral models along `S ⟶ Spec ℤ`, so the square comparing them over the
integral models is cartesian. -/
theorem isPullback_affineChart :
    IsPullback (AffineSpace.toSpecMvPoly (ULift.{u} (Fin n)) S) (affineChart n S)
      (affineChartZ.{u} n) (toProjectiveSpaceZ n S) := by
  have t : IsPullback (toProjectiveSpaceZ n S) (ProjectiveSpace n S ↘ S)
      (terminal.from (ProjectiveSpaceZ.{u} n)) (terminal.from S) :=
    (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_bot ?_ (toSpecMvPoly_affineChartZ n S) t
  rw [affineChart_over, terminal.comp_from]
  exact (IsPullback.of_hasPullback _ _).flip

/-- The affine chart `affineChart` is an open immersion. -/
instance isOpenImmersion_affineChart : IsOpenImmersion (affineChart n S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_affineChart n S) inferInstance

end ProjectiveSpace

/-- **Chow's lemma for an affine scheme of finite type over an affine base.** Such a scheme
immerses into a projective space over the base, so it is its own Chow modification.

A morphism of affine schemes locally of finite type factors through a closed immersion into an
affine space over the target, and the standard affine chart embeds that affine space as an open
subscheme of a projective space over the target; a closed immersion followed by an open immersion
is an immersion. -/
theorem HasChowModification.of_isAffine {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [LocallyOfFiniteType f] : HasChowModification f := by
  obtain ⟨m, i, hi, hcomm⟩ := exists_isClosedImmersion_affineSpace f
  have : IsClosedImmersion i := hi
  refine HasChowModification.of_isImmersion (i ≫ ProjectiveSpace.affineChart m S) ?_
  rw [Category.assoc, ProjectiveSpace.affineChart_over]
  exact hcomm

end AlgebraicGeometry

end

end
