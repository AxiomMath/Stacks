module

public import StacksFrontier.AlgebraicGeometry.CurveAffineOrHProjective.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The affine line is a curve, and it is affine and not H-projective

The statements of [Stacks, Tag 0A27] and of its proof steps are all quantified over curves, so
they say nothing at all unless a curve exists. This file exhibits one — the affine line
`Spec k[T]` over a field — and uses it to show that the two alternatives of the tag are both
live: `Spec k[T]` is a curve which *is* affine and which admits *no* closed immersion into
relative projective space over `k`. Together with
`AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOver_self` this exhibits data for each
side of the tag's disjunction separately, so neither side is forced by the hypotheses.

It also shows that the hypotheses of
`AlgebraicGeometry.isAffine_of_isOpenImmersion_of_isAffineOpen_compl_singleton` — the step
[Stacks, Tag 0A27] takes with [Stacks, Tag 09N9] — are jointly satisfiable, by the complement of
the two points `T = 0` and `T = 1` inside the complement of the origin.

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_specPolynomial` and
  `AlgebraicGeometry.topologicalKrullDim_specPolynomial`: the two conditions of the curve
  hypothesis that are not automatic for the affine line.
* `AlgebraicGeometry.isCurve_specPolynomial`: the affine line over a field is a curve.
* `AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOver_self`: relative projective
  space is H-projective over its base, by the identity.
* `AlgebraicGeometry.not_exists_isClosedImmersion_projectiveSpaceOver_specPolynomial`: the affine
  line is not H-projective over its ground field.
* `AlgebraicGeometry.originPolynomial`, `AlgebraicGeometry.zeroLocus_X_eq_singleton` and
  `AlgebraicGeometry.basicOpen_X_eq_compl_singleton`: the complement of the origin of the affine
  line is the basic open of the coordinate.
* `AlgebraicGeometry.isAffine_toScheme_of_notMem_originPolynomial` and
  `AlgebraicGeometry.exists_isAffine_compl_originPolynomial`: the hypotheses of
  `isAffine_of_isOpenImmersion_of_isAffineOpen_compl_singleton` have a model in which the open
  immersion is not an isomorphism.

## Implementation notes

**No new name for the affine line.** `AlgebraicGeometry.affineLine` already exists in this
repository and is the affine line over `ℤ`, so the scheme here is written out as
`Spec (CommRingCat.of (Polynomial k))` — the spelling
`StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine` already uses — rather than given a
second name that would have to be identified with the first.

**No `@[stacks]` attribute.** Nothing here is a Stacks tag; these are the satisfiability controls
for the statements of `CurveAffineOrHProjective.Basic`.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-! ### The affine line over a field is a curve -/

/-- **The structure morphism of the affine line over a field is locally of finite type.** The
polynomial ring in one variable is an algebra of finite type over the field, and
`AlgebraicGeometry.LocallyOfFiniteType` is the ring-hom property `RingHom.FiniteType` read on
`Spec`. -/
public theorem locallyOfFiniteType_specPolynomial :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- **The affine line over a field has dimension one.** The topological Krull dimension of the
spectrum of a ring is the ring's Krull dimension, and `dim k[T] = dim k + 1 = 1`. -/
public theorem topologicalKrullDim_specPolynomial :
    topologicalKrullDim (Spec (CommRingCat.of (Polynomial k))) = 1 := by
  change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  rfl

/-- **The affine line over a field is a curve.** It is integral because the polynomial ring is a
domain, its structure morphism is separated and quasi-compact because it is a morphism of affine
schemes, it is locally of finite type by `locallyOfFiniteType_specPolynomial`, and it has
dimension one by `topologicalKrullDim_specPolynomial`.

This is the first inhabitant of `AlgebraicGeometry.IsCurve` ([Stacks, Tag 0A23]) in this
repository, and so the first evidence that any statement quantified over curves says anything. -/
public theorem isCurve_specPolynomial :
    IsCurve k (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) := by
  have := locallyOfFiniteType_specPolynomial k
  refine (isCurve_iff k _).mpr ⟨⟨⟩, ?_⟩
  exact topologicalKrullDim_specPolynomial k

/-! ### Each side of the disjunction of Tag 0A27 is realised -/

/-- **Relative projective space is H-projective over its base**, by the identity closed
immersion. This is the cheapest witness that the right-hand alternative of [Stacks, Tag 0A27] is
satisfiable at all: the existential it asserts is not empty. -/
public theorem exists_isClosedImmersion_projectiveSpaceOver_self (n : ℕ) (S : Scheme.{u}) :
    ∃ (m : ℕ) (i : projectiveSpaceOver n S ⟶ projectiveSpaceOver m S),
      IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver m S ↘ S)
        = (projectiveSpaceOver n S ↘ S) :=
  ⟨n, 𝟙 _, inferInstance, by simp⟩

/-- **The affine line over a field is not H-projective over that field.** It is a curve and it is
affine, and a curve cannot be both
(`AlgebraicGeometry.not_isAffine_of_isCurve_of_isClosedImmersion_projectiveSpaceOver`, the remark
preceding [Stacks, Tag 0A27]).

So the left-hand alternative of [Stacks, Tag 0A27] holds here and the right-hand one fails:
the disjunction is not secretly forced to its projective side. -/
public theorem not_exists_isClosedImmersion_projectiveSpaceOver_specPolynomial :
    ¬ ∃ (n : ℕ) (i : Spec (CommRingCat.of (Polynomial k)) ⟶
          projectiveSpaceOver n (Spec (CommRingCat.of k))),
        IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
          Spec (CommRingCat.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) :=
  fun ⟨_, i, hi, h⟩ =>
    have := isCurve_specPolynomial k
    have := hi
    not_isAffine_of_isCurve_of_isClosedImmersion_projectiveSpaceOver k i h inferInstance

/-! ### The hypotheses of the `09N9` step are jointly satisfiable -/

/-- **The origin of the affine line.** The prime ideal generated by the coordinate; it is maximal
because the coordinate is irreducible and the polynomial ring over a field is a principal ideal
ring. -/
public noncomputable def originPolynomial : PrimeSpectrum (Polynomial k) :=
  ⟨Ideal.span {(Polynomial.X : Polynomial k)},
    (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X).isPrime⟩

/-- **The vanishing locus of the coordinate on the affine line is the origin alone.** A prime
containing `T` contains the maximal ideal `(T)` and is not the whole ring, so it *is* `(T)`. -/
public theorem zeroLocus_X_eq_singleton :
    PrimeSpectrum.zeroLocus {(Polynomial.X : Polynomial k)} = {originPolynomial k} := by
  have hmax : (Ideal.span {(Polynomial.X : Polynomial k)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, fun p hp => ?_⟩
  · refine (PrimeSpectrum.mem_zeroLocus _ _).mpr ?_
    change ({(Polynomial.X : Polynomial k)} : Set (Polynomial k))
      ⊆ (Ideal.span {(Polynomial.X : Polynomial k)} : Ideal (Polynomial k))
    exact Ideal.subset_span
  · exact PrimeSpectrum.ext (hmax.eq_of_le p.isPrime.ne_top
      ((Ideal.span_le).mpr ((PrimeSpectrum.mem_zeroLocus _ _).mp hp))).symm

/-- **The basic open of the coordinate on the affine line is the complement of the origin.** -/
public theorem basicOpen_X_eq_compl_singleton :
    (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) :
        Set (PrimeSpectrum (Polynomial k)))
      = ({originPolynomial k} : Set (PrimeSpectrum (Polynomial k)))ᶜ := by
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  exact congrArg (·ᶜ) (zeroLocus_X_eq_singleton k)

/-- **The hypotheses of `isAffine_of_isOpenImmersion_of_isAffineOpen_compl_singleton` are jointly
satisfiable, and its conclusion holds there.** Take the curve to be the affine line, the point to
be the origin, the affine open complement to be the basic open of the coordinate — which is
`Spec k[T, T⁻¹]` — and the open immersion to be its inclusion. Every hypothesis of that theorem
holds and the open subscheme is indeed affine, as the theorem then concludes.

So that step is not vacuous: its hypothesis set has a model, exhibited here rather than argued
for. The affineness in the conclusion is obtained *through* that theorem, not from the basic open
being affine, which is what makes this a real test of it. -/
public theorem isAffine_toScheme_of_notMem_originPolynomial
    (V : (Spec (CommRingCat.of (Polynomial k))).Opens) (hV : originPolynomial k ∉ V)
    (U : (Spec (CommRingCat.of (Polynomial k))).Opens)
    (hU : (U : Set (Spec (CommRingCat.of (Polynomial k))))
      = ({originPolynomial k} : Set (PrimeSpectrum (Polynomial k)))ᶜ)
    (hUaff : IsAffineOpen U) : IsAffine V.toScheme := by
  have := isCurve_specPolynomial k
  have : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  refine isAffine_of_isOpenImmersion_of_isAffineOpen_compl_singleton k
    (g := Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) V.ι
    (x := originPolynomial k) ?_ hU hUaff
  rw [Scheme.Opens.range_ι]
  exact hV

/-- **The hypotheses of `isAffine_of_isOpenImmersion_of_isAffineOpen_compl_singleton` have a
model, non-degenerately.** Take `U` to be the complement of the origin of the affine line — the
basic open of the coordinate, which is `Spec k[T, T⁻¹]` — and `V` to be the complement of the two
points `T = 0` and `T = 1`. Then `V` is a strictly smaller open of `U` missing the origin, and
the theorem concludes that `V` is affine.

Compactness of `V` comes from the spectrum of a Noetherian ring being a Noetherian space, *not*
from `V` being a basic open and hence affine, so the affineness in the conclusion is genuinely
produced by the theorem rather than assumed. -/
public theorem exists_isAffine_compl_originPolynomial :
    ∃ U V : (Spec (CommRingCat.of (Polynomial k))).Opens,
      (U : Set (Spec (CommRingCat.of (Polynomial k))))
          = ({originPolynomial k} : Set (PrimeSpectrum (Polynomial k)))ᶜ ∧
        IsAffineOpen U ∧ V < U ∧ originPolynomial k ∉ V ∧ IsAffine V.toScheme := by
  -- the point `T = 1` lies in `U` and not in `V`, so the inclusion is strict
  have hone : ((Polynomial.X : Polynomial k) - 1) ∣ ((Polynomial.X : Polynomial k)) → False := by
    intro hdvd
    refine (Polynomial.irreducible_X_sub_C (1 : k)).not_isUnit (isUnit_of_dvd_one ?_)
    have : ((Polynomial.X : Polynomial k) - 1) ∣
        ((Polynomial.X : Polynomial k) - ((Polynomial.X : Polynomial k) - 1)) :=
      dvd_sub hdvd dvd_rfl
    simpa [Polynomial.C_1] using this
  have hprime : (Ideal.span {(Polynomial.X : Polynomial k) - 1}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible
      (by simpa [Polynomial.C_1] using Polynomial.irreducible_X_sub_C (1 : k))).isPrime
  have hnot : originPolynomial k ∉
      (PrimeSpectrum.basicOpen ((Polynomial.X : Polynomial k) * (Polynomial.X - 1)) :
        (Spec (CommRingCat.of (Polynomial k))).Opens) := by
    rw [PrimeSpectrum.mem_basicOpen]
    exact not_not.mpr (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  refine ⟨PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k),
    PrimeSpectrum.basicOpen ((Polynomial.X : Polynomial k) * (Polynomial.X - 1)),
    basicOpen_X_eq_compl_singleton k, IsAffineOpen.Spec_basicOpen _, ?_, hnot,
    isAffine_toScheme_of_notMem_originPolynomial k _ hnot _
      (basicOpen_X_eq_compl_singleton k) (IsAffineOpen.Spec_basicOpen _)⟩
  refine lt_of_le_of_ne (by rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_left) fun heq => ?_
  have hmem : (⟨Ideal.span {(Polynomial.X : Polynomial k) - 1}, hprime⟩ :
      PrimeSpectrum (Polynomial k)) ∈
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) := by
    rw [PrimeSpectrum.mem_basicOpen]
    exact fun hx => hone (Ideal.mem_span_singleton.mp hx)
  rw [← heq, PrimeSpectrum.mem_basicOpen] at hmem
  exact hmem (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

end AlgebraicGeometry

end
