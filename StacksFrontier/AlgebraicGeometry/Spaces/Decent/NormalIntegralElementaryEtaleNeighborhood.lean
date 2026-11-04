module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalIntegralEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor

/-!
# Normal integral elementary étale neighborhoods

Every point of a normal integral algebraic space over a scheme `S` has an elementary étale
neighborhood — Stacks 0BGU — whose scheme is a *normal integral affine* scheme.

Stacks 0BBP supplies an elementary étale neighborhood with affine scheme at every point of a
decent algebraic space, and an integral algebraic space is decent. That neighborhood is an
affine étale chart of `X`, so the shrinking step of Stacks 0AYH,
`AlgebraicGeometry.Space.exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart`, cuts
out of it a normal integral affine open around its distinguished point; and a pointed open
subscheme of an elementary étale neighborhood is again one, by
`AlgebraicGeometry.Space.openRestrictionNeighborhood`, since the morphism from the spectrum of
the residue field at the distinguished point into `X` is literally unchanged by the shrinking.

At the generic point of a prime divisor of such an `X`, locally Noetherian as well, the
resulting neighborhood meets every geometric hypothesis of the order comparison of Stacks
0ENM, `AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing`: the
codimension-one condition on the marked point is the codimension-one condition on the generic
point of the prime divisor, by Stacks 0ED1 and Stacks 02IZ.

## Main results

* `AlgebraicGeometry.Space.exists_isAffine_isNormal_isIntegral_elementaryEtaleNeighborhood`:
  an elementary étale neighborhood with normal integral affine scheme at every point.
* `AlgebraicGeometry.Space.PrimeDivisor.localRingDimension_genericPoint` and
  `AlgebraicGeometry.Space.coheight_eq_one_of_chartPoint_genericPoint`: the generic point of a
  prime divisor has a one-dimensional local ring, and a point of an étale chart above it has
  coheight one — the converse of
  `AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_of_coheight_chartPoint_eq_one`.
* `AlgebraicGeometry.Space.exists_isNormal_isIntegral_coheight_eq_one_elementaryEtaleNeighborhood`:
  the two combined, which is the chart the order comparison of Stacks 0ENM asks for.

## Implementation notes

The hypothesis that the residue field at the distinguished point be the residue field of the
space is *not* available for a prescribed chart: it is a condition on the chart, not something
a shrinking can arrange, as shrinking does not change the residue field at the marked point.
This is why the neighborhood here is produced from Stacks 0BBP's and then shrunk, rather than
from a chart chosen for its normality and integrality and then upgraded. For the same reason
there is no such neighborhood at *all* the codimension-one points of one chart at once, which
is what the proof of Stacks 0EPX would want of a chart trivializing an invertible module.

## References

* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 0AYH](https://stacks.math.columbia.edu/tag/0AYH)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0ED1](https://stacks.math.columbia.edu/tag/0ED1)
* [Stacks Project, Tag 0ENJ](https://stacks.math.columbia.edu/tag/0ENJ)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A normal integral affine elementary étale neighborhood.** Let `X` be a normal integral
algebraic space over `S`. Every point of `|X|` has an elementary étale neighborhood whose
scheme is a normal integral affine scheme.

An affine elementary étale neighborhood exists by Stacks 0BBP, and the shrinking step of
Stacks 0AYH cuts a normal integral affine open out of it around its distinguished point; a
pointed open subscheme of an elementary étale neighborhood is again an elementary étale
neighborhood of the same point. -/
theorem exists_isAffine_isNormal_isIntegral_elementaryEtaleNeighborhood
    (hX : IsAlgebraicSpace B S hS X)
    (hnormal : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsNormal Y))
    (hintegral : IsIntegralSpace B S hS X) (x : points B S hS X) :
    ∃ E : ElementaryEtaleNeighborhood B S hS X hX x,
      IsAffine E.scheme.left.1 ∧ IsNormal E.scheme.left.1 ∧ IsIntegral E.scheme.left.1 := by
  have hdec : IsDecentSpace B S hS X := IsIntegralSpace.isDecentSpace B S hS X hintegral
  obtain ⟨E, hEaff, -, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hX hdec x
  obtain ⟨W, hW, hWaff, hWnormal, hWintegral⟩ :=
    exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart B S hS hX hnormal hintegral
      E.scheme hEaff E.toSpace
      ((isEtale_iff_presheaf_of_yoneda B S hS E.toSpace).1 E.etale_toSpace) E.point
  exact ⟨openRestrictionNeighborhood B S hS X hX x E W hW, hWaff, hWnormal, hWintegral⟩

/-! ### At the generic point of a prime divisor -/

/-- **The local ring of `|X|` at the generic point of a prime divisor has dimension one.** The
closure of that point has codimension one in `|X|` by the definition of a prime divisor, and on
a decent algebraic space the codimension of an irreducible closed subset is the dimension of
the local ring at its generic point, which is Stacks 0ED1. -/
theorem PrimeDivisor.localRingDimension_genericPoint (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X) :
    localRingDimension B S hS (Z.genericPoint B S hS X) = 1 :=
  (codimension_eq_localRingDimension B S hS hX hdec _ (Z.genericPoint B S hS X)
      (IrreducibleCloseds.coe_closureSingleton (Z.genericPoint B S hS X)).symm).symm.trans
    (Z.codimension_genericPoint B S hS X)

/-- **A point of an étale chart above the generic point of a prime divisor has coheight one.**
This is the converse of
`AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_of_coheight_chartPoint_eq_one`,
and it is the form in which the codimension hypothesis of Stacks 0ENM —
`AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing` — is met: the
dimension of the local ring of `|X|` at the generic point of the prime divisor is one, and that
dimension is the Krull dimension of the local ring of any étale chart at any point above it,
which is the coheight by Stacks 02IZ. -/
theorem coheight_eq_one_of_chartPoint_genericPoint (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (u : (BigFppfOver.toScheme B S hS).obj U)
    (hu : ChartPoint B S hS U a u (Z.genericPoint B S hS X)) :
    Order.coheight u = 1 := by
  have h := localRingDimension_eq_of_chartPoint B S hS hX U a ha u _ hu
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight u,
    PrimeDivisor.localRingDimension_genericPoint B S hS hX hdec Z] at h
  exact_mod_cast h.symm

/-- **The chart the order comparison of Stacks 0ENM asks for, at the generic point of a prime
divisor.** Let `X` be a normal, integral, locally Noetherian algebraic space over `S`. The
generic point of a prime divisor of `X` has an elementary étale neighborhood whose scheme is a
normal integral affine locally Noetherian scheme and whose distinguished point has coheight one.

These are exactly the geometric hypotheses of
`AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing`, so the order of
vanishing along the prime divisor of a rational function of such a chart is the order of
vanishing of that function at the distinguished point of the chart.

Note what is *not* claimed: that a single chart is an elementary étale neighborhood of the
generic points of *all* the prime divisors meeting it. It cannot be arranged — the residue
field at the distinguished point of an elementary étale neighborhood is the residue field of
the space at the point below it, by
`AlgebraicGeometry.Space.exists_affine_elementaryEtaleNeighborhood'`, and an étale chart has a
nontrivial finite separable residue extension at a point in general — and it is what the proof
of Stacks 0EPX would need from a single trivializing chart. -/
theorem exists_isNormal_isIntegral_coheight_eq_one_elementaryEtaleNeighborhood
    (hX : IsAlgebraicSpace B S hS X)
    (hnormal : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsNormal Y))
    (hnoeth : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hintegral : IsIntegralSpace B S hS X) (Z : PrimeDivisor B S hS X) :
    ∃ E : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X),
      IsAffine E.scheme.left.1 ∧ IsNormal E.scheme.left.1 ∧ IsIntegral E.scheme.left.1 ∧
        IsLocallyNoetherian E.scheme.left.1 ∧ Order.coheight E.point = 1 := by
  have hdec : IsDecentSpace B S hS X := IsIntegralSpace.isDecentSpace B S hS X hintegral
  obtain ⟨E, hEaff, hEnormal, hEintegral⟩ :=
    exists_isAffine_isNormal_isIntegral_elementaryEtaleNeighborhood B S hS hX hnormal hintegral
      (Z.genericPoint B S hS X)
  have hEetale := (isEtale_iff_presheaf_of_yoneda B S hS E.toSpace).1 E.etale_toSpace
  refine ⟨E, hEaff, hEnormal, hEintegral,
    (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y) hX).mp
      hnoeth E.scheme E.toSpace hEetale, ?_⟩
  refine coheight_eq_one_of_chartPoint_genericPoint B S hS hX hdec Z E.scheme E.toSpace hEetale
    E.point ?_
  have hchart := chartPoint_pointsToScheme B S hS E.scheme E.toSpace
    (presheafPoint B S hS E.scheme E.point E.residueField_contained)
  rwa [pointsToScheme_presheafPoint B S hS E.scheme E.point E.residueField_contained,
    E.map_point] at hchart

end AlgebraicGeometry.Space

end
