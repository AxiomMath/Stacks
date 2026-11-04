module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding

/-!
# The two routes from the meromorphic functions on the chart into `Q(𝒪^h_{X, ξ})`

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S`, let `Z` be
a prime divisor of `X` with generic point `ξ` and let `(U, u)` be the chosen affine elementary
étale neighbourhood of `ξ`, with `A = Γ(U, 𝒪_U)`.

There are two ring homomorphisms from the meromorphic functions `𝒦_X(U)` on that chart into the
total ring of fractions `Q(𝒪^h_{X, ξ})` of the henselian local ring at `ξ`:

* pull a meromorphic function back to `Spec(𝒪_{U, u})` and push it into `Q(𝒪^h_{X, ξ})`, which
  is the route used by the canonical ratio of Stacks 0EPR; and
* read `𝒦_X(U)` as the total ring of fractions `Q(A)` of `A` by Stacks 0EN6, part (2), and push
  along `A → 𝒪_{U, u} → 𝒪^h_{X, ξ}`, which is the route used by the embedding
  `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK.

This file proves that **the two agree**. Both are ring homomorphisms out of the total ring of
fractions of `A`, and they agree on `A` itself, where both are
`AlgebraicGeometry.Space.PrimeDivisor.chartSectionsToGenericHenselianLocalRing` followed by the
structure map of `Q(𝒪^h_{X, ξ})`; the comparison is therefore the uniqueness of a map out of a
localization.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.genericStalkSectionsToHenselian_chartDiagramRestrict`:
  restricting a regular function on `U` to `Spec(𝒪_{U, u})` and mapping it into `𝒪^h_{X, ξ}` is
  taking its germ at `u` and mapping that into `𝒪^h_{X, ξ}`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericChartMeromorphicToGeneric` is the first route,
  as a single ring homomorphism, and
  `AlgebraicGeometry.Space.PrimeDivisor.genericChartMeromorphicToGeneric_algebraMap` says that it
  agrees with the second on the regular functions.
* `AlgebraicGeometry.Space.PrimeDivisor.genericChartMeromorphicToGeneric_eq_mk'`: **the two
  routes agree**, in the form that reads a meromorphic function on `U` as the fraction `p / q` of
  two regular functions.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- **Restricting a regular function on `U` to `Spec(𝒪_{U, u})` is taking its germ at `u`**, once
the global functions on `Spec(𝒪_{U, u})` are identified with `𝒪_{U, u}`.  Composed with the
canonical map of Stacks 0EMY this says that the two maps `A → 𝒪^h_{X, ξ}` of this file agree. -/
theorem PrimeDivisor.genericStalkSectionsToHenselian_chartDiagramRestrict
    (a : chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec)) :
    Z.genericStalkSectionsToHenselian B S hS hX hdec
        (chartDiagramRestrict B S hS (Z.genericStalkMorphism B S hS hX hdec)
          (Z.genericStalkChartDiagram B S hS hX hdec) a) =
      Z.chartSectionsToGenericHenselianLocalRing B S hS hX hdec a := by
  refine congrArg (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    (Z.genericChart B S hS hX hdec)) ?_
  change (Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).hom.hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (Z.genericStalkSpecToChart B S hS hX hdec)).op).hom a) = _
  rw [Scheme.Γ_map_op, Z.toScheme_map_genericStalkSpecToChart B S hS hX hdec,
    Scheme.fromSpecStalk_appTop]
  change (Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).hom.hom
      (((Spec (Z.genericStalkRing B S hS hX hdec)).presheaf.map
          (homOfLE le_top).op).hom
        ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).inv.hom
          ((((BigFppfOver.toScheme B S hS).obj
            (Z.genericChart B S hS hX hdec).scheme).presheaf.germ ⊤
              (Z.genericChart B S hS hX hdec).point trivial).hom a))) = _
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  exact (Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).inv_hom_id_apply _

include hInt hN in
/-- **The first route out of `𝒦_X(U)`**: pull a meromorphic function on the chart `U` back to
`Spec(𝒪_{U, u})` along the morphism `j` of Stacks 0ENK and push it into `Q(𝒪^h_{X, ξ})`, as a
single ring homomorphism.  This is the composite through which the canonical ratio of Stacks
0EPR sees a meromorphic function on `X`. -/
def PrimeDivisor.genericChartMeromorphicToGeneric :
    (meromorphicChartSheaf B S hS X hX).obj.obj (op (Z.genericEtaleChart B S hS hX hdec)) →+*
      Z.genericTotalFractionRing B S hS hX hdec :=
  (Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN).comp
    (chartMeromorphicRingedSitePullbackHom B S hS (Z.genericStalkMorphism B S hS hX hdec)
      (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
      (Z.genericStalkChartDiagram B S hS hX hdec))

include hInt hN in
/-- `AlgebraicGeometry.Space.PrimeDivisor.genericChartMeromorphicToGeneric` is the composite it
is defined to be, read on an element. -/
theorem PrimeDivisor.genericChartMeromorphicToGeneric_apply
    (m : (meromorphicChartSheaf B S hS X hX).obj.obj (op (Z.genericEtaleChart B S hS hX hdec))) :
    Z.genericChartMeromorphicToGeneric B S hS hX hdec hInt hN m =
      Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
        (chartMeromorphicRingedSitePullbackHom B S hS (Z.genericStalkMorphism B S hS hX hdec)
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
          (Z.genericStalkChartDiagram B S hS hX hdec) m) := rfl

include hInt hN in
/-- **The two routes out of `𝒦_X(U)` agree on the regular functions.**  Pulling a regular
function back to `Spec(𝒪_{U, u})` and pushing it into `Q(𝒪^h_{X, ξ})` is taking its germ at `u`,
mapping that into `𝒪^h_{X, ξ}` by Stacks 0EMY, and taking the structure map of the total ring of
fractions. -/
theorem PrimeDivisor.genericChartMeromorphicToGeneric_algebraMap
    (a : chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec)) :
    Z.genericChartMeromorphicToGeneric B S hS hX hdec hInt hN
        (algebraMap (chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec))
          ((meromorphicChartSheaf B S hS X hX).obj.obj
            (op (Z.genericEtaleChart B S hS hX hdec))) a) =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
        (Z.chartSectionsToGenericHenselianLocalRing B S hS hX hdec a) := by
  refine Eq.trans (congrArg (Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN)
    (RingHom.congr_fun (chartMeromorphicFunctionPullback_algebraMap B S hS
      (Z.genericStalkMorphism B S hS hX hdec)
      (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
      (Z.genericStalkChartDiagram B S hS hX hdec)) a)) ?_
  exact Eq.trans (Z.genericStalkMeromorphicToGeneric_algebraMap B S hS hX hdec hInt hN _)
    (congrArg (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec))
      (Z.genericStalkSectionsToHenselian_chartDiagramRestrict B S hS hX hdec a))

include hInt hN in
/-- **The two routes from `𝒦_X(U)` into `Q(𝒪^h_{X, ξ})` agree**, read on a meromorphic function
presented as a fraction `p / q` of regular functions on `U`: by Stacks 0EN6, part (2), every
meromorphic function on the affine chart `U` has such a presentation, with `q` a nonzerodivisor.

Both sides are determined by the common restriction of the two routes to the regular functions,
`AlgebraicGeometry.Space.PrimeDivisor.genericChartMeromorphicToGeneric_algebraMap`: the first
because a meromorphic function is a fraction, the second because the map on total rings of
fractions is the localization of that restriction. -/
theorem PrimeDivisor.genericChartMeromorphicToGeneric_eq_mk'
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (hCof : IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)))
    (m : (meromorphicChartSheaf B S hS X hX).obj.obj (op (Z.genericEtaleChart B S hS hX hdec)))
    (p : chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec))
    (q : (chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec))⁰)
    (hm : m * algebraMap (chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec))
          ((meromorphicChartSheaf B S hS X hX).obj.obj
            (op (Z.genericEtaleChart B S hS hX hdec)))
          (q : chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec)) =
      algebraMap (chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec))
        ((meromorphicChartSheaf B S hS X hX).obj.obj
          (op (Z.genericEtaleChart B S hS hX hdec))) p) :
    Z.genericChartMeromorphicToGeneric B S hS hX hdec hInt hN m =
      Z.chartTotalFractionRingToGeneric B S hS hX hdec hCof
        (IsLocalization.mk'
          (FractionRing (chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec))) p q) := by
  have hle := Z.nonZeroDivisors_le_comap_chartSectionsToGenericHenselianLocalRing B S hS hX hdec
    hCof
  have hmap : Z.chartTotalFractionRingToGeneric B S hS hX hdec hCof
      (IsLocalization.mk'
        (FractionRing (chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec))) p q) =
      IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
        (Z.chartSectionsToGenericHenselianLocalRing B S hS hX hdec p)
        ⟨Z.chartSectionsToGenericHenselianLocalRing B S hS hX hdec
          (q : chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec)), hle q.2⟩ :=
    IsLocalization.map_mk' hle p q
  have key : Z.genericChartMeromorphicToGeneric B S hS hX hdec hInt hN m *
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (Z.chartSectionsToGenericHenselianLocalRing B S hS hX hdec
            (q : chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec))) =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec)
        (Z.chartSectionsToGenericHenselianLocalRing B S hS hX hdec p) := by
    rw [← Z.genericChartMeromorphicToGeneric_algebraMap B S hS hX hdec hInt hN
        (q : chartRing B S hS X hX (Z.genericEtaleChart B S hS hX hdec)),
      ← Z.genericChartMeromorphicToGeneric_algebraMap B S hS hX hdec hInt hN p, ← map_mul, hm]
  rw [hmap, IsLocalization.eq_mk'_iff_mul_eq]
  exact key

end AlgebraicGeometry.Space

end
