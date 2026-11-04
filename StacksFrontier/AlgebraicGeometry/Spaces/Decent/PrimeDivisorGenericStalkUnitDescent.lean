module

public import StacksFrontier.AlgebraicGeometry.FlatChartFractionUnitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGeneratorRatio

/-!
# The coefficient at the generic point is a unit as soon as it is one on a chart

Let `X` be a locally Noetherian integral algebraic space over a scheme `S`, let `ℒ` be an
invertible `𝒪_X`-module and let `Z ⊂ X` be a prime divisor with generic point `ξ`. The
coefficient of Stacks 0EPR of a meromorphic section of `ℒ` lives in the meromorphic functions
over the chart `Spec(𝒪_{U, u})`. This file shows that it is the image of a *unit* of `𝒪_{U, u}`
as soon as its restriction to a chart `W` of `Spec(𝒪_{U, u})` is the image of a unit of `𝒪_W`.

The descent is `AlgebraicGeometry.exists_isUnit_eq_appTop_of_isUnit_of_flat`, run on the
morphism of schemes underlying the chart: `𝒪_{U, u}` is a local ring, a chart of its spectrum
is flat over it, and a point of the chart over the closed point makes the map to the local ring
there faithfully flat. The ring of meromorphic functions over each of the two charts is the
total ring of fractions of its regular functions by Stacks 0EN6, part (2), which on
`Spec(𝒪_{U, u})` is
`AlgebraicGeometry.Space.PrimeDivisor.isFractionRing_genericStalkMeromorphic` and on `W` is
`AlgebraicGeometry.Space.isFractionRing_meromorphicFunctionSheaf_obj` at the two hypotheses of
Stacks 0EN6 that `Spec(𝒪_{U, u})` satisfies.

## Main definitions

* `PrimeDivisor.genericStalkChartMap` is the morphism of schemes `W ⟶ Spec(𝒪_{U, u})` underlying a
  chart `W` of `Spec(𝒪_{U, u})`.

## Main results

* `PrimeDivisor.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_chart`: the coefficient of
  Stacks 0EPR is the image of a unit of `𝒪_{U, u}` as soon as its restriction to an affine chart
  `W` of `Spec(𝒪_{U, u})` carrying a point over the closed point is the image of a unit of `𝒪_W`.
* `PrimeDivisor.etale_genericStalkChartMap` and `PrimeDivisor.flat_genericStalkChartMap`: that
  morphism of schemes is étale, hence flat.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

/-- **The morphism of schemes underlying a chart of `Spec(𝒪_{U, u})`.** The chart
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkChart` is the identity chart of the algebraic
space represented by `Spec(𝒪_{U, u})`, so the scheme underlying it is `Spec(𝒪_{U, u})` itself
and a morphism of charts into it is a morphism of schemes to `Spec(𝒪_{U, u})`. -/
def PrimeDivisor.genericStalkChartMap
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec) :
    smallEtaleScheme B S hS (Z.genericStalkSpace B S hS hX hdec).1 W ⟶
      Spec (Z.genericStalkRing B S hS hX hdec) :=
  (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1 ⋙
    BigFppfOver.toScheme B S hS).map k

/-- The restriction of regular functions along a chart of `Spec(𝒪_{U, u})` is the comparison on
global sections of the underlying morphism of schemes: the structure presheaf of the small étale
site is global sections of the underlying scheme by definition. -/
theorem PrimeDivisor.structurePresheaf_map_eq_appTop
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec) :
    (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).map k.op =
      (Z.genericStalkChartMap B S hS hX hdec W k).appTop :=
  rfl

/-- **The morphism of schemes underlying a chart of `Spec(𝒪_{U, u})` is étale.** The chart
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkChart` is the *identity* chart of the algebraic
space represented by `Spec(𝒪_{U, u})`, so the structural morphism of a chart over it is the
morphism of charts itself, and an étale chart has an étale underlying morphism of schemes. -/
theorem PrimeDivisor.etale_genericStalkChartMap
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec) :
    AlgebraicGeometry.Etale (Z.genericStalkChartMap B S hS hX hdec W k) := by
  have hetale (C : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1) :
      IsEtale B S hS C.obj.hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS C.obj.hom).2 C.property
  have hke : IsEtale B S hS (yoneda.map ((SmallEtale.toOver B S hS
      (Z.genericStalkSpace B S hS hX hdec).1).map k)) :=
    isEtale_of_isEtale_over B S hS
      (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS
        (Z.genericStalkSpace B S hS hX hdec).1).obj W))
      (isAlgebraicSpace_yoneda B S hS (Z.genericStalkSpec B S hS hX hdec))
      (Z.genericStalkSpace B S hS hX hdec).2 _ W.obj.hom
      (Z.genericStalkChart B S hS hX hdec).obj.hom (hetale W) (hetale _)
      (CostructuredArrow.w ((SmallEtale.inclusion B S hS
        (Z.genericStalkSpace B S hS hX hdec).1).map k))
  exact (presheaf_yoneda_map_etale_iff B S hS ((SmallEtale.toOver B S hS
    (Z.genericStalkSpace B S hS hX hdec).1).map k)).1
      ((isEtale_iff_presheaf_of_yoneda B S hS _).1 hke)

/-- **The morphism of schemes underlying a chart of `Spec(𝒪_{U, u})` is flat**, being étale. -/
theorem PrimeDivisor.flat_genericStalkChartMap
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec) :
    AlgebraicGeometry.Flat (Z.genericStalkChartMap B S hS hX hdec W k) :=
  have := Z.etale_genericStalkChartMap B S hS hX hdec W k
  inferInstance

variable (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN in
/-- **The coefficient of Stacks 0EPR is a unit as soon as it is a unit on a chart.** If the
restriction of the coefficient of a meromorphic section `t` of `ℒ` against the generator chosen
at `ξ` to an *affine* chart `W` of `Spec(𝒪_{U, u})` carrying a point over the closed point is
the image of a unit regular function on `W`, then the coefficient itself is the image of a unit
of `𝒪_{U, u}`. -/
theorem PrimeDivisor.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_chart
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec)
    (hWaff : IsAffine (smallEtaleScheme B S hS (Z.genericStalkSpace B S hS hX hdec).1 W))
    (w : smallEtaleScheme B S hS (Z.genericStalkSpace B S hS hX hdec).1 W)
    (hw : (Z.genericStalkChartMap B S hS hX hdec W k).base w =
      IsLocalRing.closedPoint (Z.genericStalkRing B S hS hX hdec))
    (v : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj (op W))
    (hv : IsUnit v)
    (hres : ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.map k.op).hom
        (Z.genericStalkCoefficient B S hS hX hdec L hL t) =
      ((toMeromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).hom.app (op W)).hom v) :
    ∃ a : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec)), IsUnit a ∧
      Z.genericStalkCoefficient B S hS hX hdec L hL t =
        algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
            (op (Z.genericStalkChart B S hS hX hdec)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec))) a := by
  have := Z.flat_genericStalkChartMap B S hS hX hdec W k
  refine AlgebraicGeometry.exists_isUnit_eq_appTop_of_isUnit_of_flat
    (Z.genericStalkRing B S hS hX hdec)
    (smallEtaleScheme B S hS (Z.genericStalkSpace B S hS hX hdec).1 W)
    (Z.genericStalkChartMap B S hS hX hdec W k) w hw
    (algK := Z.genericStalkMeromorphicAlgebra B S hS hX hdec)
    (fracK := Z.isFractionRing_genericStalkMeromorphic B S hS hX hdec hInt hN)
    (algKO := ((toMeromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).hom.app (op W)).hom.toAlgebra)
    (fracKO := isFractionRing_meromorphicFunctionSheaf_obj B S hS
      (Z.genericStalkSpace B S hS hX hdec)
      (Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_genericStalkSpace B S hS hX hdec
        hInt)
      (Z.hasLocallyFiniteIrreducibleComponents_genericStalkSpace B S hS hX hdec hN) W hWaff)
    (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.map k.op).hom) (fun a ↦ ?_) hv hres
  exact (ConcreteCategory.congr_hom ((toMeromorphicFunctionSheaf B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2).hom.naturality
      k.op) a).symm

end AlgebraicGeometry.Space

end
