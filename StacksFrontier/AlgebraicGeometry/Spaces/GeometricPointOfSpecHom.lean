module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange

/-!
# Geometric points of a representable algebraic space from morphisms of schemes

A geometric point of the algebraic space represented by an object `U` of the big fppf site is
nothing but a morphism of schemes `Spec Ω ⟶ U` over `S`, for an algebraically closed field `Ω`
whose spectrum the site contains: the section of `yoneda.obj U` it needs *is* that morphism.
The point of the identity chart it lies over is the image of the closed point of `Spec Ω`.

## Main definitions

* `AlgebraicGeometry.Space.geometricPointOfSpecHom` is the geometric point of `yoneda.obj U`
  attached to a morphism `Spec Ω ⟶ U` of schemes.

## Main results

* `AlgebraicGeometry.Space.toScheme_map_geometricPointOfSpecHom_value`: the morphism of schemes
  underlying the section of the geometric point is the given one.
* `AlgebraicGeometry.Space.chartPoint_geometricPointOfSpecHom`: the point of the identity chart
  carried by the geometric point is the image of the closed point of `Spec Ω`.
* `AlgebraicGeometry.Space.geometricPointMap_geometricPointOfSpecHom`: the image of the
  geometric point under a morphism of the site is the geometric point of the composite.

## Implementation notes

The structure morphism to the base is a parameter, with the factorisation of `σ` through it as
a hypothesis, rather than the composite `Spec Ω ⟶ U ⟶ S`, so that all three results hold by
`rfl`. Defining it as the composite would leave the image of a geometric point and the geometric
point of the composite differing by `CategoryTheory.Over.w g`, in the type of the section.

## References

* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For an object `U` of the big fppf site over `S`, an algebraically closed field `Ω` whose
spectrum the site contains, a morphism `tb : Spec Ω ⟶ S` and a morphism of schemes
`σ : Spec Ω ⟶ U` over `tb`, the geometric point of `yoneda.obj U` whose field is `Ω`, whose
structure morphism to `S` is `tb` and whose section is `σ`. -/
@[stacks 0486 "part (1): a geometric point of a representable algebraic space"]
def geometricPointOfSpecHom (U : BigFppfOver B S hS) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (hΩ : B.Contains (Spec (.of Ω))) (tb : Spec (.of Ω) ⟶ S)
    (σ : Spec (.of Ω) ⟶ (BigFppfOver.toScheme B S hS).obj U)
    (hσ : σ ≫ B.inclusion.map U.hom = tb) :
    GeometricPoint B S hS (yoneda.obj U) :=
  ⟨{ carrier := Ω
     contained := hΩ
     toBase := tb
     value := Over.homMk (ObjectProperty.homMk σ) (ObjectProperty.hom_ext _ hσ) }, inferInstance⟩

/-- The morphism of schemes underlying the section of
`AlgebraicGeometry.Space.geometricPointOfSpecHom` is the morphism it was built from. -/
theorem toScheme_map_geometricPointOfSpecHom_value (U : BigFppfOver B S hS) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (hΩ : B.Contains (Spec (.of Ω))) (tb : Spec (.of Ω) ⟶ S)
    (σ : Spec (.of Ω) ⟶ (BigFppfOver.toScheme B S hS).obj U)
    (hσ : σ ≫ B.inclusion.map U.hom = tb) :
    (BigFppfOver.toScheme B S hS).map
        (geometricPointOfSpecHom B S hS U hΩ tb σ hσ).val.value = σ :=
  rfl

/-- The point of the identity chart carried by
`AlgebraicGeometry.Space.geometricPointOfSpecHom` is the image of the closed point of
`Spec Ω`. -/
theorem chartPoint_geometricPointOfSpecHom (U : BigFppfOver B S hS) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (hΩ : B.Contains (Spec (.of Ω))) (tb : Spec (.of Ω) ⟶ S)
    (σ : Spec (.of Ω) ⟶ (BigFppfOver.toScheme B S hS).obj U)
    (hσ : σ ≫ B.inclusion.map U.hom = tb) :
    chartPoint B S hS (yoneda.obj U)
        (yonedaIdentityNeighborhood U (geometricPointOfSpecHom B S hS U hΩ tb σ hσ)) =
      σ.base (closedPoint Ω) :=
  rfl

/-- The image of
`AlgebraicGeometry.Space.geometricPointOfSpecHom` of `σ` under `yoneda.map g` is the geometric
point of the composite `σ ≫ g`, with the same structure morphism to the base. -/
theorem geometricPointMap_geometricPointOfSpecHom {U W : BigFppfOver B S hS} (g : U ⟶ W)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (hΩ : B.Contains (Spec (.of Ω)))
    (tb : Spec (.of Ω) ⟶ S)
    (σ : Spec (.of Ω) ⟶ (BigFppfOver.toScheme B S hS).obj U)
    (hσ : σ ≫ B.inclusion.map U.hom = tb)
    (hσ' : (σ ≫ (BigFppfOver.toScheme B S hS).map g) ≫ B.inclusion.map W.hom = tb) :
    geometricPointMap (yoneda.map g) (geometricPointOfSpecHom B S hS U hΩ tb σ hσ) =
      geometricPointOfSpecHom B S hS W hΩ tb
        (σ ≫ (BigFppfOver.toScheme B S hS).map g) hσ' :=
  rfl

end AlgebraicGeometry.Space

end
