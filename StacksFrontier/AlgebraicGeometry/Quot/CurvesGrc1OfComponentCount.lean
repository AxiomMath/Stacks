module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGeometricallyReducedConnectedOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGeometricallyReducedOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReducedLocus

/-!
# Condition (2)(b) of Stacks 0E1I with no input

`StacksFrontier.AlgebraicGeometry.Quot.CurvesGeometricallyReducedConnectedOverField` translates
condition (2)(b) of Stacks 0E1I for the family of curves of a proper flat morphism `X ⟶ Spec k`
of the site, given the translation of geometric reducedness of the fibres of a represented
morphism into geometric reducedness of the morphism of schemes. That translation is
`AlgebraicGeometry.Space.forall_isGeometricallyReducedFibreAt_yoneda_map_iff`; this file applies
it.

## Main results

* `AlgebraicGeometry.isGrc1CurveFamily_curveFamilyOfSchemeMorphism_iff_geometricallyReduced`:
  condition (2)(b) of Stacks 0E1I for the family of a proper flat morphism `X ⟶ Spec k` of the
  site, with no input.

## References

* [Stacks Project, Tag 0E1I](https://stacks.math.columbia.edu/tag/0E1I)
* [Stacks Project, Tag 0E0G](https://stacks.math.columbia.edu/tag/0E0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

section PartTwoTranslation

/-- **Condition (2)(b) of Stacks 0E1I.** Let `X` be a proper scheme of dimension at most one over
a field `k`, presented by a proper flat morphism `g : X ⟶ Spec k` of finite presentation of the
big fppf site of `Spec(ℤ)`. The family of curves of `g` has geometric fibres that are reduced,
connected and of dimension `1` exactly when `X` is geometrically reduced over `k`, geometrically
connected over `k`, and of dimension `1`. -/
theorem isGrc1CurveFamily_curveFamilyOfSchemeMorphism_iff_geometricallyReduced
    {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} {t : Spec (.of k) ⟶ integerBase}
    {T : BigFppfOver B integerBase hZ} (g : T ⟶ fieldSiteObject B hZ hk t)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    IsGrc1CurveFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      GeometricallyReduced ((BigFppfOver.toScheme B integerBase hZ).map g) ∧
        GeometricallyConnected
          ((BigFppfOver.toScheme B integerBase hZ).map g : _ ⟶ Spec (.of k)) ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 :=
  isGrc1CurveFamily_curveFamilyOfSchemeMorphism_iff
    (fun g => Space.forall_isGeometricallyReducedFibreAt_yoneda_map_iff B integerBase hZ g) g
    hflat hproper hlfp hqc hsep hqsep hdim

end PartTwoTranslation

end AlgebraicGeometry

end
