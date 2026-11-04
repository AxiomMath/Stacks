module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# Flatness over an affine scheme, read on the sections over one surjective affine chart

Let `R` be a ring with `Spec R` in the big fppf site, let `X` be an algebraic space over
`Spec R` and let `G` be a quasi-coherent `𝒪_X`-module.  If `U ⟶ X` is a surjective étale chart
whose underlying scheme is affine, then `G` is flat over `Spec R` in the sense of Stacks 05VV
as soon as the module of sections `G(U)` is flat over `R`.

This is the converse of `AlgebraicGeometry.Space.flat_sections_of_isFlatOver`, for an affine
base which is a scheme of the site rather than the base scheme of the site, and with flatness
read on one chart only.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_of_flat_sections_of_isSurjective`: the statement above.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Flatness over `Spec R` from the sections over one surjective affine chart.**  Let
`p : X ⟶ Spec R` be a morphism from an algebraic space to the algebraic space of `Spec R`, let
`G` be a quasi-coherent `𝒪_X`-module and let `U` be an étale scheme chart of `X` with affine
underlying scheme, surjective onto `X`, with structure morphism `α : U ⟶ Spec R`.  If `G(U)` is
a flat `R`-module through `α`, then `G` is flat over `Spec R` (Stacks 05VV). -/
theorem isFlatOver_of_flat_sections_of_isSurjective {R : CommRingCat.{u}}
    {hR : B.Contains (Spec R)} {b : Spec R ⟶ S} {X : AlgebraicSpaces B S hS}
    (p : X ⟶ schemeSpace (siteObject B S hS hR b)) (G : Modules.{u, u} B S hS X.1 X.2)
    [hG : G.IsQuasicoherentOnSite] (U : SmallEtale B S hS X.1) [IsAffine (chartScheme U)]
    (hU : Function.Surjective (pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom))
    (α : (SmallEtale.toOver B S hS X.1).obj U ⟶ siteObject B S hS hR b)
    (hα : U.1.hom ≫ p.hom = yoneda.map α)
    (hflat :
      let : Module R (G.val.obj (op U)) := Module.compHom _
        ((Scheme.ΓSpecIso R).inv ≫ ((BigFppfOver.toScheme B S hS).map α).appTop).hom
      Module.Flat R (G.val.obj (op U))) :
    IsFlatOver B S hS X.2 p.hom G := by
  let d : ChartDiagram B S hS X.1 (schemeSpace (siteObject B S hS hR b)).1 p.hom :=
    { U := U
      V := selfChart B S hS (siteObject B S hS hR b)
      g := α
      comm := hα.trans (Category.comp_id (yoneda.map α)).symm }
  have : SheafOfModules.IsQuasicoherent (chartRestrictionSheaf B S hS X G U) :=
    isQuasicoherent_chartRestrictionSheaf B S hS X G hG U
  let f : chartScheme U ⟶ Spec R := (BigFppfOver.toScheme B S hS).map α
  let : Module R (G.val.obj (op U)) := Module.compHom _
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom
  let : Module R Γ(chartRestrictionSheaf B S hS X G U, ⊤) := Module.compHom _
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom
  have h1 : Module.Flat R Γ(chartRestrictionSheaf B S hS X G U, ⊤) :=
    Module.Flat.of_semilinearEquiv (RingEquiv.refl R)
      (chartRestrictionSheafTopEquiv B S hS X G U).symm.toAddEquiv
      (fun a m => (chartRestrictionSheafTopEquiv B S hS X G U).symm.map_smul
        (((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom a) m)
  have h2 : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom
      (chartRestrictionSheaf B S hS X G U) :=
    (isFlatOver_overSpec_iff_flat_sections f (chartRestrictionSheaf B S hS X G U)).2 h1
  have hd : IsFlatOverOnChartDiagram B S hS X.2 G d :=
    (AlgebraicGeometry.isFlatOver_iff_of_moduleIso _
      (restrictToChartIsoChartRestrictionSheaf B S hS X G U)).2 h2
  exact (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS p G).2
    (isFlatOver_of_isFlatOverOnChartDiagram_of_surjective B S hS p G d hU hd)

end AlgebraicGeometry.Space

end
