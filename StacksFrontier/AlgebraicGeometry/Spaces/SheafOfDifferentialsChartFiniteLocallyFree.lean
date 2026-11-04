module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSmoothFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedSheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme

/-!
# Finite local freeness of `Ω_{X/Y}` read on an étale chart

In a commuting square of étale scheme charts of a morphism `f : X ⟶ Y` of algebraic spaces over
a scheme `S`, whose chart `U ⟶ X` of the source is surjective, the sheaf of differentials
`Ω_{X/Y}` of Stacks 04CT is finite locally free on the small étale site of `X` exactly when the
sheaf of relative differentials `Ω_{U/V}` of the square's morphism of schemes is finite locally
free.

Finite local freeness descends along the surjective étale chart and is preserved by pullback
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_etaleModulePullback_iff`); the restriction
of `Ω_{X/Y}` to the chart is `Ω_{U/V}` read on the small étale site of the algebraic space `U`
(Stacks 04CU, `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`), which is the
associated module of the Zariski sheaf `Ω_{U/V}` (Stacks 04CS,
`AlgebraicGeometry.Space.sheafOfDifferentialsRepresentedIso`); and finite local freeness is
invariant under the comparison of Stacks 03DX (2) and under passing to the associated module on
the small étale site (Stacks 05VG).

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials_iff_chart`.

## References

* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 0D12](https://stacks.math.columbia.edu/tag/0D12)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Finite local freeness of `Ω_{X/Y}` read on a square of étale scheme charts.** In a
commuting square of étale scheme charts of `f : X ⟶ Y` whose chart of the source is surjective,
the sheaf of differentials `Ω_{X/Y}` of Stacks 04CT is finite locally free on the small étale
site of `X` exactly when the sheaf of relative differentials `Ω_{U/V}` of the square's scheme
morphism is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_sheafOfDifferentials_iff_chart {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) (b : yoneda.obj V ⟶ Y.1)
    (ψ : U ⟶ V)
    (haEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hbEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (haSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hdiag : yoneda.map ψ ≫ b = a ≫ f.hom) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (sheafOfDifferentials B S hS f) ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ)) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ)
  let c : schemeSpace U ⟶ X := ObjectProperty.homMk a
  have hcEt : IsEtale B S hS c.hom :=
    isEtale_of_presheaf_etale B S hS haEtale
  have hcSurj : IsSurjective B S hS c.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U a).1 haSurj
  let e := ((modulePullbackIsoEtaleModulePullback B S hS c hcEt).app _).symm ≪≫
    (sheafOfDifferentialsEtaleLocalizationIso B S hS f c (schemeSpaceMap ψ)
      (ObjectProperty.homMk b : schemeSpace V ⟶ Y) hcEt (isEtale_of_presheaf_etale B S hS hbEtale)
      (ObjectProperty.hom_ext _ hdiag.symm)).trans
    (sheafOfDifferentialsRepresentedIso B S hS ψ)
  refine (isFiniteLocallyFreeOnSite_etaleModulePullback_iff B S hS
    c hcEt hcSurj _).trans ?_
  have key : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ))) ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ)) :=
    (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS U _).trans
      (_root_.AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property _)
  exact ⟨fun h ↦ key.1 (SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso e h),
    fun h ↦ SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso e.symm (key.2 h)⟩

end AlgebraicGeometry.Space

end
