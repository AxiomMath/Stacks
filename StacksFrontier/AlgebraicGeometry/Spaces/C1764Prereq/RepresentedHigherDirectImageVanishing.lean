module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishingNoetherian
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSectionsNatural
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal

/-!
# Higher direct images to an affine scheme from a represented space

Let `g : T' ⟶ T` be a quasi-compact and quasi-separated morphism of schemes of the big fppf site
over `S`, with `T` affine, and `𝓜` a quasi-coherent module on the small étale site of the algebraic
space represented by `T'`. If the Zariski cohomology `Hⁿ(T', 𝓜|_{T'})` of the restriction of `𝓜` to
`T'` vanishes, then so does `Rⁿg_*𝓜` on the small étale site.

## Main results

* `isZero_rightDerived_modulePushforward_representedSpaceMap_of_isZero`: if `Hⁿ(T', 𝓜|_{T'})`
  vanishes, then so does `Rⁿg_*𝓜`.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1764Prereq

attribute [local instance 5000] SheafOfModules.instAbelian

open AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] hasInjectiveResolutions_modules in
/-- **Higher direct images to an affine scheme of a quasi-coherent module on a represented space
vanish with the Zariski cohomology of its restriction.** Let `g : T' ⟶ T` be a morphism of the big
fppf site over `S` whose underlying morphism of schemes is quasi-compact and quasi-separated, with
`T` affine, and `𝓜` a quasi-coherent module on the small étale site of the represented algebraic
space `h_{T'}`. If `Hⁿ(T', 𝓜|_{T'}) = 0` for the restriction of `𝓜` to the Zariski site of `T'`,
then `Rⁿg_*𝓜 = 0`. -/
theorem isZero_rightDerived_modulePushforward_representedSpaceMap_of_isZero
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map g)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map g)]
    (M : Space.Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
    (hM : M.IsQuasicoherentOnSite) (n : ℕ)
    (h : IsZero (((SheafOfModules.evaluation ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf
      (Opposite.op ⊤)).rightDerived n).obj
        (restrictToChartScheme B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T') M
          (idEtaleChart B S hS T')))) :
    have := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
    IsZero (((modulePushforward B S hS (representedSpaceMap B S hS g)).rightDerived n).obj M) := by
  have := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
  obtain ⟨G, hG, ⟨e⟩⟩ :=
    exists_isQuasicoherent_iso_representedAssociatedModule_of_isQuasicoherentOnSite B S hS T' M hM
  have := hG
  obtain ⟨eG⟩ := nonempty_restrictToChartScheme_idEtaleChart_representedAssociatedModule
    (B := B) (S := S) (hS := hS) T' G hG
  have hG0 : IsZero (((SheafOfModules.evaluation ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf
      (Opposite.op ⊤)).rightDerived n).obj G) :=
    h.of_iso (((SheafOfModules.evaluation _ _).rightDerived n).mapIso
      (eG.symm ≪≫ (restrictToChartSchemeFunctor B S hS (yoneda.obj T')
        (isAlgebraicSpace_yoneda B S hS T') (idEtaleChart B S hS T')).mapIso e))
  obtain ⟨e'⟩ := nonempty_rightDerived_modulePushforward_representedAssociatedModule B S hS g
    inferInstance inferInstance G hG n
  refine IsZero.of_iso ?_ (((modulePushforward B S hS (representedSpaceMap B S hS g)).rightDerived
    n).mapIso e.symm ≪≫ e')
  refine Functor.map_isZero _ ?_
  refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine _ ?_
  exact IsZero.of_iso (Functor.map_isZero (ModuleCat.restrictScalars
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom) hG0)
    ((Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardNatIso
      ((BigFppfOver.toScheme B S hS).map g) n).app ⟨G, hG⟩).symm

end AlgebraicGeometry.C1764Prereq

end
