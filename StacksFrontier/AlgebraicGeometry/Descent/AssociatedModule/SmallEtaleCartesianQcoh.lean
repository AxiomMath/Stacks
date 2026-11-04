module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesSheafAnyUniverse

/-!
# Quasi-coherent modules on the small étale sites are the cartesian ones

Let `S` be a scheme. A sheaf of modules `𝒢` on the small étale site of `S` is *cartesian between
affine objects* when for every morphism `T ⟶ T'` of the site whose underlying schemes are affine
the base-change comparison `Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective. This file proves that
this condition characterises quasi-coherence on the site, and records the same statement on the
small affine étale site `S_{affine, étale}`, at the universe of the schemes.

On `S_étale` the forward implication is the forward half of Descent, Proposition 03DX (2),
`AlgebraicGeometry.SmallEtale.isCartesianOnAffines_of_isQuasicoherentOnSite`. The converse is
the counit argument: a module cartesian between affine objects is the associated module of its
restriction to the small Zariski site, by
`AlgebraicGeometry.SmallEtale.isIso_counit_of_isCartesianOnAffines`, that restriction is
quasi-coherent because it is cartesian between affine opens, and an associated module of a
quasi-coherent module is quasi-coherent on the site (Stacks 03DV (2)).

On `S_{affine, étale}` the forward implication is Stacks 0H04 for the chart rings, run at the
universe of the schemes through the universe lift of the sections, and the converse is
condition (1) implies condition (2) of Stacks 0GZX: a cartesian presheaf of modules is a sheaf,
by flat descent, and it is quasi-coherent.

## Main results

* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffines`: a sheaf of
  modules on `S_étale` is quasi-coherent exactly when it is cartesian between affine objects.
* `AlgebraicGeometry.SmallEtale.isSheaf_of_cartesian_smallAffineEtale`: a cartesian presheaf of
  modules on `S_{affine, étale}` is a sheaf, at the universe of the schemes.
* `isIso_restrictionBaseChange_smallAffineEtale_of_isQuasicoherentOnSite`, in the same namespace:
  a quasi-coherent module on `S_{affine, étale}` is cartesian, at the universe of the schemes.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules

namespace AlgebraicGeometry.SmallEtale

universe u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A sheaf of modules on the small étale site which is cartesian between affine objects is
quasi-coherent.** It is the associated module of its restriction to the small Zariski site,
which is quasi-coherent because it is cartesian between affine opens. -/
theorem isQuasicoherentOnSite_of_isCartesianOnAffines
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : IsCartesianOnAffines B S hS G) :
    G.IsQuasicoherentOnSite := by
  have hZ : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G) := by
    refine Stacks.AlgebraicGeometry.CartesianQuasicoherent.isQuasicoherent_of_bijective_restriction
      _ fun V V' hV hV' hle => bijective_restrictionBaseChange_restrictModule B S hS G hle ?_
    have aV : AlgebraicGeometry.IsAffine
        ((toScheme B S hS).obj ((opensToSmallEtale B S hS).obj V)) := hV
    have aV' : AlgebraicGeometry.IsAffine
        ((toScheme B S hS).obj ((opensToSmallEtale B S hS).obj V')) := hV'
    exact hG ((opensToSmallEtale B S hS).map (homOfLE hle)) aV' aV
  have := isIso_counit_of_isCartesianOnAffines B S hS G hG hZ
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (asIso ((associatedModuleAdjunction B S hS).counit.app G))
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _ hZ)

/-- **Quasi-coherence on the small étale site is the cartesian condition between affine
objects.** -/
theorem isQuasicoherentOnSite_iff_isCartesianOnAffines
    (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    G.IsQuasicoherentOnSite ↔ IsCartesianOnAffines B S hS G :=
  ⟨isCartesianOnAffines_of_isQuasicoherentOnSite B S hS G,
    isQuasicoherentOnSite_of_isCartesianOnAffines B S hS G⟩

/-- **A cartesian presheaf of modules over the chart rings of the small affine étale site is a
sheaf**, with sections at the universe of the schemes. The coverings of the site are finite flat
coverings of affine schemes, so this is flat descent of modules. -/
theorem isSheaf_of_cartesian_smallAffineEtale
    (M : PresheafOfModules.{u} (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (SmallAffineEtale B S hS)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{u + 1, u, u, u} M f)) :
    Presheaf.IsSheaf (SmallAffineEtale.topology B S hS) M.presheaf := by
  refine isSheaf_of_cartesian_of_flat_refinements'.{u, u + 1, u, u, u, u + 1}
    (SmallAffineEtale.toScheme B S hS) (affineChartRings B S hS) ?_ ?_ M hM _ ?_
  · intro U E hfin hE
    have _ := hfin
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (SmallAffineEtale.toScheme B S hS))).mp hE
    exact faithfullyFlat_pi_affineChartRings B S hS E.X E.f hcov hfl
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_affineChartRings B S hS h
  · intro U T hT
    exact Stacks.Sites.exists_finite_flat_refinement
      (SmallAffineEtale.toScheme B S hS) (SmallAffineEtale.precoverage B S hS)
      (smallAffineEtale_covering_finite_flat B S hS) T hT

/-- **A quasi-coherent module on the small affine étale site is cartesian**, with sections at the
universe of the schemes. This is Stacks 0H04 for the chart rings, applied after raising the
universe of the sections, and descended back along that lift. -/
theorem isIso_restrictionBaseChange_smallAffineEtale_of_isQuasicoherentOnSite
    (M : PresheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineEtaleRingedSite B S hS).O).obj)
    (hM : Presheaf.IsSheaf (SmallAffineEtale.topology B S hS) M.presheaf)
    (hqc : (⟨M, hM⟩ : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallAffineEtaleRingedSite B S hS).O)).IsQuasicoherentOnSite)
    {U V : (SmallAffineEtale B S hS)ᵒᵖ} (f : U ⟶ V) :
    IsIso (restrictionBaseChange.{u + 1, u, u, u} (R := affineChartRings B S hS) M f) := by
  have hRing : Presheaf.IsSheaf (SmallAffineEtale.topology B S hS)
      (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat) :=
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineEtaleRingedSite B S hS).O).property
  have h₂ := _root_.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hqc
  have h₃ := isIso_restrictionBaseChange_affineChart_of_isQuasicoherentOnSite.{u, u}
    B S hS hRing _ h₂ f.unop
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_restrictionBaseChange_of_uliftForPresentation
      (affineChartRings B S hS) hRing ⟨M, hM⟩ _ h₃)

end AlgebraicGeometry.SmallEtale

end
