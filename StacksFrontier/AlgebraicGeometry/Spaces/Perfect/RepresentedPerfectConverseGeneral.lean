module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedPerfectConverseCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport

/-!
# Perfectness of `ε^*E` on a represented algebraic space forces perfectness of `E`

Let `T` be an object of the big fppf site with underlying scheme `X`, and `E` an object of
`D(𝒪_X)` with quasi-coherent cohomology sheaves. If `ε^*E` is a perfect object of `D(𝒪_{h_T})`
(perfectness on the small étale site of the represented algebraic space, Stacks 08G5), then `E`
is perfect. This is the converse half of Stacks 08HG, for objects with quasi-coherent cohomology.

Perfectness on `X` is local on the affine opens `U` of `X`; each is isomorphic to `Spec A`, the
restriction of `ε^*E` to `h_{Spec A}` is perfect and is `ε^*(E|_{Spec A})`, and the affine case
`AlgebraicGeometry.Space.isPerfect_spec_of_isPerfect_representedDerivedAssociatedModule` applies.

## Main results

* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_representedDerivedAssociatedModule_of_scheme`.

## References

* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule
  etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- **Perfect complexes on a scheme are local on an open covering**, at the level of complexes
(so independent of a model of the derived category). -/
theorem isPerfectComplex_of_forall_restrictFunctor {X : Scheme.{u}}
    (E₀ : CochainComplex X.Modules ℤ) {I : Type*} {U : I → Scheme.{u}} (j : ∀ i, U i ⟶ X)
    [∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ i y, j i y = x)
    (h : ∀ i, RingedSpace.IsPerfectComplex (X := (U i).toRingedSpace)
      (((Scheme.Modules.restrictFunctor (j i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀)) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) E₀ :=
  (Stacks.Duality.SupportedGeneration.isPerfect_Q_obj_iff_isPerfectComplex E₀).1
    (Stacks.Duality.SupportedGeneration.isPerfect_of_forall_derivedRestrict _ j hcov fun i =>
      Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := (U i).toRingedSpace)
        ((Scheme.Modules.restrictFunctor (j i)).mapDerivedCategoryFactors.app E₀).symm
        ((Stacks.Duality.SupportedGeneration.isPerfect_Q_obj_iff_isPerfectComplex _).2 (h i)))

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The converse of Stacks 08HG, for quasi-coherent cohomology.** Let `T` be an object of the
big fppf site with scheme `X` and `E` an object of `D(𝒪_X)` with quasi-coherent cohomology. If
`ε^*E` is perfect on the small étale site of `h_T`, then `E` is perfect. -/
theorem isPerfect_of_isPerfect_representedDerivedAssociatedModule_of_scheme
    (T : BigFppfOver B S hS)
    (E : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E).IsQuasicoherent)
    (h : (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).IsPerfect
      ((representedDerivedAssociatedModule B S hS T).obj E)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace) E := by
  let X := (BigFppfOver.toScheme B S hS).obj T
  let E₀ := DerivedCategory.Q.objPreimage E
  let eE : DerivedCategory.Q.obj E₀ ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hj : ∀ U : X.affineOpens, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (openSubHom T U.1)) := fun U => by
    rw [toScheme_map_openSubHom]
    exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion U.1.ι)
  have hcov : ∀ x : X, ∃ (U : X.affineOpens)
      (y : (BigFppfOver.toScheme B S hS).obj (openSub T U.1)),
      (BigFppfOver.toScheme B S hS).map (openSubHom T U.1) y = x := fun x => by
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ (⊤ : X.Opens) from trivial)
    refine ⟨⟨U, hU⟩, ⟨x, hxU⟩, ?_⟩
    rw [toScheme_map_openSubHom]
    rfl
  suffices key : ∀ U : X.affineOpens, RingedSpace.IsPerfectComplex
      (X := ((BigFppfOver.toScheme B S hS).obj (openSub T U.1)).toRingedSpace)
      (((Scheme.Modules.restrictFunctor ((BigFppfOver.toScheme B S hS).map
        (openSubHom T U.1))).mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀) by
    exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := X.toRingedSpace) eE
      (RingedSpace.IsPerfectComplex.isPerfect.{u, u + 1}
        (isPerfectComplex_of_forall_restrictFunctor E₀
          (fun U : X.affineOpens => (BigFppfOver.toScheme B S hS).map (openSubHom T U.1))
          hcov key))
  intro U
  -- The affine open `U`, as an object of the big fppf site isomorphic to some `Spec A`.
  obtain ⟨A, _, hA, p, ⟨eU⟩⟩ := exists_iso_mk_spec B S hS (openSub T U.1) U.2
  let g' : BigFppfOver.mk B S hS hA p ⟶ T := eU.inv ≫ openSubHom T U.1
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g') := by
    show _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (eU.inv ≫ openSubHom T U.1))
    rw [Functor.map_comp]
    infer_instance
  have hφ : IsEtale B S hS (representedSpaceMap B S hS g').hom :=
    isEtale_of_presheaf_etale B S hS
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) g').2 inferInstance)
  let f := (BigFppfOver.toScheme B S hS).map g'
  have := preservesFiniteLimits_modulesPullback_of_flat f
  have : PreservesFiniteColimits (Scheme.Modules.pullback f) :=
    AlgebraicGeometry.preservesFiniteColimits_modulesPullback f
  -- `E|_{Spec A}` is perfect, by the affine case.
  have hE' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedPullback f.toLRSHom.toShHom).obj E)).IsQuasicoherent := fun i =>
    (SheafOfModules.isQuasicoherent _).prop_of_iso
      ((((Scheme.Modules.pullback f).mapDerivedCategoryHomologyIso i).app E).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso
          ((Scheme.Modules.derivedPullbackIsoMapDerivedCategory f).app E).symm)
      (Stacks.Modules.isQuasicoherent_pullback f _ (hE i))
  obtain ⟨F, hF, ⟨eF⟩⟩ :=
    isPerfect_etaleModulePullback_standard B S hS (representedSpaceMap B S hS g') hφ _ h
  have hperf := isPerfect_spec_of_isPerfect_representedDerivedAssociatedModule B S hS hA p
    ((derivedPullback f.toLRSHom.toShHom).obj E) hE'
    ⟨F, hF, ⟨eF ≪≫ (representedDerivedAssociatedModulePullbackIso B S hS g' hφ).app E⟩⟩
  -- Back to `U` along the isomorphism `U ≅ Spec A`.
  let ψ := (BigFppfOver.toScheme B S hS).map eU.hom
  have hc₁ : RingedSpace.IsPerfectComplex (X := (Spec (CommRingCat.of A)).toRingedSpace)
      (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀) :=
    (Stacks.Duality.SupportedGeneration.isPerfect_Q_obj_iff_isPerfectComplex
      (X := (Spec (CommRingCat.of A)).toRingedSpace)
      (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀)).1
      ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace
        (X := (Spec (CommRingCat.of A)).toRingedSpace) (DerivedCategory.Q.obj
          (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀))).1
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
        (X := (Spec (CommRingCat.of A)).toRingedSpace)
        ((derivedPullback f.toLRSHom.toShHom).mapIso eE.symm ≪≫
          (Scheme.Modules.derivedPullbackIsoMapDerivedCategory f).app _ ≪≫
          ((Scheme.Modules.pullback f).mapDerivedCategoryFactors.app E₀)) hperf))
  have hc₂ := Stacks.Duality.SupportedGeneration.isPerfectComplex_restrictFunctor_of_isIso ψ _ hc₁
  have hψ : ψ ≫ f = (BigFppfOver.toScheme B S hS).map (openSubHom T U.1) := by
    show (BigFppfOver.toScheme B S hS).map eU.hom ≫
      (BigFppfOver.toScheme B S hS).map (eU.inv ≫ openSubHom T U.1) = _
    rw [← Functor.map_comp, Iso.hom_inv_id_assoc]
  let Φ : Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor ψ ≅
      Scheme.Modules.restrictFunctor ((BigFppfOver.toScheme B S hS).map (openSubHom T U.1)) :=
    Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback ψ) ≪≫
      Scheme.Modules.pullbackComp ψ f ≪≫ Scheme.Modules.pullbackCongr hψ ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback _).symm
  exact RingedSpace.IsPerfectComplex.of_iso hc₂
    ((Functor.mapHomologicalComplexCompIso Φ (ComplexShape.up ℤ)).app E₀)

end AlgebraicGeometry.Space
