module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitToRestrictScalarsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGeometricallyConnectedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral
public import StacksFrontier.LinearAlgebra.FinrankLeOneBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact

/-!
# The structure map of a direct image over the spectrum of a field

Let `f : Z ⟶ U₀` be a morphism from an algebraic space to the algebraic space of an affine scheme
`U₀ = Spec K` with `K` a field. If `Z` has a point, `f_*𝒪_Z` is quasi-coherent and its module
`Γ(U₀, f_*𝒪_Z)` is finite of dimension at most one over `K`, then `𝒪_{U₀} ⟶ f_*𝒪_Z` is an
isomorphism. Global sections on `U₀` form an equivalence on quasi-coherent modules, and the
nonzero `K`-linear map `K = Γ(𝒪) ⟶ Γ(f_*𝒪_Z)` into a space of dimension at most one is bijective.

## Main results

* `AlgebraicGeometry.Space.structureModuleToModulePushforward`: `𝒪_Y ⟶ f_*𝒪_X` as a morphism of
  `𝒪_Y`-modules.
* `AlgebraicGeometry.Space.isIso_structureSharp_of_finrank_le_one`.
* `AlgebraicGeometry.Space.representedAffineSections_modulePushforward_iso_of_isIso`: conversely,
  an invertible structure map gives `Γ(U₀, f_*𝒪_Z) ≅ Γ(U₀, 𝒪)`.
* `AlgebraicGeometry.Space.subsingleton_representedAffineSections_modulePushforward_of_isEmpty`:
  for `Z` without points, `Γ(U₀, f_*𝒪_Z) = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- Global sections on an affine represented space reflect isomorphisms of quasi-coherent
modules. -/
theorem isIso_of_isIso_representedAffineSections_map
    {M N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)}
    (g : M ⟶ N) (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    [IsIso ((representedAffineSections B S hS U).map g)] : IsIso g := by
  let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).O))
  let g' : (⟨M, hM⟩ : P.FullSubcategory) ⟶ ⟨N, hN⟩ := ObjectProperty.homMk g
  have h := NatIso.naturality_1 (representedAffineAssocInverseIso B S hS U) g'
  have h₁ : IsIso ((ObjectProperty.ι P ⋙ representedAffineSections B S hS U).map g') :=
    inferInstanceAs (IsIso ((representedAffineSections B S hS U).map g))
  have h₂ : IsIso ((representedAffineAssoc B S hS U).inverse.map g') := by
    have := (NatIso.isIso_map_iff (representedAffineAssocInverseIso B S hS U) g').2 h₁
    exact this
  have h₃ : IsIso g' := isIso_of_reflects_iso g' (representedAffineAssoc B S hS U).inverse
  exact inferInstanceAs (IsIso ((ObjectProperty.ι P).map g'))

/-- Global sections on an affine represented space are faithful on quasi-coherent modules. -/
theorem eq_zero_of_representedAffineSections_map_eq_zero
    {M N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)}
    (g : M ⟶ N) (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hg : (representedAffineSections B S hS U).map g = 0) : g = 0 := by
  let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).O))
  let g' : (⟨M, hM⟩ : P.FullSubcategory) ⟶ ⟨N, hN⟩ := ObjectProperty.homMk g
  let z : (⟨M, hM⟩ : P.FullSubcategory) ⟶ ⟨N, hN⟩ := ObjectProperty.homMk 0
  have h0 : (ObjectProperty.ι P ⋙ representedAffineSections B S hS U).map g' =
      (ObjectProperty.ι P ⋙ representedAffineSections B S hS U).map z := by
    change (representedAffineSections B S hS U).map g =
      (representedAffineSections B S hS U).map 0
    rw [hg, Functor.map_zero]
  have hgz : (representedAffineAssoc B S hS U).inverse.map g' =
      (representedAffineAssoc B S hS U).inverse.map z := by
    rw [← NatIso.naturality_2 (representedAffineAssocInverseIso B S hS U) g',
      ← NatIso.naturality_2 (representedAffineAssocInverseIso B S hS U) z, h0]
  have := (representedAffineAssoc B S hS U).inverse.map_injective hgz
  exact congrArg (fun k => (ObjectProperty.ι P).map k) this

/-- `Γ(U, 𝒪) ≅ A` for the represented affine `U = Spec A`. -/
def representedAffineSectionsStructureModuleIso :
    (representedAffineSections B S hS U).obj
        (structureModule (schemeSpace U)) ≅
      ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  (representedAffineSections B S hS U).mapIso (representedAffineAssociatedObjUnitIso B S hS
      U).symm ≪≫
    (asIso ((representedAffineAssociatedAdjunction B S hS U).unit.app _)).symm


section Unit

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The structure map `𝒪_Y ⟶ f_*𝒪_X`, read as a morphism of `𝒪_Y`-modules. -/
def structureModuleToModulePushforward :
    structureModule Y ⟶ (modulePushforward B S hS f).obj (structureModule X) :=
  SheafOfModules.unitToRestrictScalarsObjUnit (structureSharp B S hS f)

/-- If `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism of modules, the structure map is an isomorphism. -/
theorem isIso_structureSharp_of_isIso_structureModuleToModulePushforward
    [h : IsIso (structureModuleToModulePushforward f)] : IsIso (structureSharp B S hS f) :=
  have : IsIso (SheafOfModules.unitToRestrictScalarsObjUnit (structureSharp B S hS f)) := h
  SheafOfModules.isIso_of_isIso_unitToRestrictScalarsObjUnit _

/-- If the structure map is an isomorphism, so is `𝒪_Y ⟶ f_*𝒪_X` as a map of modules. -/
theorem isIso_structureModuleToModulePushforward_of_isIso [IsIso (structureSharp B S hS f)] :
    IsIso (structureModuleToModulePushforward f) :=
  SheafOfModules.isIso_unitToRestrictScalarsObjUnit_of_isIso _

end Unit

section Nontrivial

variable {B S hS}

/-- The ring of global functions of an algebraic space with a point is nontrivial. -/
theorem nontrivial_globalFunctions'_of_point {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    Nontrivial (globalFunctions' B S hS F) := by
  let := pointTopology B S hS F
  obtain ⟨U, p, -⟩ := exists_chart_point B S hS F hF x
  refine nontrivial_of_ne 0 1 fun h => ?_
  have h' : (0 : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤)) = 1 :=
    congrArg (fun t : globalFunctions' B S hS F => t.val (op U)) h
  have hg := congrArg (((BigFppfOver.toScheme B S hS).obj U.obj.left).presheaf.germ ⊤
    (pointsToScheme B S hS U.obj.left p) trivial).hom h'
  rw [map_zero, map_one] at hg
  exact zero_ne_one hg

/-- If the structure map `𝒪_{U₀} ⟶ f_*𝒪_Z` vanishes on the identity chart of `U₀`, then the ring
of global functions of `Z` is zero. -/
theorem subsingleton_globalFunctions'_of_structureSharp_eq_zero {Z : AlgebraicSpaces B S hS}
    (U₀ : BigFppfOver B S hS) (f : Z ⟶ (schemeSpaceFunctor B S hS).obj U₀)
    (h : ∀ a, ((structureSharp B S hS f).hom.app (op (idEtaleChart B S hS U₀))).hom a = 0) :
    Subsingleton (globalFunctions' B S hS Z.obj) := by
  have hV : IsIso ((comparisonFunctor B S hS ((schemeSpaceFunctor B S hS).obj U₀)).obj
      (idEtaleChart B S hS U₀)).1.hom := by
    change IsIso (𝟙 ((schemeSpaceFunctor B S hS).obj U₀)); infer_instance
  have hsm : ∀ a : ToType ((structureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj U₀)).obj.obj
      (op (idEtaleChart B S hS U₀))), structureMapApp B S hS f (idEtaleChart B S hS U₀) a =
      structureMapApp B S hS f (idEtaleChart B S hS U₀) (0 : ToType ((structureRingSheaf B S hS
        ((schemeSpaceFunctor B S hS).obj U₀)).obj.obj (op (idEtaleChart B S hS U₀)))) := fun a =>
    (directImageSectionsEquiv B S hS f (idEtaleChart B S hS U₀)).injective
      ((h a).trans (h 0).symm)
  have htc : ∀ a, terminalChartPullback B S hS f (idEtaleChart B S hS U₀) hV a =
      terminalChartPullback B S hS f (idEtaleChart B S hS U₀) hV 0 := fun a =>
    Subtype.ext (funext fun U => by
      change chartPullback B S hS f _ (terminalChartIndex B S hS f _ hV U.unop) a =
        chartPullback B S hS f _ (terminalChartIndex B S hS f _ hV U.unop)
          (0 : ToType ((structureRingSheaf B S hS
            ((schemeSpaceFunctor B S hS).obj U₀)).obj.obj (op (idEtaleChart B S hS U₀))))
      refine (chartProjection_structureMapApp B S hS f _ _ a).symm.trans ?_
      refine Eq.trans ?_ (chartProjection_structureMapApp B S hS f _ _ _)
      exact congrArg _ (hsm a))
  have h10 : globalFunctionsMap B S hS f 1 = globalFunctionsMap B S hS f 0 :=
    (globalFunctionsMap_eq_terminalChartPullback B S hS U₀ f hV 1).trans
      ((htc _).trans (globalFunctionsMap_eq_terminalChartPullback B S hS U₀ f hV 0).symm)
  rw [map_one, map_zero] at h10
  exact subsingleton_of_zero_eq_one h10.symm

end Nontrivial

section FieldBase

variable {B S hS} (U₀ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
  {Z : AlgebraicSpaces B S hS} (f : Z ⟶ (schemeSpaceFunctor B S hS).obj U₀)

/-- **Over the spectrum of a field, a direct image of the structure sheaf with at most
one-dimensional global sections is the structure sheaf.** If `Γ(U₀, 𝒪)` is a field, `Z` has a
point, `f_*𝒪_Z` is quasi-coherent and its module of global sections is finite of dimension at
most one, then `𝒪_{U₀} ⟶ f_*𝒪_Z` is an isomorphism. -/
theorem isIso_structureSharp_of_finrank_le_one
    (hK : IsField Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)) (x : points B S hS Z.obj)
    (hq : ((modulePushforward B S hS f).obj (structureModule Z)).IsQuasicoherentOnSite)
    (hfin : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)
      ((representedAffineSections B S hS U₀).obj
        ((modulePushforward B S hS f).obj (structureModule Z))))
    (hN : Module.finrank Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)
      ((representedAffineSections B S hS U₀).obj
        ((modulePushforward B S hS f).obj (structureModule Z))) ≤ 1) :
    IsIso (structureSharp B S hS f) := by
  let u := structureModuleToModulePushforward f
  let e := representedAffineSectionsStructureModuleIso B S hS U₀
  let ℓ := e.inv ≫ (representedAffineSections B S hS U₀).map u
  have hmap : (representedAffineSections B S hS U₀).map u = e.hom ≫ ℓ :=
    (Iso.hom_inv_id_assoc e _).symm
  have hℓ : ℓ.hom ≠ 0 := by
    intro h0
    have h2 : (representedAffineSections B S hS U₀).map u = 0 := by
      rw [hmap, ModuleCat.hom_ext h0 (g := 0)]
      exact Limits.comp_zero
    have hu : u = 0 := eq_zero_of_representedAffineSections_map_eq_zero B S hS U₀ u
      (SheafOfModules.isQuasicoherentOnSite_unit _) hq h2
    have hs := subsingleton_globalFunctions'_of_structureSharp_eq_zero U₀ f
      (fun a => SheafOfModules.app_eq_zero_of_unitToRestrictScalarsObjUnit_eq_zero _ hu _ a)
    have := nontrivial_globalFunctions'_of_point Z.2 x
    exact not_subsingleton _ hs
  have := hfin
  have hb := LinearMap.bijective_of_ne_zero_of_finrank_le_one hK hN ℓ.hom hℓ
  have hℓi : IsIso ℓ := (ConcreteCategory.isIso_iff_bijective ℓ).2 hb
  have : IsIso ((representedAffineSections B S hS U₀).map u) := by
    rw [hmap]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom e) hℓi
  have : IsIso u := isIso_of_isIso_representedAffineSections_map B S hS U₀ u
    (SheafOfModules.isQuasicoherentOnSite_unit _) hq
  exact isIso_structureSharp_of_isIso_structureModuleToModulePushforward f

/-- **Over the spectrum of a field, an invertible structure map gives one-dimensional global
sections of `f_*𝒪_Z`.** -/
theorem representedAffineSections_modulePushforward_iso_of_isIso
    [IsIso (structureSharp B S hS f)] :
    Nonempty ((representedAffineSections B S hS U₀).obj
        ((modulePushforward B S hS f).obj (structureModule Z)) ≅
      ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)) :=
  have := isIso_structureModuleToModulePushforward_of_isIso f
  ⟨(representedAffineSections B S hS U₀).mapIso (asIso (structureModuleToModulePushforward
      f)).symm ≪≫
    representedAffineSectionsStructureModuleIso B S hS U₀⟩

/-- The structure module of an algebraic space without points is zero. -/
theorem isZero_structureModule_of_isEmpty (hZ : IsEmpty (points B S hS Z.obj)) :
    IsZero (structureModule Z) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  apply SheafOfModules.hom_ext
  ext W : 2
  have : IsEmpty ((BigFppfOver.toScheme B S hS).obj W.unop.obj.left) :=
    ⟨fun y => hZ.false (pointsMap B S hS _ W.unop.obj.hom
      (surjective_pointsToScheme B S hS W.unop.obj.left y).choose)⟩
  have : Subsingleton ((structureModule Z).val.obj W) :=
    (inferInstance : Subsingleton Γ((BigFppfOver.toScheme B S hS).obj W.unop.obj.left, ⊤))
  exact LinearMap.ext fun _ => Subsingleton.elim (α := (structureModule Z).val.obj W) _ _

/-- Over an affine represented base, the global sections of the direct image of the structure
sheaf of an algebraic space without points vanish. -/
theorem subsingleton_representedAffineSections_modulePushforward_of_isEmpty
    (hZ : IsEmpty (points B S hS Z.obj)) :
    Subsingleton ((representedAffineSections B S hS U₀).obj
      ((modulePushforward B S hS f).obj (structureModule Z))) := by
  have h1 := (isZero_structureModule_of_isEmpty hZ)
  have h2 := Functor.map_isZero (modulePushforward B S hS f) h1
  have h3 := Functor.map_isZero (representedAffineSections B S hS U₀) h2
  exact (ModuleCat.isZero_iff_subsingleton).1 h3

end FieldBase

end AlgebraicGeometry.Space
