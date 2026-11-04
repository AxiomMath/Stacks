module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardFieldSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsCorepresentable
public import StacksFrontier.CategoryTheory.Preadditive.RetractsOfFiniteFree

/-!
# The derived fibre of `Rf_*𝒪_X` over a field-valued point

Let `f : X ⟶ Y` be a proper, flat morphism of finite presentation of algebraic spaces and
`p : Spec k ⟶ Y` a field-valued point. By cohomology and base change (Stacks 0CTM, part (1)) the
derived pullback of `Rf_*𝒪_X` to `Spec k` is `Rf_{k,*}𝒪_{X_k}` for the fibre `X_k = X ×_Y Spec k`,
and the global sections of its cohomology sheaves are the cohomology of `𝒪_{X_k}`
(`AlgebraicGeometry.Space.globalSectionsHomologyDerivedModulePushforwardSingleIso`, the Leray
degeneration over the spectrum of a field). So the vanishing of `H^j(X_k, 𝒪_{X_k})` gives the
vanishing of the global sections of `H^j(Lp^* Rf_*𝒪_X)`, in the form `Hom(𝒪, -)` in which
`AlgebraicGeometry.Space.exists_mem_singleDegreeFreePoints_of_isZero_homModule_homology` reads
it.

## Main results

* `isZero_homModule_unit_of_isZero_globalSections`: `Hom(𝒪, M) = 0` when the global sections of
  `M` vanish.
* `isZero_homModule_homology_smallEtaleDerivedModulePullback_derivedModulePushforward`: the
  derived fibre statement above.

## References

* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

-- the global `HasDerivedCategory` instances of `Homology/DerivedCategory/LocallySmall` compete
-- with the standard model in which the derived functors used here are stated

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`Hom(𝒪, M)` vanishes with the global sections of `M`**: morphisms out of the structure
sheaf are global sections (`Stacks.Cohomology.SiteModules.unitSectionsAddEquiv`). -/
theorem isZero_homModule_unit_of_isZero_globalSections {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {A : Type u} [CommRing A]
    (ρ : A →+* End (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    (M : Modules.{u, u} B S hS F hF)
    (h : IsZero ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj M)) :
    IsZero ((homModule (SheafOfModules.unit _) ρ).obj M) := by
  have hsec : Subsingleton M.sections := ModuleCat.subsingleton_of_isZero h
  have hs : Subsingleton (HomFrom (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) M ρ) :=
    ⟨fun a b => HomFrom.ext
      ((Stacks.Cohomology.SiteModules.unitSectionsAddEquiv _ M).injective (Subsingleton.elim _ _))⟩
  have : Subsingleton ((homModule (SheafOfModules.unit _) ρ).obj M) := hs
  exact ModuleCat.isZero_of_subsingleton _

variable {X Y : AlgebraicSpaces B S hS}

/-- **The derived fibre of `Rf_*𝒪_X` at a field-valued point has the cohomology of the fibre.**
Let `f : X ⟶ Y` be proper, flat and of finite presentation, `p` a field-valued point of `Y`, and
`j` a degree in which the cohomology of the structure sheaf of the fibre `X ×_Y Spec k` vanishes.
Then the global sections of `H^j(Lp^* Rf_*𝒪_X)` vanish. -/
theorem isZero_homModule_homology_smallEtaleDerivedModulePullback_derivedModulePushforward
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (p : FieldValuedPoint B S hS Y.1) (j : ℕ)
    (hvan : IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (AlgebraicSpaces.fiberProduct B S hS f
          (ObjectProperty.homMk (yonedaEquiv.symm p.value) : schemeSpace p.siteObject ⟶ Y)).1
        (AlgebraicSpaces.fiberProduct B S hS f
          (ObjectProperty.homMk (yonedaEquiv.symm p.value) :
            schemeSpace p.siteObject ⟶ Y)).2).O)).rightDerived j).obj
      (structureSheafModule B S hS (AlgebraicSpaces.fiberProduct B S hS f
          (ObjectProperty.homMk (yonedaEquiv.symm p.value) : schemeSpace p.siteObject ⟶ Y))))) :
    IsZero ((homModule (SheafOfModules.unit _) (Stacks.SheafOfModules.unitEndRingHom.{u}
        (structureSheaf B S hS (yoneda.obj p.siteObject)
          (isAlgebraicSpace_yoneda B S hS p.siteObject))
        (isTerminal_idChart B S hS p.siteObject))).obj
      ((DerivedCategory.homologyFunctor _ (j : ℤ)).obj
        ((smallEtaleDerivedModulePullback B S hS
          (ObjectProperty.homMk (yonedaEquiv.symm p.value) : schemeSpace p.siteObject ⟶ Y)).obj
          ((derivedModulePushforward B S hS f).obj
            ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)))))) := by
  let V := p.siteObject
  let g : schemeSpace V ⟶ Y := ObjectProperty.homMk (yonedaEquiv.symm p.value)
  let X' := AlgebraicSpaces.fiberProduct B S hS f g
  let f' : X' ⟶ schemeSpace V := ObjectProperty.homMk (pullback.snd f.hom g.hom)
  let g' : X' ⟶ X := ObjectProperty.homMk (pullback.fst f.hom g.hom)
  have sq : IsPullback g' f' f g := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
  let E := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj (SheafOfModules.unit _)
  have hbc := (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp E
    (isPerfect_unit X)).2 g f' g' sq
  -- `Lg^* Rf_* 𝒪_X ≅ Rf'_* 𝒪_{X'}`, the latter read as the total right derived functor
  let e₁ := @asIso _ _ _ _ _ hbc ≪≫
    (derivedModulePushforward B S hS f').mapIso (smallEtaleDerivedModulePullbackUnitIso g') ≪≫
    (smallEtaleDerivedModulePushforwardIso B S hS f').app _
  -- global sections of the cohomology sheaves are the cohomology of the fibre
  have hcoh := acyclicHigherDirectImages_of_field (K := p.carrier) (V := V) (Iso.refl _) f'
    (structureSheafModule B S hS X')
  let e₂ := globalSectionsHomologyDerivedModulePushforwardSingleIso B S hS f'
    (structureSheafModule B S hS X') hcoh j
  let e₃ := rightDerivedGlobalSectionsModulePushforwardIsoOfIsPullbackSection B S hS f'
    (globalSectionsRingHom B S hS (schemeSpace V).1 (schemeSpace V).2 (𝟙 _))
    (globalSectionsRingHom B S hS X'.1 X'.2 f'.hom)
    (fun c => isPullbackSection_globalSectionsRingHom B S hS V f' c)
    (structureSheafModule B S hS X') j
  have h₃ : IsZero ((ModuleCat.restrictScalars
      (globalSectionsRingHom B S hS (schemeSpace V).1 (schemeSpace V).2 (𝟙 _))).obj
        (((modulePushforward B S hS f' ⋙
          Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (schemeSpace V).1 (schemeSpace V).2).O)).rightDerived j).obj
          (structureSheafModule B S hS X'))) :=
    (Functor.map_isZero _ hvan).of_iso e₃
  have h₂ : IsZero ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (schemeSpace V).1 (schemeSpace V).2).O)).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (schemeSpace V))) (j : ℤ)).obj
        ((smallEtaleDerivedModulePullback B S hS g).obj
          ((derivedModulePushforward B S hS f).obj E)))) := by
    have := ModuleCat.subsingleton_of_isZero h₃
    have h₂' : IsZero (((modulePushforward B S hS f' ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (schemeSpace V).1 (schemeSpace V).2).O)).rightDerived j).obj
          (structureSheafModule B S hS X')) :=
      @ModuleCat.isZero_of_subsingleton _ _ _ ‹Subsingleton ((ModuleCat.restrictScalars _).obj _)›
    exact (h₂'.of_iso e₂).of_iso
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor _).mapIso
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (schemeSpace V))) (j : ℤ)).mapIso e₁))
  exact isZero_homModule_unit_of_isZero_globalSections _ _ h₂

end AlgebraicGeometry.Space

end
