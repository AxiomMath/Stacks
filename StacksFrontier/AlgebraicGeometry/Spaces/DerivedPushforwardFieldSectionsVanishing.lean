module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardFieldSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardLeftTExact
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# Vanishing cohomology over a field and sections of the derived direct image

Let `f : X ⟶ Spec k` be a morphism of algebraic spaces to the spectrum of a field and `𝓜` an
`𝒪_X`-module with `Hⁿ(X, 𝓜) = 0`. Then the cohomology sheaf `Hⁿ(Rf_*(𝓜[0]))` on `Spec k` has
no nonzero global section, hence no nonzero morphism from the structure sheaf: its global
sections are `Hⁿ(X, 𝓜)`
(`AlgebraicGeometry.Space.globalSectionsHomologyDerivedModulePushforwardFieldIso`).

## Main definitions

* `AlgebraicGeometry.Space.HasVanishingFieldFibreCohomologyAboveOne`: the fibres of `f` over
  field-valued points have no cohomology of the structure sheaf in degrees at least two.

## Main results

* `AlgebraicGeometry.Space.subsingleton_unit_hom_homology_derivedModulePushforward_of_isZero`:
  if `Hⁿ(X, 𝓜) = 0`, every morphism `𝒪 ⟶ Hⁿ(Rf_*(𝓜[0]))` is zero.
* `AlgebraicGeometry.Space.subsingleton_unit_hom_homology_derivedModulePushforward_fiberProduct`:
  the same for the structure sheaf of a fibre over a field, in degrees at least two, when the
  fibres over fields have no cohomology above degree one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}

/-- **A vanishing cohomology group of a space over a field kills the sections of the
corresponding cohomology sheaf of the derived direct image.** For `f : X ⟶ Spec k` and an
`𝒪_X`-module `𝓜` with `Hⁿ(X, 𝓜) = 0`, every morphism `𝒪 ⟶ Hⁿ(Rf_*(𝓜[0]))` is zero. -/
theorem subsingleton_unit_hom_homology_derivedModulePushforward_of_isZero (K : Type u) [Field K]
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of K)) (f : X ⟶ schemeSpace V)
    (M : Modules.{u, u} B S hS X.1 X.2) (n : ℕ)
    (hM : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived
        n).obj M)) :
    Subsingleton (SheafOfModules.unit _ ⟶ (DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (schemeSpace V).1 (schemeSpace V).2) n).obj
        ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have := hasSeparator_modules B S hS X.1 X.2
  have := site_hasSheafify_addCommGrp.{u + 1, u, u + 1}
    (J := (smallEtaleRingedSite B S hS X.1 X.2).J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, u + 1}
    (J := (smallEtaleRingedSite B S hS X.1 X.2).J)
  have := moduleSheavesEnoughInjectives.{u + 1, u, u, u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  have hU : IsZero ((globalModuleCohomology.{u + 1, u, u, u + 1} R n).obj
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} M)) := by
    refine IsZero.of_iso ?_ ((rightDerivedGlobalSectionsUliftIso.{u + 1} R n).app M).symm
    exact @ModuleCat.isZero_of_subsingleton _ _ _
      ⟨fun a b => ULift.ext ((ModuleCat.subsingleton_of_isZero hM).elim _ _)⟩
  let ψ := RingHom.id (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj V)))
  have hL := ((ModuleCat.restrictScalars
      ((globalSectionsRingHom B S hS X.1 X.2 f.hom).comp ψ)).map_isZero hU).of_iso
    (globalSectionsHomologyDerivedModulePushforwardFieldIso B S hS K e ψ f M n)
  let H := (DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (schemeSpace V).1 (schemeSpace V).2) n).obj
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))
  have hs : Subsingleton H.sections := ModuleCat.subsingleton_of_isZero hL
  have eH : (DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (schemeSpace V).1 (schemeSpace V).2) n).obj
        ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj M)) ≅ H :=
    (DerivedCategory.homologyFunctor _ n).mapIso
      ((derivedModulePushforwardIsoTotalRightDerived B S hS f).app _)
  refine ⟨fun a b => ?_⟩
  have : a ≫ eH.hom = b ≫ eH.hom :=
    (SheafOfModules.unitHomEquiv H).injective (Subsingleton.elim _ _)
  simpa using congrArg (· ≫ eH.inv) this

/-- The hypothesis `Hᵠ(X_k, 𝒪_{X_k}) = 0` for `q ≥ 2` of the fibres of `f : X ⟶ Y` over the
field-valued points `Spec k ⟶ Y` of a scheme `Y`, with `X_k = X ×_Y Spec k`. -/
def HasVanishingFieldFibreCohomologyAboveOne {V₀ : BigFppfOver B S hS} (f : X ⟶ schemeSpace V₀) :
    Prop :=
  ∀ (p : FieldValuedPoint B S hS (schemeSpace V₀).1) (q : ℕ), 2 ≤ q →
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (AlgebraicSpaces.fiberProduct B S hS f (schemeSpaceMap p.value)).1
        (AlgebraicSpaces.fiberProduct B S hS f (schemeSpaceMap p.value)).2).O)).rightDerived
          q).obj
      (AlgebraicGeometry.Space.structureSheafModule B S hS
        (AlgebraicSpaces.fiberProduct B S hS f (schemeSpaceMap p.value))))

/-- **The cohomology sheaves above degree one of the derived direct image along a fibre over a
field have no nonzero sections**, when the fibres over fields have no cohomology above degree
one. -/
theorem subsingleton_unit_hom_homology_derivedModulePushforward_fiberProduct
    {V₀ : BigFppfOver B S hS} (f : X ⟶ schemeSpace V₀)
    (hvan : HasVanishingFieldFibreCohomologyAboveOne B S hS f)
    (p : FieldValuedPoint B S hS (schemeSpace V₀).1) (m : ℕ) (hm : 2 ≤ m) :
    Subsingleton (SheafOfModules.unit _ ⟶ (DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (schemeSpace p.siteObject).1 (schemeSpace p.siteObject).2) m).obj
        ((derivedModulePushforward B S hS
          (ObjectProperty.homMk (pullback.snd f.hom (schemeSpaceMap p.value).hom) :
            AlgebraicSpaces.fiberProduct B S hS f (schemeSpaceMap p.value) ⟶
              schemeSpace p.siteObject)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (AlgebraicGeometry.Space.structureSheafModule B S hS
              (AlgebraicSpaces.fiberProduct B S hS f (schemeSpaceMap p.value)))))) :=
  subsingleton_unit_hom_homology_derivedModulePushforward_of_isZero B S hS p.carrier (Iso.refl _)
    _ _ m (hvan p m hm)

end AlgebraicGeometry.Space

end
