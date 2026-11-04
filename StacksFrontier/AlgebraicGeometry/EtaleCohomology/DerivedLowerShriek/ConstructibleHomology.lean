module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreClassRightDerivedFunctorPlus
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage
public import StacksFrontier.Homology.PseudoCoherent.Locality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible cohomology of `Rf_!`: reduction to sheaves

Let `B` be a big étale site, `f : X ⟶ Y` a morphism of schemes of `B` with a compactification
`j : X ⟶ X̄`, `f̄ : X̄ ⟶ Y`, and `Λ` a Noetherian ring. The functor
`Rf_! = Rf̄_* ∘ j_!` of `Stacks.EtaleCohomology.derivedLowerShriek` acts on the bounded below
derived category of sheaves of `Λ`-modules on Mathlib's small étale site. This file reduces the
constructibility of the cohomology sheaves of `Rf_! K`, for `K` with constructible torsion
cohomology sheaves, to the case of a single constructible torsion sheaf: if every `R^p f̄_*(j_! F)`
with `F` constructible and torsion is constructible, then so is every `H^n(Rf_! K)`.

This is the dévissage of the last paragraph of the proof of Stacks 0GL0 ("using the first
spectral sequence of Derived Categories, Lemma 015J"), carried out by
`CategoryTheory.Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj`. Extension by zero is
exact, so `H^q(Rj_! K) = j_!(H^q K)`.

## Main definitions

* `Stacks.EtaleCohomology.IsBigSiteConstructibleEtaleModule`: constructibility (Stacks 03RW (3))
  of a sheaf of `Λ`-modules on Mathlib's small étale site, through the identification
  `Stacks.EtaleCohomology.etaleModulesToSmallEtale` with the small étale site of Stacks 021B.

## Main results

* `Stacks.EtaleCohomology.isWeakSerreClass_isBigSiteConstructibleEtaleModule`: Stacks 03RZ (3)
  transported to Mathlib's small étale site.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_sheaf`: the
  reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

section

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **A constructible sheaf of `Λ`-modules on Mathlib's small étale site** (Stacks 03RW (3)): its
transport to the small étale site of Stacks 021B is constructible. -/
def IsBigSiteConstructibleEtaleModule : ObjectProperty (EtaleModules.{u, r} Λ X.obj) :=
  fun F => IsConstructibleModuleSheaf B X Λ ((etaleModulesToSmallEtale B X Λ).obj F)

/-- **Stacks 03RZ (3) on Mathlib's small étale site**: the constructible sheaves of `Λ`-modules
form a weak Serre subcategory, because they are the inverse image of the constructible sheaves on
the small étale site of Stacks 021B under an equivalence. -/
theorem isWeakSerreClass_isBigSiteConstructibleEtaleModule :
    (IsBigSiteConstructibleEtaleModule B X Λ).IsWeakSerreClass := by
  have := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, r} B X Λ
  exact ObjectProperty.isWeakSerreClass_of_iff
    (fun F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ) =>
      IsConstructibleModuleSheaf B X Λ F)
    (etaleModulesToSmallEtale B X Λ) (fun _ => Iff.rfl)

end

section Reduction

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X.obj ⟶ Y.obj)
  (j : CompactificationOf (Over.mk f)) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- The cohomology sheaves of `Rj_! K` are the extensions by zero of those of `K`: extension by
zero is exact, so its right derived functor is the functor it induces on derived categories. -/
theorem nonempty_homology_etaleModuleDerivedExtensionByZero_iso
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X.obj)) (q : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj K) ≅
      (etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) :=
  ⟨(DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((etaleModuleExtensionByZero.{u, r} Λ
        j.immersion).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app K) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (etaleModuleExtensionByZero.{u, r} Λ j.immersion) q).app (DerivedCategory.Plus.ι.obj K)⟩

/-- **Reduction of the constructibility of `H^n(Rf_! K)` to sheaves.** If for every
constructible torsion sheaf of `Λ`-modules `F` on `X` all the higher direct images
`R^p f̄_*(j_! F)` are constructible, then for every bounded below complex `K` with constructible
torsion cohomology sheaves, every cohomology sheaf of `Rf_! K = Rf̄_*(j_! K)` is constructible.
This is the dévissage by the first spectral sequence of Stacks 015J in the proof of Stacks 0GL0;
it uses that `j_!` is exact. -/
@[sga "4½ Th_finitude 1.3" "clause b), special case"]
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_sheaf
    (hcore : ∀ F : EtaleModules.{u, r} Λ X.obj, IsBigSiteConstructibleEtaleModule B X Λ F →
      IsTorsionEtaleModule Λ X.obj F → ∀ p : ℕ,
        IsBigSiteConstructibleEtaleModule B Y Λ
          (((etaleModuleDirectImage.{u, r} Λ j.toBase).rightDerived p).obj
            ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F)))
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X.obj))
    (hK : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
        ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
      IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ
      ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((derivedLowerShriek.{u, r} f j Λ).obj K)) := by
  have hQ := isWeakSerreClass_isBigSiteConstructibleEtaleModule B Y Λ
  let P : ObjectProperty (EtaleModules.{u, r} Λ j.space) := fun M =>
    ∃ F : EtaleModules.{u, r} Λ X.obj, IsBigSiteConstructibleEtaleModule B X Λ F ∧
      IsTorsionEtaleModule Λ X.obj F ∧
        Nonempty (M ≅ (etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F)
  have hP : P.IsClosedUnderIsomorphisms :=
    ⟨fun e ⟨F, h₁, h₂, ⟨e'⟩⟩ => ⟨F, h₁, h₂, ⟨e.symm ≪≫ e'⟩⟩⟩
  have h :=
    (etaleModuleDirectImage.{u, r} Λ j.toBase).derivedCategoryBPlus_rightDerivedFunctorPlus_obj
      P (IsBigSiteConstructibleEtaleModule B Y Λ)
      (fun M ⟨F, h₁, h₂, ⟨e⟩⟩ p =>
        (IsBigSiteConstructibleEtaleModule B Y Λ).prop_of_iso
          (((etaleModuleDirectImage.{u, r} Λ j.toBase).rightDerived p).mapIso e).symm
          (hcore F h₁ h₂ p))
      ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj K)
      (fun q => ⟨_, (hK q).1, (hK q).2, nonempty_homology_etaleModuleDerivedExtensionByZero_iso
        B f j Λ K q⟩)
  exact h.2 n

end Reduction

end Stacks.EtaleCohomology

end
