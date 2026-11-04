module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsAtModel
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSetBaseChangeMateIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality

/-!
# Cohomology of an algebraic space over an affine one, read on the base

For a morphism `f : X ⟶ Y` of algebraic spaces and `M` in `D(𝒪_X)`, `Hⁱ(X, M) = 0` exactly when
every morphism `𝒪_Y[0] ⟶ (Rf_* M)⟦i⟧` vanishes. When `Y = h_U` with `U` affine, `Spec R`, such
morphisms vanish as soon as `RΓ(U, Rf_* M)` lies in degrees `< i` in `D(R)`.

## Main results

* `StacksDraft.PseudoCoherence.IsPseudoCoherent.exists_isLE`: a pseudo-coherent object of `D(R)`
  is bounded above.
* `AlgebraicGeometry.Space.eq_zero_of_isLE_representedAffineDerivedSections`: morphisms
  `𝒪[0] ⟶ N⟦q⟧` vanish when `RΓ(U, N)` lies in degrees `< q`.
* `Space.isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff_derivedModulePushforward`:
  for `f : X ⟶ Y`, `Hⁱ(X, M) = 0` exactly when every morphism `𝒪_Y[0] ⟶ (Rf_* M)⟦i⟧` vanishes.

## Implementation notes

`Hⁱ(X, M) = Hom(𝒪_X[0], M⟦i⟧)`, `𝒪_X[0] = Lf^*𝒪_{h_U}[0]`, `Lf^* ⊣ Rf_*`, and on the affine
`h_U` the morphisms `𝒪[0] ⟶ N` are the morphisms `R[0] ⟶ RΓ(U, N)` through `Φ ⊣ RΓ(U, -)`; the
latter vanish when `RΓ(U, N)` lies in negative degrees since `R` is projective.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe v w u

namespace StacksDraft.PseudoCoherence

/-- A pseudo-coherent object of `D(R)` is bounded above. -/
theorem IsPseudoCoherent.exists_isLE {R : Type w} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
    {K : DerivedCategory (ModuleCat.{v} R)} (hK : IsPseudoCoherent K) : ∃ a : ℤ, K.IsLE a := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  exact ⟨b, (DerivedCategory.isLE_iff _ _).2 fun i hi =>
    (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj E) b i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩

end StacksDraft.PseudoCoherence

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  isGrothendieckAbelian_ringedToposStructureRingSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Morphisms out of `𝒪[0]` on an affine represented space.** For `U` with affine underlying
scheme and `N` in `D(𝒪_{h_U})` with `RΓ(U, N)` in degrees `≤ a`, every morphism `𝒪[0] ⟶ N⟦q⟧`
with `a < q` vanishes. -/
theorem eq_zero_of_isLE_representedAffineDerivedSections (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (N : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
    {a q : ℤ} (hN : ((representedAffineDerivedSections B S hS U).obj N).IsLE a) (hq : a < q)
    (g : (DerivedCategory.singleFunctor _ 0).obj
      (structureModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) ⟶ N⟦q⟧) : g = 0 := by
  set adj := representedAffineDerivedAdjunction B S hS U
  set i := representedAffineDerivedAssociatedSingleUnitIso B S hS U 0
  have := hN
  have : DerivedCategory.TStructure.t.IsLE ((representedAffineDerivedSections B S hS U ⋙
      shiftFunctor _ q).obj N) (a - q) := DerivedCategory.TStructure.t.isLE_shift
    ((representedAffineDerivedSections B S hS U).obj N) a q (a - q) (by omega)
  have hle : ((representedAffineDerivedSections B S hS U).obj (N⟦q⟧)).IsLE (a - q) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (((representedAffineDerivedSections B S hS U).commShiftIso q).app N).symm (a - q)
  have h0 : adj.homEquiv _ _ (i.hom ≫ g) = 0 :=
    DerivedCategory.from_singleFunctor_obj_eq_zero_of_isLE_of_projective (n := a - q)
      (by omega) _ _
  have h1 : i.hom ≫ g = 0 := by
    rw [← (adj.homEquiv _ _).symm_apply_apply (i.hom ≫ g), h0, Adjunction.homEquiv_counit,
      Functor.map_zero, Limits.zero_comp]
  simpa using congrArg (i.inv ≫ ·) h1

section GlobalSections

attribute [local instance 20000] ModuleCat.hasDerivedCategory

/-- **`Hⁱ(X, M)` through a morphism `f : X ⟶ Y`.** For `M` in `D(𝒪_X)`, `Hⁱ(X, M) = 0` exactly when
every morphism `𝒪_Y[0] ⟶ (Rf_* M)⟦i⟧` of `D(𝒪_Y)` vanishes. -/
theorem isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff_derivedModulePushforward
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i).obj
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj M)) ↔
      ∀ g : (DerivedCategory.singleFunctor _ 0).obj (structureModule Y) ⟶
        ((derivedModulePushforward B S hS f).obj M)⟦i⟧, g = 0 := by
  rw [isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff X M i]
  have hz : ∀ {C : Type _} [Category C] [HasZeroMorphisms C] (A B : C),
      (∀ g : A ⟶ B, g = 0) ↔ Subsingleton (A ⟶ B) := fun A B =>
    ⟨fun h => ⟨fun a b => (h a).trans (h b).symm⟩, fun _ g => Subsingleton.elim _ _⟩
  rw [hz, hz]
  let e := smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) f
  let c := ((derivedModulePushforward B S hS f).commShiftIso i).app M
  exact ((e.homCongr (Iso.refl _)).symm.trans
    (((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _).trans
      ((Iso.refl _).homCongr c))).subsingleton_congr

end GlobalSections

end AlgebraicGeometry.Space

end
