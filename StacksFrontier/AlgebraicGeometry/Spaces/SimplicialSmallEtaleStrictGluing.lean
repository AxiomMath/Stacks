module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealizationLeftDerivedComponent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleCohomology
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.QuasicoherentCartesianEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictCocyclePair
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.QuasicoherentDerivedPullbackOfExact
public import StacksFrontier.CategoryTheory.Shift.HomVanishingTransport

/-!
# Gluing derived modules on the strict components of a simplicial algebraic space

Let `X` be a simplicial algebraic space and `(K₀, α)` a pair of Stacks 0GMF on the degree-zero
strict component, realizing through `e : L realize_0^* K₀' ≅ K₀` to an object `K₀` of
`D(𝒪_{X_0})`. If the objects `K_n = L X(τⁿₙ)^* K₀` have no negative self-extensions, the
cartesian simplicial system of Stacks 0GMF attached to the pair is the system of an object `K'`
of the derived category of the total site of the strict components (Stacks 0D9T, in its
flatness-free form `exists_isCartesianDerivedModule_realizing_moduleSystem`). If moreover the
face maps of `X` have exact pullbacks and the `K_n` have quasi-coherent cohomology, so has `K'`:
its cohomology modules are cartesian (Stacks 0D7L (2)) with quasi-coherent components, hence
quasi-coherent (Stacks 0D7M).

## Main results

All in the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`:

* `pairDerivedModuleSystem_shift_hom_eq_zero`: the objects of the system of the pair have no
  negative self-extensions.
* `exists_isCartesianDerivedModule_pairDerivedModuleSystem`: the system of the pair is the system
  of a cartesian object of the derived category.
* `derivedCategoryB_isQuasicoherentOnSite_of_pairDerivedModuleSystem_iso`: that object has
  quasi-coherent cohomology.
* `exists_strictGluing`: the resulting gluing statement on the strict components.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackOfToposHom
open scoped Simplicial

universe u

-- no global `HasDerivedCategory` instance on these categories of sheaves of modules
attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

/-- The pullback of the degree-`k` object of the system of a pair to `X_k` is `L X(τᵏₖ)^* K₀`. -/
private theorem nonempty_derivedPullback_pairDerivedModuleSystem_iso
    (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (e : (derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).obj Pr.obj ≅ K₀)
    (k : SimplexCategory) :
    Nonempty ((derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) k)
      (strictComponentRingedToposHom X k)).obj
        (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).obj k) ≅
      (derivedPullback (spacesEtaleRingedToposHom
        (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀) :=
  ⟨(strictComponentDerivedTransitionIso X
        (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len))).app Pr.obj ≪≫
      (derivedPullback (spacesEtaleRingedToposHom
        (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).mapIso e⟩

/-- **The objects of the system of a pair have no negative self-extensions** when the objects
`K_k = L X(τᵏₖ)^* K₀` they realize to have none. -/
theorem pairDerivedModuleSystem_shift_hom_eq_zero
    (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (e : (derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).obj Pr.obj ≅ K₀)
    (hExt : ∀ (k : SimplexCategory) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback (spacesEtaleRingedToposHom
          (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀ ⟶
        (shiftFunctor (DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op k))).Modules)
          i).obj ((derivedPullback (spacesEtaleRingedToposHom
          (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀),
        g = 0)
    (k : SimplexCategory) (t : ℕ) (ht : 0 < t)
    (f : (shiftFunctor (DerivedCategory
        ((strictSituation X).componentRingedTopos (strictStructureSheaf X) k).Modules) (t : ℤ)).obj
          (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).obj k) ⟶
      ((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).obj k) :
    f = 0 := by
  obtain ⟨ι⟩ := nonempty_derivedPullback_pairDerivedModuleSystem_iso X Pr K₀ e k
  have := derivedPullback_commShift (strictComponentRingedToposHom X k)
  have h1 : (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) k)
      (strictComponentRingedToposHom X k)).Faithful := inferInstance
  have h2 : (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) k)
      (strictComponentRingedToposHom X k)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have hK : ∀ g : (shiftFunctor (DerivedCategory
        (spacesEtaleRingedTopos B S hS (X.obj (op k))).Modules) (t : ℤ)).obj
          ((derivedPullback (spacesEtaleRingedToposHom
            (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀) ⟶
        (derivedPullback (spacesEtaleRingedToposHom
            (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀,
      g = 0 := fun g ↦
    eq_zero_of_forall_hom_shift_neg_eq_zero
      (C := DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op k))).Modules) (t : ℤ)
      (hExt k (-(t : ℤ)) (by lia)) g
  exact Functor.eq_zero_of_shift_hom_eq_zero_of_faithful
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) k)
      (strictComponentRingedToposHom X k))
    ι (t : ℤ) hK f

/-- **The system of a pair is the system of a cartesian object** (Stacks 0D9T, flatness-free):
when the objects `K_k = L X(τᵏₖ)^* K₀` have no negative self-extensions, there is a cartesian
object `K'` of the derived category of the total site of the strict components whose simplicial
system is isomorphic to the system of Stacks 0GMF of the pair. -/
theorem exists_isCartesianDerivedModule_pairDerivedModuleSystem
    (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (e : (derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).obj Pr.obj ≅ K₀)
    (hExt : ∀ (k : SimplexCategory) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback (spacesEtaleRingedToposHom
          (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀ ⟶
        (shiftFunctor (DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op k))).Modules)
          i).obj ((derivedPullback (spacesEtaleRingedToposHom
          (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀),
        g = 0) :
    ∃ K' : DerivedCategory ((strictSituation X).totalRingedTopos (strictStructureSheaf X)).Modules,
      (strictSituation X).IsCartesianDerivedModule (strictStructureSheaf X) K' ∧
        Nonempty ((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr ≅
          (strictSituation X).derivedModuleSystem (strictStructureSheaf X) K') :=
  SimplicialSiteSituation.exists_isCartesianDerivedModule_realizing_moduleSystem _
    ((strictSituation X).pairDerivedModuleSystem_cartesian (strictStructureSheaf X) Pr)
    (pairDerivedModuleSystem_shift_hom_eq_zero X Pr K₀ e hExt)

/-! ### Quasi-coherence of the glued object -/

/-- **Exactness of the pullback along a transition of the strict components**: the pullback of
modules along the transition of the strict components along `φ` is exact when that along `X(φ)`
is. -/
theorem preservesFiniteLimits_strictTransitionPullbackModules {m n : SimplexCategory} (φ : m ⟶ n)
    (hφ : PreservesFiniteLimits
      (spacesEtaleRingedToposHom (X.map φ.op)).toModulesHom.pullbackModules) :
    PreservesFiniteLimits ((strictSituation X).transitionRingedToposHom
      (strictStructureSheaf X) φ).toModulesHom.pullbackModules := by
  have e := (RingedToposHom.pullbackModulesCompIso (strictComponentRingedToposHom X n)
      ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)).symm ≪≫
    strictComponentPullbackModulesTransitionIso X φ ≪≫
    RingedToposHom.pullbackModulesCompIso (spacesEtaleRingedToposHom (X.map φ.op))
      (strictComponentRingedToposHom X m)
  have :=
    RingedToposHom.isEquivalence_pullbackModules_of_isEquivalence_ringedToposEquivalenceModules
      (strictComponentRingedToposHom X m)
  have :=
    RingedToposHom.isEquivalence_pullbackModules_of_isEquivalence_ringedToposEquivalenceModules
      (strictComponentRingedToposHom X n)
  have : PreservesFiniteLimits
      ((strictComponentRingedToposHom X m).toModulesHom.pullbackModules ⋙
        (spacesEtaleRingedToposHom (X.map φ.op)).toModulesHom.pullbackModules) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      (((strictSituation X).transitionRingedToposHom
          (strictStructureSheaf X) φ).toModulesHom.pullbackModules ⋙
        (strictComponentRingedToposHom X n).toModulesHom.pullbackModules) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (strictComponentRingedToposHom X n).toModulesHom.pullbackModules

/-- **The cohomology modules of a cartesian object are cartesian** (Stacks 0D7L (2)) when the
face maps of `X` have exact pullbacks. -/
theorem isCartesianModule_homology_of_isCartesianDerivedModule
    (hface : ∀ (k : ℕ) (i : Fin (k + 2)), PreservesFiniteLimits
      (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ i).op)).toModulesHom.pullbackModules)
    (K : DerivedCategory ((strictSituation X).totalRingedTopos (strictStructureSheaf X)).Modules)
    (hK : (strictSituation X).IsCartesianDerivedModule (strictStructureSheaf X) K) (q : ℤ) :
    (strictSituation X).IsCartesianModule (strictStructureSheaf X)
      ((DerivedCategory.homologyFunctor
        ((strictSituation X).totalRingedTopos (strictStructureSheaf X)).Modules q).obj K) :=
  ((strictSituation X).isCartesianModule_iff_faces (strictStructureSheaf X) _).2 fun k i ↦
    ((strictSituation X).isIso_derivedComponentModuleTransition_app_iff (strictStructureSheaf X)
      (SimplexCategory.δ i) (preservesFiniteLimits_strictTransitionPullbackModules X _ (hface k i))
      K).1 (hK _) q

/-- An object of the derived category of a strict component has quasi-coherent cohomology when
its realization `L realize_n^*` is isomorphic to one with quasi-coherent cohomology
(Stacks 03DM). -/
theorem derivedCategoryB_isQuasicoherentOnSite_of_strictComponent_iso (n : SimplexCategory)
    (M : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n).Modules)
    (N : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op n))).Modules)
    (ι : (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
      (strictComponentRingedToposHom X n)).obj M ≅ N)
    (hN : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS (X.obj (op n))).O))
      N) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n).O)) M :=
  open Stacks.Cohomology.CohomologicalDescent in
  OfRingedToposHom.derivedCategoryB_isQuasicoherentOnSite_of_derivedPullback
    (strictComponentRingedToposHom X n) M (fun q ↦ SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso ι).symm (hN q))

/-- **The components of the cohomology modules of the glued object are quasi-coherent** when the
objects `K_k = L X(τᵏₖ)^* K₀` have quasi-coherent cohomology. -/
theorem isQuasicoherentOnSite_componentModule_homology
    (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (e : (derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).obj Pr.obj ≅ K₀)
    (hK : ∀ k : SimplexCategory, DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS (X.obj (op k))).O))
      ((derivedPullback (spacesEtaleRingedToposHom
          (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀))
    (K' : DerivedCategory ((strictSituation X).totalRingedTopos (strictStructureSheaf X)).Modules)
    (eT : (strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr ≅
      (strictSituation X).derivedModuleSystem (strictStructureSheaf X) K')
    (n : SimplexCategory) (q : ℤ) :
    ((strictSituation X).componentModule (strictStructureSheaf X)
      ((DerivedCategory.homologyFunctor
        ((strictSituation X).totalRingedTopos (strictStructureSheaf X)).Modules q).obj K')
      n).IsQuasicoherentOnSite := by
  obtain ⟨ι⟩ := nonempty_derivedPullback_pairDerivedModuleSystem_iso X Pr K₀ e n
  have hT := derivedCategoryB_isQuasicoherentOnSite_of_strictComponent_iso X n
    (((strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr).obj n) _ ι
    (hK n)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      ((strictSituation X).componentModulesRestriction (strictStructureSheaf X) n)
        q).app K').symm ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso
        ((SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation n).mapIso eT.symm)).symm
    (hT q)

/-- **The glued object has quasi-coherent cohomology** (Stacks 0D7M) when the face maps of `X`
have exact pullbacks and the objects `K_k = L X(τᵏₖ)^* K₀` have quasi-coherent cohomology. -/
theorem derivedCategoryB_isQuasicoherentOnSite_of_pairDerivedModuleSystem_iso
    (hface : ∀ (k : ℕ) (i : Fin (k + 2)), PreservesFiniteLimits
      (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ i).op)).toModulesHom.pullbackModules)
    (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (e : (derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).obj Pr.obj ≅ K₀)
    (hK : ∀ k : SimplexCategory, DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS (X.obj (op k))).O))
      ((derivedPullback (spacesEtaleRingedToposHom
          (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀))
    (K' : DerivedCategory ((strictSituation X).totalRingedTopos (strictStructureSheaf X)).Modules)
    (hK' : (strictSituation X).IsCartesianDerivedModule (strictStructureSheaf X) K')
    (eT : (strictSituation X).pairDerivedModuleSystem (strictStructureSheaf X) Pr ≅
      (strictSituation X).derivedModuleSystem (strictStructureSheaf X) K') :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((strictSituation X).totalRingedTopos (strictStructureSheaf X)).O)) K' := fun q ↦
  open SimplicialSiteSituation in
  (isQuasicoherentOnSite_iff_isCartesianModule_and_isQuasicoherentOnSite_componentModule
    (strictSituation X) (strictStructureSheaf X) _).2
    ⟨isCartesianModule_homology_of_isCartesianDerivedModule X hface K' hK' q,
      fun n ↦ isQuasicoherentOnSite_componentModule_homology X Pr K₀ e hK K' eT n q⟩

/-- Derived pullback along the transition of a simplex map equal to an identity is isomorphic
to the identity on objects. -/
theorem nonempty_derivedTransitionPullback_obj_iso_of_eq_id {n : SimplexCategory} (τ : n ⟶ n)
    (hτ : τ = 𝟙 n)
    (P : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n).Modules) :
    Nonempty
      (((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) τ).obj P ≅ P) := by
  subst hτ
  have hφ := (strictSituation X).isFlat_transitionRingedToposHom_id (strictStructureSheaf X) n
  let : PreservesFiniteLimits ((strictSituation X).transitionRingedToposHom
      (strictStructureSheaf X) (𝟙 n)).toModulesHom.pullbackModules :=
    ((exactFunctor_iff _).1 ((strictSituation X).exactFunctor_transitionPullbackModules'
      (strictStructureSheaf X) (𝟙 n) hφ)).1
  let : PreservesFiniteColimits ((strictSituation X).transitionRingedToposHom
      (strictStructureSheaf X) (𝟙 n)).toModulesHom.pullbackModules :=
    AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
      ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) (𝟙 n))
  exact ⟨(((strictSituation X).derivedTransitionPullbackIsoMapDerivedCategory
      (strictStructureSheaf X) (𝟙 n) hφ ≪≫
    derivedNatIso ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X)
      (𝟙 n)).toModulesHom.pullbackModules
      (𝟭 (((strictSituation X).componentRingedTopos (strictStructureSheaf X) n).Modules))
      ((strictSituation X).transitionPullbackModulesIdToposIso (strictStructureSheaf X) n) ≪≫
    derivedIdIso).app P)⟩

/-- **Gluing on the strict components.** Let `K₀ ∈ D(𝒪_{X_0})` and `α` satisfy the cocycle
condition on `X_2`, let the face maps of `X` have exact pullbacks, let every
`K_k = L X(τᵏₖ)^* K₀` have quasi-coherent cohomology and no negative self-extensions. Then there
is an object `K'` of the derived category of the total site of the strict components with
quasi-coherent cohomology whose degree-zero component realizes to `K₀`. -/
theorem exists_strictGluing
    (hface : ∀ (k : ℕ) (i : Fin (k + 2)), PreservesFiniteLimits
      (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ i).op)).toModulesHom.pullbackModules)
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (α : (derivedPullback (spacesEtaleRingedToposHom
        (X.map (SimplexCategory.δ (1 : Fin 2)).op))).obj K₀ ≅
      (derivedPullback (spacesEtaleRingedToposHom
        (X.map (SimplexCategory.δ (0 : Fin 2)).op))).obj K₀)
    (hα : SpacesEtaleDerivedCocycle X K₀ α)
    (hK : ∀ k : SimplexCategory, DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS (X.obj (op k))).O))
      ((derivedPullback (spacesEtaleRingedToposHom
          (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀))
    (hExt : ∀ (k : SimplexCategory) (i : ℤ), i < 0 →
      ∀ g : (derivedPullback (spacesEtaleRingedToposHom
          (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀ ⟶
        (shiftFunctor (DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op k))).Modules)
          i).obj ((derivedPullback (spacesEtaleRingedToposHom
          (X.map (SimplexCategory.const (SimplexCategory.mk 0) k (Fin.last k.len)).op))).obj K₀),
        g = 0) :
    ∃ K' : DerivedCategory ((strictSituation X).totalRingedTopos (strictStructureSheaf X)).Modules,
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            ((strictSituation X).totalRingedTopos (strictStructureSheaf X)).O)) K' ∧
      Nonempty ((derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) ⦋0⦌)
        (strictComponentRingedToposHom X ⦋0⦌)).obj
          (((strictSituation X).derivedComponentModuleRestriction (strictStructureSheaf X)
            ⦋0⦌).obj K') ≅ K₀) :=
  (exists_derivedModuleCocyclePair X K₀ α hα).elim fun Pr hPr ↦ hPr.elim fun e _ ↦
    (exists_isCartesianDerivedModule_pairDerivedModuleSystem X Pr K₀ e hExt).elim
      fun K' hK' ↦ hK'.2.elim fun eT ↦
        (nonempty_derivedTransitionPullback_obj_iso_of_eq_id X
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) (Fin.last 0))
          (SimplexCategory.Hom.ext _ _
            (OrderHom.ext _ _ (funext fun _ ↦ Subsingleton.elim (α := Fin 1) _ _)))
          Pr.obj).elim fun ι ↦
          ⟨K', derivedCategoryB_isQuasicoherentOnSite_of_pairDerivedModuleSystem_iso X hface Pr K₀ e
              hK K' hK'.1 eT,
            ⟨(derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌)))
              (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) ⦋0⦌)
              (strictComponentRingedToposHom X ⦋0⦌)).mapIso
                ((SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation ⦋0⦌).mapIso
                  eT.symm ≪≫ ι) ≪≫ e⟩⟩

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
