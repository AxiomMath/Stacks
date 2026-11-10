module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# Derived coextension of scalars along a projective algebra needs no derived correction

Let `f : R →+* B` make `B` a projective `R`-module.  Then coextension of scalars
`Hom_R(B, -) : Mod_R ⥤ Mod_B` is exact, and the functor it induces termwise on derived categories
agrees with `Dualizing.derivedHom f = RHom_R(B, -)`. In particular `RHom_R(B, M)` is concentrated
in degree zero, where it is `Hom_R(B, M)`.

## Main results

* `Dualizing.preservesFiniteColimits_coextendScalars_of_projective`: coextension of scalars
  along a projective algebra is exact.
* `Dualizing.coextendScalarsMapDerivedCategoryIsoDerivedHom_of_projective`: `RHom_R(B, -)` is
  the termwise extension of `Hom_R(B, -)` to derived categories.
* `Dualizing.derivedHomObjSingleIso`: `RHom_R(B, M[0]) ≅ Hom_R(B, M)[0]`.

## References

* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- If an `R`-algebra `B` is a projective `R`-module, it is projective for the `R`-module
structure that `ModuleCat.restrictScalars` puts on it. -/
theorem projective_restrictScalars_algebraMap_of_projective {R B : Type u} [CommRing R]
    [CommRing B] [Algebra R B] [Module.Projective R B] :
    Module.Projective R
      ((ModuleCat.restrictScalars.{u} (algebraMap R B)).obj (ModuleCat.of B B)) := by
  let e : B ≃ₗ[R]
      ((ModuleCat.restrictScalars.{u} (algebraMap R B)).obj (ModuleCat.of B B)) :=
    { toFun := fun b ↦ (b : B)
      invFun := fun b ↦ (b : B)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r b ↦ by
        change _ = algebraMap R B r • (b : B)
        rw [smul_eq_mul, Algebra.smul_def] }
  exact Module.Projective.of_equiv' e

variable {R B : Type u} [CommRing R] [CommRing B]

/-- Coextension of scalars along a projective algebra preserves epimorphisms. -/
theorem preservesEpimorphisms_coextendScalars_of_projective (f : R →+* B)
    (hproj : Module.Projective R
      ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B B))) :
    (ModuleCat.coextendScalars.{u, u, u} f).PreservesEpimorphisms := by
  constructor
  intro M M' g hg
  rw [ModuleCat.epi_iff_surjective]
  intro k
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property g.hom
    (ModuleCat.CoextendScalars.equiv f M' k) ((ModuleCat.epi_iff_surjective g).mp hg)
  refine ⟨(ModuleCat.CoextendScalars.equiv f M).symm φ, ?_⟩
  exact ModuleCat.CoextendScalars.ext (LinearMap.ext fun b ↦ DFunLike.congr_fun hφ b)

/-- Coextension of scalars along a projective algebra preserves finite colimits. -/
theorem preservesFiniteColimits_coextendScalars_of_projective (f : R →+* B)
    (hproj : Module.Projective R
      ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B B))) :
    PreservesFiniteColimits (ModuleCat.coextendScalars.{u, u, u} f) := by
  have : (ModuleCat.coextendScalars.{u, u, u} f).PreservesEpimorphisms :=
    preservesEpimorphisms_coextendScalars_of_projective f hproj
  have : (ModuleCat.coextendScalars.{u, u, u} f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- When `f : R →+* B` makes `B` a projective `R`-module, the functor that coextension of
scalars along `f` induces termwise on derived categories is isomorphic to
`Dualizing.derivedHom f`. -/
noncomputable def coextendScalarsMapDerivedCategoryIsoDerivedHom_of_projective (f : R →+* B)
    (hproj : Module.Projective R
      ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B B))) :
    letI := preservesFiniteColimits_coextendScalars_of_projective f hproj
    (ModuleCat.coextendScalars.{u, u, u} f).mapDerivedCategory ≅ derivedHom.{u, u, u} f := by
  letI := preservesFiniteColimits_coextendScalars_of_projective f hproj
  let F := ModuleCat.coextendScalars.{u, u, u} f
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  have hptw : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor W :=
    coextendScalars_hasPointwiseRightDerivedFunctor.{u, u, u} f
  have hF : F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv W :=
    Functor.isRightDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  exact Functor.rightDerivedUnique F.mapDerivedCategory
    ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
      DerivedCategory.Qh W)
    F.mapDerivedCategoryFactorsh.inv
    ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh W) W

/-- For `f : R →+* B` making `B` a projective `R`-module and an `R`-module `M`, the value of
derived coextension of scalars at `M` placed in degree zero is `Hom_R(B, M)` placed in degree
zero. -/
noncomputable def derivedHomObjSingleIso (f : R →+* B)
    (hproj : Module.Projective R
      ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B B)))
    (M : ModuleCat.{u} R) :
    (derivedHom.{u, u, u} f).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        ((ModuleCat.coextendScalars.{u, u, u} f).obj M) := by
  letI := preservesFiniteColimits_coextendScalars_of_projective f hproj
  exact ((coextendScalarsMapDerivedCategoryIsoDerivedHom_of_projective f hproj).app _).symm ≪≫
    ((ModuleCat.coextendScalars.{u, u, u} f).mapDerivedCategorySingleFunctor 0).app M

end Dualizing

end
