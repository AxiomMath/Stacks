module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsDerivedSectionsAmplitude

/-!
# The alternating Čech complex computes `Hᵐ(RΓ(X, ℱ))`, linearly over the base

Let `f : X ⟶ Spec A` be separated, `ℱ` a quasi-coherent `𝒪_X`-module and `U` a finite affine
open covering of `X`. The homology of the alternating Čech complex of `ℱ` on `U`, a complex of
`A`-modules, is the cohomology of the object `RΓ(X, ℱ[0])` of `D(Γ(Spec A, 𝒪))`, with scalars
restricted along `A ⟶ Γ(Spec A, 𝒪)`. This is the bridge between the two forms the cohomology
modules take in the proof of [Stacks, Tag 0G8J]: the Čech form, in which the de Rham differential
is an `A`-linear map of complexes (`Stacks.Cech.alternatingCechModulePush`), and the derived form,
in which the Künneth isomorphism of [Stacks, Tag 0FU4] lives
(`AlgebraicGeometry.TopDegreeDifferential.formsKunnethTopDegreeIso`).

## Main definitions

* `Stacks.Cech.alternatingCechModuleHomologyIsoSectionsOverBase`: the comparison, over `A`.
* `Stacks.Cech.alternatingCechModuleHomologyRestrictIsoSectionsOverBase`: the comparison, over
  `Γ(Spec A, 𝒪)`, the ring over which the derived Künneth isomorphism is linear.

## References

* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase singleD)

open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I : Type u}
  [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)
  [F.IsQuasicoherent] [IsSeparated f] (hUaff : ∀ i, IsAffineOpen (U i))

/-- **The homology of the alternating Čech complex of an affine covering is the cohomology of
`RΓ(X, ℱ[0])`, `A`-linearly** ([Stacks, Tags 01FM, 01XD]): both are the right derived functors
of global sections at `ℱ`, read over `A` through `A ⟶ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`
(`Stacks.Cech.alternatingCechModuleHomologyIsoCohomology` and
`AlgebraicGeometry.homologyIso_sectionsOverBase`). -/
def alternatingCechModuleHomologyIsoSectionsOverBase (m : ℕ) :
    (alternatingCechModuleComplex f U F).homology m ≅
      (ModuleCat.restrictScalars.{u} (toSpecΓ (CommRingCat.of A)).hom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace))
          (m : ℤ)).obj ((sectionsOverBase f.toLRSHom.toShHom).obj (singleD F))) :=
  alternatingCechModuleHomologyIsoCohomology f U hU F hUaff m ≪≫
    ModuleCat.restrictScalarsComp'App (toSpecΓ (CommRingCat.of A)).hom
      (structureSheafGlobalHom f) (globalRingHom f).hom rfl _ ≪≫
    (ModuleCat.restrictScalars.{u} (toSpecΓ (CommRingCat.of A)).hom).mapIso
      (((homologyIso_sectionsOverBase f m).app F).symm ≪≫
        (DerivedCategory.homologyFunctor _ (m : ℤ)).mapIso
          ((sectionsOverBase f.toLRSHom.toShHom).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F)))

/-- The ring map `A ⟶ Γ(Spec A, 𝒪)` is inverse to `Γ(Spec A, 𝒪) ≅ A`. -/
theorem toSpecΓ_comp_ΓSpecIso_hom (A : CommRingCat.{u}) :
    (toSpecΓ A).hom.comp (Scheme.ΓSpecIso A).hom.hom = RingHom.id _ := by
  have h : toSpecΓ A = (Scheme.ΓSpecIso A).inv := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  rw [h]
  ext x
  exact congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso A).hom_inv_id

/-- **The homology of the alternating Čech complex, read over `Γ(Spec A, 𝒪)`, is the cohomology
of `RΓ(X, ℱ[0])`**: `Stacks.Cech.alternatingCechModuleHomologyIsoSectionsOverBase` with scalars
restricted back along `Γ(Spec A, 𝒪) ≅ A`. -/
def alternatingCechModuleHomologyRestrictIsoSectionsOverBase (m : ℕ) :
    (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom).obj
        ((alternatingCechModuleComplex f U F).homology m) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace))
        (m : ℤ)).obj ((sectionsOverBase f.toLRSHom.toShHom).obj (singleD F)) :=
  (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom).mapIso
      (alternatingCechModuleHomologyIsoSectionsOverBase f U hU F hUaff m) ≪≫
    (ModuleCat.restrictScalarsComp'App (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (toSpecΓ (CommRingCat.of A)).hom (RingHom.id _)
      (toSpecΓ_comp_ΓSpecIso_hom (CommRingCat.of A)).symm _).symm ≪≫
    ModuleCat.restrictScalarsId'App (RingHom.id _) rfl _

end Stacks.Cech

end
