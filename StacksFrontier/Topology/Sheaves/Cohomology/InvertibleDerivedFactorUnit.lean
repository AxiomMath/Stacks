module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedIdempotentSplitting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The factors of a product decomposition as images of idempotents

Let `(e_n)` be a locally finite complete family of orthogonal idempotents of `Γ(X, 𝒪_X)`. The
`n`-th factor `𝒪_n = e_n 𝒪_X`, read as an `𝒪_X`-module, is the image of multiplication by `e_n`
on `𝒪_X`. The image of an idempotent is preserved by every functor.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.InvertibleDerived

section Generic

variable {C : Type*} [Category* C] [Preadditive C] [HasKernels C]

/-- An object retracting onto a summand cut out by an idempotent is the image of the idempotent. -/
public def isoSplitObjOfRetract {A B : C} (ι : A ⟶ B) (π : B ⟶ A) (h₁ : ι ≫ π = 𝟙 A)
    {p : B ⟶ B} (h₂ : π ≫ ι = p) : A ≅ splitObj p where
  hom := kernel.lift _ ι (by
    rw [Preadditive.comp_sub, Category.comp_id, ← h₂, ← Category.assoc, h₁, Category.id_comp,
      sub_self])
  inv := splitι p ≫ π
  hom_inv_id := by rw [← Category.assoc, kernel.lift_ι, h₁]
  inv_hom_id := by
    have hp : p ≫ p = p := by
      rw [← h₂, Category.assoc, ← Category.assoc ι, h₁, Category.id_comp]
    rw [← cancel_mono (splitι p), Category.assoc, kernel.lift_ι, Category.assoc, h₂,
      Category.id_comp, splitι_comp hp]

variable {D : Type*} [Category* D] [Preadditive D] [HasKernels D]

/-- **Every functor preserves the image of an idempotent.** -/
@[sga "4 I 8.7.8" "special case"]
public def mapSplitObjIso (F : C ⥤ D) {K : C} {p : K ⟶ K} (hp : p ≫ p = p) :
    F.obj (splitObj p) ≅ splitObj (F.map p) :=
  isoSplitObjOfRetract (F.map (splitι p)) (F.map (splitπ hp))
    (by rw [← F.map_comp, splitι_splitπ, F.map_id]) (by rw [← F.map_comp, splitπ_splitι])

end Generic

variable {X : RingedSpace.{u, u}}

namespace LocallyFiniteIdempotents

variable (E : LocallyFiniteIdempotents X) (n : ℤ)

/-- The `n`-th factor of `𝒪_X`, as an `𝒪_X`-module along `s ↦ e_n s`. -/
public abbrev factorUnit : Mod X.sheaf :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (E.proj n))).obj
      (SheafOfModules.unit _)

/-- The projection `𝒪_X ⟶ 𝒪_n`, `s ↦ e_n s`, as a map of `𝒪_X`-modules. -/
public def unitToFactor : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⟶
    E.factorUnit n :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (E.toCornerHom n U.unop).toAddMonoidHom
      naturality := fun U V f => by
        ext s
        exact (E.toCorner_naturality n f s).symm }
    fun U r m => (E.toCornerHom n U.unop).map_mul r m⟩

/-- The inclusion `𝒪_n ⟶ 𝒪_X` of the `n`-th factor, as a map of `𝒪_X`-modules. -/
public def factorToUnit : E.factorUnit n ⟶
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun c => (c : E.Corner n U.unop).1
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      naturality := fun U V f => by
        ext c
        rfl }
    fun U r c => by
      have h : ∀ r' : X.presheaf.obj U, (globalRes (E.e n) U.unop * r') *
          (c : E.Corner n U.unop).1 = r' * (c : E.Corner n U.unop).1 := fun r' => by
        rw [mul_comm (globalRes (E.e n) U.unop) r', mul_assoc, E.mem_corner n c]
      exact h r⟩

/-- The inclusion `𝒪_n ⟶ 𝒪_X` followed by the projection `𝒪_X ⟶ 𝒪_n` is the identity of `𝒪_n`. -/
public theorem factorToUnit_unitToFactor :
    E.factorToUnit n ≫ E.unitToFactor n = 𝟙 _ := by
  ext U c
  exact LocallyFiniteIdempotents.Corner.ext E (E.mem_corner n c)

/-- The projection `𝒪_X ⟶ 𝒪_n` followed by the inclusion `𝒪_n ⟶ 𝒪_X` is multiplication by `e_n`
on `𝒪_X`. -/
public theorem unitToFactor_factorToUnit :
    E.unitToFactor n ≫ E.factorToUnit n = smulHom (E.e n) _ := by
  ext U
  exact (E.toCorner_val n 1).trans (smul_eq_mul _ _).symm

/-- **The `n`-th factor is the image of multiplication by `e_n` on `𝒪_X`.** -/
public def toOXModUnitIso :
    (E.productDecomposition.toOXMod n).obj (SheafOfModules.unit _) ≅
      splitObj (smulHom (E.e n) (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        X.sheaf))) :=
  (eqToIso (congrArg SheafOfModules.restrictScalars (E.productDecomposition_proj n))).app _ ≪≫
    isoSplitObjOfRetract (E.factorToUnit n) (E.unitToFactor n) (E.factorToUnit_unitToFactor n)
      (E.unitToFactor_factorToUnit n)

end LocallyFiniteIdempotents

end Stacks.Cohomology.InvertibleDerived

end
