module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Extension of scalars, universe lifts, and the honest tensor product

Let `R → S` be a map of commutative rings given by an algebra structure. Extension of scalars
`ModuleCat.extendScalars (algebraMap R S)` sends a module `M` to `S ⊗_R M`, but the `R`-module
structure it puts on `S` is `Module.compHom S (algebraMap R S)` rather than `Algebra.toModule`;
the two agree by `Algebra.smul_def`, yet not syntactically, so a statement about
`(ModuleCat.extendScalars (algebraMap R S)).obj M` and a statement about `S ⊗[R] M` are not
interchangeable. This file crosses that boundary, and crosses a universe lift at the same time:
a module in a small universe is lifted into the category extension of scalars acts on, and
extension of scalars then has to be commuted past the lift.

## Main definitions

* `ModuleCat.extendScalarsAlgebraEquiv`: `(extendScalars (algebraMap R S)).obj M ≃ₗ[S] S ⊗[R] M`,
  with the module universe independent of the two ring universes.
* `ModuleCat.extendScalarsUliftIso`: `(extendScalars (algebraMap R S)).obj (ULift M) ≅
  ULift (S ⊗[R] M)`, the composite of that identification with the two universe lifts.

## Main results

* `ModuleCat.extendScalarsUliftIso_hom_tmul`: the identification is `s ⊗ up m ↦ up (s ⊗ m)`.
* `ModuleCat.extendScalarsUliftIso_naturality`: it is natural, the map on the right being the
  base change `LinearMap.baseChange` of the map on the left.

## Implementation notes

`PseudoCoherence.extendScalarsAlgebraMapObjIso` is the first identification for a module whose
universe is that of both rings; the version here repeats its construction with the three
universes independent, which is what a module category accommodating a universe lift needs.

The naturality statement is phrased with `LinearMap.baseChange`, the honest base change of an
`R`-linear map, on the right-hand side.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe u₁ u₂ v w

namespace ModuleCat

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]

/-- **Extension of scalars along `algebraMap R S` is the tensor product `S ⊗[R] -`.** The
identification is the identity on elements, between the tensor product formed with the `R`-module
structure `Module.compHom S (algebraMap R S)` on `S` and the one formed with `Algebra.toModule`. -/
def extendScalarsAlgebraEquiv (M : ModuleCat.{w} R) :
    ((ModuleCat.extendScalars (algebraMap R S)).obj M) ≃ₗ[S] S ⊗[R] M := by
  have hcomm : SMulCommClass R S ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (ModuleCat.of S S)) :=
    ⟨fun r s t ↦ mul_left_comm (algebraMap R S r) s (t : S)⟩
  let e : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { AddEquiv.refl S with map_smul' := fun r s ↦ (Algebra.smul_def (R := R) (A := S) r s).symm }
  let e' : ((ModuleCat.extendScalars (algebraMap R S)).obj M) ≃+ (S ⊗[R] M) :=
    (TensorProduct.congr e (LinearEquiv.refl R M)).toAddEquiv
  refine { e' with map_smul' := ?_ }
  change ∀ (s : S) (z : (ModuleCat.extendScalars (algebraMap R S)).obj M),
    e' (s • z) = s • e' z
  intro s z
  induction z using TensorProduct.induction_on with
  | zero =>
      calc
        e' (s • 0) = e' 0 := congrArg e' (smul_zero s)
        _ = 0 := e'.map_zero
        _ = s • e' 0 := by rw [e'.map_zero, smul_zero]
  | tmul t m => rfl
  | add z z' hz hz' =>
      calc
        e' (s • (z + z')) = e' (s • z + s • z') := congrArg e' (smul_add s z z')
        _ = e' (s • z) + e' (s • z') := e'.map_add _ _
        _ = s • e' z + s • e' z' := congrArg₂ (· + ·) hz hz'
        _ = s • (e' z + e' z') := (smul_add s _ _).symm
        _ = s • e' (z + z') := congrArg (fun x ↦ s • x) (e'.map_add z z').symm

/-- `ModuleCat.extendScalarsAlgebraEquiv` sends `s ⊗ m` to `s ⊗ m`. -/
@[simp]
lemma extendScalarsAlgebraEquiv_apply_tmul (M : ModuleCat.{w} R) (s : S) (m : M) :
    extendScalarsAlgebraEquiv (S := S) M (s ⊗ₜ[R, algebraMap R S] m) = s ⊗ₜ[R] m := rfl

/-- **Extension of scalars commutes with a universe lift of the module.** The identification
sends `s ⊗ up m` to `up (s ⊗ m)`. -/
def extendScalarsUliftIso (M : ModuleCat.{w} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj ((ModuleCat.uliftFunctor.{v} R).obj M) ≅
      (ModuleCat.uliftFunctor.{v} S).obj (ModuleCat.of S (S ⊗[R] M)) :=
  LinearEquiv.toModuleIso
    (extendScalarsAlgebraEquiv ((ModuleCat.uliftFunctor.{v} R).obj M) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
        (ULift.moduleEquiv (R := R) (M := M)) ≪≫ₗ
      (ULift.moduleEquiv (R := S) (M := S ⊗[R] M)).symm)

/-- `ModuleCat.extendScalarsUliftIso` sends `s ⊗ up m` to `up (s ⊗ m)`. -/
@[simp]
lemma extendScalarsUliftIso_hom_tmul (M : ModuleCat.{w} R) (s : S) (m : M) :
    (extendScalarsUliftIso.{u₁, u₂, v, w} (S := S) M).hom
        (s ⊗ₜ[R, algebraMap R S] (ULift.up.{v} m)) = ULift.up (s ⊗ₜ[R] m) := rfl

/-- **The identification of extension of scalars past a universe lift is natural**, the
comparison on the lifted side being the base change of the map. -/
lemma extendScalarsUliftIso_naturality {M N : ModuleCat.{w} R} (g : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap R S)).map ((ModuleCat.uliftFunctor.{v} R).map g) ≫
        (extendScalarsUliftIso.{u₁, u₂, v, w} (S := S) N).hom =
      (extendScalarsUliftIso.{u₁, u₂, v, w} (S := S) M).hom ≫
        (ModuleCat.uliftFunctor.{v} S).map
          (ModuleCat.ofHom (LinearMap.baseChange S g.hom)) := by
  ext z
  show ULift.up ((1 : S) ⊗ₜ[R] g.hom z.down) =
    ULift.up ((LinearMap.baseChange S g.hom) ((1 : S) ⊗ₜ[R] z.down))
  rw [LinearMap.baseChange_tmul]

end ModuleCat

end
