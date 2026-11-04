module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksFrontier.RingTheory.Flat.LazardDevissage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An `A`-linear endofunctor of `A`-modules is tensoring, on flat modules

Let `A` be a commutative ring and let `Φ : ModuleCat.{u} A ⥤ ModuleCat.{u} A` be an additive
`A`-linear functor which preserves filtered colimits.  There is a canonical map

`Φ(A) ⊗_A M ⟶ Φ(M)`,

natural in `M`, sending `x ⊗ m` to `Φ(a ↦ a • m)(x)`.  It is an isomorphism whenever `M` is
**flat** over `A`.

This is the abstract content of the proof of **Stacks 073K, part (2)**: for a cartesian square
of algebraic spaces over affine bases `Y = Spec A` and `Y' = Spec B` with `g` flat, the
comparison map `H^i(X, ℱ) ⊗_A B ⟶ H^i(X', ℱ')` that part (2) asserts to be invertible is the
component at `B` of such a map, and `B` is flat over `A`.  No weakening of the hypotheses of
073K is involved: the only property of `B` that enters is its flatness, which is the source's
hypothesis on `g`.

## Main definitions

* `Stacks.FlatDevissage.spanHom`: the morphism `A ⟶ M` of `A`-modules determined by an element
  of `M`, that is `a ↦ a • m`.
* `Stacks.FlatDevissage.tensorComparison`: **the canonical map** `Φ(A) ⊗_A - ⟶ Φ`, as a natural
  transformation out of `CategoryTheory.MonoidalCategory.tensorLeft (Φ.obj A)`.

## Main results

* `Stacks.FlatDevissage.tensorComparisonApp_tmul`: the defining formula
  `x ⊗ m ↦ Φ(spanHom m)(x)`.
* `Stacks.FlatDevissage.tensorComparison_app_unit`: at `M = A` the map is the right unitor, hence
  invertible.
* `Stacks.FlatDevissage.isIso_tensorComparison_app_of_flat`: **the comparison is invertible at
  every flat module.**

## Implementation notes

`A`-linearity of `Φ` — `CategoryTheory.Functor.Linear A Φ` — is what makes the formula
`x ⊗ m ↦ Φ(spanHom m)(x)` additive and homogeneous in `m`: `spanHom (a • m) = a • spanHom m`, and
an `A`-linear functor turns that scalar out of `Φ.map`.  Additivity alone does not suffice, and
the formula is not well defined on the tensor product without it.

Preservation of filtered colimits is required of `Φ` only; the other functor in the dévissage is
`tensorLeft (Φ.obj A)`, which preserves *all* colimits because `ModuleCat.{u} A` is monoidal
closed (`CategoryTheory.MonoidalClosed`), and is additive because the monoidal structure is
preadditive.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Stacks.FlatDevissage

universe u

variable {A : Type u} [CommRing A]

/-- The morphism `A ⟶ M` of `A`-modules determined by an element `m` of `M`: it sends `a` to
`a • m`, so `1` to `m`.  Every morphism out of the free module of rank one is of this form. -/
def spanHom {M : ModuleCat.{u} A} (m : M) : unitModule A ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)

/-- `spanHom m` sends `a` to `a • m`. -/
@[simp]
theorem spanHom_apply {M : ModuleCat.{u} A} (m : M) (a : A) : (spanHom m).hom a = a • m := rfl

/-- Postcomposing `spanHom m` with a morphism `u` gives `spanHom (u m)`. -/
theorem spanHom_comp {M N : ModuleCat.{u} A} (m : M) (u : M ⟶ N) :
    spanHom m ≫ u = spanHom (u.hom m) := by
  ext
  simp [spanHom]

/-- `spanHom` is homogeneous: `spanHom (a • m) = a • spanHom m`. -/
theorem spanHom_smul {M : ModuleCat.{u} A} (a : A) (m : M) :
    spanHom (a • m) = a • spanHom (M := M) m := by
  ext
  simp [spanHom]

/-- `spanHom` is additive in the element. -/
theorem spanHom_add {M : ModuleCat.{u} A} (m n : M) :
    spanHom (m + n) = spanHom (M := M) m + spanHom (M := M) n := by
  ext
  simp [spanHom, smul_add]

/-- `spanHom` at the free module of rank one is multiplication, that is a scalar multiple of the
identity. -/
theorem spanHom_unit (a : A) : spanHom (M := unitModule A) a = a • 𝟙 (unitModule A) := by
  ext
  simp [spanHom, smul_eq_mul, mul_comm]

variable (Φ : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [Φ.Additive] [Functor.Linear A Φ]

/-- **The canonical map `Φ(A) ⊗_A M ⟶ Φ(M)`.**  It sends `x ⊗ m` to `Φ(spanHom m)(x)`; the
`A`-linearity of `Φ` is what makes this well defined on the tensor product. -/
@[sga "5 IIIB 5.4" "more general"]
def tensorComparisonApp (M : ModuleCat.{u} A) :
    (tensorLeft (Φ.obj (unitModule A))).obj M ⟶ Φ.obj M :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun (x : Φ.obj (unitModule A)) (m : M) ↦ (Φ.map (spanHom m)).hom x)
    (fun x y m ↦ by simp) (fun a x m ↦ by simp)
    (fun x m n ↦ by rw [spanHom_add, Φ.map_add]; simp)
    (fun a x m ↦ by rw [spanHom_smul, Φ.map_smul]; simp)

/-- `tensorComparisonApp Φ M` sends `x ⊗ m` to `Φ(spanHom m)(x)`. -/
@[simp]
theorem tensorComparisonApp_tmul (M : ModuleCat.{u} A) (x : Φ.obj (unitModule A)) (m : M) :
    (tensorComparisonApp Φ M).hom (x ⊗ₜ[A] m) = (Φ.map (spanHom m)).hom x :=
  rfl

/-- **The canonical map `Φ(A) ⊗_A - ⟶ Φ`**, as a natural transformation.  Naturality is the
identity `spanHom m ≫ u = spanHom (u m)`. -/
@[ega "III 7.2.2" "special case"]
def tensorComparison : tensorLeft (Φ.obj (unitModule A)) ⟶ Φ where
  app := tensorComparisonApp Φ
  naturality M N u := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun x m ↦ ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [show ((tensorLeft (Φ.obj (unitModule A))).map u).hom (x ⊗ₜ[A] m) = x ⊗ₜ[A] u.hom m from
      ModuleCat.MonoidalCategory.whiskerLeft_apply _ u x m]
    rw [tensorComparisonApp_tmul, tensorComparisonApp_tmul,
      show Φ.map (spanHom (u.hom m)) = Φ.map (spanHom m) ≫ Φ.map u by
        rw [← Φ.map_comp, spanHom_comp]]
    simp

/-- The component of `tensorComparison Φ` at `M` is `tensorComparisonApp Φ M`. -/
@[simp]
theorem tensorComparison_app (M : ModuleCat.{u} A) :
    (tensorComparison Φ).app M = tensorComparisonApp Φ M :=
  rfl

/-- **At the free module of rank one the comparison is the right unitor.**  Indeed
`spanHom a = a • 𝟙`, and an `A`-linear functor sends that to `a • 𝟙`, so the formula
`x ⊗ a ↦ Φ(spanHom a)(x)` reads `x ⊗ a ↦ a • x`. -/
theorem tensorComparison_app_unit :
    (tensorComparison Φ).app (unitModule A) = (ρ_ (Φ.obj (unitModule A))).hom := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun x a ↦ ?_
  rw [tensorComparison_app, tensorComparisonApp_tmul, spanHom_unit, Φ.map_smul, Φ.map_id]
  rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  simp

/-- The comparison is invertible at the free module of rank one. -/
instance isIso_tensorComparison_app_unit : IsIso ((tensorComparison Φ).app (unitModule A)) := by
  rw [tensorComparison_app_unit]
  infer_instance

/-- **The canonical map `Φ(A) ⊗_A M ⟶ Φ(M)` is invertible for every flat `M`.**

This is the dévissage of `Stacks.FlatDevissage.isIso_app_of_flat`: both functors are additive and
preserve filtered colimits — `tensorLeft` because `ModuleCat.{u} A` is monoidal closed — and the
comparison is invertible at the free module of rank one. -/
theorem isIso_tensorComparison_app_of_flat [PreservesFilteredColimitsOfSize.{u, u} Φ]
    (M : ModuleCat.{u} A) [Module.Flat A M] : IsIso ((tensorComparison Φ).app M) :=
  isIso_app_of_flat' (tensorComparison Φ) (isIso_tensorComparison_app_unit Φ) M

/-- **The same, for a flat module given as a type.** -/
theorem isIso_tensorComparison_app_of_flat' [PreservesFilteredColimitsOfSize.{u, u} Φ]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Flat A M] :
    IsIso ((tensorComparison Φ).app (ModuleCat.of A M)) :=
  isIso_tensorComparison_app_of_flat Φ (ModuleCat.of A M)

end Stacks.FlatDevissage

end
