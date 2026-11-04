module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange

/-!
# Annihilators of finitely generated ideals under flat base change

Let `R → S` be a flat ring map and `I` an ideal of `R` which is finitely generated as an
`R`-module. Then the extension of the annihilator of `I` is the annihilator of the extension of
`I`. This is the commutative-algebra input for the flat base change of the diagonal annihilator
and hence of the Noether different.

## Main definitions

* `Stacks.Discriminant.idealBaseChangeMap` is the `S`-linear map `S ⊗[R] I → S` induced by the
  inclusion of `I`.

## Main results

* `Stacks.Discriminant.idealBaseChangeMap_injective` and
  `Stacks.Discriminant.range_idealBaseChangeMap` identify `S ⊗[R] I` with the extension of `I`.
* `Stacks.Discriminant.annihilator_map_eq_of_flat`: taking annihilators commutes with flat base
  change along a finitely generated ideal.

## Implementation notes

Flatness enters twice: it makes `S ⊗[R] I → S` injective, which identifies `S ⊗[R] I` with the
extended ideal, and it is what makes the annihilator of a base-changed module the extension of
the annihilator. Finiteness of `I` as a module is what the latter statement needs, so it is taken
as a hypothesis rather than derived.

## References

* [Stacks Project, Tag 0BVM](https://stacks.math.columbia.edu/tag/0BVM)
* [Stacks Project, Tag 0BVN](https://stacks.math.columbia.edu/tag/0BVN)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.Flat R S] (I : Ideal R)

/-- The `S`-linear map `S ⊗[R] I → S` obtained by base changing the inclusion of `I` into `R`
and identifying `S ⊗[R] R` with `S`. Its image is the extension of `I` to `S`. -/
def idealBaseChangeMap : S ⊗[R] ↥I →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
    (LinearMap.baseChange S I.subtype)

/-- Over a flat extension, the base change of a finitely generated ideal injects into the
extension ring. -/
theorem idealBaseChangeMap_injective :
    Function.Injective (idealBaseChangeMap (S := S) I) := by
  intro x y h
  have hi : Function.Injective (LinearMap.baseChange S I.subtype) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.iff_lTensor_injectiveₛ.mp (inferInstance : Module.Flat R S)) I
  exact hi ((TensorProduct.AlgebraTensorModule.rid R S S).injective h)

omit [Module.Flat R S] in
/-- The image of the base change of `I` is the extension of `I` to `S`. -/
theorem range_idealBaseChangeMap :
    (idealBaseChangeMap (S := S) I).range = Ideal.map (algebraMap R S) I := by
  dsimp [idealBaseChangeMap]
  rw [LinearMap.range_comp]
  show Submodule.map (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap
    (Submodule.baseChange S I) = Ideal.map (algebraMap R S) I
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  have key (r : R) : (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap
      ((TensorProduct.mk R S R 1) r) = algebraMap R S r := by
    simp [TensorProduct.AlgebraTensorModule.rid, Algebra.smul_def]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    rw [key]
    exact Ideal.mem_map_of_mem _ hr
  · rw [Ideal.map, Ideal.span_le]
    rintro x ⟨r, hr, rfl⟩
    exact Submodule.subset_span ⟨_, ⟨r, hr, rfl⟩, key r⟩

/-- Over a flat extension, the extension of the annihilator of a finitely generated ideal is the
annihilator of the extension. -/
theorem annihilator_map_eq_of_flat [Module.Finite R ↥I] :
    Ideal.map (algebraMap R S) I.annihilator =
      (Ideal.map (algebraMap R S) I).annihilator := by
  rw [ann_extension_eq_ann_baseChange_module (R := R) (S := S) (M := ↥I)]
  ext s
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · rw [Submodule.mem_annihilator]
    intro x hx
    obtain ⟨y, rfl⟩ : x ∈ (idealBaseChangeMap (S := S) I).range := by
      rwa [range_idealBaseChangeMap]
    simpa only [map_smul, map_zero, smul_eq_mul] using
      congrArg (idealBaseChangeMap (S := S) I) ((Module.mem_annihilator.mp hs) y)
  · rw [Module.mem_annihilator]
    intro y
    apply idealBaseChangeMap_injective (S := S) I
    simpa only [map_smul, map_zero, smul_eq_mul] using (Submodule.mem_annihilator.mp hs) _
      (range_idealBaseChangeMap (S := S) I ▸ ⟨y, rfl⟩)

end Stacks.Discriminant
