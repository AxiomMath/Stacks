module

public import StacksFrontier.RingTheory.NaiveCotangent.Cocartesian
public import StacksFrontier.RingTheory.NaiveCotangent.FlatBaseLocalizedTarget

/-!
# The naive cotangent complex for a flat algebra, base changed and then localized

Let `R → A` be flat, let `R → B` be an arbitrary ring map, and let `C` be a localization of
`B ⊗_R A`.  Then the canonical map of two-term complexes of `C`-modules

`NL_{A/R} ⊗_A C ⟶ NL_{C/B}`

is a quasi-isomorphism.

## Main results

* `NaiveCotangent.bijective_onH₁_nlExtensionBaseChangeMap_canHom_of_flat_algebra` and
  `NaiveCotangent.bijective_onH₀_nlExtensionBaseChangeMap_canHom`: the comparison
  `NL_{A/R} ⊗_A (B ⊗_R A) ⟶ NL_{(B ⊗_R A)/B}` is bijective on `H₁` when `A` is flat over `R`,
  and bijective on `H₀` always.
* `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_canHom_of_flat_algebra`: that comparison is
  a quasi-isomorphism, the first assertion of Stacks 0FJU in the
  `NaiveCotangent.nlExtensionBaseChangeMap` packaging.
* `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_algebra`: **the comparison
  `NL_{A/R} ⊗_A C ⟶ NL_{C/B}` is a quasi-isomorphism** when `A` is flat over `R` and `C` is a
  localization of `B ⊗_R A`.

## References

* [Stacks Project, Tag 0FJU](https://stacks.math.columbia.edu/tag/0FJU), base change of the naive
  cotangent complex along a cocartesian square with one flat side.
* [Stacks Project, Tag 0FUZ](https://stacks.math.columbia.edu/tag/0FUZ), arbitrary base change of
  the naive cotangent complex on `H⁰`, and surjectivity on `H⁻¹`.
* [Stacks Project, Tag 00S7](https://stacks.math.columbia.edu/tag/00S7), the naive cotangent
  complex and localization of the target.
* [Stacks Project, Tag 0FK0](https://stacks.math.columbia.edu/tag/0FK0), base change for the naive
  cotangent complex of a morphism of schemes.
-/

@[expose] public section

namespace NaiveCotangent

open Algebra TensorProduct

noncomputable section

section FlatAlgebraLocalizedTarget

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **Injectivity on the cycles of the conormal term**, read on the two-term complexes: for `A`
flat over `R`, an element of `NL_{A/R} ⊗_A (B ⊗_R A)` in degree `1` that is killed by the
differential and by the comparison to `NL_{(B ⊗_R A)/B}` is zero. -/
theorem eq_zero_of_canHom_f₁_eq_zero_of_flat_algebra [Module.Flat R A] :
    ∀ z : (nlExtensionBaseChange ((Generators.self R A).toExtension) (B ⊗[R] A)).X₁,
      (nlExtensionBaseChange ((Generators.self R A).toExtension) (B ⊗[R] A)).d z = 0 →
      (nlExtensionBaseChangeMap (T := B ⊗[R] A)
        (FlatBaseChangeNL.canHom (R := R) (S := A) B)).f₁ z = 0 → z = 0 :=
  cotangent_intrinsic_baseChange_cycle_injective_of_flat (R := R) (S := A) (T := B)

/-- **Surjectivity on the cycles of the conormal term**, read on the two-term complexes: every
cycle of `NL_{(B ⊗_R A)/B}` in degree `1` is the image of a cycle of `NL_{A/R} ⊗_A (B ⊗_R A)`.
-/
theorem exists_canHom_f₁_eq :
    ∀ y : (nlOfExtension ((Generators.self B (B ⊗[R] A)).toExtension)).X₁,
      (nlOfExtension ((Generators.self B (B ⊗[R] A)).toExtension)).d y = 0 →
      ∃ z : (nlExtensionBaseChange ((Generators.self R A).toExtension) (B ⊗[R] A)).X₁,
        (nlExtensionBaseChange ((Generators.self R A).toExtension) (B ⊗[R] A)).d z = 0 ∧
        (nlExtensionBaseChangeMap (T := B ⊗[R] A)
          (FlatBaseChangeNL.canHom (R := R) (S := A) B)).f₁ z = y :=
  (naiveCotangentComplex_baseChange_homology (T := B) (Algebra.Generators.self R A)).2.2.2.2.2.2.2

/-- **Surjectivity on the cokernels**, read on the two-term complexes: every element of
`NL_{(B ⊗_R A)/B}` in degree `0` differs by a boundary from one in the image of the comparison.
-/
theorem exists_sub_canHom_f₀_mem_range :
    ∀ y : (nlOfExtension ((Generators.self B (B ⊗[R] A)).toExtension)).X₀,
      ∃ z : (nlExtensionBaseChange ((Generators.self R A).toExtension) (B ⊗[R] A)).X₀,
        y - (nlExtensionBaseChangeMap (T := B ⊗[R] A)
            (FlatBaseChangeNL.canHom (R := R) (S := A) B)).f₀ z ∈
          LinearMap.range (nlOfExtension ((Generators.self B (B ⊗[R] A)).toExtension)).d :=
  (naiveCotangentComplex_baseChange_homology (T := B) (Algebra.Generators.self R A)).2.2.2.2.2.1

/-- **Injectivity on the cokernels**, read on the two-term complexes: an element of
`NL_{A/R} ⊗_A (B ⊗_R A)` in degree `0` whose image is a boundary is itself a boundary. -/
theorem canHom_f₀_mem_range_iff :
    ∀ z : (nlExtensionBaseChange ((Generators.self R A).toExtension) (B ⊗[R] A)).X₀,
      (nlExtensionBaseChangeMap (T := B ⊗[R] A)
          (FlatBaseChangeNL.canHom (R := R) (S := A) B)).f₀ z ∈
          LinearMap.range (nlOfExtension ((Generators.self B (B ⊗[R] A)).toExtension)).d ↔
        z ∈ LinearMap.range
          (nlExtensionBaseChange ((Generators.self R A).toExtension) (B ⊗[R] A)).d :=
  (naiveCotangentComplex_baseChange_homology (T := B)
    (Algebra.Generators.self R A)).2.2.2.2.2.2.1

/-- **Flat base change of a flat algebra is bijective on `H₁`.**  For `A` flat over `R` the
comparison `NL_{A/R} ⊗_A (B ⊗_R A) ⟶ NL_{(B ⊗_R A)/B}` carries the kernel of its source
differential bijectively onto the kernel of its target differential. -/
theorem bijective_onH₁_nlExtensionBaseChangeMap_canHom_of_flat_algebra [Module.Flat R A] :
    Function.Bijective (nlExtensionBaseChangeMap (T := B ⊗[R] A)
      (FlatBaseChangeNL.canHom (R := R) (S := A) B)).onH₁ := by
  refine bijective_onH₁_of_bijOn _ ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
    rw [chainMap_comm_apply, hx, map_zero]
  · intro x hx y hy hxy
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx hy
    refine sub_eq_zero.mp (eq_zero_of_canHom_f₁_eq_zero_of_flat_algebra (x - y) ?_ ?_)
    · rw [map_sub, hx, hy, sub_zero]
    · rw [map_sub, hxy, sub_self]
  · intro y hy
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hy
    obtain ⟨x, hdx, hfx⟩ := exists_canHom_f₁_eq y hy
    exact ⟨x, by simpa only [SetLike.mem_coe, LinearMap.mem_ker] using hdx, hfx⟩

/-- **Arbitrary base change is bijective on `H₀`.**  For any ring maps `R → A` and `R → B` the
comparison `NL_{A/R} ⊗_A (B ⊗_R A) ⟶ NL_{(B ⊗_R A)/B}` is bijective on the cokernels of the two
differentials. -/
theorem bijective_onH₀_nlExtensionBaseChangeMap_canHom :
    Function.Bijective (nlExtensionBaseChangeMap (T := B ⊗[R] A)
      (FlatBaseChangeNL.canHom (R := R) (S := A) B)).onH₀ := by
  refine ⟨fun u v huv => ?_, fun v => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [onH₀_mk, onH₀_mk, Submodule.Quotient.eq] at huv
    rw [Submodule.Quotient.eq]
    refine (canHom_f₀_mem_range_iff (x - y)).mp ?_
    rw [map_sub]
    exact huv
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨x, hx⟩ := exists_sub_canHom_f₀_mem_range y
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [onH₀_mk, Submodule.Quotient.eq]
    simpa only [neg_sub] using neg_mem hx

/-- **Base change of the naive cotangent complex of a flat algebra to the pushout**, the first
assertion of Stacks 0FJU in the packaging of `NaiveCotangent.nlExtensionBaseChangeMap`: for `A`
flat over `R` the canonical map `NL_{A/R} ⊗_A (B ⊗_R A) ⟶ NL_{(B ⊗_R A)/B}` is a
quasi-isomorphism. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_canHom_of_flat_algebra [Module.Flat R A] :
    IsQuasiIso (nlExtensionBaseChangeMap (T := B ⊗[R] A)
      (FlatBaseChangeNL.canHom (R := R) (S := A) B)) :=
  ⟨bijective_onH₁_nlExtensionBaseChangeMap_canHom_of_flat_algebra,
    bijective_onH₀_nlExtensionBaseChangeMap_canHom⟩

variable {C : Type u} [CommRing C] [Algebra R C] [Algebra A C] [Algebra B C]
  [Algebra (B ⊗[R] A) C] [IsScalarTower R A C] [IsScalarTower R B C]
  [IsScalarTower A (B ⊗[R] A) C] [IsScalarTower B (B ⊗[R] A) C]

/-- **The naive cotangent complex for a flat algebra base changed and then localized.**  Let
`R → B` be a ring map, let `R → A` be flat, and let `C` be a localization of `B ⊗_R A` at a
multiplicative subset, compatibly with the maps out of `A` and `B`.  Then the canonical map of
two-term complexes of `C`-modules

`NL_{A/R} ⊗_A C ⟶ NL_{C/B}`

is a quasi-isomorphism, for every morphism of extensions `h` inducing it. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_of_flat_algebra [Module.Flat R A]
    (M : Submonoid (B ⊗[R] A)) [IsLocalization M C]
    (h : ((Generators.self R A).toExtension).Hom ((Generators.self B C).toExtension)) :
    IsQuasiIso (nlExtensionBaseChangeMap (T := C) h) := by
  have : Module.Flat (B ⊗[R] A) C := IsLocalization.flat C M
  refine isQuasiIso_nlExtensionBaseChangeMap_congr h
    (flatBaseLocalizedHom (R := R) (A := A) (B := B) (C := C)) ?_
  refine IsQuasiIso.of_comp_right
    (isQuasiIso_cancelBaseChangeChainMap (D := B ⊗[R] A) (C := C)
      ((Generators.self R A).toExtension)) ?_
  rw [nlExtensionBaseChangeMap_flatBaseLocalizedHom_comp_cancel]
  exact (isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization M _).comp
    (isQuasiIso_nlExtensionBaseChangeMap_canHom_of_flat_algebra.baseChange C)

end FlatAlgebraLocalizedTarget

end

end NaiveCotangent

end
