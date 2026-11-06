module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.AmitsurFaithfullyFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of module maps along a faithfully flat ring map

Let `B` be a faithfully flat commutative `R`-algebra and let `M` and `N` be arbitrary
`R`-modules.  This file proves that a `B`-linear map `ψ : B ⊗[R] M → B ⊗[R] N` whose two base
changes to `B ⊗[R] B` agree is the base change of a unique `R`-linear map `M → N`; together with
the injectivity of `f ↦ f.baseChange B` this identifies

`Hom_R(M, N)  ≃  { ψ : Hom_B(B ⊗[R] M, B ⊗[R] N) // the two base changes of ψ agree }`.

This is the left exactness of `Hom_R(M, -)` applied to the Amitsur complex of `R → B`: the
condition on `ψ` says that `m ↦ ψ (1 ⊗ₜ m)` lands in the equalizer of the two maps
`B ⊗[R] N → (B ⊗[R] B) ⊗[R] N`, and that equalizer is `N` itself because the Amitsur complex of
`R → B` with coefficients in `N` is exact.

## Main definitions

* `Stacks.Descent.homBaseChange` is the base change of a `B`-linear map `B ⊗[R] M → B ⊗[R] N`
  along an `R`-algebra map `i : B →ₐ[R] T`, a `T`-linear map `T ⊗[R] M → T ⊗[R] N`.  That it
  deserves the name is `Stacks.Descent.homBaseChange_comp_rTensor`, which says that the square
  with vertical maps `i ⊗ id` commutes.
* `Stacks.Descent.kerIncludeLeftSubRightEquiv` identifies `N` with the equalizer of the two
  inclusions `B ⊗[R] N → (B ⊗[R] B) ⊗[R] N`.
* `Stacks.Descent.baseChangeHomEquiv` is the displayed bijection.

## Main results

* `Stacks.Descent.baseChange_injective_of_faithfullyFlat`: `f ↦ f.baseChange B` is injective.
* `Stacks.Descent.existsUnique_baseChange_eq`: **the fullness statement**, that a `ψ` whose two
  base changes to `B ⊗[R] B` agree is the base change of a unique `R`-linear map.

## Implementation notes

A `T`-linear map out of `T ⊗[R] M` is the same thing as an `R`-linear map out of `M`
(`LinearMap.liftBaseChangeEquiv`), so the base change of `ψ` along `i : B →ₐ[R] T` is defined by
lifting `m ↦ (i ⊗ id) (ψ (1 ⊗ₜ m))`.  This asks nothing of `T` beyond being an `R`-algebra
receiving `B`; in particular the two base changes to `B ⊗[R] B` are both defined without ever
making `B ⊗[R] B` an algebra over `B`, which would need two incompatible instances.  All the
general lemmas are proved with `T` a variable and are instantiated at `T = B ⊗[R] B` only in the
statements that need it.

`ModuleCat.baseExtensionFullyFaithfulOfFaithfullyFlat` is the same mathematics in bundled form:
full faithfulness of base extension into `Stacks.Descent.DescentData`.  Its descent condition is
the compatibility square of `Stacks.Descent.DescentData.Hom` at the canonical transition
isomorphism, phrased on `(B ⊗[R] M) ⊗[R] B`, and it needs `R` and `B` in one universe.  What is
proved here is the unbundled form, with the condition read literally as the equality of the two
base changes, with `R`, `B`, `M` and `N` in four independent universes, and from the Amitsur
complex rather than from the split-equaliser criterion.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
-/

@[expose] public section

open scoped TensorProduct

universe u v w w'

namespace Stacks.Descent

variable (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
  {M : Type w} [AddCommGroup M] [Module R M] {N : Type w'} [AddCommGroup N] [Module R N]
  {T : Type*} [CommRing T] [Algebra R T]

/-- The base change along an `R`-algebra map `i : B →ₐ[R] T` of a `B`-linear map
`ψ : B ⊗[R] M → B ⊗[R] N`: the unique `T`-linear map `T ⊗[R] M → T ⊗[R] N` making the square
with vertical maps `i ⊗ id` commute, which is
`Stacks.Descent.homBaseChange_comp_rTensor`. -/
noncomputable def homBaseChange (i : B →ₐ[R] T) (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) :
    T ⊗[R] M →ₗ[T] T ⊗[R] N :=
  LinearMap.liftBaseChange T
    (LinearMap.rTensor N i.toLinearMap ∘ₗ (LinearMap.liftBaseChangeEquiv B).symm ψ)

/-- The base change of `ψ` along `i` sends `t ⊗ₜ m` to `t • (i ⊗ id) (ψ (1 ⊗ₜ m))`. -/
@[simp]
theorem homBaseChange_tmul (i : B →ₐ[R] T) (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) (t : T) (m : M) :
    homBaseChange R B i ψ (t ⊗ₜ m) = t • LinearMap.rTensor N i.toLinearMap (ψ (1 ⊗ₜ m)) :=
  rfl

/-- `i ⊗ id` carries the `B`-action on `B ⊗[R] N` to the `T`-action on `T ⊗[R] N`. -/
theorem rTensor_algHom_smul (i : B →ₐ[R] T) (b : B) (x : B ⊗[R] N) :
    LinearMap.rTensor N i.toLinearMap (b • x) = i b • LinearMap.rTensor N i.toLinearMap x := by
  induction x with
  | tmul c n => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy]

/-- The defining property of `Stacks.Descent.homBaseChange`: the square whose horizontal maps are
`ψ` and its base change and whose vertical maps are `i ⊗ id` commutes. -/
theorem homBaseChange_comp_rTensor (i : B →ₐ[R] T) (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) :
    (homBaseChange R B i ψ).restrictScalars R ∘ₗ LinearMap.rTensor M i.toLinearMap =
      LinearMap.rTensor N i.toLinearMap ∘ₗ ψ.restrictScalars R := by
  ext b m
  change homBaseChange R B i ψ (i b ⊗ₜ m) = LinearMap.rTensor N i.toLinearMap (ψ (b ⊗ₜ m))
  rw [homBaseChange_tmul,
    show (b ⊗ₜ m : B ⊗[R] M) = b • (1 ⊗ₜ m) by simp [TensorProduct.smul_tmul'],
    map_smul, rTensor_algHom_smul]

/-- `Stacks.Descent.homBaseChange` is the *unique* `T`-linear map making that square commute. -/
theorem homBaseChange_eq_of_comp_rTensor (i : B →ₐ[R] T) (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N)
    (α : T ⊗[R] M →ₗ[T] T ⊗[R] N)
    (h : α.restrictScalars R ∘ₗ LinearMap.rTensor M i.toLinearMap =
      LinearMap.rTensor N i.toLinearMap ∘ₗ ψ.restrictScalars R) :
    α = homBaseChange R B i ψ := by
  ext m
  simpa using congr($h ((1 : B) ⊗ₜ m))

/-- Base changing the base change of an `R`-linear map gives its base change. -/
theorem homBaseChange_baseChange (i : B →ₐ[R] T) (f : M →ₗ[R] N) :
    homBaseChange R B i (f.baseChange B) = f.baseChange T := by
  ext m
  simp [homBaseChange]

/-- The descent condition on `ψ`, unwound: the two base changes of `ψ` to `B ⊗[R] B` agree
exactly when `m ↦ ψ (1 ⊗ₜ m)` lands in the equalizer of the two inclusions
`B ⊗[R] N → (B ⊗[R] B) ⊗[R] N`. -/
theorem homBaseChange_includeLeft_eq_includeRight_iff (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) :
    homBaseChange R B (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) ψ =
        homBaseChange R B (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) ψ ↔
      ∀ m : M,
        LinearMap.rTensor N (Algebra.TensorProduct.includeLeftSubRight R B) (ψ (1 ⊗ₜ m)) = 0 := by
  rw [homBaseChange, homBaseChange, (LinearMap.liftBaseChangeEquiv _).injective.eq_iff,
    LinearMap.ext_iff]
  refine forall_congr' fun m => ?_
  simp only [LinearMap.comp_apply, LinearMap.liftBaseChangeEquiv_symm_apply,
    Algebra.TensorProduct.includeLeftSubRight, LinearMap.rTensor_sub, LinearMap.sub_apply,
    sub_eq_zero]

section FaithfullyFlat

variable [Module.FaithfullyFlat R B]

/-- **The faithfulness half, at the level of modules.**  Base change along a faithfully flat
ring map is injective on `R`-linear maps. -/
@[ega "0 6.6.1" "a", sga "1 VIII 1.4" "partial"]
theorem baseChange_injective_of_faithfullyFlat :
    Function.Injective (fun f : M →ₗ[R] N => f.baseChange B) := fun _ _ h =>
  LinearMap.ext fun m =>
    Module.FaithfullyFlat.tensorProduct_mk_injective N (congr($h (1 ⊗ₜ m)))

/-- For a faithfully flat `R`-algebra `B`, the module `N` *is* the equalizer of the two
inclusions `B ⊗[R] N → (B ⊗[R] B) ⊗[R] N`, by the exactness of the Amitsur complex with
coefficients in `N`. -/
@[sga "1 VIII 1.5"]
noncomputable def kerIncludeLeftSubRightEquiv :
    N ≃ₗ[R]
      LinearMap.ker (LinearMap.rTensor N (Algebra.TensorProduct.includeLeftSubRight R B)) :=
  LinearEquiv.ofBijective
    ((TensorProduct.mk R B N 1).codRestrict
      (LinearMap.ker (LinearMap.rTensor N (Algebra.TensorProduct.includeLeftSubRight R B)))
      fun n => congr($(rTensor_includeLeftSubRight_comp_mk R B N) n))
    ⟨fun _ _ hab =>
      Module.FaithfullyFlat.tensorProduct_mk_injective N (Subtype.ext_iff.mp hab),
     fun x => by
      obtain ⟨n, hn⟩ := (exact_mk_rTensor_includeLeftSubRight R B N).linearMap_ker_eq.le x.2
      exact ⟨n, Subtype.ext hn⟩⟩

/-- The equivalence `Stacks.Descent.kerIncludeLeftSubRightEquiv` sends `n` to `1 ⊗ₜ n`. -/
@[simp]
theorem kerIncludeLeftSubRightEquiv_apply_coe (n : N) :
    (kerIncludeLeftSubRightEquiv R B n : B ⊗[R] N) = 1 ⊗ₜ n :=
  rfl

/-- **The fullness half of Stacks 023S for a single faithfully flat ring map.**  A `B`-linear map
`ψ : B ⊗[R] M → B ⊗[R] N` whose two base changes to `B ⊗[R] B` agree is the base change of an
`R`-linear map `M → N`. -/
@[sga "1 VIII 1.4" "partial"]
theorem exists_baseChange_eq (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N)
    (h : homBaseChange R B (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) ψ =
      homBaseChange R B (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) ψ) :
    ∃ f : M →ₗ[R] N, f.baseChange B = ψ := by
  have hzero := (homBaseChange_includeLeft_eq_includeRight_iff R B ψ).mp h
  let g := ((LinearMap.liftBaseChangeEquiv B).symm ψ).codRestrict
    (LinearMap.ker (LinearMap.rTensor N (Algebra.TensorProduct.includeLeftSubRight R B)))
    fun m => hzero m
  exact ⟨(kerIncludeLeftSubRightEquiv R B).symm.toLinearMap ∘ₗ g,
    (LinearMap.liftBaseChangeEquiv B).symm.injective (LinearMap.ext fun m =>
      congrArg Subtype.val ((kerIncludeLeftSubRightEquiv R B).apply_symm_apply (g m)))⟩

/-- **The fullness half of Stacks 023S for a single faithfully flat ring map**, with the
uniqueness of the descended map. -/
theorem existsUnique_baseChange_eq (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N)
    (h : homBaseChange R B (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) ψ =
      homBaseChange R B (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) ψ) :
    ∃! f : M →ₗ[R] N, f.baseChange B = ψ := by
  obtain ⟨f, hf⟩ := exists_baseChange_eq R B ψ h
  exact ⟨f, hf, fun g hg => baseChange_injective_of_faithfullyFlat R B (hg.trans hf.symm)⟩

/-- **Full faithfulness of base change along a faithfully flat ring map**, as a bijection:
`R`-linear maps `M → N` are exactly the `B`-linear maps `B ⊗[R] M → B ⊗[R] N` whose two base
changes to `B ⊗[R] B` agree. -/
@[sga "1 VIII 1.4"]
noncomputable def baseChangeHomEquiv :
    (M →ₗ[R] N) ≃
      {ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N //
        homBaseChange R B (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) ψ =
          homBaseChange R B (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) ψ} :=
  Equiv.ofBijective
    (fun f => ⟨f.baseChange B, by rw [homBaseChange_baseChange, homBaseChange_baseChange]⟩)
    ⟨fun _ _ h =>
      baseChange_injective_of_faithfullyFlat R B (Subtype.ext_iff.mp h),
     fun ψ => (exists_baseChange_eq R B ψ.1 ψ.2).imp fun _ hf => Subtype.ext hf⟩

/-- The bijection `Stacks.Descent.baseChangeHomEquiv` sends `f` to its base change
`f.baseChange B`. -/
@[simp]
theorem baseChangeHomEquiv_apply_coe (f : M →ₗ[R] N) :
    (baseChangeHomEquiv R B f : B ⊗[R] M →ₗ[B] B ⊗[R] N) = f.baseChange B :=
  rfl

/-- The `R`-linear map `f` descended from `ψ` satisfies `1 ⊗ₜ f m = ψ (1 ⊗ₜ m)`. -/
@[simp]
theorem baseChangeHomEquiv_symm_apply_tmul_one
    (ψ : {ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N //
      homBaseChange R B (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) ψ =
        homBaseChange R B (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) ψ}) (m : M) :
    (1 : B) ⊗ₜ (baseChangeHomEquiv R B).symm ψ m = (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) (1 ⊗ₜ m) :=
  congr($(congrArg Subtype.val ((baseChangeHomEquiv R B).apply_symm_apply ψ)) (1 ⊗ₜ m))

end FaithfullyFlat

end Stacks.Descent

end
