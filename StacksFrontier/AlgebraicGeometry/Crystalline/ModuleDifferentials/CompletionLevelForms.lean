module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevel
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.QuotientForms

/-!
# The two shapes of the differentials of a completion, in every degree and after tensoring

Let `A → B` be a ring map, let an ideal `J` of `B` carry divided powers `δ`, let `p` be nilpotent
modulo `J`, write `B̂` for the `p`-adic completion of `B`, and let `cmp` be a comparison of
[Stacks, Tag 07KK] with cutoff `N`.  At a level `k = N + e`,
`Crystalline.completedDifferentialsLevelLinearEquiv` of `ModuleDifferentials/CompletionLevel.lean`
is a `B̂`-linear identification of the two shapes of the differentials of `B̂` modulo `pᵏ`:

`Ω_{B̂/A,γ̂} / pᵏ ≃ Ω̂_{B/A,δ} / pᵏ`.

This module carries that identification up the exterior powers and across a tensor product.  For
every module `M` over the level ring `B̂/pᵏ` and every degree `i`,

`M ⊗_{B̂} Ωⁱ_{B̂/A,γ̂} ≃ M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{B/A,δ}`,

which is the form the level-`e` step of the source's proof of [Stacks, Tag 07LF] consumes: there
the left side is the degree-`i` term of the divided power de Rham complex of the completed
envelope `D(n)` and the right side is the degree-`i` term of the complex the cosimplicial module
`Ω_{D(*)}` of [Stacks, Tag 07LA] is assembled from.

## Why it is true

A module over `B̂/pᵏ` is killed by `pᵏ`, so a tensor product over `B̂` with such a module only
sees its second factor modulo `pᵏ`; and modulo `pᵏ` the two shapes agree.  Formally, for a
`B̂`-module `N` the reduction `N → N/pᵏ·N` is a base change along `B̂ → B̂/pᵏ`
(`Crystalline.isBaseChange_mkQ_smulTop`, from `Crystalline.isBaseChange_of_quotientLinearEquiv`
of `ModuleDifferentials/QuotientForms.lean`), hence so is its degree-`i` exterior power
(`Crystalline.isBaseChange_exteriorPowerMapOfBaseChange`, which is
`DeRhamBaseChange.isBaseChange_exteriorPower` fed with
`ExteriorAlgebra.exteriorPowerBaseChangeMap`), and cancelling the two tensor products gives

`M ⊗_{B̂/pᵏ} ⋀ⁱ_{B̂/pᵏ} (N/pᵏ·N) ≃ M ⊗_{B̂} ⋀ⁱ_{B̂} N`.

Reading this for `N = Ω_{B̂/A,γ̂}` — where the reduction is composed with the level identification,
which is allowed because the composite is again a quotient description
(`Crystalline.isBaseChange_comp_mkQ_smulTop`) — and for `N = Ω̂_{B/A,δ}`, the two readings have
the same left-hand side, and the stated equivalence is one composed with the inverse of the other.

This is the same argument as the `QuotientForms` section of
`ModuleDifferentials/QuotientForms.lean`, which is why the base-change machinery below is stated
for an arbitrary base change in degree one rather than only for a reduction map: there the
degree-one base change is the reduction of the differentials along `B → B ⧸ K`, here it is the
reduction of the differentials of `B̂` followed by the level identification.

No flatness, no finiteness, no hypothesis on `i` and no completion of a tensor product appears.
Degree zero is the harmless statement `M ⊗_{B̂} B̂ ≃ M ⊗_{B̂} B̂`.

## Main definitions

* `Crystalline.exteriorPowerMapOfBaseChange` and
  `Crystalline.exteriorPowerEquivOfBaseChange` — the degree-`i` companion of a degree-one base
  change `f : X → Y` along `R → S`, as a map `⋀ⁱ_R X → ⋀ⁱ_S Y` and as the equivalence
  `S ⊗_R ⋀ⁱ_R X ≃ ⋀ⁱ_S Y`.
* `Crystalline.tensorExteriorPowerEquivOfBaseChange` — `M ⊗_S ⋀ⁱ_S Y ≃ M ⊗_R ⋀ⁱ_R X` for an
  `S`-module `M`.
* `Crystalline.completedDifferentialsLevelMap` — the reduction of `Ω_{B̂/A,γ̂}` modulo `pᵏ`
  followed by the level identification, as a `B̂`-linear map into `Ω̂_{B/A,δ} / pᵏ`.
* `Crystalline.completionDifferentialsReductionMap` — the reduction of `Ω̂_{B/A,δ}` modulo `pᵏ`.
* `Crystalline.tensorFormsCompletionLevelEquiv` — **the level identification in degree `i`, after
  tensoring**: `M ⊗_{B̂} Ωⁱ_{B̂/A,γ̂} ≃ M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{B/A,δ}`.

## Main results

* `Crystalline.isBaseChange_mkQ_smulTop` and `Crystalline.isBaseChange_comp_mkQ_smulTop` — the
  reduction `N → N/I·N`, and the reduction followed by any `R`-linear identification of its
  target, are base changes along `R → R ⧸ I`.
* `Crystalline.isBaseChange_exteriorPowerMapOfBaseChange` — exterior powers of a base change are
  base changes.
* `Crystalline.isBaseChange_completedDifferentialsLevelMap` and
  `Crystalline.isBaseChange_completionDifferentialsReductionMap` — the two degree-one maps the
  main equivalence is built from are base changes along `B̂ → B̂/pᵏ`.
* `Crystalline.tensorFormsCompletionLevelEquiv_apply`,
  `Crystalline.completedDifferentialsLevelMap_apply` and
  `Crystalline.completionDifferentialsReductionMap_apply` — the three definitional equations,
  recorded because the generator computation below rewrites with them rather than unfolding the
  definitions.
* `Crystalline.tensorFormsCompletionLevelEquiv_tmul_ιMulti` — **the equation pinning the main
  equivalence down**: on a tensor of a section with a wedge `ω₁ ∧ ⋯ ∧ ωᵢ` of differentials of
  `B̂` it is, read through the canonical description
  `Crystalline.tensorExteriorPowerEquivOfBaseChange` of its target, the wedge of the classes of
  the `ωⱼ` under `Crystalline.completedDifferentialsLevelLinearEquiv`, slot by slot.
* `Crystalline.tensorFormsCompletionLevelEquiv_tmul_ιMulti_of_mk` — the same equation with the
  canonical description cleared away: if `ωⱼ` and `ηⱼ` have the same class under the level
  identification in every slot, the equivalence carries `m ⊗ ω₁ ∧ ⋯ ∧ ωᵢ` to
  `m ⊗ η₁ ∧ ⋯ ∧ ηᵢ`.  Such `ηⱼ` exist for every `ωⱼ`, so this determines the equivalence on
  generators of the source.

## Implementation notes

The target of the main equivalence is written `⋀ⁱ_{B̂} Ω̂_{B/A,δ}` and not
`dividedPowerDifferentialForms` of anything: the completion `Ω̂_{B/A,δ}` is the `p`-adic
completion of a module, not the module of divided power differentials of a divided power ring, so
there is no divided power structure to name it with.  The source is written
`dividedPowerDifferentialForms`, which is by definition the exterior power
`⋀ⁱ_{B̂} Ω_{B̂/A,γ̂}`, so both sides are exterior powers over `B̂` and no transport of structure
occurs anywhere in this file.

The pinning equation is stated in two shapes because no unconditional slotwise formula with
values in `M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{B/A,δ}` exists: the level identification lands in a quotient of
`Ω̂_{B/A,δ}` and that quotient has no canonical splitting.  What is canonical is the quotient
description of the target supplied by
`Crystalline.tensorExteriorPowerEquivOfBaseChange`, and the first shape is the formula read
through it; the second shape says that a lift along the reduction, which always exists, may be
used instead.

`Crystalline.isBaseChange_comp_mkQ_smulTop` is how the level identification enters: it is the
`B̂`-linear equivalence `E` of that lemma, so nothing has to be known about it beyond its type,
and in particular its `B̂`-linearity — `Crystalline.completedDifferentialsLevelEquiv_smul` — is
used only through `Crystalline.completedDifferentialsLevelLinearEquiv`.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Crystalline

/-! ### Reductions modulo an ideal as base changes -/

section Reduction

variable {R : Type*} [CommRing R] (I : Ideal R) (N : Type*) [AddCommGroup N] [Module R N]

/-- The reduction `N → N/I·N` followed by an `R`-linear identification of its target is a base
change along `R → R ⧸ I`. -/
private theorem isBaseChange_comp_mkQ_smulTop_aux {Y : Type*} [AddCommGroup Y] [Module R Y]
    [Module (R ⧸ I) Y] [IsScalarTower R (R ⧸ I) Y]
    (E : (N ⧸ (I • (⊤ : Submodule R N))) ≃ₗ[R] Y) :
    IsBaseChange (R ⧸ I) (E.toLinearMap ∘ₗ (I • (⊤ : Submodule R N)).mkQ) := by
  refine isBaseChange_of_quotientLinearEquiv _ ?_ I ?_ E fun _ ↦ rfl
  · rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  · rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/-- **The reduction `N → N/I·N` is a base change along `R → R ⧸ I`.**  This is
`Crystalline.isBaseChange_of_quotientLinearEquiv` with the identification of the target with the
quotient taken to be the identity. -/
public theorem isBaseChange_mkQ_smulTop :
    IsBaseChange (R ⧸ I) (I • (⊤ : Submodule R N)).mkQ :=
  isBaseChange_comp_mkQ_smulTop_aux I N (LinearEquiv.refl R _)

/-- **The reduction `N → N/I·N` followed by an `R`-linear identification of its target is a base
change along `R → R ⧸ I`.**  The identification is not asked to be `R ⧸ I`-linear: it is so
automatically, `R → R ⧸ I` being surjective, and
`Crystalline.isBaseChange_of_quotientLinearEquiv` only consumes its `R`-linearity. -/
public theorem isBaseChange_comp_mkQ_smulTop {Y : Type*} [AddCommGroup Y] [Module R Y]
    [Module (R ⧸ I) Y] [IsScalarTower R (R ⧸ I) Y]
    (E : (N ⧸ (I • (⊤ : Submodule R N))) ≃ₗ[R] Y) :
    IsBaseChange (R ⧸ I) (E.toLinearMap ∘ₗ (I • (⊤ : Submodule R N)).mkQ) :=
  isBaseChange_comp_mkQ_smulTop_aux I N E

end Reduction

/-! ### Exterior powers of a base change -/

section BaseChangeExteriorPower

variable {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y] (f : X →ₗ[R] Y)
  (hf : IsBaseChange S f)

/-- **The degree-`i` companion of a base change in degree one**, the `i`-th exterior power of
`f : X → Y` read along the ring map `R → S`: the comparison
`ExteriorAlgebra.exteriorPowerBaseChangeMap` into `⋀ⁱ_S (S ⊗_R X)` followed by the `i`-th
exterior power of the identification `S ⊗_R X ≃ Y` that `f` being a base change provides. -/
public noncomputable def exteriorPowerMapOfBaseChange (i : ℕ) :
    ↥(⋀[R]^i X) →ₗ[R] ↥(⋀[S]^i Y) :=
  (LinearMap.restrictScalars R (exteriorPower.map i hf.equiv.toLinearMap)).comp
    (ExteriorAlgebra.exteriorPowerBaseChangeMap R S X i)

/-- **The degree-`i` companion carries wedges to wedges**, slot by slot. -/
public theorem exteriorPowerMapOfBaseChange_ιMulti (i : ℕ) (v : Fin i → X) :
    exteriorPowerMapOfBaseChange f hf i (exteriorPower.ιMulti R i v) =
      exteriorPower.ιMulti S i fun j ↦ f (v j) := by
  have hv : (hf.equiv.toLinearMap ∘ fun j ↦ (1 : S) ⊗ₜ[R] v j) = fun j ↦ f (v j) := by
    funext j
    change hf.equiv ((1 : S) ⊗ₜ[R] v j) = _
    rw [hf.equiv_tmul, one_smul]
  change exteriorPower.map i hf.equiv.toLinearMap
      (ExteriorAlgebra.exteriorPowerBaseChangeMap R S X i (exteriorPower.ιMulti R i v)) = _
  rw [ExteriorAlgebra.exteriorPowerBaseChangeMap_ιMulti, exteriorPower.map_apply_ιMulti, hv]

/-- **The exterior powers of a base change are base changes.**  The degree-one hypothesis and the
equation on wedges are exactly what `DeRhamBaseChange.isBaseChange_exteriorPower` consumes. -/
public theorem isBaseChange_exteriorPowerMapOfBaseChange (i : ℕ) :
    IsBaseChange S (exteriorPowerMapOfBaseChange f hf i) :=
  DeRhamBaseChange.isBaseChange_exteriorPower hf _ (exteriorPowerMapOfBaseChange_ιMulti f hf i)

/-- **`⋀ⁱ_S Y = S ⊗_R ⋀ⁱ_R X`** for a base change `f : X → Y` in degree one. -/
public noncomputable def exteriorPowerEquivOfBaseChange (i : ℕ) :
    S ⊗[R] ↥(⋀[R]^i X) ≃ₗ[S] ↥(⋀[S]^i Y) :=
  (isBaseChange_exteriorPowerMapOfBaseChange f hf i).equiv

/-- The degree-`i` comparison carries `s ⊗ x` to `s` times the image of `x`. -/
@[simp]
public theorem exteriorPowerEquivOfBaseChange_tmul (i : ℕ) (s : S) (x : ↥(⋀[R]^i X)) :
    exteriorPowerEquivOfBaseChange f hf i (s ⊗ₜ x) =
      s • exteriorPowerMapOfBaseChange f hf i x :=
  IsBaseChange.equiv_tmul _ s x

/-- The degree-`i` comparison on the standard generators, which is what identifies it as the
canonical map rather than merely as some bijection. -/
public theorem exteriorPowerEquivOfBaseChange_tmul_ιMulti (i : ℕ) (s : S) (v : Fin i → X) :
    exteriorPowerEquivOfBaseChange f hf i (s ⊗ₜ exteriorPower.ιMulti R i v) =
      s • exteriorPower.ιMulti S i fun j ↦ f (v j) := by
  rw [exteriorPowerEquivOfBaseChange_tmul, exteriorPowerMapOfBaseChange_ιMulti]

section Tensor

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- **`M ⊗_S ⋀ⁱ_S Y = M ⊗_R ⋀ⁱ_R X`** for an `S`-module `M` and a base change `f : X → Y` in
degree one.  It is `Crystalline.exteriorPowerEquivOfBaseChange` — the degree-`i` exterior power of
`Y` is the base change of that of `X` — followed by
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
public noncomputable def tensorExteriorPowerEquivOfBaseChange (i : ℕ) :
    M ⊗[S] ↥(⋀[S]^i Y) ≃ₗ[S] M ⊗[R] ↥(⋀[R]^i X) :=
  (TensorProduct.congr (LinearEquiv.refl S M)
      (exteriorPowerEquivOfBaseChange f hf i).symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M ↥(⋀[R]^i X))

/-- The inverse of the tensored comparison carries `m ⊗ x` to `m` tensored with the image of
`x`. -/
@[simp]
public theorem tensorExteriorPowerEquivOfBaseChange_symm_tmul (i : ℕ) (m : M)
    (x : ↥(⋀[R]^i X)) :
    (tensorExteriorPowerEquivOfBaseChange f hf M i).symm (m ⊗ₜ x) =
      m ⊗ₜ exteriorPowerMapOfBaseChange f hf i x := by
  rw [tensorExteriorPowerEquivOfBaseChange, LinearEquiv.symm_trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, TensorProduct.congr_symm,
    LinearEquiv.refl_symm, LinearEquiv.symm_symm, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, exteriorPowerEquivOfBaseChange_tmul, one_smul]

/-- The inverse of the tensored comparison on the standard generators. -/
public theorem tensorExteriorPowerEquivOfBaseChange_symm_tmul_ιMulti (i : ℕ) (m : M)
    (v : Fin i → X) :
    (tensorExteriorPowerEquivOfBaseChange f hf M i).symm
        (m ⊗ₜ exteriorPower.ιMulti R i v) =
      m ⊗ₜ exteriorPower.ιMulti S i fun j ↦ f (v j) := by
  rw [tensorExteriorPowerEquivOfBaseChange_symm_tmul, exteriorPowerMapOfBaseChange_ιMulti]

/-- **The tensored comparison on the standard generators**: a tensor of a section with a wedge of
images is the tensor of the section with the wedge of the elements themselves. -/
public theorem tensorExteriorPowerEquivOfBaseChange_tmul_ιMulti (i : ℕ) (m : M)
    (v : Fin i → X) :
    tensorExteriorPowerEquivOfBaseChange f hf M i
        (m ⊗ₜ exteriorPower.ιMulti S i fun j ↦ f (v j)) =
      m ⊗ₜ exteriorPower.ιMulti R i v := by
  apply (tensorExteriorPowerEquivOfBaseChange f hf M i).symm.injective
  rw [LinearEquiv.symm_apply_apply, tensorExteriorPowerEquivOfBaseChange_symm_tmul,
    exteriorPowerMapOfBaseChange_ιMulti]

end Tensor

end BaseChangeExteriorPower

/-! ### The two degree-one maps at a level -/

section Level

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)

/-- **The reduction of the completion `Ω̂_{B/A,δ}` modulo `pᵏ`.**  The quotient is the one
`Crystalline.completionDifferentialsModPow` takes, by the `pᵏ`-multiples read over the completion
`B̂`, so the reduction is `B̂`-linear and its target is a module over the level ring `B̂/pᵏ`. -/
public noncomputable def completionDifferentialsReductionMap (k : ℕ) :
    AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
        (dividedPowerDifferentials (A := A) delta) →ₗ[
        AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
      completionDifferentialsModPow (A := A) J delta p k :=
  (DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k •
      (⊤ : Submodule (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
        (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
          (dividedPowerDifferentials (A := A) delta)))).mkQ

/-- The reduction sends an element to its class modulo `pᵏ`. -/
@[simp]
public theorem completionDifferentialsReductionMap_apply (k : ℕ)
    (omega : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
      (dividedPowerDifferentials (A := A) delta)) :
    completionDifferentialsReductionMap (A := A) J delta p k omega =
      Submodule.Quotient.mk omega :=
  rfl

/-- **`Ω̂_{B/A,δ} / pᵏ` is the base change of `Ω̂_{B/A,δ}` along `B̂ → B̂/pᵏ`.** -/
public theorem isBaseChange_completionDifferentialsReductionMap (k : ℕ) :
    IsBaseChange
      (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
        DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k)
      (completionDifferentialsReductionMap (A := A) J delta p k) :=
  isBaseChange_mkQ_smulTop _ _

variable (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- **The reduction of the universal differentials `Ω_{B̂/A,γ̂}` modulo `pᵏ`, followed by the level
identification.**  Its target is `Ω̂_{B/A,δ} / pᵏ`, and
`Crystalline.completedDifferentialsLevelLinearEquiv` — [Stacks, Tag 07KK] read at the level
`k = N + e` — is the identification used. -/
public noncomputable def completedDifferentialsLevelMap
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ) :
    dividedPowerDifferentials (A := A) (DividedPowers.completedDividedPowers J delta p hp).1 →ₗ[
        AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
      completionDifferentialsModPow (A := A) J delta p (cmp.quotientSystem.cutoff + e) :=
  (completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e).toLinearMap ∘ₗ
    (DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
          (cmp.quotientSystem.cutoff + e) •
        (⊤ : Submodule (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
          (dividedPowerDifferentials (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1))).mkQ

/-- The level map sends a differential of `B̂` to the image of its class modulo `pᵏ` under the
level identification. -/
@[simp]
public theorem completedDifferentialsLevelMap_apply
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ)
    (omega : dividedPowerDifferentials (A := A)
      (DividedPowers.completedDividedPowers J delta p hp).1) :
    completedDifferentialsLevelMap (A := A) J delta p hp cmp e omega =
      completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e
        (Submodule.Quotient.mk omega) :=
  rfl

/-- **`Ω̂_{B/A,δ} / pᵏ` is also the base change of `Ω_{B̂/A,γ̂}` along `B̂ → B̂/pᵏ`.**  That is the
content of the level identification: the two shapes of the differentials of `B̂` have the same
reduction modulo `pᵏ`, so either one exhibits it as a base change. -/
public theorem isBaseChange_completedDifferentialsLevelMap
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ) :
    IsBaseChange
      (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
        DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
          (cmp.quotientSystem.cutoff + e))
      (completedDifferentialsLevelMap (A := A) J delta p hp cmp e) :=
  isBaseChange_comp_mkQ_smulTop _ _
    (completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e)

/-! ### The level identification in every degree, after tensoring -/

section Tensor

variable (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ)
variable (M : Type*) [AddCommGroup M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
      (cmp.quotientSystem.cutoff + e)) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
        (cmp.quotientSystem.cutoff + e)) M]

/-- **The level identification in degree `i`, after tensoring with a module of the level.**  For a
module `M` over the level ring `B̂/pᵏ`, `k = N + e`,

`M ⊗_{B̂} Ωⁱ_{B̂/A,γ̂} ≃ M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{B/A,δ}`.

Both sides are computed by `Crystalline.tensorExteriorPowerEquivOfBaseChange` out of
`M ⊗_{B̂/pᵏ} ⋀ⁱ_{B̂/pᵏ} (Ω̂_{B/A,δ} / pᵏ)`: the left by
`Crystalline.isBaseChange_completedDifferentialsLevelMap`, the right by
`Crystalline.isBaseChange_completionDifferentialsReductionMap`.  So the identification is one
composed with the inverse of the other, and the tensor products it relates are the uncompleted
ones, which is what the level-`e` step of the source's proof of [Stacks, Tag 07LF] needs. -/
public noncomputable def tensorFormsCompletionLevelEquiv (i : ℕ) :
    M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
        dividedPowerDifferentialForms (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1 i ≃ₗ[
        AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
          DividedPowers.pAdicIdeal
            (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
            (cmp.quotientSystem.cutoff + e)]
      M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
        ↥(⋀[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]^i
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
            (dividedPowerDifferentials (A := A) delta))) :=
  (tensorExteriorPowerEquivOfBaseChange
        (completedDifferentialsLevelMap (A := A) J delta p hp cmp e)
        (isBaseChange_completedDifferentialsLevelMap (A := A) J delta p hp cmp e)
        M i).symm.trans
    (tensorExteriorPowerEquivOfBaseChange
      (completionDifferentialsReductionMap (A := A) J delta p (cmp.quotientSystem.cutoff + e))
      (isBaseChange_completionDifferentialsReductionMap (A := A) J delta p
        (cmp.quotientSystem.cutoff + e)) M i)

/-- **How the level identification in degree `i` is composed**: the inverse of the description of
its source by `Crystalline.completedDifferentialsLevelMap`, followed by the description of its
target by `Crystalline.completionDifferentialsReductionMap`. -/
public theorem tensorFormsCompletionLevelEquiv_apply (i : ℕ)
    (x : M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
      dividedPowerDifferentialForms (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1 i) :
    tensorFormsCompletionLevelEquiv (A := A) J delta p hp cmp e M i x =
      tensorExteriorPowerEquivOfBaseChange
        (completionDifferentialsReductionMap (A := A) J delta p (cmp.quotientSystem.cutoff + e))
        (isBaseChange_completionDifferentialsReductionMap (A := A) J delta p
          (cmp.quotientSystem.cutoff + e)) M i
        ((tensorExteriorPowerEquivOfBaseChange
          (completedDifferentialsLevelMap (A := A) J delta p hp cmp e)
          (isBaseChange_completedDifferentialsLevelMap (A := A) J delta p hp cmp e)
          M i).symm x) :=
  rfl

/-- **The equation pinning the level identification in degree `i` down.**  On a tensor of a
section with a wedge of universal differentials of `B̂` it is, read through the canonical
description `Crystalline.tensorExteriorPowerEquivOfBaseChange` of its target, the wedge of the
classes of those differentials under
`Crystalline.completedDifferentialsLevelLinearEquiv`, slot by slot.  Those wedges span, so no
second identification satisfies the same equation. -/
@[simp]
public theorem tensorFormsCompletionLevelEquiv_tmul_ιMulti (i : ℕ) (m : M)
    (v : Fin i → dividedPowerDifferentials (A := A)
      (DividedPowers.completedDividedPowers J delta p hp).1) :
    tensorFormsCompletionLevelEquiv (A := A) J delta p hp cmp e M i
        (m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i v) =
      tensorExteriorPowerEquivOfBaseChange
        (completionDifferentialsReductionMap (A := A) J delta p (cmp.quotientSystem.cutoff + e))
        (isBaseChange_completionDifferentialsReductionMap (A := A) J delta p
          (cmp.quotientSystem.cutoff + e)) M i
        (m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
            DividedPowers.pAdicIdeal
              (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
              (cmp.quotientSystem.cutoff + e)) i
          fun j ↦ completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e
            (Submodule.Quotient.mk (v j))) := by
  have key : (tensorExteriorPowerEquivOfBaseChange
        (completedDifferentialsLevelMap (A := A) J delta p hp cmp e)
        (isBaseChange_completedDifferentialsLevelMap (A := A) J delta p hp cmp e) M i).symm
        (m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i v) =
      m ⊗ₜ exteriorPower.ιMulti
        (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
          DividedPowers.pAdicIdeal
            (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
            (cmp.quotientSystem.cutoff + e)) i
        (fun j ↦ completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e
          (Submodule.Quotient.mk (v j))) :=
    tensorExteriorPowerEquivOfBaseChange_symm_tmul_ιMulti
      (completedDifferentialsLevelMap (A := A) J delta p hp cmp e)
      (isBaseChange_completedDifferentialsLevelMap (A := A) J delta p hp cmp e) M i m v
  rw [tensorFormsCompletionLevelEquiv_apply]
  exact DFunLike.congr_arg _ key

/-- **The pinning equation with the canonical description of the target cleared away.**  If
differentials `ωⱼ` of `B̂` and elements `ηⱼ` of the completion `Ω̂_{B/A,δ}` have the same class
modulo `pᵏ` under the level identification in every slot, then the identification in degree `i`
carries `m ⊗ ω₁ ∧ ⋯ ∧ ωᵢ` to `m ⊗ η₁ ∧ ⋯ ∧ ηᵢ`.  Such `ηⱼ` exist for every `ωⱼ`, the reduction
being surjective, so this determines the identification on generators of its source. -/
public theorem tensorFormsCompletionLevelEquiv_tmul_ιMulti_of_mk (i : ℕ) (m : M)
    (v : Fin i → dividedPowerDifferentials (A := A)
      (DividedPowers.completedDividedPowers J delta p hp).1)
    (w : Fin i → AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
      (dividedPowerDifferentials (A := A) delta))
    (h : ∀ j, completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e
        (Submodule.Quotient.mk (v j)) = Submodule.Quotient.mk (w j)) :
    tensorFormsCompletionLevelEquiv (A := A) J delta p hp cmp e M i
        (m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i v) =
      m ⊗ₜ exteriorPower.ιMulti
        (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i w := by
  have hfun : (fun j ↦ completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e
        (Submodule.Quotient.mk (v j))) =
      fun j ↦ completionDifferentialsReductionMap (A := A) J delta p
        (cmp.quotientSystem.cutoff + e) (w j) := by
    funext j
    rw [completionDifferentialsReductionMap_apply]
    exact h j
  have key := tensorExteriorPowerEquivOfBaseChange_tmul_ιMulti
    (completionDifferentialsReductionMap (A := A) J delta p (cmp.quotientSystem.cutoff + e))
    (isBaseChange_completionDifferentialsReductionMap (A := A) J delta p
      (cmp.quotientSystem.cutoff + e)) M i m w
  rw [tensorFormsCompletionLevelEquiv_tmul_ιMulti, hfun, key]

end Tensor

end Level

end Crystalline

end
