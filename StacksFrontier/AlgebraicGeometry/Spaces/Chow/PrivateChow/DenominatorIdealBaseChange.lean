module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel

/-!
# Ideals of denominators and flat base change

Let `R → A` be a flat ring map, let `j : M → P` be an injective map of `R`-modules and `x ∈ P`.
The *ideal of denominators* of `x` relative to `j` is `{r ∈ R : r x ∈ j(M)}`. If `j' : M' → P'` is
an injective map of `A`-modules identified with `A ⊗_R j` by bijective comparison maps carrying
`1 ⊗ x` to `x' ∈ P'`, then the ideal of denominators of `x'` relative to `j'` is the extension of
the ideal of denominators of `x`, and the comparison `A ⊗_R {r : r x ∈ j(M)} → {a : a x' ∈ j'(M')}`
is bijective.

## Main definitions

* `Module.denominatorIdeal`: the ideal of denominators `{r ∈ R : r x ∈ j(M)}` of `x ∈ P`
  relative to `j : M → P`, the preimage of `range j` under `r ↦ r • x`.
* `Module.idealBaseChange`: the extension `A ⊗_R I → A`, `a ⊗ r ↦ a r`, of an ideal of `R`.

## Main results

* `Module.injective_idealBaseChange_and_range`: flat base change of an ideal of denominators —
  the extension of the ideal of denominators of `x` is injective, with image the ideal of
  denominators of `x'`.
-/

@[expose] public section

open TensorProduct

namespace Module

variable {R : Type*} [CommRing R] {M P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

/-- The ideal of denominators `{r ∈ R : r x ∈ j(M)}` of `x ∈ P` relative to `j : M → P`. -/
def denominatorIdeal (j : M →ₗ[R] P) (x : P) : Ideal R :=
  (LinearMap.range j).comap (LinearMap.toSpanSingleton R P x)

/-- An element `r ∈ R` lies in the ideal of denominators of `x` relative to `j` if and only if
`r • x = j m` for some `m ∈ M`. -/
theorem mem_denominatorIdeal_iff (j : M →ₗ[R] P) (x : P) (r : R) :
    r ∈ denominatorIdeal j x ↔ ∃ m, j m = r • x :=
  Iff.rfl

variable {A : Type*} [CommRing A] [Algebra R A]
  {M' P' : Type*} [AddCommGroup M'] [Module A M'] [AddCommGroup P'] [Module A P']

/-- The extension `A ⊗_R I → A`, `a ⊗ r ↦ a r`, of an ideal of `R`. -/
noncomputable def idealBaseChange (I : Ideal R) : A ⊗[R] I →ₗ[A] A :=
  LinearMap.liftBaseChange A ((Algebra.linearMap R A).comp I.subtype)

/-- The extension `A ⊗_R I → A` sends `a ⊗ r` to `a * r`. -/
@[simp]
theorem idealBaseChange_tmul (I : Ideal R) (a : A) (r : I) :
    idealBaseChange I (a ⊗ₜ[R] r) = a * algebraMap R A r := by
  simp [idealBaseChange]

/-- **Flat base change of an ideal of denominators.** Let `R → A` be flat, `j : M → P` and
`j' : M' → P'` maps of modules over `R` and over `A`, and `cM : A ⊗ M → M'`,
`cP : A ⊗ P → P'` comparison maps with `cM` surjective, `cP` injective, `j' ∘ cM = cP ∘ (A ⊗ j)`
and `cP (a ⊗ x) = a x'`. Then the extension `A ⊗_R {r : r x ∈ j(M)} → A` is injective with image
`{a : a x' ∈ j'(M')}`. -/
theorem injective_idealBaseChange_and_range [Module.Flat R A] (j : M →ₗ[R] P) (x : P)
    (j' : M' →ₗ[A] P') (x' : P') (cM : A ⊗[R] M →ₗ[A] M') (cP : A ⊗[R] P →ₗ[A] P')
    (hcM : Function.Surjective cM) (hcP : Function.Injective cP)
    (hsq : ∀ z, j' (cM z) = cP (LinearMap.lTensor A j z))
    (hx : ∀ a : A, cP (a ⊗ₜ[R] x) = a • x') (D : Ideal R)
    (hD : ∀ r, r ∈ D ↔ ∃ m, j m = r • x) (D' : Ideal A)
    (hD' : ∀ a, a ∈ D' ↔ ∃ m, j' m = a • x') :
    Function.Injective (idealBaseChange (A := A) D) ∧
      ∀ a : A, a ∈ D' ↔ ∃ z, idealBaseChange (A := A) D z = a := by
  obtain rfl : D = denominatorIdeal j x := Submodule.ext hD
  obtain rfl : D' = denominatorIdeal j' x' := Submodule.ext hD'
  set D := denominatorIdeal j x
  have hrid : ∀ z : A ⊗[R] D, idealBaseChange (A := A) D z =
      TensorProduct.AlgebraTensorModule.rid R A A (LinearMap.lTensor A D.subtype z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]
    | tmul a r => simp [Algebra.smul_def, mul_comm]
  refine ⟨fun z w h => ?_, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · rw [hrid, hrid] at h
    exact Module.Flat.lTensor_preserves_injective_linearMap D.subtype Subtype.val_injective
      ((TensorProduct.AlgebraTensorModule.rid R A A).injective h)
  · obtain ⟨m', hm'⟩ := ha
    obtain ⟨w, rfl⟩ := hcM m'
    let ψ : R →ₗ[R] P ⧸ LinearMap.range j :=
      (LinearMap.range j).mkQ.comp (LinearMap.toSpanSingleton R P x)
    have hex : Function.Exact D.subtype ψ := by
      intro r
      simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Set.mem_range, Submodule.coe_subtype, Subtype.exists, exists_prop, exists_eq_right]
      rfl
    have hax : a ⊗ₜ[R] x = LinearMap.lTensor A j w := by
      refine hcP ?_
      rw [hx, ← hsq, hm', LinearMap.toSpanSingleton_apply]
    have hzero : LinearMap.lTensor A ψ (a ⊗ₜ[R] (1 : R)) = 0 := by
      have : LinearMap.lTensor A ψ (a ⊗ₜ[R] (1 : R)) =
          LinearMap.lTensor A ((LinearMap.range j).mkQ.comp j) w := by
        rw [LinearMap.lTensor_tmul, LinearMap.lTensor_comp_apply, ← hax]
        simp [ψ]
      rw [this]
      have h0 : (LinearMap.range j).mkQ.comp j = 0 := by
        ext m
        simp
      rw [h0, LinearMap.lTensor_zero, LinearMap.zero_apply]
    obtain ⟨z, hz⟩ := (Module.Flat.lTensor_exact A hex (a ⊗ₜ[R] (1 : R))).1 hzero
    refine ⟨z, ?_⟩
    rw [hrid, hz]
    simp
  · rintro ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => rw [map_add]; exact (denominatorIdeal j' x').add_mem hz hw
    | tmul a r =>
      obtain ⟨m, hm⟩ := r.2
      refine ⟨cM (a ⊗ₜ[R] m), ?_⟩
      rw [idealBaseChange_tmul, hsq, LinearMap.lTensor_tmul,
        show j m = (r : R) • x from hm, ← TensorProduct.smul_tmul, hx,
        LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_comm]

end Module

end
