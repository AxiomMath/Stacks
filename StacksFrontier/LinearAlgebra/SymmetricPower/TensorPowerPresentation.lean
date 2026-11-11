module

public import StacksFrontier.LinearAlgebra.SymmetricPower.QuotientOfTensorPower

/-!
# Presentations of the exterior and symmetric powers, in every universe

This file states Stacks Tag 00DP over a commutative ring `R : Type u` in an arbitrary universe.
Mathlib's symmetric power `SymmetricPower R ι M` takes its index type `ι` in the universe of
`R`, so the notation `Sym[R]^(n + 2) M = SymmetricPower R (Fin (n + 2)) M` only exists for
`R : Type`. Here the symmetric power of degree `n + 2` is
`SymmetricPower R (ULift (Fin (n + 2))) M`, the symmetric power indexed by a set with `n + 2`
elements in the universe of `R`, and the projection from the tensor power `⨂[R]^(n + 2) M`
sends `⨂ₜ k, f k` to `⨂ₛ k, f k.down`.

## Main results

* `exists_presentation_exteriorPower`: the exact sequence
  `(⊕ relators) → Tⁿ⁺²(M) → ⋀ⁿ⁺²(M) → 0`.
* `exists_presentation_symmetricPower`: the exact sequence
  `(⊕ relators) → Tⁿ⁺²(M) → Symⁿ⁺²(M) → 0`.
* `exists_presentation_exteriorPower_and_symmetricPower_univ`: both together (Stacks 00DP).
-/

@[expose] public section

open TensorProduct

universe u

section

variable {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A map out of the tensor power is exact after `Φ` if its kernel lies in the range of `Φ` and it
kills the images of all pure tensors under `Φ`. -/
private theorem exact_of_ker_le_range_of_tprod' {ι : Type*} [DecidableEq ι] {n : ℕ}
    {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (Φ : DirectSum ι (fun _ => ⨂[R]^n M) →ₗ[R] N) (π : N →ₗ[R] P)
    (hker : LinearMap.ker π ≤ LinearMap.range Φ)
    (h : ∀ (c : ι) (g : Fin n → M), π (Φ (DirectSum.lof R _ _ c (⨂ₜ[R] k, g k))) = 0) :
    Function.Exact Φ π := by
  rw [LinearMap.exact_iff]
  exact le_antisymm hker (LinearMap.range_le_ker_iff.2 (DirectSum.linearMap_ext R fun c =>
    PiTensorProduct.ext (MultilinearMap.ext fun g => h c g)))

/-- **Stacks Tag 00DP**, exterior power part. Let `M` be a module over a commutative ring `R`
with a generating system `x : I → M`, and let `n + 2 ≥ 2`. There is an exact sequence
`(⊕_{j₁<j₂} ⊕_{i₁,i₂} Tⁿ(M)) ⊕ (⊕_{j₁<j₂} ⊕_{i} Tⁿ(M)) → Tⁿ⁺²(M) → ⋀ⁿ⁺²(M) → 0` whose first map
sends a pure tensor in the `(j₁, j₂, i₁, i₂)` summand to the symmetrised relator (with `x_{i₁}`,
`x_{i₂}` in slots `j₁, j₂`, plus the swapped term), a pure tensor in the `(j₁, j₂, i)` summand to
the diagonal relator, and whose second map sends `⨂ₜ k, f k` to `ιMulti f`. -/
theorem exists_presentation_exteriorPower {I : Type*} [DecidableEq I] (x : I → M)
    (hx : Submodule.span R (Set.range x) = ⊤) (n : ℕ) :
    ∃ (Φ : DirectSum ((SlotPair n × I × I) ⊕ (SlotPair n × I)) (fun _ => ⨂[R]^n M)
              →ₗ[R] ⨂[R]^(n + 2) M)
       (π : ⨂[R]^(n + 2) M →ₗ[R] ⋀[R]^(n + 2) M),
        (∀ (jp : SlotPair n) (i₁ i₂ : I) (f : Fin n → M),
          Φ (DirectSum.lof R _ _ (Sum.inl (jp, i₁, i₂)) (⨂ₜ[R] k, f k))
            = (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₁) (x i₂) f k)
              + (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₂) (x i₁) f k)) ∧
        (∀ (jp : SlotPair n) (i : I) (f : Fin n → M),
          Φ (DirectSum.lof R _ _ (Sum.inr (jp, i)) (⨂ₜ[R] k, f k))
            = (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i) (x i) f k)) ∧
        (∀ f : Fin (n + 2) → M, π (⨂ₜ[R] k, f k) = exteriorPower.ιMulti R (n + 2) f) ∧
        Function.Exact Φ π ∧ Function.Surjective π := by
  let Φ : DirectSum ((SlotPair n × I × I) ⊕ (SlotPair n × I)) (fun _ => ⨂[R]^n M)
      →ₗ[R] ⨂[R]^(n + 2) M :=
    DirectSum.toModule R _ _ fun c => Sum.elim
      (fun p : SlotPair n × I × I => PiTensorProduct.lift
        (insTwoTprod R p.1.1.1 p.1.1.2 p.1.2 (x p.2.1) (x p.2.2)
          + insTwoTprod R p.1.1.1 p.1.1.2 p.1.2 (x p.2.2) (x p.2.1)))
      (fun p : SlotPair n × I => PiTensorProduct.lift
        (insTwoTprod R p.1.1.1 p.1.1.2 p.1.2 (x p.2) (x p.2))) c
  let π : ⨂[R]^(n + 2) M →ₗ[R] ⋀[R]^(n + 2) M :=
    PiTensorProduct.lift (exteriorPower.ιMulti R (n + 2)).toMultilinearMap
  have hΦ₁ (jp : SlotPair n) (i₁ i₂ : I) (f : Fin n → M) :
      Φ (DirectSum.lof R _ _ (Sum.inl (jp, i₁, i₂)) (⨂ₜ[R] k, f k))
        = (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₁) (x i₂) f k)
          + (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₂) (x i₁) f k) := by
    simp [Φ]
  have hΦ₂ (jp : SlotPair n) (i : I) (f : Fin n → M) :
      Φ (DirectSum.lof R _ _ (Sum.inr (jp, i)) (⨂ₜ[R] k, f k))
        = (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i) (x i) f k) := by
    simp [Φ]
  have hπ (f : Fin (n + 2) → M) : π (⨂ₜ[R] k, f k) = exteriorPower.ιMulti R (n + 2) f := by
    simp [π]
  refine ⟨Φ, π, hΦ₁, hΦ₂, hπ, ?_, ?_⟩
  · refine exact_of_ker_le_range_of_tprod' Φ π ?_ ?_
    · have hE := tprod_mem_of_apply_eq hx (LinearMap.range Φ)
        (fun jp i₁ i₂ g => LinearMap.mem_range.2 ⟨_, hΦ₁ jp i₁ i₂ g⟩)
        (fun jp i g => LinearMap.mem_range.2 ⟨_, hΦ₂ jp i g⟩)
      let A : M [⋀^Fin (n + 2)]→ₗ[R] (⨂[R]^(n + 2) M ⧸ LinearMap.range Φ) :=
        { (LinearMap.range Φ).mkQ.compMultilinearMap (PiTensorProduct.tprod R) with
          map_eq_zero_of_eq' := fun f i j hf hij => by
            simpa [Submodule.Quotient.mk_eq_zero] using hE f hf hij }
      have hL : exteriorPower.alternatingMapLinearEquiv A ∘ₗ π = (LinearMap.range Φ).mkQ :=
        PiTensorProduct.ext (MultilinearMap.ext fun f => by simp [hπ, A])
      intro z hz
      have hz' := LinearMap.congr_fun hL z
      rw [LinearMap.comp_apply, LinearMap.mem_ker.1 hz, map_zero, Submodule.mkQ_apply] at hz'
      exact (Submodule.Quotient.mk_eq_zero _).1 hz'.symm
    · rintro (⟨jp, i₁, i₂⟩ | ⟨jp, i⟩) g
      · have := (exteriorPower.ιMulti R (n + 2)).map_swap_add
          (v := insTwo jp.1.1 jp.1.2 jp.2 (x i₁) (x i₂) g) jp.2.ne
        rw [insTwo_comp_swap] at this
        simpa [hΦ₁, hπ, add_comm] using this
      · simpa [hΦ₂, hπ] using (exteriorPower.ιMulti R (n + 2)).map_eq_zero_of_eq
          (insTwo jp.1.1 jp.1.2 jp.2 (x i) (x i) g)
          ((insTwo_apply_fst _ _ _).trans (insTwo_apply_snd _ _ _).symm) jp.2.ne
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span R (n + 2) M,
      Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact LinearMap.mem_range.2 ⟨_, hπ f⟩

/-- **Stacks Tag 00DP**, symmetric power part. Let `M` be a module over a commutative ring
`R : Type u` with a generating system `x : I → M`, and let `n + 2 ≥ 2`. There is an exact sequence
`(⊕_{j₁<j₂} ⊕_{i₁,i₂} Tⁿ(M)) → Tⁿ⁺²(M) → Symⁿ⁺²(M) → 0` whose first map sends a pure tensor in
the `(j₁, j₂, i₁, i₂)` summand to the antisymmetrised relator (with `x_{i₁}`, `x_{i₂}` in slots
`j₁, j₂`, minus the swapped term), and whose second map sends `⨂ₜ k, f k` to `⨂ₛ k, f k.down`.
The symmetric power is indexed by `ULift (Fin (n + 2))`, a set of `n + 2` slots in the universe
of `R`, as Mathlib's `SymmetricPower` requires. -/
theorem exists_presentation_symmetricPower {I : Type*} [DecidableEq I] (x : I → M)
    (hx : Submodule.span R (Set.range x) = ⊤) (n : ℕ) :
    ∃ (Ψ : DirectSum (SlotPair n × I × I) (fun _ => ⨂[R]^n M) →ₗ[R] ⨂[R]^(n + 2) M)
       (ρ : ⨂[R]^(n + 2) M →ₗ[R] SymmetricPower R (ULift.{u} (Fin (n + 2))) M),
        (∀ (jp : SlotPair n) (i₁ i₂ : I) (f : Fin n → M),
          Ψ (DirectSum.lof R _ _ (jp, i₁, i₂) (⨂ₜ[R] k, f k))
            = (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₁) (x i₂) f k)
              - (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₂) (x i₁) f k)) ∧
        (∀ f : Fin (n + 2) → M, ρ (⨂ₜ[R] k, f k) = ⨂ₛ[R] k, f k.down) ∧
        Function.Exact Ψ ρ ∧ Function.Surjective ρ := by
  let Ψ : DirectSum (SlotPair n × I × I) (fun _ => ⨂[R]^n M) →ₗ[R] ⨂[R]^(n + 2) M :=
    DirectSum.toModule R _ _ fun p => PiTensorProduct.lift
      (insTwoTprod R p.1.1.1 p.1.1.2 p.1.2 (x p.2.1) (x p.2.2)
        - insTwoTprod R p.1.1.1 p.1.1.2 p.1.2 (x p.2.2) (x p.2.1))
  let e : ⨂[R]^(n + 2) M ≃ₗ[R] ⨂[R] _ : ULift.{u} (Fin (n + 2)), M :=
    PiTensorProduct.reindex R (fun _ => M) Equiv.ulift.symm
  have he (f : Fin (n + 2) → M) : e (⨂ₜ[R] k, f k) = ⨂ₜ[R] k, f k.down := by
    simp [e, PiTensorProduct.reindex_tprod]
  have he' (f : ULift.{u} (Fin (n + 2)) → M) :
      e.symm (⨂ₜ[R] k, f k) = ⨂ₜ[R] k, f (ULift.up k) := by
    rw [LinearEquiv.symm_apply_eq, he]
  let ρ := SymmetricPower.mk R (ULift.{u} (Fin (n + 2))) M ∘ₗ e.toLinearMap
  have hΨ (jp : SlotPair n) (i₁ i₂ : I) (f : Fin n → M) :
      Ψ (DirectSum.lof R _ _ (jp, i₁, i₂) (⨂ₜ[R] k, f k))
        = (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₁) (x i₂) f k)
          - (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₂) (x i₁) f k) := by
    simp [Ψ]
  have hρ (f : Fin (n + 2) → M) : ρ (⨂ₜ[R] k, f k) = ⨂ₛ[R] k, f k.down := by
    simp [ρ, he, SymmetricPower.tprod]
  refine ⟨Ψ, ρ, hΨ, hρ, ?_, ?_⟩
  · refine exact_of_ker_le_range_of_tprod' Ψ ρ ?_ ?_
    · intro z hz
      have hle : addConGen (SymmetricPower.Rel R (ULift.{u} (Fin (n + 2))) M)
          ≤ AddCon.ker ((LinearMap.range Ψ).mkQ ∘ₗ e.symm.toLinearMap) := by
        refine AddCon.addConGen_le.2 fun _ _ h => ?_
        obtain ⟨σ, f⟩ := h
        rw [AddCon.ker_rel, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.mkQ_apply, Submodule.Quotient.eq]
        simp only [LinearEquiv.coe_coe, he']
        have := tprod_sub_tprod_perm_mem hx _
          (fun jp i₁ i₂ g => LinearMap.mem_range.2 ⟨_, hΨ jp i₁ i₂ g⟩)
          (Equiv.ulift.symm.trans (σ.trans Equiv.ulift)) (fun k => f (ULift.up k))
        simpa using this
      have hrel : addConGen (SymmetricPower.Rel R (ULift.{u} (Fin (n + 2))) M) (e z) 0 :=
        SymmetricPower.mk_eq_mk_iff.1 ((LinearMap.mem_ker.1 hz).trans (map_zero _).symm)
      simpa using (AddCon.ker_rel _).1 (hle hrel)
    · rintro ⟨jp, i₁, i₂⟩ g
      have := SymmetricPower.tprod_equiv (R := R)
        (Equiv.ulift.trans ((Equiv.swap jp.1.1 jp.1.2).trans Equiv.ulift.symm))
        (fun k : ULift.{u} (Fin (n + 2)) => insTwo jp.1.1 jp.1.2 jp.2 (x i₁) (x i₂) g k.down)
      have hsw (k : Fin (n + 2)) : insTwo jp.1.1 jp.1.2 jp.2 (x i₁) (x i₂) g
          (Equiv.swap jp.1.1 jp.1.2 k) = insTwo jp.1.1 jp.1.2 jp.2 (x i₂) (x i₁) g k :=
        congrFun (insTwo_comp_swap (x i₁) (x i₂) g) k
      simp only [Equiv.trans_apply, Equiv.ulift_symm_down, hsw] at this
      simpa [hΨ, hρ, sub_eq_zero] using this.symm
  · exact (LinearMap.range_eq_top.1 (SymmetricPower.range_mk R _ M)).comp e.surjective

/-- **Stacks Tag 00DP.** Let `M` be a module over a commutative ring `R` (in any universe) with a
generating system `x : I → M`, and let `n + 2 ≥ 2`. There are canonical exact sequences

  `(⊕_{j₁<j₂} ⊕_{i₁,i₂} Tⁿ(M)) ⊕ (⊕_{j₁<j₂} ⊕_{i} Tⁿ(M)) → Tⁿ⁺²(M) → ⋀ⁿ⁺²(M) → 0`   and
  `(⊕_{j₁<j₂} ⊕_{i₁,i₂} Tⁿ(M)) → Tⁿ⁺²(M) → Symⁿ⁺²(M) → 0`,

where a pure tensor `⨂ₜ f` in the `(j₁, j₂, i₁, i₂)` summand maps to the tensor with `x_{i₁}`,
`x_{i₂}` in slots `j₁, j₂` and `f` in the remaining slots, plus (exterior side) or minus
(symmetric side) the same tensor with `x_{i₁}` and `x_{i₂}` swapped; a pure tensor in the
`(j₁, j₂, i)` summand maps to the tensor with `x_i` in both slots `j₁, j₂`; and the projections
send `⨂ₜ f` to `ιMulti f` and to `⨂ₛ f`. The symmetric power is
`SymmetricPower R (ULift (Fin (n + 2))) M`, indexed by `n + 2` slots in the universe of `R`. -/
@[stacks 00DP "Both exact sequences, for a ring in any universe; `n + 2` plays Stacks' `n ≥ 2`."]
theorem exists_presentation_exteriorPower_and_symmetricPower_univ {I : Type*} [DecidableEq I]
    (x : I → M) (hx : Submodule.span R (Set.range x) = ⊤) (n : ℕ) :
    (∃ (Φ : DirectSum ((SlotPair n × I × I) ⊕ (SlotPair n × I)) (fun _ => ⨂[R]^n M)
              →ₗ[R] ⨂[R]^(n + 2) M)
       (π : ⨂[R]^(n + 2) M →ₗ[R] ⋀[R]^(n + 2) M),
        (∀ (jp : SlotPair n) (i₁ i₂ : I) (f : Fin n → M),
          Φ (DirectSum.lof R _ _ (Sum.inl (jp, i₁, i₂)) (⨂ₜ[R] k, f k))
            = (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₁) (x i₂) f k)
              + (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₂) (x i₁) f k)) ∧
        (∀ (jp : SlotPair n) (i : I) (f : Fin n → M),
          Φ (DirectSum.lof R _ _ (Sum.inr (jp, i)) (⨂ₜ[R] k, f k))
            = (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i) (x i) f k)) ∧
        (∀ f : Fin (n + 2) → M, π (⨂ₜ[R] k, f k) = exteriorPower.ιMulti R (n + 2) f) ∧
        Function.Exact Φ π ∧ Function.Surjective π) ∧
    (∃ (Ψ : DirectSum (SlotPair n × I × I) (fun _ => ⨂[R]^n M) →ₗ[R] ⨂[R]^(n + 2) M)
       (ρ : ⨂[R]^(n + 2) M →ₗ[R] SymmetricPower R (ULift.{u} (Fin (n + 2))) M),
        (∀ (jp : SlotPair n) (i₁ i₂ : I) (f : Fin n → M),
          Ψ (DirectSum.lof R _ _ (jp, i₁, i₂) (⨂ₜ[R] k, f k))
            = (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₁) (x i₂) f k)
              - (⨂ₜ[R] k, insTwo jp.1.1 jp.1.2 jp.2 (x i₂) (x i₁) f k)) ∧
        (∀ f : Fin (n + 2) → M, ρ (⨂ₜ[R] k, f k) = ⨂ₛ[R] k, f k.down) ∧
        Function.Exact Ψ ρ ∧ Function.Surjective ρ) :=
  ⟨exists_presentation_exteriorPower x hx n, exists_presentation_symmetricPower x hx n⟩

end
