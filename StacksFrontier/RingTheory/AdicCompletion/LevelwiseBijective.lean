module

public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange
public import StacksFrontier.RingTheory.AdicCompletion.EventuallyBijective

/-!
# Levelwise bijectivity is preserved by tensoring and by exterior powers

Let `K` be an ideal of a commutative ring `S` and let `g : X →ₗ[S] Y`.  Reducing modulo `K` is the
same as tensoring with `S ⧸ K`: the reduction `g.reduceModIdeal K` and the base change
`LinearMap.baseChange (S ⧸ K) g` are conjugate under `TensorProduct.quotTensorEquivQuotSMul`, so
one is bijective exactly when the other is.  In the tensored shape the two operations we need
commute with the base change:

* `S ⧸ K ⊗ (W ⊗ X) ≃ W ⊗ (S ⧸ K ⊗ X)` is `TensorProduct.leftComm`, which turns the base change of
  `W ⊗ g` into `W ⊗` of the base change of `g`;
* `S ⧸ K ⊗ ⋀ⁱ X ≃ ⋀ⁱ_{S ⧸ K} (S ⧸ K ⊗ X)` is `ExteriorAlgebra.exteriorPowerBaseChange`, which
  turns the base change of `⋀ⁱ g` into `⋀ⁱ` of the base change of `g`.

Since both operations carry a linear equivalence to a linear equivalence, bijectivity modulo `K` is
inherited by `W ⊗ g` and by `⋀ⁱ g`.  No flatness and no finiteness hypothesis appears: exterior
powers commute with base change for an arbitrary commutative algebra
(`ExteriorAlgebra.exteriorPowerBaseChange`), and the quotient `S ⧸ K` is one.

Together with `Crystalline.map_bijective_of_reduceModIdeal_eventually` this is what upgrades a
degree-one identification of two `p`-adic systems to an identification of the terms
`M ⊗ ⋀ⁱ Ω` of the two de Rham complexes built from them.

## Main results

* `Crystalline.bijective_reduceModIdeal_iff_baseChange` — the reduction and the base change along
  `S → S ⧸ K` are bijective together.
* `Crystalline.bijective_reduceModIdeal_lTensor` — levelwise bijectivity is inherited by `W ⊗ g`.
* `Crystalline.bijective_reduceModIdeal_exteriorPowerMap` — levelwise bijectivity is inherited by
  `⋀ⁱ g`.
-/

@[expose] public section

open scoped TensorProduct

namespace Crystalline

universe u v w

/-- Two maps conjugate by bijections are bijective together. -/
private theorem bijective_iff_of_comm {alpha beta gamma delta : Type*} {a : alpha → gamma}
    {b : beta → delta} {u : alpha → beta} {v : gamma → delta} (hu : Function.Bijective u)
    (hv : Function.Bijective v) (hcomm : v ∘ a = b ∘ u) :
    Function.Bijective a ↔ Function.Bijective b := by
  refine ⟨fun ha ↦ ?_, fun hb ↦ ?_⟩
  · refine (Function.Bijective.of_comp_iff b hu).mp ?_
    rw [← hcomm]
    exact hv.comp ha
  · refine (Function.Bijective.of_comp_iff' hv a).mp ?_
    rw [hcomm]
    exact hb.comp hu

section Reduction

variable {S : Type u} [CommRing S] {X : Type v} [AddCommGroup X] [Module S X]
  {Y : Type w} [AddCommGroup Y] [Module S Y]

/-- Reducing modulo `K` and tensoring with `S ⧸ K` are conjugate under
`TensorProduct.quotTensorEquivQuotSMul`. -/
theorem quotTensorEquivQuotSMul_baseChange (K : Ideal S) (g : X →ₗ[S] Y)
    (t : (S ⧸ K) ⊗[S] X) :
    TensorProduct.quotTensorEquivQuotSMul Y K (LinearMap.baseChange (S ⧸ K) g t) =
      g.reduceModIdeal K (TensorProduct.quotTensorEquivQuotSMul X K t) := by
  induction t with
  | add t t' ht ht' => simp [ht, ht']
  | tmul r x =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [LinearMap.baseChange_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
      TensorProduct.quotTensorEquivQuotSMul_mk_tmul, LinearMap.reduceModIdeal_apply,
      map_smul]

/-- **Levelwise bijectivity is the same as bijectivity after tensoring with `S ⧸ K`.** -/
theorem bijective_reduceModIdeal_iff_baseChange (K : Ideal S) (g : X →ₗ[S] Y) :
    Function.Bijective (LinearMap.baseChange (S ⧸ K) g) ↔
      Function.Bijective (g.reduceModIdeal K) :=
  bijective_iff_of_comm (TensorProduct.quotTensorEquivQuotSMul X K).bijective
    (TensorProduct.quotTensorEquivQuotSMul Y K).bijective
    (funext fun t ↦ quotTensorEquivQuotSMul_baseChange K g t)

end Reduction

section Tensor

variable {S : Type u} [CommRing S] {X Y : Type v} [AddCommGroup X] [Module S X]
  [AddCommGroup Y] [Module S Y] {W : Type w} [AddCommGroup W] [Module S W]

/-- The base change of `W ⊗ g` is `W ⊗` of the base change of `g`, read through
`TensorProduct.leftComm`. -/
theorem leftComm_baseChange_lTensor (K : Ideal S) (g : X →ₗ[S] Y)
    (t : (S ⧸ K) ⊗[S] (W ⊗[S] X)) :
    TensorProduct.leftComm S (S ⧸ K) W Y
        (LinearMap.baseChange (S ⧸ K) (LinearMap.lTensor W g) t) =
      LinearMap.lTensor W ((LinearMap.baseChange (S ⧸ K) g).restrictScalars S)
        (TensorProduct.leftComm S (S ⧸ K) W X t) := by
  induction t with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul r t =>
    induction t with
    | add u u' hu hu' => simp only [TensorProduct.tmul_add, map_add, hu, hu']
    | tmul w x => simp [TensorProduct.leftComm_tmul]

/-- The functorial map `W ⊗ e` of a linear equivalence is bijective. -/
theorem bijective_lTensor (e : X ≃ₗ[S] Y) (W : Type w) [AddCommGroup W] [Module S W] :
    Function.Bijective (LinearMap.lTensor W e.toLinearMap) := by
  exact (LinearEquiv.lTensor W e).bijective

/-- **Tensoring preserves levelwise bijectivity.**  If `g` is bijective modulo `K`, so is
`W ⊗ g`. -/
theorem bijective_reduceModIdeal_lTensor (K : Ideal S) (g : X →ₗ[S] Y)
    (h : Function.Bijective (g.reduceModIdeal K)) (W : Type w) [AddCommGroup W] [Module S W] :
    Function.Bijective ((LinearMap.lTensor W g).reduceModIdeal K) := by
  rw [← bijective_reduceModIdeal_iff_baseChange] at h ⊢
  let e : (S ⧸ K) ⊗[S] X ≃ₗ[S] (S ⧸ K) ⊗[S] Y :=
    LinearEquiv.ofBijective ((LinearMap.baseChange (S ⧸ K) g).restrictScalars S) h
  exact (bijective_iff_of_comm (TensorProduct.leftComm S (S ⧸ K) W X).bijective
    (TensorProduct.leftComm S (S ⧸ K) W Y).bijective
    (funext fun t ↦ leftComm_baseChange_lTensor K g t)).mpr (bijective_lTensor e W)

end Tensor

section Exterior

variable {S : Type u} [CommRing S] {X Y : Type v} [AddCommGroup X] [Module S X]
  [AddCommGroup Y] [Module S Y]

/-- The exterior power of a linear equivalence is bijective. -/
theorem bijective_exteriorPowerMap (i : ℕ) (e : X ≃ₗ[S] Y) :
    Function.Bijective (exteriorPower.map i e.toLinearMap) := by
  have h1 := e.symm_comp
  have h2 := e.comp_symm
  refine (LinearEquiv.ofLinearMap (exteriorPower.map i e.toLinearMap)
    (exteriorPower.map i e.symm.toLinearMap) ?_ ?_ : (⋀[S]^i X) ≃ₗ[S] (⋀[S]^i Y)).bijective
  · rw [← exteriorPower.map_comp, h2, exteriorPower.map_id]
  · rw [← exteriorPower.map_comp, h1, exteriorPower.map_id]

/-- The base change of `⋀ⁱ g` is `⋀ⁱ` of the base change of `g`, read through
`ExteriorAlgebra.exteriorPowerBaseChange`. -/
theorem exteriorPowerBaseChange_baseChange_map (K : Ideal S) (g : X →ₗ[S] Y) (i : ℕ)
    (t : (S ⧸ K) ⊗[S] (⋀[S]^i X)) :
    ExteriorAlgebra.exteriorPowerBaseChange S (S ⧸ K) Y i
        (LinearMap.baseChange (S ⧸ K) (exteriorPower.map i g) t) =
      exteriorPower.map i (LinearMap.baseChange (S ⧸ K) g)
        (ExteriorAlgebra.exteriorPowerBaseChange S (S ⧸ K) X i t) := by
  have key : ∀ x ∈ Submodule.span S (Set.range (exteriorPower.ιMulti S i (M := X))),
      ∀ r : S ⧸ K,
        ExteriorAlgebra.exteriorPowerBaseChange S (S ⧸ K) Y i
            (LinearMap.baseChange (S ⧸ K) (exteriorPower.map i g) (r ⊗ₜ[S] x)) =
          exteriorPower.map i (LinearMap.baseChange (S ⧸ K) g)
            (ExteriorAlgebra.exteriorPowerBaseChange S (S ⧸ K) X i (r ⊗ₜ[S] x)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      intro r
      have hfun : (fun j ↦ (1 : S ⧸ K) ⊗ₜ[S] (g ∘ v) j) =
          (LinearMap.baseChange (S ⧸ K) g) ∘ (fun j ↦ (1 : S ⧸ K) ⊗ₜ[S] v j) :=
        funext fun j ↦ (g.baseChange_tmul (A := S ⧸ K) 1 (v j)).symm
      rw [LinearMap.baseChange_tmul, exteriorPower.map_apply_ιMulti,
        ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti,
        ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti, map_smul,
        exteriorPower.map_apply_ιMulti, hfun]
    | zero =>
      intro r
      simp
    | add u u' _ _ hu hu' =>
      intro r
      simp only [TensorProduct.tmul_add, map_add, hu, hu']
    | smul s u _ hu =>
      intro r
      rw [← TensorProduct.smul_tmul]
      exact hu (s • r)
  induction t with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul r x =>
    exact key x (by rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top) r

/-- **Exterior powers preserve levelwise bijectivity.**  If `g` is bijective modulo `K`, so is
`⋀ⁱ g`. -/
theorem bijective_reduceModIdeal_exteriorPowerMap (K : Ideal S) (g : X →ₗ[S] Y) (i : ℕ)
    (h : Function.Bijective (g.reduceModIdeal K)) :
    Function.Bijective ((exteriorPower.map i g).reduceModIdeal K) := by
  rw [← bijective_reduceModIdeal_iff_baseChange] at h ⊢
  let e : (S ⧸ K) ⊗[S] X ≃ₗ[S ⧸ K] (S ⧸ K) ⊗[S] Y :=
    LinearEquiv.ofBijective (LinearMap.baseChange (S ⧸ K) g) h
  exact (bijective_iff_of_comm
    (ExteriorAlgebra.exteriorPowerBaseChange S (S ⧸ K) X i).bijective
    (ExteriorAlgebra.exteriorPowerBaseChange S (S ⧸ K) Y i).bijective
    (funext fun t ↦ exteriorPowerBaseChange_baseChange_map K g i t)).mpr
      (bijective_exteriorPowerMap i e)

end Exterior

end Crystalline

end
