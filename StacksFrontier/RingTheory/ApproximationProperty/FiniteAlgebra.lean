module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.RingTheory.AdicCompletion.FiniteBaseChange
public import StacksFrontier.RingTheory.ApproximationProperty.Basic

/-!
# The approximation property passes to finite local algebras

Let `(A, 𝔪)` be a Noetherian local ring with the approximation property and let `B` be a local
ring which is a finite `A`-algebra. Then `B` has the approximation property with respect to its
own `𝔪_B`-adic completion `B̂` (C. Rotthaus, Proposition (1.5)).

The proof is a Weil restriction in coordinates. Since `B` is finite over `A` and local, its
completion is the base change `B ⊗[A] Â` (completion commutes with finite base change,
`AdicCompletion.nonempty_algEquiv_tensorProduct_of_isLocalRing`). Choose generators
`w₁, …, wᵣ` of `B` as an `A`-module and generators `z₁, …, zₛ ∈ Aʳ` of the module of relations
among them. A system `f₁ = … = fₘ = 0` over `B` in the variables `Y₁, …, Yₙ` is rewritten in
the coordinates `Yᵢ = ∑ₗ wₗ Yᵢₗ`: there are polynomials `Fⱼₖ` over `A` with
`fⱼ(∑ₗ wₗ Yᵢₗ) = ∑ₖ wₖ Fⱼₖ(Y)`, universally in the `A`-algebra in which the `Yᵢₗ` take their
values. A solution of the system in `B̂ = B ⊗[A] Â` is then written in coordinates over `Â`, and
`∑ₖ wₖ ⊗ Fⱼₖ = 0` means, by right exactness of the tensor product, that the coordinate vector
`(Fⱼₖ)ₖ` is an `Â`-combination of the relations: `Fⱼₖ = ∑ₜ zₜₖ Lⱼₜ`. These are polynomial
equations over `A` in the unknowns `Yᵢₗ` and `Lⱼₜ`, solvable in `Â`; a solution in `A` given by
the approximation property of `A` produces the solution `∑ₗ yᵢₗ wₗ` of the original system in `B`.

## Main results

* `IsLocalRing.HasApproximationProperty.of_finite`: a local ring which is a finite algebra over a
  Noetherian local ring with the approximation property has the approximation property.

## References

* [C. Rotthaus, *Rings with approximation property*, Math. Ann. 287 (1990), 455–466]
* [Stacks Project, Tag 07BX](https://stacks.math.columbia.edu/tag/07BX)
-/

@[expose] public section

universe u v

open IsLocalRing TensorProduct

namespace IsLocalRing.HasApproximationProperty

/-- Every element of `B ⊗[A] C` is a sum `∑ₖ wₖ ⊗ cₖ` when the `wₖ` span `B`. -/
private theorem exists_eq_sum_tmul {A B C : Type*} [CommRing A] [AddCommGroup B] [Module A B]
    [AddCommGroup C] [Module A C] {r : ℕ} (w : Fin r → B)
    (hw : Submodule.span A (Set.range w) = ⊤) (t : B ⊗[A] C) :
    ∃ c : Fin r → C, t = ∑ k, w k ⊗ₜ[A] c k := by
  induction t using TensorProduct.inductionOn with
  | tmul b c =>
    have hb : b ∈ Submodule.span A (Set.range w) := hw ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hb
    refine ⟨fun k => a k • c, ?_⟩
    rw [← ha, TensorProduct.sum_tmul]
    simp [TensorProduct.smul_tmul]
  | add t t' ht ht' =>
    obtain ⟨c, rfl⟩ := ht
    obtain ⟨c', rfl⟩ := ht'
    exact ⟨c + c', by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

/-- Right exactness of the tensor product in coordinates: if `∑ₖ wₖ ⊗ cₖ = 0` in `B ⊗[A] C`,
where the `wₖ` span `B` and the `zₜ` span the module of relations among them, then the
coordinate vector `c` is a combination of the relations `zₜ` with coefficients in `C`. -/
private theorem exists_eq_sum_smul_of_sum_tmul_eq_zero {A B C : Type*} [CommRing A]
    [AddCommGroup B] [Module A B] [AddCommGroup C] [Module A C] {r s : ℕ} (w : Fin r → B)
    (hw : Submodule.span A (Set.range w) = ⊤) (z : Fin s → Fin r → A)
    (hz : Submodule.span A (Set.range z) = LinearMap.ker (Fintype.linearCombination A w))
    (c : Fin r → C) (hc : ∑ k, w k ⊗ₜ[A] c k = 0) :
    ∃ L : Fin s → C, ∀ k, c k = ∑ t, z t k • L t := by
  classical
  set φ := Fintype.linearCombination A w
  set ψ := Fintype.linearCombination A z
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hw]
  have hexact : Function.Exact ψ φ := by
    rw [LinearMap.exact_iff, Fintype.range_linearCombination, hz]
  set u : (Fin r → A) ⊗[A] C := ∑ k, Pi.single k 1 ⊗ₜ[A] c k
  have hu : φ.rTensor C u = 0 := by
    simp [u, φ, map_sum, LinearMap.rTensor_tmul, hc]
  obtain ⟨v, hv⟩ := (rTensor_exact C hexact hφ u).mp hu
  obtain ⟨L, rfl⟩ := exists_eq_sum_tmul (fun t : Fin s => (Pi.single t 1 : Fin s → A))
    (by
      rw [eq_top_iff]
      intro a _
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨a, by ext j; simp [Pi.single_apply]⟩) v
  refine ⟨L, fun k => ?_⟩
  let Θ : (Fin r → A) ⊗[A] C →ₗ[A] C :=
    (TensorProduct.lid A C).toLinearMap ∘ₗ (LinearMap.proj k).rTensor C
  have h1 : Θ u = c k := by
    simp [Θ, u, map_sum, LinearMap.rTensor_tmul, Pi.single_apply]
  have h2 : Θ (ψ.rTensor C (∑ t, Pi.single t 1 ⊗ₜ[A] L t)) = ∑ t, z t k • L t := by
    simp [Θ, ψ, map_sum, LinearMap.rTensor_tmul]
  rw [← h1, ← hv, h2]

/-- The approximation property passes to a finite local algebra `B` over `A` once the completion
of `B` is identified with `B ⊗[A] Â`. -/
private theorem of_finite_of_algEquiv {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : HasApproximationProperty A) {B : Type v} [CommRing B]
    [IsLocalRing B] [Algebra A B] [Module.Finite A B]
    (e : B ⊗[A] AdicCompletion (maximalIdeal A) A ≃ₐ[B] AdicCompletion (maximalIdeal B) B) :
    HasApproximationProperty B := by
  classical
  intro n m f x hx
  obtain ⟨r, w, hw⟩ := Module.Finite.exists_fin (R := A) (M := B)
  obtain ⟨s, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (LinearMap.ker (Fintype.linearCombination A w)))
  have hF : ∀ j, ∃ F : Fin r → MvPolynomial (Fin n × Fin r) A,
      MvPolynomial.aeval (fun i => ∑ l, w l ⊗ₜ[A] MvPolynomial.X (i, l)) (f j) =
        ∑ k, w k ⊗ₜ[A] F k :=
    fun j => exists_eq_sum_tmul w hw _
  choose F hF using hF
  have hnat : ∀ (C : Type u) [CommRing C] [Algebra A C] (c : Fin n × Fin r → C) (j : Fin m),
      MvPolynomial.aeval (fun i => ∑ l, w l ⊗ₜ[A] c (i, l)) (f j) =
        ∑ k, w k ⊗ₜ[A] MvPolynomial.aeval c (F j k) := by
    intro C _ _ c j
    let ev : B ⊗[A] MvPolynomial (Fin n × Fin r) A →ₐ[B] B ⊗[A] C :=
      Algebra.TensorProduct.map (AlgHom.id B B) (MvPolynomial.aeval c)
    have h1 := congrArg ev (hF j)
    rw [MvPolynomial.comp_aeval_apply] at h1
    simpa [ev, map_sum, Algebra.TensorProduct.map_tmul] using h1
  have hx' : ∀ j, MvPolynomial.aeval (fun i => e.symm (x i)) (f j) = 0 := fun j => by
    have := MvPolynomial.comp_aeval_apply x e.symm.toAlgHom (f j)
    rw [hx j, map_zero] at this
    simpa using this.symm
  have hc : ∀ i, ∃ c : Fin r → AdicCompletion (maximalIdeal A) A,
      e.symm (x i) = ∑ l, w l ⊗ₜ[A] c l :=
    fun i => exists_eq_sum_tmul w hw _
  choose ĉ hĉ using hc
  have hL : ∀ j, ∃ L : Fin s → AdicCompletion (maximalIdeal A) A, ∀ k,
      MvPolynomial.aeval (fun il : Fin n × Fin r => ĉ il.1 il.2) (F j k) = ∑ t, z t k • L t := by
    intro j
    apply exists_eq_sum_smul_of_sum_tmul_eq_zero w hw z hz
    rw [← hnat]
    have := hx' j
    simp only [hĉ] at this
    exact this
  choose L hL using hL
  let G : Fin m × Fin r → MvPolynomial ((Fin n × Fin r) ⊕ (Fin m × Fin s)) A := fun jk =>
    MvPolynomial.rename Sum.inl (F jk.1 jk.2) -
      ∑ t, MvPolynomial.C (z t jk.2) * MvPolynomial.X (Sum.inr (jk.1, t))
  let ξ : (Fin n × Fin r) ⊕ (Fin m × Fin s) → AdicCompletion (maximalIdeal A) A := fun
    | Sum.inl il => ĉ il.1 il.2
    | Sum.inr jt => L jt.1 jt.2
  obtain ⟨y, hy⟩ := hA.exists_aeval_eq_zero G ξ (by
    rintro ⟨j, k⟩
    simp only [G, map_sub, map_sum, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X]
    rw [sub_eq_zero]
    exact (hL j k).trans (by simp [ξ, Algebra.smul_def]))
  have hzk : ∀ t, ∑ k, z t k • w k = 0 := fun t => by
    have : z t ∈ LinearMap.ker (Fintype.linearCombination A w) :=
      hz ▸ Submodule.subset_span ⟨t, rfl⟩
    simpa [Fintype.linearCombination_apply] using this
  refine ⟨fun i => ∑ l, y (Sum.inl (i, l)) • w l, fun j => ?_⟩
  have hyk : ∀ k, MvPolynomial.aeval (fun il => y (Sum.inl il)) (F j k) =
      ∑ t, z t k * y (Sum.inr (j, t)) := fun k => by
    have := hy (j, k)
    simp only [G, map_sub, map_sum, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply] at this
    exact sub_eq_zero.mp this
  let ρ := Algebra.TensorProduct.rid A B B
  have h1 := MvPolynomial.comp_aeval_apply (fun i => ∑ l, w l ⊗ₜ[A] y (Sum.inl (i, l)))
    ρ.toAlgHom (f j)
  rw [hnat A (fun il => y (Sum.inl il)) j] at h1
  have h2 : (fun i => ρ.toAlgHom (∑ l, w l ⊗ₜ[A] y (Sum.inl (i, l)))) =
      fun i => ∑ l, y (Sum.inl (i, l)) • w l := by
    funext i
    simp [ρ, map_sum]
  rw [h2] at h1
  rw [← h1]
  simp only [AlgEquiv.coe_toAlgHom, map_sum, ρ, Algebra.TensorProduct.rid_tmul, hyk]
  calc ∑ k, (∑ t, z t k * y (Sum.inr (j, t))) • w k
      = ∑ t, y (Sum.inr (j, t)) • ∑ k, z t k • w k := by
        simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp_rw [mul_comm]
    _ = 0 := by simp [hzk]

/-- **The approximation property passes to finite local algebras** (Rotthaus, Proposition
(1.5)). Let `A` be a Noetherian local ring with the approximation property and let `B` be a local
ring which is a finite `A`-algebra. Then `B` has the approximation property, with respect to its
own completion `B̂ = lim B/𝔪_Bⁿ`. -/
theorem of_finite {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : HasApproximationProperty A) {B : Type v} [CommRing B] [IsLocalRing B] [Algebra A B]
    [Module.Finite A B] : HasApproximationProperty B := by
  have : IsLocalHom (algebraMap A B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 5 1).mp
      (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (maximalIdeal B)))
  obtain ⟨e⟩ := AdicCompletion.nonempty_algEquiv_tensorProduct_of_isLocalRing A B
  exact of_finite_of_algEquiv hA e

end IsLocalRing.HasApproximationProperty

end
