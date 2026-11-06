module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# A universal algebra for idempotents after base change

For a finite, finitely presented algebra `B` over `A`, the functor sending an `A`-algebra `A'`
to the idempotents of `B ⊗[A] A'` admits a finitely presented weakly universal object: an
`A`-algebra carrying one idempotent from which every idempotent after base change is obtained
by specialization.

## Main results

* `Algebra.exists_finitePresentation_algebra_universal_for_idempotents` constructs a finitely
  presented `A`-algebra carrying an idempotent from which every idempotent after base change is
  obtained.

## Implementation notes

The universal property asserts existence, rather than uniqueness, of the specializing algebra
homomorphism. Its action on the universal idempotent is expressed using the functorial map on
tensor products.

The construction presents `B` as the cokernel of a map of finite free `A`-modules, writes the
multiplication table of the chosen generators in those coordinates, and takes the quotient of a
polynomial ring by the resulting idempotency equations.

## References

* [Stacks Project, Tag 0F3M](https://stacks.math.columbia.edu/tag/0F3M)
-/

@[expose] public section

universe u v w

open Algebra TensorProduct

/-- The coordinates of a base change of a finite free module: `(Fin n → A) ⊗[A] S` is the
module of `S`-valued functions on `Fin n`. -/
private noncomputable def coordEquiv (A S : Type*) [CommRing A] [CommRing S]
    [Algebra A S] (n : ℕ) : ((Fin n → A) ⊗[A] S) ≃ₗ[A] (Fin n → S) :=
  (TensorProduct.piLeft A S (fun _ : Fin n => A)).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.lid A S)

private lemma coordEquiv_tmul (A S : Type*) [CommRing A] [CommRing S]
    [Algebra A S] (n : ℕ) (x : Fin n → A) (s : S) (i : Fin n) :
    coordEquiv A S n (x ⊗ₜ[A] s) i = x i • s := by
  simp [coordEquiv]

private lemma coordEquiv_symm_apply (A S : Type*) [CommRing A] [CommRing S]
    [Algebra A S] (n : ℕ) (a : Fin n → S) :
    (coordEquiv A S n).symm a = ∑ i, Pi.single i 1 ⊗ₜ[A] a i := by
  apply (coordEquiv A S n).injective
  ext i
  simp [coordEquiv, TensorProduct.piLeft, Pi.single_apply]

/-- Every element of `(Fin n → A) ⊗[A] S` is the sum of its coordinates times the basis. -/
private lemma coordEquiv_decomp (A S : Type*) [CommRing A] [CommRing S]
    [Algebra A S] (n : ℕ) (x : (Fin n → A) ⊗[A] S) :
    x = ∑ i, Pi.single i 1 ⊗ₜ[A] coordEquiv A S n x i := by
  simpa using coordEquiv_symm_apply A S n (coordEquiv A S n x)

/-- The idempotency defect of `∑ q eᵢ ⊗ sᵢ` is the image under `q` of the defect computed with the
multiplication table `c`. -/
private lemma mul_self_sub_self_eq_rTensor (A B S : Type*) [CommRing A] [CommRing B]
    [CommRing S] [Algebra A B] [Algebra A S] {n : ℕ} (q : (Fin n → A) →ₗ[A] B)
    (c : Fin n → Fin n → Fin n → A)
    (hc : ∀ i j, q (c i j) = q (Pi.single i 1) * q (Pi.single j 1)) (s : Fin n → S) :
    (∑ i, q (Pi.single i 1) ⊗ₜ[A] s i) * (∑ i, q (Pi.single i 1) ⊗ₜ[A] s i) -
        ∑ i, q (Pi.single i 1) ⊗ₜ[A] s i =
      q.rTensor S ((∑ i, ∑ j, c i j ⊗ₜ[A] (s i * s j)) - ∑ i, Pi.single i 1 ⊗ₜ[A] s i) := by
  calc
    _ = (∑ i, ∑ j, (q (Pi.single i 1) * q (Pi.single j 1)) ⊗ₜ[A] (s i * s j)) -
          ∑ i, q (Pi.single i 1) ⊗ₜ[A] s i := by
      simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
      rw [Finset.sum_comm]
    _ = _ := by simp [hc, map_sub, map_sum, LinearMap.rTensor_tmul]

/-- **Stacks Project, Tag 0F3M.** A finite, finitely presented algebra has a finitely
presented weakly universal base change equipped with an idempotent: every idempotent after an
arbitrary base change is the image of the universal one under some specialization. -/
@[stacks 0F3M]
theorem Algebra.exists_finitePresentation_algebra_universal_for_idempotents
    (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.FinitePresentation A B] :
    ∃ (Auniv : Type (max u v)) (_ : CommRing Auniv) (_ : Algebra A Auniv)
      (_ : Algebra.FinitePresentation A Auniv)
      (euniv : B ⊗[A] Auniv),
      IsIdempotentElem euniv ∧
        ∀ (A' : Type w) [CommRing A'] [Algebra A A'] (e : B ⊗[A] A'),
          IsIdempotentElem e →
            ∃ f : Auniv →ₐ[A] A',
              Algebra.TensorProduct.map (AlgHom.id A B) f euniv = e := by
  classical
  let : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B
  obtain ⟨n, m, q, g, hq, hExact⟩ := Module.FinitePresentation.exists_fin' A B
  let c : Fin n → Fin n → Fin n → A := fun i j =>
    (hq (q (Pi.single i 1) * q (Pi.single j 1))).choose
  have hc : ∀ i j, q (c i j) = q (Pi.single i 1) * q (Pi.single j 1) := fun i j =>
    (hq (q (Pi.single i 1) * q (Pi.single j 1))).choose_spec
  let P := MvPolynomial (Fin n ⊕ Fin m) A
  let z : Fin n → P := fun i => MvPolynomial.X (Sum.inl i)
  let y : Fin m → P := fun k => MvPolynomial.X (Sum.inr k)
  let eqn : Fin n → P := fun i =>
    (∑ j, ∑ k, c j k i • (z j * z k)) - z i - ∑ k, g (Pi.single k 1) i • y k
  let I : Ideal P := Ideal.span (Set.range eqn)
  let U := P ⧸ I
  let : CommRing U := inferInstance
  let : Algebra A U := inferInstance
  have hfpU : Algebra.FinitePresentation A U :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range eqn))
  let Auniv := ULift.{max u v} U
  let : CommRing Auniv := inferInstance
  let : Algebra A Auniv := inferInstance
  let eUL : Auniv ≃ₐ[A] U := ULift.algEquiv
  let : Algebra.FinitePresentation A Auniv := hfpU.equiv eUL.symm
  let κ₀ : P →ₐ[A] U := Ideal.Quotient.mkₐ A I
  let eU : B ⊗[A] U := ∑ i, q (Pi.single i 1) ⊗ₜ[A] κ₀ (z i)
  refine ⟨Auniv, inferInstance, inferInstance, inferInstance,
    Algebra.TensorProduct.map (AlgHom.id A B) eUL.symm.toAlgHom eU, ?_, ?_⟩
  · refine IsIdempotentElem.map ?_ (Algebra.TensorProduct.map (AlgHom.id A B) eUL.symm.toAlgHom)
    let s : Fin n → U := fun i => κ₀ (z i)
    have hd : (∑ i, ∑ j, c i j ⊗ₜ[A] (s i * s j)) - ∑ i, Pi.single i 1 ⊗ₜ[A] s i =
        g.rTensor U (∑ k, Pi.single k 1 ⊗ₜ[A] κ₀ (y k)) := by
      rw [← sub_eq_zero]
      apply (coordEquiv A U n).injective
      ext i
      have h : κ₀ (eqn i) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
      simp only [eqn, map_sub, map_sum, map_smul, map_mul] at h
      simpa [s, coordEquiv, TensorProduct.piLeft, LinearMap.rTensor_tmul, Pi.single_apply,
        map_sub, map_sum, map_smul] using h
    rw [IsIdempotentElem, ← sub_eq_zero]
    refine (mul_self_sub_self_eq_rTensor A B U q c hc s).trans ?_
    rw [hd, ← LinearMap.rTensor_comp_apply, hExact.linearMap_comp_eq_zero]
    simp
  · intro A' _ _ e he
    obtain ⟨ξ, rfl⟩ := LinearMap.rTensor_surjective A' hq e
    have hξ := coordEquiv_decomp A A' n ξ
    generalize coordEquiv A A' n ξ = s at hξ
    subst hξ
    have he' : q.rTensor A' (∑ i, Pi.single i 1 ⊗ₜ[A] s i) = ∑ i, q (Pi.single i 1) ⊗ₜ[A] s i := by
      simp [LinearMap.rTensor_tmul]
    have hd : q.rTensor A' ((∑ i, ∑ j, c i j ⊗ₜ[A] (s i * s j)) - ∑ i, Pi.single i 1 ⊗ₜ[A] s i) =
        0 := by
      rw [← mul_self_sub_self_eq_rTensor A B A' q c hc s, ← he', he.eq, sub_self]
    obtain ⟨η, hη⟩ := (rTensor_exact A' hExact hq _).1 hd
    have hηc := coordEquiv_decomp A A' m η
    generalize coordEquiv A A' m η = t at hηc
    subst hηc
    have hst (i : Fin n) :
        (∑ j, ∑ k, c j k i • (s j * s k)) - s i - ∑ k, g (Pi.single k 1) i • t k = 0 := by
      have hrel : coordEquiv A A' n ((∑ j, ∑ k, c j k ⊗ₜ[A] (s j * s k)) -
          ∑ j, Pi.single j 1 ⊗ₜ[A] s j - g.rTensor A' (∑ k, Pi.single k 1 ⊗ₜ[A] t k)) i =
            (∑ j, ∑ k, c j k i • (s j * s k)) - s i - ∑ k, g (Pi.single k 1) i • t k := by
        simp [coordEquiv, TensorProduct.piLeft, LinearMap.rTensor_tmul, Pi.single_apply, map_sub,
          map_sum]
      rw [← hrel, hη, sub_self]
      simp
    let ev : P →ₐ[A] A' := MvPolynomial.aeval (Sum.elim s t)
    have hevZ (i : Fin n) : ev (z i) = s i := MvPolynomial.aeval_X _ _
    have hevY (k : Fin m) : ev (y k) = t k := MvPolynomial.aeval_X _ _
    have hev (i : Fin n) : ev (eqn i) = 0 := by
      simpa only [eqn, map_sub, map_sum, map_smul, map_mul, hevZ, hevY] using hst i
    have hI : I ≤ RingHom.ker ev.toRingHom := Ideal.span_le.2 (Set.range_subset_iff.2 hev)
    let f₀ : U →ₐ[A] A' := Ideal.Quotient.liftₐ I ev fun _ hp => hI hp
    have hf₀ (i : Fin n) : f₀ (κ₀ (z i)) = s i :=
      (AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I ev fun _ hp => hI hp) (z i)).trans (hevZ i)
    refine ⟨f₀.comp eUL.toAlgHom, ?_⟩
    rw [he']
    simp [eU, hf₀, Algebra.TensorProduct.map_tmul]
