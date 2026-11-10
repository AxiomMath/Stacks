module

public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.NodeExample.FiniteEtale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Trace.Defs

/-!
# Traces in the nodal power map example

Let `k` be a field, `A = k[x,y]/(xy)`, `B = k[u,v]/(uv)` and `A → B` the branchwise power map
`x ↦ uⁿ`, `y ↦ vᵐ`.  This file computes the traces of `1`, `uⁱ` and `vʲ` from `L` to `K`, the
total quotient rings of `B` and `A`, branch by branch.

## Main results

* `Stacks.Discriminant.NodeExample.trace_one`,
  `Stacks.Discriminant.NodeExample.trace_u_pow` and
  `Stacks.Discriminant.NodeExample.trace_v_pow`: the three trace values.

## Implementation notes

The trace formula is stated with its denominator cleared, as
`Trace(1) · (x + y) = nx + my` in the total quotient ring, since `x + y` is a nonzerodivisor
but not a unit of `A`.

## References

* [Stacks Project, Tag 0BWP](https://stacks.math.columbia.edu/tag/0BWP)
* [Stacks Project, Tag 0BWM](https://stacks.math.columbia.edu/tag/0BWM)
* [Stacks Project, Tag 0BWN](https://stacks.math.columbia.edu/tag/0BWN)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Discriminant.NodeExample

universe u

variable (k : Type u) [Field k]

private noncomputable def projectiveTrace
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (f : M →ₗ[R] M) : R :=
  contractLeft R M ((dualTensorHomEquiv R M M).symm f)

private theorem dualTensorHom_map_split
    {R M F : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid F] [Module R F]
    (i : M →ₗ[R] F) (p : F →ₗ[R] M)
    (z : Module.Dual R M ⊗[R] M) :
    dualTensorHom R F F (TensorProduct.map p.dualMap i z) =
      i.comp ((dualTensorHom R M M z).comp p) := by
  induction z using TensorProduct.inductionOn with
  | tmul φ m =>
      ext x
      simp [TensorProduct.map_tmul, LinearMap.dualMap_apply, dualTensorHom_apply]
  | add x y hx hy => ext m; simp [hx, hy]

private theorem contractTensor_map_split
    {R M F : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommGroup F] [Module R F]
    (i : M →ₗ[R] F) (p : F →ₗ[R] M) (h : p.comp i = LinearMap.id)
    (z : Module.Dual R M ⊗[R] M) :
    contractLeft R F (TensorProduct.map p.dualMap i z) = contractLeft R M z := by
  induction z using TensorProduct.inductionOn with
  | tmul φ m =>
      simp only [TensorProduct.map_tmul, contractLeft_apply, LinearMap.dualMap_apply]
      change φ ((p.comp i) m) = φ m
      rw [h]
      rfl
  | add x y hx hy => simp [hx, hy]

private theorem projectiveTrace_eq_freeTrace
    {R M F : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
    (i : M →ₗ[R] F) (p : F →ₗ[R] M) (h : p.comp i = LinearMap.id)
    (f : M →ₗ[R] M) :
    projectiveTrace f = LinearMap.trace R F (i.comp (f.comp p)) := by
  let z := (dualTensorHomEquiv R M M).symm f
  have hz : (dualTensorHomEquiv R F F).symm (i.comp (f.comp p)) =
      TensorProduct.map p.dualMap i z := by
    apply (dualTensorHomEquiv R F F).injective
    rw [LinearEquiv.apply_symm_apply]
    change i.comp (f.comp p) =
      dualTensorHom R F F (TensorProduct.map p.dualMap i z)
    rw [dualTensorHom_map_split]
    rw [show dualTensorHom R M M z = f from
      (dualTensorHomEquiv R M M).apply_symm_apply f]
  change contractLeft R M z = _
  rw [LinearMap.trace_eq_contract' R F]
  change contractLeft R M z =
    contractLeft R F ((dualTensorHomEquiv R F F).symm (i.comp (f.comp p)))
  rw [hz]
  exact (contractTensor_map_split i p h z).symm

private theorem projectiveTrace_baseChange
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (f : M →ₗ[R] M) :
    algebraMap R A (projectiveTrace f) =
      projectiveTrace (f.baseChange A) := by
  classical
  obtain ⟨n, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let F := Fin n → R
  let FA := A ⊗[R] F
  let : Module.Free R F := inferInstance
  let : Module.Finite R F := inferInstance
  let bFA : Module.Basis (Fin n) A FA :=
    Algebra.TensorProduct.basis A (Pi.basisFun R (Fin n))
  let : Module.Free A FA := Module.Free.of_basis bFA
  let : Module.Finite A FA := Module.Finite.of_basis bFA
  let iA : A ⊗[R] M →ₗ[A] FA := i.baseChange A
  let pA : FA →ₗ[A] A ⊗[R] M := p.baseChange A
  have hpiA : pA.comp iA = LinearMap.id := by
    dsimp [iA, pA]
    rw [← LinearMap.baseChange_comp, hpi, LinearMap.baseChange_id]
  let : Module.Finite A (A ⊗[R] M) := Module.Finite.base_change R A M
  let : Module.Projective A (A ⊗[R] M) := Module.Projective.of_split iA pA hpiA
  let g := i.comp (f.comp p)
  let gA := iA.comp ((f.baseChange A).comp pA)
  have hgA : gA = g.baseChange A := by
    dsimp [gA, g]
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
  rw [projectiveTrace_eq_freeTrace i p hpi f,
    projectiveTrace_eq_freeTrace iA pA hpiA (f.baseChange A)]
  change algebraMap R A (LinearMap.trace R F g) = LinearMap.trace A FA gA
  rw [hgA, ← LinearMap.trace_baseChange]

private lemma projectiveTrace_conj
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) :
    projectiveTrace (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) = projectiveTrace f := by
  let z := (dualTensorHomEquiv R M M).symm f
  have hz : (dualTensorHomEquiv R N N).symm
      (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) =
      TensorProduct.map e.symm.toLinearMap.dualMap e.toLinearMap z := by
    apply (dualTensorHomEquiv R N N).injective
    rw [LinearEquiv.apply_symm_apply]
    change _ = dualTensorHom R N N _
    rw [dualTensorHom_map_split]
    simp [z]
  unfold projectiveTrace
  rw [hz]
  apply contractTensor_map_split
  ext m
  exact e.symm_apply_apply m

private lemma trace_power_eq_zero_of_basis
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (b : Module.Basis (Fin n) R S) (c : S) (a : R)
    (hb : ∀ j, b j = c ^ (j : ℕ)) (hc : c ^ n = algebraMap R S a)
    (i : ℕ) (hi : 0 < i) (hin : i < n) : Algebra.trace R S (c ^ i) = 0 := by
  classical
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Algebra.leftMulMatrix_apply]
  change (LinearMap.toMatrix b b (Algebra.lmul R S (c ^ i))) j j = 0
  rw [LinearMap.toMatrix_apply]
  change b.repr (c ^ i * b j) j = 0
  rw [hb, ← pow_add]
  by_cases hij : i + j.val < n
  · let l : Fin n := ⟨i + j.val, hij⟩
    have hl : l ≠ j := by intro h; have := congrArg Fin.val h; dsimp [l] at this; omega
    rw [show c ^ (i + j.val) = b l from (hb l).symm, b.repr_self]
    simp [hl]
  · let l : Fin n := ⟨i + j.val - n, by omega⟩
    have hl : l ≠ j := by intro h; have := congrArg Fin.val h; dsimp [l] at this; omega
    have he : c ^ (i + j.val) = a • b l := by
      rw [Algebra.smul_def, hb, ← hc, ← pow_add]
      congr 1
      dsimp [l]
      omega
    rw [he, map_smul, b.repr_self]
    simp [hl]

/-- If a coordinate becomes a unit, the other coordinate vanishes. -/
private lemma baseCoord_not_eq_zero_of_isUnit
    {S : Type*} [CommRing S] [Algebra (nodeRing k) S] (i : Bool)
    (hu : IsUnit (algebraMap (nodeRing k) S (baseCoord k i))) :
    algebraMap (nodeRing k) S (baseCoord k (!i)) = 0 := by
  apply hu.mul_left_cancel
  rw [mul_zero, ← map_mul, baseCoord_mul_not, map_zero]

/-- The `d i`-th power of a branch coordinate is the image of the base coordinate. -/
private lemma tmul_branchCoord_pow
    (d : Bool → ℕ) (f : nodeRing k →+* targetNodeRing k)
    (hf : ∀ i, f (baseCoord k i) = branchCoord k i ^ d i)
    (i : Bool) (S : Type*) [CommRing S] [Algebra (nodeRing k) S] :
    letI := f.toAlgebra
    ((1 : S) ⊗ₜ[nodeRing k] branchCoord k i) ^ d i =
      algebraMap S (S ⊗[nodeRing k] targetNodeRing k)
        (algebraMap (nodeRing k) S (baseCoord k i)) := by
  let := f.toAlgebra
  change (Algebra.TensorProduct.includeRight : targetNodeRing k →ₐ[nodeRing k]
    S ⊗[nodeRing k] targetNodeRing k) (branchCoord k i) ^ d i = _
  rw [← map_pow, ← hf]
  exact ((Algebra.TensorProduct.includeRight : targetNodeRing k →ₐ[nodeRing k]
    S ⊗[nodeRing k] targetNodeRing k).commutes _).trans
    (IsScalarTower.algebraMap_apply (nodeRing k) S _ _).symm

private lemma branch_tensor_equiv
    (d : Bool → ℕ) (hd : ∀ i, 0 < d i)
    (f : nodeRing k →+* targetNodeRing k)
    (hf : ∀ i, f (baseCoord k i) = branchCoord k i ^ d i)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a)
    (i : Bool) (S : Type*) [CommRing S] [Algebra (nodeRing k) S]
    (hu : IsUnit (algebraMap (nodeRing k) S (baseCoord k i))) :
    letI := f.toAlgebra
    ∃ e : AdjoinRoot (Polynomial.X ^ d i - Polynomial.C
        (algebraMap (nodeRing k) S (baseCoord k i))) ≃ₐ[S] S ⊗[nodeRing k] targetNodeRing k,
      e (AdjoinRoot.root _) = (1 : S) ⊗ₜ[nodeRing k] branchCoord k i := by
  let A := nodeRing k
  let B := targetNodeRing k
  let : Algebra A B := f.toAlgebra
  let C := S ⊗[A] B
  let : CommRing C := inferInstanceAs (CommRing (S ⊗[A] B))
  let : Algebra S C := inferInstanceAs (Algebra S (S ⊗[A] B))
  let p : Polynomial S := Polynomial.X ^ d i - Polynomial.C (algebraMap A S (baseCoord k i))
  let Q := AdjoinRoot p
  let r : Q := AdjoinRoot.root p
  have hr : r ^ d i = algebraMap S Q (algebraMap A S (baseCoord k i)) := by
    have h := AdjoinRoot.eval₂_root p
    change (Polynomial.X ^ d i - Polynomial.C (algebraMap A S (baseCoord k i))).eval₂
      (algebraMap S Q) r = 0 at h
    simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero] using h
  have hother : algebraMap A S (baseCoord k (!i)) = 0 := baseCoord_not_eq_zero_of_isUnit k i hu
  let g : B →+* Q := Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom ((algebraMap S Q).comp (algebraMap A S) |>.comp (algebraMap k A))
      (fun j => if j = i then r else 0)) (by
        intro p hp
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
        cases i <;> simp)
  have hg (j : Bool) : g (branchCoord k j) = if j = i then r else 0 := by
    cases j <;> change (Ideal.Quotient.lift _ _ _) (Ideal.Quotient.mk _ _) = _
    all_goals rw [Ideal.Quotient.lift_mk]; simp
  have hgk (a : k) : g (algebraMap k B a) =
      algebraMap S Q (algebraMap A S (algebraMap k A a)) := by
    change (Ideal.Quotient.lift _ _ _) (Ideal.Quotient.mk _ (MvPolynomial.C a)) = _
    rw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]
    rfl
  have hgf : g.comp f = (algebraMap S Q).comp (algebraMap A S) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change g (f (algebraMap k A a)) = _
      rw [hk, hgk]
      rfl
    · intro j
      fin_cases j
      · change g (f (baseCoord k false)) = algebraMap S Q (algebraMap A S (baseCoord k false))
        rw [hf, map_pow, hg]
        cases i
        · simpa using hr
        · simpa [Nat.ne_of_gt (hd false), hother] using congrArg (algebraMap S Q) hother.symm
      · change g (f (baseCoord k true)) = algebraMap S Q (algebraMap A S (baseCoord k true))
        rw [hf, map_pow, hg]
        cases i
        · simpa [Nat.ne_of_gt (hd true), hother] using congrArg (algebraMap S Q) hother.symm
        · simpa using hr
  let gA : B →ₐ[A] Q :=
    { __ := g
      commutes' := fun a => (RingHom.congr_fun hgf a).trans
        (IsScalarTower.algebraMap_apply A S Q a).symm }
  let φ : C →ₐ[S] Q := AlgHom.liftEquiv A S B Q gA
  have hφ (s : S) (b : B) : φ (s ⊗ₜ[A] b) = s • g b := rfl
  let t : C := (1 : S) ⊗ₜ[A] branchCoord k i
  let iSC : S →+* C := algebraMap S C
  have ht : t ^ d i = iSC (algebraMap A S (baseCoord k i)) := tmul_branchCoord_pow k d f hf i S
  have hunit : IsUnit t := (isUnit_pow_iff (Nat.ne_of_gt (hd i))).mp
    (ht.symm ▸ hu.map iSC)
  have htother : (1 : S) ⊗ₜ[A] branchCoord k (!i) = (0 : C) := by
    apply hunit.mul_left_cancel
    rw [mul_zero t]
    change (Algebra.TensorProduct.includeRight : B →ₐ[A] C) (branchCoord k i) *
      (Algebra.TensorProduct.includeRight : B →ₐ[A] C) (branchCoord k (!i)) = 0
    rw [← map_mul, branchCoord_mul_not, map_zero]
  let ψ : Q →ₐ[S] C := AdjoinRoot.liftAlgHom p (Algebra.ofId S C) t (by
    change (Polynomial.X ^ d i - Polynomial.C (algebraMap A S (baseCoord k i))).eval₂
      (algebraMap S C) t = 0
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    exact sub_eq_zero.mpr ht)
  have hψ : ψ r = t := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hφψ : φ.comp ψ = AlgHom.id S Q := by
    apply AdjoinRoot.algHom_ext
    change φ (ψ r) = r
    rw [hψ, hφ, hg, ite_eq_left rfl, one_smul]
  have hψφ : ψ.comp φ = AlgHom.id S C := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.toRingHom_injective
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change ψ (φ ((1 : S) ⊗ₜ[A] algebraMap k B a)) = (1 : S) ⊗ₜ[A] algebraMap k B a
      rw [hφ, one_smul, hgk, ψ.commutes]
      rw [← hk]
      exact ((Algebra.TensorProduct.includeRight : B →ₐ[A] C).commutes
        (algebraMap k A a)).symm
    · intro j
      have hj : Ideal.Quotient.mk _ (MvPolynomial.X j) = branchCoord k j := by cases j <;> rfl
      change ψ (φ ((1 : S) ⊗ₜ[A] Ideal.Quotient.mk _ (MvPolynomial.X j))) =
        (1 : S) ⊗ₜ[A] Ideal.Quotient.mk _ (MvPolynomial.X j)
      rw [hj, hφ, one_smul, hg]
      by_cases hji : j = i
      · subst j
        rw [ite_eq_left rfl, hψ]
      · rw [ite_eq_right hji, map_zero]
        have hjn : j = !i := by cases j <;> cases i <;> simp_all
        rw [hjn, htother]
  let e : Q ≃ₐ[S] C :=
    { __ := ψ
      invFun := φ
      left_inv := fun a => AlgHom.congr_fun hφψ a
      right_inv := fun a => AlgHom.congr_fun hψφ a }
  exact ⟨e, hψ⟩

private lemma projectiveTrace_lmul_baseChange
    {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Module.Finite R B] [Module.Projective R B]
    [Module.Free S (S ⊗[R] B)] (b : B) :
    algebraMap R S (projectiveTrace (Algebra.lmul R B b)) =
      Algebra.trace S (S ⊗[R] B) ((1 : S) ⊗ₜ[R] b) := by
  have h : (Algebra.lmul R B b).baseChange S =
      Algebra.lmul S (S ⊗[R] B) ((1 : S) ⊗ₜ[R] b) := by
    ext s
    simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rw [projectiveTrace_baseChange, h, Algebra.trace_apply,
    LinearMap.trace_eq_contract']
  rfl

private lemma branch_trace_values
    (d : Bool → ℕ) (hd : ∀ i, 0 < d i)
    (f : nodeRing k →+* targetNodeRing k)
    (hf : ∀ i, f (baseCoord k i) = branchCoord k i ^ d i)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a)
    (i : Bool) (S : Type*) [CommRing S] [Algebra (nodeRing k) S]
    (hu : IsUnit (algebraMap (nodeRing k) S (baseCoord k i))) :
    letI := f.toAlgebra
    let C := S ⊗[nodeRing k] targetNodeRing k
    Module.Free S C ∧ Algebra.trace S C 1 = (d i : S) ∧
      ∀ j r, 0 < r → r < d j →
        Algebra.trace S C ((1 : S) ⊗ₜ[nodeRing k] (branchCoord k j ^ r)) = 0 := by
  let A := nodeRing k
  let B := targetNodeRing k
  let : Algebra A B := f.toAlgebra
  let C := S ⊗[A] B
  let : CommRing C := inferInstanceAs (CommRing (S ⊗[A] B))
  let : Algebra S C := inferInstanceAs (Algebra S (S ⊗[A] B))
  classical
  have hsub (h : Subsingleton S) : Module.Free S C ∧ Algebra.trace S C 1 = (d i : S) ∧
      ∀ j r, 0 < r → r < d j →
        Algebra.trace S C ((1 : S) ⊗ₜ[A] (branchCoord k j ^ r)) = 0 := by
    let := h
    have : Subsingleton C := Module.subsingleton S C
    exact ⟨inferInstance, Subsingleton.elim _ _, fun _ _ _ _ => Subsingleton.elim _ _⟩
  cases subsingleton_or_nontrivial S with
  | inl h => exact hsub h
  | inr h =>
    let := h
    obtain ⟨e, he⟩ := branch_tensor_equiv k d hd f hf hk i S hu
    let p : Polynomial S := Polynomial.X ^ d i - Polynomial.C (algebraMap A S (baseCoord k i))
    have hp : p.Monic := Polynomial.monic_X_pow_sub_C _ (Nat.ne_of_gt (hd i))
    have hdeg : p.natDegree = d i := Polynomial.natDegree_X_pow_sub_C
    let pb := AdjoinRoot.powerBasis' hp
    let b : Module.Basis (Fin (d i)) S C :=
      (pb.basis.map e.toLinearEquiv).reindex (finCongr hdeg)
    have hb (j : Fin (d i)) : b j = ((1 : S) ⊗ₜ[A] branchCoord k i) ^ j.val := by
      simp only [b, Module.Basis.reindex_apply, Module.Basis.map_apply, pb.basis_eq_pow]
      change e (AdjoinRoot.root p ^ ((finCongr hdeg).symm j).val) = _
      rw [map_pow, he]
      rfl
    have : Module.Free S C := Module.Free.of_basis b
    refine ⟨inferInstance, ?_, ?_⟩
    · simpa only [map_one, Fintype.card_fin, nsmul_eq_mul, mul_one] using
        Algebra.trace_algebraMap_of_basis (R := S) (S := C) b (1 : S)
    · intro j r hr hrd
      by_cases hji : j = i
      · subst j
        have h := trace_power_eq_zero_of_basis (d i) b _ _ hb (tmul_branchCoord_pow k d f hf i S)
          r hr hrd
        change Algebra.trace S C
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] C) (branchCoord k i ^ r)) = 0
        rw [map_pow]
        exact h
      · have hj : j = !i := by cases i <;> cases j <;> simp_all
        have hmul : algebraMap S C (algebraMap A S (baseCoord k i)) *
            ((1 : S) ⊗ₜ[A] (branchCoord k j ^ r)) = 0 := by
          have hrel : branchCoord k i ^ d i * branchCoord k j ^ r = 0 := by
            rw [hj]
            cases i
            · exact targetNode_power_relation k (d false) r (hd false) hr
            · change v k ^ d true * u k ^ r = 0
              rw [mul_comm]
              exact targetNode_power_relation k r (d true) hr (hd true)
          have hmap := congrArg (Algebra.TensorProduct.includeRight : B →ₐ[A] C) hrel
          rw [map_mul, map_zero, ← hf] at hmap
          change (Algebra.TensorProduct.includeRight : B →ₐ[A] C)
              (algebraMap A B (baseCoord k i)) * _ = 0 at hmap
          rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A S C] at hmap
          exact hmap
        have hz := (hu.map (algebraMap S C)).mul_left_cancel (hmul.trans (mul_zero _).symm)
        rw [hz, map_zero]

private lemma dedekind_trace_baseChange
    {A B S : Type*} [CommRing A] [CommRing B] [CommRing S] [Algebra A B]
    (setup : DedekindDifferentSetup A B)
    [Algebra (FractionRing A) S] [Algebra A S] [IsScalarTower A (FractionRing A) S]
    [Module.Free S (S ⊗[A] B)] (b : B) :
    algebraMap (FractionRing A) S (setup.trace (b ⊗ₜ[A] (1 : FractionRing A))) =
      Algebra.trace S (S ⊗[A] B) ((1 : S) ⊗ₜ[A] b) := by
  let K := FractionRing A
  let M := K ⊗[A] B
  let L := B ⊗[A] K
  let := setup.finite
  let : Algebra K L := Algebra.TensorProduct.rightAlgebra
  let := setup.etaleGenericFiber
  let e : M ≃ₐ[K] L := Algebra.TensorProduct.commRight A K B
  have : Module.Finite K M := Module.Finite.base_change A K B
  have : Module.Finite K L := Module.Finite.equiv e.toLinearEquiv
  have : Module.Flat K L := Algebra.Smooth.flat K L
  have : Module.FinitePresentation K L :=
    Module.FinitePresentation.of_finite_of_finitePresentation K L
  have : Module.Projective K L := Module.Flat.projective_of_finitePresentation
  have : Module.Projective K M := Module.Projective.of_equiv e.symm.toLinearEquiv
  let eS : (S ⊗[K] M) ≃ₐ[S] S ⊗[A] B := Algebra.TensorProduct.cancelBaseChange A K S S B
  have : Module.Free S (S ⊗[K] M) := Module.Free.of_equiv eS.symm.toLinearEquiv
  have hμ : e.toLinearMap.comp
      ((Algebra.lmul K M ((1 : K) ⊗ₜ[A] b)).comp e.symm.toLinearMap) =
      Algebra.lmul K L (b ⊗ₜ[A] (1 : K)) := by
    apply LinearMap.ext
    intro z
    change e (((1 : K) ⊗ₜ[A] b) * e.symm z) = (b ⊗ₜ[A] (1 : K)) * z
    rw [map_mul, e.apply_symm_apply]
    rfl
  have ht : projectiveTrace (Algebra.lmul K M ((1 : K) ⊗ₜ[A] b)) =
      setup.trace (b ⊗ₜ[A] (1 : K)) := by
    rw [← projectiveTrace_conj e.toLinearEquiv]
    change projectiveTrace (e.toLinearMap.comp
      ((Algebra.lmul K M ((1 : K) ⊗ₜ[A] b)).comp e.symm.toLinearMap)) = _
    rw [hμ]
    rfl
  rw [← ht, projectiveTrace_lmul_baseChange]
  rw [← Algebra.trace_eq_of_algEquiv eS]
  congr 1
  exact (Algebra.TensorProduct.cancelBaseChange_tmul A K S S B (1 : S) (1 : K) b).trans
    (by rw [one_smul])

private lemma eq_zero_of_localization_pair
    {R : Type*} [CommRing R] (a b z : R) (h : IsUnit (a + b))
    (ha : algebraMap R (Localization.Away a) z = 0)
    (hb : algebraMap R (Localization.Away b) z = 0) : z = 0 := by
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq a (ha.trans (map_zero _).symm)
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq b (hb.trans (map_zero _).symm)
  simp only [mul_zero] at hm hn
  have hc : IsCoprime a b := by
    obtain ⟨u, hu⟩ := h
    refine ⟨↑u⁻¹, ↑u⁻¹, ?_⟩
    rw [← mul_add, ← hu]
    simp
  obtain ⟨r, s, hrs⟩ := hc.pow (m := m) (n := n)
  calc
    z = (r * a ^ m + s * b ^ n) * z := by rw [hrs, one_mul]
    _ = 0 := by rw [add_mul, mul_assoc, mul_assoc, hm, hn, mul_zero, mul_zero, add_zero]

/-- Localizing the fraction field at a branch coordinate makes that coordinate a unit. -/
private lemma isUnit_algebraMap_away (i : Bool) :
    IsUnit (algebraMap (nodeRing k)
      (Localization.Away (algebraMap (nodeRing k) (FractionRing (nodeRing k)) (baseCoord k i)))
      (baseCoord k i)) := by
  rw [IsScalarTower.algebraMap_apply (nodeRing k) (FractionRing (nodeRing k))
    (Localization.Away (algebraMap (nodeRing k) (FractionRing (nodeRing k)) (baseCoord k i)))]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The sum of the two coordinates is a unit in the fraction field of the node. -/
private lemma isUnit_algebraMap_x_add_y :
    IsUnit (algebraMap (nodeRing k) (FractionRing (nodeRing k)) (x k) +
      algebraMap (nodeRing k) (FractionRing (nodeRing k)) (y k)) := by
  have hreg : x k + y k ∈ nonZeroDivisors (nodeRing k) := by
    simpa only [pow_one, map_add, x, y] using
      nodal_pow_sum_regular (k := k) (0 : Fin 2) 1 (by decide) 1 1 (by decide) (by decide)
  rw [← map_add]
  exact IsLocalization.map_units (FractionRing (nodeRing k)) ⟨x k + y k, hreg⟩

private lemma generic_trace_on_branch
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI := f.toAlgebra
    ∀ (setup : DedekindDifferentSetup (nodeRing k) (targetNodeRing k)) (i : Bool),
      let K := FractionRing (nodeRing k)
      let S := Localization.Away (algebraMap (nodeRing k) K (baseCoord k i))
      algebraMap K S (setup.trace 1) = ((if i then m else n : ℕ) : S) ∧
      ∀ (j : Bool) r, 0 < r → r < (if j then m else n) → algebraMap K S
        (setup.trace ((branchCoord k j ^ r) ⊗ₜ[nodeRing k] (1 : K))) = 0 := by
  let A := nodeRing k
  let B := targetNodeRing k
  let K := FractionRing A
  let : Algebra A B := f.toAlgebra
  intro setup i
  let S := Localization.Away (algebraMap A K (baseCoord k i))
  let d : Bool → ℕ := fun j => if j then m else n
  have hd : ∀ j, 0 < d j := by
    intro j
    cases j
    · change 0 < n
      exact Nat.pos_of_ne_zero fun h => hn.ne_zero (by simp [h])
    · change 0 < m
      exact Nat.pos_of_ne_zero fun h => hm.ne_zero (by simp [h])
  have hf : ∀ j, f (baseCoord k j) = branchCoord k j ^ d j := by
    intro j
    cases j <;> assumption
  obtain ⟨hfree, h1, hp⟩ :=
    branch_trace_values k d hd f hf hk i S (isUnit_algebraMap_away k i)
  let := hfree
  constructor
  · have h := dedekind_trace_baseChange (S := S) setup (1 : B)
    simpa only [← Algebra.TensorProduct.one_def] using h.trans h1
  · intro j r hr hrd
    exact (dedekind_trace_baseChange (S := S) setup (branchCoord k j ^ r)).trans (hp j r hr hrd)

/-- The trace vanishes on proper powers of a branch coordinate. -/
private lemma trace_branch_pow_eq_zero
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    ∀ (setup : DedekindDifferentSetup (nodeRing k) (targetNodeRing k)) (j : Bool) (r : ℕ),
      1 ≤ r → r < (if j then m else n) →
        setup.trace (TensorProduct.tmul (nodeRing k) (branchCoord k j ^ r) 1) = 0 := by
  intro setup j r hr hrd
  have hbranch := generic_trace_on_branch k n m hn hm f hx hy hk setup
  apply eq_zero_of_localization_pair (algebraMap (nodeRing k) (FractionRing (nodeRing k)) (x k))
    (algebraMap (nodeRing k) (FractionRing (nodeRing k)) (y k)) _ (isUnit_algebraMap_x_add_y k)
  · exact (hbranch false).2 j r hr hrd
  · exact (hbranch true).2 j r hr hrd

/-- The trace of one on the generic fibre is `(nx+my)/(x+y)`. -/
@[stacks 0BWP "trace of one"]
theorem trace_one
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    ∀ setup : DedekindDifferentSetup (nodeRing k) (targetNodeRing k),
      setup.trace 1 *
        algebraMap (nodeRing k) (FractionRing (nodeRing k)) (x k + y k) =
        algebraMap (nodeRing k) (FractionRing (nodeRing k))
          ((algebraMap k (nodeRing k) (n : k)) * x k +
            (algebraMap k (nodeRing k) (m : k)) * y k)  := by
  let A := nodeRing k
  let B := targetNodeRing k
  let K := FractionRing A
  let : Algebra A B := f.toAlgebra
  intro setup
  have hbranch := generic_trace_on_branch k n m hn hm f hx hy hk setup
  apply sub_eq_zero.mp
  apply eq_zero_of_localization_pair (algebraMap A K (x k)) (algebraMap A K (y k)) _
    (isUnit_algebraMap_x_add_y k)
  · let S := Localization.Away (algebraMap A K (x k))
    have hy0 : algebraMap A S (y k) = 0 :=
      baseCoord_not_eq_zero_of_isUnit k false (isUnit_algebraMap_away k false)
    have htr : algebraMap K S (setup.trace 1) = (n : S) := (hbranch false).1
    simp only [map_sub, map_add, map_mul, map_natCast]
    rw [IsScalarTower.algebraMap_apply A K S] at hy0
    rw [htr, hy0]
    ring
  · let S := Localization.Away (algebraMap A K (y k))
    have hx0 : algebraMap A S (x k) = 0 :=
      baseCoord_not_eq_zero_of_isUnit k true (isUnit_algebraMap_away k true)
    have htr : algebraMap K S (setup.trace 1) = (m : S) := (hbranch true).1
    simp only [map_sub, map_add, map_mul, map_natCast]
    rw [IsScalarTower.algebraMap_apply A K S] at hx0
    rw [htr, hx0]
    ring


/-- The trace vanishes on proper powers of the first branch coordinate. -/
@[stacks 0BWP "trace of u powers"]
theorem trace_u_pow
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    ∀ (setup : DedekindDifferentSetup (nodeRing k) (targetNodeRing k))
      (i : ℕ), 1 ≤ i → i < n →
        setup.trace (TensorProduct.tmul (nodeRing k) (u k ^ i) 1) = 0  := by
  intro setup i hi hin
  exact trace_branch_pow_eq_zero k n m hn hm f hx hy hk setup false i hi hin


/-- The trace vanishes on proper powers of the second branch coordinate. -/
@[stacks 0BWP "trace of v powers"]
theorem trace_v_pow
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    ∀ (setup : DedekindDifferentSetup (nodeRing k) (targetNodeRing k))
      (j : ℕ), 1 ≤ j → j < m →
        setup.trace (TensorProduct.tmul (nodeRing k) (v k ^ j) 1) = 0  := by
  intro setup j hj hjm
  exact trace_branch_pow_eq_zero k n m hn hm f hx hy hk setup true j hj hjm

end Stacks.Discriminant.NodeExample

end
