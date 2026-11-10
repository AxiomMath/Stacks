module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Splitting monic polynomials off a root

A monic polynomial with a root in the base ring factors with that root split off, and after a
finite free extension of the base ring one can always split off a root. Consequently a finite
ring map becomes, after a finite free extension, a quotient of a ring in which each variable
satisfies a polynomial that splits into linear factors.

## References

* [Stacks Project, Tag 052Y](https://stacks.math.columbia.edu/tag/052Y)
-/

@[expose] public section

universe u v

section

/-- If `a` is a root of a monic polynomial `P`, then `P = (X - C a) * Q` for some monic
polynomial `Q`. -/
@[stacks 052Z]
theorem exists_monic_eq_X_sub_C_mul_of_isRoot {R : Type*} [CommRing R]
    {P : Polynomial R} (hP : P.Monic) {a : R} (ha : P.IsRoot a) :
    ∃ Q : Polynomial R, Q.Monic ∧ P = (Polynomial.X - Polynomial.C a) * Q := by
  nontriviality R
  let L : Polynomial R := Polynomial.X - Polynomial.C a
  have hL : L.Monic := by
    simpa [L] using Polynomial.monic_X_sub_C a
  have hfactor : L * (P /ₘ L) = P := by
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot).2 ha
  have hQ0 : P /ₘ L ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfactor
    exact hP.ne_zero hfactor.symm
  have hdegree : L.degree ≤ P.degree := by
    rw [← hfactor, hL.degree_mul_comm, hL.degree_mul,
      Polynomial.degree_eq_natDegree hQ0, add_comm]
    exact le_add_of_nonneg_right (WithBot.coe_nonneg.mpr (Nat.zero_le _))
  have hleading := Polynomial.leadingCoeff_divByMonic_of_monic hL hdegree
  have hQ : (P /ₘ L).Monic := by
    change (P /ₘ L).leadingCoeff = 1
    rw [hleading, hP.leadingCoeff]
  exact ⟨P /ₘ L, hQ, by simpa [L] using hfactor.symm⟩

end

section

/-- For a monic polynomial `P` over `R` there is a finite free `R`-algebra `R'` over which the
image of `P` factors as `(X - C α) * Q`, with `Q` monic. -/
@[stacks 0530]
theorem exists_finite_free_algebra_factor {R : Type u} [CommRing R]
    {P : Polynomial R} (hP : P.Monic) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Module.Free R R'),
      ∃ (α : R') (Q : Polynomial R'),
        Q.Monic ∧ P.map (algebraMap R R') = (Polynomial.X - Polynomial.C α) * Q := by
  let _ : Module.Finite R (AdjoinRoot P) := hP.finite_adjoinRoot
  let _ : Module.Free R (AdjoinRoot P) := hP.free_adjoinRoot
  let p : Polynomial (AdjoinRoot P) := P.map (algebraMap R (AdjoinRoot P))
  let α : AdjoinRoot P := AdjoinRoot.root P
  let q : Polynomial (AdjoinRoot P) := p /ₘ (Polynomial.X - Polynomial.C α)
  have hp : p.Monic := hP.map _
  have hroot : p.IsRoot α := AdjoinRoot.isRoot_root P
  have hfactor : (Polynomial.X - Polynomial.C α) * q = p :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance, α, q, ?_, ?_⟩
  · exact (Polynomial.monic_X_sub_C α).of_mul_monic_left (hfactor.symm ▸ hp)
  · exact hfactor.symm

end

section

open scoped TensorProduct

private theorem exists_splits_map_fin {R : Type u} [CommRing R] [Nontrivial R]
    {n : ℕ} (P : Fin n → Polynomial R) (hP : ∀ i, (P i).Monic) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Module.Free R S) (_ : Nontrivial S),
      ∀ i, ((P i).map (algebraMap R S)).Splits := by
  induction n generalizing R with
  | zero => exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, fun i ↦ i.elim0⟩
  | succ n ih =>
      obtain ⟨A, _, _, _, _, _, hA⟩ := (hP 0).exists_splits_map
      let Q : Fin n → Polynomial A := fun i ↦ (P i.succ).map (algebraMap R A)
      have hQ (i : Fin n) : (Q i).Monic := (hP i.succ).map (algebraMap R A)
      obtain ⟨B, _, _, _, _, _, hB⟩ := ih Q hQ
      let : Algebra R B := (algebraMap A B).comp (algebraMap R A) |>.toAlgebra
      have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
      refine ⟨B, inferInstance, inferInstance, Module.Finite.trans A B,
        Module.Free.trans (R := R) (S := A) (M := B), inferInstance, ?_⟩
      have hmap (p : Polynomial R) : (p.map (algebraMap R A)).map (algebraMap A B) =
          p.map (algebraMap R B) := by
        rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rw [← hmap]
        exact hA.map _
      · rw [← hmap]
        exact hB j

/-- A finite algebra becomes a quotient by split univariate polynomials after an injective
finite free extension of its base ring. -/
@[stacks 0531]
theorem exists_finite_free_extension_quotient_split_polynomials
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    [Algebra R S] [Module.Finite R S] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Module.Free R R'),
      Function.Injective (algebraMap R R') ∧
        letI : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
        ∃ (n : ℕ) (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R')
          (f : (MvPolynomial (Fin n) R' ⧸
            Ideal.span (Set.range fun i : Fin n ↦
              ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j))))
              →ₐ[R'] S ⊗[R] R'),
          Function.Surjective f := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      let : Subsingleton R := hR
      let : Subsingleton S := Algebra.subsingleton R S
      refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
      · exact fun _ _ _ ↦ Subsingleton.elim _ _
      · let : Algebra R (S ⊗[R] R) := Algebra.TensorProduct.rightAlgebra
        let : Subsingleton (S ⊗[R] R) := Algebra.subsingleton R (S ⊗[R] R)
        refine ⟨0, (fun i ↦ i.elim0), (fun i ↦ i.elim0), ?_, ?_⟩
        · exact Ideal.Quotient.liftₐ _ (MvPolynomial.aeval Fin.elim0) (by simp)
        · exact fun y ↦ ⟨0, Subsingleton.elim _ y⟩
  | inr hR =>
      let : Nontrivial R := hR
      obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := R) (M := S)
      have hxint (i : Fin n) : IsIntegral R (x i) :=
        Algebra.IsIntegral.isIntegral (x i)
      choose P hP hPx using fun i ↦ hxint i
      obtain ⟨R', _, _, _, _, _, hPi⟩ := exists_splits_map_fin P hP
      refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
      · exact FaithfulSMul.algebraMap_injective R R'
      · let : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
        choose roots hroots using fun i ↦ Polynomial.splits_iff_exists_multiset.mp (hPi i)
        have hroots' (i : Fin n) :
            (P i).map (algebraMap R R') =
              ((roots i).map fun a ↦ Polynomial.X - Polynomial.C a).prod := by
          simpa only [Polynomial.Monic.leadingCoeff ((hP i).map (algebraMap R R')),
            Polynomial.C_1, one_mul] using hroots i
        let y : Fin n → S ⊗[R] R' := fun i ↦ x i ⊗ₜ[R] (1 : R')
        let g : MvPolynomial (Fin n) R' →ₐ[R'] S ⊗[R] R' := MvPolynomial.aeval y
        have hrel (i : Fin n) :
            g (∏ j : Fin (roots i).toList.length,
              (MvPolynomial.X i - MvPolynomial.C (roots i).toList[j])) = 0 := by
          have hfactor :
              (∏ j : Fin (roots i).toList.length,
                (MvPolynomial.X i - MvPolynomial.C (roots i).toList[j])) =
                ((P i).map (algebraMap R R')).toMvPolynomial i := by
            rw [hroots' i]
            simp only [map_multiset_prod, Multiset.map_map, Function.comp_apply, map_sub,
              Polynomial.toMvPolynomial_X, Polynomial.toMvPolynomial_C]
            rw [← Multiset.prod_toList]
            simpa using (Fin.prod_univ_fun_getElem (roots i).toList fun a ↦
              MvPolynomial.X i - MvPolynomial.C a)
          rw [hfactor, MvPolynomial.aeval_toMvPolynomial]
          have hi := congrArg (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] R') (hPx i)
          simpa [y, Polynomial.aeval_def, Polynomial.eval₂_map,
            ← IsScalarTower.algebraMap_eq R R' (S ⊗[R] R')] using hi
        have hspan : ∀ q, q ∈ Ideal.span (Set.range fun i : Fin n ↦
              ∏ j : Fin (roots i).toList.length,
                (MvPolynomial.X i - MvPolynomial.C (roots i).toList[j])) → g q = 0 := by
          intro q hq
          rw [← RingHom.mem_ker]
          exact (Ideal.span_le.mpr fun q hq ↦ by obtain ⟨i, rfl⟩ := hq; exact hrel i) hq
        let f := Ideal.Quotient.liftₐ _ g hspan
        refine ⟨n, (fun i ↦ (roots i).toList.length),
          (fun i j ↦ (roots i).toList[j]), f, ?_⟩
        have hC (r : R') (b : S) :
            algebraMap R' (S ⊗[R] R') r * (b ⊗ₜ[R] (1 : R')) = b ⊗ₜ[R] r := by
          rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
          exact (Algebra.TensorProduct.tmul_mul_tmul 1 b r 1).trans (by simp)
        have hg : Function.Surjective g := by
          intro z
          induction z using TensorProduct.inductionOn with
          | add z w hz hw =>
              obtain ⟨z, rfl⟩ := hz
              obtain ⟨w, rfl⟩ := hw
              exact ⟨z + w, map_add g z w⟩
          | tmul s r =>
              have hs : s ∈ Submodule.span R (Set.range x) := by rw [hx]; trivial
              have hs' : ∃ q, g q = s ⊗ₜ[R] (1 : R') := by
                refine Submodule.span_induction
                  (p := fun s _ ↦ ∃ q, g q = s ⊗ₜ[R] (1 : R')) ?_ ?_ ?_ ?_ hs
                · rintro _ ⟨i, rfl⟩
                  exact ⟨MvPolynomial.X i, by simp [g, y]⟩
                · exact ⟨0, by simp⟩
                · rintro a b _ _ ⟨q, hq⟩ ⟨p, hp⟩
                  exact ⟨q + p, by simp [hq, hp, TensorProduct.add_tmul]⟩
                · rintro a b _ ⟨q, hq⟩
                  refine ⟨MvPolynomial.C (algebraMap R R' a) * q, ?_⟩
                  rw [map_mul, MvPolynomial.aeval_C, hq, hC, ← mul_one (algebraMap R R' a),
                    ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
              obtain ⟨q, hq⟩ := hs'
              refine ⟨MvPolynomial.C r * q, ?_⟩
              rw [map_mul, MvPolynomial.aeval_C, hq, hC]
        intro z
        obtain ⟨q, rfl⟩ := hg z
        exact ⟨Ideal.Quotient.mk _ q, rfl⟩

end
