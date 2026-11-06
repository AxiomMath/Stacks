module

import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The Galois resolvent of a polynomial

Let `f ∈ A[X]` have roots `b₁, …, bₘ` (after some ring map `A → B`) and let `c ∈ Aᵐ`. For a
permutation `π` of the roots put `t(π) = ∑ᵢ cᵢ b_{π i}`. The **Galois resolvent**
`Φ(T) = ∏_π (T - t(π))`, its **discriminant** `Δ = ∏_{π ≠ π'} (t(π) - t(π'))` and the
**Lagrange-type polynomials** `R_τ` with `R_τ(t(π)) = Δ · t(π τ)` have coefficients which are
polynomials in the coefficients of `f` and in `c`: they are symmetric in the roots, so the
fundamental theorem of symmetric polynomials writes them in the elementary symmetric functions of
the roots, which are the signed coefficients of `f`.

They are built here as universal polynomials over `ℤ[γ₁, …, γₘ][u₁, …, uₘ]` and specialized.

## Main definitions

* `Polynomial.galoisResolvent`, `Polynomial.resolventDisc`, `Polynomial.resolventPerm`.
* `Polynomial.twistedComp`: the composite `Δ^{deg Ψ} Ψ^{fr}(R / Δ)`, without denominators.

## Main results

* `Polynomial.galoisResolvent_spec`: the three defining properties after a map splitting `f`.
* `Polynomial.galoisResolvent_monic`.
* `Polynomial.exists_natDegree_resolvent_le`: uniform degree bounds over `R[X]` for linear forms
  with constant coefficients.
* `Polynomial.exists_resolventDisc_ne_zero`: for separable monic `f` over a domain the
  discriminant does not vanish at some `c` with coordinates in any large enough finite set.
-/

@[expose] public section

open Polynomial Finset Nat

noncomputable section

namespace Polynomial

namespace GaloisResolvent

variable (m : ℕ)

/-- The ring `ℤ[γ₁, …, γₘ]` of the universal coefficients of the linear form. -/
abbrev CoeffRing := MvPolynomial (Fin m) ℤ

/-- The ring `ℤ[γ][u₁, …, uₘ]` of the universal roots. -/
abbrev RootRing := MvPolynomial (Fin m) (CoeffRing m)

/-- The universal value of the linear form `∑ γᵢ u_{π i}`. -/
def t (π : Equiv.Perm (Fin m)) : RootRing m :=
  ∑ i, MvPolynomial.C (MvPolynomial.X i) * MvPolynomial.X (π i)

/-- Permuting the universal roots by `e` sends `t(π)` to `t(e π)`. -/
theorem rename_t (e π : Equiv.Perm (Fin m)) :
    MvPolynomial.rename e (t m π) = t m (e * π) := by
  simp [t, map_sum, Equiv.Perm.mul_apply]

/-- The universal resolvent `∏_π (T - t(π))`. -/
def Φ : (RootRing m)[X] := ∏ π : Equiv.Perm (Fin m), (X - C (t m π))

/-- The universal discriminant `∏_{π ≠ π'} (t(π) - t(π'))`. -/
def Δ : RootRing m := ∏ π : Equiv.Perm (Fin m), ∏ π' ∈ univ.erase π, (t m π - t m π')

/-- The universal Lagrange-type polynomial with `R_τ(t(π)) = Δ · t(π τ)`. -/
def R (τ : Equiv.Perm (Fin m)) : (RootRing m)[X] :=
  ∑ π : Equiv.Perm (Fin m), C (t m (π * τ) * ∏ ρ ∈ univ.erase π, ∏ ρ' ∈ univ.erase ρ,
    (t m ρ - t m ρ')) * ∏ π' ∈ univ.erase π, (X - C (t m π'))

/-- Reindexing by left multiplication by `e`: the product of `F` over the permutations other than
`e π` equals the product of `F (e ρ)` over the permutations `ρ` other than `π`. -/
theorem prod_erase_mul_left {M : Type*} [CommMonoid M] (e π : Equiv.Perm (Fin m))
    (F : Equiv.Perm (Fin m) → M) :
    ∏ ρ ∈ univ.erase (e * π), F ρ = ∏ ρ ∈ univ.erase π, F (e * ρ) := by
  refine Finset.prod_nbij' (e⁻¹ * ·) (e * ·) ?_ ?_ ?_ ?_ ?_ <;> intro x hx
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at hx ⊢
    exact fun h => hx (by rw [← h]; group)
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at hx ⊢
    exact fun h => hx (mul_left_cancel h)
  · simp
  · simp
  · simp

/-- The universal discriminant with the factor of index `π` removed. -/
def discOff (π : Equiv.Perm (Fin m)) : RootRing m :=
  ∏ ρ ∈ univ.erase π, ∏ ρ' ∈ univ.erase ρ, (t m ρ - t m ρ')

/-- The Lagrange basis numerator `∏_{π' ≠ π} (T - t(π'))`. -/
def lagNum (π : Equiv.Perm (Fin m)) : (RootRing m)[X] :=
  ∏ π' ∈ univ.erase π, (X - C (t m π'))

/-- Permuting the universal roots by `e` sends `discOff m π` to `discOff m (e * π)`. -/
theorem rename_discOff (e π : Equiv.Perm (Fin m)) :
    MvPolynomial.rename e (discOff m π) = discOff m (e * π) := by
  simp only [discOff, map_prod, map_sub, rename_t]
  rw [prod_erase_mul_left]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [prod_erase_mul_left]

/-- Permuting the universal roots by `e` sends `lagNum m π` to `lagNum m (e * π)`. -/
theorem map_rename_lagNum (e π : Equiv.Perm (Fin m)) :
    (lagNum m π).map (MvPolynomial.rename e).toRingHom = lagNum m (e * π) := by
  simp only [lagNum, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_t]
  rw [prod_erase_mul_left]

/-- The universal resolvent `Φ m` is invariant under permutations of the universal roots. -/
theorem map_rename_Φ (e : Equiv.Perm (Fin m)) :
    (Φ m).map (MvPolynomial.rename e).toRingHom = Φ m := by
  simp only [Φ, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, rename_t]
  exact Fintype.prod_equiv (Equiv.mulLeft e) _ _ (fun _ => rfl)

/-- The universal discriminant `Δ m` is invariant under permutations of the universal roots. -/
theorem rename_Δ (e : Equiv.Perm (Fin m)) : MvPolynomial.rename e (Δ m) = Δ m := by
  simp only [Δ, map_prod, map_sub, rename_t]
  exact Fintype.prod_equiv (Equiv.mulLeft e) _ _ fun π => (prod_erase_mul_left m e π
    (fun π' => t m (e * π) - t m π')).symm

/-- `R m τ = ∑_π t(π τ) · discOff m π · lagNum m π`. -/
theorem R_eq (τ : Equiv.Perm (Fin m)) :
    R m τ = ∑ π, C (t m (π * τ) * discOff m π) * lagNum m π := rfl

/-- The universal Lagrange-type polynomial `R m τ` is invariant under permutations of the
universal roots. -/
theorem map_rename_R (e τ : Equiv.Perm (Fin m)) :
    (R m τ).map (MvPolynomial.rename e).toRingHom = R m τ := by
  rw [R_eq, Polynomial.map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft e) _ _ fun π => ?_
  rw [Polynomial.map_mul, map_C, map_rename_lagNum]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, rename_t,
    rename_discOff, Equiv.coe_mulLeft, mul_assoc]

/-- Every coefficient of the universal resolvent `Φ m` is symmetric in the universal roots. -/
theorem isSymmetric_coeff_Φ (k : ℕ) : (Φ m |>.coeff k).IsSymmetric := fun e => by
  have := congrArg (fun P => P.coeff k) (map_rename_Φ m e)
  simpa using this

/-- The universal discriminant `Δ m` is symmetric in the universal roots. -/
theorem isSymmetric_Δ : (Δ m).IsSymmetric := rename_Δ m

/-- Every coefficient of `R m τ` is symmetric in the universal roots. -/
theorem isSymmetric_coeff_R (τ : Equiv.Perm (Fin m)) (k : ℕ) : ((R m τ).coeff k).IsSymmetric :=
  fun e => by
    have := congrArg (fun P => P.coeff k) (map_rename_R m e τ)
    simpa using this

/-- Write a symmetric polynomial in the universal roots as a polynomial in the elementary
symmetric polynomials (the fundamental theorem of symmetric polynomials). -/
def desym (s : RootRing m) (hs : s.IsSymmetric) : MvPolynomial (Fin m) (CoeffRing m) :=
  (MvPolynomial.esymmAlgEquiv (Fin m) (CoeffRing m) (Fintype.card_fin m)).symm ⟨s, hs⟩

/-- Substituting the elementary symmetric polynomials into `desym m s hs` recovers `s`. -/
theorem aeval_desym (s : RootRing m) (hs : s.IsSymmetric) :
    MvPolynomial.aeval (fun i : Fin m => MvPolynomial.esymm (Fin m) (CoeffRing m) (i + 1))
      (desym m s hs) = s := by
  rw [← MvPolynomial.esymmAlgHom_apply]
  show ((MvPolynomial.esymmAlgEquiv (Fin m) (CoeffRing m) (Fintype.card_fin m))
    ((MvPolynomial.esymmAlgEquiv (Fin m) (CoeffRing m) (Fintype.card_fin m)).symm ⟨s, hs⟩)).val = s
  rw [AlgEquiv.apply_symm_apply]

variable {m} {A B : Type*} [CommRing A] [CommRing B]

/-- Specialize the elementary symmetric polynomials to the signed coefficients of `f` and keep the
coefficients of the linear form as variables. -/
def κ (f : A[X]) : MvPolynomial (Fin m) (CoeffRing m) →+* MvPolynomial (Fin m) A :=
  MvPolynomial.eval₂Hom (MvPolynomial.map (Int.castRingHom A))
    (fun j : Fin m => MvPolynomial.C ((-1) ^ ((j : ℕ) + 1) * f.coeff (m - ((j : ℕ) + 1))))

/-- Evaluation of the universal roots at `b` and of the universal coefficients at `ψ ∘ c`. -/
def evalRoot (ψ : A →+* B) (c : Fin m → A) (b : Fin m → B) : RootRing m →+* B :=
  MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Int.castRingHom B) fun i => ψ (c i)) b

/-- `evalRoot ψ c b` sends `t(π)` to `∑ᵢ ψ (c i) * b (π i)`. -/
theorem evalRoot_t (ψ : A →+* B) (c : Fin m → A) (b : Fin m → B) (π : Equiv.Perm (Fin m)) :
    evalRoot ψ c b (t m π) = ∑ i, ψ (c i) * b (π i) := by
  simp [evalRoot, t]

/-- Evaluating the `n`-th elementary symmetric polynomial at `b` gives the `n`-th elementary
symmetric function of the values of `b`. -/
theorem eval₂_esymm {σ R S : Type*} [CommSemiring R] [CommSemiring S] [Fintype σ]
    (g : R →+* S) (b : σ → S) (n : ℕ) :
    MvPolynomial.eval₂ g b (MvPolynomial.esymm σ R n) = (univ.val.map b).esymm n := by
  simp_rw [MvPolynomial.esymm, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_prod,
    MvPolynomial.eval₂_X, Finset.esymm_map_val]

/-- **The specialization of a symmetric function.** If `f` maps to `∏ (X - b i)`, then evaluating
the specialization of a symmetric polynomial `s` at `c` is evaluating `s` at the roots `b`. -/
theorem map_eval_κ_desym (f : A[X]) (ψ : A →+* B) (b : Fin m → B)
    (hb : f.map ψ = ∏ i, (X - C (b i))) (c : Fin m → A) (s : RootRing m) (hs : s.IsSymmetric) :
    ψ (MvPolynomial.eval c (κ f (desym m s hs))) = evalRoot ψ c b s := by
  conv_rhs => rw [← aeval_desym m s hs]
  generalize desym m s hs = P
  have hγ : ∀ r : CoeffRing m, ψ (MvPolynomial.eval₂ (Int.castRingHom A) c r) =
      MvPolynomial.eval₂ (Int.castRingHom B) (fun i => ψ (c i)) r := by
    intro r
    rw [MvPolynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  have hvieta : ∀ j : Fin m, ψ ((-1) ^ ((j : ℕ) + 1) * f.coeff (m - ((j : ℕ) + 1))) =
      (univ.val.map b).esymm ((j : ℕ) + 1) := by
    intro j
    have hcoeff := congrArg (fun P => P.coeff (m - ((j : ℕ) + 1))) hb
    simp only [coeff_map] at hcoeff
    rw [Finset.prod_eq_multiset_prod] at hcoeff
    rw [show (univ.val.map fun i => X - C (b i)) = (univ.val.map b).map (fun t => X - C t) by
      rw [Multiset.map_map]; rfl] at hcoeff
    rw [Multiset.prod_X_sub_C_coeff _ (by simp)] at hcoeff
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin] at hcoeff
    have hk : m - (m - ((j : ℕ) + 1)) = (j : ℕ) + 1 := by omega
    rw [hk] at hcoeff
    rw [map_mul, hcoeff, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
    simp
  induction P using MvPolynomial.induction_on with
  | C a => simpa [κ, evalRoot] using hγ a
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp, MvPolynomial.aeval_X]
    congr 1
    simp only [κ, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_C, evalRoot,
      MvPolynomial.coe_eval₂Hom, eval₂_esymm, hvieta]

variable (m) in
/-- The universal resolvent `Φ m` is monic. -/
theorem monic_Φ : (Φ m).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

variable (m) in
/-- The universal resolvent `Φ m` has degree `m !`. -/
theorem natDegree_Φ : (Φ m).natDegree = m ! := by
  rw [Φ, natDegree_prod_of_monic _ _ fun π _ => monic_X_sub_C _]
  simp [Fintype.card_perm]

variable (m) in
/-- The universal Lagrange-type polynomial `R m τ` has degree at most `m !`. -/
theorem natDegree_R_le (τ : Equiv.Perm (Fin m)) : (R m τ).natDegree ≤ m ! := by
  rw [R_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun π _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [lagNum, natDegree_prod_of_monic _ _ fun π _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem
    (Finset.mem_univ _), Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  exact Nat.sub_le _ _

variable (m) in
/-- `Δ m` is the product of the factor `∏_{π' ≠ π} (t(π) - t(π'))` of index `π` and
`discOff m π`. -/
theorem Δ_eq_mul_discOff (π : Equiv.Perm (Fin m)) :
    Δ m = (∏ π' ∈ univ.erase π, (t m π - t m π')) * discOff m π := by
  rw [Δ, discOff, ← Finset.mul_prod_erase _ _ (Finset.mem_univ π)]

variable (m) in
/-- `R_τ(t(π)) = Δ · t(π τ)` for the universal polynomials. -/
theorem eval_R (τ π : Equiv.Perm (Fin m)) : (R m τ).eval (t m π) = Δ m * t m (π * τ) := by
  rw [R_eq, eval_finset_sum, Finset.sum_eq_single π]
  · rw [eval_mul, eval_C, lagNum, eval_prod, Δ_eq_mul_discOff m π]
    simp only [eval_sub, eval_X, eval_C]
    ring
  · intro ρ _ hρ
    rw [eval_mul, lagNum, eval_prod, Finset.prod_eq_zero (i := π)
      (Finset.mem_erase.mpr ⟨Ne.symm hρ, Finset.mem_univ π⟩) (by simp), mul_zero]
  · intro h; exact absurd (Finset.mem_univ π) h

/-- The specialization of a universal polynomial with symmetric coefficients of degree at most
`m !`. -/
def specPoly (f : A[X]) (c : Fin m → A) (P : (RootRing m)[X])
    (hP : ∀ k, (P.coeff k).IsSymmetric) : A[X] :=
  ∑ k ∈ range (m ! + 1), C (MvPolynomial.eval c (κ f (desym m _ (hP k)))) * X ^ k

/-- If `f` maps to `∏ (X - b i)` under `ψ`, then the image under `ψ` of `specPoly f c P hP` is
`P` with its coefficients evaluated by `evalRoot ψ c b`. -/
theorem map_specPoly (f : A[X]) (ψ : A →+* B) (b : Fin m → B)
    (hb : f.map ψ = ∏ i, (X - C (b i))) (c : Fin m → A) (P : (RootRing m)[X])
    (hP : ∀ k, (P.coeff k).IsSymmetric) (hdeg : P.natDegree ≤ m !) :
    (specPoly f c P hP).map ψ = P.map (evalRoot ψ c b) := by
  rw [specPoly, Polynomial.map_sum]
  simp only [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
    map_eval_κ_desym f ψ b hb c]
  conv_rhs => rw [(P.map (evalRoot ψ c b)).as_sum_range' (m ! + 1)
    ((natDegree_map_le).trans_lt (Nat.lt_succ_of_le hdeg))]
  simp [coeff_map, C_mul_X_pow_eq_monomial]

/-- The `k`-th coefficient of `specPoly f c P hP`. -/
private theorem coeff_specPoly (f : A[X]) (c : Fin m → A) (P : (RootRing m)[X])
    (hP : ∀ k, (P.coeff k).IsSymmetric) (k : ℕ) :
    (specPoly f c P hP).coeff k =
      if k ∈ range (m ! + 1) then MvPolynomial.eval c (κ f (desym m _ (hP k))) else 0 := by
  simp only [specPoly, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]

end GaloisResolvent

open GaloisResolvent

variable {m : ℕ} {A B : Type*} [CommRing A] [CommRing B]

/-- The **Galois resolvent** `Φ(T) = ∏_π (T - ∑ᵢ cᵢ b_{π i})` of `f` for the linear form with
coefficients `c`, where the `b i` are the roots of `f`; its coefficients are polynomials in the
coefficients of `f` and in `c`, by the fundamental theorem of symmetric polynomials. -/
def galoisResolvent (f : A[X]) (c : Fin m → A) : A[X] :=
  specPoly f c (Φ m) (isSymmetric_coeff_Φ m)

variable (m) in
/-- The discriminant of the Galois resolvent as a polynomial in the coefficients `c` of the linear
form. -/
def resolventDiscPoly (f : A[X]) : MvPolynomial (Fin m) A :=
  κ f (desym m (Δ m) (isSymmetric_Δ m))

/-- The **resolvent discriminant** `∏_{π ≠ π'} (t(π) - t(π'))`. -/
def resolventDisc (f : A[X]) (c : Fin m → A) : A :=
  MvPolynomial.eval c (resolventDiscPoly m f)

/-- The **Lagrange-type polynomial** `R_τ`, with `R_τ(t(π)) = Δ · t(π τ)`. -/
def resolventPerm (f : A[X]) (c : Fin m → A) (τ : Equiv.Perm (Fin m)) : A[X] :=
  specPoly f c (R m τ) (isSymmetric_coeff_R m τ)

/-- The twisted composite `Δ^{deg Ψ} Ψ^{fr}(R / Δ)`, written without denominators. -/
def twistedComp (fr : A →+* A) (Ψ : A[X][X]) (R : A[X][X]) (Δ : A[X]) : A[X][X] :=
  ∑ k ∈ Finset.range (Ψ.natDegree + 1), C (Δ ^ (Ψ.natDegree - k) * (Ψ.coeff k).map fr) * R ^ k

/-- If `f` maps to `∏ (X - b i)` under `ψ`, then with `t(π) = ∑ᵢ ψ (c i) * b (π i)` the image of
`galoisResolvent f c` is `∏_π (X - t(π))`, the image of `resolventDisc f c` is
`Δ = ∏_{π ≠ π'} (t(π) - t(π'))`, and the image of `resolventPerm f c τ` takes the value
`Δ · t(π τ)` at `t(π)`. -/
theorem galoisResolvent_spec (f : A[X]) (c : Fin m → A) (ψ : A →+* B) (b : Fin m → B)
    (hb : f.map ψ = ∏ i, (X - C (b i))) :
    (galoisResolvent f c).map ψ = ∏ π : Equiv.Perm (Fin m), (X - C (∑ i, ψ (c i) * b (π i))) ∧
      ψ (resolventDisc f c) = ∏ π : Equiv.Perm (Fin m), ∏ π' ∈ Finset.univ.erase π,
        ((∑ i, ψ (c i) * b (π i)) - ∑ i, ψ (c i) * b (π' i)) ∧
      ∀ τ π : Equiv.Perm (Fin m), ((resolventPerm f c τ).map ψ).eval (∑ i, ψ (c i) * b (π i)) =
        ψ (resolventDisc f c) * ∑ i, ψ (c i) * b ((π * τ) i) := by
  have hΔ : ψ (resolventDisc f c) = evalRoot ψ c b (Δ m) := map_eval_κ_desym f ψ b hb c _ _
  refine ⟨?_, ?_, fun τ π => ?_⟩
  · rw [galoisResolvent, map_specPoly f ψ b hb c _ _ (natDegree_Φ m).le, Φ, Polynomial.map_prod]
    simp [evalRoot_t]
  · rw [hΔ, Δ]; simp [evalRoot_t]
  · rw [resolventPerm, map_specPoly f ψ b hb c _ _ (natDegree_R_le m τ), ← evalRoot_t ψ c b π,
      eval_map, eval₂_at_apply, eval_R, map_mul, hΔ, evalRoot_t]

/-- The Galois resolvent `galoisResolvent f c` is monic. -/
theorem galoisResolvent_monic (f : A[X]) (c : Fin m → A) : (galoisResolvent f c).Monic := by
  nontriviality A
  have hdeg : (galoisResolvent f c).natDegree ≤ m ! := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    rw [galoisResolvent, coeff_specPoly, if_neg (by simpa using hk)]
  refine monic_of_natDegree_le_of_coeff_eq_one _ hdeg ?_
  rw [galoisResolvent, coeff_specPoly, if_pos (by simp)]
  have h1 : (Φ m).coeff (m !) = 1 := by
    rw [← natDegree_Φ m]; exact monic_Φ m
  have : desym m _ (isSymmetric_coeff_Φ m (m !)) = 1 := by
    rw [show desym m _ (isSymmetric_coeff_Φ m (m !)) = desym m 1 MvPolynomial.IsSymmetric.one
      by simp only [desym, h1]]
    simp only [desym]
    exact (MvPolynomial.esymmAlgEquiv (Fin m) (CoeffRing m) (Fintype.card_fin m)).symm.map_one
  rw [this, map_one, map_one]



namespace GaloisResolvent

/-- Evaluating a multivariate polynomial at polynomials of degree at most `d`, with constant
coefficients, gives a polynomial of degree at most `totalDegree * d`. -/
theorem natDegree_eval₂_le {σ S R : Type*} [CommSemiring S] [CommSemiring R] (g : S →+* R[X])
    (hg : ∀ s, (g s).natDegree = 0) (x : σ → R[X]) (d : ℕ) (hx : ∀ i, (x i).natDegree ≤ d)
    (P : MvPolynomial σ S) : (MvPolynomial.eval₂ g x P).natDegree ≤ P.totalDegree * d := by
  classical
  rw [MvPolynomial.eval₂_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun α hα => ?_
  refine (natDegree_mul_le).trans ?_
  rw [hg, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i ∈ α.support, (x i ^ α i).natDegree ≤ ∑ i ∈ α.support, α i * d :=
        Finset.sum_le_sum fun i _ => (natDegree_pow_le).trans (Nat.mul_le_mul_left _ (hx i))
    _ = (α.sum fun _ e => e) * d := by rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ P.totalDegree * d := Nat.mul_le_mul_right _ (MvPolynomial.le_totalDegree hα)

/-- If the coefficients of `f ∈ R[X][X]` have degree at most `d`, then evaluating `κ f P` at
constants `C (c i)` gives a polynomial of degree at most `P.totalDegree * d`. -/
theorem natDegree_eval_κ_le {R : Type*} [CommRing R] (f : R[X][X]) (c : Fin m → R) (d : ℕ)
    (hf : ∀ j, (f.coeff j).natDegree ≤ d) (P : MvPolynomial (Fin m) (CoeffRing m)) :
    (MvPolynomial.eval (fun i => C (c i)) (κ f P)).natDegree ≤ P.totalDegree * d := by
  rw [κ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  refine natDegree_eval₂_le _ (fun r => ?_) _ d (fun j => ?_) P
  · have : (MvPolynomial.eval fun i => C (c i)) (MvPolynomial.map (Int.castRingHom R[X]) r) =
        C (MvPolynomial.eval₂ (Int.castRingHom R) c r) := by
      rw [MvPolynomial.eval_map, MvPolynomial.hom_eval₂]
      congr 1
    simp only [RingHom.comp_apply]
    rw [this, natDegree_C]
  simp only [Function.comp_apply, MvPolynomial.eval_C]
  refine (natDegree_mul_le).trans ?_
  rw [show ((-1 : R[X]) ^ ((j : ℕ) + 1)) = C ((-1) ^ ((j : ℕ) + 1)) by simp, natDegree_C, zero_add]
  exact hf _

/-- The coefficients of `specPoly` at constant `c` have degree at most `S * d`, if the total
degrees of the `desym` of the coefficients of `P` are at most `S`. -/
private theorem natDegree_coeff_specPoly_le {R : Type*} [CommRing R] (f : R[X][X]) (c : Fin m → R)
    (d : ℕ) (hf : ∀ j, (f.coeff j).natDegree ≤ d) (P : (RootRing m)[X])
    (hP : ∀ k, (P.coeff k).IsSymmetric) (S : ℕ)
    (hS : ∀ k ∈ range (m ! + 1), (desym m _ (hP k)).totalDegree ≤ S) (k : ℕ) :
    ((specPoly f (fun i => C (c i)) P hP).coeff k).natDegree ≤ S * d := by
  rw [coeff_specPoly]
  split_ifs with hk
  · exact (natDegree_eval_κ_le f c d hf _).trans (Nat.mul_le_mul_right _ (hS k hk))
  · simp

end GaloisResolvent

open GaloisResolvent in
/-- There is a bound `D`, depending only on `m` and `d`, such that for every monic `f ∈ R[X][X]`
of degree `m` whose coefficients have degree at most `d` and every `c` with constant coordinates,
the coefficients of `galoisResolvent f c`, the discriminant `resolventDisc f c`, and each
`resolventPerm f c τ` and its coefficients have degree at most `D`. -/
theorem exists_natDegree_resolvent_le (m d : ℕ) : ∃ D : ℕ, ∀ (R : Type*) [CommRing R]
    (f : R[X][X]) (c : Fin m → R), f.Monic → f.natDegree = m → (∀ j, (f.coeff j).natDegree ≤ d) →
      (∀ k, ((galoisResolvent f (fun i => C (c i))).coeff k).natDegree ≤ D) ∧
      (resolventDisc f (fun i => C (c i))).natDegree ≤ D ∧
      ∀ τ, (resolventPerm f (fun i => C (c i)) τ).natDegree ≤ D ∧
        ∀ k, ((resolventPerm f (fun i => C (c i)) τ).coeff k).natDegree ≤ D := by
  classical
  let S₁ := ∑ k ∈ range (m ! + 1), (desym m _ (isSymmetric_coeff_Φ m k)).totalDegree
  let S₂ := (desym m _ (isSymmetric_Δ m)).totalDegree
  let S₃ := ∑ τ : Equiv.Perm (Fin m), ∑ k ∈ range (m ! + 1),
    (desym m _ (isSymmetric_coeff_R m τ k)).totalDegree
  refine ⟨m ! + (S₁ + S₂ + S₃) * d, fun R _ f c _ _ hf =>
    ⟨fun k => ?_, ?_, fun τ => ⟨?_, fun k => ?_⟩⟩⟩
  · refine (natDegree_coeff_specPoly_le f c d hf _ _ S₁ (fun k hk => ?_) k).trans ?_
    · exact Finset.single_le_sum (f := fun k => (desym m _ (isSymmetric_coeff_Φ m k)).totalDegree)
        (fun _ _ => Nat.zero_le _) hk
    · nlinarith
  · rw [resolventDisc, resolventDiscPoly]
    refine (natDegree_eval_κ_le f c d hf _).trans ?_
    nlinarith
  · rw [resolventPerm, specPoly]
    refine (natDegree_sum_le_of_forall_le _ _ fun k hk => ?_)
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    have := Finset.mem_range.mp hk
    omega
  · refine (natDegree_coeff_specPoly_le f c d hf _ _ S₃ (fun k hk => ?_) k).trans ?_
    · refine le_trans (Finset.single_le_sum (f := fun k =>
        (desym m _ (isSymmetric_coeff_R m τ k)).totalDegree) (fun _ _ => Nat.zero_le _) hk)
        (Finset.single_le_sum (f := fun τ => ∑ k ∈ range (m ! + 1),
          (desym m _ (isSymmetric_coeff_R m τ k)).totalDegree) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ τ))
    · nlinarith

namespace GaloisResolvent

/-- Specializing along `f` viewed with constant coefficients in `MvPolynomial (Fin m) A` and then
evaluating at the variables gives the specialization `κ f P`. -/
theorem eval_X_κ_map_C {A : Type*} [CommRing A] (f : A[X])
    (P : MvPolynomial (Fin m) (CoeffRing m)) :
    MvPolynomial.eval MvPolynomial.X (κ (f.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)) P) =
      κ f P := by
  rw [κ, κ, MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  congr 1
  · refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => by simp)
    simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval_C]
    rfl
  · funext j; simp [coeff_map]

/-- Mapping the coefficients along an injective ring homomorphism preserves the total degree. -/
theorem totalDegree_map_of_injective {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {g : R →+* S} (hg : Function.Injective g) (p : MvPolynomial σ R) :
    (MvPolynomial.map g p).totalDegree = p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree,
    MvPolynomial.support_map_of_injective _ hg]

end GaloisResolvent

open GaloisResolvent in
/-- For a monic `f` of degree `m` over a domain, separable over the fraction field, and a finite
set `S` with more than `(m !) ^ 2` elements, some `c` with coordinates in `S` has
`resolventDisc f c ≠ 0`. -/
theorem exists_resolventDisc_ne_zero {A : Type*} [CommRing A] [IsDomain A] (f : A[X])
    (hf : f.Monic) (hm : f.natDegree = m)
    (hsep : (f.map (algebraMap A (FractionRing A))).Separable) (S : Finset A)
    (hS : (m !) ^ 2 < S.card) :
    ∃ c : Fin m → A, (∀ i, c i ∈ S) ∧ resolventDisc f c ≠ 0 := by
  classical
  let K := FractionRing A
  let L := SplittingField (f.map (algebraMap A K))
  let fL := f.map (algebraMap A L)
  have hfL : fL = (f.map (algebraMap A K)).map (algebraMap K L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hsplit : Splits fL := hfL ▸ SplittingField.splits _
  have hsepL : fL.Separable := hfL ▸ hsep.map
  have hnodup := nodup_roots hsepL
  have hcard : fL.roots.toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots,
      show fL.natDegree = f.natDegree from hf.natDegree_map _, hm]
  let e : fL.roots.toFinset ≃ Fin m := Fintype.equivFinOfCardEq (by simpa using hcard)
  let b : Fin m → L := fun i => (e.symm i : L)
  have hbinj : Function.Injective b := fun i j h => e.symm.injective (Subtype.ext h)
  have hb : fL = ∏ i, (X - C (b i)) := by
    conv_lhs => rw [hsplit.eq_prod_roots_of_monic (hf.map _)]
    rw [show fL.roots = fL.roots.toFinset.val by
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup], ← Finset.prod_eq_multiset_prod,
      ← Finset.prod_coe_sort]
    exact Fintype.prod_equiv e _ _ fun x => by simp [b]
  let A' := MvPolynomial (Fin m) A
  let ψ : A' →+* MvPolynomial (Fin m) L := MvPolynomial.map (algebraMap A L)
  have hAL : Function.Injective (algebraMap A L) := IsScalarTower.algebraMap_eq A K L ▸
    (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let f' : A'[X] := f.map MvPolynomial.C
  have hb' : f'.map ψ = ∏ i, (X - C (MvPolynomial.C (b i))) := by
    have : f'.map ψ = fL.map MvPolynomial.C := by
      simp only [f', fL, Polynomial.map_map]; congr 1; exact MvPolynomial.map_comp_C _
    rw [this, hb, Polynomial.map_prod]; simp
  have hQ := (galoisResolvent_spec f' MvPolynomial.X ψ _ hb').2.1
  have hQeq : resolventDisc f' MvPolynomial.X = resolventDiscPoly m f := eval_X_κ_map_C f _
  rw [hQeq] at hQ
  have hfac : ∀ π : Equiv.Perm (Fin m), ∀ π' ∈ Finset.univ.erase π,
      ((∑ i, ψ (MvPolynomial.X i) * MvPolynomial.C (b (π i))) -
        ∑ i, ψ (MvPolynomial.X i) * MvPolynomial.C (b (π' i))) =
      ∑ i, MvPolynomial.C (b (π i) - b (π' i)) * MvPolynomial.X i := by
    intro π π' _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ψ (MvPolynomial.X i) = MvPolynomial.X i from MvPolynomial.map_X _ _, map_sub]
    ring
  have hlin : ∀ π : Equiv.Perm (Fin m), ∀ π' ∈ Finset.univ.erase π,
      (∑ i, MvPolynomial.C (b (π i) - b (π' i)) * MvPolynomial.X i : MvPolynomial (Fin m) L) ≠ 0 ∧
      (∑ i, MvPolynomial.C (b (π i) - b (π' i)) * MvPolynomial.X i :
        MvPolynomial (Fin m) L).totalDegree ≤ 1 := by
    intro π π' hπ'
    have hne : π' ≠ π := (Finset.mem_erase.mp hπ').1
    obtain ⟨i, hi⟩ : ∃ i, π i ≠ π' i := by
      by_contra! h; exact hne (Equiv.ext fun i => (h i).symm)
    refine ⟨fun h0 => ?_, ?_⟩
    · have := congrArg (fun p : MvPolynomial (Fin m) L => p.coeff (Finsupp.single i 1)) h0
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Finsupp.single_left_inj one_ne_zero, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact hi (hbinj (sub_eq_zero.mp this))
    · refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  have hQ0 : resolventDiscPoly m f ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hQ
    refine (Finset.prod_ne_zero_iff.mpr fun π _ => Finset.prod_ne_zero_iff.mpr fun π' hπ' => ?_)
      hQ.symm
    rw [hfac π π' hπ']; exact (hlin π π' hπ').1
  have hdeg : (resolventDiscPoly m f).totalDegree < S.card := by
    have hmap : (ψ (resolventDiscPoly m f)).totalDegree = (resolventDiscPoly m f).totalDegree :=
      totalDegree_map_of_injective hAL _
    rw [← hmap, hQ]
    refine lt_of_le_of_lt ?_ hS
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans
      ((Finset.sum_le_sum fun π _ => ?_).trans (le_of_eq (show ∑ _π : Equiv.Perm (Fin m), m ! =
        (m !) ^ 2 by simp [Fintype.card_perm, sq])))
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine (Finset.sum_le_sum fun π' hπ' => ?_).trans (show ∑ _π' ∈ univ.erase π, 1 ≤ (m !) by
      simp [Finset.card_erase_of_mem (Finset.mem_univ π), Fintype.card_perm])
    rw [hfac π π' hπ']; exact (hlin π π' hπ').2
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hQ0 S
  by_contra! hall
  have hfilter : ({x ∈ Fintype.piFinset fun _ : Fin m => S |
      MvPolynomial.eval x (resolventDiscPoly m f) = 0} : Finset (Fin m → A)) =
      Fintype.piFinset fun _ => S :=
    Finset.filter_true_of_mem fun x hx => hall x (Fintype.mem_piFinset.mp hx)
  rw [hfilter, Fintype.card_piFinset_const, Nat.cast_pow] at hsz
  have hSpos : (0 : ℚ≥0) < S.card := by exact_mod_cast (Nat.zero_le _).trans_lt hS
  rw [div_self (pow_ne_zero _ hSpos.ne'), le_div_iff₀ hSpos, one_mul] at hsz
  exact absurd hsz (not_le.mpr (mod_cast hdeg))

end Polynomial
