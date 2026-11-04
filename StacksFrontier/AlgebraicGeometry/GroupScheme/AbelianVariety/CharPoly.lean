module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.EndomorphismKernelCount
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TateModule
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionCharpolyDense
public import StacksFrontier.Algebra.MvPolynomial.HomogeneousOfScaling

/-!
# The characteristic polynomial of an endomorphism of an abelian variety

Let `A` be an abelian variety of dimension `g` over a field `k` and `α` an endomorphism of `A`
(a homomorphism of group schemes). Write `deg` for the degree of an endomorphism
(`Stacks.Groupoids.endDegree`: the degree of the extension of function fields when it is dominant,
that is an isogeny, and `0` otherwise). Following [Mumford, *Abelian varieties*, §19] and
[Milne, *Abelian varieties*, I.10–I.12], this file proves:

* **the degree is a homogeneous polynomial of degree `2g`**: for endomorphisms `α, β` the function
  `(n, m) ↦ deg (nα + mβ)` is given by a homogeneous polynomial of degree `2g` with rational
  coefficients (`Stacks.Groupoids.exists_isHomogeneous_endDegree_zpow_mul_zpow`, Mumford §19,
  Theorem 2 and Milne, Proposition I.10.13);
* **the characteristic polynomial**: there is a unique monic `χ_α ∈ ℚ[X]` of degree `2g` with
  `χ_α(n) = deg (α - n)` for all integers `n` (`Stacks.Groupoids.endCharPoly`);
* **`deg α = det(T_ℓ α)`**: for `k` algebraically closed and `ℓ` a prime invertible in `k`,
  `χ_α` is the characteristic polynomial of `α` acting on the `ℓ`-adic Tate module `T_ℓ A`
  (`Stacks.Groupoids.charpoly_tateModuleMap`, Mumford §19, Theorem 4 and Milne,
  Proposition I.10.20). Consequently `deg α = det(T_ℓ α)`
  (`Stacks.Groupoids.endDegree_eq_det_tateModuleMap`) and the trace of `T_ℓ α` is the rational
  number `Tr(α) = -χ_α.nextCoeff`, independent of `ℓ`
  (`Stacks.Groupoids.trace_tateModuleMap_eq_abelianVarietyTrace`).

## The proof of `χ_α = det(X - T_ℓ α)`

The degree `R ↦ deg R(α)` on `ℤ[X]` is the norm form of `χ_α`:
`deg R(α) = Res(χ_α, R)` (`Stacks.Groupoids.exists_endDegree_endPolyEval_eq_normForm`). For `R`
in the set described below, `R(α)` is étale, so its kernel on `A(k)` has exactly `deg R(α)`
points (`Stacks.Groupoids.natCard_comp_eq_one_eq_endDegree_of_charZero`,
`Stacks.Groupoids.natCard_comp_endPolyEval_eq_one_eq_endDegree_of_charP`). Kernel counts on
`A(k)[ℓ^N]` for `N` large determine the `ℓ`-adic valuation of `det R(T_ℓ α)`, and Mumford's
resultant lemma, for a set of `R` which is `ℓ`-adically dense, identifies the characteristic
polynomial of `T_ℓ α` with `χ_α`
(`Stacks.Picard.exists_charpoly_levelMatrix_eq_of_normForm_of_dense`). The set is: all `R` in
characteristic `0`, and in characteristic `p` the `R` congruent modulo `p` to a constant prime to
`p` (`Stacks.Polynomial.exists_intPoly_map_toZModPow_eq_modEq_const`). Mumford and Milne use all
`R` together with the equality `v_ℓ(#Ker β) = v_ℓ(deg β)` for every isogeny `β`. That equality
rests on the inseparable degree being a power of `p`. For an étale `β` it is just `#Ker β = deg β`,
and the restriction to étale `R(α)` is what lets this proof avoid it.

## Main definitions

* `Stacks.Groupoids.endCharPoly A α`: the characteristic polynomial `χ_α ∈ ℚ[X]`.
* `Stacks.Groupoids.abelianVarietyTrace A α`: the trace `Tr(α) ∈ ℚ`.

## References

* [D. Mumford, *Abelian varieties*, §19]
* [J. S. Milne, *Abelian varieties*, I.10–I.12]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Polynomial
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

section Degree

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

/-- **Homogeneity of the degree**: `deg (n • f) = n ^ (2 g) · deg f` for every integer `n`,
`n = 0` included. -/
theorem endDegree_zpow_eq_pow_mul (f : A ⟶ A) (n : ℤ) :
    (endDegree A (f ^ n) : ℤ) = n ^ (2 * abelianVarietyDimension A) * endDegree A f := by
  have h : f ^ n = f ≫ (𝟙 A : A ⟶ A) ^ n := by rw [GrpObj.comp_zpow, Category.comp_id]
  rw [h, endDegree_comp, Nat.cast_mul, endDegree_zpow_id_eq_pow, mul_comm]

/-- **The degree of `nα + mβ` is a homogeneous polynomial of degree `2g` in `(n, m)`**
([Mumford, *Abelian varieties*, §19, Theorem 2], [Milne, *Abelian varieties*, I.10.13]). Here
`nα + mβ` is `α ^ n * β ^ m` in the multiplicative notation of the group `A ⟶ A`. -/
theorem exists_isHomogeneous_endDegree_zpow_mul_zpow (α β : A ⟶ A) :
    ∃ P : MvPolynomial (Fin 2) ℚ, P.IsHomogeneous (2 * abelianVarietyDimension A) ∧
      ∀ n m : ℤ, (endDegree A (α ^ n * β ^ m) : ℚ) = MvPolynomial.eval ![(n : ℚ), (m : ℚ)] P := by
  obtain ⟨P, -, hP⟩ := exists_mvPolynomial_endDegree_prod_zpow A ![α, β]
  have hprod : ∀ c : Fin 2 → ℤ, ∏ j, ![α, β] j ^ c j = α ^ c 0 * β ^ c 1 := fun c =>
    Fin.prod_univ_two _
  refine ⟨P, MvPolynomial.isHomogeneous_of_eval_intCast_mul fun m c => ?_, fun n m => ?_⟩
  · have h1 := hP (fun i => m * c i)
    have h2 := hP c
    rw [hprod] at h1 h2
    rw [← h1, ← h2, mul_comm m (c 0), mul_comm m (c 1), zpow_mul, zpow_mul, ← mul_zpow]
    exact_mod_cast endDegree_zpow_eq_pow_mul A (α ^ c 0 * β ^ c 1) m
  · have h := hP ![n, m]
    rw [hprod] at h
    have hv : (fun j => ((![n, m] j : ℤ) : ℚ)) = ![(n : ℚ), (m : ℚ)] := by
      funext j
      fin_cases j <;> rfl
    rw [← hv]
    exact h

/-- **The characteristic polynomial of an endomorphism** `α` of an abelian variety: the monic
polynomial `χ_α ∈ ℚ[X]` of degree `2g` with `χ_α(n) = deg (α - n)` for all integers `n`, so
that `deg R(α) = N(R mod χ_α)` for every `R ∈ ℤ[X]`
(`Stacks.Groupoids.exists_endDegree_endPolyEval_eq_normForm`). It is unique, a polynomial being
determined by its values at the integers. -/
def endCharPoly (α : A ⟶ A) [IsMonHom α] : ℚ[X] :=
  (exists_endDegree_endPolyEval_eq_normForm A α).choose

variable (α : A ⟶ A) [IsMonHom α]

/-- `χ_α` is monic. -/
theorem endCharPoly_monic : (endCharPoly A α).Monic :=
  (exists_endDegree_endPolyEval_eq_normForm A α).choose_spec.1

/-- `χ_α` has degree `2 g`. -/
theorem natDegree_endCharPoly :
    (endCharPoly A α).natDegree = 2 * abelianVarietyDimension A :=
  (exists_endDegree_endPolyEval_eq_normForm A α).choose_spec.2.1

/-- `χ_α(n) = deg (α - n)`. -/
theorem eval_intCast_endCharPoly (n : ℤ) :
    (endCharPoly A α).eval (n : ℚ) = endDegree A (α * ((𝟙 A) ^ n)⁻¹) :=
  (exists_endDegree_endPolyEval_eq_normForm A α).choose_spec.2.2.1 n

/-- `deg R(α) = N(R mod χ_α)`. -/
theorem endDegree_endPolyEval_eq_normForm (R : ℤ[X]) :
    (endDegree A (endPolyEval α R) : ℚ) = Stacks.Polynomial.normForm (endCharPoly A α) R :=
  (exists_endDegree_endPolyEval_eq_normForm A α).choose_spec.2.2.2 R

/-- The constant coefficient of `χ_α` is `deg α`. -/
theorem coeff_zero_endCharPoly : (endCharPoly A α).coeff 0 = endDegree A α := by
  rw [coeff_zero_eq_eval_zero, ← Int.cast_zero, eval_intCast_endCharPoly, zpow_zero, inv_one,
    mul_one]

/-- **The trace of an endomorphism** `α` of an abelian variety: minus the second coefficient of
its characteristic polynomial. -/
def abelianVarietyTrace : ℚ := -(endCharPoly A α).nextCoeff

end Degree

section Tate

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

omit [IsAlgClosed k] in
/-- The `ℓ`-adically dense set of polynomials `R` for which `R(α)` is étale for every
endomorphism `α`: in characteristic `p > 0` the `R` congruent modulo `p` to a constant prime to
`p`, and every `R` in characteristic `0`. -/
theorem exists_intPoly_map_toZModPow_eq_charP_modEq_const (hℓk : IsUnit (ℓ : k))
    (S : ℤ_[ℓ][X]) (N : ℕ) : ∃ R : ℤ[X], R.natDegree = S.natDegree ∧
      (∀ p : ℕ, p.Prime → CharP k p → ¬ (p : ℤ) ∣ R.coeff 0 ∧ ∀ j, j ≠ 0 → (p : ℤ) ∣ R.coeff j) ∧
      (R.map (Int.castRingHom ℤ_[ℓ])).map (PadicInt.toZModPow N) =
        S.map (PadicInt.toZModPow N) := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ CharP k p
  · obtain ⟨p, hp, hchar⟩ := h
    have hpℓ : p ≠ ℓ := by
      rintro rfl
      exact hℓk.ne_zero (CharP.cast_eq_zero k p)
    obtain ⟨R, hRdeg, hRp, hRS⟩ :=
      Stacks.Polynomial.exists_intPoly_map_toZModPow_eq_modEq_const p hp hpℓ S N
    refine ⟨R, hRdeg, fun q _ hq => ?_, hRS⟩
    obtain rfl := CharP.eq k hq hchar
    exact hRp
  · obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (ℓ + 1)
    have hpℓ : p ≠ ℓ := by lia
    obtain ⟨R, hRdeg, -, hRS⟩ :=
      Stacks.Polynomial.exists_intPoly_map_toZModPow_eq_modEq_const p hp hpℓ S N
    exact ⟨R, hRdeg, fun q hq hchar => absurd ⟨q, hq, hchar⟩ h, hRS⟩

variable (α : A ⟶ A) [IsMonHom α]

/-- **Kernel counts.** For `R` in the dense set of
`Stacks.Groupoids.exists_intPoly_map_toZModPow_eq_charP_modEq_const` with `deg R(α) ≠ 0`, the
kernel of `R(α)` on `A(k)` has `deg R(α) = N(R mod χ_α)` elements. -/
theorem natCard_ker_aeval_postcompPoints_eq_normForm (R : ℤ[X])
    (hR : ∀ p : ℕ, p.Prime → CharP k p → ¬ (p : ℤ) ∣ R.coeff 0 ∧ ∀ j, j ≠ 0 → (p : ℤ) ∣ R.coeff j)
    (hnorm : Stacks.Polynomial.normForm (endCharPoly A α) R ≠ 0) :
    (Nat.card (aeval (Stacks.Picard.asEnd (postcompPoints A α)) R).ker : ℚ) =
      Stacks.Polynomial.normForm (endCharPoly A α) R := by
  rw [Nat.card_congr (kerAevalPostcompPointsEquiv A α R), ← endDegree_endPolyEval_eq_normForm]
  congr 1
  have := isMonHom_endPolyEval α R
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | h0
  · have : CharP k (ringChar k) := ringChar.charP k
    exact natCard_comp_endPolyEval_eq_one_eq_endDegree_of_charP k A (ringChar k) α R
      (hR _ hp inferInstance).1 (hR _ hp inferInstance).2
  · have : CharP k 0 := h0 ▸ ringChar.charP k
    have := CharP.charP_to_charZero k
    refine natCard_comp_eq_one_eq_endDegree_of_charZero k A _ fun h => hnorm ?_
    rw [← endDegree_endPolyEval_eq_normForm, h, Nat.cast_zero]

/-- The `ℤ/ℓ^n`-module structure on the `ℓ^n`-torsion of `A(k)`. -/
abbrev torsionZModModule (n : ℕ) :
    Module (ZMod (ℓ ^ n))
      (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ : ℤ) ^ n)) :=
  haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  AddCommGroup.zmodModule fun x => by
    apply Subtype.ext
    have h := (Submodule.mem_torsionBy_iff _ _).1 x.2
    change (ℓ ^ n) • (x : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) = 0
    rw [← natCast_zsmul]
    push_cast
    exact h

/-- **The matrix of `T_ℓ α` reduces modulo `ℓ^n` to the matrix of `α` on `A(k)[ℓ^n]`**, in the
reduction of a `ℤ_ℓ`-basis of `T_ℓ A`. -/
theorem toMatrix_levelMap_tateReductionBasis {r : ℕ}
    (b : Module.Basis (Fin r) ℤ_[ℓ] (tateModule A ℓ))
    (n : ℕ) :
    letI : ∀ m : ℕ, Module (ZMod (ℓ ^ m))
        (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ : ℤ) ^ m)) :=
      fun m => torsionZModModule A ℓ m
    LinearMap.toMatrix
        (AbelianGroup.tateReductionBasis (exists_nsmul_eq_point A ℓ) b
          (AbelianGroup.torsionByNatCastPowEquiv _ ℓ n))
        (AbelianGroup.tateReductionBasis (exists_nsmul_eq_point A ℓ) b
          (AbelianGroup.torsionByNatCastPowEquiv _ ℓ n))
        (Stacks.Picard.levelMap (ℓ := ℓ) (postcompPoints A α) n) =
      (LinearMap.toMatrix b b (tateModuleMap ℓ α)).map (PadicInt.toZModPow n) := by
  classical
  let : ∀ m : ℕ, Module (ZMod (ℓ ^ m))
      (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ : ℤ) ^ m)) :=
    fun m => torsionZModModule A ℓ m
  set e := AbelianGroup.torsionByNatCastPowEquiv (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ℓ n
  set B := AbelianGroup.tateReductionBasis (exists_nsmul_eq_point A ℓ) b e
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
  have hB : Stacks.Picard.levelMap (ℓ := ℓ) (postcompPoints A α) n (B j) =
      Fintype.linearCombination (ZMod (ℓ ^ n)) (fun i => e (AbelianGroup.tateReduction ℓ n (b i)))
        (fun i => PadicInt.toZModPow n (b.repr (tateModuleMap ℓ α (b j)) i)) := by
    rw [← AbelianGroup.apply_tateReduction_linearCombination, Fintype.linearCombination_apply,
      ← Finset.sum_congr rfl fun i _ => rfl, b.sum_repr, AbelianGroup.tateReductionBasis_apply]
    exact Subtype.ext rfl
  rw [hB, AbelianGroup.tateReductionBasis_repr_linearCombination]

/-- **The characteristic polynomial of `T_ℓ α` is `χ_α`**, matrix form: for every `ℤ_ℓ`-basis `b`
of `T_ℓ A`, the characteristic polynomial of the matrix of `T_ℓ α` is `χ_α` in `ℚ_ℓ[X]`
([Mumford, *Abelian varieties*, §19, Theorem 4]). -/
theorem charpoly_toMatrix_tateModuleMap (hℓk : IsUnit (ℓ : k))
    (b : Module.Basis (Fin (2 * abelianVarietyDimension A)) ℤ_[ℓ] (tateModule A ℓ)) :
    (LinearMap.toMatrix b b (tateModuleMap ℓ α)).charpoly.map PadicInt.Coe.ringHom =
      (endCharPoly A α).map (algebraMap ℚ ℚ_[ℓ]) := by
  classical
  let : ∀ n : ℕ, Module (ZMod (ℓ ^ n))
      (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ : ℤ) ^ n)) :=
    fun n => torsionZModModule A ℓ n
  have hP : ∀ N, Nonempty (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A))
      ((ℓ : ℤ) ^ N) ≃+ (Fin (2 * abelianVarietyDimension A) → ZMod (ℓ ^ N))) :=
    fun N => ⟨(AbelianGroup.torsionByNatCastPowEquiv _ ℓ N).symm.trans
      (nonempty_torsionBy_pow_addEquiv A ℓ hℓk N).some⟩
  obtain ⟨F, hFχ, hF⟩ := Stacks.Picard.exists_charpoly_levelMatrix_eq_of_normForm_of_dense
    (postcompPoints A α) _ (exists_intPoly_map_toZModPow_eq_charP_modEq_const ℓ hℓk) hP
    (endCharPoly A α) (endCharPoly_monic A α) (natDegree_endCharPoly A α)
    (fun R hR hnorm => natCard_ker_aeval_postcompPoints_eq_normForm A α R hR hnorm)
  have hred : ∀ n, (LinearMap.toMatrix b b (tateModuleMap ℓ α)).charpoly.map
      (PadicInt.toZModPow n) = F.map (PadicInt.toZModPow n) := by
    intro n
    rw [← Matrix.charpoly_map, ← toMatrix_levelMap_tateReductionBasis A ℓ α b n,
      ← hF n ((hP n).some)]
    exact Stacks.Picard.charpoly_toMatrix_eq _ n _ _
  have hMF : (LinearMap.toMatrix b b (tateModuleMap ℓ α)).charpoly = F := by
    ext j
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    rw [← coeff_map, ← coeff_map, hred n]
  rw [hMF, hFχ]

/-- The `ℓ`-adic Tate module has a basis indexed by `Fin (2 g)`. -/
private theorem nonempty_basis_tateModule (hℓk : IsUnit (ℓ : k)) :
    Nonempty (Module.Basis (Fin (2 * abelianVarietyDimension A)) ℤ_[ℓ] (tateModule A ℓ)) := by
  have := module_free_tateModule A ℓ hℓk
  have := module_finite_tateModule A ℓ hℓk
  exact ⟨Module.finBasisOfFinrankEq _ _ (finrank_tateModule A ℓ hℓk)⟩

/-- **The characteristic polynomial of `T_ℓ α` is `χ_α`** ([Mumford, *Abelian varieties*, §19,
Theorem 4], [Milne, *Abelian varieties*, I.10.20]). Let `A` be an abelian variety over an
algebraically closed field `k`, `ℓ` a prime invertible in `k` and `α` an endomorphism of `A`.
Then `det(X - T_ℓ α) = χ_α` in `ℚ_ℓ[X]`, where `χ_α` is the rational polynomial with
`χ_α(n) = deg (α - n)`. -/
theorem charpoly_tateModuleMap (hℓk : IsUnit (ℓ : k)) :
    haveI := module_free_tateModule A ℓ hℓk
    haveI := module_finite_tateModule A ℓ hℓk
    (LinearMap.charpoly (tateModuleMap ℓ α)).map PadicInt.Coe.ringHom =
      (endCharPoly A α).map (algebraMap ℚ ℚ_[ℓ]) := by
  have := module_free_tateModule A ℓ hℓk
  have := module_finite_tateModule A ℓ hℓk
  obtain ⟨b⟩ := nonempty_basis_tateModule A ℓ hℓk
  rw [← LinearMap.charpoly_toMatrix (tateModuleMap ℓ α) b]
  exact charpoly_toMatrix_tateModuleMap A ℓ α hℓk b

/-- **`deg (α - n) = det(n - T_ℓ α)`**: the characteristic polynomial of `T_ℓ α`, evaluated at an
integer `n`, is the degree of `α - n` (in the multiplicative notation of `A ⟶ A`,
`α * ((𝟙 A) ^ n)⁻¹`); this is also the degree of `n - α`. -/
theorem endDegree_mul_zpow_inv_eq_eval_charpoly_tateModuleMap (hℓk : IsUnit (ℓ : k)) (n : ℤ) :
    haveI := module_free_tateModule A ℓ hℓk
    haveI := module_finite_tateModule A ℓ hℓk
    (endDegree A (α * ((𝟙 A) ^ n)⁻¹) : ℤ_[ℓ]) =
      (LinearMap.charpoly (tateModuleMap ℓ α)).eval (n : ℤ_[ℓ]) := by
  have := module_free_tateModule A ℓ hℓk
  have := module_finite_tateModule A ℓ hℓk
  apply Subtype.val_injective
  have h := congrArg (fun F => F.eval (n : ℚ_[ℓ])) (charpoly_tateModuleMap A ℓ α hℓk)
  simp only [eval_intCast_map, eval_intCast_endCharPoly, map_natCast] at h
  show ((endDegree A (α * ((𝟙 A) ^ n)⁻¹) : ℤ_[ℓ]) : ℚ_[ℓ]) = _
  rw [PadicInt.coe_natCast, ← h]
  rfl

/-- The characteristic polynomial of `T_ℓ α` has degree `2 g`. -/
theorem natDegree_charpoly_tateModuleMap (hℓk : IsUnit (ℓ : k)) :
    haveI := module_free_tateModule A ℓ hℓk
    haveI := module_finite_tateModule A ℓ hℓk
    (LinearMap.charpoly (tateModuleMap ℓ α)).natDegree = 2 * abelianVarietyDimension A := by
  have := module_free_tateModule A ℓ hℓk
  have := module_finite_tateModule A ℓ hℓk
  rw [LinearMap.charpoly_natDegree, finrank_tateModule A ℓ hℓk]

/-- **`deg α = det(T_ℓ α)`** ([Mumford, *Abelian varieties*, §19, Theorem 4]). For an
endomorphism `α` of an abelian variety over an algebraically closed field `k` and a prime `ℓ`
invertible in `k`, the degree of `α` (zero unless `α` is an isogeny) is the determinant of the
endomorphism `T_ℓ α` of the `ℓ`-adic Tate module. -/
theorem endDegree_eq_det_tateModuleMap (hℓk : IsUnit (ℓ : k)) :
    (endDegree A α : ℤ_[ℓ]) = LinearMap.det (tateModuleMap ℓ α) := by
  obtain ⟨b⟩ := nonempty_basis_tateModule A ℓ hℓk
  rw [← LinearMap.det_toMatrix b, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin,
    Even.neg_one_pow (even_two_mul _), one_mul]
  apply Subtype.val_injective
  have h := congrArg (fun F => F.coeff 0) (charpoly_toMatrix_tateModuleMap A ℓ α hℓk b)
  simp only [coeff_map, coeff_zero_endCharPoly, map_natCast] at h
  show ((endDegree A α : ℤ_[ℓ]) : ℚ_[ℓ]) = _
  rw [PadicInt.coe_natCast]
  exact h.symm

/-- **The trace of `T_ℓ α` is the rational number `Tr(α)`**, for every prime `ℓ` invertible in
the algebraically closed field `k`. In particular it is independent of `ℓ`, and `Tr(α)` is
`ℓ`-integral for every such `ℓ`. -/
theorem trace_tateModuleMap_eq_abelianVarietyTrace (hℓk : IsUnit (ℓ : k)) :
    ((LinearMap.trace ℤ_[ℓ] (tateModule A ℓ) (tateModuleMap ℓ α) : ℤ_[ℓ]) : ℚ_[ℓ]) =
      (abelianVarietyTrace A α : ℚ_[ℓ]) := by
  obtain ⟨b⟩ := nonempty_basis_tateModule A ℓ hℓk
  rw [LinearMap.trace_eq_matrix_trace ℤ_[ℓ] b, Matrix.trace_eq_neg_charpoly_nextCoeff]
  have h := congrArg Polynomial.nextCoeff (charpoly_toMatrix_tateModuleMap A ℓ α hℓk b)
  rw [nextCoeff_map Subtype.val_injective, nextCoeff_map (algebraMap ℚ ℚ_[ℓ]).injective] at h
  rw [abelianVarietyTrace, Rat.cast_neg, PadicInt.coe_neg, ← eq_ratCast (algebraMap ℚ ℚ_[ℓ]),
    ← h]
  rfl

end Tate

end Stacks.Groupoids
