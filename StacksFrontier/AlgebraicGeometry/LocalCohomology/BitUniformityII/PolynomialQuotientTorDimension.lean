module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Koszul.TorComparison.QuotientTor
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular
public import StacksFrontier.RingTheory.ReesAlgebra.ExtendEval
public import StacksFrontier.RingTheory.Tor.LongExactSequence

/-!
# The quotients `A[x₁, …, x_r]/(x₁, …, x_r)ⁿ` have Tor dimension at most `r`

In the standard example of system (4) of [Stacks, Tag 0GA5] the source remarks that the quotients
`A[x₁, …, x_r]/(x₁, …, x_r)ⁿ` have Tor dimension at most `r` for all `n`, so that the step of the
argument using [Stacks, Tag 0GA3] can be avoided there. This file proves that remark: for every
module `N` over `R = A[x₁, …, x_r]` and every `p > r`, `Tor_p^R(R/(x)ⁿ, N) = 0`.

## Main results

* `Stacks.LocalCohomology.UniformityII.isZero_tor_quotient_idealOfVars`: `R/(x)` has Tor
  dimension at most `r`.
* `Stacks.LocalCohomology.UniformityII.isZero_tor_quotient_pow_idealOfVars`: every quotient
  `R/(x)ⁿ` has Tor dimension at most `r`.

## Implementation notes

By induction on `n`, along the short exact sequences `0 → (x)ⁿ/(x)ⁿ⁺¹ → R/(x)ⁿ⁺¹ → R/(x)ⁿ → 0`
and the long exact sequence of `Tor_•(-, N)`: the module `(x)ⁿ/(x)ⁿ⁺¹` is a finite direct sum of
copies of `R/(x)`, one for each monomial of degree `n`, the copy indexed by `xˢ` mapping
`c ↦ c xˢ`.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory MvPolynomial

namespace Stacks.LocalCohomology.UniformityII

universe u

variable {A : Type u} [CommRing A] {r : ℕ}

/-- The exponents `s : Fin r →₀ ℕ` of the monomials of degree `n` in `r` variables. -/
@[reducible] alias degreeMonomials := Stacks.ReesAlgebra.degreeMonomials

/-- An exponent `s` lies in `degreeMonomials r n` if and only if `s` has degree `n`. -/
theorem mem_degreeMonomials {n : ℕ} {s : Fin r →₀ ℕ} :
    s ∈ degreeMonomials r n ↔ s.degree = n := by
  rw [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  simp

/-- If `s ≤ t` and `s` and `t` have the same degree, then `s = t`. -/
theorem eq_of_le_of_degree_eq {s t : Fin r →₀ ℕ} (h : s ≤ t) (hd : s.degree = t.degree) :
    s = t := by
  have h₁ : s + (t - s) = t := add_tsub_cancel_of_le h
  have h₂ : (t - s).degree = 0 := by
    have := congrArg Finsupp.degree h₁
    rw [map_add, hd] at this
    omega
  rw [Finsupp.degree_eq_zero_iff] at h₂
  rw [← h₁, h₂, add_zero]

/-- A monomial `xˢ` of degree `n` lies in `(x₁, …, x_r)ⁿ`. -/
theorem monomial_mem_pow_idealOfVars {n : ℕ} {s : Fin r →₀ ℕ} (hs : s.degree = n) :
    monomial s (1 : A) ∈ idealOfVars (Fin r) A ^ n := by
  refine (mem_pow_idealOfVars_iff n _).2 fun x hx => ?_
  rw [Finset.mem_singleton.1 (support_monomial_subset hx), hs]

/-- A polynomial with zero constant coefficient lies in `(x₁, …, x_r)`. -/
theorem mem_idealOfVars_of_coeff_zero {a : MvPolynomial (Fin r) A} (ha : a.coeff 0 = 0) :
    a ∈ idealOfVars (Fin r) A := by
  rw [← pow_one (idealOfVars (Fin r) A)]
  refine (mem_pow_idealOfVars_iff' 1 a).2 fun x hx => ?_
  rw [(Finsupp.degree_eq_zero_iff x).1 (by omega)]
  exact ha

variable (A r)

/-- Multiplication by a monomial `xˢ` of degree `n`, from `R/(x)` to `R/(x)ⁿ⁺¹`. -/
noncomputable def quotientMulMonomial (n : ℕ) (s : degreeMonomials r n) :
    (MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A) →ₗ[MvPolynomial (Fin r) A]
      (MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A ^ (n + 1)) :=
  Submodule.liftQ _ ((idealOfVars (Fin r) A ^ (n + 1)).mkQ ∘ₗ
      LinearMap.mulRight (MvPolynomial (Fin r) A) (monomial s.1 1)) (by
    intro a ha
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulRight_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, pow_succ']
    exact Ideal.mul_mem_mul ha (monomial_mem_pow_idealOfVars (mem_degreeMonomials.1 s.2)))

/-- The map `(R/(x))^{monomials of degree n} ⟶ R/(x)ⁿ⁺¹`, `(cₛ) ↦ ∑ cₛ xˢ`. -/
noncomputable def sumMulMonomial (n : ℕ) :
    (degreeMonomials r n → MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A)
      →ₗ[MvPolynomial (Fin r) A] (MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A ^ (n + 1)) :=
  ∑ s, quotientMulMonomial A r n s ∘ₗ LinearMap.proj s

/-- The canonical surjection `R/(x)ⁿ⁺¹ ⟶ R/(x)ⁿ`. -/
noncomputable abbrev quotientPowSucc (n : ℕ) :
    (MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A ^ (n + 1)) →ₗ[MvPolynomial (Fin r) A]
      (MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A ^ n) :=
  Submodule.factor (Ideal.pow_le_pow_right (Nat.le_succ n))

variable {A r}

/-- On classes of polynomials `aₛ`, `sumMulMonomial` is the class of `∑ aₛ xˢ`. -/
theorem sumMulMonomial_mk (n : ℕ) (a : degreeMonomials r n → MvPolynomial (Fin r) A) :
    sumMulMonomial A r n (fun s => Submodule.Quotient.mk (a s)) =
      Submodule.Quotient.mk (∑ s, a s * monomial s.1 1) := by
  rw [sumMulMonomial, LinearMap.sum_apply]
  show _ = (Submodule.mkQ _) (∑ s, a s * monomial s.1 1)
  rw [map_sum]
  rfl

/-- Every family of classes `cₛ` lifts to polynomials `aₛ`, and `sumMulMonomial` is then
the class of `∑ aₛ xˢ`. -/
private theorem exists_eq_mk_and_sumMulMonomial_eq_mk (n : ℕ)
    (c : degreeMonomials r n → MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A) :
    ∃ a : degreeMonomials r n → MvPolynomial (Fin r) A,
      c = (fun s => Submodule.Quotient.mk (a s)) ∧
        sumMulMonomial A r n c = Submodule.Quotient.mk (∑ s, a s * monomial s.1 1) := by
  choose a ha using fun s => Submodule.Quotient.mk_surjective _ (c s)
  obtain rfl : c = fun s => Submodule.Quotient.mk (a s) := funext fun s => (ha s).symm
  exact ⟨a, rfl, sumMulMonomial_mk n a⟩

/-- The map `(cₛ) ↦ ∑ cₛ xˢ` from `(R/(x))^{monomials of degree n}` to `R/(x)ⁿ⁺¹` is injective. -/
theorem sumMulMonomial_injective (n : ℕ) : Function.Injective (sumMulMonomial A r n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  obtain ⟨a, hc', hc''⟩ := exists_eq_mk_and_sumMulMonomial_eq_mk n c
  rw [hc'', Submodule.Quotient.mk_eq_zero] at hc
  funext s₀
  rw [hc', Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
  have hs₀ := mem_degreeMonomials.1 s₀.2
  have h := (mem_pow_idealOfVars_iff' (n + 1) _).1 hc s₀.1 (by omega)
  rw [coeff_sum, Fintype.sum_eq_single s₀] at h
  · rw [coeff_mul_monomial', ite_eq_left le_rfl, tsub_self, mul_one] at h
    exact mem_idealOfVars_of_coeff_zero h
  · intro s hs
    rw [coeff_mul_monomial']
    exact ite_eq_right fun hle => hs (Subtype.ext (eq_of_le_of_degree_eq hle
      (by rw [mem_degreeMonomials.1 s.2, hs₀])))

/-- The composite `(R/(x))^{monomials of degree n} ⟶ R/(x)ⁿ⁺¹ ⟶ R/(x)ⁿ` is zero. -/
theorem quotientPowSucc_sumMulMonomial (n : ℕ) :
    quotientPowSucc A r n ∘ₗ sumMulMonomial A r n = 0 := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨a, -, hc⟩ := exists_eq_mk_and_sumMulMonomial_eq_mk n c
  rw [LinearMap.comp_apply, hc, LinearMap.zero_apply]
  show (Submodule.Quotient.mk _ : _ ⧸ idealOfVars (Fin r) A ^ n) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.sum_mem _ fun s _ =>
    Ideal.mul_mem_left _ _ (monomial_mem_pow_idealOfVars (mem_degreeMonomials.1 s.2))

/-- The kernel of `R/(x)ⁿ⁺¹ ⟶ R/(x)ⁿ` is contained in the image of `sumMulMonomial`. -/
theorem ker_quotientPowSucc_le (n : ℕ) :
    LinearMap.ker (quotientPowSucc A r n) ≤ LinearMap.range (sumMulMonomial A r n) := by
  intro y hy
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  replace hy : (Submodule.Quotient.mk q : _ ⧸ idealOfVars (Fin r) A ^ n) = 0 := hy
  rw [Submodule.Quotient.mk_eq_zero] at hy
  refine ⟨fun s => Submodule.Quotient.mk (C (q.coeff s.1)), ?_⟩
  rw [sumMulMonomial_mk, Submodule.Quotient.eq]
  refine (mem_pow_idealOfVars_iff' (n + 1) _).2 fun t ht => ?_
  rw [coeff_sub, coeff_sum]
  simp only [C_mul_monomial, mul_one, coeff_monomial]
  by_cases htn : t.degree = n
  · rw [Fintype.sum_eq_single ⟨t, mem_degreeMonomials.2 htn⟩]
    · simp
    · exact fun s hs => ite_eq_right fun h => hs (Subtype.ext h)
  · rw [Finset.sum_eq_zero]
    · rw [(mem_pow_idealOfVars_iff' n q).1 hy t (by omega), sub_zero]
    · intro s _
      rw [ite_eq_right]
      intro h
      exact htn (h ▸ mem_degreeMonomials.1 s.2)

/-- For every module `N` over `R = A[x₁, …, x_r]` and every `p > r`, `Tor_p^R(R/(x), N) = 0`. -/
theorem isZero_tor_quotient_idealOfVars (N : ModuleCat.{u} (MvPolynomial (Fin r) A)) {p : ℕ}
    (hp : r < p) :
    IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin r) A)) p).obj
      (ModuleCat.of _ (MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A))).obj N) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := Module.subsingleton (MvPolynomial (Fin r) A)
      (((Tor' (ModuleCat.{u} (MvPolynomial (Fin r) A)) p).obj
        (ModuleCat.of _ (MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A))).obj N)
    exact ModuleCat.isZero_of_subsingleton _
  · have hf : Koszul.IsKoszulRegular (X : Fin r → MvPolynomial (Fin r) A) := by
      cases r with
      | zero =>
        intro i hi
        refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
        show IsZero (ModuleCat.of _ (⋀[MvPolynomial (Fin 0) A]^i
          (Fin 0 → MvPolynomial (Fin 0) A)))
        have : Subsingleton (⋀[MvPolynomial (Fin 0) A]^i (Fin 0 → MvPolynomial (Fin 0) A)) :=
          exteriorPower.subsingleton_of_span_eq_top_of_card_lt
            (Pi.basisFun (MvPolynomial (Fin 0) A) (Fin 0))
            (Pi.basisFun (MvPolynomial (Fin 0) A) (Fin 0)).span_eq i
            (by simpa using Nat.pos_of_ne_zero hi)
        exact ModuleCat.isZero_of_subsingleton _
      | succ m => exact isKoszulRegular_X m
    exact Koszul.isZero_tor_of_lt (X : Fin r → MvPolynomial (Fin r) A) hf N hp

/-- A finite direct sum of copies of `R/(x)` has vanishing `Tor_p(-, N)` for `p > r`. -/
theorem isZero_tor_pi_quotient_idealOfVars {J : Type} [Fintype J]
    (N : ModuleCat.{u} (MvPolynomial (Fin r) A)) {p : ℕ} (hp : r < p) :
    IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin r) A)) p).obj
      (ModuleCat.of _ (J → MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A))).obj N) := by
  let G := ((tensoringRight (ModuleCat.{u} (MvPolynomial (Fin r) A))).obj N).leftDerived p
  let f : J → ModuleCat.{u} (MvPolynomial (Fin r) A) :=
    fun _ => ModuleCat.of _ (MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A)
  show IsZero (G.obj (ModuleCat.of _ (∀ j, f j)))
  refine IsZero.of_iso ?_ (G.mapIso (ModuleCat.biproductIsoPi f)).symm
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← G.map_id, ← biproduct.total, G.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hz : IsZero (G.obj (f j)) := isZero_tor_quotient_idealOfVars N hp
  rw [G.map_comp, hz.eq_of_tgt (G.map (biproduct.π f j)) 0, zero_comp]

/-- `A[x₁, …, x_r]/(x₁, …, x_r)ⁿ` has Tor dimension at most `r` for all `n`: for every module `N`
over `R = A[x₁, …, x_r]` and every `p > r`, `Tor_p^R(R/(x₁, …, x_r)ⁿ, N) = 0`. -/
@[stacks 0GA5 "in the standard example, `A[x₁, …, x_r]/(x₁, …, x_r)ⁿ` has tor dimension at \
most `r` for all `n`"]
theorem isZero_tor_quotient_pow_idealOfVars (n : ℕ) (N : ModuleCat.{u} (MvPolynomial (Fin r) A))
    {p : ℕ} (hp : r < p) :
    IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin r) A)) p).obj
      (ModuleCat.of _ (MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A ^ n))).obj N) := by
  let G := ((tensoringRight (ModuleCat.{u} (MvPolynomial (Fin r) A))).obj N).leftDerived p
  induction n with
  | zero =>
    have : Subsingleton (MvPolynomial (Fin r) A ⧸ idealOfVars (Fin r) A ^ 0) := by
      rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.one_eq_top]
    show IsZero (G.obj _)
    exact G.map_isZero (ModuleCat.isZero_of_subsingleton _)
  | succ n ih =>
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    let S : ShortComplex (ModuleCat.{u} (MvPolynomial (Fin r) A)) :=
      ShortComplex.mk (ModuleCat.ofHom (sumMulMonomial A r n))
        (ModuleCat.ofHom (quotientPowSucc A r n))
        (ModuleCat.hom_ext (quotientPowSucc_sumMulMonomial n))
    have hS : S.ShortExact := .mk'
      ((ShortComplex.moduleCat_exact_iff_ker_sub_range S).2 (ker_quotientPowSucc_le n))
      ((ModuleCat.mono_iff_injective _).2 (sumMulMonomial_injective n))
      ((ModuleCat.epi_iff_surjective _).2
        (Submodule.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ n))))
    exact ((Stacks.Tor.Tor'_composableArrows_exact_first hS N q).exact 0).isZero_X₂
      ((isZero_tor_pi_quotient_idealOfVars N hp).eq_of_src _ _) (ih.eq_of_tgt _ _)

end Stacks.LocalCohomology.UniformityII

end
