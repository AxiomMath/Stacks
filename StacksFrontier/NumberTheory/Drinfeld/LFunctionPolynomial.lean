module

public import StacksFrontier.NumberTheory.Adeles.SwitchingEll
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionTraceCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyTracePowers

/-!
# Towards `L(X, ℱ_{ρ ⊗ χ}, T)` being a polynomial of degree `4g - 4`: the algebraic inputs

Let `X` be a smooth projective geometrically irreducible curve of genus `g` over a finite field
`k`, `ρ : π₁(X, x̄) → GL₂(E)` continuous and absolutely irreducible and `χ` a character of finite
order. Drinfeld's proof of Stacks Theorem 03VU uses that the L-function of `ℱ_{ρ ⊗ χ}` is a
polynomial of degree `4g - 4`. Its proof has three steps:

1. rationality, `L = ∏ᵢ det(1 - π^* T | Hⁱ_c(X_k̄, ℱ))^{(-1)^{i+1}}` (Tag 03V0);
2. `H⁰ = H²_c = 0`: by Tags 03VL and 03VK these are the invariants and the coinvariants (twisted)
   of `π₁(X_k̄)` acting on `E²`, and both vanish because `π₁(X_k̄)` is normal in `π₁(X)` with
   abelian quotient `Ẑ` while `ρ ⊗ χ` is absolutely irreducible of rank two;
3. `dim H¹ = -χ(X_k̄, ℱ) = 2 (2g - 2)`.

This file proves the algebraic parts of steps 1 and 2:

* the group-theoretic vanishing of step 2. A two-dimensional absolutely irreducible
  representation admits no stable subspace other than `0` and `E²`, and its image does not
  commute. So a normal subgroup `N` containing every commutator has no nonzero invariant
  vector, and the vectors `ρ(n) v - v`, `n ∈ N`, span `E²` (the coinvariants vanish). Twisting
  by a character keeps absolute irreducibility.
* the final algebra of the argument: an alternating product
  `∏ᵢ det(1 - φᵢ T | Vᵢ)^{(-1)^{i+1}}` whose modules vanish outside degree `1` is the polynomial
  `det(1 - φ₁ T | V₁)`. It has constant term `1`, degree at most `rank V₁`, and coefficient
  `(-1)^{rank V₁} det φ₁` in degree `rank V₁`. So an L-function with such a cohomological
  expression is a polynomial of degree at most `rank V₁`. If `φ₁` is invertible over a field, the
  degree is exactly `rank V₁`.

## Main results

* `Stacks.Drinfeld.IsAbsolutelyIrreducible.eq_bot_or_eq_top`: a stable subspace is `0` or `E²`.
* `Stacks.Drinfeld.IsAbsolutelyIrreducible.not_forall_commute`: the image does not commute.
* `Stacks.Drinfeld.IsAbsolutelyIrreducible.of_smul`: twisting by a character.
* `Stacks.Drinfeld.IsAbsolutelyIrreducible.eq_zero_of_forall_mulVec_eq`: no invariants under a
  normal subgroup containing the commutators.
* `Stacks.Drinfeld.IsAbsolutelyIrreducible.span_mulVec_sub_eq_top`: no coinvariants under such a
  subgroup.
* `Stacks.Drinfeld.exists_polynomial_eq_gradedCharSeries`: the alternating product with
  cohomology only in degree `1` is a polynomial of degree at most `rank V₁` with constant
  term `1`.
* `Stacks.Drinfeld.exists_polynomial_eq_lFunction`: the same for an L-function with such a
  cohomological expression.

## References

* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
-/

@[expose] public noncomputable section

open Stacks.Adeles Stacks.EtaleCohomology Matrix

universe u

namespace Stacks.Drinfeld

/-! ### Absolutely irreducible two-dimensional representations -/

section Irreducible

variable {Γ : Type*} [Group Γ] {E : Type*} [Field E] {ρ : Γ →* GL (Fin 2) E}

/-- **An absolutely irreducible representation has no stable subspace other than `0` and `E²`.**
The matrices stabilizing a subspace `W` form a subspace of `M₂(E)` containing the image of `ρ`,
hence all of `M₂(E)`, and a matrix sends a given nonzero vector of `W` to any vector. -/
public theorem IsAbsolutelyIrreducible.eq_bot_or_eq_top (h : IsAbsolutelyIrreducible ρ)
    (W : Submodule E (Fin 2 → E))
    (hW : ∀ g, ∀ v ∈ W, (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  let S : Submodule E (Matrix (Fin 2) (Fin 2) E) :=
    { carrier := {A | ∀ v ∈ W, A *ᵥ v ∈ W}
      add_mem' := fun {A B} hA hB v hv => by
        rw [Matrix.add_mulVec]
        exact W.add_mem (hA v hv) (hB v hv)
      zero_mem' := fun v _ => by
        rw [Matrix.zero_mulVec]
        exact W.zero_mem
      smul_mem' := fun c A hA v hv => by
        rw [Matrix.smul_mulVec]
        exact W.smul_mem c (hA v hv) }
  have hS : Submodule.span E (Set.range fun g => (ρ g : Matrix (Fin 2) (Fin 2) E)) ≤ S :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hW)
  rw [show Submodule.span E _ = ⊤ from h] at hS
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := Function.ne_iff.1 hw0
  refine eq_top_iff.2 fun v _ => ?_
  let A : Matrix (Fin 2) (Fin 2) E := Matrix.of fun a b => if b = i then v a / w i else 0
  have hA : A *ᵥ w = v := by
    funext a
    simp only [A, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact div_mul_cancel₀ (v a) hi
  simpa [hA] using (hS Submodule.mem_top : A ∈ S) w hw

/-- **The image of an absolutely irreducible representation does not commute**: otherwise the
span of the image, which is `M₂(E)`, would be commutative. -/
public theorem IsAbsolutelyIrreducible.not_forall_commute (h : IsAbsolutelyIrreducible ρ) :
    ¬ ∀ a b : Γ, Commute (ρ a : Matrix (Fin 2) (Fin 2) E) (ρ b) := by
  intro hc
  set s := Set.range fun g => (ρ g : Matrix (Fin 2) (Fin 2) E)
  have hspan : Submodule.span E s = ⊤ := h
  -- if the image lies in a centralizer, so does the whole span, which is everything
  have key : ∀ T : Set (Matrix (Fin 2) (Fin 2) E),
      (∀ a ∈ s, a ∈ Subalgebra.centralizer E T) → ∀ A, A ∈ Subalgebra.centralizer E T := by
    intro T hT A
    have hle : Submodule.span E s ≤ Subalgebra.toSubmodule (Subalgebra.centralizer E T) :=
      Submodule.span_le.2 hT
    rw [hspan] at hle
    exact hle Submodule.mem_top
  -- every matrix commutes with the image
  have h1 := key s fun a ⟨x, hx⟩ => (Subalgebra.mem_centralizer_iff E).2 fun b ⟨y, hy⟩ => by
    subst hx hy
    exact (hc y x).eq
  -- hence every matrix commutes with every matrix
  have h2 := key Set.univ fun a ha => (Subalgebra.mem_centralizer_iff E).2 fun A _ =>
    ((Subalgebra.mem_centralizer_iff E).1 (h1 A) _ ha).symm
  have h3 := (Subalgebra.mem_centralizer_iff E).1 (h2 !![(0 : E), 1; 0, 0])
    !![(0 : E), 0; 1, 0] (Set.mem_univ _)
  have h4 := congrFun (congrFun h3 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h4

/-- **Twisting by a character keeps absolute irreducibility.** If `ρ'(g) = χ(g) ρ(g)` for a
character `χ : Γ → Eˣ` (for instance `ρ' = Stacks.EtaleCohomology.characterTwist ρ χ`, by
`Stacks.EtaleCohomology.characterTwist_val`), then `ρ(g) = χ(g)⁻¹ ρ'(g)`, so the span of the image
of `ρ` lies in that of `ρ'`. -/
public theorem IsAbsolutelyIrreducible.of_smul (h : IsAbsolutelyIrreducible ρ) (χ : Γ →* Eˣ)
    {ρ' : Γ →* GL (Fin 2) E}
    (hρ' : ∀ g, (ρ' g : Matrix (Fin 2) (Fin 2) E) = (χ g : E) • (ρ g : Matrix (Fin 2) (Fin 2) E)) :
    IsAbsolutelyIrreducible ρ' := by
  unfold IsAbsolutelyIrreducible at h ⊢
  rw [eq_top_iff, ← h]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  have hg : (ρ g : Matrix (Fin 2) (Fin 2) E) =
      ((χ g)⁻¹ : Eˣ).val • (ρ' g : Matrix (Fin 2) (Fin 2) E) := by
    rw [hρ', smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  change (ρ g : Matrix (Fin 2) (Fin 2) E) ∈ Submodule.span E _
  rw [hg]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

/-- Acting by `ρ a` after `ρ b` only depends on the product `a * b`. -/
private theorem mulVec_mulVec_eq_of_mul_eq (ρ : Γ →* GL (Fin 2) E) {a b c d : Γ}
    (h : a * b = c * d) (v : Fin 2 → E) :
    (ρ a : Matrix (Fin 2) (Fin 2) E) *ᵥ (ρ b : Matrix (Fin 2) (Fin 2) E) *ᵥ v =
      (ρ c : Matrix (Fin 2) (Fin 2) E) *ᵥ (ρ d : Matrix (Fin 2) (Fin 2) E) *ᵥ v := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul,
    ← map_mul, h]

/-- If a normal subgroup containing every commutator acts trivially on `E²`, the image of `ρ`
commutes; so for an absolutely irreducible `ρ` this does not happen. -/
public theorem IsAbsolutelyIrreducible.not_forall_mem_mulVec_eq (h : IsAbsolutelyIrreducible ρ)
    (N : Subgroup Γ) (hN : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ N) :
    ¬ ∀ n ∈ N, ∀ v : Fin 2 → E, (ρ n : Matrix (Fin 2) (Fin 2) E) *ᵥ v = v := by
  intro htriv
  refine IsAbsolutelyIrreducible.not_forall_commute h fun a b => ?_
  have h1 : ρ (a * b * a⁻¹ * b⁻¹) = 1 := by
    refine Units.ext ?_
    rw [Units.val_one]
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
    exact htriv _ (hN a b) v
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact congrArg Units.val h1

/-- **No invariants.** Let `N` be a normal subgroup containing every commutator (for instance
`π₁(X_k̄) ⊆ π₁(X)`, with abelian quotient `Gal(k̄/k)`). If `ρ` is absolutely irreducible of rank
two, then `(E²)^N = 0`: the invariants form a stable subspace, which is not all of `E²`, since
then the image of `ρ` would commute. -/
public theorem IsAbsolutelyIrreducible.eq_zero_of_forall_mulVec_eq
    (h : IsAbsolutelyIrreducible ρ) (N : Subgroup Γ) [N.Normal]
    (hN : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ N)
    {v : Fin 2 → E} (hv : ∀ n ∈ N, (ρ n : Matrix (Fin 2) (Fin 2) E) *ᵥ v = v) : v = 0 := by
  let W : Submodule E (Fin 2 → E) :=
    { carrier := {v | ∀ n ∈ N, (ρ n : Matrix (Fin 2) (Fin 2) E) *ᵥ v = v}
      add_mem' := fun {v w} hv hw n hn => by rw [Matrix.mulVec_add, hv n hn, hw n hn]
      zero_mem' := fun n _ => Matrix.mulVec_zero _
      smul_mem' := fun c v hv n hn => by rw [Matrix.mulVec_smul, hv n hn] }
  have hstab : ∀ g, ∀ v ∈ W, (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ W := by
    intro g v hv n hn
    have hconj : g⁻¹ * n * g ∈ N := by
      simpa using Subgroup.Normal.conj_mem inferInstance n hn g⁻¹
    change (ρ n : Matrix (Fin 2) (Fin 2) E) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ v) =
      (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ v
    rw [mulVec_mulVec_eq_of_mul_eq ρ (c := g) (d := g⁻¹ * n * g) (by group), hv _ hconj]
  rcases IsAbsolutelyIrreducible.eq_bot_or_eq_top h W hstab with hW | hW
  · have hvW : v ∈ W := hv
    rwa [hW, Submodule.mem_bot] at hvW
  · exact absurd (fun n hn w => (show w ∈ W from hW ▸ Submodule.mem_top) n hn)
      (IsAbsolutelyIrreducible.not_forall_mem_mulVec_eq h N hN)

/-- **No coinvariants.** For `N` as in `eq_zero_of_forall_mulVec_eq`, the vectors
`ρ(n) v - v` with `n ∈ N` span `E²`, that is `(E²)_N = 0`: their span is a stable subspace, and
it is not `0`, since then `N` would act trivially. -/
public theorem IsAbsolutelyIrreducible.span_mulVec_sub_eq_top
    (h : IsAbsolutelyIrreducible ρ) (N : Subgroup Γ) [N.Normal]
    (hN : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ N) :
    Submodule.span E
      {w : Fin 2 → E | ∃ n ∈ N, ∃ v, w = (ρ n : Matrix (Fin 2) (Fin 2) E) *ᵥ v - v} = ⊤ := by
  set U := Submodule.span E
    {w : Fin 2 → E | ∃ n ∈ N, ∃ v, w = (ρ n : Matrix (Fin 2) (Fin 2) E) *ᵥ v - v}
  have hstab : ∀ g, ∀ u ∈ U, (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ u ∈ U := by
    intro g u hu
    induction hu using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨n, hn, v, rfl⟩ := hw
      refine Submodule.subset_span ⟨g * n * g⁻¹, Subgroup.Normal.conj_mem inferInstance n hn g,
        (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ v, ?_⟩
      rw [Matrix.mulVec_sub, mulVec_mulVec_eq_of_mul_eq ρ (c := g * n * g⁻¹) (d := g) (by group)]
    | zero =>
      rw [Matrix.mulVec_zero]
      exact U.zero_mem
    | add x y _ _ hx hy =>
      rw [Matrix.mulVec_add]
      exact U.add_mem hx hy
    | smul c x _ hx =>
      rw [Matrix.mulVec_smul]
      exact U.smul_mem c hx
  rcases IsAbsolutelyIrreducible.eq_bot_or_eq_top h U hstab with hU | hU
  · refine absurd (fun n hn v => ?_) (IsAbsolutelyIrreducible.not_forall_mem_mulVec_eq h N hN)
    have hmem : (ρ n : Matrix (Fin 2) (Fin 2) E) *ᵥ v - v ∈ U :=
      Submodule.subset_span ⟨n, hn, v, rfl⟩
    rwa [hU, Submodule.mem_bot, sub_eq_zero] at hmem
  · exact hU

end Irreducible

/-! ### An alternating product with cohomology only in degree one -/

section Polynomial

variable {Λ : Type*} [CommRing Λ] [Nontrivial Λ] (V : ℤ → Type*) [∀ i, AddCommGroup (V i)]
  [∀ i, Module Λ (V i)] [∀ i, Module.Finite Λ (V i)] [∀ i, Module.Free Λ (V i)]
  (φ : ∀ i, V i →ₗ[Λ] V i)

/-- If the modules `Vᵢ` vanish outside degree `1`, the alternating product
`∏ᵢ det(1 - φᵢ T | Vᵢ)^{(-1)^{i+1}}` is `det(1 - φ₁ T | V₁)`. -/
public theorem gradedCharSeries_eq_charPowerSeries_one
    (hV : ∀ i ≠ 1, Subsingleton (V i)) :
    gradedCharSeries V φ = charPowerSeries (φ 1) 1 := by
  rw [gradedCharSeries_eq_prod V φ {1} fun i hi => hV i (Finset.notMem_singleton.1 hi),
    Finset.prod_singleton, gradedCharFactor, ite_eq_right (by decide)]

/-- **An alternating product with cohomology only in degree `1` is a polynomial.** If the finite
free modules `Vᵢ` vanish outside degree `1`, then `∏ᵢ det(1 - φᵢ T | Vᵢ)^{(-1)^{i+1}}` is the image
in `Λ⟦T⟧` of the polynomial `det(1 - φ₁ T | V₁)`. This polynomial has constant term `1`, degree at
most `r = rank V₁`, and coefficient `(-1)^r det φ₁` in degree `r`. -/
public theorem exists_polynomial_eq_gradedCharSeries (hV : ∀ i ≠ 1, Subsingleton (V i)) :
    ∃ P : Polynomial Λ, (P : PowerSeries Λ) = gradedCharSeries V φ ∧
      P.natDegree ≤ Module.finrank Λ (V 1) ∧ P.coeff 0 = 1 ∧
      P.coeff (Module.finrank Λ (V 1)) =
        (-1) ^ Module.finrank Λ (V 1) * LinearMap.det (φ 1) := by
  classical
  set b := Module.finBasis Λ (V 1)
  set A := LinearMap.toMatrix b b (φ 1)
  refine ⟨A.charpolyRev, ?_, ?_, ?_, ?_⟩
  · rw [gradedCharSeries_eq_charPowerSeries_one V φ hV, charPowerSeries_eq_localCharSeries b,
      ← localCharPolynomial_one_eq_charpolyRev, coe_localCharPolynomial]
  · rw [← localCharPolynomial_one_eq_charpolyRev]
    simpa using natDegree_localCharPolynomial_le A 1
  · rw [← localCharPolynomial_one_eq_charpolyRev]
    exact coeff_zero_localCharPolynomial A one_ne_zero
  · rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, Polynomial.revAt_le le_rfl, Nat.sub_self, ← LinearMap.det_toMatrix b,
      Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc,
      ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **An L-function with cohomology only in degree `1` is a polynomial.** If a family of
Frobenius matrices on a scheme of finite type over a finite field has
`L(X, ℱ) = ∏ᵢ det(1 - φᵢ T | Vᵢ)^{(-1)^{i+1}}`, with the finite free `Vᵢ` vanishing outside
degree `1`, then `L(X, ℱ)` is a polynomial with constant term `1`, of degree at most `rank V₁`,
with coefficient `(-1)^{rank V₁} det φ₁` in degree `rank V₁`. This is the last step of the proof
that `L(X, ℱ_{ρ ⊗ χ}, T)` is a polynomial of degree `4g - 4`, with `Vᵢ = Hⁱ_c(X_k̄, ℱ_{ρ ⊗ χ})`. -/
public theorem exists_polynomial_eq_lFunction {k : Type u} [Field k] [Finite k]
    {X : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ AlgebraicGeometry.Spec (.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
    (D : FrobeniusMatrices f Λ) (hD : D.lFunction = gradedCharSeries V φ)
    (hV : ∀ i ≠ 1, Subsingleton (V i)) :
    ∃ P : Polynomial Λ, (P : PowerSeries Λ) = D.lFunction ∧
      P.natDegree ≤ Module.finrank Λ (V 1) ∧ P.coeff 0 = 1 ∧
      P.coeff (Module.finrank Λ (V 1)) =
        (-1) ^ Module.finrank Λ (V 1) * LinearMap.det (φ 1) := by
  rw [hD]
  exact exists_polynomial_eq_gradedCharSeries V φ hV

/-- Over a field, if `φ₁` is invertible the polynomial of `exists_polynomial_eq_gradedCharSeries`
has degree exactly `rank V₁`. -/
public theorem exists_polynomial_eq_gradedCharSeries_natDegree_eq {K : Type*} [Field K]
    (V : ℤ → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (φ : ∀ i, V i →ₗ[K] V i)
    (hV : ∀ i ≠ 1, Subsingleton (V i)) (hφ : LinearMap.det (φ 1) ≠ 0) :
    ∃ P : Polynomial K, (P : PowerSeries K) = gradedCharSeries V φ ∧
      P.natDegree = Module.finrank K (V 1) ∧ P.coeff 0 = 1 := by
  obtain ⟨P, hP, hdeg, h0, htop⟩ := exists_polynomial_eq_gradedCharSeries V φ hV
  refine ⟨P, hP, le_antisymm hdeg (Polynomial.le_natDegree_of_ne_zero ?_), h0⟩
  rw [htop]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hφ

end Polynomial

end Stacks.Drinfeld
