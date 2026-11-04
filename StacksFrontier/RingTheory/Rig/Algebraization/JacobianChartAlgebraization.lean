module

public import StacksFrontier.RingTheory.AdicCompletion.IteratedMvPolynomial
public import StacksFrontier.RingTheory.Rig.Algebraization.JacobianCriterion
public import StacksFrontier.RingTheory.Rig.LiftingGeneral
public import StacksFrontier.RingTheory.Rig.RigEtaleSurjection

/-!
# The Jacobian criterion for algebraization (Stacks 0GAW)

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` an `I`-adically complete `A`-algebra of
finite type modulo `I`, presented as `B = A⟨x₁, …, x_r⟩/J`.  Suppose given `b`, an integer
`m ≤ r` and `f₁, …, f_m ∈ J` with `V(b) ⊆ V(IB)`, with the Jacobian determinant
`Δ = det(∂fⱼ/∂xᵢ)_{i, j ≤ m}` dividing `b`, and with `bJ ⊆ (f₁, …, f_m) + J²`.  Then `B` is the
`I`-adic completion of a finite type `A`-algebra.

## The route

As in the source, `B` is compared with the completion of the finite type algebra
`C = A[z₁, …, z_t, x₁, …, x_r]/(z₁Δ' - a₁^{c₁}, …, z_tΔ' - a_t^{c₁}, f'₁, …, f'_m)` of Stacks
0GAV, built from polynomial approximations `f'ⱼ` of the `fⱼ` and generators `a₁, …, a_t` of
`I`.  Two steps differ from the source in method, not in what they prove.

* **The lift `C^∧ → B`.**  The source lifts the approximate map `C^∧ → B/IⁿB` by the uniform
  lifting result Stacks 0GAQ, which rests on the local cohomology of Section 0GA6.  Here the
  lift is produced by Newton's method (`Rig.exists_algHom_newton`): the relations of `C` have
  Jacobian determinant `Δ'^{t+1}` with respect to `z₁, …, z_t, x₁, …, x_m`, and the relations
  `zₖΔ' - aₖ^{c₁}` themselves force a fixed power of `I` into `Δ'B` at every approximate
  solution (Nakayama), so the linearized equations are solved exactly at every step.
* **The comparison of the two `H⁰`'s.**  The source inverts `b` and observes that
  `H⁰(NL^∧_{C^∧/A}) ⊗ B[1/b]` and `H⁰(NL^∧_{B/A}) ⊗ B[1/b]` are both free of rank `r - m`.
  Here nothing is inverted: Cramer's rule exhibits both modules as free of rank `r - m` up to
  explicit scalars dividing a power of `b`, the degree-`0` maps of Stacks 0GAE compare them,
  and an adjugate computation (`Rig.smul_mem_of_rank_comparison`) gives the annihilation with
  an explicit exponent.  Together with the rig-smoothness of `B` this is the annihilation of
  `Ker(φ)/Ker(φ)²` that the source extracts from the six-term sequence of Stacks 0ALM.

## Main results

* `Rig.exists_newton_correction` and `Rig.exists_algHom_newton` — Newton's method for a system
  of restricted power series whose Jacobian determinant at approximate solutions divides a
  fixed power of `I`.
* `Rig.smul_mem_of_rank_comparison` — two modules free of the same rank up to scalars, related
  by a split surjection of relations, have relation modules agreeing up to a product of those
  scalars.
* `Rig.det_smul_sub_tailInclusion_cramerTail` and
  `Rig.det_mul_smul_eq_zero_of_tailInclusion_mem` — Cramer's rule splitting `R^n` into the
  first `m` coordinates and the last `n - m`.
* `Rig.exists_degreeZero_maps` — the degree-`0` maps of the homotopy equivalence of Stacks 0GAE.
* `Rig.exists_pow_smul_cotangent_eq_bot_of_jacobianChart` — the conormal annihilation for a
  surjection from the completion of the algebra of Stacks 0GAV onto `B`.
* `Rig.exists_finiteType_adicCompletion_algEquiv_of_jacobianChart` — **Stacks 0GAW**.

## References

* [Stacks Project, Tag 0GAW](https://stacks.math.columbia.edu/tag/0GAW)
* [Stacks Project, Tag 0GAV](https://stacks.math.columbia.edu/tag/0GAV)
* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 0ALR](https://stacks.math.columbia.edu/tag/0ALR)
* [Stacks Project, Tag 0GAE](https://stacks.math.columbia.edu/tag/0GAE)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

namespace Rig

universe u v

attribute [local instance] HasDerivedCategory.standard

section PolynomialDerivative

open RestrictedPowerSeries

variable {A : Type u} [CommRing A] (I : Ideal A) {σ : Type*}

/-- Formal partial differentiation of restricted power series restricts, on polynomials, to
the formal partial differentiation of polynomials. -/
public theorem partialDerivative_polynomialAlgHom (i : σ) (p : MvPolynomial σ A) :
    partialDerivative I i (polynomialAlgHom I σ p) =
      polynomialAlgHom I σ (MvPolynomial.pderiv i p) := by
  apply Subtype.ext
  funext n
  show MvPolynomial.pderiv i (MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p) =
    MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) (MvPolynomial.pderiv i p)
  exact MvPolynomial.pderiv_map

end PolynomialDerivative

section Newton

open RestrictedPowerSeries

/-- If a power of `J` lies in `(x)`, a suitable multiple of that power lies in `(xᵏ)`. -/
private theorem pow_mul_le_span_singleton_pow {R : Type*} [CommRing R] {J : Ideal R} {x : R}
    {a : ℕ} (h : J ^ a ≤ Ideal.span {x}) (k : ℕ) : J ^ (a * k) ≤ Ideal.span {x ^ k} := by
  rw [pow_mul, ← Ideal.span_singleton_pow]
  exact Ideal.pow_right_mono h k

variable {A : Type u} [CommRing A] (I : Ideal A) {B : Type*} [CommRing B] [Algebra A B]
  {N M : ℕ}

/-- **One Newton step, with an exact correction on the generators.**  Let
`F₁, …, F_M ∈ A⟨x₁, …, x_N⟩`, let `s : Fin M → Fin N` select `M` of the variables, let
`ψ : A⟨x⟩ → B` be an `A`-algebra map with `ψ(Fⱼ) ∈ IᵐB`, and suppose the determinant `d` of
the matrix `(ψ(∂Fⱼ/∂x_{s i}))` satisfies `IᵉB ⊆ dB` with `2e ≤ m`.  Then there are
`δ₁, …, δ_N ∈ I^{m-2e}B` with `ψ(g) - ∑ᵢ ψ(∂g/∂xᵢ) δᵢ ∈ I^{2m-2e}B` for every `g` in the
ideal generated by the `Fⱼ`.

Writing `ψ(F) = d²G` with `G ∈ I^{m-2e}B`, the correction is `δ = adj(Qᵀ)(dG)` placed in the
selected coordinates, which solves the linearized system on the generators exactly. -/
public theorem exists_newton_correction (ψ : RestrictedPowerSeries I (Fin N) →ₐ[A] B)
    (F : Fin M → RestrictedPowerSeries I (Fin N)) (s : Fin M → Fin N) (e m : ℕ)
    (hm : 2 * e ≤ m)
    (hdet : (I.map (algebraMap A B)) ^ e ≤
      Ideal.span {(Matrix.of fun i j ↦ ψ (partialDerivative I (s i) (F j))).det})
    (hF : ∀ j, ψ (F j) ∈ (I.map (algebraMap A B)) ^ m) :
    ∃ δ : Fin N → B, (∀ i, δ i ∈ (I.map (algebraMap A B)) ^ (m - 2 * e)) ∧
      ∀ g ∈ Ideal.span (Set.range F),
        ψ g - ∑ i, ψ (partialDerivative I i g) * δ i ∈
          (I.map (algebraMap A B)) ^ (2 * m - 2 * e) := by
  classical
  set L := I.map (algebraMap A B) with hL
  set Q : Matrix (Fin M) (Fin M) B := Matrix.of fun i j ↦ ψ (partialDerivative I (s i) (F j))
    with hQ
  set d := Q.det with hd
  have hsq : L ^ (2 * e) ≤ Ideal.span {d ^ 2} := by
    rw [mul_comm]
    exact pow_mul_le_span_singleton_pow hdet 2
  have hG : ∀ j, ∃ G ∈ L ^ (m - 2 * e), d ^ 2 * G = ψ (F j) := by
    intro j
    have h := hF j
    rw [show m = 2 * e + (m - 2 * e) by omega, pow_add] at h
    exact Ideal.mem_span_singleton_mul.mp (Ideal.mul_mono_left hsq h)
  choose G hGmem hGeq using hG
  set η : Fin M → B := Q.transpose.adjugate.mulVec (fun j ↦ d * G j) with hη
  have hQη : ∀ j, ∑ i, ψ (partialDerivative I (s i) (F j)) * η i = ψ (F j) := by
    intro j
    have h : Q.transpose.mulVec η = d • fun j ↦ d * G j := by
      rw [hη, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.det_transpose,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have hj := congrFun h j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hQ, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul] at hj
    rw [hj, ← hGeq j]
    ring
  set δ : Fin N → B := fun x ↦ ∑ i, if s i = x then η i else 0 with hδ
  have hδsum : ∀ h : RestrictedPowerSeries I (Fin N),
      ∑ x, ψ (partialDerivative I x h) * δ x =
        ∑ i, ψ (partialDerivative I (s i) h) * η i := by
    intro h
    simp only [hδ, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp
  have hηmem : ∀ i, η i ∈ L ^ (m - 2 * e) := by
    intro i
    simp only [hη, Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hGmem j))
  have hδmem : ∀ x, δ x ∈ L ^ (m - 2 * e) := fun x ↦ Ideal.sum_mem _ fun i _ ↦ by
    split_ifs
    · exact hηmem i
    · exact zero_mem _
  refine ⟨δ, hδmem, ?_⟩
  intro g hg
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
  have hderiv : ∀ x, partialDerivative I x (∑ j, c j * F j) =
      ∑ j, (c j * partialDerivative I x (F j) + F j * partialDerivative I x (c j)) := by
    intro x
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ partialDerivative_mul I x (c j) (F j)
  have hexp : ψ (∑ j, c j * F j) -
      ∑ x, ψ (partialDerivative I x (∑ j, c j * F j)) * δ x =
        -∑ j, ψ (F j) * ∑ x, ψ (partialDerivative I x (c j)) * δ x := by
    have hsplit : ∑ x, ψ (partialDerivative I x (∑ j, c j * F j)) * δ x =
        ∑ j, ψ (c j) * ∑ x, ψ (partialDerivative I x (F j)) * δ x +
          ∑ j, ψ (F j) * ∑ x, ψ (partialDerivative I x (c j)) * δ x := by
      simp only [hderiv, map_sum, map_add, map_mul, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact congrArg₂ (· + ·) Finset.sum_comm Finset.sum_comm
    rw [hsplit]
    simp only [hδsum, hQη, map_sum, map_mul]
    ring
  rw [hexp]
  refine neg_mem (Ideal.sum_mem _ fun j _ ↦ ?_)
  rw [show 2 * m - 2 * e = m + (m - 2 * e) by omega, pow_add]
  exact Ideal.mul_mem_mul (hF j) (Ideal.sum_mem _ fun x _ ↦ Ideal.mul_mem_left _ _ (hδmem x))

variable [IsAdicComplete (I.map (algebraMap A B)) B]

/-- **Newton's method in an adically complete algebra.**  Let `F₁, …, F_M ∈ A⟨x₁, …, x_N⟩`
and `s : Fin M → Fin N` select `M` variables, and suppose that for every `A`-algebra map
`ψ : A⟨x⟩ → B` with `ψ(Fⱼ) ∈ IᵐB` for some `m > e` the Jacobian determinant
`d = det(ψ(∂Fⱼ/∂x_{s i}))` satisfies `IᵉB ⊆ dB`.  Then every continuous `ψ₀` with
`ψ₀(Fⱼ) ∈ IⁿB`, `n > 4e`, is congruent modulo `I^{n-2e}` to an `A`-algebra map `φ` killing
every `Fⱼ`.

This is the tool replacing, in the proof of Stacks 0GAW, the uniform lifting of Stacks 0GAQ:
for the algebra of Stacks 0GAV the Jacobian determinant is controlled by the equations
themselves, so no obstruction theory is needed. -/
public theorem exists_algHom_newton (hI : I.FG)
    (F : Fin M → RestrictedPowerSeries I (Fin N)) (s : Fin M → Fin N) (e : ℕ)
    (hdet : ∀ (ψ : RestrictedPowerSeries I (Fin N) →ₐ[A] B) (m : ℕ), e < m →
      (∀ j, ψ (F j) ∈ (I.map (algebraMap A B)) ^ m) →
      (I.map (algebraMap A B)) ^ e ≤
        Ideal.span {(Matrix.of fun i j ↦ ψ (partialDerivative I (s i) (F j))).det})
    (n : ℕ) (hn : 4 * e < n) (ψ₀ : RestrictedPowerSeries I (Fin N) →ₐ[A] B)
    (hψ₀ : @Continuous _ _ (limitTopology I (Fin N))
      ((I.map (algebraMap A B)).adicTopology) ψ₀)
    (h0 : ∀ j, ψ₀ (F j) ∈ (I.map (algebraMap A B)) ^ n) :
    ∃ φ : RestrictedPowerSeries I (Fin N) →ₐ[A] B,
      (∀ g ∈ Ideal.span (Set.range F), φ g = 0) ∧
        ∀ g, φ g - ψ₀ g ∈ (I.map (algebraMap A B)) ^ (n - 2 * e) := by
  have hspan : ∀ (ψ : RestrictedPowerSeries I (Fin N) →ₐ[A] B) (m : ℕ),
      (∀ j, ψ (F j) ∈ (I.map (algebraMap A B)) ^ m) →
      ∀ g ∈ Ideal.span (Set.range F), ψ g ∈ (I.map (algebraMap A B)) ^ m := by
    intro ψ m hψ g hg
    have hle : Ideal.span (Set.range F) ≤ ((I.map (algebraMap A B)) ^ m).comap ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hψ j
    exact hle hg
  refine exists_limit_algHom (I.map (algebraMap A B)) (Ideal.span (Set.range F))
    (fun f ↦ @Continuous _ _ (limitTopology I (Fin N))
      ((I.map (algebraMap A B)).adicTopology) f) (2 * e) n (by omega) ?_ ψ₀ hψ₀
    (hspan ψ₀ n h0)
  intro m ψ hm hcont hJ
  have hF : ∀ j, ψ (F j) ∈ (I.map (algebraMap A B)) ^ m :=
    fun j ↦ hJ _ (Ideal.subset_span ⟨j, rfl⟩)
  obtain ⟨δ, hδ, hfac⟩ := exists_newton_correction I ψ F s e m (by omega)
    (hdet ψ m (by omega) hF) hF
  obtain ⟨ψ', hψ'c, hψ'J, hψ'd⟩ := exists_perturbed_algHom_of_obstruction_factors I hI
    (Ideal.span (Set.range F)) (m - 2 * e) ψ hcont δ hδ
    (fun g hg ↦ Ideal.pow_le_pow_right (by omega) (hfac g hg))
  exact ⟨ψ', hψ'c, hψ'J, hψ'd⟩

end Newton

section RankComparison

variable {R : Type*} [CommRing R] {N N₀ : Type*} [AddCommGroup N] [Module R N]
  [AddCommGroup N₀] [Module R N₀] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Comparing two modules which are free of the same rank up to a scalar.**

Let `N`, `N₀` be modules with submodules `V ≤ W ≤ N` and `W₀ ≤ N₀`, and let `α : N → N₀`,
`β : N₀ → N` be linear maps with `α(W) ⊆ W₀` and `αβ ≡ id` modulo `W₀`.  Suppose that `N₀/W₀`
and `N/V` are both free on `κ` up to a scalar: every element times `s₀` (resp. `s`) is
congruent to one coming from `R^κ` along `ι₀` (resp. `ι`), and `ι₀` is injective modulo `W₀`
up to the scalar `t₀`.  Then `W/V` is killed by `(t₀s₀s)^{#κ}s`.

This is the comparison of the source's proof of Stacks 0GAW, "both are free modules of rank
`r - m` after inverting `b`", carried out without inverting anything: the composite
`θ = L₀ ∘ α ∘ ι` is an endomorphism of `R^κ` which `θ' = L ∘ β ∘ ι₀` inverts up to `t₀s₀s`,
so the adjugate of `t₀θ` inverts it up to `(t₀s₀s)^{#κ}`. -/
public theorem smul_mem_of_rank_comparison
    (V W : Submodule R N) (W₀ : Submodule R N₀) (hVW : V ≤ W)
    (ι : (κ → R) →ₗ[R] N) (L : N →ₗ[R] (κ → R))
    (ι₀ : (κ → R) →ₗ[R] N₀) (L₀ : N₀ →ₗ[R] (κ → R))
    (α : N →ₗ[R] N₀) (β : N₀ →ₗ[R] N) (s s₀ t₀ : R)
    (hV : ∀ w, s • w - ι (L w) ∈ V)
    (hW₀ : ∀ w, s₀ • w - ι₀ (L₀ w) ∈ W₀)
    (hι₀ : ∀ z, ι₀ z ∈ W₀ → t₀ • z = 0)
    (hα : ∀ w ∈ W, α w ∈ W₀)
    (hαβ : ∀ w, α (β w) - w ∈ W₀) :
    ∀ w ∈ W, ((t₀ * s₀ * s) ^ Fintype.card κ * s) • w ∈ V := by
  classical
  set θ : (κ → R) →ₗ[R] (κ → R) := L₀ ∘ₗ α ∘ₗ ι with hθ
  set θ' : (κ → R) →ₗ[R] (κ → R) := L ∘ₗ β ∘ₗ ι₀ with hθ'
  set D : R := t₀ * s₀ * s with hD
  -- `θ'` is a right inverse of `t₀θ` up to `D`
  have h1 : ∀ y, t₀ • θ (θ' y) = D • y := by
    intro y
    have ha := hα _ (hVW (hV (β (ι₀ y))))
    rw [map_sub, map_smul] at ha
    have hb := hαβ (ι₀ y)
    have hc := hW₀ (α (ι (θ' y)))
    have hmem : ι₀ ((s₀ * s) • y - θ (θ' y)) ∈ W₀ := by
      have : ι₀ ((s₀ * s) • y - θ (θ' y)) =
          s₀ • (s • α (β (ι₀ y)) - α (ι (L (β (ι₀ y))))) - (s₀ * s) • (α (β (ι₀ y)) - ι₀ y) +
            (s₀ • α (ι (θ' y)) - ι₀ (L₀ (α (ι (θ' y))))) := by
        simp only [hθ, hθ', LinearMap.coe_comp, Function.comp_apply, map_sub, map_smul,
          smul_sub, mul_smul]
        abel
      rw [this]
      exact W₀.add_mem (W₀.sub_mem (W₀.smul_mem _ ha) (W₀.smul_mem _ hb)) hc
    have h := hι₀ _ hmem
    rw [smul_sub, sub_eq_zero, smul_smul] at h
    rw [← h, hD, mul_assoc]
  -- `t₀θ` kills the coordinates of elements of `W`
  have h2 : ∀ z, ι z ∈ W → t₀ • θ z = 0 := by
    intro z hz
    have hmem : ι₀ (θ z) ∈ W₀ := by
      have := W₀.sub_mem (W₀.smul_mem s₀ (hα _ hz)) (hW₀ (α (ι z)))
      simpa [hθ] using this
    exact hι₀ _ hmem
  -- hence `D ^ #κ` kills them
  have h3 : ∀ z, t₀ • θ z = 0 → D ^ Fintype.card κ • z = 0 := by
    intro z hz
    set M := LinearMap.toMatrix' (t₀ • θ) with hM
    set M' := LinearMap.toMatrix' θ' with hM'
    have hMM' : M * M' = D • (1 : Matrix κ κ R) := by
      rw [hM, hM', ← LinearMap.toMatrix'_comp]
      have : (t₀ • θ) ∘ₗ θ' = D • LinearMap.id := by
        refine LinearMap.ext fun y ↦ ?_
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
          LinearMap.id_coe, id_eq]
        exact h1 y
      rw [this, map_smul, LinearMap.toMatrix'_id]
    have hdet : M.det * M'.det = D ^ Fintype.card κ := by
      rw [← Matrix.det_mul, hMM', Matrix.det_smul, Matrix.det_one, mul_one]
    have hleft : (M'.det • M.adjugate) * M = D ^ Fintype.card κ • (1 : Matrix κ κ R) := by
      rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm, hdet]
    have hMz : M.mulVec z = 0 := by
      rw [hM, LinearMap.toMatrix'_mulVec]
      exact hz
    have := congrArg (fun X : Matrix κ κ R ↦ X.mulVec z) hleft
    simp only [← Matrix.mulVec_mulVec, hMz, Matrix.mulVec_zero, Matrix.smul_mulVec,
      Matrix.one_mulVec] at this
    exact this.symm
  intro w hw
  have hιw : ι (L w) ∈ W := by
    have : ι (L w) = s • w - (s • w - ι (L w)) := by abel
    rw [this]
    exact W.sub_mem (W.smul_mem s hw) (hVW (hV w))
  have hz := h3 _ (h2 _ hιw)
  have : ((D ^ Fintype.card κ) * s) • w =
      D ^ Fintype.card κ • (s • w - ι (L w)) + ι (D ^ Fintype.card κ • L w) := by
    rw [map_smul, smul_sub, mul_smul]
    abel
  rw [this, hz, map_zero, add_zero]
  exact V.smul_mem _ (hV w)

end RankComparison

section CramerSplit

variable {R : Type*} [CommRing R] {n m k : ℕ} (hk : m + k = n)

/-- The inclusion `R^k → R^n` onto the last `k` coordinates, for `n = m + k`. -/
public def tailInclusion : (Fin k → R) →ₗ[R] (Fin n → R) where
  toFun z i := if h : m ≤ (i : ℕ) then z ⟨i - m, by omega⟩ else 0
  map_add' z w := by
    funext i
    by_cases h : m ≤ (i : ℕ) <;> simp [h]
  map_smul' c z := by
    funext i
    by_cases h : m ≤ (i : ℕ) <;> simp [h]

/-- The projection `R^n → R^k` onto the last `k` coordinates, for `n = m + k`. -/
public def tailProjection : (Fin n → R) →ₗ[R] (Fin k → R) :=
  LinearMap.funLeft R R fun l : Fin k ↦ ⟨m + l, by omega⟩

/-- The tail inclusion vanishes on the first `m` coordinates. -/
public theorem tailInclusion_castLE (z : Fin k → R) (i : Fin m) :
    tailInclusion hk z (Fin.castLE (by omega) i) = 0 := by
  have : ¬ m ≤ (i : ℕ) := by omega
  simp [tailInclusion, this]

/-- The tail projection is a retraction of the tail inclusion. -/
public theorem tailProjection_tailInclusion (z : Fin k → R) :
    tailProjection hk (tailInclusion hk z) = z := by
  funext l
  simp [tailProjection, tailInclusion, LinearMap.funLeft]

/-- A vector vanishing on the first `m` coordinates is the tail inclusion of its tail. -/
public theorem tailInclusion_tailProjection (w : Fin n → R)
    (hw : ∀ i : Fin m, w (Fin.castLE (by omega) i) = 0) :
    tailInclusion hk (tailProjection hk w) = w := by
  funext i
  by_cases h : m ≤ (i : ℕ)
  · simp only [tailInclusion, tailProjection, LinearMap.coe_mk, AddHom.coe_mk, h, dite_true,
      LinearMap.funLeft_apply]
    congr 1
    ext
    simp only
    omega
  · simp only [tailInclusion, LinearMap.coe_mk, AddHom.coe_mk, h, dite_false]
    exact (hw ⟨i, by omega⟩).symm

variable (u : Fin m → (Fin n → R))

/-- The square block `(u_j(i))_{i, j < m}` of a family of `m` vectors of `R^n`, `m ≤ n`. -/
public def cramerBlock : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j ↦ u j (Fin.castLE (by omega) i)

/-- **Cramer's rule, splitting off the first `m` coordinates.**  The linear map
`w ↦ ∑ⱼ (adj(U) w_{<m})ⱼ uⱼ`, for `U` the top block of the family `u`. -/
public def cramerCombination : (Fin n → R) →ₗ[R] (Fin n → R) :=
  Fintype.linearCombination R u ∘ₗ (cramerBlock hk u).adjugate.mulVecLin ∘ₗ
    LinearMap.funLeft R R (Fin.castLE (by omega))

/-- The last `k` coordinates of `det(U) w - ∑ⱼ (adj(U) w_{<m})ⱼ uⱼ`. -/
public def cramerTail : (Fin n → R) →ₗ[R] (Fin k → R) :=
  tailProjection hk ∘ₗ ((cramerBlock hk u).det • LinearMap.id - cramerCombination hk u)

/-- The Cramer combination lies in the span of the family. -/
public theorem cramerCombination_mem_span (w : Fin n → R) :
    cramerCombination hk u w ∈ Submodule.span R (Set.range u) := by
  simp only [cramerCombination, LinearMap.coe_comp, Function.comp_apply,
    Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- `det(U) w - ι(L w)` is the Cramer combination, where `ι` is the tail inclusion and `L` the
Cramer tail. -/
public theorem det_smul_sub_tailInclusion_cramerTail (w : Fin n → R) :
    (cramerBlock hk u).det • w - tailInclusion hk (cramerTail hk u w) =
      cramerCombination hk u w := by
  classical
  have htop : ∀ i : Fin m, ((cramerBlock hk u).det • w - cramerCombination hk u w)
      (Fin.castLE (by omega) i) = 0 := by
    intro i
    set v := LinearMap.funLeft R R (Fin.castLE (by omega : m ≤ n)) w with hv
    have hv' : (cramerBlock hk u).mulVec ((cramerBlock hk u).adjugate.mulVec v) =
        (cramerBlock hk u).det • v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hvi := congrFun hv' i
    have key : ∑ x, ((cramerBlock hk u).adjugate.mulVec v) x * u x (Fin.castLE (by omega) i) =
        (cramerBlock hk u).det * w (Fin.castLE (by omega) i) := by
      rw [Pi.smul_apply, smul_eq_mul, hv, LinearMap.funLeft_apply] at hvi
      rw [← hvi]
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cramerCombination, LinearMap.coe_comp,
      Function.comp_apply, Fintype.linearCombination_apply, Finset.sum_apply,
      Matrix.mulVecLin_apply]
    rw [← hv, key, sub_self]
  rw [cramerTail, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, tailInclusion_tailProjection hk _ htop, sub_sub_cancel]

/-- **Injectivity of the tail inclusion modulo a module of relations, up to a scalar.**  If `b`
carries `W₀` into the span of the family `u`, then `det(U) · b` kills every `z` with
`ι(z) ∈ W₀`. -/
public theorem det_mul_smul_eq_zero_of_tailInclusion_mem (W₀ : Submodule R (Fin n → R)) (b : R)
    (hb : ∀ w ∈ W₀, b • w ∈ Submodule.span R (Set.range u)) (z : Fin k → R)
    (hz : tailInclusion hk z ∈ W₀) : ((cramerBlock hk u).det * b) • z = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hb _ hz)
  have hUc : (cramerBlock hk u).mulVec c = 0 := by
    funext i
    have h := congrFun hc (Fin.castLE (by omega) i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tailInclusion_castLE,
      mul_zero] at h
    simp only [Matrix.mulVec, dotProduct, cramerBlock, Matrix.of_apply, Pi.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hdc : (cramerBlock hk u).det • c = 0 := by
    have := congrArg (cramerBlock hk u).adjugate.mulVec hUc
    rwa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
  have hzero : tailInclusion hk (((cramerBlock hk u).det * b) • z) = 0 := by
    rw [map_smul, mul_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [smul_smul, show (cramerBlock hk u).det * c j = 0 from congrFun hdc j, zero_smul]
  have := congrArg (tailProjection hk) hzero
  rwa [tailProjection_tailInclusion, map_zero] at this

end CramerSplit

section DegreeZero

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
  {B : AdicFiniteTypeAlgebra.{u, v} A I}

/-- **The degree-`0` shadow of Stacks 0GAE.**  For two completed polynomial presentations `P`,
`Q` of `B` there are linear maps `α : ⨁ B dxᵢ → ⨁ B dyⱼ` and `β` back, with `α` carrying the
relations of `P` into those of `Q` and `αβ ≡ id` modulo the relations of `Q`.  They are the
degree-`0` components of the homotopy equivalence of Stacks 0GAE, read through the
identifications of the terms of the completed naive cotangent complexes. -/
public theorem exists_degreeZero_maps (P Q : CompletedPolynomialPresentation I B) :
    ∃ (α : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] (Fin Q.variableCount → B.carrier))
      (β : (Fin Q.variableCount → B.carrier) →ₗ[B.carrier] (Fin P.variableCount → B.carrier)),
      (∀ w ∈ LinearMap.range (completedNaiveCotangentComplex B P).differential,
        α w ∈ LinearMap.range (completedNaiveCotangentComplex B Q).differential) ∧
      ∀ w, α (β w) - w ∈ LinearMap.range (completedNaiveCotangentComplex B Q).differential := by
  obtain ⟨e⟩ := completedNaiveCotangentComplex_homotopyEquiv I B P Q
  set KP := completedNaiveCotangentComplex B P
  set KQ := completedNaiveCotangentComplex B Q
  let a : ModuleCat.of B.carrier (CompletedNaiveCotangentComplex.LiftedDifferentials (P := P)) ⟶
      ModuleCat.of B.carrier (CompletedNaiveCotangentComplex.LiftedDifferentials (P := Q)) :=
    KP.degreeZeroIso.inv ≫ e.hom.f 0 ≫ KQ.degreeZeroIso.hom
  let b : ModuleCat.of B.carrier (CompletedNaiveCotangentComplex.LiftedDifferentials (P := Q)) ⟶
      ModuleCat.of B.carrier (CompletedNaiveCotangentComplex.LiftedDifferentials (P := P)) :=
    KQ.degreeZeroIso.inv ≫ e.inv.f 0 ≫ KP.degreeZeroIso.hom
  refine ⟨ULift.moduleEquiv.toLinearMap ∘ₗ a.hom ∘ₗ ULift.moduleEquiv.symm.toLinearMap,
    ULift.moduleEquiv.toLinearMap ∘ₗ b.hom ∘ₗ ULift.moduleEquiv.symm.toLinearMap, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have h2 := KP.degreeNegOneIso.inv ≫= (e.hom.comm (-1) 0 =≫ KQ.degreeZeroIso.hom)
    simp only [Category.assoc, KP.cochainComplex_d, KQ.cochainComplex_d, Iso.inv_hom_id,
      Iso.inv_hom_id_assoc, Category.comp_id] at h2
    have h := congrArg (fun g ↦ g.hom (ULift.up x)) h2
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_ofHom, CompletedNaiveCotangentComplex.liftedDifferential_up] at h
    refine ⟨((KP.degreeNegOneIso.inv ≫ e.hom.f (-1) ≫ KQ.degreeNegOneIso.hom).hom
      (ULift.up x)).down, ?_⟩
    have h' := congrArg ULift.down h
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, a,
      ModuleCat.hom_comp, ULift.moduleEquiv_symm_apply, ULift.moduleEquiv_apply]
    exact h'
  · intro w
    have hcomm := e.homotopyInvHomId.comm 0
    have hd01 : KQ.cochainComplex.d 0 1 = 0 :=
      HomologicalComplex.double_d_eq_zero₀ _ _ 0 1 (by decide)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl), hd01, Limits.zero_comp,
      zero_add, prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl),
      KQ.cochainComplex_d, HomologicalComplex.comp_f, HomologicalComplex.id_f] at hcomm
    have h2 := KQ.degreeZeroIso.inv ≫= (hcomm =≫ KQ.degreeZeroIso.hom)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Preadditive.add_comp,
      Preadditive.comp_add, Category.id_comp] at h2
    have h := congrArg (fun g ↦ g.hom (ULift.up w)) h2
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.coe_comp,
      Function.comp_apply, ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.id_coe, id_eq] at h
    have hPP : ∀ z, KP.degreeZeroIso.inv.hom (KP.degreeZeroIso.hom.hom z) = z := fun z ↦ by
      simp
    have hab : a.hom (b.hom (ULift.up w)) =
        KQ.degreeZeroIso.hom.hom ((e.hom.f 0).hom ((e.inv.f 0).hom
          (KQ.degreeZeroIso.inv.hom (ULift.up w)))) := by
      simp only [a, b, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, hPP]
    refine ⟨((KQ.degreeZeroIso.inv ≫ e.homotopyInvHomId.hom 0 (-1) ≫
      KQ.degreeNegOneIso.hom).hom (ULift.up w)).down, ?_⟩
    have h' := congrArg ULift.down h
    show _ = (a.hom (b.hom (ULift.up w))).down - w
    rw [hab, eq_sub_iff_add_eq]
    exact h'.symm

end DegreeZero

section Divisibility

variable {R : Type*} [CommRing R] (J : Ideal R)

/-- If powers of `J` lie in `(x)` and in `(y)`, a power of `J` lies in `(xy)`. -/
public theorem exists_pow_le_span_singleton_mul {x y : R}
    (hx : ∃ a, J ^ a ≤ Ideal.span {x}) (hy : ∃ b, J ^ b ≤ Ideal.span {y}) :
    ∃ c, J ^ c ≤ Ideal.span {x * y} := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by
    rw [pow_add, ← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mul_mono ha hb⟩

/-- If a power of `J` lies in `(x)`, a power of `J` lies in `(xᵏ)`. -/
public theorem exists_pow_le_span_singleton_pow {x : R} (hx : ∃ a, J ^ a ≤ Ideal.span {x})
    (k : ℕ) : ∃ c, J ^ c ≤ Ideal.span {x ^ k} := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨a * k, pow_mul_le_span_singleton_pow ha k⟩

/-- An ideal containing the `c`-th powers of `t` generators of `I` contains a power of `I`. -/
private theorem map_pow_le_of_forall_pow_mem {A : Type u} [CommRing A] {I : Ideal A}
    {B : Type*} [CommRing B] [Algebra A B] {t : ℕ}
    (agen : Fin t → A) (hagen : Ideal.span (Set.range agen) = I) (c : ℕ) {J : Ideal B}
    (h : ∀ k, algebraMap A B (agen k ^ c) ∈ J) :
    (I.map (algebraMap A B)) ^ (1 + t * (c - 1)) ≤ J := by
  have := span_range_pow_le_of_forall_pow_mem agen c (J.comap (algebraMap A B)) h
  rw [hagen] at this
  rwa [← Ideal.map_pow, Ideal.map_le_iff_le_comap]

/-- The defining relations of the multi-generator Jacobian algebra vanish in it. -/
private theorem algebraMap_multiJacobianRelations_eq_zero {A : Type u} [CommRing A]
    {r m t : ℕ} (hm : m ≤ r)
    (f : Fin m → MvPolynomial (Fin r) A) (a : Fin t → A) (c : ℕ) (j : Fin (t + m)) :
    algebraMap _ (MultiJacobianAlgebra hm f a c) (multiJacobianRelations hm f a c j) = 0 :=
  have hker : Ideal.span (Set.range (multiJacobianRelations hm f a c)) =
      (multiJacobianGenerators hm f a c).toExtension.ker :=
    (Algebra.Generators.ker_naive _ _).symm
  hker.le (Ideal.subset_span ⟨j, rfl⟩)

/-- An element of the presenting ring acts on the conormal module through its image in `B`. -/
private theorem toAlgHom_smul_cotangent_mk {A : Type u} [CommRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (x : P.completedPolynomialRing)
    (z : P.extension.ker) :
    P.toAlgHom x • Algebra.Extension.Cotangent.mk (P := P.extension) z =
      Algebra.Extension.Cotangent.mk (P := P.extension) ((show P.extension.Ring from x) • z) := by
  rw [map_smul, cotangent_ring_smul]
  rfl

end Divisibility

section Conormal

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- The defining relations of the multi-generator Jacobian algebra vanish in its completion,
read through the completed presentation. -/
private theorem toAlgHom_multiJacobianRelations_eq_zero {r m t : ℕ} (hm : m ≤ r)
    (f : Fin m → MvPolynomial (Fin r) A) (a : Fin t → A) (c : ℕ) (j : Fin (t + m)) :
    (multiJacobianCompletedPresentation I hm f a c).toAlgHom
      (algebraMap (MvPolynomial (Fin (t + r)) A) (completedPolynomialAlgebra I (t + r))
        (multiJacobianRelations hm f a c j)) = 0 := by
  refine (completedPresentationMap_algebraMap I _ _).trans ?_
  have h := congrArg
    (algebraMap (MultiJacobianAlgebra hm f a c)
      (adicCompletionAlgebra I (B := MultiJacobianAlgebra hm f a c)))
    (algebraMap_multiJacobianRelations_eq_zero hm f a c j)
  rwa [map_zero] at h

/-- **The relations of a Jacobian chart, read on the conormal module.**  For a Jacobian chart
`bJ ⊆ (f₁, …, f_m) + J²` on a presentation of `B`, multiplication by the image of `b` carries
the image of `J/J² → ⨁ B dxᵢ` into the span of the images of the classes of the `fⱼ`. -/
public theorem smul_mem_span_differential_of_jacobianChart
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    {m : ℕ} (b : P.completedPolynomialRing) (f : Fin m → P.ker)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2)
    (w : Fin P.variableCount → B.carrier)
    (hw : w ∈ LinearMap.range (completedNaiveCotangentComplex B P).differential) :
    P.toAlgHom b • w ∈ Submodule.span B.carrier (Set.range fun j : Fin m ↦
      (completedNaiveCotangentComplex B P).differential
        (Algebra.Extension.Cotangent.mk (P := P.extension) ⟨(f j).1, (f j).2⟩)) := by
  classical
  set K := completedNaiveCotangentComplex B P
  obtain ⟨x, rfl⟩ := hw
  obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := P.extension) x
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hrelations g.1 g.2)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hy
  have hzker : z ∈ P.extension.ker := Ideal.pow_le_self two_ne_zero hz
  let bR : P.extension.Ring := b
  let cR : Fin m → P.extension.Ring := c
  have hmk : Algebra.Extension.Cotangent.mk (P := P.extension) (bR • g) =
      ∑ j, cR j • Algebra.Extension.Cotangent.mk (P := P.extension) ⟨(f j).1, (f j).2⟩ +
        Algebra.Extension.Cotangent.mk (P := P.extension) ⟨z, hzker⟩ := by
    have hsum : bR • g = ∑ j, cR j • (⟨(f j).1, (f j).2⟩ : P.extension.ker) + ⟨z, hzker⟩ := by
      apply Subtype.ext
      let g' : P.completedPolynomialRing := g.1
      have e1 : b * g' = ∑ j, c j * (f j).1 + z := by rw [← hyz, ← hc]
      rw [Submodule.coe_add, Submodule.coe_sum]
      simp only [Submodule.coe_smul, smul_eq_mul]
      exact e1
    rw [hsum, map_add, map_sum]
    simp only [map_smul]
  have hz0 : Algebra.Extension.Cotangent.mk (P := P.extension) ⟨z, hzker⟩ = 0 :=
    (Algebra.Extension.Cotangent.mk_eq_zero_iff _).mpr hz
  rw [← map_smul, toAlgHom_smul_cotangent_mk B P b g, hmk, hz0, add_zero, map_sum]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [cotangent_ring_smul, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **The conormal annihilation in the last step of the proof of Stacks 0GAW.**

Let `B = A⟨x₁, …, x_r⟩/J` carry a Jacobian chart `b, f₁, …, f_m` as in Stacks 0GAW, let
`C = A[z₁, …, z_t, x₁, …, x_r]/(z₁Δ' - a₁^{c₁}, …, z_tΔ' - a_t^{c₁}, f'₁, …, f'_m)` be the
algebra of Stacks 0GAV for any polynomials `f'ⱼ` in the same variables and generators
`a₁, …, a_t` of `I`, and let `φ : C^∧ → B` be any surjection of `A`-algebras.  Then a power of
`I` annihilates `Ker(φ)/Ker(φ)²`.

This is the source's argument, with its localization replaced by explicit scalars.  The
six-term sequence of Stacks 0ALM reduces the claim to the annihilation of the kernel of
`H⁰(NL^∧_{C^∧/A} ⊗ B) → H⁰(NL^∧_{B/A})` together with that of `H⁻¹(NL^∧_{B/A})`, which is the
rig-smoothness of `B`.  Here both are done at the level of presentations: present `B` through
`C^∧` by `A⟨z, x⟩ → C^∧ → B`.  By Cramer's rule both `H⁰(NL^∧_{C^∧/A} ⊗ B)` and
`H⁰(NL^∧_{B/A})` are free of rank `r - m` up to scalars dividing a power of `I`
(`det_smul_sub_tailInclusion_cramerTail`, `det_mul_smul_eq_zero_of_tailInclusion_mem`), the
degree-`0` maps of Stacks 0GAE compare them (`exists_degreeZero_maps`), and
`smul_mem_of_rank_comparison` turns this into: a power of `I` carries every relation of the
presentation through `C^∧` into the span of the relations of `C`.  Rig-smoothness of `B`
(Stacks 0GAJ, condition (3)) then kills what is left in the conormal module. -/
public theorem exists_pow_smul_cotangent_eq_bot_of_jacobianChart
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (m : ℕ) (hm : m ≤ P.variableCount) (b : P.completedPolynomialRing) (f : Fin m → P.ker)
    (hvanish : B.adicIdeal ≤ (Ideal.span {P.toAlgHom b}).radical)
    (hjacobian :
      P.toAlgHom (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
          (f j : P.completedPolynomialRing)) ∣ P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2)
    {t : ℕ} (agen : Fin t → A) (hagen : Ideal.span (Set.range agen) = I) (c₁ : ℕ)
    (f' : Fin m → MvPolynomial (Fin P.variableCount) A)
    (φ : (adicCompletionObj I (B := MultiJacobianAlgebra hm f' agen c₁)).carrier →ₐ[A]
      B.carrier)
    (hφ : Function.Surjective φ) :
    ∃ c : ℕ, I ^ c • (⊤ : Submodule A (RingHom.ker φ.toRingHom).Cotangent) = ⊥ := by
  classical
  let r := P.variableCount
  let C := MultiJacobianAlgebra hm f' agen c₁
  let T := adicCompletionObj I (B := C)
  let PT := multiJacobianCompletedPresentation I hm f' agen c₁
  let rel := multiJacobianRelations hm f' agen c₁
  let L := I.map (algebraMap A B.carrier)
  -- the presentation of `B` through `C^∧`
  let Θ : completedPolynomialAlgebra I (t + r) →ₐ[A] B.carrier := φ.comp PT.toAlgHom
  have hΘs : Function.Surjective Θ := hφ.comp PT.toAlgHom_surjective
  let P' : CompletedPolynomialPresentation I B :=
    ⟨t + r, RingHom.ker Θ.toRingHom, Ideal.quotientKerAlgEquivOfSurjective hΘs⟩
  let K' := completedNaiveCotangentComplex B P'
  let K := completedNaiveCotangentComplex B P
  -- the ring map `ρ : A[z, x] → C → C^∧ → B`
  let ρ : MvPolynomial (Fin (t + r)) A →+* B.carrier :=
    φ.toRingHom.comp ((algebraMap C T.carrier).comp (algebraMap _ C))
  have hrelC : ∀ j, algebraMap _ C (rel j) = 0 :=
    algebraMap_multiJacobianRelations_eq_zero hm f' agen c₁
  have hPTalg : ∀ p, PT.toAlgHom (algebraMap (MvPolynomial (Fin (t + r)) A)
      (completedPolynomialAlgebra I (t + r)) p) = algebraMap C T.carrier (algebraMap _ C p) :=
    fun p ↦ completedPresentationMap_algebraMap I _ p
  have hΘρ : ∀ p, Θ (algebraMap (MvPolynomial (Fin (t + r)) A)
      (completedPolynomialAlgebra I (t + r)) p) = ρ p := fun p ↦ by
    show φ (PT.toAlgHom _) = _
    rw [hPTalg]
    rfl
  have hρC : ∀ a : A, ρ (MvPolynomial.C a) = algebraMap A B.carrier a := by
    intro a
    show φ (algebraMap C T.carrier (algebraMap _ C (MvPolynomial.C a))) = _
    rw [show (MvPolynomial.C a : MvPolynomial (Fin (t + r)) A) =
        algebraMap A (MvPolynomial (Fin (t + r)) A) a from rfl,
      ← IsScalarTower.algebraMap_apply A (MvPolynomial (Fin (t + r)) A) C a,
      ← IsScalarTower.algebraMap_apply A C T.carrier a, AlgHom.commutes]
  have hρrel : ∀ j, ρ (rel j) = 0 := by
    intro j
    show φ (algebraMap C T.carrier (algebraMap _ C (rel j))) = 0
    rw [hrelC, map_zero, map_zero]
  -- the relations of `C`, read in the presentation through `C^∧`
  let F : Fin (t + m) → completedPolynomialAlgebra I (t + r) := fun j ↦
    algebraMap (MvPolynomial (Fin (t + r)) A) (completedPolynomialAlgebra I (t + r)) (rel j)
  have hPTF : ∀ j, PT.toAlgHom (F j) = 0 :=
    toAlgHom_multiJacobianRelations_eq_zero hm f' agen c₁
  have hFker : ∀ j, (show P'.extension.Ring from F j) ∈ P'.extension.ker := fun j ↦ by
    show φ (PT.toAlgHom (F j)) = 0
    rw [hPTF, map_zero]
  let u : Fin (t + m) → (Fin (t + r) → B.carrier) := fun j ↦
    K'.differential (Algebra.Extension.Cotangent.mk (P := P'.extension) ⟨_, hFker j⟩)
  have hu_apply : ∀ j i, u j i = ρ (MvPolynomial.pderiv i (rel j)) := by
    intro j i
    refine (congrFun (K'.differential_mk ⟨_, hFker j⟩) i).trans ?_
    show Θ (K'.partialDeriv i (algebraMap _ _ (rel j))) = _
    rw [K'.partialDeriv_polynomial, hΘρ]
  -- `δ = Δ'` and `ζₖ = zₖ` in `B`, with `δζₖ = aₖ^{c₁}`
  let δ := ρ (rename (Fin.natAdd t) (jacobian hm f').det)
  have hδζ : ∀ k : Fin t, algebraMap A B.carrier (agen k ^ c₁) =
      ρ (X (Fin.castAdd r k)) * δ := by
    intro k
    have h0 := hρrel (Fin.castAdd m k)
    change ρ (multiJacobianRelations hm f' agen c₁ (Fin.castAdd m k)) = 0 at h0
    rw [multiJacobianRelations_castAdd, map_sub, map_mul, hρC, sub_eq_zero] at h0
    exact h0.symm
  have hkT : (t + m) + (r - m) = t + r := by omega
  have hk₀ : m + (r - m) = r := by omega
  have hdetT : (cramerBlock hkT u).det = δ ^ (t + 1) := by
    have h1 : cramerBlock hkT u = ρ.mapMatrix (jacobian (by omega : t + m ≤ t + r) rel) := by
      ext i j
      exact hu_apply j _
    rw [h1, ← RingHom.map_det,
      show (jacobian (by omega : t + m ≤ t + r) rel).det =
        rename (Fin.natAdd t) (jacobian hm f').det ^ (t + 1) from
      det_pderiv_multiJacobianRelations hm _ f' agen c₁, map_pow]
  have hδI : ∃ c, L ^ c ≤ Ideal.span {δ} := by
    refine ⟨1 + t * (c₁ - 1), map_pow_le_of_forall_pow_mem agen hagen c₁ fun k ↦ ?_⟩
    rw [hδζ k]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  -- the chart of `B`
  let u₀ : Fin m → (Fin r → B.carrier) := fun j ↦
    K.differential (Algebra.Extension.Cotangent.mk (P := P.extension) ⟨(f j).1, (f j).2⟩)
  let Δ₀ := (cramerBlock hk₀ u₀).det
  have hΔ₀b : Δ₀ ∣ P.toAlgHom b := by
    have h1 : cramerBlock hk₀ u₀ =
        (P.toAlgHom : P.completedPolynomialRing →+* B.carrier).mapMatrix
          (Matrix.of fun i j : Fin m ↦ K.partialDeriv (Fin.castLE hm i) (f j)) := by
      ext i j
      exact congrFun (K.differential_mk ⟨(f j).1, (f j).2⟩) _
    show (cramerBlock hk₀ u₀).det ∣ _
    rw [h1, ← RingHom.map_det]
    exact hjacobian
  obtain ⟨cb, hcb⟩ := exists_pow_adicIdeal_le_span_of_le_radical B (P.toAlgHom b) hvanish
  have hbI : ∃ c, L ^ c ≤ Ideal.span {P.toAlgHom b} := ⟨cb, hcb⟩
  have hΔI : ∃ c, L ^ c ≤ Ideal.span {Δ₀} :=
    ⟨cb, hcb.trans (Ideal.span_singleton_le_span_singleton.mpr hΔ₀b)⟩
  -- the comparison
  obtain ⟨α, β, hα, hαβ⟩ := exists_degreeZero_maps P' P
  let V := Submodule.span B.carrier (Set.range u)
  let W := LinearMap.range K'.differential
  let W₀ := LinearMap.range K.differential
  have hVW : V ≤ W := Submodule.span_le.mpr (Set.range_subset_iff.mpr fun _ ↦ ⟨_, rfl⟩)
  have hspan₀ : Submodule.span B.carrier (Set.range u₀) ≤ W₀ :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun _ ↦ ⟨_, rfl⟩)
  have hcomp := smul_mem_of_rank_comparison V W W₀ hVW (tailInclusion hkT)
    (cramerTail hkT u) (tailInclusion hk₀) (cramerTail hk₀ u₀) α β (δ ^ (t + 1)) Δ₀
    (Δ₀ * P.toAlgHom b)
    (fun w ↦ by
      rw [← hdetT, det_smul_sub_tailInclusion_cramerTail]
      exact cramerCombination_mem_span hkT u w)
    (fun w ↦ by
      rw [det_smul_sub_tailInclusion_cramerTail]
      exact hspan₀ (cramerCombination_mem_span hk₀ u₀ w))
    (fun z hz ↦ det_mul_smul_eq_zero_of_tailInclusion_mem hk₀ u₀ W₀ _
      (fun w hw ↦ smul_mem_span_differential_of_jacobianChart B P b f hrelations w hw) z hz)
    hα hαβ
  obtain ⟨cG, hcG⟩ : ∃ c, L ^ c ≤ Ideal.span
      {(Δ₀ * P.toAlgHom b * Δ₀ * δ ^ (t + 1)) ^ Fintype.card (Fin (r - m)) * δ ^ (t + 1)} := by
    have hδt := exists_pow_le_span_singleton_pow L hδI (t + 1)
    exact exists_pow_le_span_singleton_mul L
      (exists_pow_le_span_singleton_pow L (exists_pow_le_span_singleton_mul L
        (exists_pow_le_span_singleton_mul L (exists_pow_le_span_singleton_mul L hΔI hbI) hΔI)
        hδt) _) hδt
  have hgrad : ∀ a ∈ I ^ cG, ∀ w ∈ W, algebraMap A B.carrier a • w ∈ V := by
    intro a ha w hw
    have hmem : algebraMap A B.carrier a ∈ Ideal.span
        {(Δ₀ * P.toAlgHom b * Δ₀ * δ ^ (t + 1)) ^ Fintype.card (Fin (r - m)) *
          δ ^ (t + 1)} := by
      refine hcG ?_
      show _ ∈ (I.map (algebraMap A B.carrier)) ^ cG
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
    rw [← hy, mul_smul]
    exact V.smul_mem y (hcomp w hw)
  -- rig-smoothness of `B` kills the rest
  have hBs := isRigSmooth_of_jacobianChart B P m hm b f hvanish hjacobian hrelations
  obtain ⟨cB, hcB⟩ := (isRigSmooth_iff_cotangentFactorization B P').mp hBs
  have hmain : ∀ a ∈ I ^ cG, ∀ a' ∈ I ^ cB, ∀ y : T.carrier, φ y = 0 →
      algebraMap A T.carrier (a' * a) * y ∈ (RingHom.ker φ.toRingHom) ^ 2 := by
    intro a ha a' ha' y hy
    obtain ⟨g₀, rfl⟩ := PT.toAlgHom_surjective y
    let g : completedPolynomialAlgebra I (t + r) := g₀
    have hgker : (show P'.extension.Ring from g) ∈ P'.extension.ker := hy
    obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun B.carrier).mp
      (hgrad a ha _ ⟨Algebra.Extension.Cotangent.mk (P := P'.extension) ⟨_, hgker⟩, rfl⟩)
    choose γ' hγ' using fun j ↦ hΘs (γ j)
    let g' : completedPolynomialAlgebra I (t + r) :=
      algebraMap A _ a * g - ∑ j, γ' j * F j
    have hg'ker : (show P'.extension.Ring from g') ∈ P'.extension.ker := by
      show Θ g' = 0
      have hΘg : Θ g = 0 := hy
      simp only [g', map_sub, map_mul, map_sum, AlgHom.commutes, hΘg, mul_zero, zero_sub]
      rw [neg_eq_zero]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [show Θ (F j) = 0 from hFker j, mul_zero]
    have hsmul : ∀ (x : completedPolynomialAlgebra I (t + r)) (z : P'.extension.ker),
        Θ x • Algebra.Extension.Cotangent.mk (P := P'.extension) z =
          Algebra.Extension.Cotangent.mk (P := P'.extension)
            ((show P'.extension.Ring from x) • z) :=
      toAlgHom_smul_cotangent_mk B P'
    have hmk : Algebra.Extension.Cotangent.mk (P := P'.extension) ⟨_, hg'ker⟩ =
        algebraMap A B.carrier a •
            Algebra.Extension.Cotangent.mk (P := P'.extension) ⟨_, hgker⟩ -
          ∑ j, γ j • Algebra.Extension.Cotangent.mk (P := P'.extension) ⟨_, hFker j⟩ := by
      rw [show algebraMap A B.carrier a = Θ (algebraMap A _ a) from (Θ.commutes a).symm,
        hsmul]
      simp only [← hγ', hsmul, ← map_sum, ← map_sub]
      congr 1
      apply Subtype.ext
      rw [Submodule.coe_sub, Submodule.coe_sum]
      rfl
    have hd : K'.differential (Algebra.Extension.Cotangent.mk (P := P'.extension)
        ⟨_, hg'ker⟩) = 0 := by
      rw [hmk, map_sub, map_sum, map_smul, sub_eq_zero, ← hγ]
      simp only [map_smul]
      rfl
    obtain ⟨h, hh⟩ := hcB a' ha'
    have hzero : algebraMap A B.carrier a' •
        Algebra.Extension.Cotangent.mk (P := P'.extension) ⟨_, hg'ker⟩ = 0 := by
      have := LinearMap.congr_fun hh
        (Algebra.Extension.Cotangent.mk (P := P'.extension) ⟨_, hg'ker⟩)
      rw [LinearMap.comp_apply, hd, map_zero, LinearMap.smul_apply, LinearMap.id_apply] at this
      exact this.symm
    let x' : completedPolynomialAlgebra I (t + r) := algebraMap A _ a' * g'
    have hsq : (show P'.extension.Ring from x') ∈ P'.extension.ker ^ 2 := by
      have hmem : (show P'.extension.Ring from x') ∈ P'.extension.ker :=
        Ideal.mul_mem_left _ _ hg'ker
      rw [← Algebra.Extension.Cotangent.mk_eq_zero_iff (P := P'.extension) ⟨_, hmem⟩]
      have := hsmul (algebraMap A _ a') ⟨_, hg'ker⟩
      rw [AlgHom.commutes, hzero] at this
      exact this.symm
    let πT : completedPolynomialAlgebra I (t + r) →+* T.carrier := PT.toAlgHom.toRingHom
    let ψT : P'.extension.Ring →+* T.carrier := πT
    have hle : P'.extension.ker.map ψT ≤ RingHom.ker φ.toRingHom :=
      Ideal.map_le_iff_le_comap.mpr fun _ hx ↦ hx
    have himage := Ideal.mem_map_of_mem ψT hsq
    rw [Ideal.map_pow] at himage
    have himage' := Ideal.pow_right_mono hle 2 himage
    have hπF : ∀ j, πT (F j) = 0 := hPTF
    have hπA : ∀ a : A, πT (algebraMap A _ a) = algebraMap A T.carrier a :=
      fun a ↦ PT.toAlgHom.commutes a
    have hval : ψT (show P'.extension.Ring from x') =
        algebraMap A T.carrier (a' * a) * PT.toAlgHom g₀ := by
      show πT (algebraMap A _ a' * (algebraMap A _ a * g - ∑ j, γ' j * F j)) = _
      simp only [map_mul, map_sub, map_sum, hπF, hπA, mul_zero, Finset.sum_const_zero,
        sub_zero, ← mul_assoc]
      rfl
    rwa [hval] at himage'
  -- conclusion
  refine ⟨cB + cG, le_antisymm (Submodule.smul_le.mpr ?_) bot_le⟩
  intro c hc z _
  obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.toCotangent_surjective _ z
  rw [pow_add] at hc
  refine Submodule.mul_induction_on hc
    (C := fun c ↦ c • (RingHom.ker φ.toRingHom).toCotangent ⟨y, hy⟩ ∈ (⊥ : Submodule A _))
    (fun a' ha' a ha ↦ ?_) (fun x x' hx hx' ↦ ?_)
  · rw [Submodule.mem_bot, ← algebraMap_smul T.carrier, ← map_smul]
    refine (Ideal.toCotangent_eq_zero _ _).mpr ?_
    rw [Submodule.coe_smul, smul_eq_mul]
    exact hmain a ha a' ha' y hy
  · rw [add_smul]
    exact Submodule.add_mem _ hx hx'

end Conormal

section Universe

/-- A completion of a finite type `A`-algebra in any universe is the completion of a finite
type `A`-algebra in the universe of `A`: replace the algebra by a quotient of a polynomial ring
in finitely many variables. -/
public theorem exists_finiteType_algEquiv_adicCompletion_of_algEquiv {A : Type u} [CommRing A]
    (I : Ideal A) {D : Type*} [CommRing D] [Algebra A D] [Algebra.FiniteType A D]
    {E : Type*} [CommRing E] [Algebra A E] (e : E ≃ₐ[A] AdicCompletion (I.map (algebraMap A D)) D) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (E ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A D)
  let eQ := Ideal.quotientKerAlgEquivOfSurjective hg
  have hft : Algebra.FiniteType A (MvPolynomial (Fin n) A ⧸ RingHom.ker g) :=
    Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType A D) eQ.symm
  have hIJ : I.map (algebraMap A D) =
      (I.map (algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker g))).map
        ((eQ : (MvPolynomial (Fin n) A ⧸ RingHom.ker g) →ₐ[A] D) :
          (MvPolynomial (Fin n) A ⧸ RingHom.ker g) →+* D) := by
    rw [Ideal.map_map]
    congr 1
    exact ((eQ : (MvPolynomial (Fin n) A ⧸ RingHom.ker g) →ₐ[A] D).comp_algebraMap).symm
  exact ⟨_, inferInstance, inferInstance, hft,
    ⟨e.trans (AdicCompletion.congrAlgEquiv eQ hIJ).symm⟩⟩

end Universe

section Main

open RestrictedPowerSeries

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

omit [IsNoetherianRing A] in
/-- The restricted power series attached to a polynomial corresponds, in the adic completion
of the polynomial ring, to that polynomial. -/
public theorem adicCompletionAlgEquiv_polynomialAlgHom {σ : Type*} (p : MvPolynomial σ A) :
    adicCompletionAlgEquiv I σ (polynomialAlgHom I σ p) =
      algebraMap (MvPolynomial σ A)
        (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A))
        p :=
  adicCompletionEquiv_polynomialRingHom I σ p

/-- **Stacks Project, Tag 0GAW: the Jacobian criterion for algebraization.**

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` an `I`-adically complete `A`-algebra
with `B/IB` of finite type over `A/I` (an object of Stacks 0AL4), presented as
`B = A⟨x₁, …, x_r⟩/J`.  Assume there are `b ∈ B`, `0 ≤ m ≤ r` and `f₁, …, f_m ∈ J` such that

1. `V(b) ⊆ V(IB)` in `Spec(B)`,
2. the image of `Δ = det(∂fⱼ/∂xᵢ)_{1 ≤ i, j ≤ m}` in `B` divides `b`, and
3. `bJ ⊆ (f₁, …, f_m) + J²`.

Then there exist a finite type `A`-algebra `C` and an `A`-algebra isomorphism `B ≅ C^∧`.

Here `b` is given by a lift to `A⟨x⟩`; condition (1) is `IB ⊆ √(b)`.

**The proof.**  As in the source, `C` is the algebra
`A[z₁, …, z_t, x₁, …, x_r]/(z₁Δ' - a₁^{c₁}, …, z_tΔ' - a_t^{c₁}, f'₁, …, f'_m)` of Stacks 0GAV
built from polynomial approximations `f'ⱼ` of the `fⱼ` and generators `a₁, …, a_t` of `I`, and
it maps onto `B/IⁿB`.  The lift of that map to `φ : C^∧ → B` is produced by Newton's method
(`exists_algHom_newton`): in this algebra the Jacobian determinant of the relations with
respect to `z₁, …, z_t, x₁, …, x_m` is `Δ'^{t+1}`, and the relations themselves force a fixed
power of `I` into `Δ'B`, so the linearized equations can be solved exactly at each step and
the source's uniform lifting result Stacks 0GAQ is not needed.  `φ` is surjective because it is
surjective modulo `I`, a power of `I` kills `Ker(φ)/Ker(φ)²`
(`exists_pow_smul_cotangent_eq_bot_of_jacobianChart`, the source's application of Stacks 0ALM
and of the comparison of free modules of rank `r - m`), and Stacks 0ALR concludes. -/
@[stacks 0GAW]
public theorem exists_finiteType_adicCompletion_algEquiv_of_jacobianChart
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (m : ℕ) (hm : m ≤ P.variableCount) (b : P.completedPolynomialRing)
    (f : Fin m → P.ker)
    (hvanish : B.adicIdeal ≤ (Ideal.span {P.toAlgHom b}).radical)
    (hjacobian :
      P.toAlgHom (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
          (f j : P.completedPolynomialRing)) ∣ P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  classical
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hBcomplete : IsAdicComplete (I.map (algebraMap A B.carrier)) B.carrier :=
    B.isAdicallyComplete
  obtain ⟨t, agen, hagen⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hIfg
  have hai : ∀ i, agen i ∈ I := fun i ↦ hagen ▸ Ideal.subset_span ⟨i, rfl⟩
  set r := P.variableCount with hr
  -- `V(b) ⊆ V(IB)` gives `c₁` with `I^{c₁}B ⊆ bB`
  obtain ⟨c₁, hc₁⟩ := exists_pow_adicIdeal_le_span_of_le_radical B (P.toAlgHom b) hvanish
  -- the relations read as restricted power series
  let g : Fin m → RestrictedPowerSeries I (Fin r) := fun j ↦
    (adicCompletionAlgEquiv I (Fin r)).symm (f j : P.completedPolynomialRing)
  have hge : ∀ j, adicCompletionAlgEquiv I (Fin r) (g j) =
      (f j : P.completedPolynomialRing) := fun j ↦ AlgEquiv.apply_symm_apply _ _
  have hgker : ∀ j, g j ∈ P.restrictedKer := by
    intro j
    rw [P.mem_restrictedKer_iff, hge j]
    exact (f j).2
  obtain ⟨b', hb'⟩ := hjacobian
  -- the accuracy of the approximation
  set e := (t + 1) * (1 + t * (c₁ - 1)) with he
  set n := 4 * e + 1 with hn
  obtain ⟨f', hf'proj, hf'mem⟩ := P.exists_mvPolynomial_approx_mem_restrictedKer hIfg n g hgker
  -- the cofactors `b_k` of `b`
  have hbsex : ∀ i : Fin t, ∃ w : B.carrier,
      P.toAlgHom b * w = algebraMap A B.carrier (agen i ^ c₁) := by
    intro i
    have hmem : algebraMap A B.carrier (agen i ^ c₁) ∈ B.adicIdeal ^ c₁ := by
      rw [show B.adicIdeal = I.map (algebraMap A B.carrier) from rfl, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow (hai i) c₁)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (hc₁ hmem)
    exact ⟨w, (mul_comm _ _).trans hw⟩
  choose bs hbs using hbsex
  -- the determinant of the approximations is close to `Δ`
  have hbapprox : b' * P.restrictedToAlgHom
        (polynomialAlgHom I (Fin r) (jacobian hm f').det) - P.toAlgHom b ∈
      (I ^ n).map (algebraMap A B.carrier) := by
    have hdet := det_partialDeriv_sub_restrictedToAlgHom_det_mem P hIfg n hm g f' hf'proj
    rw [show (Matrix.det fun i j : Fin m ↦
          (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
            (adicCompletionAlgEquiv I (Fin r) (g j))) =
        (Matrix.det fun i j : Fin m ↦
          (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
            (f j : P.completedPolynomialRing)) from by
      congr 1
      funext i j
      rw [hge j]] at hdet
    rw [hb', show b' * P.restrictedToAlgHom
          (polynomialAlgHom I (Fin r) (jacobian hm f').det) -
          P.toAlgHom (Matrix.det fun i j : Fin m ↦
            (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
              (f j : P.completedPolynomialRing)) * b' =
        -(b' * (P.toAlgHom (Matrix.det fun i j : Fin m ↦
            (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
              (f j : P.completedPolynomialRing)) - P.restrictedToAlgHom
          (polynomialAlgHom I (Fin r) (jacobian hm f').det))) from by ring]
    exact neg_mem (Ideal.mul_mem_left _ b' hdet)
  -- the surjection `ψ : C ⟶ B/IⁿB`
  obtain ⟨ψ, hψsurj, -, -⟩ := exists_algHom_multiJacobianAlgebra_quotient P hIfg n hm f'
    agen c₁ (P.toAlgHom b) b' bs hf'mem hbapprox hbs
  let C := MultiJacobianAlgebra hm f' agen c₁
  let T := adicCompletionObj I (B := C)
  let PT := multiJacobianCompletedPresentation I hm f' agen c₁
  have hLn : (I ^ n).map (algebraMap A B.carrier) =
      (I.map (algebraMap A B.carrier)) ^ n := Ideal.map_pow _ _ _
  let ψ' : C →ₐ[A] B.carrier ⧸ (I.map (algebraMap A B.carrier)) ^ n :=
    (Ideal.quotientEquivAlgOfEq A hLn).toAlgHom.comp ψ
  have hψ'surj : Function.Surjective ψ' :=
    (Ideal.quotientEquivAlgOfEq A hLn).surjective.comp hψsurj
  have hkillK : ∀ x : C, x ∈ (I.map (algebraMap A C)) ^ n → ψ' x = 0 := by
    intro x hx
    refine eq_zero_of_mem_map_pow n ψ' x ?_
    rwa [Ideal.map_pow]
  let ψq : C ⧸ (I.map (algebraMap A C)) ^ n →ₐ[A]
      B.carrier ⧸ (I.map (algebraMap A B.carrier)) ^ n :=
    Ideal.Quotient.liftₐ ((I.map (algebraMap A C)) ^ n) ψ' hkillK
  have hψqsurj : Function.Surjective ψq := by
    intro y
    obtain ⟨x, rfl⟩ := hψ'surj y
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  let ψn : T.carrier →ₐ[A] B.carrier ⧸ (I.map (algebraMap A B.carrier)) ^ n :=
    ψq.comp ((AdicCompletion.evalₐ (I.map (algebraMap A C)) n).restrictScalars A)
  have hψnsurj : Function.Surjective ψn :=
    hψqsurj.comp (AdicCompletion.surjective_evalₐ (I.map (algebraMap A C)) n)
  -- a continuous lift `ψ̂ : A⟨z, x⟩ → B` of `ψn`
  obtain ⟨ψh, hψhc, hψhred⟩ := exists_continuousAlgHom_lift_quotient hIfg PT n ψn
  -- the relations of `C` as restricted power series
  let rel := multiJacobianRelations hm f' agen c₁
  let FR : Fin (t + m) → RestrictedPowerSeries I (Fin (t + r)) := fun j ↦
    polynomialAlgHom I (Fin (t + r)) (rel j)
  have hkerG : Ideal.span (Set.range (multiJacobianRelations hm f' agen c₁)) =
      (multiJacobianGenerators hm f' agen c₁).toExtension.ker :=
    (Algebra.Generators.ker_naive _ _).symm
  have hFRker : ∀ j, PT.restrictedToAlgHom (FR j) = 0 := fun j ↦
    (congrArg PT.toAlgHom (adicCompletionAlgEquiv_polynomialAlgHom (I := I) (rel j))).trans
      (toAlgHom_multiJacobianRelations_eq_zero hm f' agen c₁ j)
  let ψh' : RestrictedPowerSeries I (Fin (t + r)) →ₐ[A] B.carrier := ψh
  have hψh'c : @Continuous _ _ (limitTopology I (Fin (t + r)))
      ((I.map (algebraMap A B.carrier)).adicTopology) ψh' := hψhc
  have h0 : ∀ j, ψh' (FR j) ∈ (I.map (algebraMap A B.carrier)) ^ n := by
    intro j
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (hψhred (FR j)).trans (by rw [hFRker j, map_zero])
  -- the Jacobian determinant of the relations, and the relations `zₖΔ' - aₖ^{c₁}`
  have h' : t + m ≤ t + r := by omega
  have hmat : ∀ ψ : RestrictedPowerSeries I (Fin (t + r)) →ₐ[A] B.carrier,
      (Matrix.of fun i j ↦ ψ (partialDerivative I (Fin.castLE h' i) (FR j))).det =
        ψ (polynomialAlgHom I _ (rename (Fin.natAdd t) (jacobian hm f').det)) ^ (t + 1) := by
    intro ψ
    have h1 : (Matrix.of fun i j ↦ ψ (partialDerivative I (Fin.castLE h' i) (FR j))) =
        (ψ.toRingHom.comp (polynomialAlgHom I (Fin (t + r))).toRingHom).mapMatrix
          (jacobian h' rel) := by
      ext i j
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, FR,
        partialDerivative_polynomialAlgHom]
      rfl
    rw [h1, ← RingHom.map_det, show (jacobian h' rel).det =
        rename (Fin.natAdd t) (jacobian hm f').det ^ (t + 1) from
      det_pderiv_multiJacobianRelations hm h' f' agen c₁, map_pow]
    rfl
  have hzrel : ∀ (ψ : RestrictedPowerSeries I (Fin (t + r)) →ₐ[A] B.carrier) (k : Fin t),
      algebraMap A B.carrier (agen k ^ c₁) =
        ψ (polynomialAlgHom I _ (X (Fin.castAdd r k))) *
          ψ (polynomialAlgHom I _ (rename (Fin.natAdd t) (jacobian hm f').det)) -
          ψ (FR (Fin.castAdd m k)) := by
    intro ψ k
    have : FR (Fin.castAdd m k) = polynomialAlgHom I (Fin (t + r))
        (X (Fin.castAdd r k) * rename (Fin.natAdd t) (jacobian hm f').det -
          MvPolynomial.C (agen k ^ c₁)) :=
      congrArg (polynomialAlgHom I (Fin (t + r))) (multiJacobianRelations_castAdd hm f' agen c₁ k)
    rw [this, map_sub, map_mul, map_sub, map_mul,
      show (MvPolynomial.C (agen k ^ c₁) : MvPolynomial (Fin (t + r)) A) =
        algebraMap A _ (agen k ^ c₁) from rfl, AlgHom.commutes, AlgHom.commutes]
    ring
  have hc''e : 1 + t * (c₁ - 1) ≤ e := by
    rw [he]
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos t)
  have hdet : ∀ (ψ : RestrictedPowerSeries I (Fin (t + r)) →ₐ[A] B.carrier) (m' : ℕ), e < m' →
      (∀ j, ψ (FR j) ∈ (I.map (algebraMap A B.carrier)) ^ m') →
      (I.map (algebraMap A B.carrier)) ^ e ≤
        Ideal.span
          {(Matrix.of fun i j ↦ ψ (partialDerivative I (Fin.castLE h' i) (FR j))).det} := by
    intro ψ m' hm' hF
    set Dψ := ψ (polynomialAlgHom I _ (rename (Fin.natAdd t) (jacobian hm f').det)) with hDψ
    have hN : (I.map (algebraMap A B.carrier)) ^ (1 + t * (c₁ - 1)) ≤
        Ideal.span {Dψ} ⊔ (I.map (algebraMap A B.carrier)) ^ m' := by
      refine map_pow_le_of_forall_pow_mem agen hagen c₁ fun k ↦ ?_
      rw [hzrel ψ k]
      exact sub_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _
        (Ideal.mem_span_singleton_self _))) (Ideal.mem_sup_right (hF _))
    have hNak : (I.map (algebraMap A B.carrier)) ^ (1 + t * (c₁ - 1)) ≤ Ideal.span {Dψ} := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (IsAdicComplete.le_jacobson_bot (I.map (algebraMap A B.carrier)))
        (hN.trans (sup_le_sup_left ?_ _))
      rw [smul_eq_mul, ← pow_succ']
      exact Ideal.pow_le_pow_right (by omega)
    rw [hmat, he, mul_comm]
    exact pow_mul_le_span_singleton_pow hNak _
  -- Newton's method produces `φ̂ : A⟨z, x⟩ → B` killing the relations
  obtain ⟨φh, hφh0, hφhd⟩ := exists_algHom_newton I hIfg FR (Fin.castLE h') e hdet n
    (by omega) ψh' hψh'c h0
  -- `φ̂` kills the kernel of the presentation of `C^∧`
  let eR := adicCompletionAlgEquiv I (Fin (t + r))
  have hα : RingHom.ker (presentationAlgHom (multiJacobianGenerators hm f' agen c₁)).toRingHom =
      Ideal.span (Set.range rel) := hkerG.symm
  have hvan : ∀ x ∈ PT.ideal, (φh.comp eR.symm.toAlgHom) x = 0 := by
    intro x hx
    have hx' : x ∈ (RingHom.ker (presentationAlgHom
        (multiJacobianGenerators hm f' agen c₁)).toRingHom).map
          (algebraMap (MvPolynomial (Fin (t + r)) A) (completedPolynomialAlgebra I (t + r))) := hx
    rw [hα] at hx'
    have hle : (Ideal.span (Set.range rel)).map
        (algebraMap (MvPolynomial (Fin (t + r)) A) (completedPolynomialAlgebra I (t + r))) ≤
          (Ideal.span (Set.range FR)).comap (eR.symm : _ →+* _) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      show eR.symm (algebraMap _ _ (rel j)) ∈ Ideal.span (Set.range FR)
      rw [← adicCompletionAlgEquiv_polynomialAlgHom, AlgEquiv.symm_apply_apply]
      exact Ideal.subset_span ⟨j, rfl⟩
    exact hφh0 _ (hle hx')
  let φR : PT.completedPolynomialRing →ₐ[A] B.carrier := φh.comp eR.symm.toAlgHom
  let φT : T.carrier →ₐ[A] B.carrier :=
    (Ideal.Quotient.liftₐ PT.ideal φR hvan).comp PT.quotientEquiv.symm.toAlgHom
  have hfac : ∀ y : RestrictedPowerSeries I (Fin (t + r)), φT (PT.restrictedToAlgHom y) = φh y := by
    intro y
    have hy : PT.restrictedToAlgHom y =
        PT.quotientEquiv (Ideal.Quotient.mk PT.ideal (eR y)) := rfl
    rw [hy]
    show Ideal.Quotient.liftₐ PT.ideal φR hvan
      (PT.quotientEquiv.symm (PT.quotientEquiv (Ideal.Quotient.mk PT.ideal (eR y)))) = φh y
    rw [AlgEquiv.symm_apply_apply]
    exact congrArg φh (eR.symm_apply_apply y)
  -- `φ` is surjective, because it is surjective modulo `I`
  have hne : n - 2 * e ≠ 0 := by omega
  have hmkφL : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap A B.carrier))).comp φT.toRingHom) := by
    intro z₀
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (I := I.map (algebraMap A B.carrier)) z₀
    obtain ⟨w, hw⟩ := hψnsurj (Ideal.Quotient.mk ((I.map (algebraMap A B.carrier)) ^ n) z)
    obtain ⟨y, rfl⟩ := PT.restrictedToAlgHom_surjective w
    have h1 : ψh' y - z ∈ (I.map (algebraMap A B.carrier)) ^ n :=
      Ideal.Quotient.eq.mp ((hψhred y).trans hw)
    refine ⟨PT.restrictedToAlgHom y, Ideal.Quotient.eq.mpr ?_⟩
    show φT (PT.restrictedToAlgHom y) - z ∈ _
    rw [hfac y, show φh y - z = (φh y - ψh' y) + (ψh' y - z) by ring]
    exact add_mem (Ideal.pow_le_self hne (hφhd y)) (Ideal.pow_le_self (by omega) h1)
  have hTcomplete : IsAdicComplete (I.map (algebraMap A T.carrier)) T.carrier :=
    T.isAdicallyComplete
  have hMmap : (I.map (algebraMap A T.carrier)).map φT.toRingHom =
      I.map (algebraMap A B.carrier) := by
    rw [Ideal.map_map]
    congr 1
    ext y
    exact φT.commutes y
  have hhaus : IsHausdorff ((I.map (algebraMap A T.carrier)).map φT.toRingHom) B.carrier := by
    rw [hMmap]
    infer_instance
  have hφsurj : Function.Surjective φT :=
    surjective_of_mk_map_comp_surjective (I := I.map (algebraMap A T.carrier)) φT.toRingHom
      (by rwa [hMmap])
  -- the conormal annihilation, and Stacks 0ALR
  obtain ⟨c₂, hc₂⟩ := exists_pow_smul_cotangent_eq_bot_of_jacobianChart B P m hm b f hvanish
    ⟨b', hb'⟩ hrelations agen hagen c₁ f' φT hφsurj
  obtain ⟨D, _, _, hD, ⟨E⟩⟩ :=
    _root_.exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated A C B.carrier I
      φT hφsurj c₂ hc₂
  exact exists_finiteType_algEquiv_adicCompletion_of_algEquiv I E

end Main

end Rig

end
