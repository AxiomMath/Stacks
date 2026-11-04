module

public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.BlockRepresentation
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.SquareZero
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.Universal

/-!
# The tangent space of a universal deformation ring under de Jong's conjecture

Let `R` be the universal deformation ring of `ρ₀ : π → GLₙ(𝐅_ℓ)` with determinant fixed to `δ`,
let `N ⊆ π` be a normal subgroup on which `ρ₀` is absolutely irreducible, and assume `ℓ ∤ n`.
Assume moreover that every continuous representation of `π` over `𝐅_ℓ⟦X⟧`, of any rank, has
finite image on `N`. Then the cotangent space `𝔪/(𝔪² + ℓR)` of `R` is finite.

Let `T = R/(𝔪² + ℓR)` and write the normalized pushforward of the universal representation to
`T` as `σ = ρ₀ + d`, where `d` has entries in the square-zero maximal ideal of `T`. Then:

* the entries of `d(g)` for `g ∈ N` span the maximal ideal of `T`: modulo the ideal they span,
  `σ` agrees with `ρ₀` on `N`, hence on `π`
  (`Matrix.GeneralLinearGroup.eq_map_of_eq_map_of_mem_normal`, which uses the fixed determinant
  and `ℓ ∤ n`), and the rigidity of the universal deformation then forces that ideal to be the
  maximal ideal;
* for an `𝐅_ℓ`-linear functional `μ` on `T` the map `b_μ = μ ∘ d` satisfies
  `b_μ(gh) = ρ₀(g) b_μ(h) + b_μ(g) ρ₀(h)`, so `[[ρ₀, ∑ₖ b_{μₖ} Xᵏ], [0, ρ₀]]` is a representation
  over `𝐅_ℓ⟦X⟧` for any sequence `μₖ`;
* if the maximal ideal of `T` were infinite-dimensional, the coordinate functionals of a basis
  would give such a representation whose finite image on `N` forces two distinct coordinate
  functionals to agree on the entries of `d` over `N`, hence on the whole maximal ideal, which is
  absurd.

## Main results

* `Deformation.IsUniversalFixedDeterminantDeformation.finite_quotient_sq_sup_span`: under de Jong's
  conjecture, `R/(𝔪² + ℓR)` is finite.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped PowerSeries.WithPiTopology

namespace Deformation.IsUniversalFixedDeterminantDeformation

universe u v

variable {ℓ n : ℕ} [Fact ℓ.Prime] {π : Type u} [Group π] [TopologicalSpace π]
  {ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)} {δ : π →ₜ* ℤ_[ℓ]ˣ}
  {R : Type v} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
  {reduce : R →+* ZMod ℓ} {ρuniv : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R}

section SquareZero

variable (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
  (I : Ideal R) [IsLocalRing (R ⧸ I)] [Algebra (ZMod ℓ) (R ⧸ I)]

include h in
/-- If `𝔪² ⊆ I`, the maximal ideal of `R ⧸ I` has square zero. -/
theorem mul_eq_zero_of_mem_maximalIdeal (hI : maximalIdeal R ^ 2 ≤ I) {x y : R ⧸ I}
    (hx : x ∈ maximalIdeal (R ⧸ I)) (hy : y ∈ maximalIdeal (R ⧸ I)) : x * y = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [h.mk_mem_maximalIdeal_quotient_iff] at hx hy
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact hI (pow_two (maximalIdeal R) ▸ Ideal.mul_mem_mul hx hy)

include h in
/-- Matrices with entries in a square-zero maximal ideal multiply to zero. -/
theorem matrix_mul_eq_zero_of_mem (hI : maximalIdeal R ^ 2 ≤ I)
    {X Y : Matrix (Fin n) (Fin n) (R ⧸ I)} (hX : ∀ i j, X i j ∈ maximalIdeal (R ⧸ I))
    (hY : ∀ i j, Y i j ∈ maximalIdeal (R ⧸ I)) : X * Y = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun k _ => h.mul_eq_zero_of_mem_maximalIdeal I hI (hX i k) (hY k j)

/-- The constant deformation `ρ₀` over `R ⧸ I`. -/
abbrev constRep (g : π) : Matrix (Fin n) (Fin n) (R ⧸ I) :=
  (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)).map (algebraMap (ZMod ℓ) (R ⧸ I))

/-- The deviation `d = σ - ρ₀` of the normalized pushforward from the constant deformation. -/
def deviation (g : π) : Matrix (Fin n) (Fin n) (R ⧸ I) :=
  (h.normalizedPushforward I g : Matrix (Fin n) (Fin n) (R ⧸ I)) - constRep (ρ₀ := ρ₀) I g

/-- The entries of the deviation lie in the maximal ideal of `R ⧸ I`. -/
theorem deviation_mem (g : π) (i j : Fin n) :
    h.deviation I g i j ∈ maximalIdeal (R ⧸ I) :=
  h.normalizedPushforward_sub_mem I g i j

omit [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R] [IsLocalRing (R ⧸ I)] in
/-- The constant deformation is multiplicative. -/
theorem constRep_mul (g g' : π) :
    constRep (ρ₀ := ρ₀) I (g * g') = constRep (ρ₀ := ρ₀) I g * constRep (ρ₀ := ρ₀) I g' := by
  simp only [constRep, map_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact Matrix.map_mul

/-- If `𝔪² ⊆ I`, the deviation satisfies `d(gg') = ρ₀(g) d(g') + d(g) ρ₀(g')`. -/
theorem deviation_mul (hI : maximalIdeal R ^ 2 ≤ I) (g g' : π) :
    h.deviation I (g * g') = constRep (ρ₀ := ρ₀) I g * h.deviation I g' +
      h.deviation I g * constRep (ρ₀ := ρ₀) I g' := by
  have e : (h.normalizedPushforward I (g * g') : Matrix (Fin n) (Fin n) (R ⧸ I)) =
      (constRep (ρ₀ := ρ₀) I g + h.deviation I g) * (constRep (ρ₀ := ρ₀) I g' +
        h.deviation I g') := by
    rw [map_mul, Matrix.GeneralLinearGroup.coe_mul, deviation, deviation]
    abel_nf
  have hz := h.matrix_mul_eq_zero_of_mem I hI (h.deviation_mem I g) (h.deviation_mem I g')
  rw [deviation, e, constRep_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hz]
  abel

/-- The functional `μ` applied entrywise to the deviation. -/
def deviationFunctional (μ : (R ⧸ I) →ₗ[ZMod ℓ] ZMod ℓ) (g : π) :
    Matrix (Fin n) (Fin n) (ZMod ℓ) :=
  (h.deviation I g).map μ

omit [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R] [IsLocalRing (R ⧸ I)] in
/-- `μ` commutes with left multiplication by constant matrices. -/
theorem map_functional_const_mul (μ : (R ⧸ I) →ₗ[ZMod ℓ] ZMod ℓ)
    (A : Matrix (Fin n) (Fin n) (ZMod ℓ)) (X : Matrix (Fin n) (Fin n) (R ⧸ I)) :
    (A.map (algebraMap (ZMod ℓ) (R ⧸ I)) * X).map μ = A * X.map μ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, ← Algebra.smul_def, map_smul,
    smul_eq_mul]

omit [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R] [IsLocalRing (R ⧸ I)] in
/-- `μ` commutes with right multiplication by constant matrices. -/
theorem map_functional_mul_const (μ : (R ⧸ I) →ₗ[ZMod ℓ] ZMod ℓ)
    (A : Matrix (Fin n) (Fin n) (ZMod ℓ)) (X : Matrix (Fin n) (Fin n) (R ⧸ I)) :
    (X * A.map (algebraMap (ZMod ℓ) (R ⧸ I))).map μ = X.map μ * A := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, mul_comm (X _ _),
    ← Algebra.smul_def, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- If `𝔪² ⊆ I`, the functional `μ` applied to the deviation is an upper block cocycle for
`ρ₀`. -/
theorem isUpperBlockCocycle_deviationFunctional (hI : maximalIdeal R ^ 2 ≤ I)
    (μ : (R ⧸ I) →ₗ[ZMod ℓ] ZMod ℓ) :
    IsUpperBlockCocycle ρ₀.toMonoidHom (h.deviationFunctional I μ) := fun g g' => by
  rw [deviationFunctional, h.deviation_mul I hI, Matrix.map_add _ (map_add μ)]
  rw [map_functional_const_mul, map_functional_mul_const]
  rfl

omit [IsLocalRing (R ⧸ I)] in
/-- The deviation functional of `μ - μ'` is the difference of those of `μ` and `μ'`. -/
theorem deviationFunctional_sub (μ μ' : (R ⧸ I) →ₗ[ZMod ℓ] ZMod ℓ) (g : π) :
    h.deviationFunctional I (μ - μ') g =
      h.deviationFunctional I μ g - h.deviationFunctional I μ' g := by
  ext i j; simp [deviationFunctional]

end SquareZero

/-- A local quotient of `R` in which `ℓ` vanishes has characteristic `ℓ`. -/
theorem charP_quotient (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (J : Ideal R) [IsLocalRing (R ⧸ J)] (hℓ : algebraMap ℤ_[ℓ] R ℓ ∈ J) :
    CharP (R ⧸ J) ℓ := by
  refine (CharP.charP_iff_prime_eq_zero (Fact.out : ℓ.Prime)).2 ?_
  rw [← map_natCast (algebraMap ℤ_[ℓ] (R ⧸ J)), ← Ideal.Quotient.mk_algebraMap,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hℓ

/-- `ℓ` lies in the maximal ideal of a universal deformation ring. -/
theorem algebraMap_mem_maximalIdeal
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) :
    algebraMap ℤ_[ℓ] R ℓ ∈ maximalIdeal R := by
  rw [← h.ker_reduce, RingHom.mem_ker, h.reduce_algebraMap, map_natCast, ZMod.natCast_self]

/-- A quotient of `R` by an ideal contained in the maximal ideal is local. -/
theorem isLocalRing_quotient_of_le
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) (J : Ideal R)
    (hJ : J ≤ maximalIdeal R) : IsLocalRing (R ⧸ J) :=
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- If `𝔪² ⊆ I`, the quotient `R ⧸ I` is complete for its maximal ideal. -/
theorem isAdicComplete_quotient_of_sq_le
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) (J : Ideal R)
    [IsLocalRing (R ⧸ J)] (hJ : maximalIdeal R ^ 2 ≤ J) :
    IsAdicComplete (maximalIdeal (R ⧸ J)) (R ⧸ J) := by
  refine isAdicComplete_of_pow_eq_bot _ (k := 2) ?_
  rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← Ideal.map_pow,
    eq_bot_iff, ← Ideal.map_quotient_self J]
  exact Ideal.map_mono hJ

/-- **The cotangent space under de Jong's conjecture.** Let `N` be a normal subgroup of `π` on
which `ρ₀` is absolutely irreducible, assume `ℓ ∤ n`, and assume that every continuous
representation of `π` over `𝐅_ℓ⟦X⟧`, of any rank, has finite image on `N`. Then
`R/(𝔪² + ℓR)` is finite. -/
theorem finite_quotient_sq_sup_span [IsTopologicalGroup π]
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (N : Subgroup π) [N.Normal] (hirr : IsAbsolutelyIrreducible fun g : N => ρ₀ g)
    (hn : ¬ ℓ ∣ n)
    (hconj : ∀ (m : ℕ) (ρ : π →ₜ* Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ))),
      (ρ '' (N : Set π)).Finite) :
    Finite (R ⧸ (maximalIdeal R ^ 2 ⊔ Ideal.span {algebraMap ℤ_[ℓ] R ℓ})) := by
  classical
  set I₀ := maximalIdeal R ^ 2 ⊔ Ideal.span {algebraMap ℤ_[ℓ] R ℓ}
  set T := R ⧸ I₀
  have hsqI₀ : maximalIdeal R ^ 2 ≤ I₀ := le_sup_left
  have hℓI₀ : algebraMap ℤ_[ℓ] R ℓ ∈ I₀ := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hI₀m : I₀ ≤ maximalIdeal R :=
    sup_le (Ideal.pow_le_self two_ne_zero)
      ((Ideal.span_singleton_le_iff_mem _).2 h.algebraMap_mem_maximalIdeal)
  have : IsLocalRing T := h.isLocalRing_quotient_of_le I₀ hI₀m
  have : CharP T ℓ := h.charP_quotient I₀ hℓI₀
  let : Algebra (ZMod ℓ) T := ZMod.algebra T ℓ
  set alg := algebraMap (ZMod ℓ) T
  set mk : R →+* T := Ideal.Quotient.mk I₀
  set d := h.deviation I₀
  have hd := h.deviation_mem I₀
  -- the ideal spanned by the deviations on `N`
  set Eset : Set T := {x | ∃ g ∈ N, ∃ i j, d g i j = x}
  have hEm : Eset ⊆ maximalIdeal T := by
    rintro _ ⟨g, -, i, j, rfl⟩; exact hd g i j
  set U : Ideal T := Ideal.span Eset
  have hUm : U ≤ maximalIdeal T := Ideal.span_le.2 hEm
  set I₁ : Ideal R := U.comap mk
  have hI₀₁ : I₀ ≤ I₁ := fun a ha => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]; exact U.zero_mem
  have hI₁m : I₁ ≤ maximalIdeal R := fun a ha =>
    (h.mk_mem_maximalIdeal_quotient_iff I₀ a).1 (hUm ha)
  have : IsLocalRing (R ⧸ I₁) := h.isLocalRing_quotient_of_le I₁ hI₁m
  have : CharP (R ⧸ I₁) ℓ := h.charP_quotient I₁ (hI₀₁ hℓI₀)
  let : Algebra (ZMod ℓ) (R ⧸ I₁) := ZMod.algebra (R ⧸ I₁) ℓ
  have hfactorU : ∀ x ∈ U, Ideal.Quotient.factor hI₀₁ x = 0 := fun x hx => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  have hfactor_alg : ∀ c, Ideal.Quotient.factor hI₀₁ (alg c) = algebraMap (ZMod ℓ) (R ⧸ I₁) c :=
    fun c => RingHom.congr_fun (Subsingleton.elim
      ((Ideal.Quotient.factor hI₀₁).comp alg) (algebraMap (ZMod ℓ) (R ⧸ I₁))) c
  have hn₁ : IsUnit (Fintype.card (Fin n) : R ⧸ I₁) := by
    rw [Fintype.card_fin, ← map_natCast (algebraMap (ZMod ℓ) (R ⧸ I₁))]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    rwa [ne_eq, ZMod.natCast_eq_zero_iff]
  have hN : ∀ g ∈ N, h.normalizedPushforward I₁ g =
      Matrix.GeneralLinearGroup.map (algebraMap (ZMod ℓ) (R ⧸ I₁)) (ρ₀ g) := fun g hg => by
    rw [← h.map_factor_normalizedPushforward I₀ hI₀₁]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
    have e : (h.normalizedPushforward I₀ g : Matrix (Fin n) (Fin n) T) i j =
        alg (ρ₀ g i j) + d g i j := by
      simp only [d, deviation, constRep, Matrix.sub_apply, Matrix.map_apply, alg]
      ring
    rw [e, map_add, hfactor_alg, hfactorU _ (Ideal.subset_span ⟨g, hg, i, j, rfl⟩), add_zero]
  have hrig := Matrix.GeneralLinearGroup.eq_map_of_eq_map_of_mem_normal N ρ₀.toMonoidHom hirr
    hn₁ (h.normalizedPushforward I₁) (h.normalizedPushforward_sub_mem I₁)
    (h.det_normalizedPushforward I₁) hN
  have hmI₁ : maximalIdeal R ≤ I₁ := h.maximalIdeal_le_of_conj_eq I₁
    (h.isAdicComplete_quotient_of_sq_le I₁ (hsqI₀.trans hI₀₁)) 1
    fun g => by rw [inv_one, one_mul, mul_one]; exact hrig g
  have hmU : maximalIdeal T ≤ U := fun x hx => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hmI₁ ((h.mk_mem_maximalIdeal_quotient_iff I₀ a).1 hx)
  -- `U` is the `𝐅_ℓ`-span of the deviations
  have hUspan : ∀ x ∈ U, x ∈ Submodule.span (ZMod ℓ) Eset := by
    intro x hx
    have hspanm : Submodule.span (ZMod ℓ) Eset ≤ (maximalIdeal T).restrictScalars (ZMod ℓ) :=
      Submodule.span_le.2 hEm
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul t y _ hy =>
      have hym : y ∈ maximalIdeal T := hspanm hy
      have ht : t - alg (h.quotientReduce I₀ t) ∈ maximalIdeal T :=
        h.sub_algebraMap_quotientReduce_mem I₀ t
      have : t • y = (h.quotientReduce I₀ t) • y := by
        rw [smul_eq_mul, Algebra.smul_def]
        have := h.mul_eq_zero_of_mem_maximalIdeal I₀ hsqI₀ ht hym
        rw [sub_mul, sub_eq_zero] at this
        exact this
      rw [this]
      exact Submodule.smul_mem _ _ hy
  -- a functional vanishing on the deviations over `N` vanishes on the maximal ideal
  have hvanish : ∀ μ : T →ₗ[ZMod ℓ] ZMod ℓ, (∀ g ∈ N, h.deviationFunctional I₀ μ g = 0) →
      ∀ x ∈ maximalIdeal T, μ x = 0 := by
    intro μ hμ x hx
    have hxs := hUspan x (hmU hx)
    clear hx
    induction hxs using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, hg, i, j, rfl⟩ := hy
      exact congrFun (congrFun (hμ g hg) i) j
    | zero => exact map_zero μ
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul c y _ hy => rw [map_smul, hy, smul_zero]
  -- the maximal ideal of `T` is finite
  set V : Submodule (ZMod ℓ) T := (maximalIdeal T).restrictScalars (ZMod ℓ)
  have hVfin : Finite V := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    let b := Module.Free.chooseBasis (ZMod ℓ) V
    have : Infinite (Module.Free.ChooseBasisIndex (ZMod ℓ) V) := by
      by_contra hfin
      rw [not_infinite_iff_finite] at hfin
      have : Module.Finite (ZMod ℓ) V := Module.Finite.of_basis b
      have : Finite V := Module.finite_of_finite (ZMod ℓ)
      exact not_finite V
    let ε := Infinite.natEmbedding (Module.Free.ChooseBasisIndex (ZMod ℓ) V)
    choose μ hμ using fun k => LinearMap.exists_extend (b.coord (ε k))
    let c : ℕ → π → Matrix (Fin n) (Fin n) (ZMod ℓ) := fun k => h.deviationFunctional I₀ (μ k)
    have hcoc : ∀ k, IsUpperBlockCocycle ρ₀.toMonoidHom (c k) := fun k =>
      h.isUpperBlockCocycle_deviationFunctional I₀ hsqI₀ (μ k)
    have hcont : ∀ k, Continuous (c k) := by
      intro k
      let : TopologicalSpace T := ⊥
      have : DiscreteTopology T := ⟨rfl⟩
      have hmk : Continuous mk := by
        rw [h.isAdicTopology]
        exact RingHom.continuous_adic_of_pow_le_ker _ mk 2 fun a ha => by
          rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]; exact hsqI₀ ha
      have hF : Continuous fun g => (Matrix.GeneralLinearGroup.map mk (ρuniv g), ρ₀ g) :=
        ((Matrix.GeneralLinearGroup.continuous_map mk hmk).comp ρuniv.continuous_toFun).prodMk
          ρ₀.continuous_toFun
      have : c k = (fun p : Matrix.GeneralLinearGroup (Fin n) T ×
          Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ) =>
          (((Matrix.GeneralLinearGroup.map alg h.reduce_rep.choose * p.1 *
            (Matrix.GeneralLinearGroup.map alg h.reduce_rep.choose)⁻¹ :
              Matrix.GeneralLinearGroup (Fin n) T) : Matrix (Fin n) (Fin n) T) -
            (p.2 : Matrix (Fin n) (Fin n) (ZMod ℓ)).map alg).map (μ k)) ∘
          fun g => (Matrix.GeneralLinearGroup.map mk (ρuniv g), ρ₀ g) := by
        funext g
        simp only [c, deviationFunctional, deviation, constRep, Function.comp_apply,
          normalizedPushforward_apply]
        rfl
      rw [this]
      exact continuous_of_discreteTopology.comp hF
    obtain ⟨k₁, k₂, hne, heq⟩ := exists_ne_eqOn_of_finite_image_blockRepresentation ρ₀ c hcoc
      hcont N (hconj (n + n) _)
    have hzero := hvanish (μ k₁ - μ k₂) fun g hg => by
      rw [deviationFunctional_sub, sub_eq_zero]; exact heq g hg
    have h1 := hzero _ (b (ε k₁)).2
    have e1 : ∀ k, μ k (b (ε k₁) : T) = b.coord (ε k) (b (ε k₁)) := fun k => by
      rw [← hμ k]; rfl
    rw [LinearMap.sub_apply, e1, e1, sub_eq_zero, Module.Basis.coord_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      Finsupp.single_apply, ite_eq_left rfl, ite_eq_right (fun e => hne (ε.injective e))] at h1
    exact one_ne_zero h1
  -- conclude
  refine Finite.of_injective (fun t : T => (h.quotientReduce I₀ t,
    (⟨t - alg (h.quotientReduce I₀ t), h.sub_algebraMap_quotientReduce_mem I₀ t⟩ : V))) ?_
  intro t t' htt'
  have h1 := congrArg Prod.fst htt'
  have h2 := congrArg (fun p => (p.2 : T)) htt'
  simp only at h1 h2
  rw [h1] at h2
  exact sub_left_injective h2

end Deformation.IsUniversalFixedDeterminantDeformation
