module

public import StacksFrontier.RingTheory.GeometricallyIrreducible.SeparableClosure.IrreducibilityDescent
import StacksCore.Tactic.EgaSgaAttribute

/-! # Tensor products over an algebraically closed base

The specialization argument showing that `Ebar ⊗[Ω] F'` is a domain for an algebraically
closed field `Ω` and a finitely generated field extension `F'/Ω`, and its consequence over a
perfect base. -/

@[expose] public section

open scoped TensorProduct

-- ===================================================================================
-- Ingredients for `algClosedBase_alg_closed_in_fracTensor` (specialization route).
-- ===================================================================================

/-- (sub-lemma 2) `Ω` algebraically closed ⟹ any `β ∈ Ebar` integral over `Ω` lies in `Ω`. -/
theorem algClosedBase_omega_alg_closed_in_Ebar
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω]
    (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (β : Ebar) (hβ : IsIntegral Ω β) :
    β ∈ Set.range (algebraMap Ω Ebar) := by
  have hirr : Irreducible (minpoly Ω β) := minpoly.irreducible hβ
  have hdeg : (minpoly Ω β).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible Ω hirr
  exact minpoly.mem_range_of_degree_eq_one Ω β hdeg

/-- (sub-lemma 3a) Over an infinite field, a nonzero `MvPolynomial` has a point where it is
nonzero. -/
@[sga "3 XIV 6.4" "special case", sga "3 XXIV 3.9.1" "infinite residue fields"]
theorem algClosedBase_mvpoly_exists_eval_ne_zero
    (Ω : Type*) [Field Ω] [Infinite Ω] (ι : Type*)
    (h : MvPolynomial ι Ω) (hh : h ≠ 0) :
    ∃ x : ι → Ω, MvPolynomial.eval x h ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hh (MvPolynomial.funext (fun x => by rw [hcon x, map_zero]))

/-- (sub-lemma 3b) If `g` vanishes wherever `a ≠ 0` (over an infinite field), and `a ≠ 0`, then `g
= 0`. -/
@[sga "3 XXIV 3.9.1" "infinite residue fields"]
theorem algClosedBase_mvpoly_eq_zero_of_vanish
    (Ω : Type*) [Field Ω] [Infinite Ω] (ι : Type*) (a g : MvPolynomial ι Ω)
    (ha : a ≠ 0)
    (hvanish : ∀ x : ι → Ω, MvPolynomial.eval x a ≠ 0 → MvPolynomial.eval x g = 0) :
    g = 0 := by
  have hag : a * g = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x a = 0
    · rw [hx, zero_mul]
    · rw [hvanish x hx, mul_zero]
  rcases mul_eq_zero.mp hag with h | h
  · exact absurd h ha
  · exact h

open MvPolynomial in
/-- (sub-lemma 6) The specialization map `Φ_λ = id_Ebar ⊗ (eval λ) : Ebar ⊗[Ω] P → Ebar`. -/
noncomputable def algClosedBase_myPhi (Ω : Type*) [Field Ω] (Ebar : Type*) [Field Ebar]
    [Algebra Ω Ebar] (ι : Type*) (lam : ι → Ω) :
    (Ebar ⊗[Ω] MvPolynomial ι Ω) →ₐ[Ω] Ebar :=
  (Algebra.TensorProduct.rid Ω Ω Ebar).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id Ω Ebar) (MvPolynomial.aeval lam))

open MvPolynomial in
/-- The specialization map sends `a ⊗ h` to `a` times the image of `h` evaluated at `lam`. -/
theorem algClosedBase_myPhi_tmul (Ω : Type*) [Field Ω] (Ebar : Type*) [Field Ebar]
    [Algebra Ω Ebar] (ι : Type*) (lam : ι → Ω) (a : Ebar) (h : MvPolynomial ι Ω) :
    algClosedBase_myPhi Ω Ebar ι lam (a ⊗ₜ[Ω] h)
      = a * algebraMap Ω Ebar (MvPolynomial.aeval lam h) := by
  show (Algebra.TensorProduct.rid Ω Ω Ebar)
    (Algebra.TensorProduct.map (AlgHom.id Ω Ebar) (MvPolynomial.aeval lam) (a ⊗ₜ[Ω] h)) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul,
    Algebra.smul_def, mul_comm]

/-- (toward sub-lemma 4/7) The structural map `P →ₐ[Ω] K₀` (`P → Frac P --e--> K₀`). -/
noncomputable def algClosedBase_jK (Ω : Type*) [Field Ω] (K₀ : Type*) [Field K₀] [Algebra Ω K₀]
    (ι : Type*) (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀) :
    MvPolynomial ι Ω →ₐ[Ω] K₀ :=
  e.toAlgHom.comp
    (IsScalarTower.toAlgHom Ω (MvPolynomial ι Ω) (FractionRing (MvPolynomial ι Ω)))

/-- The structural map `P →ₐ[Ω] K₀` sends `c` to the image under `e` of `c` viewed in
`Frac P`. -/
theorem algClosedBase_jK_apply (Ω : Type*) [Field Ω] (K₀ : Type*) [Field K₀] [Algebra Ω K₀]
    (ι : Type*) (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀) (c : MvPolynomial ι Ω) :
    algClosedBase_jK Ω K₀ ι e c
      = e (algebraMap (MvPolynomial ι Ω) (FractionRing (MvPolynomial ι Ω)) c) := rfl

/-- (toward sub-lemma 4/7) Single-element denominator clearing: every `k ∈ K₀` becomes `jK a` after
multiplying by a nonzero `jK c` (`c ∈ P`). -/
theorem algClosedBase_clear_one (Ω : Type*) [Field Ω] (K₀ : Type*) [Field K₀] [Algebra Ω K₀]
    (ι : Type*) (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀) (k : K₀) :
    ∃ (a : MvPolynomial ι Ω) (c : MvPolynomial ι Ω), c ≠ 0 ∧
      algClosedBase_jK Ω K₀ ι e c * k = algClosedBase_jK Ω K₀ ι e a := by
  obtain ⟨a, c, hc, hac⟩ := IsFractionRing.div_surjective (A := MvPolynomial ι Ω) (e.symm k)
  have hcne : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine ⟨a, c, hcne, ?_⟩
  set f := algebraMap (MvPolynomial ι Ω) (FractionRing (MvPolynomial ι Ω)) with hf
  have hfc : f c ≠ 0 :=
    (map_ne_zero_iff f (IsFractionRing.injective (MvPolynomial ι Ω)
      (FractionRing (MvPolynomial ι Ω)))).mpr hcne
  have h1 : f a = e.symm k * f c := by
    field_simp [f] at hac ⊢
    linear_combination hac
  rw [algClosedBase_jK_apply, algClosedBase_jK_apply, h1, map_mul, AlgEquiv.apply_symm_apply,
    mul_comm]

/-- (toward sub-lemma 4/7) The structural ring hom `B₀ = Ebar ⊗[Ω] P → B = Ebar ⊗[Ω] K₀`. -/
noncomputable def algClosedBase_incl (Ω : Type*) [Field Ω] (Ebar : Type*) [Field Ebar]
    [Algebra Ω Ebar] (K₀ : Type*) [Field K₀] [Algebra Ω K₀] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀) :
    (Ebar ⊗[Ω] MvPolynomial ι Ω) →ₐ[Ω] (Ebar ⊗[Ω] K₀) :=
  Algebra.TensorProduct.map (AlgHom.id Ω Ebar) (algClosedBase_jK Ω K₀ ι e)

/-- The structural map `Ebar ⊗[Ω] P → Ebar ⊗[Ω] K₀` sends `x ⊗ a` to `x ⊗ jK a`. -/
theorem algClosedBase_incl_tmul (Ω : Type*) [Field Ω] (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (K₀ : Type*) [Field K₀] [Algebra Ω K₀] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀) (x : Ebar) (a : MvPolynomial ι Ω) :
    algClosedBase_incl Ω Ebar K₀ ι e (x ⊗ₜ[Ω] a) = x ⊗ₜ[Ω] algClosedBase_jK Ω K₀ ι e a := by
  rw [algClosedBase_incl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- (toward sub-lemma 4/7) General denominator clearing: for any `b ∈ B` there is `0 ≠ c ∈ P` and
`b₀ ∈ B₀` with `incl b₀ = (1 ⊗ jK c) * b`. (So `B` is `B₀` localised at `P∖0`.) -/
theorem algClosedBase_clear_gen (Ω : Type*) [Field Ω] (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (K₀ : Type*) [Field K₀] [Algebra Ω K₀] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀) (b : Ebar ⊗[Ω] K₀) :
    ∃ (c : MvPolynomial ι Ω) (b₀ : Ebar ⊗[Ω] MvPolynomial ι Ω), c ≠ 0 ∧
      algClosedBase_incl Ω Ebar K₀ ι e b₀ = (1 ⊗ₜ[Ω] algClosedBase_jK Ω K₀ ι e c) * b := by
  induction b using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul x k =>
      obtain ⟨a, c, hc, hck⟩ := algClosedBase_clear_one Ω K₀ ι e k
      refine ⟨c, x ⊗ₜ[Ω] a, hc, ?_⟩
      rw [algClosedBase_incl_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hck]
  | add x y hx hy =>
      obtain ⟨cx, bx, hcx, hbx⟩ := hx
      obtain ⟨cy, by', hcy, hby⟩ := hy
      refine ⟨cx * cy, ((1 : Ebar) ⊗ₜ[Ω] cy) * bx + ((1 : Ebar) ⊗ₜ[Ω] cx) * by',
        mul_ne_zero hcx hcy, ?_⟩
      have key : (1 : Ebar) ⊗ₜ[Ω] algClosedBase_jK Ω K₀ ι e (cx * cy)
          = (1 ⊗ₜ[Ω] algClosedBase_jK Ω K₀ ι e cx)
              * ((1 : Ebar) ⊗ₜ[Ω] algClosedBase_jK Ω K₀ ι e cy) := by
        rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [map_add, map_mul, map_mul, algClosedBase_incl_tmul, algClosedBase_incl_tmul, hbx, hby,
        key]
      ring

/-- (helper) `algClosedBase_jK` is injective. -/
theorem algClosedBase_jK_injective (Ω : Type*) [Field Ω] (K₀ : Type*) [Field K₀] [Algebra Ω K₀]
    (ι : Type*) (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀) :
    Function.Injective (algClosedBase_jK Ω K₀ ι e) := by
  intro a b hab
  rw [algClosedBase_jK_apply, algClosedBase_jK_apply] at hab
  exact IsFractionRing.injective (MvPolynomial ι Ω) (FractionRing (MvPolynomial ι Ω))
    (e.injective hab)

/-- (helper) `algClosedBase_incl` is injective (flatness of `Ebar` over the field `Ω`). -/
theorem algClosedBase_incl_injective (Ω : Type*) [Field Ω] (Ebar : Type*) [Field Ebar]
    [Algebra Ω Ebar] (K₀ : Type*) [Field K₀] [Algebra Ω K₀] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀) :
    Function.Injective (algClosedBase_incl Ω Ebar K₀ ι e) := by
  exact TensorProduct.map_injective_of_flat_flat (AlgHom.id Ω Ebar).toLinearMap
    (algClosedBase_jK Ω K₀ ι e).toLinearMap Function.injective_id
    (algClosedBase_jK_injective Ω K₀ ι e)

/-- (helper) Bridge formula for `algClosedBase_myPhi`: the `i`-th `b`-coordinate (over `Ω`) of `Φ_λ
w` is `eval λ` of the `i`-th `P`-coordinate of `w` (the latter computed in `P ⊗[Ω] Ebar` via
`comm` and the `P`-basis `Algebra.TensorProduct.basis P b`). -/
theorem algClosedBase_myPhi_repr (Ω : Type*) [Field Ω] (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (ι : Type*) (b : Module.Basis (Module.Free.ChooseBasisIndex Ω Ebar) Ω Ebar) (lam : ι → Ω)
    (w : Ebar ⊗[Ω] MvPolynomial ι Ω) (i : Module.Free.ChooseBasisIndex Ω Ebar) :
    b.repr (algClosedBase_myPhi Ω Ebar ι lam w) i
      = MvPolynomial.eval lam
          ((Algebra.TensorProduct.basis (MvPolynomial ι Ω) b).repr
            (Algebra.TensorProduct.comm Ω Ebar (MvPolynomial ι Ω) w) i) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x h =>
      rw [algClosedBase_myPhi_tmul, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.basis_repr_tmul, MvPolynomial.aeval_eq_eval, mul_comm x,
        ← Algebra.smul_def, map_smul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul,
        MvPolynomial.algebraMap_eq, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, hx, hy]

/-- (helper) Bridge formula for `algClosedBase_incl`: the `i`-th `b`-coordinate (over `K₀`) of
`incl w` is `jK` of the `i`-th `P`-coordinate of `w`. -/
theorem algClosedBase_incl_repr (Ω : Type*) [Field Ω] (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (K₀ : Type*) [Field K₀] [Algebra Ω K₀] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀)
    (b : Module.Basis (Module.Free.ChooseBasisIndex Ω Ebar) Ω Ebar)
    (w : Ebar ⊗[Ω] MvPolynomial ι Ω) (i : Module.Free.ChooseBasisIndex Ω Ebar) :
    (Algebra.TensorProduct.basis K₀ b).repr
        (Algebra.TensorProduct.comm Ω Ebar K₀ (algClosedBase_incl Ω Ebar K₀ ι e w)) i
      = algClosedBase_jK Ω K₀ ι e
          ((Algebra.TensorProduct.basis (MvPolynomial ι Ω) b).repr
            (Algebra.TensorProduct.comm Ω Ebar (MvPolynomial ι Ω) w) i) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x h =>
      rw [algClosedBase_incl_tmul, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.basis_repr_tmul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul]
      congr 1
      rw [MvPolynomial.algebraMap_eq,
        show (MvPolynomial.C ((b.repr x) i) : MvPolynomial ι Ω)
          = algebraMap Ω (MvPolynomial ι Ω) ((b.repr x) i) from rfl,
        AlgHom.commutes]
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, hx, hy]

/-- (helper) A root of a `(d+1)`-term polynomial with nonzero leading coefficient is integral. -/
theorem algClosedBase_isIntegral_of_relation (Ω : Type*) [Field Ω] (Ebar : Type*) [Field Ebar]
    [Algebra Ω Ebar] (d : ℕ) (c : ℕ → Ω) (hcd : c d ≠ 0) (β : Ebar)
    (hroot : ∑ j ∈ Finset.range (d + 1), algebraMap Ω Ebar (c j) * β ^ j = 0) :
    IsIntegral Ω β := by
  rw [← isAlgebraic_iff_isIntegral]
  refine ⟨∑ j ∈ Finset.range (d+1), Polynomial.C (c j) * Polynomial.X ^ j, ?_, ?_⟩
  · intro hp
    apply hcd
    have := congrArg (fun q => Polynomial.coeff q d) hp
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Finset.sum_ite_eq'] using this
  · rw [map_sum, ← hroot]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]

/-- Given `u, v ∈ B₀ = Ebar ⊗[Ω] P` with `v ≠ 0` and a `P[X]`-relation `∑_{j≤d} a_j u^j v^{d-j} =
0` (`a_d ≠ 0`) holding in `B₀`, the quotient `u/v` is "constant", i.e. `incl u = (1 ⊗ₜ r) ·
incl v` in `B = Ebar ⊗[Ω] K₀` for some `r ∈ K₀`. Proof (specialization route): specialize `s ↦
λ ∈ Ω` via `Φ_λ = algClosedBase_myPhi` (Ebar-grading-respecting), use `IsAlgClosed Ω` to force
the specialized value `β(λ) ∈ Ω`, slice against an `Ω`-basis `{φ_i}` of `Ebar`
(`Algebra.TensorProduct.basis`) to get `u_i(λ) = β(λ) v_i(λ)`, hence `u_i v_{i*} = u_{i*} v_i`
in `P` (Zariski density over infinite `Ω`, sub-lemma `algClosedBase_mvpoly_eq_zero_of_vanish`),
whence `r := jK(u_{i*})/jK(v_{i*}) ∈ K₀` works. Uses ONLY `IsAlgClosed Ω` + the tensor
structure (the `IsDomain B` enters only through the caller's denominator clearing). Acyclic. -/
theorem algClosedBase_specialization_slice
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω]
    (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (K₀ : Type*) [Field K₀] [Algebra Ω K₀] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀)
    (u v : Ebar ⊗[Ω] MvPolynomial ι Ω) (hv : v ≠ 0)
    (d : ℕ) (a : ℕ → MvPolynomial ι Ω) (had : a d ≠ 0)
    (hrel : ∑ j ∈ Finset.range (d + 1),
        (1 ⊗ₜ[Ω] a j) * u ^ j * v ^ (d - j) = 0) :
    ∃ r : K₀, algClosedBase_incl Ω Ebar K₀ ι e u
      = (1 ⊗ₜ[Ω] r) * algClosedBase_incl Ω Ebar K₀ ι e v := by
  classical
  have : Infinite Ω := inferInstance
  set κ := Module.Free.ChooseBasisIndex Ω Ebar with hκ
  set b : Module.Basis κ Ω Ebar := Module.Free.chooseBasis Ω Ebar with hb
  -- coordinate maps into P
  set co : (Ebar ⊗[Ω] MvPolynomial ι Ω) → κ → MvPolynomial ι Ω := fun w i =>
    (Algebra.TensorProduct.basis (MvPolynomial ι Ω) b).repr
      (Algebra.TensorProduct.comm Ω Ebar (MvPolynomial ι Ω) w) i with hco
  have hcop : ∀ w i, co w i = (Algebra.TensorProduct.basis (MvPolynomial ι Ω) b).repr
      (Algebra.TensorProduct.comm Ω Ebar (MvPolynomial ι Ω) w) i := fun w i => by rw [hco]
  -- Some coordinate of v is nonzero
  have hvc_ne : ∃ i, co v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv
    have h0 : (Algebra.TensorProduct.comm Ω Ebar (MvPolynomial ι Ω) v) = 0 := by
      apply (Algebra.TensorProduct.basis (MvPolynomial ι Ω) b).repr.injective
      rw [map_zero]
      refine Finsupp.ext (fun i => ?_)
      rw [← hcop v i, hcon i, Finsupp.coe_zero, Pi.zero_apply]
    have hinj := (Algebra.TensorProduct.comm Ω Ebar (MvPolynomial ι Ω)).injective
    apply hinj
    rw [h0, map_zero]
  obtain ⟨istar, hvstar⟩ := hvc_ne
  -- Key polynomial identity: co u i * co v istar = co u istar * co v i  for all i.
  have hkey : ∀ i, co u i * co v istar = co u istar * co v i := by
    intro i
    have := algClosedBase_mvpoly_eq_zero_of_vanish Ω ι (a d * co v istar)
      (co u i * co v istar - co u istar * co v i) (mul_ne_zero had hvstar) ?_
    · exact sub_eq_zero.mp this
    · -- vanishing on the locus `a d * co v istar ≠ 0`
      intro lam hlam
      rw [map_mul] at hlam
      have hadlam : MvPolynomial.eval lam (a d) ≠ 0 := fun h => hlam (by rw [h, zero_mul])
      have hvstarlam : MvPolynomial.eval lam (co v istar) ≠ 0 := fun h => hlam (by rw [h, mul_zero])
      -- Apply Φ_λ to hrel
      set Φ := algClosedBase_myPhi Ω Ebar ι lam with hΦ
      set pu := Φ u with hpu
      set pv := Φ v with hpv
      have hpv_ne : pv ≠ 0 := by
        intro h
        apply hvstarlam
        have hb2 := algClosedBase_myPhi_repr Ω Ebar ι b lam v istar
        rw [← hΦ, ← hpv, h, ← hcop v istar] at hb2
        simpa using hb2.symm
      -- relation in Ebar after applying Φ
      have hΦrel : ∑ j ∈ Finset.range (d + 1),
          algebraMap Ω Ebar (MvPolynomial.eval lam (a j)) * pu ^ j * pv ^ (d - j) = 0 := by
        have := congrArg Φ hrel
        rw [map_sum, map_zero] at this
        rw [← this]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_mul, map_mul, map_pow, map_pow, ← hpu, ← hpv]
        congr 1
        congr 1
        rw [hΦ, algClosedBase_myPhi_tmul, one_mul, MvPolynomial.aeval_eq_eval]
      -- divide by pv^d : β = pu * pv⁻¹ satisfies the Ω-poly
      set β := pu * pv⁻¹ with hβ
      have hβrel : ∑ j ∈ Finset.range (d + 1),
          algebraMap Ω Ebar (MvPolynomial.eval lam (a j)) * β ^ j = 0 := by
        have hpvd : pv ^ d ≠ 0 := pow_ne_zero d hpv_ne
        apply mul_right_cancel₀ hpvd
        rw [zero_mul, ← hΦrel, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range, Nat.lt_succ_iff] at hj
        have hk : pv⁻¹ ^ j * pv ^ d = pv ^ (d - j) := by
          have h2 : pv ^ d = pv ^ j * pv ^ (d - j) := by rw [← pow_add, Nat.add_sub_cancel' hj]
          rw [h2, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hpv_ne), one_mul]
        rw [hβ, mul_pow, mul_assoc, mul_assoc, hk, mul_assoc]
      -- β integral over Ω, hence in Ω
      have hβint : IsIntegral Ω β :=
        algClosedBase_isIntegral_of_relation Ω Ebar d (fun j => MvPolynomial.eval lam (a j))
          hadlam β hβrel
      obtain ⟨cc, hcc⟩ := algClosedBase_omega_alg_closed_in_Ebar Ω Ebar β hβint
      -- pu = β * pv = cc • pv
      have hpu_eq : pu = cc • pv := by
        rw [Algebra.smul_def, hcc, hβ, mul_assoc, inv_mul_cancel₀ hpv_ne, mul_one]
      -- slice: eval lam (co u i) = cc * eval lam (co v i)
      have hslice : ∀ i, MvPolynomial.eval lam (co u i) = cc * MvPolynomial.eval lam (co v i) := by
        intro i
        have hu := algClosedBase_myPhi_repr Ω Ebar ι b lam u i
        have hvv := algClosedBase_myPhi_repr Ω Ebar ι b lam v i
        rw [← hΦ, ← hpu, ← hcop u i] at hu
        rw [← hΦ, ← hpv, ← hcop v i] at hvv
        rw [hpu_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, hvv] at hu
        rw [← hu]
      -- conclude eval lam g = 0
      rw [map_sub, map_mul, map_mul, hslice i, hslice istar]
      ring
  -- Define r and verify incl u = (1 ⊗ r) * incl v
  have hjvstar : algClosedBase_jK Ω K₀ ι e (co v istar) ≠ 0 := by
    exact (map_ne_zero_iff _ (algClosedBase_jK_injective Ω K₀ ι e)).2 hvstar
  set r : K₀ := algClosedBase_jK Ω K₀ ι e (co u istar) * (algClosedBase_jK Ω K₀ ι e (co v istar))⁻¹
    with hr
  refine ⟨r, ?_⟩
  -- jK (co u i) = r * jK (co v i)
  have hjK : ∀ i, algClosedBase_jK Ω K₀ ι e (co u i)
      = r * algClosedBase_jK Ω K₀ ι e (co v i) := by
    intro i
    have happ := congrArg (algClosedBase_jK Ω K₀ ι e) (hkey i)
    rw [map_mul, map_mul] at happ
    rw [hr]
    field_simp
    linear_combination happ
  -- reduce to coordinatewise via the K₀-basis & comm injectivity
  apply (Algebra.TensorProduct.comm Ω Ebar K₀).injective
  apply (Algebra.TensorProduct.basis K₀ b).repr.injective
  ext i
  rw [algClosedBase_incl_repr Ω Ebar K₀ ι e b u i, ← hcop u i]
  rw [map_mul]
  rw [Algebra.TensorProduct.comm_tmul]
  rw [show (r ⊗ₜ[Ω] (1 : Ebar)) * (Algebra.TensorProduct.comm Ω Ebar K₀)
      (algClosedBase_incl Ω Ebar K₀ ι e v)
      = r • (Algebra.TensorProduct.comm Ω Ebar K₀) (algClosedBase_incl Ω Ebar K₀ ι e v) from by
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
    algClosedBase_incl_repr Ω Ebar K₀ ι e b v i, ← hcop v i]
  exact hjK i

/-- Denominator clearing (Steps 1-2 / Part II.3): from `IsIntegral K₀ β` produce `u, v ∈ B₀`,
`v ≠ 0`, and a primitive `P[X]`-relation `∑_{j≤d} a_j u^j v^{d-j} = 0`
(`a_d ≠ 0`) in `B₀`, together with the `M`-identity `β · (incl v) = incl u` and `incl v ≠ 0` in
`M = Frac B`. (Clear `K₀ = Frac P` denominators of `β = u/v` and of `minpoly K₀ β` into `B₀ =
Ebar ⊗[Ω] P`; `B = (P∖0)⁻¹ B₀` via `algClosedBase_clear_gen`.) Acyclic — pure
IsFractionRing/IsLocalization + minpoly denominator clearing; no downstream lemma used. -/
theorem algClosedBase_clear_to_relation
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω]
    (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (K₀ : Type*) [Field K₀] [Algebra Ω K₀] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀)
    [IsDomain (Ebar ⊗[Ω] K₀)]
    [Algebra K₀ (Ebar ⊗[Ω] K₀)]
    (hAlg : ∀ k : K₀, algebraMap K₀ (Ebar ⊗[Ω] K₀) k = (1 : Ebar) ⊗ₜ[Ω] k)
    (β : FractionRing (Ebar ⊗[Ω] K₀)) (hβ : IsIntegral K₀ β) :
    ∃ (u v : Ebar ⊗[Ω] MvPolynomial ι Ω) (d : ℕ) (a : ℕ → MvPolynomial ι Ω),
      v ≠ 0 ∧ a d ≠ 0 ∧
      (∑ j ∈ Finset.range (d + 1), (1 ⊗ₜ[Ω] a j) * u ^ j * v ^ (d - j) = 0) ∧
      algebraMap (Ebar ⊗[Ω] K₀) (FractionRing (Ebar ⊗[Ω] K₀))
            (algClosedBase_incl Ω Ebar K₀ ι e v) ≠ 0 ∧
      β * algebraMap (Ebar ⊗[Ω] K₀) (FractionRing (Ebar ⊗[Ω] K₀))
            (algClosedBase_incl Ω Ebar K₀ ι e v)
        = algebraMap (Ebar ⊗[Ω] K₀) (FractionRing (Ebar ⊗[Ω] K₀))
            (algClosedBase_incl Ω Ebar K₀ ι e u) := by
  classical
  set incl := algClosedBase_incl Ω Ebar K₀ ι e with hincl
  set jK := algClosedBase_jK Ω K₀ ι e with hjK
  set aM := algebraMap (Ebar ⊗[Ω] K₀) (FractionRing (Ebar ⊗[Ω] K₀)) with haM
  -- injectivity facts
  have haM_inj : Function.Injective aM :=
    IsFractionRing.injective (Ebar ⊗[Ω] K₀) (FractionRing (Ebar ⊗[Ω] K₀))
  have hincl_inj : Function.Injective incl := algClosedBase_incl_injective Ω Ebar K₀ ι e
  have hjK_inj : Function.Injective jK := algClosedBase_jK_injective Ω K₀ ι e
  have hKB_inj : Function.Injective (algebraMap K₀ (Ebar ⊗[Ω] K₀)) :=
    (algebraMap K₀ (Ebar ⊗[Ω] K₀)).injective
  -- `1 ⊗ₜ k = algebraMap K₀ B k`
  have htmul (k : K₀) : (1 : Ebar) ⊗ₜ[Ω] k = algebraMap K₀ (Ebar ⊗[Ω] K₀) k := (hAlg k).symm
  -- `1 ⊗ₜ x ≠ 0` for `x ≠ 0`
  have htmul_ne (k : K₀) (hk : k ≠ 0) : (1 : Ebar) ⊗ₜ[Ω] k ≠ 0 := by
    rw [htmul]
    exact fun h => hk (hKB_inj (by rw [h, map_zero]))
  -- bridge: aM (1 ⊗ₜ k) = algebraMap K₀ M k
  have hbridge (k : K₀) : aM ((1 : Ebar) ⊗ₜ[Ω] k)
      = algebraMap K₀ (FractionRing (Ebar ⊗[Ω] K₀)) k := by
    rw [htmul, haM,
      ← IsScalarTower.algebraMap_apply K₀ (Ebar ⊗[Ω] K₀) (FractionRing (Ebar ⊗[Ω] K₀)) k]
  -- Step 1: β = aM u' / aM v'
  obtain ⟨u', v', hv'mem, hdiv⟩ :=
    IsFractionRing.div_surjective (A := Ebar ⊗[Ω] K₀) (K := FractionRing (Ebar ⊗[Ω] K₀)) β
  have hv'ne : v' ≠ 0 := nonZeroDivisors.ne_zero hv'mem
  have haMv'ne : aM v' ≠ 0 := (map_ne_zero_iff aM haM_inj).mpr hv'ne
  have hβdiv : β * aM v' = aM u' := by
    rw [← hdiv]
    exact div_mul_cancel₀ (aM u') haMv'ne
  -- Step 2: clear denominators of v'
  obtain ⟨cv, v₀, hcv, hv₀⟩ := algClosedBase_clear_gen Ω Ebar K₀ ι e v'
  -- w := (1 ⊗ₜ jK cv) * u'
  set w := ((1 : Ebar) ⊗ₜ[Ω] jK cv) * u' with hw
  -- Step 3: clear denominators of w
  obtain ⟨cw, u₀, hcw, hu₀⟩ := algClosedBase_clear_gen Ω Ebar K₀ ι e w
  -- final v
  set v : Ebar ⊗[Ω] MvPolynomial ι Ω := ((1 : Ebar) ⊗ₜ[Ω] cw) * v₀ with hv
  -- incl v = (1 ⊗ₜ jK cw) * incl v₀
  have hinclv : incl v = ((1 : Ebar) ⊗ₜ[Ω] jK cw) * incl v₀ := by
    rw [hv, map_mul, algClosedBase_incl_tmul]
  -- incl v ≠ 0
  have hinclvne : incl v ≠ 0 := by
    rw [hinclv, hv₀]
    exact mul_ne_zero (htmul_ne _ ((map_ne_zero_iff _ hjK_inj).2 hcw))
      (mul_ne_zero (htmul_ne _ ((map_ne_zero_iff _ hjK_inj).2 hcv)) hv'ne)
  -- aM (incl v) ≠ 0
  have hVne : aM (incl v) ≠ 0 := (map_ne_zero_iff aM haM_inj).mpr hinclvne
  -- the M-identity: β * aM (incl v) = aM (incl u₀)
  have hMid : β * aM (incl v) = aM (incl u₀) := by
    have hawval : aM w = aM ((1:Ebar) ⊗ₜ[Ω] jK cv) * aM u' := by
      rw [hw, map_mul]
    have h1 : β * aM (incl v₀) = aM w := by
      rw [hv₀, map_mul, hawval]
      linear_combination aM ((1:Ebar) ⊗ₜ[Ω] jK cv) * hβdiv
    have hu₀val : aM (incl u₀) = aM ((1:Ebar) ⊗ₜ[Ω] jK cw) * aM w := by
      rw [hu₀, map_mul]
    rw [hinclv, map_mul, hu₀val]
    linear_combination aM ((1:Ebar) ⊗ₜ[Ω] jK cw) * h1
  -- v ≠ 0 follows from incl v ≠ 0
  have hvne : v ≠ 0 := (map_ne_zero_iff _ hincl_inj).1 hinclvne
  -- minimal polynomial of β
  set p := minpoly K₀ β with hp
  have hpmon : p.Monic := minpoly.monic hβ
  set d := p.natDegree with hd
  have hpcoeffd : p.coeff d = 1 := hpmon.coeff_natDegree
  -- clear denominators of all coefficients with a common denominator
  have hcd : ∀ j : ℕ, ∃ (aj cj : MvPolynomial ι Ω), cj ≠ 0 ∧ jK cj * p.coeff j = jK aj :=
    fun j => algClosedBase_clear_one Ω K₀ ι e (p.coeff j)
  choose aj cj hcjne hcjeq using hcd
  -- common denominator
  set cc : MvPolynomial ι Ω := ∏ i ∈ Finset.range (d + 1), cj i with hcc
  have hccne : cc ≠ 0 := by
    rw [hcc]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hcjne i)
  -- the cleared coefficients
  set a : ℕ → MvPolynomial ι Ω :=
    fun j => (∏ i ∈ (Finset.range (d + 1)).erase j, cj i) * aj j with ha
  -- key: jK cc * p.coeff j = jK (a j) for j ∈ range (d+1)
  have hkey : ∀ j ∈ Finset.range (d + 1), jK cc * p.coeff j = jK (a j) := by
    intro j hj
    have hsplit : cc = (∏ i ∈ (Finset.range (d + 1)).erase j, cj i) * cj j := by
      rw [hcc, Finset.prod_erase_mul _ _ hj]
    rw [hsplit, ha, map_mul, map_mul]
    rw [mul_assoc, hcjeq j]
  -- a d ≠ 0
  have had : a d ≠ 0 := by
    have hdmem : d ∈ Finset.range (d + 1) := Finset.self_mem_range_succ d
    have : jK cc = jK (a d) := by
      have := hkey d hdmem
      rwa [hpcoeffd, mul_one] at this
    have had_eq : a d = cc := (hjK_inj this).symm
    rw [had_eq]; exact hccne
  refine ⟨u₀, v, d, a, hvne, had, ?_, hVne, hMid⟩
  -- the polynomial relation: prove via incl injective, then aM injective
  apply hincl_inj
  rw [map_zero]
  apply haM_inj
  rw [map_zero, map_sum, map_sum]
  -- aeval relation: ∑ p.coeff j • β^j = 0
  have haeval : ∑ j ∈ Finset.range (d + 1),
      algebraMap K₀ (FractionRing (Ebar ⊗[Ω] K₀)) (p.coeff j) * β ^ j = 0 := by
    have h0 : (Polynomial.aeval β) p = 0 := minpoly.aeval K₀ β
    rw [Polynomial.aeval_eq_sum_range] at h0
    rw [← h0]
    apply Finset.sum_congr rfl
    intro j _
    rw [Algebra.smul_def]
  -- main computation
  have key : ∀ j ∈ Finset.range (d + 1),
      aM (incl ((1 ⊗ₜ[Ω] a j) * u₀ ^ j * v ^ (d - j)))
        = aM ((1 : Ebar) ⊗ₜ[Ω] jK cc)
          * (algebraMap K₀ (FractionRing (Ebar ⊗[Ω] K₀)) (p.coeff j) * β ^ j)
          * aM (incl v) ^ d := by
    intro j hj
    have hjle : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    -- expand incl of the product
    have hexp : incl ((1 ⊗ₜ[Ω] a j) * u₀ ^ j * v ^ (d - j))
        = ((1 : Ebar) ⊗ₜ[Ω] jK (a j)) * incl u₀ ^ j * incl v ^ (d - j) := by
      rw [hincl, hjK]
      rw [map_mul, map_mul, map_pow, map_pow, algClosedBase_incl_tmul]
    rw [hexp, map_mul, map_mul, map_pow, map_pow]
    -- aM (incl u₀) = β * aM (incl v)
    rw [← hMid]
    rw [mul_pow]
    -- aM(1 ⊗ₜ jK (a j)) via bridge and hkey
    have hcoeff : aM ((1 : Ebar) ⊗ₜ[Ω] jK (a j))
        = aM ((1 : Ebar) ⊗ₜ[Ω] jK cc)
          * algebraMap K₀ (FractionRing (Ebar ⊗[Ω] K₀)) (p.coeff j) := by
      have hsplit2 : (1 : Ebar) ⊗ₜ[Ω] jK (a j)
          = ((1 : Ebar) ⊗ₜ[Ω] jK cc) * ((1 : Ebar) ⊗ₜ[Ω] p.coeff j) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← (hkey j hj)]
      rw [hsplit2, map_mul, hbridge, hbridge]
    rw [hcoeff]
    have hpow : aM (incl v) ^ j * aM (incl v) ^ (d - j) = aM (incl v) ^ d := by
      rw [← pow_add, Nat.add_sub_cancel' hjle]
    rw [← hpow]
    ring
  rw [Finset.sum_congr rfl key]
  -- factor out and use haeval
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [haeval, mul_zero, zero_mul]

/-- The main-lemma assembly, consuming Kernel A and Lemma B. The extra hypothesis `hAlg` states
that the `K₀`-algebra structure on `B` is the canonical `1 ⊗ₜ ·` one, the right algebra
structure; it is `rfl` at the call site `algClosedBase_core` and threaded through the consumers.
This is Stacks 037K/04KZ: the constant field `Ω(s)` is algebraically closed in `Ebar(s)`. -/
theorem algClosedBase_alg_closed_in_fracTensor
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω]
    (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (K₀ : Type*) [Field K₀] [Algebra Ω K₀] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀)
    [IsDomain (Ebar ⊗[Ω] K₀)]
    [Algebra K₀ (Ebar ⊗[Ω] K₀)]
    (hAlg : ∀ k : K₀, algebraMap K₀ (Ebar ⊗[Ω] K₀) k = (1 : Ebar) ⊗ₜ[Ω] k)
    (β : FractionRing (Ebar ⊗[Ω] K₀)) (hβ : IsIntegral K₀ β) :
    β ∈ Set.range (algebraMap K₀ (FractionRing (Ebar ⊗[Ω] K₀))) := by
  classical
  obtain ⟨u, v, d, a, hv, had, hrel, hvM, hquot⟩ :=
    algClosedBase_clear_to_relation Ω Ebar K₀ ι e hAlg β hβ
  obtain ⟨r, hr⟩ := algClosedBase_specialization_slice Ω Ebar K₀ ι e u v hv d a had hrel
  refine ⟨r, ?_⟩
  set M := FractionRing (Ebar ⊗[Ω] K₀) with hM
  set B := Ebar ⊗[Ω] K₀ with hB
  have hKr : algebraMap K₀ M r = algebraMap B M (algebraMap K₀ B r) :=
    IsScalarTower.algebraMap_apply K₀ B M r
  have hImg : algebraMap B M (algClosedBase_incl Ω Ebar K₀ ι e u)
      = algebraMap B M (algebraMap K₀ B r)
        * algebraMap B M (algClosedBase_incl Ω Ebar K₀ ι e v) := by
    rw [hr, map_mul]
    congr 2
    rw [hAlg r]
  rw [← hquot] at hImg
  rw [hKr]
  exact mul_right_cancel₀ hvM hImg.symm

/-- (A2-core-KERNEL-LD assembly). α separable over K₀ ⟹ integral ⟹ (kernel)
α ∈ range(algebraMap K₀ M) ⟹ minpoly K₀ α = X - C r has degree 1. -/
theorem algClosedBase_minpoly_natDegree_eq_one
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω]
    (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (K₀ : Type*) [Field K₀] [Algebra Ω K₀] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀)
    [IsDomain (Ebar ⊗[Ω] K₀)]
    [Algebra K₀ (Ebar ⊗[Ω] K₀)]
    (hAlg : ∀ k : K₀, algebraMap K₀ (Ebar ⊗[Ω] K₀) k = (1 : Ebar) ⊗ₜ[Ω] k)
    (α : FractionRing (Ebar ⊗[Ω] K₀)) (hα : IsSeparable K₀ α) :
    (minpoly K₀ α).natDegree = 1 := by
  have hint : IsIntegral K₀ α := hα.isIntegral
  obtain ⟨r, hr⟩ := algClosedBase_alg_closed_in_fracTensor Ω Ebar K₀ ι e hAlg α hint
  have hαr : α = algebraMap K₀ (FractionRing (Ebar ⊗[Ω] K₀)) r := hr.symm
  rw [hαr, minpoly.eq_X_sub_C (FractionRing (Ebar ⊗[Ω] K₀)) r]
  simp

/-- (A2-core-KERNEL assembly). An element `x` of `M` separable over
`K₀` has minpoly of degree 1 (kernel), hence lies in `Set.range (algebraMap K₀ M) = ⊥`. -/
theorem sepClosed_K0_in_M
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω]
    (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (K₀ : Type*) [Field K₀] [Algebra Ω K₀] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] K₀)
    [IsDomain (Ebar ⊗[Ω] K₀)]
    [Algebra K₀ (Ebar ⊗[Ω] K₀)]
    (hAlg : ∀ k : K₀, algebraMap K₀ (Ebar ⊗[Ω] K₀) k = (1 : Ebar) ⊗ₜ[Ω] k) :
    separableClosure K₀ (FractionRing (Ebar ⊗[Ω] K₀)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_separableClosure_iff] at hx
  rw [IntermediateField.mem_bot]
  have hdeg : (minpoly K₀ x).natDegree = 1 :=
    algClosedBase_minpoly_natDegree_eq_one Ω Ebar K₀ ι e hAlg x hx
  have hint : IsIntegral K₀ x := hx.isIntegral
  have hdeg1 : (minpoly K₀ x).degree = 1 := by
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), hdeg]; rfl
  obtain ⟨y, hy⟩ := minpoly.mem_range_of_degree_eq_one K₀ x hdeg1
  exact ⟨y, hy⟩

/-- (A2-core-CORE) The B/M-construction glue, stated with an OPAQUE
transcendental base `Kt` (a plain field type) to dodge the FractionRing-of-subtype instance
diamond. Given `Ω` alg-closed, `Ebar/Ω`, a purely transcendental `Kt/Ω` (`e`), `Ebar ⊗[Ω] Kt` a
domain, and `F'/Kt` finite separable, concludes `IsDomain (Ebar ⊗[Ω] F')`. Chain (informal
Steps A + wrap-up): `B := Ebar ⊗[Ω] Kt` is a domain, `M := Frac B`, `M ⊗[Kt] F'` is a FIELD
(`tensorSep_finite_isField'` using `sepClosed_K0_in_M`), `B ⊗[Kt] F' ↪ M ⊗[Kt] F'` (flatness of
the localization `B ↪ M`, so a subring of a field is a domain), and `B ⊗[Kt] F' ≅ Ebar ⊗[Ω] F'`
(base-change associativity `cancelBaseChange`). ACYCLIC: invokes only `sepClosed_K0_in_M`,
`tensorSep_finite_isField'`, and Mathlib; no `geomPure_*`/`tensorAlgClosed_*`. -/
theorem algClosedBase_core
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω]
    (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (Kt : Type*) [Field Kt] [Algebra Ω Kt] (ι : Type*)
    (e : FractionRing (MvPolynomial ι Ω) ≃ₐ[Ω] Kt)
    [IsDomain (Ebar ⊗[Ω] Kt)]
    (F' : Type*) [Field F'] [Algebra Ω F'] [Algebra Kt F'] [IsScalarTower Ω Kt F']
    [Algebra.IsSeparable Kt F'] [FiniteDimensional Kt F'] :
    IsDomain (Ebar ⊗[Ω] F') := by
  let algKtB : Algebra Kt (Ebar ⊗[Ω] Kt) := Algebra.TensorProduct.rightAlgebra
  set B := Ebar ⊗[Ω] Kt with hB
  have hsc : separableClosure Kt (FractionRing B) = ⊥ :=
    sepClosed_K0_in_M Ω Ebar Kt ι e (fun _ => rfl)
  have hMfield : IsField ((FractionRing B) ⊗[Kt] F') :=
    tensorSep_finite_isField' Kt (FractionRing B) hsc F'
  let : Field ((FractionRing B) ⊗[Kt] F') := hMfield.toField
  have hMdom : IsDomain ((FractionRing B) ⊗[Kt] F') := Field.isDomain
  have hBF'dom : IsDomain (B ⊗[Kt] F') := by
    let ψ : B →ₐ[Kt] (FractionRing B) := IsScalarTower.toAlgHom Kt B (FractionRing B)
    have hψinj : Function.Injective ψ := IsFractionRing.injective B (FractionRing B)
    let Φ : (B ⊗[Kt] F') →ₐ[Kt] ((FractionRing B) ⊗[Kt] F') :=
      Algebra.TensorProduct.map ψ (AlgHom.id Kt F')
    have hΦinj : Function.Injective Φ :=
      TensorProduct.map_injective_of_flat_flat ψ.toLinearMap (AlgHom.id Kt F').toLinearMap
        hψinj Function.injective_id
    exact Function.Injective.isDomain Φ.toRingHom hΦinj
  have eglue : (Ebar ⊗[Ω] Kt) ⊗[Kt] F' ≃+* Ebar ⊗[Ω] F' := by
    have hmap : ∀ x : Kt, (algebraMap Kt (Ebar ⊗[Ω] Kt)) x = 1 ⊗ₜ[Ω] x := fun x => rfl
    have einner : (Ebar ⊗[Ω] Kt) ≃ₐ[Kt] (Kt ⊗[Ω] Ebar) :=
      AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm Ω Ebar Kt).toRingEquiv)
        (by intro x; rw [hmap]; simp)
    have e0 := Algebra.TensorProduct.comm Kt (Ebar ⊗[Ω] Kt) F'
    have e1 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := Kt) (A₁ := F')) einner
    have e2 := Algebra.TensorProduct.cancelBaseChange Ω Kt Kt F' Ebar
    have e3 := Algebra.TensorProduct.comm Ω F' Ebar
    exact (((e0.trans e1).trans e2).toRingEquiv).trans e3.toRingEquiv
  exact eglue.symm.toMulEquiv.isDomain (B ⊗[Kt] F')

/-- For an algebraically closed `Ω`, an extension `Ebar/Ω`, and a finitely generated field
extension `F'/Ω`, the ring `Ebar ⊗[Ω] F'` is a domain. -/
@[ega "IV 4.3.2" "special case", ega "IV 4.3.6" "special case", ega "IV 4.3.9" "special case"]
theorem algClosedBase_tensor_isDomain
    (Ω : Type*) [Field Ω] [IsAlgClosed Ω]
    (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar]
    (F' : Type*) [Field F'] [Algebra Ω F']
    (hfg : (⊤ : IntermediateField Ω F').FG) :
    IsDomain (Ebar ⊗[Ω] F') := by
  -- base; Galois-descent irreducibility of the primitive-element minpoly + free⟹torsion-free
  -- localization embedding into the field K[X]/(f).)
  -- ASSEMBLY (no own open goals): Ω alg-closed ⟹ perfect ⟹ separating transcendence basis `s`;
  -- `Kt := Frac(MvPolynomial s Ω)` purely transcendental, `F'/Kt` finite separable (transported
  -- from the subtype `K₀ = adjoin Ω s` via `efield`); `Ebar ⊗[Ω] Kt` a domain
  -- (`finite_separableClosure_kernel_aux_domain`); finish via the diamond-free
  -- `algClosedBase_core`.
  have : PerfectField Ω := inferInstance
  have hEFT : Algebra.EssFiniteType Ω F' := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨s, htb, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField Ω F'
  -- Subtype K₀ used ONLY to obtain the F'-side instances (separable, finite over the
  -- transcendental base).  The FractionRing/tensor work happens over the PLAIN field `Kt`.
  set K₀ := IntermediateField.adjoin Ω (↑s : Set F') with hK₀
  have h1 := htb.isAlgebraic
  have hsepI : Algebra.IsSeparable ↥K₀ F' := hsep
  have halg : Algebra.IsAlgebraic ↥K₀ F' := by
    constructor; intro x
    rw [hK₀, IntermediateField.isAlgebraic_adjoin_iff]
    have hx := h1.isAlgebraic x
    have heq : Set.range (Subtype.val : (↑s:Set F')→F') = (↑s : Set F') := Subtype.range_coe
    exact heq ▸ hx
  have hEFTk : Algebra.EssFiniteType ↥K₀ F' := Algebra.EssFiniteType.of_comp Ω ↥K₀ F'
  have hfinK0 : Module.Finite ↥K₀ F' := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have hai : AlgebraicIndependent Ω (Subtype.val : (↑s:Set F')→F') := htb.left
  have hadj : IntermediateField.adjoin Ω (Set.range (Subtype.val : (↑s:Set F')→F')) = K₀ := by
    rw [hK₀, Subtype.range_coe]
  have efield : FractionRing (MvPolynomial (↑s:Set F') Ω) ≃ₐ[Ω] ↥K₀ :=
    hai.aevalEquivField.trans (IntermediateField.equivOfEq hadj)
  -- The PLAIN transcendental base field Kt and the transport of F'-structure along efield.
  set Kt := FractionRing (MvPolynomial (↑s:Set F') Ω) with hKt
  let algKtF' : Algebra Kt F' := RingHom.toAlgebra ((algebraMap ↥K₀ F').comp efield.toRingHom)
  have hKtmap : ∀ c : Kt, (algebraMap Kt F') c = (algebraMap ↥K₀ F') (efield c) := fun c => rfl
  have hstΩ : IsScalarTower Ω Kt F' := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    rw [hKtmap (algebraMap Ω Kt x), AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply Ω ↥K₀ F']
  have hsepKt : Algebra.IsSeparable Kt F' :=
    Algebra.IsSeparable.of_equiv_equiv efield.symm.toRingEquiv (RingEquiv.refl F')
      (by ext c; change (algebraMap Kt F') (efield.symm c) = (algebraMap ↥K₀ F') c
          rw [hKtmap, AlgEquiv.apply_symm_apply])
  have hfinKt : FiniteDimensional Kt F' := by
    show Module.Finite Kt F'
    rw [Module.finite_def, Submodule.fg_def]
    obtain ⟨b, hb⟩ : (⊤ : Submodule ↥K₀ F').FG := (Module.finite_def.mp hfinK0)
    refine ⟨(b : Set F'), b.finite_toSet, ?_⟩
    rw [eq_top_iff]
    intro x _
    have hxK0 : x ∈ Submodule.span ↥K₀ (b : Set F') := by rw [hb]; trivial
    refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span Kt (b : Set F'))
      ?_ ?_ ?_ ?_ hxK0
    · intro y hy; exact Submodule.subset_span hy
    · exact Submodule.zero_mem _
    · intro y z _ _ hy hz; exact Submodule.add_mem _ hy hz
    · intro a y _ hy
      have hrw : a • y = (efield.symm a) • y := by
        rw [Algebra.smul_def, Algebra.smul_def, hKtmap, AlgEquiv.apply_symm_apply]
      rw [hrw]; exact Submodule.smul_mem _ _ hy
  -- B := Ebar ⊗[Ω] Kt is a domain (the localized polynomial ring base case).
  have hBdom : IsDomain (Ebar ⊗[Ω] Kt) :=
    finite_separableClosure_kernel_aux_domain Ω (↑s:Set F') Ebar
  -- Finish via the diamond-free core.
  exact algClosedBase_core Ω Ebar Kt (↑s : Set F') (AlgEquiv.refl) F'
--
/-- (A2-core) ASSEMBLY: base-change associativity reduces `Ebar ⊗[P] L'` to `Ebar ⊗[Ω] F'` (`F' :=
Ω ⊗[P] L'`, a FIELD by `hF`); `F'/Ω` is f.g. (`algClosure_tensor_fg`); then the alg-closed-base
kernel `algClosedBase_tensor_isDomain` finishes. -/
theorem tensorAlgClosed_algClosedBase_isDomain
    (P : Type*) [Field P]
    (Ω : Type*) [Field Ω] [Algebra P Ω] [IsAlgClosed Ω]
    (Ebar : Type*) [Field Ebar] [Algebra Ω Ebar] [Algebra P Ebar] [IsScalarTower P Ω Ebar]
    [IsAlgClosed Ebar]
    (L' : Type*) [Field L'] [Algebra P L']
    (hfg : (⊤ : IntermediateField P L').FG)
    (hF : IsField (Ω ⊗[P] L')) :
    IsDomain (Ebar ⊗[P] L') := by
  -- closed base.  Ω alg-closed ⟹ Ω alg-closed in F':=Ω⊗[P]L' ⟹ geometrically irreducible;
  -- Ω alg-closed ⟹ perfect ⟹ F'/Ω separable ⟹ geometrically reduced.  hF essential, hfg used.)
  let : Field (Ω ⊗[P] L') := hF.toField
  -- Reduction 1: Ebar ⊗[Ω] (Ω ⊗[P] L') ≃ₐ[Ebar] Ebar ⊗[P] L' via cancelBaseChange.
  have e : (Ebar ⊗[Ω] (Ω ⊗[P] L')) ≃ₐ[Ebar] (Ebar ⊗[P] L') :=
    Algebra.TensorProduct.cancelBaseChange P Ω Ebar Ebar L'
  suffices h : IsDomain (Ebar ⊗[Ω] (Ω ⊗[P] L')) by
    exact e.symm.toMulEquiv.isDomain (Ebar ⊗[Ω] (Ω ⊗[P] L'))
  have hfgF : (⊤ : IntermediateField Ω (Ω ⊗[P] L')).FG := algClosure_tensor_fg P Ω L' hfg hF
  exact algClosedBase_tensor_isDomain Ω Ebar (Ω ⊗[P] L') hfgF
--
/-- (A2) ASSEMBLY: take `Ω := ↥(algebraicClosure P Ebar)` (algebraically closed since it is the
algebraic closure of `P` inside the algebraically closed `Ebar`; separable algebraic over the
perfect `P`). `Ω ⊗[P] L'` is a field (A2-Claim1); feed it to the alg-closed-base core
(A2-core). -/
@[ega "IV 4.3.6" "special case"]
theorem tensorAlgClosed_perfectBase_isDomain
    (P : Type*) [Field P] [PerfectField P]
    (Ebar : Type*) [Field Ebar] [Algebra P Ebar] [IsAlgClosed Ebar]
    (L' : Type*) [Field L'] [Algebra P L']
    (hfg : (⊤ : IntermediateField P L').FG)
    (hsc : separableClosure P L' = ⊥) :
    IsDomain (Ebar ⊗[P] L') := by
  -- is legitimate; geometrically irreducible AND geometrically reduced ⟹ domain).
  set Ω : Type _ := ↥(algebraicClosure P Ebar) with hΩ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := P) (K := Ω)
  have : Algebra.IsSeparable P Ω := inferInstance
  have : Algebra.IsAlgebraic P Ω := inferInstance
  have hF : IsField (Ω ⊗[P] L') :=
    perfectBase_algClosure_tensor_isField P Ω L' hsc
  exact tensorAlgClosed_algClosedBase_isDomain P Ω Ebar L' hfg hF
