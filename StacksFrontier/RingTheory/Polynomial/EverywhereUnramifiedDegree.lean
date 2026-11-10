module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import StacksFrontier.RingTheory.DedekindDomain.UnramifiedTraceDual
public import StacksFrontier.RingTheory.Polynomial.LaurentLatticeIntersection

/-!
# Extensions of `k(s)` unramified over `k[s]` and over `k[s⁻¹]`

Let `k ⊆ F` be fields and `s ∈ F` transcendental over `k`, with `F` a fraction field both of
`k[s]` and of `k[s⁻¹]`. Let `N / F` be finite separable and suppose that the integral closures of
`k[s]` and of `k[s⁻¹]` in `N` are unramified at every prime: `N` is the function field of a finite
étale cover of `𝐏¹_k`. Then `[N : F]` is at most the dimension over `k` of every finite-dimensional
`k`-subspace containing all elements of `N` integral over both `k[s]` and `k[s⁻¹]` (the global
functions on the cover). In particular, when these are only the constants, `N = F`: `𝐏¹` has no
nontrivial connected finite étale covers.

The proof chooses, by Smith normal form, `k[s]`- and `k[s⁻¹]`-bases of the two integral closures.
Their discriminants are units, that is, nonzero constants, because both integral closures are
self-dual for the trace (`mem_range_of_forall_traceForm_mem_range`). The count of global sections
is `Polynomial.card_le_finrank_of_coordLattice_inf_le`.

## Main results

* `Polynomial.exists_basis_discr_eq_algebraMap`: a basis of an everywhere unramified integral
  closure of `k[t]` with constant discriminant.
* `Polynomial.finrank_le_of_forall_isUnramifiedAt`: the degree bound.
-/

@[expose] public noncomputable section

open Module Polynomial

namespace Polynomial

variable {k F N : Type*} [Field k] [Field F] [Algebra k F] [Field N] [Algebra F N] [Algebra k N]
  [IsScalarTower k F N]

omit [Algebra k N] [IsScalarTower k F N] in
/-- If `x` is integral over `k[t⁻¹]`, then `t^D x` is integral over `k[t]` for some `D`. -/
theorem exists_pow_mul_isIntegral {t : F} (ht : t ≠ 0) {x : N}
    (hx : IsIntegral (Algebra.adjoin k {t⁻¹}) x) :
    ∃ D : ℕ, IsIntegral (Algebra.adjoin k {t}) (algebraMap F N (t ^ D) * x) := by
  obtain ⟨p, hpm, hpx⟩ := hx
  have hmem : ∀ z ∈ Algebra.adjoin k {t⁻¹}, ∃ q : k[X], aeval t⁻¹ q = z := fun z hz ↦ by
    rwa [Algebra.adjoin_singleton_eq_range_aeval] at hz
  choose q hq using fun i ↦ hmem _ (p.coeff i).2
  set D := ∑ i ∈ Finset.range (p.natDegree + 1), (q i).natDegree
  refine ⟨D, ?_⟩
  let ι : Algebra.adjoin k {t⁻¹} →+* F := algebraMap _ F
  let P : F[X] := scaleRoots (p.map ι) (t ^ D)
  have hPm : P.Monic := (monic_scaleRoots_iff _).mpr (hpm.map _)
  have hPlift : P ∈ lifts (algebraMap (Algebra.adjoin k {t}) F) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots, coeff_map, natDegree_map_eq_of_injective Subtype.val_injective]
    by_cases hi : i ≤ p.natDegree
    · rcases eq_or_lt_of_le hi with rfl | hlt
      · rw [hpm.coeff_natDegree, map_one, one_mul, tsub_self, pow_zero]
        exact ⟨1, map_one _⟩
      · have hdeg : (q i).natDegree ≤ D * (p.natDegree - i) := by
          calc (q i).natDegree ≤ D :=
                Finset.single_le_sum (f := fun i ↦ (q i).natDegree) (fun _ _ ↦ Nat.zero_le _)
                  (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
            _ ≤ D * (p.natDegree - i) := Nat.le_mul_of_pos_right _ (by omega)
        refine ⟨⟨_, pow_mul_aeval_inv_mem_adjoin (k := k) ht hdeg⟩, ?_⟩
        change t ^ (D * (p.natDegree - i)) * aeval t⁻¹ (q i) = _
        rw [hq, pow_mul, mul_comm]
        rfl
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), map_zero, zero_mul]
      exact ⟨0, map_zero _⟩
  obtain ⟨Q, hQmap, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hPlift hPm
  refine ⟨Q, hQm, ?_⟩
  have h1 : eval₂ (algebraMap (Algebra.adjoin k {t}) N) (algebraMap F N (t ^ D) * x) Q =
      eval₂ (algebraMap F N) (algebraMap F N (t ^ D) * x) P := by
    rw [← hQmap, eval₂_map, ← IsScalarTower.algebraMap_eq]
  rw [h1, scaleRoots_eval₂_mul, eval₂_map, ← IsScalarTower.algebraMap_eq, hpx, mul_zero]

variable (k)

/-- `k[t] ≅ k[X]` for `t` transcendental over `k`. -/
def adjoinSingletonEquiv {t : F} (ht : Transcendental k t) : k[X] ≃ₐ[k] Algebra.adjoin k {t} :=
  (AlgEquiv.ofInjective (aeval t) ((transcendental_iff_injective).mp ht)).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval k t).symm)

/-- `k[t]` is a principal ideal ring for `t` transcendental over `k`. -/
theorem isPrincipalIdealRing_adjoin {t : F} (ht : Transcendental k t) :
    IsPrincipalIdealRing (Algebra.adjoin k {t}) :=
  IsPrincipalIdealRing.of_surjective (adjoinSingletonEquiv k ht).toRingHom
    (adjoinSingletonEquiv k ht).surjective

omit [Algebra k N] [IsScalarTower k F N] in
/-- **A basis with constant discriminant.** If the integral closure of `k[t]` in `N` is unramified
at every prime, it has a `k[t]`-basis, which is an `F`-basis of `N`, whose discriminant is a
nonzero constant; coordinates of integral elements in this basis lie in `k[t]`. -/
theorem exists_basis_discr_eq_algebraMap {t : F} (ht : Transcendental k t)
    [IsFractionRing (Algebra.adjoin k {t}) F] [FiniteDimensional F N] [Algebra.IsSeparable F N]
    (hunr : ∀ (P : Ideal (integralClosure (Algebra.adjoin k {t}) N)) [P.IsPrime],
      Algebra.IsUnramifiedAt (Algebra.adjoin k {t}) P) :
    ∃ b : Basis (Fin (finrank F N)) F N, (∀ i, IsIntegral (Algebra.adjoin k {t}) (b i)) ∧
      (∀ x : N, IsIntegral (Algebra.adjoin k {t}) x →
        ∀ i, b.equivFun x i ∈ Algebra.adjoin k {t}) ∧
      ∃ α : k, α ≠ 0 ∧ Algebra.discr F b = algebraMap k F α := by
  classical
  set R := Algebra.adjoin k {t}
  have : IsPrincipalIdealRing R := isPrincipalIdealRing_adjoin k ht
  set B := integralClosure R N
  have : IsDedekindDomain B := integralClosure.isDedekindDomain R F N
  have : IsFractionRing B N := integralClosure.isFractionRing_of_finite_extension (A := R) F N
  have : Module.Finite R B := IsIntegralClosure.finite R F N B
  have : Module.Free R B := Module.free_of_finite_type_torsion_free'
  let b₀ := Module.Free.chooseBasis R B
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) N :=
    IsIntegralClosure.isLocalization R F N B
  let b₁ : Basis (Module.Free.ChooseBasisIndex R B) F N :=
    b₀.localizationLocalization F (nonZeroDivisors R) N
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R B) = finrank F N :=
    (Module.finrank_eq_card_basis b₁).symm
  let e := Fintype.equivFinOfCardEq hcard
  let b := b₁.reindex e
  have hb_apply : ∀ i, b i = algebraMap B N (b₀ (e.symm i)) := by
    intro i
    rw [Basis.reindex_apply, Basis.localizationLocalization_apply]
  have hcoord : ∀ y : B, ∀ i, b.equivFun (algebraMap B N y) i =
      algebraMap R F (b₀.repr y (e.symm i)) := by
    intro y i
    rw [Basis.equivFun_apply, Basis.repr_reindex_apply,
      Basis.localizationLocalization_repr_algebraMap]
  have hcoordR : ∀ x : N, IsIntegral R x → ∀ i, b.equivFun x i ∈ R := by
    intro x hx i
    have := hcoord ⟨x, hx⟩ i
    change b.equivFun x i = _ at this
    rw [this]
    exact (b₀.repr ⟨x, hx⟩ (e.symm i)).2
  have hbint : ∀ i, IsIntegral R (b i) := fun i ↦ by
    rw [hb_apply]
    exact (b₀ (e.symm i)).2
  refine ⟨b, hbint, hcoordR, ?_⟩
  -- the trace dual basis lies in `B`
  let bd := (Algebra.traceForm F N).dualBasis (traceForm_nondegenerate F N) b
  have hexpand : ∀ z : N, z = ∑ j, b.equivFun z j • b j := fun z ↦ (b.sum_equivFun z).symm
  have hdual : ∀ i j, Algebra.traceForm F N (bd i) (b j) = if j = i then 1 else 0 :=
    fun i j ↦ LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate F N) b i j
  have key : ∀ i (z : N), Algebra.traceForm F N (bd i) z = b.equivFun z i := by
    intro i z
    conv_lhs => rw [hexpand z]
    rw [map_sum]
    simp only [map_smul, hdual, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hbd : ∀ i, IsIntegral R (bd i) := by
    intro i
    obtain ⟨y, hy⟩ := mem_range_of_forall_traceForm_mem_range R F N B hunr (x := bd i) (by
      intro y
      rw [← Algebra.traceForm_apply, key, hcoord y i]
      exact ⟨_, rfl⟩)
    rw [← hy]
    exact y.2
  have htrace : ∀ x : N, IsIntegral R x → Algebra.trace F N x ∈ R := by
    intro x hx
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (Algebra.isIntegral_trace (L := F) (F := N) hx)
    rw [← hr]
    exact r.2
  let G : Matrix (Fin (finrank F N)) (Fin (finrank F N)) F := Algebra.traceMatrix F b
  let M : Matrix (Fin (finrank F N)) (Fin (finrank F N)) F :=
    Matrix.of fun i j ↦ b.equivFun (bd i) j
  have hMG : M * G = 1 := by
    ext i l
    have hsum : bd i = ∑ j, M i j • b j := hexpand (bd i)
    have h := hdual i l
    rw [hsum, map_sum, LinearMap.sum_apply] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply,
      show (if i = l then (1 : F) else 0) = if l = i then 1 else 0 from if_congr eq_comm rfl rfl,
      ← h]
    rfl
  have hGR : ∀ i j, G i j ∈ R := fun i j ↦ by
    simp only [G, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    exact htrace _ ((hbint i).mul (hbint j))
  have hMR : ∀ i j, M i j ∈ R := fun i j ↦ hcoordR _ (hbd i) j
  let GR : Matrix (Fin (finrank F N)) (Fin (finrank F N)) R := Matrix.of fun i j ↦ ⟨G i j, hGR i j⟩
  let MR : Matrix (Fin (finrank F N)) (Fin (finrank F N)) R := Matrix.of fun i j ↦ ⟨M i j, hMR i j⟩
  have hGmap : GR.map (algebraMap R F) = G := by ext; rfl
  have hMmap : MR.map (algebraMap R F) = M := by ext; rfl
  have hinj : Function.Injective (algebraMap R F) := Subtype.val_injective
  have hdet1 : MR.det * GR.det = 1 := by
    apply hinj
    rw [map_mul, map_one, RingHom.map_det, RingHom.map_det]
    change (MR.map (algebraMap R F)).det * (GR.map (algebraMap R F)).det = 1
    rw [hGmap, hMmap, ← Matrix.det_mul, hMG, Matrix.det_one]
  have hunit : IsUnit GR.det := IsUnit.of_mul_eq_one _ (by rwa [mul_comm])
  have hunit' : IsUnit ((adjoinSingletonEquiv k ht).symm GR.det) :=
    hunit.map (adjoinSingletonEquiv k ht).symm
  obtain ⟨α, hα, hαeq⟩ := Polynomial.isUnit_iff.mp hunit'
  refine ⟨α, hα.ne_zero, ?_⟩
  have hGdet : GR.det = algebraMap k R α := by
    rw [← (adjoinSingletonEquiv k ht).apply_symm_apply GR.det, ← hαeq, ← algebraMap_eq,
      AlgEquiv.commutes]
  rw [Algebra.discr_def]
  change G.det = _
  rw [← hGmap]
  refine (RingHom.map_det (algebraMap R F) GR).symm.trans ?_
  rw [hGdet, ← IsScalarTower.algebraMap_apply]

variable {k}

/-- **Function fields of finite étale covers of `𝐏¹`.** Let `s ∈ F` be transcendental over `k`,
with `F` a fraction field of `k[s]` and of `k[s⁻¹]`, and let `N / F` be finite separable such that
the integral closures of `k[s]` and of `k[s⁻¹]` in `N` are unramified at every prime. Then
`[N : F] ≤ dim_k W` for every finite-dimensional `k`-subspace `W` of `N` containing all elements
integral over both `k[s]` and `k[s⁻¹]`. -/
theorem finrank_le_of_forall_isUnramifiedAt {s : F} (hs : Transcendental k s)
    [IsFractionRing (Algebra.adjoin k {s}) F] [IsFractionRing (Algebra.adjoin k {s⁻¹}) F]
    [FiniteDimensional F N] [Algebra.IsSeparable F N]
    (h₀ : ∀ (P : Ideal (integralClosure (Algebra.adjoin k {s}) N)) [P.IsPrime],
      Algebra.IsUnramifiedAt (Algebra.adjoin k {s}) P)
    (h₁ : ∀ (P : Ideal (integralClosure (Algebra.adjoin k {s⁻¹}) N)) [P.IsPrime],
      Algebra.IsUnramifiedAt (Algebra.adjoin k {s⁻¹}) P)
    (W : Submodule k N) [FiniteDimensional k W]
    (hW : ∀ x : N, IsIntegral (Algebra.adjoin k {s}) x → IsIntegral (Algebra.adjoin k {s⁻¹}) x →
      x ∈ W) :
    finrank F N ≤ finrank k W := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs isAlgebraic_zero
  have hsi : Transcendental k s⁻¹ := fun h ↦ hs (IsAlgebraic.inv_iff.mp h)
  obtain ⟨b, hbint, hbR, α, hα, hb⟩ := exists_basis_discr_eq_algebraMap k hs h₀
  obtain ⟨c, hcint, hcS, β, -, hc⟩ := exists_basis_discr_eq_algebraMap k hsi h₁
  have hlaurent : ∀ {t u : F}, t * u = 1 → ∀ (b c : Basis (Fin (finrank F N)) F N),
      (∀ x : N, IsIntegral (Algebra.adjoin k {t}) x →
        ∀ i, b.equivFun x i ∈ Algebra.adjoin k {t}) →
      (∀ j, IsIntegral (Algebra.adjoin k {u}) (c j)) →
      ∀ i j, b.toMatrix c i j ∈ Algebra.adjoin k {t, u} := by
    intro t u htu b c hb hc i j
    have ht : t ≠ 0 := left_ne_zero_of_mul_eq_one htu
    obtain rfl : u = t⁻¹ := eq_inv_of_mul_eq_one_right htu
    obtain ⟨D, hD⟩ := exists_pow_mul_isIntegral ht (hc j)
    have h1 := hb _ hD i
    rw [← Algebra.smul_def, map_smul, Pi.smul_apply, smul_eq_mul] at h1
    rw [Basis.toMatrix_apply, ← Basis.equivFun_apply]
    have : b.equivFun (c j) i = t⁻¹ ^ D * (t ^ D * b.equivFun (c j) i) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ ht, one_pow, one_mul]
    rw [this]
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _) ?_
    exact Algebra.adjoin_mono (by simp) h1
  have hint : ∀ {t : F} (d : Basis (Fin (finrank F N)) F N) {x : N},
      (∀ i, IsIntegral (Algebra.adjoin k {t}) (d i)) →
      (∀ i, d.equivFun x i ∈ Algebra.adjoin k {t}) → IsIntegral (Algebra.adjoin k {t}) x := by
    intro t d x hd hx
    rw [← d.sum_equivFun x]
    refine IsIntegral.sum _ fun i _ ↦ ?_
    rw [Algebra.smul_def]
    exact (isIntegral_algebraMap (x := (⟨_, hx i⟩ : Algebra.adjoin k {t}))).mul (hd i)
  have := card_le_finrank_of_coordLattice_inf_le hs b c hα hb hc
    (hlaurent (mul_inv_cancel₀ hs0) b c hbR hcint)
    (fun i j ↦ Set.pair_comm s _ ▸ hlaurent (inv_mul_cancel₀ hs0) c b hcS hbint i j) W
    fun x hx ↦ hW x (hint b hbint (mem_coordLattice.mp (Submodule.mem_inf.mp hx).1))
      (hint c hcint (mem_coordLattice.mp (Submodule.mem_inf.mp hx).2))
  simpa using this

end Polynomial

end
