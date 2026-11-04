module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionCoordinates
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorHorizontal

/-!
# The round-trip comparison of [Stacks, Lemma 60.17.5, Tag 07L5]

Let `(M, ∇)` be a pair over `D`, let `ρ : D → D` be a ring endomorphism and let
`ξ_i = x_i - ρ(x_i)`. The comparison

`c_{id_D, ρ} : M ⟶ M ⊗^∧_{D, ρ} D,    m ↦ ∑_K ξ^{[K]} ⊗ θ_K(m)`

of the proof of [Stacks, Proposition 60.17.4, Tag 07JH] is formalized abstractly: for a
`p`-adically complete target `N` with a `ρ`-semilinear map `ι : M → N` having the universal
property of the completed base change and a connection with `∇_N(ι m) = ∑_i ι(θ_i m) ⊗ d(ρ x_i)`,
the Taylor sum

`Φ(m) = ∑_K ξ^{[K]} • ι(θ_K m)`

is a `D`-linear bijection (`Crystalline.taylorRoundTripEquiv`), whose inverse is the Taylor sum
`∑_K (-ξ)^{[K]} • θ_K` in the other direction extended along the universal property, and it is
**horizontal**, that is, compatible with the connections (`Crystalline.coordOp_taylorRoundTrip`).

## Main definitions

* `Crystalline.taylorRoundTrip` — the comparison `Φ` as a `D`-linear map.
* `Crystalline.taylorRoundTripEquiv` — the comparison as a `D`-linear equivalence.

## Main results

* `Crystalline.coordOp_taylorRoundTrip` — **the comparison is horizontal**: it commutes with the
  coordinate operators, the compatibility with connections whose proof
  [Stacks, Lemma 60.17.5, Tag 07L5] omits.
* `Crystalline.CompletedConnection.exists_baseChange_lift` and
  `Crystalline.CompletedConnection.baseChangeCarrier_ext` — the universal property of the
  completed base change `M ⊗̂_D D'` for semilinear maps into complete modules.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u uI

namespace Crystalline

/-! ### The universal property of the completed base change -/

namespace CompletedConnection

section UniversalProperty

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (M : Type u) [AddCommGroup M] [Module D M] {R : Type u} [CommRing R] (τ : D' →+* R)
  {N : Type u} [AddCommGroup N] [Module R N]

/-- The uncompleted lift `c' ⊗ m ↦ τ(c') • φ(m)` of a semilinear map along a base change. -/
def baseChangeLiftRaw (φ : M →+ N)
    (hφ : ∀ (c : D) (m : M), φ (c • m) = τ (algebraMap D D' c) • φ m) :
    D' ⊗[D] M →+ N :=
  TensorProduct.liftAddHom
    { toFun := fun c' ↦
        { toFun := fun m ↦ τ c' • φ m
          map_zero' := by rw [_root_.map_zero, smul_zero]
          map_add' := fun m m' ↦ by rw [_root_.map_add, smul_add] }
      map_zero' := by ext; simp
      map_add' := fun c c' ↦ by ext; simp [add_smul] }
    fun c c' m ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, hφ, smul_smul, Algebra.smul_def, map_mul]
      rw [mul_comm]

/-- **The universal property of the completed base change, existence**: a semilinear map into a
`p`-adically complete module extends along `m ↦ 1 ⊗ m`. -/
theorem exists_baseChange_lift (hN : IsAdicComplete (pAdicIdeal (A := R) p) N) (φ : M →+ N)
    (hφ : ∀ (c : D) (m : M), φ (c • m) = τ (algebraMap D D' c) • φ m) :
    ∃ ψ : baseChangeCarrier p D D' M →+ N,
      (∀ (c' : D') (x : baseChangeCarrier p D D' M), ψ (c' • x) = τ c' • ψ x) ∧
        ∀ m : M, ψ (baseChangeInclusion p D D' M m) = φ m := by
  set lam := baseChangeLiftRaw D D' M τ φ hφ with hlam
  set e := AdicCompletion.ofLinearEquiv (pAdicIdeal (A := R) p) N
  set ψ : baseChangeCarrier p D D' M →+ N :=
    (e.symm.toLinearMap.toAddMonoidHom).comp (PAdicCompletion.mapAddHom p D' R lam) with hψ
  have hψof : ∀ y : D' ⊗[D] M, ψ (AdicCompletion.of (pAdicIdeal (A := D') p) _ y) = lam y := by
    intro y
    simp only [hψ, AddMonoidHom.coe_comp, Function.comp_apply, PAdicCompletion.mapAddHom_of]
    exact AdicCompletion.ofLinearEquiv_symm_of _ _
  have hlam_smul : ∀ (c' : D') (y : D' ⊗[D] M), lam (c' • y) = τ c' • lam y := by
    intro c' y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      simp [hlam, baseChangeLiftRaw, smul_smul]
    | add y y' hy hy' => rw [smul_add, _root_.map_add, hy, hy', _root_.map_add, smul_add]
  refine ⟨ψ, fun c' x ↦ ?_, fun m ↦ ?_⟩
  · have := addMonoidHom_ext_adicCompletion p hN.toIsHausdorff
      (f := ψ.comp (DistribSMul.toAddMonoidHom _ c'))
      (g := (DistribSMul.toAddMonoidHom N (τ c')).comp ψ) fun y ↦ by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply,
          DistribSMul.toAddMonoidHom_apply]
        rw [← map_smul, hψof, hψof, hlam_smul]
    exact DFunLike.congr_fun this x
  · rw [baseChangeInclusion_apply, hψof]
    simp [hlam, baseChangeLiftRaw]

/-- **The universal property of the completed base change, uniqueness**: two semilinear additive
maps into a `p`-adically separated module agreeing on `m ↦ 1 ⊗ m` agree. -/
theorem baseChangeCarrier_ext (hN : IsHausdorff (pAdicIdeal (A := R) p) N)
    {ψ ψ' : baseChangeCarrier p D D' M →+ N}
    (hψ : ∀ (c' : D') (x : baseChangeCarrier p D D' M), ψ (c' • x) = τ c' • ψ x)
    (hψ' : ∀ (c' : D') (x : baseChangeCarrier p D D' M), ψ' (c' • x) = τ c' • ψ' x)
    (h : ∀ m : M, ψ (baseChangeInclusion p D D' M m) = ψ' (baseChangeInclusion p D D' M m)) :
    ψ = ψ' := by
  refine addMonoidHom_ext_adicCompletion p hN fun y ↦ ?_
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c m =>
    rw [of_tmul_eq_smul_inclusion, hψ, hψ', h]
  | add y y' hy hy' => rw [_root_.map_add, _root_.map_add, _root_.map_add, hy, hy']

end UniversalProperty

end CompletedConnection

/-! ### Reindexing the differentiated Taylor series -/

section Reindex

variable {ι : Type uI} [Fintype ι] [DecidableEq ι] {X : Type u} [AddCommGroup X]

/-- **The reindexing `K = K' + e_i`** of the differentiated Taylor series over a downward closed
finite set `R` of multi-indices: the pairs `(K, i)` with `K ∈ R` and `k_i ≥ 1` correspond to the
pairs `(K', i)` with `K' + e_i ∈ R`. -/
theorem sum_support_sub_single_eq (R : Finset (ι →₀ ℕ)) (hR : ∀ K ∈ R, ∀ L ≤ K, L ∈ R)
    (f : (ι →₀ ℕ) → ι → X) :
    ∑ K ∈ R, ∑ i ∈ K.support, f (K - Finsupp.single i 1) i =
      ∑ i, ∑ K ∈ R.filter (fun K ↦ K + Finsupp.single i 1 ∈ R), f K i := by
  have h1 : ∀ K : ι →₀ ℕ, ∑ i ∈ K.support, f (K - Finsupp.single i 1) i =
      ∑ i, if K i ≠ 0 then f (K - Finsupp.single i 1) i else 0 := by
    intro K
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext i
    simp [Finsupp.mem_support_iff]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun K ↦ K - Finsupp.single i 1) (fun K ↦ K + Finsupp.single i 1)
    ?_ ?_ ?_ ?_ ?_
  · intro K hK
    obtain ⟨hKR, hKi⟩ := Finset.mem_filter.mp hK
    refine Finset.mem_filter.mpr ⟨hR K hKR _ tsub_le_self, ?_⟩
    rwa [tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hKi))]
  · intro K hK
    obtain ⟨-, hKi⟩ := Finset.mem_filter.mp hK
    refine Finset.mem_filter.mpr ⟨hKi, ?_⟩
    simp [Finsupp.add_apply]
  · intro K hK
    obtain ⟨-, hKi⟩ := Finset.mem_filter.mp hK
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hKi))
  · intro K _
    exact add_tsub_cancel_right K _
  · intro K _
    rfl

end Reindex

/-! ### The comparison -/

/-- The negative of a family of elements of the divided power ideal stays in the ideal. -/
private theorem neg_mem_ideal_family {D : DividedPowerRing.{u}} {ι : Type uI}
    {xi : ι → (D : Type u)} (hxi : ∀ i, xi i ∈ D.ideal) (i : ι) : (-xi) i ∈ D.ideal := by
  simpa using D.ideal.neg_mem (hxi i)

/-- A linear map `φ` whose composite with `incl` is the Taylor sum for `eta` sends the Taylor sum
for `zeta` with `zeta + eta = 0` to the inclusion `incl'`. -/
private theorem map_completeTaylorSum_eq_of_comp (p : ℕ) (D : DividedPowerRing.{u}) {ι : Type uI}
    {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
    {P : Type u} [AddCommGroup P] [Module (D : Type u) P]
    {Q : Type u} [AddCommGroup Q] [Module (D : Type u) Q]
    {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}
    (hfin : ∀ (n : ℕ) (m : M),
      {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite)
    (hP : IsPAdicallyComplete p D P) (hQ : IsPAdicallyComplete p D Q)
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hthAdd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (incl : M →+ P) (incl' : M →+ Q) {zeta eta : ι → (D : Type u)}
    (hzeta : ∀ i, zeta i ∈ D.ideal) (heta : ∀ i, eta i ∈ D.ideal) (hsum : zeta + eta = 0)
    (φ : P →ₗ[(D : Type u)] Q)
    (hcomp : ∀ m, φ (incl m) = completeTaylorSum p D thetaPow incl' eta hfin hQ m)
    (m : M) : φ (completeTaylorSum p D thetaPow incl zeta hfin hP m) = incl' m := by
  classical
  rw [map_taylorSum p D hfin hP hQ, show φ.toAddMonoidHom.comp incl = AddMonoidHom.mk'
      (completeTaylorSum p D thetaPow incl' eta hfin hQ)
      (taylorSum_add p D incl' eta hfin hQ hfamM hthAdd) from AddMonoidHom.ext hcomp,
    taylorSum_taylorSum p D hfin hQ hfamM hthAdd incl' hzeta
    heta, hsum, taylorSum_zero_family p D hfin hQ hfamM]

section RoundTrip

variable (p : ℕ) (D : DividedPowerRing.{u}) {ι : Type u} [Fintype ι] [DecidableEq ι]
  {Omega : Type u} [AddCommGroup Omega] [Module (D : Type u) Omega]
  (b : Module.Basis ι (D : Type u) Omega) {d : D.carrier → Omega}
  (x : ι → (D : Type u)) (hbx : ∀ i, b i = d (x i))
  {M : Type u} [AddCommGroup M] [Module (D : Type u) M] (hM : IsPAdicallyComplete p D M)
  (nablaM : CompletedConnection p D Omega d M)
  {thetaPow : (ι →₀ ℕ) → (M → M)}
  (hfamM : IsThetaMonomialFamily M (coordOp p b hM nablaM) thetaPow)
  (hfin : ∀ (n : ℕ) (m : M),
    {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite)
  {N : Type u} [AddCommGroup N] [Module (D : Type u) N] (hN : IsPAdicallyComplete p D N)
  (ρ : (D : Type u) →+* (D : Type u)) (incl : M →ₛₗ[ρ] N)
  (xi : ι → (D : Type u)) (hxi : ∀ i, xi i ∈ D.ideal)

/-- **The round-trip comparison** `Φ(m) = ∑_K ξ^{[K]} • ι(θ_K m)`, as an additive map. -/
def taylorRoundTripAdd : M →+ N :=
  AddMonoidHom.mk' (completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN)
    (taylorSum_add p D incl.toAddMonoidHom xi hfin hN hfamM (coordOp_add p b hM nablaM))

/-- The value of `Crystalline.taylorRoundTripAdd`. -/
theorem taylorRoundTripAdd_apply (m : M) :
    taylorRoundTripAdd p D b hM nablaM hfamM hfin hN ρ incl xi m =
      completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN m := rfl

variable {delta : ι → (D.carrier → D.carrier)} {deltaPow : (ι →₀ ℕ) → (D.carrier → D.carrier)}
  (hfamD : IsThetaMonomialFamily (D : Type u) delta deltaPow)
  (hdelta : ∀ (i : ι) (a : (D : Type u)), delta i a = b.repr (d a) i)
  (htay : ∀ (a : (D : Type u)) (n : ℕ), ∃ T : Finset (ι →₀ ℕ),
    (∀ J ∉ T, deltaPow J a ∈ pAdicIdeal (A := (D : Type u)) p ^ n) ∧
      a - ∑ J ∈ T, ρ (deltaPow J a) * taylorMonomial D xi J ∈
        pAdicIdeal (A := (D : Type u)) p ^ n)

include hfamD hdelta htay hxi in
/-- **The round-trip comparison is `D`-linear.** -/
theorem taylorRoundTripAdd_smul (a : (D : Type u)) (m : M) :
    taylorRoundTripAdd p D b hM nablaM hfamM hfin hN ρ incl xi (a • m) =
      a • taylorRoundTripAdd p D b hM nablaM hfamM hfin hN ρ incl xi m :=
  taylorSum_smul p D incl.toAddMonoidHom xi hfin hN (RingHom.id _) ρ
    (fun c m ↦ incl.map_smulₛₗ c m) hfamM hfamD (coordOp_add p b hM nablaM)
    (fun i a m ↦ by rw [coordOp_smul, hdelta]) hxi htay a m

/-- **The round-trip comparison** `Φ(m) = ∑_K ξ^{[K]} • ι(θ_K m)`, as a `D`-linear map. -/
def taylorRoundTrip : M →ₗ[(D : Type u)] N where
  toFun := taylorRoundTripAdd p D b hM nablaM hfamM hfin hN ρ incl xi
  map_add' := map_add _
  map_smul' := taylorRoundTripAdd_smul p D b hM nablaM hfamM hfin hN ρ incl xi hxi hfamD hdelta htay

/-- The value of `Crystalline.taylorRoundTrip`. -/
theorem taylorRoundTrip_apply (m : M) :
    taylorRoundTrip p D b hM nablaM hfamM hfin hN ρ incl xi hxi hfamD hdelta htay m =
      completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN m := rfl

end RoundTrip

/-! ### The inverse comparison -/

section Inverse

variable (p : ℕ) (D : DividedPowerRing.{u}) {ι : Type u} [Fintype ι] [DecidableEq ι]
  {Omega : Type u} [AddCommGroup Omega] [Module (D : Type u) Omega]
  (b : Module.Basis ι (D : Type u) Omega) {d : D.carrier → Omega}
  {M : Type u} [AddCommGroup M] [Module (D : Type u) M] (hM : IsPAdicallyComplete p D M)
  (nablaM : CompletedConnection p D Omega d M)
  {thetaPow : (ι →₀ ℕ) → (M → M)}
  (hfamM : IsThetaMonomialFamily M (coordOp p b hM nablaM) thetaPow)
  (hfin : ∀ (n : ℕ) (m : M),
    {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite)
  {N : Type u} [AddCommGroup N] [Module (D : Type u) N] (hN : IsPAdicallyComplete p D N)
  (ρ : (D : Type u) →+* (D : Type u)) (incl : M →ₛₗ[ρ] N)
  (xi : ι → (D : Type u)) (hxi : ∀ i, xi i ∈ D.ideal)
  {delta : ι → (D.carrier → D.carrier)} {deltaPow : (ι →₀ ℕ) → (D.carrier → D.carrier)}
  (hfamD : IsThetaMonomialFamily (D : Type u) delta deltaPow)
  (hdelta : ∀ (i : ι) (a : (D : Type u)), delta i a = b.repr (d a) i)
  (htay : ∀ (a : (D : Type u)) (n : ℕ), ∃ T : Finset (ι →₀ ℕ),
    (∀ J ∉ T, deltaPow J a ∈ pAdicIdeal (A := (D : Type u)) p ^ n) ∧
      a - ∑ J ∈ T, ρ (deltaPow J a) * taylorMonomial D xi J ∈
        pAdicIdeal (A := (D : Type u)) p ^ n)
  (htay' : ∀ (a : (D : Type u)) (n : ℕ), ∃ T : Finset (ι →₀ ℕ),
    (∀ J ∉ T, deltaPow J a ∈ pAdicIdeal (A := (D : Type u)) p ^ n) ∧
      ρ a - ∑ J ∈ T, deltaPow J a * taylorMonomial D (-xi) J ∈
        pAdicIdeal (A := (D : Type u)) p ^ n)

/-- **The Taylor sum in the reverse direction**, `m ↦ ∑_K (-ξ)^{[K]} • θ_K m`, on `M` itself. -/
def taylorBack : M →+ M :=
  AddMonoidHom.mk' (completeTaylorSum p D thetaPow (AddMonoidHom.id M) (-xi) hfin hM)
    (taylorSum_add p D (AddMonoidHom.id M) (-xi) hfin hM hfamM (coordOp_add p b hM nablaM))

include hxi hfamD hdelta htay' in
/-- **The reverse Taylor sum is `ρ`-semilinear.** -/
theorem taylorBack_smul (a : (D : Type u)) (m : M) :
    taylorBack p D b hM nablaM hfamM hfin xi (a • m) =
      ρ a • taylorBack p D b hM nablaM hfamM hfin xi m :=
  taylorSum_smul p D (AddMonoidHom.id M) (-xi) hfin hM ρ (RingHom.id _)
    (fun _ _ ↦ rfl) hfamM hfamD (coordOp_add p b hM nablaM)
    (fun i a m ↦ by rw [coordOp_smul, hdelta]) (neg_mem_ideal_family hxi) htay' a m

variable (huniv : ∀ φ : M →+ M, (∀ (c : (D : Type u)) (m : M), φ (c • m) = ρ c • φ m) →
    ∃ ψ : N →ₗ[(D : Type u)] M, ∀ m, ψ (incl m) = φ m)
  (hext : ∀ f g : N →ₗ[(D : Type u)] N, (∀ m, f (incl m) = g (incl m)) → f = g)

/-- **The inverse comparison** `N → M`, the extension of the reverse Taylor sum along the
universal property of `ι : M → N`. -/
def taylorRoundTripInv : N →ₗ[(D : Type u)] M :=
  (huniv (taylorBack p D b hM nablaM hfamM hfin xi)
    (taylorBack_smul p D b hM nablaM hfamM hfin ρ xi hxi hfamD hdelta htay')).choose

/-- The inverse comparison extends the reverse Taylor sum. -/
theorem taylorRoundTripInv_incl (m : M) :
    taylorRoundTripInv p D b hM nablaM hfamM hfin ρ incl xi hxi hfamD hdelta htay' huniv
        (incl m) = taylorBack p D b hM nablaM hfamM hfin xi m :=
  (huniv (taylorBack p D b hM nablaM hfamM hfin xi)
    (taylorBack_smul p D b hM nablaM hfamM hfin ρ xi hxi hfamD hdelta htay')).choose_spec m

/-- **The inverse comparison is a left inverse**: `Ψ (Φ m) = m`. -/
theorem taylorRoundTripInv_taylorRoundTrip (m : M) :
    taylorRoundTripInv p D b hM nablaM hfamM hfin ρ incl xi hxi hfamD hdelta htay' huniv
        (taylorRoundTrip p D b hM nablaM hfamM hfin hN ρ incl xi hxi hfamD hdelta htay m) = m :=
  map_completeTaylorSum_eq_of_comp p D hfin hN hM hfamM (coordOp_add p b hM nablaM)
    incl.toAddMonoidHom (AddMonoidHom.id M) hxi (neg_mem_ideal_family hxi) (add_neg_cancel xi) _
    (taylorRoundTripInv_incl p D b hM nablaM hfamM hfin ρ incl xi hxi hfamD hdelta htay' huniv) m

include hext in
/-- **The inverse comparison is a right inverse**: `Φ (Ψ z) = z`. -/
theorem taylorRoundTrip_taylorRoundTripInv (z : N) :
    taylorRoundTrip p D b hM nablaM hfamM hfin hN ρ incl xi hxi hfamD hdelta htay
        (taylorRoundTripInv p D b hM nablaM hfamM hfin ρ incl xi hxi hfamD hdelta htay' huniv
          z) = z := by
  have h := hext ((taylorRoundTrip p D b hM nablaM hfamM hfin hN ρ incl xi hxi hfamD hdelta
      htay).comp (taylorRoundTripInv p D b hM nablaM hfamM hfin ρ incl xi hxi hfamD hdelta htay'
        huniv)) LinearMap.id fun m ↦ by
    rw [LinearMap.comp_apply, taylorRoundTripInv_incl]
    exact map_completeTaylorSum_eq_of_comp p D hfin hM hN hfamM (coordOp_add p b hM nablaM)
      (AddMonoidHom.id M) incl.toAddMonoidHom (neg_mem_ideal_family hxi) hxi (neg_add_cancel xi) _
      (fun _ ↦ rfl) m
  exact DFunLike.congr_fun h z

/-- **The round-trip comparison as a `D`-linear equivalence** `M ≃ N`. -/
def taylorRoundTripEquiv : M ≃ₗ[(D : Type u)] N :=
  LinearEquiv.ofLinearMap
    (taylorRoundTrip p D b hM nablaM hfamM hfin hN ρ incl xi hxi hfamD hdelta htay)
    (taylorRoundTripInv p D b hM nablaM hfamM hfin ρ incl xi hxi hfamD hdelta htay' huniv)
    (LinearMap.ext fun z ↦ taylorRoundTrip_taylorRoundTripInv p D b hM nablaM hfamM hfin hN ρ
      incl xi hxi hfamD hdelta htay htay' huniv hext z)
    (LinearMap.ext fun m ↦ taylorRoundTripInv_taylorRoundTrip p D b hM nablaM hfamM hfin hN ρ
      incl xi hxi hfamD hdelta htay htay' huniv m)

/-- The equivalence `Crystalline.taylorRoundTripEquiv` is the round-trip comparison. -/
@[simp] theorem taylorRoundTripEquiv_apply (m : M) :
    taylorRoundTripEquiv p D b hM nablaM hfamM hfin hN ρ incl xi hxi hfamD hdelta htay htay'
        huniv hext m =
      taylorRoundTrip p D b hM nablaM hfamM hfin hN ρ incl xi hxi hfamD hdelta htay m := rfl

end Inverse

/-! ### Horizontality -/

section Horizontality

variable (p : ℕ) (D : DividedPowerRing.{u}) {ι : Type u} [Fintype ι] [DecidableEq ι]
  {Omega : Type u} [AddCommGroup Omega] [Module (D : Type u) Omega]
  (b : Module.Basis ι (D : Type u) Omega) {d : D.carrier → Omega}
  {M : Type u} [AddCommGroup M] [Module (D : Type u) M] (hM : IsPAdicallyComplete p D M)
  (nablaM : CompletedConnection p D Omega d M)
  {thetaPow : (ι →₀ ℕ) → (M → M)}
  (hfamM : IsThetaMonomialFamily M (coordOp p b hM nablaM) thetaPow)
  (hfin : ∀ (n : ℕ) (m : M),
    {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite)
  {N : Type u} [AddCommGroup N] [Module (D : Type u) N] (hN : IsPAdicallyComplete p D N)
  (nablaN : CompletedConnection p D Omega d N)
  (ρ : (D : Type u) →+* (D : Type u)) (incl : M →ₛₗ[ρ] N)
  (x : ι → (D : Type u)) (hbx : ∀ i, b i = d (x i))
  (xi : ι → (D : Type u))
  (hdxi : ∀ i, d (x i) = d (ρ (x i)) + d (xi i))
  (hdmono : ∀ K : ι →₀ ℕ, d (taylorMonomial D xi K) =
    ∑ i ∈ K.support, taylorMonomial D xi (K - Finsupp.single i 1) • d (xi i))
  (hnablaN : ∀ m : M, nablaN (incl m) =
    toCompletedTensor p D Omega N (∑ i, incl (coordOp p b hM nablaM i m) ⊗ₜ[(D : Type u)]
      d (ρ (x i))))

include hbx hdxi hdmono hnablaN in
/-- **The round-trip comparison commutes with the coordinate operators**:
`θ^N_j (Φ m) = Φ (θ_j m)`. -/
theorem coordOp_taylorRoundTrip (j : ι) (m : M) :
    coordOp p b hN nablaN j (taylorRoundTripAdd p D b hM nablaM hfamM hfin hN ρ incl xi m) =
      taylorRoundTripAdd p D b hM nablaM hfamM hfin hN ρ incl xi (coordOp p b hM nablaM j m) := by
  classical
  set θ := coordOp p b hM nablaM with hθ
  set θN := coordOp p b hN nablaN with hθN
  set c : ι → ι → (D : Type u) := fun i k ↦ b.repr (d (ρ (x i))) k with hc
  set e : ι → ι →₀ ℕ := fun i ↦ Finsupp.single i 1 with he
  have F1 : ∀ (k : ι) (y : M), θN k (incl y) = ∑ i, c i k • incl (θ i y) := by
    intro k y
    simp only [hθN, coordOp, hnablaN]
    rw [← completedTensorEquivOfBasis_apply p b hN, LinearEquiv.symm_apply_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [tensorCoordinate_tmul]
  have hθNadd : ∀ (k : ι) (y z : N), θN k (y + z) = θN k y + θN k z :=
    coordOp_add p b hN nablaN
  set θNj : N →+ N := AddMonoidHom.mk' (θN j) (hθNadd j) with hθNj
  have hrepr_mono : ∀ K : ι →₀ ℕ, b.repr (d (taylorMonomial D xi K)) j =
      ∑ i ∈ K.support, taylorMonomial D xi (K - e i) * b.repr (d (xi i)) j := by
    intro K
    rw [hdmono K, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hrepr_xi : ∀ i, b.repr (d (xi i)) j = (if i = j then 1 else 0) - c i j := by
    intro i
    have h := congrArg (fun ω ↦ b.repr ω j) (hdxi i)
    simp only [← hbx, Module.Basis.repr_self, map_add, Finsupp.add_apply] at h
    rw [Finsupp.single_apply] at h
    rw [hc]
    simp only at h ⊢
    rw [eq_sub_iff_add_eq, add_comm]
    exact h.symm
  have hshift : ∀ (K : ι →₀ ℕ) (i : ι) (y : M), θ i (thetaPow K y) = thetaPow (K + e i) y := by
    intro K i y
    rw [hfamM.2 i K]; rfl
  have hshift' : ∀ (K : ι →₀ ℕ) (y : M), thetaPow K (θ j y) = thetaPow (K + e j) y := by
    intro K y
    rw [show K + e j = e j + K from add_comm _ _, hfamM.add (e j) K, hfamM.single,
      Function.iterate_one]; rfl
  refine eq_of_forall_sub_mem_pPowSmul p D hN fun n ↦ ?_
  set R := taylorBox p D hfin n m with hR
  have hRgood : ∀ K ∉ R, thetaPow K m ∈ pPowSmul p (D : Type u) M n :=
    fun K hK ↦ mem_pPowSmul_of_notMem_taylorBox p D hfin hK
  have hdown : ∀ K ∈ R, ∀ L ≤ K, L ∈ R := fun K hK L hLK ↦ mem_taylorBox_of_le p D hfin hK hLK
  set Rf : ι → Finset (ι →₀ ℕ) := fun i ↦ R.filter (fun K ↦ K + e i ∈ R) with hRf
  have hRjgood : ∀ K ∉ Rf j, thetaPow K (θ j m) ∈ pPowSmul p (D : Type u) M n := by
    intro K hK
    rw [hshift']
    refine hRgood _ fun h ↦ hK (Finset.mem_filter.mpr ⟨hdown _ h _ le_self_add, h⟩)
  have E1 := taylorSum_sub_sum_mem p D thetaPow incl.toAddMonoidHom xi hfin hN m n R hRgood
  have E2 := taylorSum_sub_sum_mem p D thetaPow incl.toAddMonoidHom xi hfin hN (θ j m) n (Rf j)
    hRjgood
  set A : N := ∑ K ∈ R, ∑ i, (taylorMonomial D xi K * c i j) • incl (thetaPow (K + e i) m)
    with hA
  set A' : N := ∑ i, ∑ K ∈ Rf i, (taylorMonomial D xi K * c i j) • incl (thetaPow (K + e i) m)
    with hA'
  set B : N := ∑ i, ∑ K ∈ Rf i,
    (taylorMonomial D xi K * b.repr (d (xi i)) j) • incl (thetaPow (K + e i) m) with hB
  have hcoordSum : θN j (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K) = A + B := by
    have h1 : θN j (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K) =
        ∑ K ∈ R, (taylorMonomial D xi K • θN j (incl (thetaPow K m)) +
          b.repr (d (taylorMonomial D xi K)) j • incl (thetaPow K m)) := by
      show θNj _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun K _ ↦ ?_
      simp only [hθNj, AddMonoidHom.mk'_apply, taylorSumTerm, hθN, coordOp_smul]
      rfl
    rw [h1, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun K _ ↦ ?_
      rw [F1, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul, hshift]
    · have hre := sum_support_sub_single_eq R hdown (fun K i ↦
        (taylorMonomial D xi K * b.repr (d (xi i)) j) • incl (thetaPow (K + e i) m))
      rw [hB, ← hre]
      refine Finset.sum_congr rfl fun K _ ↦ ?_
      rw [hrepr_mono, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hKi : e i ≤ K := Finsupp.single_le_iff.mpr
        (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
      rw [tsub_add_cancel_of_le hKi]
  have hAA' : A - A' ∈ pPowSmul p (D : Type u) N n := by
    rw [hA, hA', Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [← Finset.sum_filter_add_sum_filter_not R (fun K ↦ K + e i ∈ R), add_sub_cancel_left]
    refine Submodule.sum_mem _ fun K hK ↦ ?_
    exact Submodule.smul_mem _ _ (map_mem_pPowSmul_of_addMonoidHom p incl.toAddMonoidHom
      (hRgood _ (Finset.mem_filter.mp hK).2))
  have hA'B : A' + B = ∑ K ∈ Rf j, taylorSumTerm D thetaPow incl.toAddMonoidHom xi (θ j m) K := by
    rw [hA', hB, ← Finset.sum_add_distrib]
    rw [Finset.sum_eq_single j]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun K _ ↦ ?_
      rw [← add_smul, ← mul_add, hrepr_xi, ite_eq_left rfl, add_sub_cancel, mul_one, taylorSumTerm,
        hshift']
      rfl
    · intro i _ hij
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun K _ ↦ ?_
      rw [← add_smul, ← mul_add, hrepr_xi, ite_eq_right hij, zero_sub, add_neg_cancel, mul_zero,
        zero_smul]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hθNmem : θN j (completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN m) -
      θN j (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K) ∈
        pPowSmul p (D : Type u) N n := by
    have hsub := map_sub θNj (completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN m)
      (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K)
    simp only [hθNj, AddMonoidHom.mk'_apply] at hsub
    rw [← hsub]
    exact coordOp_mem_pPowSmul p b hN nablaN j E1
  have : θN j (taylorRoundTripAdd p D b hM nablaM hfamM hfin hN ρ incl xi m) -
      taylorRoundTripAdd p D b hM nablaM hfamM hfin hN ρ incl xi (θ j m) =
      (θN j (completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN m) -
        θN j (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K)) + (A - A') -
      (completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN (θ j m) -
        ∑ K ∈ Rf j, taylorSumTerm D thetaPow incl.toAddMonoidHom xi (θ j m) K) := by
    rw [taylorRoundTripAdd_apply, taylorRoundTripAdd_apply, hcoordSum, ← hA'B]
    abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.add_mem _ hθNmem hAA') E2

end Horizontality

end Crystalline

end
