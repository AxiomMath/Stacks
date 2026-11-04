module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateExpansionSupport
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateFunctionals
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceSectionsLevelQuotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelFamilyFinality
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorFormula
public import StacksFrontier.AlgebraicGeometry.Crystalline.ThetaMonomialFamily
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Taylor operators of a pair

For a pair `(M, ∇)` of [Stacks, Lemma 60.17.3, Tag 07JG] whose module of differentials has a dual
family of coordinate functionals (`Crystalline.IsCoordinateDual`), write
`∇(m) = - ∑_i θ_i(m) d x_i`. This file studies the Taylor operators `θ_i` and their composites
`θ_K = ∏_i θ_i^{k_i}`, and shows that a morphism of crystals in quasi-coherent modules on
`Cris(X/S)` is determined by the map it induces on the limit module.

## Main results

* `Crystalline.coordinate_leibniz`, `Crystalline.coordinate_map_add`,
  `Crystalline.coordinate_naturality`, `Crystalline.finite_notMem_pPowSmul_of_isCoordinateDual` —
  the coordinate operators of a completed connection are additive, satisfy the Leibniz rule,
  commute with horizontal maps and tend to zero `p`-adically.
* `Crystalline.Pair.taylorTheta`, `Crystalline.Pair.taylorThetaPow` — the Taylor operators
  `θ_i = -(coordinate operators)` of a pair and their composites, with their Leibniz rule
  `Crystalline.Pair.taylorThetaPow_smul`, their convergence
  `Crystalline.Pair.finite_taylorThetaPow_notMem` and their naturality
  `Crystalline.PairHom.taylorThetaPow_apply`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.eq_of_wholeSpaceSectionsMap_eq` — a morphism of
  crystals in quasi-coherent modules is determined by the map it induces on `M = lim_e Γ(T_e, ℱ)`.
-/

@[expose] public section

open scoped TensorProduct

universe u v w uI

namespace Crystalline

section Leibniz

variable {p : ℕ} {D : Type u} [CommRing D] {Omega : Type v} [AddCommGroup Omega]
  [Module D Omega] {M : Type w} [AddCommGroup M] [Module D M] {ι : Type uI}
  {dx : ι → Omega} {dd : D → Omega} {nabla : CompletedConnection p D Omega dd M}

/-- **The Leibniz rule for the coordinate operators of a completed connection**:
`θ_j(f m) = f θ_j(m) + c_j(d f) m`, for a dual family of coordinate functionals `c_j` and a
`p`-adically separated module. -/
theorem coordinate_leibniz {theta : ι → (M → M)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    {coord : ι → (Omega →ₗ[D] D)} (hc : IsCoordinateDual dx coord)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) M) (j : ι) (f : D) (m : M) :
    theta j (f • m) = f • theta j m + coord j (dd f) • m := by
  refine hM.haus' _ (fun n ↦ ?_) |> sub_eq_zero.mp
  rw [SModEq.zero, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero,
    ← completedTensorFunctionalLevel_eq_of_hasSum p D Omega M hco hc j (f • m) n,
    CompletedConnection.leibniz, map_add, map_smul,
    completedTensorFunctionalLevel_eq_of_hasSum p D Omega M hco hc j m n,
    completedTensorFunctionalLevel_of, dualTensorCoordinate_tmul]
  rfl

/-- **The coordinate operators of a convergent coordinate expansion tend to zero**: for every `n`
only finitely many `θ_i(m)` lie outside `p^n M`, from a dual family of coordinate functionals. -/
theorem finite_notMem_pPowSmul_of_isCoordinateDual {theta : ι → (M → M)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    {coord : ι → (Omega →ₗ[D] D)} (hc : IsCoordinateDual dx coord) (m : M) (n : ℕ) :
    {i : ι | theta i m ∉ pPowSmul p D M n}.Finite := by
  classical
  let this := (DividedPowers.pAdicIdeal (A := D) p).adicTopology
  let this := completedTensorTopology p D Omega M
  have hbas := (DividedPowers.pAdicIdeal (A := D) p).ringFilterBasis.submodulesBasisIsBasis
    ((DividedPowers.pAdicIdeal (A := D) p).adic_module_basis (CompletedTensor p D Omega M))
  have : IsTopologicalAddGroup (CompletedTensor p D Omega M) :=
    hbas.toModuleFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
  have hopen : IsOpen (((DividedPowers.pAdicIdeal (A := D) p) ^ n •
      (⊤ : Submodule D (CompletedTensor p D Omega M)) :
        Submodule D (CompletedTensor p D Omega M)) : Set (CompletedTensor p D Omega M)) :=
    (SubmodulesBasis.openAddSubgroup hbas n).isOpen'
  have hfin := Filter.eventually_cofinite.mp
    ((hco m).summable.tendsto_cofinite_zero (hopen.mem_nhds (Submodule.zero_mem _)))
  refine hfin.subset fun i hi hmem ↦ hi ?_
  have h1 := map_mem_pow_smul_top_of_mem _ (dualTensorCoordinate M (coord i)) n
    (mem_pow_smul_top_of_of_mem _ n hmem)
  rwa [dualTensorCoordinate_tmul, hc.self, one_smul] at h1

/-- **The coordinate operators of a completed connection are additive**, from a dual family of
coordinate functionals and `p`-adic separatedness. -/
theorem coordinate_map_add {theta : ι → (M → M)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    {coord : ι → (Omega →ₗ[D] D)} (hc : IsCoordinateDual dx coord)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) M) (j : ι) (x y : M) :
    theta j (x + y) = theta j x + theta j y := by
  refine hM.haus' _ (fun n ↦ ?_) |> sub_eq_zero.mp
  rw [SModEq.zero, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero,
    ← completedTensorFunctionalLevel_eq_of_hasSum p D Omega M hco hc j (x + y) n,
    nabla.map_add, map_add, completedTensorFunctionalLevel_eq_of_hasSum p D Omega M hco hc j x n,
    completedTensorFunctionalLevel_eq_of_hasSum p D Omega M hco hc j y n]
  rfl

/-- **Horizontal maps commute with the coordinate operators.**  If `φ : M → N` is `D`-linear and
`∇_N ∘ φ = (φ ⊗ 1) ∘ ∇_M`, then `θ^N_j ∘ φ = φ ∘ θ^M_j`, from a dual family of coordinate
functionals and `p`-adic separatedness of `N`. -/
theorem coordinate_naturality {N : Type w} [AddCommGroup N] [Module D N]
    {nablaN : CompletedConnection p D Omega dd N} {theta : ι → (M → M)} {thetaN : ι → (N → N)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    (hcoN : IsCoordinateExpansion p D Omega dx nablaN thetaN)
    {coord : ι → (Omega →ₗ[D] D)} (hc : IsCoordinateDual dx coord)
    (hN : IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) N) (φ : M →ₗ[D] N)
    (hφ : ∀ m, nablaN (φ m) = AdicCompletion.map (DividedPowers.pAdicIdeal (A := D) p)
      (TensorProduct.map φ (LinearMap.id (R := D) (M := Omega))) (nabla m))
    (j : ι) (m : M) : thetaN j (φ m) = φ (theta j m) := by
  refine hN.haus' _ (fun n ↦ ?_) |> sub_eq_zero.mp
  rw [SModEq.zero, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero,
    ← completedTensorFunctionalLevel_eq_of_hasSum p D Omega N hcoN hc j (φ m) n, hφ]
  have key : completedTensorFunctionalLevel p D Omega N (dualTensorCoordinate N (coord j)) n
        (AdicCompletion.map (DividedPowers.pAdicIdeal (A := D) p)
          (TensorProduct.map φ (LinearMap.id (R := D) (M := Omega))) (nabla m)) =
      pLevelMapQ p D M N φ n (completedTensorFunctionalLevel p D Omega M
        (dualTensorCoordinate M (coord j)) n (nabla m)) := by
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _
      (AdicCompletion.eval (DividedPowers.pAdicIdeal (A := D) p) (M ⊗[D] Omega) n (nabla m))
    have hmap : AdicCompletion.eval (DividedPowers.pAdicIdeal (A := D) p) (N ⊗[D] Omega) n
        (AdicCompletion.map (DividedPowers.pAdicIdeal (A := D) p)
          (TensorProduct.map φ (LinearMap.id (R := D) (M := Omega))) (nabla m)) =
        Submodule.Quotient.mk (TensorProduct.map φ LinearMap.id x) := by
      rw [AdicCompletion.eval_apply, AdicCompletion.map_val_apply, ← AdicCompletion.eval_apply,
        ← hx]
      rfl
    change pLevelMapQ p D (N ⊗[D] Omega) N _ n (AdicCompletion.eval _ _ n _) =
      pLevelMapQ p D M N φ n (pLevelMapQ p D (M ⊗[D] Omega) M _ n (AdicCompletion.eval _ _ n _))
    rw [hmap, ← hx, pLevelMapQ_mk, pLevelMapQ_mk, pLevelMapQ_mk]
    congr 1
    clear hmap hx
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul y ω => simp [dualTensorCoordinate_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, completedTensorFunctionalLevel_eq_of_hasSum p D Omega M hco hc j m n, pLevelMapQ_mk]

/-- The `I`-adic topology of an `I`-adically separated module is Hausdorff. -/
theorem t2Space_adicModuleTopology {R : Type*} [CommRing R] (I : Ideal R) (N : Type*)
    [AddCommGroup N] [Module R N] (hN : IsHausdorff I N) :
    @T2Space N (I.adicModuleTopology N) := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace N := I.adicModuleTopology N
  let B := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis N))
    |>.toAddGroupFilterBasis
  rw [B.t2Space_iff_sInter_subset rfl]
  intro x hx
  simp only [Set.mem_sInter] at hx
  have hx' : ∀ n : ℕ, x ∈ I ^ n • (⊤ : Submodule R N) := fun n ↦
    hx _ (show ∃ i, ((I ^ n • (⊤ : Submodule R N) : Submodule R N) : Set N) =
      ((I ^ i • (⊤ : Submodule R N) : Submodule R N) : Set N) from ⟨n, rfl⟩)
  have : x = 0 := hN.haus x fun n ↦ by simpa [SModEq.zero] using hx' n
  simp [this]

/-- **A completed connection is determined by its coordinate operators**: two connections with
coordinate expansions by the same operators are equal, the completed tensor product being
`p`-adically separated. -/
theorem CompletedConnection.eq_of_isCoordinateExpansion
    {nabla' : CompletedConnection p D Omega dd M}
    {theta : ι → (M → M)} (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    (hco' : IsCoordinateExpansion p D Omega dx nabla' theta) : nabla = nabla' := by
  let this := completedTensorTopology p D Omega M
  have := t2Space_adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p)
    (CompletedTensor p D Omega M) inferInstance
  exact CompletedConnection.ext fun m ↦ (hco m).unique (hco' m)

/-- The submodules `I^n M` are a basis of neighbourhoods of `0` for the `I`-adic topology. -/
theorem adicModuleTopology_hasBasis {R : Type*} [CommRing R] (I : Ideal R) (N : Type*)
    [AddCommGroup N] [Module R N] :
    @Filter.HasBasis N ℕ (@nhds N (I.adicModuleTopology N) 0)
      (fun _ => True) (fun n => ((I ^ n • (⊤ : Submodule R N) : Submodule R N) : Set N)) := by
  let : TopologicalSpace R := I.adicTopology
  let B := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis N))
    |>.toAddGroupFilterBasis
  refine B.nhds_zero_hasBasis.to_hasBasis ?_ ?_
  · intro U hU
    change ∃ n, U = ((I ^ n • (⊤ : Submodule R N) : Submodule R N) : Set N) at hU
    obtain ⟨n, rfl⟩ := hU
    exact ⟨n, trivial, Set.Subset.rfl⟩
  · exact fun n _ ↦ ⟨((I ^ n • (⊤ : Submodule R N) : Submodule R N) : Set N), ⟨n, rfl⟩,
      Set.Subset.rfl⟩

/-- **A linear map is continuous for the `I`-adic topologies.** -/
@[ega "0 7.2.10" "more general"]
theorem continuous_linearMap_adicModuleTopology {R : Type*} [CommRing R] (I : Ideal R)
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (g : N →ₗ[R] N') : @Continuous N N' (I.adicModuleTopology N) (I.adicModuleTopology N') g := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace N := I.adicModuleTopology N
  let : TopologicalSpace N' := I.adicModuleTopology N'
  have hbas := I.ringFilterBasis.submodulesBasisIsBasis (I.adic_module_basis N)
  have hbas' := I.ringFilterBasis.submodulesBasisIsBasis (I.adic_module_basis N')
  have : IsTopologicalAddGroup N :=
    hbas.toModuleFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
  have : IsTopologicalAddGroup N' :=
    hbas'.toModuleFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
  refine continuous_of_continuousAt_zero g.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((adicModuleTopology_hasBasis I N).tendsto_iff (adicModuleTopology_hasBasis I N')).2
    fun n _ ↦ ⟨n, trivial, fun x hx ↦ map_mem_pow_smul_top_of_mem I g n hx⟩

/-- **A linear map commuting with the coordinate operators is horizontal.** -/
theorem horizontal_of_isCoordinateExpansion {N : Type w} [AddCommGroup N] [Module D N]
    {nablaN : CompletedConnection p D Omega dd N} {theta : ι → (M → M)} {thetaN : ι → (N → N)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    (hcoN : IsCoordinateExpansion p D Omega dx nablaN thetaN) (φ : M →ₗ[D] N)
    (hφ : ∀ c x, φ (theta c x) = thetaN c (φ x)) (x : M) :
    nablaN (φ x) = AdicCompletion.map (DividedPowers.pAdicIdeal (A := D) p)
      (TensorProduct.map φ (LinearMap.id (R := D) (M := Omega))) (nabla x) := by
  let this := completedTensorTopology p D Omega M
  let this := completedTensorTopology p D Omega N
  have := t2Space_adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p)
    (CompletedTensor p D Omega N) inferInstance
  have hmap := (hco x).map (AdicCompletion.map (DividedPowers.pAdicIdeal (A := D) p)
      (TensorProduct.map φ (LinearMap.id (R := D) (M := Omega)))).toAddMonoidHom
    (continuous_linearMap_adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p)
      ((AdicCompletion.map (DividedPowers.pAdicIdeal (A := D) p)
        (TensorProduct.map φ (LinearMap.id (R := D) (M := Omega)))).restrictScalars D))
  have hterm : ((AdicCompletion.map (DividedPowers.pAdicIdeal (A := D) p)
      (TensorProduct.map φ (LinearMap.id (R := D) (M := Omega)))).toAddMonoidHom ∘
        fun c ↦ toCompletedTensor p D Omega M (theta c x ⊗ₜ[D] dx c)) =
      fun c ↦ toCompletedTensor p D Omega N (thetaN c (φ x) ⊗ₜ[D] dx c) := by
    funext c
    simp only [Function.comp_apply, LinearMap.toAddMonoidHom_coe, toCompletedTensor,
      AdicCompletion.map_of, TensorProduct.map_tmul, LinearMap.id_apply, hφ]
  rw [hterm] at hmap
  exact (hcoN (φ x)).unique hmap

end Leibniz

/-! ### Uniqueness of the composite operators -/

/-- **The composite operators `θ_K` are determined by the `θ_i`.** -/
theorem IsThetaMonomialFamily.unique {M : Type*} {ι : Type*} {theta : ι → (M → M)}
    {f g : (ι →₀ ℕ) → (M → M)} (hf : IsThetaMonomialFamily M theta f)
    (hg : IsThetaMonomialFamily M theta g) : f = g := by
  classical
  funext K
  induction K using Finsupp.induction with
  | zero => rw [hf.apply_zero, hg.apply_zero]
  | single_add a b K _ _ ih =>
      rw [add_comm, hf.add_single, hg.add_single, ih]

/-! ### The coordinate operators of a pair, and their composites -/

section PairData

variable {p : ℕ} {D : Type u} [CommRing D] {Omega : Type v} [AddCommGroup Omega]
  [Module D Omega] {ι : Type uI} {dx : ι → Omega} {dd : D → Omega}
  {coord : ι → (Omega →ₗ[D] D)}

namespace Pair

variable (P : Pair.{u, v, uI, w} p D Omega dx dd)

/-- **The Taylor operators `θ_i` of a pair**: the negatives of the coordinate operators of its
connection, `∇ m = - ∑_i θ_i(m) d x_i`.  The sign is the one of
[Stacks, Lemma 60.17.3, Tag 07JG]: with `ξ_i = x_i ⊗ 1 - 1 ⊗ x_i`, which maps to `-d x_i` modulo
the square of the ideal of the diagonal, the comparison of a crystal is
`p₁^* m = ∑_K ξ^{[K]} p₀^*(θ_K m)` and its first-order part is `∇ m = - ∑_i θ_i(m) d x_i`. -/
noncomputable def taylorTheta (i : ι) (m : P.carrier) : P.carrier :=
  -P.hasCoordinateOperators.choose i m

/-- The connection of a pair has coordinates minus its Taylor operators. -/
theorem isCoordinateExpansion_neg_taylorTheta :
    IsCoordinateExpansion p D Omega dx P.nabla fun i m ↦ -P.taylorTheta i m := by
  simp only [taylorTheta, neg_neg]
  exact P.hasCoordinateOperators.choose_spec

/-- The Taylor operators of a pair are additive. -/
theorem taylorTheta_map_add (hc : IsCoordinateDual dx coord) (i : ι) (x y : P.carrier) :
    P.taylorTheta i (x + y) = P.taylorTheta i x + P.taylorTheta i y := by
  simp only [taylorTheta,
    coordinate_map_add P.hasCoordinateOperators.choose_spec hc P.isPAdicallyComplete.toIsHausdorff,
    neg_add]

/-- The coordinate operators of the connection commute with negation, being additive. -/
theorem coordinate_neg (hc : IsCoordinateDual dx coord) (i : ι) (x : P.carrier) :
    P.hasCoordinateOperators.choose i (-x) = -P.hasCoordinateOperators.choose i x := by
  have h := coordinate_map_add P.hasCoordinateOperators.choose_spec hc
    P.isPAdicallyComplete.toIsHausdorff i x (-x)
  have h0 := coordinate_map_add P.hasCoordinateOperators.choose_spec hc
    P.isPAdicallyComplete.toIsHausdorff i 0 0
  rw [add_zero, left_eq_add] at h0
  rw [add_neg_cancel, h0] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- **The Taylor operators commute.** -/
theorem taylorTheta_comm (hc : IsCoordinateDual dx coord) (i j : ι) :
    P.taylorTheta i ∘ P.taylorTheta j = P.taylorTheta j ∘ P.taylorTheta i := by
  funext m
  have h := congrFun (P.isIntegrable _ P.hasCoordinateOperators.choose_spec i j) m
  simpa only [Function.comp_apply, taylorTheta, P.coordinate_neg hc, neg_neg] using h

/-- **The Leibniz rule of the Taylor operators**: `θ_i(f m) = f θ_i(m) + δ_i(f) m`, when the
coordinates of `d f` are `-δ_i(f)`. -/
theorem taylorTheta_smul (hc : IsCoordinateDual dx coord) {delta : ι → D → D}
    (hdelta : ∀ i f, coord i (dd f) = -delta i f) (i : ι) (f : D) (m : P.carrier) :
    P.taylorTheta i (f • m) = f • P.taylorTheta i m + delta i f • m := by
  simp only [taylorTheta, coordinate_leibniz P.hasCoordinateOperators.choose_spec hc
    P.isPAdicallyComplete.toIsHausdorff, hdelta, neg_smul, smul_neg, neg_add, neg_neg]

/-- **The composite Taylor operators `θ_K = ∏_i θ_i^{k_i}` of a pair**, chosen by
`Crystalline.exists_isThetaMonomialFamily`. -/
noncomputable def taylorThetaPow (hc : IsCoordinateDual dx coord) :
    (ι →₀ ℕ) → (P.carrier → P.carrier) :=
  (exists_isThetaMonomialFamily (M := P.carrier) P.taylorTheta (P.taylorTheta_comm hc)).choose

/-- The composite Taylor operators of a pair are the composites of its first-order ones. -/
theorem isThetaMonomialFamily_taylorThetaPow (hc : IsCoordinateDual dx coord) :
    IsThetaMonomialFamily P.carrier P.taylorTheta (P.taylorThetaPow hc) :=
  (exists_isThetaMonomialFamily (M := P.carrier) P.taylorTheta (P.taylorTheta_comm hc)).choose_spec

/-- **The Taylor series of a pair converges**: for every `n` and `m`, only finitely many `θ_K(m)`
lie outside `p^n M`. -/
theorem finite_taylorThetaPow_notMem (hc : IsCoordinateDual dx coord) (n : ℕ)
    (m : P.carrier) :
    {K : ι →₀ ℕ | P.taylorThetaPow hc K m ∉ pPowSmul p D P.carrier n}.Finite := by
  refine finite_thetaPow_notMem_pPowSmul p D P.carrier (P.isThetaMonomialFamily_taylorThetaPow hc)
    (P.taylorTheta_map_add hc) (fun i x ↦ ?_) ?_
  · refine (P.isTopologicallyQuasiNilpotent _ P.hasCoordinateOperators.choose_spec x).preimage
      (f := fun k : ℕ ↦ (i, k)) (fun _ _ _ _ h ↦ (Prod.mk.inj h).2) |>.subset fun k hk ↦ ?_
    refine ⟨hk.1, fun hmem ↦ hk.2 ?_⟩
    have hiter : ∀ k y, (P.taylorTheta i)^[k] y = (-1 : ℤ) ^ k •
        (P.hasCoordinateOperators.choose i)^[k] y := by
      intro k y
      induction k generalizing y with
      | zero => simp
      | succ k ih =>
          rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
          let φ : P.carrier →+ P.carrier := AddMonoidHom.mk' (P.hasCoordinateOperators.choose i)
            (coordinate_map_add P.hasCoordinateOperators.choose_spec hc
              P.isPAdicallyComplete.toIsHausdorff i)
          change -φ ((-1 : ℤ) ^ k • _) = _
          rw [map_zsmul, pow_succ, mul_comm, mul_smul, neg_one_smul]
          rfl
    rw [hiter]
    exact Submodule.smul_of_tower_mem _ _ hmem
  · simpa [taylorTheta, pPowSmul] using
      finite_notMem_pPowSmul_of_isCoordinateDual P.hasCoordinateOperators.choose_spec hc m n

/-- The composite Taylor operators, as additive maps. -/
noncomputable def taylorThetaPowHom (hc : IsCoordinateDual dx coord) (K : ι →₀ ℕ) :
    P.carrier →+ P.carrier :=
  AddMonoidHom.mk' (P.taylorThetaPow hc K)
    ((P.isThetaMonomialFamily_taylorThetaPow hc).map_add (P.taylorTheta_map_add hc) K)

/-- The additive map `taylorThetaPowHom` evaluates as the composite Taylor operator. -/
@[simp] theorem taylorThetaPowHom_apply (hc : IsCoordinateDual dx coord) (K : ι →₀ ℕ)
    (m : P.carrier) : P.taylorThetaPowHom hc K m = P.taylorThetaPow hc K m := rfl

/-- **The general Leibniz rule of the composite Taylor operators**:
`θ_K(f m) = ∑_{A + B = K} c(A, B) δ_A(f) θ_B(m)` with `c(A, B) = ∏_i binom(a_i + b_i, a_i)`, for
`δ_K = ∏_i δ_i^{k_i}` the composite operators of `D` whose first-order ones are minus the
coordinates of `d`. -/
theorem taylorThetaPow_smul [DecidableEq ι] (hc : IsCoordinateDual dx coord)
    {delta : ι → D → D} {deltaPow : (ι →₀ ℕ) → (D → D)}
    (hfamD : IsThetaMonomialFamily D delta deltaPow)
    (hdelta : ∀ i f, coord i (dd f) = -delta i f) (K : ι →₀ ℕ) (f : D) (m : P.carrier) :
    P.taylorThetaPow hc K (f • m) = ∑ Q ∈ Finset.HasAntidiagonal.antidiagonal K,
      ((Q.1 + Q.2).prod fun i n ↦ n.choose (Q.1 i)) •
        (deltaPow Q.1 f • P.taylorThetaPow hc Q.2 m) := by
  rw [thetaPow_smul_eq_support (P.isThetaMonomialFamily_taylorThetaPow hc) hfamD
    (P.taylorTheta_map_add hc) (P.taylorTheta_smul hc hdelta) f m K]
  refine Finset.sum_congr rfl fun Q hQ ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal.1 hQ]
  rfl

end Pair

/-- **A morphism of pairs commutes with the Taylor operators.** -/
theorem PairHom.taylorTheta_apply {P Q : Pair.{u, v, uI, w} p D Omega dx dd} (φ : P ⟶ Q)
    (hc : IsCoordinateDual dx coord) (i : ι) (m : P.carrier) :
    Q.taylorTheta i (φ.toLinearMap m) = φ.toLinearMap (P.taylorTheta i m) := by
  simp only [Pair.taylorTheta, map_neg]
  rw [coordinate_naturality P.hasCoordinateOperators.choose_spec
    Q.hasCoordinateOperators.choose_spec hc Q.isPAdicallyComplete.toIsHausdorff φ.toLinearMap
    φ.horizontal i m]

/-- **A morphism of pairs commutes with the composite Taylor operators.** -/
theorem PairHom.taylorThetaPow_apply {P Q : Pair.{u, v, uI, w} p D Omega dx dd} (φ : P ⟶ Q)
    (hc : IsCoordinateDual dx coord) (K : ι →₀ ℕ) (m : P.carrier) :
    Q.taylorThetaPow hc K (φ.toLinearMap m) = φ.toLinearMap (P.taylorThetaPow hc K m) := by
  classical
  induction K using Finsupp.induction_linear generalizing m with
  | zero =>
      rw [(Q.isThetaMonomialFamily_taylorThetaPow hc).apply_zero,
        (P.isThetaMonomialFamily_taylorThetaPow hc).apply_zero]
      rfl
  | add K L hK hL =>
      rw [(Q.isThetaMonomialFamily_taylorThetaPow hc).add,
        (P.isThetaMonomialFamily_taylorThetaPow hc).add, Function.comp_apply, hK, hL]
      rfl
  | single i k =>
      rw [(Q.isThetaMonomialFamily_taylorThetaPow hc).single,
        (P.isThetaMonomialFamily_taylorThetaPow hc).single]
      induction k generalizing m with
      | zero => rfl
      | succ k ih =>
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, φ.taylorTheta_apply hc,
            ih]

/-- **A linear isomorphism of the modules of two pairs carrying the Taylor operators of one to
those of the other is an isomorphism of pairs**: it and its inverse are horizontal. -/
noncomputable def Pair.isoOfLinearEquivTaylorTheta {P Q : Pair.{u, v, uI, w} p D Omega dx dd}
    (φ : P.carrier ≃ₗ[D] Q.carrier)
    (h : ∀ i x, φ (P.taylorTheta i x) = Q.taylorTheta i (φ x)) : P ≅ Q where
  hom := ⟨φ.toLinearMap, horizontal_of_isCoordinateExpansion P.isCoordinateExpansion_neg_taylorTheta
    Q.isCoordinateExpansion_neg_taylorTheta φ.toLinearMap
    (fun i x ↦ (map_neg φ _).trans (congrArg Neg.neg (h i x)))⟩
  inv := ⟨φ.symm.toLinearMap, horizontal_of_isCoordinateExpansion
    Q.isCoordinateExpansion_neg_taylorTheta P.isCoordinateExpansion_neg_taylorTheta
    φ.symm.toLinearMap (fun i y ↦ by
      obtain ⟨x, rfl⟩ := φ.surjective y
      change φ.symm (-Q.taylorTheta i (φ x)) = -P.taylorTheta i (φ.symm (φ x))
      rw [← h, ← map_neg, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply])⟩
  hom_inv_id := PairHom.ext (LinearMap.ext fun x ↦ φ.symm_apply_apply x)
  inv_hom_id := PairHom.ext (LinearMap.ext fun y ↦ φ.apply_symm_apply y)

end PairData

end Crystalline

open CategoryTheory Opposite AlgebraicGeometry Simplicial

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- **A morphism of crystals in quasi-coherent modules is determined by the map it induces on
`M = lim_e Γ(T_e, ℱ)`**, the module of [Stacks, Lemma 60.17.3, Tag 07JG] at the system of
[Stacks, Tag 07JN]. -/
theorem eq_of_wholeSpaceSectionsMap_eq {F G : QuasiCoherentCrystal S} {psi chi : F ⟶ G}
    (h : (wholeSpaceLevelScalars hp 0).sectionsMap psi =
      (wholeSpaceLevelScalars hp 0).sectionsMap chi) : psi = chi := by
  refine det_of_wholeSpaceSystem hp (L := wholeSpaceLevelScalars hp 0) rfl psi chi
    fun e x ↦ ?_
  obtain ⟨m, rfl⟩ := surjective_wholeSpaceSectionsVal hp F
    (isSurjectiveComparison_of_isSheafCrystal F.property.2) 0 e x
  exact congrArg (fun z ↦ wholeSpaceSectionsVal hp G z e) (LinearMap.congr_fun h m)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
