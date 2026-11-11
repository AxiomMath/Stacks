module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZeroLevelwise
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsInfinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.RetractPairEquivalence
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairEquivalence07JH

/-!
# The equivalence of categories of pairs along a retract, for any family of coordinates

`StacksFrontier/AlgebraicGeometry/Crystalline/RetractPairEquivalence.lean` proves the equivalence of
the proof of [Stacks, Lemma 60.17.5, Tag 07L5] between the pairs over a `p`-adically complete
divided power ring `D` and the pairs over a retract `D'` of it, when the one-forms `Ω` of `D` have a
*finite* basis on the differentials `d x_i` of coordinates `x_i`.  The ring `D` of that lemma is
the completed envelope of a polynomial algebra `A[x_i]` in finitely many variables, so this is all
the lemma needs.

[Stacks, Remark 60.17.6, Tag 07L6] applies the same argument to a presentation `P → C` whose
`P/A` only has the strong lifting property of [Stacks, Tag 07K4]: the polynomial algebra mapping
onto `P` then has in general infinitely many variables, and the completed one-forms `Ω_D` of its
envelope are not free on the `d x_i` but only *topologically* free — the `p`-adic completion of a
free module.  This module carries the equivalence out in that generality.

* The coordinates are `Crystalline.CompletedCoordinateDualData`: the graded completed forms of
  `D` as before, coordinates `x_i` indexed by an arbitrary type, and in place of a basis a family
  of coordinate functionals `c_i : Ω → D` dual to the `d x_i`
  (`Crystalline.IsCoordinateDual`) such that every one-form is, modulo every `p^n`, the finite sum
  `∑_i c_i(ω) d x_i` (`approx`), together with functionals on the two-forms detecting the
  `d x_j ∧ d x_k`.
* Every completed connection on a `p`-adically complete module then has a coordinate expansion
  `∇ m = ∑_i θ_i(m) d x_i`, converging `p`-adically
  (`Crystalline.CompletedCoordinateDualData.exists_isCoordinateExpansion`), and its curvature
  vanishes exactly when the `θ_i` commute
  (`Crystalline.CompletedCoordinateDualData.isCurvatureZero_iff`): the two readings of
  integrability, Remark [Stacks, Tag 07I0] and [Stacks, Tag 07JD], agree.
* The category over `D'` is `Crystalline.CoordinateDualRetractPair`, defined as
  `Crystalline.RetractPair` is: a `p`-adically complete `D'`-module ([Stacks, Tag 07JB]) with a
  completed connection ([Stacks, Tag 07JC]) of curvature zero ([Stacks, Tag 07JD], Remark
  [Stacks, Tag 07I0]), topologically quasi-nilpotent in the sense the proof of
  [Stacks, Tag 07L5] gives that condition over `D'` ([Stacks, Tag 07JE]): "if this is true for
  `G(M', ∇')`".
* `F ∘ G ≅ 𝟭` is the collapse along `a ∘ b = id`, and `G ∘ F ≅ 𝟭` is the Taylor comparison
  `c_{id_D, b ∘ a}`, whose horizontality is
  `Crystalline.CoordinateDual.coord_taylorRoundTrip`, the infinite sums being truncated modulo
  each `p^n`.

## Main definitions

* `Crystalline.CompletedCoordinateDualData` — topological coordinates on `D`.
* `Crystalline.CoordinateDualRetractData` — a retract `a ∘ b = id` with its comparisons of forms
  and Taylor's formula for `b ∘ a`.
* `Crystalline.CoordinateDualRetractPair` — the category of pairs over `D'`.
* `Crystalline.CoordinateDual.retractPairEquivalence` — **the equivalence of categories.**

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Remark 60.17.6, Tag 07L6](https://stacks.math.columbia.edu/tag/07L6)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

/-! ### Coordinate operators from a dual family, level by level -/

section Levels

variable (p : ℕ) {D : Type u} [CommRing D] {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] {M : Type u} [AddCommGroup M] [Module D M] {ι : Type u} {dx : ι → Omega}
  {dd : D → Omega} {nabla : CompletedConnection p D Omega dd M} {theta : ι → (M → M)}

/-- **A coordinate operator carries `pⁿ M` into itself**, from a dual family of coordinate
functionals: `θ_k(x) mod pⁿ` is read off `∇ x` by a `D`-linear functional, and `∇` commutes with
the integer `pⁿ`. -/
theorem theta_mem_pPowSmul_of_mem_of_isCoordinateDual
    (hco : IsCoordinateExpansion p D Omega dx nabla theta) {coord : ι → (Omega →ₗ[D] D)}
    (hc : IsCoordinateDual dx coord) (n : ℕ) (k : ι) {x : M} (hx : x ∈ pPowSmul p D M n) :
    theta k x ∈ pPowSmul p D M n := by
  classical
  obtain ⟨y, hy⟩ := (mem_pPowSmul_iff p D M).mp hx
  have hx' : x = (p ^ n : ℕ) • y := by
    rw [← hy, show ((p : D) ^ n) = ((p ^ n : ℕ) : D) by push_cast; ring,
      Nat.cast_smul_eq_nsmul]
  have hnabla : nabla x = (p ^ n : ℕ) • nabla y := by
    rw [hx']
    exact (AddMonoidHom.mk' (fun z : M ↦ nabla z) nabla.map_add).map_nsmul (p ^ n) y
  have hzero : Submodule.Quotient.mk (p := pLevel p D M n) (theta k x) = 0 := by
    rw [← completedTensorFunctionalLevel_eq_of_hasSum p D Omega M hco hc k x n, hnabla,
      map_nsmul, ← Nat.cast_smul_eq_nsmul D, Nat.cast_pow]
    exact CompletedDeRham.smul_quotient_eq_zero p D
      (CompletedDeRham.pow_mem_pAdicIdeal_pow p D n) _
  exact (Submodule.Quotient.mk_eq_zero _).mp hzero

/-- **The levelwise coordinate expansion from a dual family of coordinate functionals.** -/
theorem isLevelwiseCoordinateExpansion_of_isCoordinateDual
    (hco : IsCoordinateExpansion p D Omega dx nabla theta) {coord : ι → (Omega →ₗ[D] D)}
    (hc : IsCoordinateDual dx coord) :
    CompletedDeRham.IsLevelwiseCoordinateExpansion p D Omega dx nabla theta :=
  isLevelwiseCoordinateExpansion_of_finite_support p D Omega M hco
    (fun m n ↦ finite_notMem_pPowSmul_of_isCoordinateDual hco hc m n)
    (fun n k _ hx ↦ theta_mem_pPowSmul_of_mem_of_isCoordinateDual p hco hc n k hx)

/-- **The coordinate expansion truncated modulo `pⁿ`**: over any finset outside which the
operators land in `pⁿ M`, the finite sum agrees with `∇ m` up to `pⁿ (M ⊗̂ Ω)`. -/
theorem sub_sum_mem_of_isCoordinateExpansion
    (hco : IsCoordinateExpansion p D Omega dx nabla theta) (m : M) (n : ℕ) (t : Finset ι)
    (ht : ∀ i ∉ t, theta i m ∈ pPowSmul p D M n) :
    nabla m - ∑ i ∈ t, toCompletedTensor p D Omega M (theta i m ⊗ₜ[D] dx i) ∈
      ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (CompletedTensor p D Omega M)) := by
  have h := isLevelExpansionAt_of_support_subset p D Omega M hco m n t fun i hi ↦ by
    by_contra hit
    exact hi (ht i hit)
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
    map_sub, AdicCompletion.eval_apply, AdicCompletion.eval_apply, sub_eq_zero]
  exact h

end Levels

/-! ### The data -/

/-- **Topological coordinates on a `p`-adically complete divided power ring**: a graded family of
forms `Ω^*` with a divided power derivation `d : D → Ω^1`, coordinates `x_i` indexed by an
arbitrary type, and a family of `D`-linear functionals `c_i : Ω^1 → D` dual to the `d x_i` such
that every one-form is, modulo every `p^n`, the finite sum `∑_i c_i(ω) d x_i`; functionals on the
two-forms detecting the `d x_j ∧ d x_k`; and the composite coordinate derivations
`∂_K = ∏_i ∂_i^{k_i}` of the `∂_i a = c_i(d a)`.

This is the shape of the `p`-adically completed divided power envelope `D` of a polynomial
presentation `A[x_i : i ∈ ι] → C` with any family of variables, and its `Ω_D` of
[Stacks, Tag 07J9], which is the completion of a module free on the `d x_i`; with finitely many
variables it is `Crystalline.CompletedCoordinateData`. -/
structure CompletedCoordinateDualData (p : ℕ) (D : DividedPowerRing.{u}) where
  /-- The modules of forms `Ω^i`. -/
  Om : ℕ → Type u
  /-- Their additive group structures. -/
  [addCommGroup : ∀ i, AddCommGroup (Om i)]
  /-- Their `D`-module structures. -/
  [module : ∀ i, Module (D : Type u) (Om i)]
  /-- The wedge product `Ω^i × Ω^1 → Ω^{i+1}`. -/
  wedge : ∀ i, Om i →ₗ[(D : Type u)] Om 1 →ₗ[(D : Type u)] Om (i + 1)
  /-- The de Rham differential of the forms. -/
  deRham : ∀ i, Om i →+ Om (i + 1)
  /-- The differential `d : D → Ω^1`. -/
  diff : D.carrier → Om 1
  /-- `d` is additive. -/
  diff_add : ∀ x y : (D : Type u), diff (x + y) = diff x + diff y
  /-- `d` obeys the Leibniz rule. -/
  diff_mul : ∀ x y : (D : Type u), diff (x * y) = x • diff y + y • diff x
  /-- `d` obeys the divided power chain rule. -/
  diff_dpow : ∀ (n : ℕ), 0 < n → ∀ x ∈ D.ideal,
    diff (D.dividedPowers.dpow n x) = D.dividedPowers.dpow (n - 1) x • diff x
  /-- The Leibniz rule `d (f ω) = f d ω + ω ∧ d f` of the forms. -/
  isGradedLeibniz : CompletedDeRham.IsGradedLeibniz (D : Type u) Om wedge deRham diff
  /-- The wedge product of one-forms is antisymmetric. -/
  wedge_anti : ∀ η ζ : Om 1, wedge 1 η ζ + wedge 1 ζ η = 0
  /-- The wedge product of a one-form with itself vanishes. -/
  wedge_self : ∀ η : Om 1, wedge 1 η η = 0
  /-- Exact one-forms are closed. -/
  deRham_diff : ∀ c : (D : Type u), deRham 1 (diff c) = 0
  /-- The index type of the coordinates. -/
  ι : Type u
  /-- Decidable equality of coordinates. -/
  [decEq : DecidableEq ι]
  /-- The coordinates `x_i`. -/
  coord : ι → (D : Type u)
  /-- The coordinate functionals `c_i : Ω^1 → D`. -/
  coordFun : ι → (Om 1 →ₗ[(D : Type u)] (D : Type u))
  /-- The coordinate functionals are dual to the `d x_i`. -/
  isCoordinateDual : IsCoordinateDual (fun i ↦ diff (coord i)) coordFun
  /-- **Topological freeness**: every one-form is, modulo `p^n`, the finite sum of its
  coordinates against the `d x_i`, the other coordinates lying in `p^n D`. -/
  approx : ∀ (ω : Om 1) (n : ℕ), ∃ T : Finset ι,
    (∀ i ∉ T, coordFun i ω ∈ pAdicIdeal (A := (D : Type u)) p ^ n) ∧
      ω - ∑ i ∈ T, coordFun i ω • diff (coord i) ∈ pPowSmul p (D : Type u) (Om 1) n
  /-- The functionals `φ_{ac}` on the two-forms. -/
  twoFormFun : ι → ι → (Om (1 + 1) →ₗ[(D : Type u)] (D : Type u))
  /-- `φ_{ac}(d x_j ∧ d x_k) = δ_{ka} δ_{jc} - δ_{kc} δ_{ja}`. -/
  twoFormFun_wedge : ∀ a c j k, twoFormFun a c (wedge 1 (diff (coord j)) (diff (coord k))) =
    (if k = a then 1 else 0) * (if j = c then 1 else 0) -
      (if k = c then 1 else 0) * (if j = a then 1 else 0)
  /-- The composite coordinate derivations `∂_K`. -/
  deltaPow : (ι →₀ ℕ) → (D.carrier → D.carrier)
  /-- `∂_K = ∏_i ∂_i^{k_i}` for the coordinate derivations `∂_i a = c_i(d a)`. -/
  isThetaMonomialFamily : IsThetaMonomialFamily (D : Type u) (fun i a ↦ coordFun i (diff a))
    deltaPow

attribute [instance] CompletedCoordinateDualData.addCommGroup CompletedCoordinateDualData.module
  CompletedCoordinateDualData.decEq

namespace CompletedCoordinateDualData

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateDualData p D)

/-- The module of one-forms `Ω = Ω^1`. -/
abbrev forms : Type u := C.Om 1

/-- The family `d x_i` of differentials of the coordinates. -/
abbrev dx : C.ι → C.forms := fun i ↦ C.diff (C.coord i)

/-! #### Every completed connection has a coordinate expansion -/

section Expansion

variable {M : Type u} [AddCommGroup M] [Module (D : Type u) M]

/-- **The contraction `M ⊗̂ Ω → M` with the coordinate functional `c_j`**, for a `p`-adically
complete `M`: the completion of `m ⊗ ω ↦ c_j(ω) m`. -/
def contraction (hM : IsPAdicallyComplete p D M) (j : C.ι) :
    CompletedTensor p (D : Type u) C.forms M →ₗ[(D : Type u)] M :=
  letI : IsAdicComplete (pAdicIdeal (A := (D : Type u)) p) M := hM
  (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := (D : Type u)) p) M).symm.toLinearMap ∘ₗ
    (AdicCompletion.map (pAdicIdeal (A := (D : Type u)) p)
      (dualTensorCoordinate M (C.coordFun j))).restrictScalars (D : Type u)

/-- The contraction on the image of the uncompleted tensor product. -/
theorem contraction_of (hM : IsPAdicallyComplete p D M) (j : C.ι) (t : M ⊗[(D : Type u)] C.forms) :
    C.contraction hM j (toCompletedTensor p (D : Type u) C.forms M t) =
      dualTensorCoordinate M (C.coordFun j) t := by
  let : IsAdicComplete (pAdicIdeal (A := (D : Type u)) p) M := hM
  simp only [contraction, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.coe_restrictScalars, toCompletedTensor, AdicCompletion.map_of]
  exact AdicCompletion.ofLinearEquiv_symm_of _ _

/-- **Every element of `M ⊗_D Ω` is, modulo `pⁿ`, its finite coordinate sum**: for every finset
containing a suitable finite set of coordinates. -/
theorem exists_tensor_approx (t : M ⊗[(D : Type u)] C.forms) (n : ℕ) :
    ∃ T : Finset C.ι, ∀ S : Finset C.ι, T ⊆ S →
      t - ∑ i ∈ S, (dualTensorCoordinate M (C.coordFun i) t) ⊗ₜ[(D : Type u)] C.dx i ∈
        ((pAdicIdeal (A := (D : Type u)) p) ^ n • ⊤ :
          Submodule (D : Type u) (M ⊗[(D : Type u)] C.forms)) := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun S _ ↦ by simp⟩
  | tmul m ω =>
    obtain ⟨T, hT, happrox⟩ := C.approx ω n
    refine ⟨T, fun S hS ↦ ?_⟩
    have hsplit : (m ⊗ₜ[(D : Type u)] ω) -
        ∑ i ∈ S, (dualTensorCoordinate M (C.coordFun i) (m ⊗ₜ[(D : Type u)] ω)) ⊗ₜ[(D : Type u)]
          C.dx i =
        m ⊗ₜ[(D : Type u)] (ω - ∑ i ∈ T, C.coordFun i ω • C.dx i) -
          ∑ i ∈ S \ T, C.coordFun i ω • (m ⊗ₜ[(D : Type u)] C.dx i) := by
      simp only [dualTensorCoordinate_tmul, TensorProduct.tmul_sub, TensorProduct.tmul_sum,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [← Finset.sum_sdiff hS]
      abel
    rw [hsplit]
    refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun i hi ↦ ?_)
    · exact map_mem_pow_smul_top_of_mem _ ((TensorProduct.mk (D : Type u) M C.forms) m) n
        happrox
    · exact Submodule.smul_mem_smul (hT i (Finset.mem_sdiff.mp hi).2) Submodule.mem_top
  | add t t' ht ht' =>
    obtain ⟨T, hT⟩ := ht
    obtain ⟨T', hT'⟩ := ht'
    refine ⟨T ∪ T', fun S hS ↦ ?_⟩
    have h := Submodule.add_mem _ (hT S (Finset.union_subset_left hS))
      (hT' S (Finset.union_subset_right hS))
    convert h using 1
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
    abel

/-- **Every element of `M ⊗̂ Ω` is the `p`-adically convergent sum of its contractions against
the `d x_i`.** -/
theorem hasSum_contraction (hM : IsPAdicallyComplete p D M)
    (z : CompletedTensor p (D : Type u) C.forms M) :
    letI := completedTensorTopology p (D : Type u) C.forms M
    HasSum (fun i ↦ toCompletedTensor p (D : Type u) C.forms M
      (C.contraction hM i z ⊗ₜ[(D : Type u)] C.dx i)) z := by
  classical
  refine hasSum_adicCompletion_of_eval_eventually_eq _ (Submodule.fg_span_singleton _) _ _
    fun n ↦ ?_
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (z.val n)
  have hz := sub_of_mem_pow_smul_top p z n t ht.symm
  obtain ⟨T, hT⟩ := C.exists_tensor_approx t n
  refine ⟨T, fun S hS ↦ ?_⟩
  have hS' := hT S hS
  have hcontr : ∀ i, C.contraction hM i z - dualTensorCoordinate M (C.coordFun i) t ∈
      pPowSmul p (D : Type u) M n := by
    intro i
    rw [← C.contraction_of hM i t, ← map_sub]
    exact map_mem_pow_smul_top_of_mem _ _ n hz
  have hdecomp : ∑ i ∈ S, toCompletedTensor p (D : Type u) C.forms M
        (C.contraction hM i z ⊗ₜ[(D : Type u)] C.dx i) - z =
      ∑ i ∈ S, toCompletedTensor p (D : Type u) C.forms M
          ((C.contraction hM i z - dualTensorCoordinate M (C.coordFun i) t) ⊗ₜ[(D : Type u)]
            C.dx i) -
        toCompletedTensor p (D : Type u) C.forms M
          (t - ∑ i ∈ S, (dualTensorCoordinate M (C.coordFun i) t) ⊗ₜ[(D : Type u)] C.dx i) -
        (z - toCompletedTensor p (D : Type u) C.forms M t) := by
    simp only [TensorProduct.sub_tmul, map_sub, map_sum, Finset.sum_sub_distrib]
    abel
  have hmem : ∑ i ∈ S, toCompletedTensor p (D : Type u) C.forms M
        (C.contraction hM i z ⊗ₜ[(D : Type u)] C.dx i) - z ∈
      ((pAdicIdeal (A := (D : Type u)) p) ^ n • ⊤ :
        Submodule (D : Type u) (CompletedTensor p (D : Type u) C.forms M)) := by
    rw [hdecomp]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ ↦ ?_)
      (map_mem_pow_smul_top_of_mem _ _ n hS')) hz
    obtain ⟨y, hy⟩ := (mem_pPowSmul_iff p (D : Type u) M).mp (hcontr i)
    rw [← hy, ← TensorProduct.smul_tmul', map_smul]
    exact Submodule.smul_mem_smul (CompletedDeRham.pow_mem_pAdicIdeal_pow p (D : Type u) n)
      Submodule.mem_top
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
    map_sub, sub_eq_zero] at hmem
  exact hmem

/-- **Every completed connection on a `p`-adically complete module has a coordinate
expansion** `∇ m = ∑_i θ_i(m) d x_i`, converging `p`-adically. -/
theorem exists_isCoordinateExpansion (hM : IsPAdicallyComplete p D M)
    (nabla : CompletedConnection p (D : Type u) C.forms C.diff M) :
    ∃ theta : C.ι → (M → M), IsCoordinateExpansion p (D : Type u) C.forms C.dx nabla theta :=
  ⟨fun i m ↦ C.contraction hM i (nabla m), fun m ↦ C.hasSum_contraction hM (nabla m)⟩

end Expansion

/-! #### The curvature in the coordinates -/

section Curvature

variable {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
  (nabla : CompletedConnection p (D : Type u) C.forms C.diff M) {theta : C.ι → (M → M)}

/-- **The curvature at one level, in the coordinates**: over a finset carrying the level-`n`
expansions of `∇ m` and of the `∇(θ_j m)`, the level-`n` value of `∇² m` is that of
`∑_{j,k} θ_k θ_j m ⊗ (d x_j ∧ d x_k)`. -/
theorem differential_nabla_val (n : ℕ) (s : Finset C.ι) (m : M)
    (h0 : CompletedDeRham.IsLevelExpansionAt p (D : Type u) C.forms C.dx nabla theta n s m)
    (h1 : ∀ j ∈ s,
      CompletedDeRham.IsLevelExpansionAt p (D : Type u) C.forms C.dx nabla theta n s (theta j m)) :
    (CompletedDeRham.differential p (D : Type u) C.Om C.wedge C.deRham M nabla C.isGradedLeibniz 1
        (nabla m)).val n =
      (∑ j ∈ s, ∑ k ∈ s, toCompletedTensor p (D : Type u) (C.Om (1 + 1)) M
        (theta k (theta j m) ⊗ₜ[(D : Type u)] C.wedge 1 (C.dx j) (C.dx k))).val n := by
  rw [CompletedDeRham.differential_val_congr p (D : Type u) C.Om C.wedge C.deRham M nabla
      C.isGradedLeibniz 1 n _ _ h0, map_sum, CompletedDeRham.val_sum_apply,
    CompletedDeRham.val_sum_apply]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [CompletedDeRham.differential_toCompletedTensor_tmul_val p (D : Type u) C.Om C.wedge C.deRham
      M nabla C.isGradedLeibniz C.dx theta 1 n s (theta j m) (C.dx j) (h1 j hj),
    C.deRham_diff, TensorProduct.tmul_zero, map_zero, add_zero]

/-- A finset carrying the level-`n` expansions of `∇ m` and of every `∇(θ_j m)`, `j` in it, and
containing a given finset. -/
theorem exists_levelExpansion_superset
    (hco : IsCoordinateExpansion p (D : Type u) C.forms C.dx nabla theta) (n : ℕ) (m : M)
    (s₀ : Finset C.ι) :
    ∃ s : Finset C.ι, s₀ ⊆ s ∧
      CompletedDeRham.IsLevelExpansionAt p (D : Type u) C.forms C.dx nabla theta n s m ∧
      ∀ j ∈ s, CompletedDeRham.IsLevelExpansionAt p (D : Type u) C.forms C.dx nabla theta n s
        (theta j m) := by
  classical
  have hsupp := fun (x : M) ↦ finite_notMem_pPowSmul_of_isCoordinateDual hco C.isCoordinateDual x n
  set s₁ := s₀ ∪ (hsupp m).toFinset with hs₁
  refine ⟨s₁ ∪ s₁.biUnion fun j ↦ (hsupp (theta j m)).toFinset,
    fun i hi ↦ Finset.mem_union_left _ (Finset.mem_union_left _ hi), ?_, fun j hj ↦ ?_⟩
  · refine isLevelExpansionAt_of_support_subset p (D : Type u) C.forms M hco m n _ fun i hi ↦ ?_
    exact Finset.mem_union_left _ (Finset.mem_union_right _ ((hsupp m).mem_toFinset.mpr hi))
  · refine isLevelExpansionAt_of_support_subset p (D : Type u) C.forms M hco (theta j m) n _
      fun k hk ↦ ?_
    by_cases hjs : j ∈ s₁
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, hjs, (hsupp (theta j m)).mem_toFinset.mpr hk⟩)
    · exfalso
      have hmem : theta j m ∈ pPowSmul p (D : Type u) M n := by
        by_contra hcon
        exact hjs (Finset.mem_union_right _ ((hsupp m).mem_toFinset.mpr hcon))
      exact hk (theta_mem_pPowSmul_of_mem_of_isCoordinateDual p hco C.isCoordinateDual n k hmem)

/-- **Commuting coordinate operators give a connection of curvature zero.** -/
theorem isCurvatureZero_of_comm
    (hco : IsCoordinateExpansion p (D : Type u) C.forms C.dx nabla theta)
    (hcomm : ∀ j k, theta j ∘ theta k = theta k ∘ theta j) :
    CompletedDeRham.IsCurvatureZero p (D : Type u) C.Om C.wedge C.deRham M nabla
      C.isGradedLeibniz := by
  classical
  intro m
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨s, -, h0, h1⟩ := C.exists_levelExpansion_superset nabla hco n m ∅
  rw [C.differential_nabla_val nabla n s m h0 h1, AdicCompletion.val_zero_apply]
  have hzero : (∑ j ∈ s, ∑ k ∈ s, toCompletedTensor p (D : Type u) (C.Om (1 + 1)) M
      (theta k (theta j m) ⊗ₜ[(D : Type u)] C.wedge 1 (C.dx j) (C.dx k))) = 0 := by
    rw [← Finset.sum_product']
    refine Finset.sum_involution (fun a _ ↦ a.swap) (fun a _ ↦ ?_) (fun a _ hne ↦ ?_)
      (fun a ha ↦ Finset.mem_product.mpr ⟨(Finset.mem_product.mp ha).2,
        (Finset.mem_product.mp ha).1⟩) (fun a _ ↦ Prod.swap_swap a)
    · obtain ⟨j, k⟩ := a
      have hjk : theta j (theta k m) = theta k (theta j m) := congrFun (hcomm j k) m
      simp only [Prod.swap_prod_mk, hjk]
      rw [← map_add, ← TensorProduct.tmul_add, C.wedge_anti, TensorProduct.tmul_zero, map_zero]
    · obtain ⟨j, k⟩ := a
      intro heq
      rw [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      exact hne (by rw [C.wedge_self, TensorProduct.tmul_zero, map_zero])
  rw [hzero, AdicCompletion.val_zero_apply]

/-- **A connection of curvature zero has commuting coordinate operators.** -/
theorem comm_of_isCurvatureZero (hM : IsPAdicallyComplete p D M)
    (hco : IsCoordinateExpansion p (D : Type u) C.forms C.dx nabla theta)
    (hcurv : CompletedDeRham.IsCurvatureZero p (D : Type u) C.Om C.wedge C.deRham M nabla
      C.isGradedLeibniz) (a c : C.ι) :
    theta a ∘ theta c = theta c ∘ theta a := by
  classical
  funext m
  refine hM.toIsHausdorff.haus' _ (fun n ↦ ?_) |> sub_eq_zero.mp
  rw [SModEq.zero]
  obtain ⟨s, hs, h0, h1⟩ := C.exists_levelExpansion_superset nabla hco n m {a, c}
  have has : a ∈ s := hs (Finset.mem_insert_self a {c})
  have hcs : c ∈ s := hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
  have hval := C.differential_nabla_val nabla n s m h0 h1
  rw [hcurv m, AdicCompletion.val_zero_apply] at hval
  set y : M ⊗[(D : Type u)] C.Om (1 + 1) := ∑ j ∈ s, ∑ k ∈ s,
    theta k (theta j m) ⊗ₜ[(D : Type u)] C.wedge 1 (C.dx j) (C.dx k) with hy
  have hx : (∑ j ∈ s, ∑ k ∈ s, toCompletedTensor p (D : Type u) (C.Om (1 + 1)) M
      (theta k (theta j m) ⊗ₜ[(D : Type u)] C.wedge 1 (C.dx j) (C.dx k))) =
      toCompletedTensor p (D : Type u) (C.Om (1 + 1)) M y := by
    simp only [hy, map_sum]
  rw [hx] at hval
  have hfun : completedTensorFunctionalLevel p (D : Type u) (C.Om (1 + 1)) M
      (dualTensorCoordinate M (C.twoFormFun a c)) n
      (toCompletedTensor p (D : Type u) (C.Om (1 + 1)) M y) = 0 := by
    change pLevelMapQ p (D : Type u) (M ⊗[(D : Type u)] C.Om (1 + 1)) M
      (dualTensorCoordinate M (C.twoFormFun a c)) n
      (AdicCompletion.eval (pAdicIdeal (A := (D : Type u)) p) (M ⊗[(D : Type u)] C.Om (1 + 1)) n
        (toCompletedTensor p (D : Type u) (C.Om (1 + 1)) M y)) = 0
    rw [AdicCompletion.eval_apply, ← hval, map_zero]
  rw [completedTensorFunctionalLevel_of] at hfun
  have hcoef : dualTensorCoordinate M (C.twoFormFun a c) y =
      theta a (theta c m) - theta c (theta a m) := by
    simp only [hy, map_sum, dualTensorCoordinate_tmul, C.twoFormFun_wedge, sub_smul, ite_mul,
      one_mul, zero_mul, ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', has, hcs, ite_true]
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hfun
  rw [hcoef] at hmem
  exact hmem

/-- **Over topological coordinates, the curvature of a completed connection vanishes if and only
if its coordinate operators commute**: the two readings of integrability, Remark
[Stacks, Tag 07I0] and [Stacks, Tag 07JD], agree. -/
theorem isCurvatureZero_iff (hM : IsPAdicallyComplete p D M)
    (hco : IsCoordinateExpansion p (D : Type u) C.forms C.dx nabla theta) :
    CompletedDeRham.IsCurvatureZero p (D : Type u) C.Om C.wedge C.deRham M nabla
        C.isGradedLeibniz ↔ ∀ j k, theta j ∘ theta k = theta k ∘ theta j :=
  ⟨fun h j k ↦ C.comm_of_isCurvatureZero nabla hM hco h j k,
    fun h ↦ C.isCurvatureZero_of_comm nabla hco h⟩

end Curvature

end CompletedCoordinateDualData

/-! ### The retract data and the pairs over `D'` -/

/-- **A retract `a ∘ b = id` of rings with differentials** over topological coordinates `C` of
`D`: ring maps `a : D → D'` and `b : D' → D` with `a ∘ b = id_{D'}`, graded forms `Ω'^*` of `D'`
with their differential, the comparisons `ψ_a`, `ψ_b` of Remark [Stacks, Tag 07KJ] with
`ψ_a ∘ ψ_b = id` on one-forms, and, for the round trip `ρ = b ∘ a`, its compatibility with the
augmentation and **Taylor's formula** `a = ∑_J ρ(∂_J a) ξ^{[J]}`, `ρ(a) = ∑_J ∂_J(a) (-ξ)^{[J]}`
for `ξ_i = x_i - ρ(x_i)`, modulo every `p^n`.  These are the fields of `Crystalline.RetractData`,
over topological coordinates. -/
structure CoordinateDualRetractData (p : ℕ) (D : DividedPowerRing.{u})
    (C : CompletedCoordinateDualData p D) where
  /-- The ring `D'`. -/
  ring : Type u
  /-- Its ring structure. -/
  [commRing : CommRing ring]
  /-- The map `a : D → D'`. -/
  [algebraA : Algebra (D : Type u) ring]
  /-- The map `b : D' → D`. -/
  [algebraB : Algebra ring (D : Type u)]
  /-- `a ∘ b = id_{D'}`. -/
  [retract : IsScalarTower ring (D : Type u) ring]
  /-- The modules of forms `Ω'^i` of `D'`. -/
  Om : ℕ → Type u
  /-- Their additive group structures. -/
  [addCommGroup : ∀ i, AddCommGroup (Om i)]
  /-- Their `D'`-module structures. -/
  [module : ∀ i, Module ring (Om i)]
  /-- The wedge product of the forms of `D'`. -/
  wedge : ∀ i, Om i →ₗ[ring] Om 1 →ₗ[ring] Om (i + 1)
  /-- The de Rham differential of the forms of `D'`. -/
  deRham : ∀ i, Om i →+ Om (i + 1)
  /-- The differential `d' : D' → Ω'^1`. -/
  diff : ring → Om 1
  /-- `d'` is additive. -/
  diff_add : ∀ x y : ring, diff (x + y) = diff x + diff y
  /-- `d'` obeys the Leibniz rule. -/
  diff_mul : ∀ x y : ring, diff (x * y) = x • diff y + y • diff x
  /-- The Leibniz rule of the forms of `D'`. -/
  isGradedLeibniz : CompletedDeRham.IsGradedLeibniz ring Om wedge deRham diff
  /-- The wedge product of one-forms of `D'` is antisymmetric. -/
  wedge_anti : ∀ η ζ : Om 1, wedge 1 η ζ + wedge 1 ζ η = 0
  /-- Exact one-forms of `D'` are closed. -/
  deRham_diff : ∀ c : ring, deRham 1 (diff c) = 0
  /-- The comparisons `ψ_a : Ω^i → Ω'^i` along `a`. -/
  psiA : ∀ i, C.Om i →ₛₗ[algebraMap (D : Type u) ring] Om i
  /-- The comparisons `ψ_b : Ω'^i → Ω^i` along `b`. -/
  psiB : ∀ i, Om i →ₛₗ[algebraMap ring (D : Type u)] C.Om i
  /-- `ψ_a (d x) = d' (a x)`. -/
  psiA_diff : ∀ x : (D : Type u), psiA 1 (C.diff x) = diff (algebraMap (D : Type u) ring x)
  /-- `ψ_b (d' x) = d (b x)`. -/
  psiB_diff : ∀ x : ring, psiB 1 (diff x) = C.diff (algebraMap ring (D : Type u) x)
  /-- `ψ_a` is multiplicative for the wedge product. -/
  psiA_wedge : ∀ (i : ℕ) (ω : C.Om i) (η : C.Om 1),
    psiA (i + 1) (C.wedge i ω η) = wedge i (psiA i ω) (psiA 1 η)
  /-- `ψ_b` is multiplicative for the wedge product. -/
  psiB_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psiB (i + 1) (wedge i ω η) = C.wedge i (psiB i ω) (psiB 1 η)
  /-- `ψ_a` commutes with the de Rham differentials. -/
  psiA_deRham : ∀ (i : ℕ) (ω : C.Om i), psiA (i + 1) (C.deRham i ω) = deRham i (psiA i ω)
  /-- `ψ_b` commutes with the de Rham differentials. -/
  psiB_deRham : ∀ (i : ℕ) (ω : Om i), psiB (i + 1) (deRham i ω) = C.deRham i (psiB i ω)
  /-- `ψ_a ∘ ψ_b = id` on one-forms. -/
  psiA_psiB : ∀ ω : Om 1, psiA 1 (psiB 1 ω) = ω
  /-- The round trip `ρ = b ∘ a` moves elements within the divided power ideal. -/
  rho_sub_mem : ∀ y : (D : Type u),
    algebraMap ring (D : Type u) (algebraMap (D : Type u) ring y) - y ∈ D.ideal
  /-- Taylor's formula `a = ∑_J ρ(∂_J a) ξ^{[J]}` modulo every `p^n`. -/
  taylor : ∀ (a : (D : Type u)) (n : ℕ), ∃ T : Finset (C.ι →₀ ℕ),
    (∀ J ∉ T, C.deltaPow J a ∈ pAdicIdeal (A := (D : Type u)) p ^ n) ∧
      a - ∑ J ∈ T, algebraMap ring (D : Type u) (algebraMap (D : Type u) ring (C.deltaPow J a)) *
        taylorMonomial D (fun i ↦ C.coord i -
          algebraMap ring (D : Type u) (algebraMap (D : Type u) ring (C.coord i))) J ∈
        pAdicIdeal (A := (D : Type u)) p ^ n
  /-- Taylor's formula `ρ(a) = ∑_J ∂_J(a) (-ξ)^{[J]}` modulo every `p^n`. -/
  taylor' : ∀ (a : (D : Type u)) (n : ℕ), ∃ T : Finset (C.ι →₀ ℕ),
    (∀ J ∉ T, C.deltaPow J a ∈ pAdicIdeal (A := (D : Type u)) p ^ n) ∧
      algebraMap ring (D : Type u) (algebraMap (D : Type u) ring a) -
        ∑ J ∈ T, C.deltaPow J a * taylorMonomial D (-fun i ↦ C.coord i -
          algebraMap ring (D : Type u) (algebraMap (D : Type u) ring (C.coord i))) J ∈
        pAdicIdeal (A := (D : Type u)) p ^ n

attribute [instance] CoordinateDualRetractData.commRing CoordinateDualRetractData.algebraA
  CoordinateDualRetractData.algebraB CoordinateDualRetractData.retract
  CoordinateDualRetractData.addCommGroup CoordinateDualRetractData.module

/-- The module of one-forms `Ω' = Ω'^1` of `D'`. -/
abbrev CoordinateDualRetractData.forms {p : ℕ} {D : DividedPowerRing.{u}}
    {C : CompletedCoordinateDualData p D} (R : CoordinateDualRetractData p D C) : Type u :=
  R.Om 1

section Category

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateDualData p D)
  (R : CoordinateDualRetractData p D C)

/-- **A pair over `D'`** in the sense of [Stacks, Lemma 60.17.5, Tag 07L5] and of
[Stacks, Remark 60.17.6, Tag 07L6]: a `p`-adically complete `D'`-module ([Stacks, Tag 07JB]) with a
completed connection `∇' : M' → M' ⊗̂_{D'} Ω'` ([Stacks, Tag 07JC]) which is integrable — its
curvature `M' → M' ⊗̂ Ω'^2` vanishes, Remark [Stacks, Tag 07I0], [Stacks, Tag 07JD] — and
topologically quasi-nilpotent in the sense the proof of [Stacks, Tag 07L5] gives the condition
over `D'`: "Let us say that `(M', ∇')` has property (07JE) if this is true for `G(M', ∇')`", `G`
being the base change along `b : D' → D` ([Stacks, Tag 07JE]). -/
structure CoordinateDualRetractPair where
  /-- The underlying module `M'`. -/
  carrier : Type u
  /-- Its additive group structure. -/
  [addCommGroup : AddCommGroup carrier]
  /-- Its `D'`-module structure. -/
  [module : Module R.ring carrier]
  /-- The module is `p`-adically complete. -/
  isPAdicallyComplete : IsPAdicallyComplete p R.ring carrier
  /-- The connection `∇' : M' → M' ⊗̂_{D'} Ω'`. -/
  nabla : CompletedConnection p R.ring R.forms R.diff carrier
  /-- The connection is integrable: its curvature vanishes (Remark [Stacks, Tag 07I0]). -/
  isIntegrable : CompletedDeRham.IsCurvatureZero p R.ring R.Om R.wedge R.deRham carrier nabla
    R.isGradedLeibniz
  /-- The base change of the connection along `b` is topologically quasi-nilpotent. -/
  isTopologicallyQuasiNilpotent_back : IsTopologicallyQuasiNilpotent p D C.forms C.dx
    (CompletedConnection.baseChange p R.ring D carrier R.forms C.forms C.diff (R.psiB 1) nabla
      C.diff_add C.diff_mul R.psiB_diff)

attribute [instance] CoordinateDualRetractPair.addCommGroup CoordinateDualRetractPair.module

/-- A morphism of pairs over `D'`: a horizontal `D'`-linear map. -/
@[ext] structure CoordinateDualRetractPairHom (P Q : CoordinateDualRetractPair C R) where
  /-- The underlying `D'`-linear map. -/
  toLinearMap : P.carrier →ₗ[R.ring] Q.carrier
  /-- Horizontality: the map commutes with the two connections. -/
  horizontal : ∀ m : P.carrier, Q.nabla (toLinearMap m) =
    AdicCompletion.map (pAdicIdeal (A := R.ring) p)
      (TensorProduct.map toLinearMap (LinearMap.id (R := R.ring) (M := R.forms))) (P.nabla m)

/-- The pairs over `D'` and their horizontal maps form a category. -/
instance instCategoryCoordinateDualRetractPair : Category (CoordinateDualRetractPair C R) where
  Hom P Q := CoordinateDualRetractPairHom C R P Q
  id P := ⟨LinearMap.id, by intro m; simp⟩
  comp {P Q R'} f g := ⟨g.toLinearMap ∘ₗ f.toLinearMap, by
    intro m
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [g.horizontal, f.horizontal, AdicCompletion.map_comp_apply, ← TensorProduct.map_comp]
    simp⟩
  id_comp f := by apply CoordinateDualRetractPairHom.ext; simp
  comp_id f := by apply CoordinateDualRetractPairHom.ext; simp
  assoc f g h := by apply CoordinateDualRetractPairHom.ext; simp [LinearMap.comp_assoc]

/-- The underlying map of an identity morphism of pairs over `D'`. -/
@[simp] theorem CoordinateDualRetractPair.id_toLinearMap (P : CoordinateDualRetractPair C R) :
    CoordinateDualRetractPairHom.toLinearMap (𝟙 P) = LinearMap.id := rfl

/-- The underlying map of a composite of morphisms of pairs over `D'`. -/
@[simp] theorem CoordinateDualRetractPair.comp_toLinearMap {P Q Q' : CoordinateDualRetractPair C R}
    (f : P ⟶ Q) (g : Q ⟶ Q') :
    CoordinateDualRetractPairHom.toLinearMap (f ≫ g) = g.toLinearMap ∘ₗ f.toLinearMap := rfl

/-- **An isomorphism of pairs over `D'` from a horizontal linear equivalence.** -/
def CoordinateDualRetractPair.isoOfHorizontalEquiv {P Q : CoordinateDualRetractPair C R}
    (e : P.carrier ≃ₗ[R.ring] Q.carrier)
    (he : ∀ m, Q.nabla (e m) = AdicCompletion.map (pAdicIdeal (A := R.ring) p)
      (TensorProduct.map e.toLinearMap (LinearMap.id (R := R.ring) (M := R.forms))) (P.nabla m)) :
    P ≅ Q where
  hom := ⟨e.toLinearMap, he⟩
  inv := ⟨e.symm.toLinearMap, horizontal_symm p e he⟩
  hom_inv_id := CoordinateDualRetractPairHom.ext (LinearMap.ext fun m ↦ e.symm_apply_apply m)
  inv_hom_id := CoordinateDualRetractPairHom.ext (LinearMap.ext fun m ↦ e.apply_symm_apply m)

end Category

namespace CoordinateDual

/-! ### Generalities on coordinate operators from a dual family -/

section Generalities

variable (p : ℕ) {D : Type u} [CommRing D] {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] {ι : Type u} {dx : ι → Omega} {dd : D → Omega}
  {coord : ι → (Omega →ₗ[D] D)}

/-- **A pair transported along a horizontal linear equivalence stays topologically
quasi-nilpotent**, from a dual family of coordinate functionals. -/
theorem isTopologicallyQuasiNilpotent_of_horizontalEquiv
    (P : Pair.{u, u, u, u} p D Omega dx dd) (hc : IsCoordinateDual dx coord) {N : Type u}
    [AddCommGroup N] [Module D N] (hN : IsPAdicallyComplete p D N)
    (nablaN : CompletedConnection p D Omega dd N) (e : P.carrier ≃ₗ[D] N)
    (he : ∀ m, nablaN (e m) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map e.toLinearMap (LinearMap.id (R := D) (M := Omega))) (P.nabla m)) :
    IsTopologicallyQuasiNilpotent p D Omega dx nablaN := by
  classical
  obtain ⟨theta, hθ⟩ := P.hasCoordinateOperators
  set theta' : ι → (N → N) := fun i z ↦ e (theta i (e.symm z)) with htheta'
  have hθ' : IsCoordinateExpansion p D Omega dx nablaN theta' := by
    intro z
    let := completedTensorTopology p D Omega P.carrier
    let := completedTensorTopology p D Omega N
    have hmap := (hθ (e.symm z)).map (AdicCompletion.map (pAdicIdeal (A := D) p)
        (TensorProduct.map e.toLinearMap (LinearMap.id (R := D) (M := Omega)))).toAddMonoidHom
      (continuous_linearMap_adicModuleTopology (pAdicIdeal (A := D) p)
        ((AdicCompletion.map (pAdicIdeal (A := D) p)
          (TensorProduct.map e.toLinearMap (LinearMap.id (R := D) (M := Omega)))).restrictScalars
              D))
    have hz : nablaN z = AdicCompletion.map (pAdicIdeal (A := D) p)
        (TensorProduct.map e.toLinearMap (LinearMap.id (R := D) (M := Omega)))
        (P.nabla (e.symm z)) := by
      rw [← he, LinearEquiv.apply_symm_apply]
    rw [hz]
    convert hmap using 1
    all_goals try rfl
  intro thetaN hθN z
  rw [eq_of_isCoordinateExpansion_of_isCoordinateDual p D Omega N hθN hθ' hc hN.toIsHausdorff]
  have hiter : ∀ (i : ι) (k : ℕ) (y : N), (theta' i)^[k] y = e ((theta i)^[k] (e.symm y)) := by
    intro i k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      simp [htheta']
  refine (P.isTopologicallyQuasiNilpotent theta hθ (e.symm z)).subset fun q hq ↦ ⟨hq.1, fun hmem ↦
    hq.2 ?_⟩
  rw [hiter]
  exact Submodule.smul_top_le_comap_smul_top _ e.toLinearMap hmem

end Generalities

/-! ### The coordinate operators of a pair over `D` -/

section PairOperators

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateDualData p D)

/-- **The coordinate operators `θ_i` of a pair over `D`**: `∇ m = ∑_i θ_i(m) d x_i`. -/
def pairTheta (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) : C.ι → (P.carrier → P.carrier) :=
  P.hasCoordinateOperators.choose

/-- The coordinate operators realize the coordinate expansion. -/
theorem isCoordinateExpansion_pairTheta (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    IsCoordinateExpansion p (D : Type u) C.forms C.dx P.nabla (pairTheta C P) :=
  P.hasCoordinateOperators.choose_spec

/-- The coordinate operators are additive. -/
theorem pairTheta_add (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) (i : C.ι)
    (x y : P.carrier) : pairTheta C P i (x + y) = pairTheta C P i x + pairTheta C P i y :=
  coordinate_map_add (isCoordinateExpansion_pairTheta C P) C.isCoordinateDual
    P.isPAdicallyComplete.toIsHausdorff i x y

/-- The coordinate operators commute. -/
theorem pairTheta_comm (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) (i j : C.ι) :
    pairTheta C P i ∘ pairTheta C P j = pairTheta C P j ∘ pairTheta C P i :=
  P.isIntegrable _ (isCoordinateExpansion_pairTheta C P) i j

/-- The Leibniz rule `θ_i(a m) = a θ_i(m) + ∂_i(a) m`. -/
theorem pairTheta_smul (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) (i : C.ι)
    (a : (D : Type u)) (m : P.carrier) :
    pairTheta C P i (a • m) = a • pairTheta C P i m + C.coordFun i (C.diff a) • m :=
  coordinate_leibniz (isCoordinateExpansion_pairTheta C P) C.isCoordinateDual
    P.isPAdicallyComplete.toIsHausdorff i a m

/-- **The composite coordinate operators `θ_K = ∏_i θ_i^{k_i}` of a pair over `D`.** -/
def pairThetaPow (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    (C.ι →₀ ℕ) → (P.carrier → P.carrier) :=
  (exists_isThetaMonomialFamily (pairTheta C P) (pairTheta_comm C P)).choose

/-- The composite operators are the composites of the coordinate operators. -/
theorem isThetaMonomialFamily_pairThetaPow (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    IsThetaMonomialFamily P.carrier (pairTheta C P) (pairThetaPow C P) :=
  (exists_isThetaMonomialFamily (pairTheta C P) (pairTheta_comm C P)).choose_spec

/-- **Item (07JE) of a pair over `D`, at every level**: only finitely many composite operators
take a given element outside `p^n M`. -/
theorem finite_pairThetaPow (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) (n : ℕ)
    (m : P.carrier) :
    {K : C.ι →₀ ℕ | pairThetaPow C P K m ∉ pPowSmul p (D : Type u) P.carrier n}.Finite :=
  finite_thetaPow_notMem_pPowSmul p (D : Type u) P.carrier (isThetaMonomialFamily_pairThetaPow C P)
    (pairTheta_add C P)
    (fun i m ↦ by
      have h := P.isTopologicallyQuasiNilpotent _ (isCoordinateExpansion_pairTheta C P) m
      exact (h.preimage (f := fun k : ℕ ↦ (i, k)) fun _ _ _ _ h ↦ by
        simpa using h).subset fun k hk ↦ hk)
    (finite_notMem_pPowSmul_of_isCoordinateDual (isCoordinateExpansion_pairTheta C P)
      C.isCoordinateDual m n)

end PairOperators

/-! ### The Taylor comparison and its horizontality -/

/-- The negative of a family of elements of the divided power ideal stays in the ideal. -/
theorem neg_mem_ideal_family {D : DividedPowerRing.{u}} {ι : Type u}
    {xi : ι → (D : Type u)} (hxi : ∀ i, xi i ∈ D.ideal) (i : ι) : (-xi) i ∈ D.ideal := by
  simpa using D.ideal.neg_mem (hxi i)

/-- A linear map `φ` whose composite with `incl` is the Taylor sum for `eta` sends the Taylor sum
for `zeta` with `zeta + eta = 0` to the inclusion `incl'`. -/
theorem map_completeTaylorSum_eq_of_comp (p : ℕ) (D : DividedPowerRing.{u}) {ι : Type u}
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

/-- **The reindexing `K = K' + e_i`** of the differentiated Taylor series over a downward closed
finite set `R` of multi-indices whose supports lie in a finset `T` of coordinates. -/
theorem sum_support_sub_single_eq_of_subset {ι : Type u} [DecidableEq ι] {X : Type u}
    [AddCommGroup X] (R : Finset (ι →₀ ℕ)) (hR : ∀ K ∈ R, ∀ L ≤ K, L ∈ R) (T : Finset ι)
    (hT : ∀ K ∈ R, K.support ⊆ T) (f : (ι →₀ ℕ) → ι → X) :
    ∑ K ∈ R, ∑ i ∈ K.support, f (K - Finsupp.single i 1) i =
      ∑ i ∈ T, ∑ K ∈ R.filter (fun K ↦ K + Finsupp.single i 1 ∈ R), f K i := by
  have h1 : ∀ K ∈ R, ∑ i ∈ K.support, f (K - Finsupp.single i 1) i =
      ∑ i ∈ T, if K i ≠ 0 then f (K - Finsupp.single i 1) i else 0 := by
    intro K hK
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext i
    simp only [Finsupp.mem_support_iff, Finset.mem_filter, iff_and_self]
    exact fun hi ↦ hT K hK (Finsupp.mem_support_iff.mpr hi)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
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

section TaylorComparison

variable (p : ℕ) (D : DividedPowerRing.{u}) {ι : Type u} [DecidableEq ι]
  {M : Type u} [AddCommGroup M] [Module (D : Type u) M] (hM : IsPAdicallyComplete p D M)
  {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}
  (hfamM : IsThetaMonomialFamily M theta thetaPow)
  (hfin : ∀ (n : ℕ) (m : M),
    {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite)
  (hadd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
  {N : Type u} [AddCommGroup N] [Module (D : Type u) N] (hN : IsPAdicallyComplete p D N)
  (ρ : (D : Type u) →+* (D : Type u)) (incl : M →ₛₗ[ρ] N)
  (xi : ι → (D : Type u)) (hxi : ∀ i, xi i ∈ D.ideal)
  {delta : ι → (D.carrier → D.carrier)} {deltaPow : (ι →₀ ℕ) → (D.carrier → D.carrier)}
  (hfamD : IsThetaMonomialFamily (D : Type u) delta deltaPow)
  (hleib : ∀ (i : ι) (a : (D : Type u)) (m : M), theta i (a • m) = a • theta i m + delta i a • m)
  (htay : ∀ (a : (D : Type u)) (n : ℕ), ∃ T : Finset (ι →₀ ℕ),
    (∀ J ∉ T, deltaPow J a ∈ pAdicIdeal (A := (D : Type u)) p ^ n) ∧
      a - ∑ J ∈ T, ρ (deltaPow J a) * taylorMonomial D xi J ∈
        pAdicIdeal (A := (D : Type u)) p ^ n)
  (htay' : ∀ (a : (D : Type u)) (n : ℕ), ∃ T : Finset (ι →₀ ℕ),
    (∀ J ∉ T, deltaPow J a ∈ pAdicIdeal (A := (D : Type u)) p ^ n) ∧
      ρ a - ∑ J ∈ T, deltaPow J a * taylorMonomial D (-xi) J ∈
        pAdicIdeal (A := (D : Type u)) p ^ n)

/-- **The comparison** `Φ(m) = ∑_K ξ^{[K]} • ι(θ_K m)`, as an additive map. -/
def taylorCompareAdd : M →+ N :=
  AddMonoidHom.mk' (completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN)
    (taylorSum_add p D incl.toAddMonoidHom xi hfin hN hfamM hadd)

/-- The value of `Crystalline.CoordinateDual.taylorCompareAdd`. -/
theorem taylorCompareAdd_apply (m : M) :
    taylorCompareAdd p D hfamM hfin hadd hN ρ incl xi m =
      completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN m := rfl

include hxi hfamD hleib htay in
/-- **The comparison is `D`-linear.** -/
theorem taylorCompareAdd_smul (a : (D : Type u)) (m : M) :
    taylorCompareAdd p D hfamM hfin hadd hN ρ incl xi (a • m) =
      a • taylorCompareAdd p D hfamM hfin hadd hN ρ incl xi m :=
  taylorSum_smul p D incl.toAddMonoidHom xi hfin hN (RingHom.id _) ρ
    (fun c m ↦ incl.map_smulₛₗ c m) hfamM hfamD hadd hleib hxi htay a m

/-- **The comparison** as a `D`-linear map. -/
def taylorCompare : M →ₗ[(D : Type u)] N where
  toFun := taylorCompareAdd p D hfamM hfin hadd hN ρ incl xi
  map_add' := map_add _
  map_smul' := taylorCompareAdd_smul p D hfamM hfin hadd hN ρ incl xi hxi hfamD hleib htay

/-- **The Taylor sum in the reverse direction**, `m ↦ ∑_K (-ξ)^{[K]} • θ_K m`, on `M` itself. -/
def taylorBack : M →+ M :=
  AddMonoidHom.mk' (completeTaylorSum p D thetaPow (AddMonoidHom.id M) (-xi) hfin hM)
    (taylorSum_add p D (AddMonoidHom.id M) (-xi) hfin hM hfamM hadd)

include hxi hfamD hleib htay' in
/-- **The reverse Taylor sum is `ρ`-semilinear.** -/
theorem taylorBack_smul (a : (D : Type u)) (m : M) :
    taylorBack p D hM hfamM hfin hadd xi (a • m) =
      ρ a • taylorBack p D hM hfamM hfin hadd xi m :=
  taylorSum_smul p D (AddMonoidHom.id M) (-xi) hfin hM ρ (RingHom.id _)
    (fun _ _ ↦ rfl) hfamM hfamD hadd hleib (neg_mem_ideal_family hxi) htay' a m

variable (huniv : ∀ φ : M →+ M, (∀ (c : (D : Type u)) (m : M), φ (c • m) = ρ c • φ m) →
    ∃ ψ : N →ₗ[(D : Type u)] M, ∀ m, ψ (incl m) = φ m)
  (hext : ∀ f g : N →ₗ[(D : Type u)] N, (∀ m, f (incl m) = g (incl m)) → f = g)

/-- **The inverse comparison** `N → M`. -/
def taylorCompareInv : N →ₗ[(D : Type u)] M :=
  (huniv (taylorBack p D hM hfamM hfin hadd xi)
    (taylorBack_smul p D hM hfamM hfin hadd ρ xi hxi hfamD hleib htay')).choose

/-- The inverse comparison extends the reverse Taylor sum. -/
theorem taylorCompareInv_incl (m : M) :
    taylorCompareInv p D hM hfamM hfin hadd ρ incl xi hxi hfamD hleib htay' huniv (incl m) =
      taylorBack p D hM hfamM hfin hadd xi m :=
  (huniv (taylorBack p D hM hfamM hfin hadd xi)
    (taylorBack_smul p D hM hfamM hfin hadd ρ xi hxi hfamD hleib htay')).choose_spec m

/-- **The comparison as a `D`-linear equivalence** `M ≃ N`. -/
def taylorCompareEquiv : M ≃ₗ[(D : Type u)] N :=
  LinearEquiv.ofLinearMap
    (taylorCompare p D hfamM hfin hadd hN ρ incl xi hxi hfamD hleib htay)
    (taylorCompareInv p D hM hfamM hfin hadd ρ incl xi hxi hfamD hleib htay' huniv)
    (by
      have h := hext ((taylorCompare p D hfamM hfin hadd hN ρ incl xi hxi hfamD hleib
          htay).comp (taylorCompareInv p D hM hfamM hfin hadd ρ incl xi hxi hfamD hleib htay'
            huniv)) LinearMap.id fun m ↦ by
        rw [LinearMap.comp_apply, taylorCompareInv_incl]
        exact map_completeTaylorSum_eq_of_comp p D hfin hM hN hfamM hadd
          (AddMonoidHom.id M) incl.toAddMonoidHom (neg_mem_ideal_family hxi) hxi
          (neg_add_cancel xi) _ (fun _ ↦ rfl) m
      exact h)
    (LinearMap.ext fun m ↦ map_completeTaylorSum_eq_of_comp p D hfin hN hM hfamM hadd
      incl.toAddMonoidHom (AddMonoidHom.id M) hxi (neg_mem_ideal_family hxi) (add_neg_cancel xi) _
      (taylorCompareInv_incl p D hM hfamM hfin hadd ρ incl xi hxi hfamD hleib htay' huniv) m)

/-- The equivalence `Crystalline.CoordinateDual.taylorCompareEquiv` is the comparison. -/
@[simp] theorem taylorCompareEquiv_apply (m : M) :
    taylorCompareEquiv p D hM hfamM hfin hadd hN ρ incl xi hxi hfamD hleib htay htay' huniv hext
        m = completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN m := rfl

end TaylorComparison

section Horizontality

variable (p : ℕ) (D : DividedPowerRing.{u}) {ι : Type u} [DecidableEq ι]
  {Omega : Type u} [AddCommGroup Omega] [Module (D : Type u) Omega] {d : D.carrier → Omega}
  {cf : ι → (Omega →ₗ[(D : Type u)] (D : Type u))} (x : ι → (D : Type u))
  (hc : IsCoordinateDual (fun i ↦ d (x i)) cf)
  {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
  {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}
  (hfamM : IsThetaMonomialFamily M theta thetaPow)
  (hfin : ∀ (n : ℕ) (m : M),
    {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite)
  (hadd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
  (hsupp : ∀ (y : M) (n : ℕ), {i : ι | theta i y ∉ pPowSmul p (D : Type u) M n}.Finite)
  {N : Type u} [AddCommGroup N] [Module (D : Type u) N] (hN : IsPAdicallyComplete p D N)
  {nablaN : CompletedConnection p (D : Type u) Omega d N} {thetaN : ι → (N → N)}
  (hθN : IsCoordinateExpansion p (D : Type u) Omega (fun i ↦ d (x i)) nablaN thetaN)
  (ρ : (D : Type u) →+* (D : Type u)) (incl : M →ₛₗ[ρ] N)
  (xi : ι → (D : Type u))
  (hdxi : ∀ i, d (x i) = d (ρ (x i)) + d (xi i))
  (hdmono : ∀ K : ι →₀ ℕ, d (taylorMonomial D xi K) =
    ∑ i ∈ K.support, taylorMonomial D xi (K - Finsupp.single i 1) • d (xi i))
  (hF1 : ∀ (k : ι) (y : M) (n : ℕ) (T : Finset ι),
    (∀ i ∉ T, theta i y ∈ pPowSmul p (D : Type u) M n) →
      thetaN k (incl y) - ∑ i ∈ T, cf k (d (ρ (x i))) • incl (theta i y) ∈
        pPowSmul p (D : Type u) N n)

include hc hsupp hθN hdxi hdmono hF1 in
/-- **The comparison commutes with the coordinate operators**: `θ^N_j (Φ m) = Φ (θ_j m)`, the
compatibility with connections whose proof [Stacks, Lemma 60.17.5, Tag 07L5] omits, here for an
arbitrary family of coordinates: every infinite sum is truncated modulo `p^n` to a finset of
coordinates chosen for `m` and `n`. -/
theorem coord_taylorRoundTrip (j : ι) (m : M) :
    thetaN j (taylorCompareAdd p D hfamM hfin hadd hN ρ incl xi m) =
      taylorCompareAdd p D hfamM hfin hadd hN ρ incl xi (theta j m) := by
  classical
  set e : ι → ι →₀ ℕ := fun i ↦ Finsupp.single i 1 with he
  have hNH := hN.toIsHausdorff
  have hθNadd : ∀ (k : ι) (y z : N), thetaN k (y + z) = thetaN k y + thetaN k z :=
    coordinate_map_add hθN hc hNH
  have hθNleib : ∀ (k : ι) (f : (D : Type u)) (z : N),
      thetaN k (f • z) = f • thetaN k z + cf k (d f) • z :=
    coordinate_leibniz hθN hc hNH
  have hθNp : ∀ (n : ℕ) (k : ι) (z : N), z ∈ pPowSmul p (D : Type u) N n →
      thetaN k z ∈ pPowSmul p (D : Type u) N n :=
    fun n k _ hz ↦ theta_mem_pPowSmul_of_mem_of_isCoordinateDual p hθN hc n k hz
  set θNj : N →+ N := AddMonoidHom.mk' (thetaN j) (hθNadd j) with hθNj
  have hrepr_mono : ∀ K : ι →₀ ℕ, cf j (d (taylorMonomial D xi K)) =
      ∑ i ∈ K.support, taylorMonomial D xi (K - e i) * cf j (d (xi i)) := by
    intro K
    rw [hdmono K, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul]
  have hrepr_xi : ∀ i, cf j (d (xi i)) = (if i = j then 1 else 0) - cf j (d (ρ (x i))) := by
    intro i
    have h := congrArg (cf j) (hdxi i)
    rw [map_add] at h
    have hd : cf j (d (x i)) = if i = j then 1 else 0 := by
      split_ifs with hij
      · rw [hij]; exact hc.self j
      · exact hc.of_ne hij
    rw [hd] at h
    rw [h]
    ring
  have hshift : ∀ (K : ι →₀ ℕ) (i : ι) (y : M), theta i (thetaPow K y) = thetaPow (K + e i) y := by
    intro K i y
    rw [hfamM.2 i K]; rfl
  have hshift' : ∀ (K : ι →₀ ℕ) (y : M), thetaPow K (theta j y) = thetaPow (K + e j) y := by
    intro K y
    rw [show K + e j = e j + K from add_comm _ _, hfamM.add (e j) K, hfamM.single,
      Function.iterate_one]; rfl
  refine eq_of_forall_sub_mem_pPowSmul p D hN fun n ↦ ?_
  set R := taylorBox p D hfin n m with hR
  have hRgood : ∀ K ∉ R, thetaPow K m ∈ pPowSmul p (D : Type u) M n :=
    fun K hK ↦ mem_pPowSmul_of_notMem_taylorBox p D hfin hK
  have hdown : ∀ K ∈ R, ∀ L ≤ K, L ∈ R := fun K hK L hLK ↦ mem_taylorBox_of_le p D hfin hK hLK
  set T : Finset ι := insert j (R.biUnion fun K ↦ (hsupp (thetaPow K m) n).toFinset ∪ K.support)
    with hT
  have hjT : j ∈ T := Finset.mem_insert_self j _
  have hTθ : ∀ K ∈ R, ∀ i ∉ T, theta i (thetaPow K m) ∈ pPowSmul p (D : Type u) M n := by
    intro K hK i hi
    by_contra hcon
    exact hi (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨K, hK,
      Finset.mem_union_left _ ((hsupp (thetaPow K m) n).mem_toFinset.mpr hcon)⟩))
  have hTsupp : ∀ K ∈ R, K.support ⊆ T := fun K hK i hi ↦
    Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨K, hK, Finset.mem_union_right _ hi⟩)
  set Rf : ι → Finset (ι →₀ ℕ) := fun i ↦ R.filter (fun K ↦ K + e i ∈ R) with hRf
  have hRjgood : ∀ K ∉ Rf j, thetaPow K (theta j m) ∈ pPowSmul p (D : Type u) M n := by
    intro K hK
    rw [hshift']
    refine hRgood _ fun h ↦ hK (Finset.mem_filter.mpr ⟨hdown _ h _ le_self_add, h⟩)
  have E1 := taylorSum_sub_sum_mem p D thetaPow incl.toAddMonoidHom xi hfin hN m n R hRgood
  have E2 := taylorSum_sub_sum_mem p D thetaPow incl.toAddMonoidHom xi hfin hN (theta j m) n (Rf j)
    hRjgood
  set A : N := ∑ K ∈ R, ∑ i ∈ T, (taylorMonomial D xi K * cf j (d (ρ (x i)))) • incl (thetaPow (K
      + e i) m)
    with hA
  set A' : N := ∑ i ∈ T, ∑ K ∈ Rf i, (taylorMonomial D xi K * cf j (d (ρ (x i)))) • incl (thetaPow
      (K + e i) m)
    with hA'
  set B : N := ∑ i ∈ T, ∑ K ∈ Rf i,
    (taylorMonomial D xi K * cf j (d (xi i))) • incl (thetaPow (K + e i) m) with hB
  have hcoordSum : θNj (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K) - (A + B) ∈
      pPowSmul p (D : Type u) N n := by
    have h1 : θNj (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K) =
        ∑ K ∈ R, (taylorMonomial D xi K • thetaN j (incl (thetaPow K m)) +
          cf j (d (taylorMonomial D xi K)) • incl (thetaPow K m)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun K _ ↦ ?_
      simp only [hθNj, AddMonoidHom.mk'_apply, taylorSumTerm]
      exact hθNleib j _ _
    have hBeq : ∑ K ∈ R, cf j (d (taylorMonomial D xi K)) • incl (thetaPow K m) = B := by
      have hre := sum_support_sub_single_eq_of_subset R hdown T hTsupp (fun K i ↦
        (taylorMonomial D xi K * cf j (d (xi i))) • incl (thetaPow (K + e i) m))
      rw [hB, ← hre]
      refine Finset.sum_congr rfl fun K _ ↦ ?_
      rw [hrepr_mono, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hKi : e i ≤ K := Finsupp.single_le_iff.mpr
        (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
      rw [tsub_add_cancel_of_le hKi]
    have hAmem : ∑ K ∈ R, taylorMonomial D xi K • thetaN j (incl (thetaPow K m)) - A ∈
        pPowSmul p (D : Type u) N n := by
      rw [hA, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun K hK ↦ ?_
      have h := Submodule.smul_mem _ (taylorMonomial D xi K)
        (hF1 j (thetaPow K m) n T (hTθ K hK))
      convert h using 1
      rw [smul_sub, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul, hshift]
    rw [h1, Finset.sum_add_distrib, hBeq]
    convert hAmem using 1
    abel
  have hAA' : A - A' ∈ pPowSmul p (D : Type u) N n := by
    rw [hA, hA', Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [← Finset.sum_filter_add_sum_filter_not R (fun K ↦ K + e i ∈ R), add_sub_cancel_left]
    refine Submodule.sum_mem _ fun K hK ↦ ?_
    exact Submodule.smul_mem _ _ (map_mem_pPowSmul_of_addMonoidHom p incl.toAddMonoidHom
      (hRgood _ (Finset.mem_filter.mp hK).2))
  have hA'B : A' + B = ∑ K ∈ Rf j, taylorSumTerm D thetaPow incl.toAddMonoidHom xi (theta j m) K
      := by
    rw [hA', hB, ← Finset.sum_add_distrib]
    rw [Finset.sum_eq_single_of_mem j hjT]
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
  have hθNmem : thetaN j (completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN m) -
      θNj (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K) ∈
        pPowSmul p (D : Type u) N n := by
    have hsub := map_sub θNj (completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN m)
      (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K)
    simp only [hθNj, AddMonoidHom.mk'_apply] at hsub ⊢
    rw [← hsub]
    exact hθNp n j _ E1
  have : thetaN j (taylorCompareAdd p D hfamM hfin hadd hN ρ incl xi m) -
      taylorCompareAdd p D hfamM hfin hadd hN ρ incl xi (theta j m) =
      (thetaN j (completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN m) -
        θNj (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K)) +
      (θNj (∑ K ∈ R, taylorSumTerm D thetaPow incl.toAddMonoidHom xi m K) - (A + B)) +
      (A - A') -
      (completeTaylorSum p D thetaPow incl.toAddMonoidHom xi hfin hN (theta j m) -
        ∑ K ∈ Rf j, taylorSumTerm D thetaPow incl.toAddMonoidHom xi (theta j m) K) := by
    rw [taylorCompareAdd_apply, taylorCompareAdd_apply, ← hA'B]
    abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ hθNmem hcoordSum) hAA') E2

end Horizontality

/-! ### The functor `G` -/

section Back

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateDualData p D)
  (R : CoordinateDualRetractData p D C)

/-- **The functor `G` on objects**: the base change of a pair over `D'` along `b`. -/
def retractBack (P : CoordinateDualRetractPair C R) : Pair.{u, u, u, u} p D C.forms C.dx C.diff
    where
  carrier := CompletedConnection.baseChangeCarrier p R.ring D P.carrier
  isPAdicallyComplete := CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _
  nabla := CompletedConnection.baseChange p R.ring D P.carrier R.forms C.forms C.diff (R.psiB 1)
    P.nabla C.diff_add C.diff_mul R.psiB_diff
  hasCoordinateOperators := C.exists_isCoordinateExpansion
    (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _) _
  isIntegrable := by
    intro theta hco i j
    have hN := CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D P.carrier
    exact (C.isCurvatureZero_iff _ hN hco).mp (CompletedDeRham.isCurvatureZero_baseChange p
      R.ring D P.carrier R.Om C.Om R.psiB R.wedge C.wedge R.deRham C.deRham C.diff P.nabla
      C.diff_add C.diff_mul R.psiB_diff R.isGradedLeibniz C.isGradedLeibniz R.psiB_wedge
      R.psiB_deRham C.wedge_anti C.deRham_diff P.isIntegrable) i j
  isTopologicallyQuasiNilpotent := P.isTopologicallyQuasiNilpotent_back

/-- **The functor `G`**: base change of pairs along `b : D' → D`. -/
def retractBackFunctor :
    CoordinateDualRetractPair C R ⥤ Pair.{u, u, u, u} p D C.forms C.dx C.diff where
  obj P := retractBack C R P
  map {P Q} f :=
    { toLinearMap := CompletedConnection.baseChangeModuleMap p R.ring D P.carrier Q.carrier
        f.toLinearMap
      horizontal := fun x ↦ by
        have h := CompletedConnection.baseChange_baseChangeModuleMap p R.ring D P.carrier
          Q.carrier R.forms C.forms C.diff (R.psiB 1) P.nabla Q.nabla C.diff_add C.diff_mul
          R.psiB_diff f.toLinearMap
          (fun m ↦ by rw [f.horizontal m, CompletedConnection.valuesMap_eq]) x
        rwa [CompletedConnection.valuesMap_eq] at h }
  map_id P := PairHom.ext (CompletedConnection.baseChangeModuleMap_id p R.ring D P.carrier)
  map_comp f g := PairHom.ext (LinearMap.ext fun x ↦
    CompletedConnection.baseChangeModuleMap_comp p R.ring D _ _ _ f.toLinearMap g.toLinearMap x)

end Back

/-! ### The round trip -/

section RoundTrip

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateDualData p D)
  (R : CoordinateDualRetractData p D C)

/-- The coordinate differences `ξ_i = x_i - ρ(x_i)`. -/
abbrev xi (i : C.ι) : (D : Type u) := C.coord i - retractRho D R.ring (C.coord i)

/-- The coordinate differences `ξ_i` lie in the divided power ideal. -/
theorem xi_mem (i : C.ι) : xi C R i ∈ D.ideal := by
  simpa [xi] using D.ideal.neg_mem (R.rho_sub_mem (C.coord i))

/-- The twice base-changed connection of `G(F(M, ∇))`, on the module
`Crystalline.retractRoundTripCarrier` of the retract. -/
abbrev roundTripNabla {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
    (nabla : CompletedConnection p D C.forms C.diff M) :
    CompletedConnection p D C.forms C.diff (retractRoundTripCarrier p D R.ring M) :=
  retractRoundTripNabla p D R.ring (R.psiA 1) (R.psiB 1) C.diff_add C.diff_mul
    R.diff_add R.diff_mul R.psiA_diff R.psiB_diff nabla

/-- The map `M ⊗̂_D Ω → G(F(M)) ⊗̂_D Ω` on the values of the connections, `ψ_b ∘ ψ_a` with
`m ↦ 1 ⊗ (1 ⊗ m)`. -/
def roundTripValues (M : Type u) [AddCommGroup M] [Module (D : Type u) M] :
    CompletedTensor p (D : Type u) C.forms M →+
      CompletedTensor p (D : Type u) C.forms (retractRoundTripCarrier p D R.ring M) :=
  (CompletedConnection.baseChangeValues p R.ring D
      (CompletedConnection.baseChangeCarrier p D R.ring M) R.forms C.forms
      (R.psiB 1)).toAddMonoidHom.comp
    (CompletedConnection.baseChangeValues p D R.ring M C.forms R.forms (R.psiA 1)).toAddMonoidHom

/-- The connection of `G(F(M, ∇))` on `1 ⊗ (1 ⊗ m)` is the image of `∇ m`. -/
theorem roundTripNabla_incl {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
    (nabla : CompletedConnection p D C.forms C.diff M) (m : M) :
    roundTripNabla C R nabla (retractRoundTripIncl p D R.ring M m) = roundTripValues C R M (nabla
        m) := by
  rw [retractRoundTripIncl_apply, CompletedConnection.baseChange_inclusion,
    CompletedConnection.baseChange_inclusion]
  rfl

/-- The values map on a pure tensor `m ⊗ d x_i`. -/
theorem roundTripValues_tmul_dx (M : Type u) [AddCommGroup M] [Module (D : Type u) M] (m : M)
    (i : C.ι) :
    roundTripValues C R M (toCompletedTensor p (D : Type u) C.forms M (m ⊗ₜ[(D : Type u)] C.dx i)) =
      toCompletedTensor p (D : Type u) C.forms (retractRoundTripCarrier p D R.ring M)
        (retractRoundTripIncl p D R.ring M m ⊗ₜ[(D : Type u)] C.diff (retractRho D R.ring (C.coord
            i))) := by
  simp only [roundTripValues, AddMonoidHom.coe_comp, Function.comp_apply,
    LinearMap.toAddMonoidHom_coe, CompletedConnection.baseChangeValues_of_tmul]
  rw [R.psiA_diff, R.psiB_diff]
  try rfl

/-- **The first-order coordinates of `G(F(M))` on `1 ⊗ (1 ⊗ y)`, modulo `pⁿ`**:
`θ^N_k(ι y) ≡ ∑_i c_k(d ρ(x_i)) ι(θ_i y)` over any finset outside which `θ_i y ∈ pⁿ M`. -/
theorem roundTrip_coord_incl (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff)
    {thetaN : C.ι → (retractRoundTripCarrier p D R.ring P.carrier → retractRoundTripCarrier p D
        R.ring P.carrier)}
    (hθN : IsCoordinateExpansion p (D : Type u) C.forms C.dx (roundTripNabla C R P.nabla) thetaN)
    (k : C.ι) (y : P.carrier) (n : ℕ) (T : Finset C.ι)
    (hT : ∀ i ∉ T, pairTheta C P i y ∈ pPowSmul p (D : Type u) P.carrier n) :
    thetaN k (retractRoundTripIncl p D R.ring P.carrier y) - ∑ i ∈ T, C.coordFun k (C.diff
        (retractRho D R.ring (C.coord
        i))) •
        retractRoundTripIncl p D R.ring P.carrier (pairTheta C P i y) ∈
      pPowSmul p (D : Type u) (retractRoundTripCarrier p D R.ring P.carrier) n := by
  have htr := sub_sum_mem_of_isCoordinateExpansion p (isCoordinateExpansion_pairTheta C P) y n T hT
  have hΨ := PAdicCompletion.map_mem_pow_smul_top p (D : Type u) (D : Type u)
    (roundTripValues C R P.carrier) n htr
  rw [map_sub, ← roundTripNabla_incl, map_sum] at hΨ
  simp only [roundTripValues_tmul_dx] at hΨ
  rw [← map_sum] at hΨ
  have h1 := map_mem_pow_smul_top_of_mem _ (completedTensorFunctionalLevel p (D : Type u) C.forms
    (retractRoundTripCarrier p D R.ring P.carrier)
    (dualTensorCoordinate (retractRoundTripCarrier p D R.ring P.carrier) (C.coordFun k)) n) n hΨ
  rw [show (pAdicIdeal (A := (D : Type u)) p) ^ n • (⊤ : Submodule (D : Type u)
      (retractRoundTripCarrier p D R.ring P.carrier ⧸ pLevel p (D : Type u)
          (retractRoundTripCarrier p D R.ring P.carrier) n))
      = ⊥ from pLevel_quotient_eq_bot p (D : Type u) (retractRoundTripCarrier p D R.ring
          P.carrier) n,
    Submodule.mem_bot, map_sub,
    completedTensorFunctionalLevel_eq_of_hasSum p (D : Type u) C.forms
      (retractRoundTripCarrier p D R.ring P.carrier) hθN C.isCoordinateDual k _ n,
    completedTensorFunctionalLevel_of, ← Submodule.Quotient.mk_sub,
    Submodule.Quotient.mk_eq_zero, map_sum] at h1
  simp only [dualTensorCoordinate_tmul] at h1
  exact h1

/-- **The comparison `c_{id_D, b ∘ a} : M ≃ G(F(M))`** of a pair over `D`, with its
horizontality and its formula. -/
theorem Pair.exists_roundTripEquiv (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    ∃ e : P.carrier ≃ₗ[(D : Type u)] retractRoundTripCarrier p D R.ring P.carrier,
      (∀ m, roundTripNabla C R P.nabla (e m) = AdicCompletion.map (pAdicIdeal (A := (D : Type u)) p)
            (TensorProduct.map e.toLinearMap (LinearMap.id (R := (D : Type u)) (M := C.forms)))
            (P.nabla m)) ∧
        ∀ m, e m = completeTaylorSum p D (pairThetaPow C P)
          (retractRoundTripIncl p D R.ring P.carrier).toAddMonoidHom (xi C R) (finite_pairThetaPow
              C P)
          (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _) m := by
  have hM := P.isPAdicallyComplete
  have hN : IsPAdicallyComplete p D (retractRoundTripCarrier p D R.ring P.carrier) :=
    CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _
  obtain ⟨thetaN, hθN⟩ := C.exists_isCoordinateExpansion hN (roundTripNabla C R P.nabla)
  refine ⟨taylorCompareEquiv p D hM (isThetaMonomialFamily_pairThetaPow C P)
    (finite_pairThetaPow C P) (pairTheta_add C P) hN (retractRho D R.ring) (retractRoundTripIncl p
        D R.ring P.carrier)
    (xi C R) (xi_mem C R) C.isThetaMonomialFamily (pairTheta_smul C P) R.taylor R.taylor'
    (retractRoundTrip_exists_lift p D R.ring P.carrier hM)
    (retractRoundTrip_ext p D R.ring P.carrier hN), ?_,
    fun m ↦ rfl⟩
  intro m
  refine horizontal_of_isCoordinateExpansion (isCoordinateExpansion_pairTheta C P) hθN _
    (fun j y ↦ ?_) m
  exact (coord_taylorRoundTrip p D C.coord C.isCoordinateDual
    (isThetaMonomialFamily_pairThetaPow C P) (finite_pairThetaPow C P) (pairTheta_add C P)
    (fun y n ↦ finite_notMem_pPowSmul_of_isCoordinateDual (isCoordinateExpansion_pairTheta C P)
      C.isCoordinateDual y n) hN hθN (retractRho D R.ring) (retractRoundTripIncl p D R.ring
          P.carrier) (xi C R)
    (fun i ↦ by rw [← C.diff_add, add_sub_cancel]) (differential_taylorMonomial C.diff C.diff_add
        C.diff_mul C.diff_dpow (xi_mem C R))
    (fun k y n T hT ↦ roundTrip_coord_incl C R P hθN k y n T hT) j y).symm

/-- **The comparison `c_{id_D, b ∘ a} : M ≃ G(F(M))`** of a pair over `D`. -/
def Pair.roundTripEquiv (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    P.carrier ≃ₗ[(D : Type u)] retractRoundTripCarrier p D R.ring P.carrier :=
  (Pair.exists_roundTripEquiv C R P).choose

/-- **The comparison is the Taylor sum** `m ↦ ∑_K ξ^{[K]} ⊗ θ_K(m)`. -/
theorem Pair.roundTripEquiv_apply (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff)
    (m : P.carrier) :
    Pair.roundTripEquiv C R P m = completeTaylorSum p D (pairThetaPow C P)
      (retractRoundTripIncl p D R.ring P.carrier).toAddMonoidHom (xi C R) (finite_pairThetaPow C P)
      (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _) m :=
  (Pair.exists_roundTripEquiv C R P).choose_spec.2 m

end RoundTrip

/-! ### The functor `F` and the equivalence -/

section Equivalence

variable {p : ℕ} {D : DividedPowerRing.{u}} (C : CompletedCoordinateDualData p D)
  (R : CoordinateDualRetractData p D C)

/-- **The functor `F` on objects**: the base change of a pair over `D` along `a`.  Its curvature
vanishes because that of the pair does, the pair's coordinate operators commuting; its base
change back along `b` is topologically quasi-nilpotent because it is isomorphic to the pair itself
by the horizontal comparison `Crystalline.CoordinateDual.Pair.roundTripEquiv`. -/
def retractForward (P : Pair.{u, u, u, u} p D C.forms C.dx C.diff) :
    CoordinateDualRetractPair C R where
  carrier := CompletedConnection.baseChangeCarrier p D R.ring P.carrier
  isPAdicallyComplete := CompletedConnection.isPAdicallyComplete_baseChangeCarrier p D R.ring _
  nabla := CompletedConnection.baseChange p D R.ring P.carrier C.forms R.forms R.diff (R.psiA 1)
    P.nabla R.diff_add R.diff_mul R.psiA_diff
  isIntegrable := CompletedDeRham.isCurvatureZero_baseChange p D R.ring P.carrier C.Om
    R.Om (R.psiA) C.wedge R.wedge C.deRham R.deRham R.diff P.nabla R.diff_add R.diff_mul
    R.psiA_diff C.isGradedLeibniz R.isGradedLeibniz R.psiA_wedge R.psiA_deRham R.wedge_anti
    R.deRham_diff ((C.isCurvatureZero_iff P.nabla P.isPAdicallyComplete
      (isCoordinateExpansion_pairTheta C P)).mpr (pairTheta_comm C P))
  isTopologicallyQuasiNilpotent_back := isTopologicallyQuasiNilpotent_of_horizontalEquiv p P
    C.isCoordinateDual (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _)
    (roundTripNabla C R P.nabla) (Pair.roundTripEquiv C R P) (Pair.exists_roundTripEquiv C R
        P).choose_spec.1

/-- **The functor `F`**: base change of pairs along `a : D → D'`. -/
def retractForwardFunctor :
    Pair.{u, u, u, u} p D C.forms C.dx C.diff ⥤ CoordinateDualRetractPair C R where
  obj P := retractForward C R P
  map {P Q} f :=
    { toLinearMap := CompletedConnection.baseChangeModuleMap p D R.ring P.carrier Q.carrier
        f.toLinearMap
      horizontal := fun x ↦ by
        have h := CompletedConnection.baseChange_baseChangeModuleMap p D R.ring P.carrier
          Q.carrier C.forms R.forms R.diff (R.psiA 1) P.nabla Q.nabla R.diff_add R.diff_mul
          R.psiA_diff f.toLinearMap
          (fun m ↦ by rw [f.horizontal m, CompletedConnection.valuesMap_eq]) x
        rwa [CompletedConnection.valuesMap_eq] at h }
  map_id P := CoordinateDualRetractPairHom.ext
    (CompletedConnection.baseChangeModuleMap_id p D R.ring P.carrier)
  map_comp f g := CoordinateDualRetractPairHom.ext (LinearMap.ext fun x ↦
    CompletedConnection.baseChangeModuleMap_comp p D R.ring _ _ _ f.toLinearMap g.toLinearMap x)

/-- **`G ∘ F ≅ 𝟭`**: the comparison `c_{id_D, b ∘ a}` of every pair over `D`. -/
def retractUnitIso :
    𝟭 (Pair.{u, u, u, u} p D C.forms C.dx C.diff) ≅
      retractForwardFunctor C R ⋙ retractBackFunctor C R :=
  NatIso.ofComponents
    (fun P ↦ Crystalline.Pair.isoOfHorizontalEquiv p (Q := (retractForwardFunctor C R ⋙
      retractBackFunctor C R).obj P) (Pair.roundTripEquiv C R P)
      (Pair.exists_roundTripEquiv C R P).choose_spec.1)
    fun {P Q} f ↦ PairHom.ext (LinearMap.ext fun m ↦ by
      have key :
          Pair.roundTripEquiv C R Q (f.toLinearMap m) =
            CompletedConnection.baseChangeModuleMap p R.ring D _ _
              (CompletedConnection.baseChangeModuleMap p D R.ring P.carrier Q.carrier f.toLinearMap)
              (Pair.roundTripEquiv C R P m) := by
          have hcomm : ∀ i y, pairTheta C Q i (f.toLinearMap y) = f.toLinearMap (pairTheta C P i
              y) :=
            fun i y ↦ coordinate_naturality (isCoordinateExpansion_pairTheta C P)
              (isCoordinateExpansion_pairTheta C Q) C.isCoordinateDual
              Q.isPAdicallyComplete.toIsHausdorff f.toLinearMap f.horizontal i y
          have hK := IsThetaMonomialFamily.map_comm (isThetaMonomialFamily_pairThetaPow C P)
            (isThetaMonomialFamily_pairThetaPow C Q) f.toLinearMap hcomm
          rw [Pair.roundTripEquiv_apply, Pair.roundTripEquiv_apply]
          refine (taylorSum_precomp p D (finite_pairThetaPow C P) (finite_pairThetaPow C Q)
            (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _) _ _
            f.toLinearMap.toAddMonoidHom hK m).trans ?_
          refine Eq.trans ?_ (map_taylorSum p D (finite_pairThetaPow C P)
            (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _)
            (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring D _) _ _ _ m).symm
          congr 1
      exact key)

/-- **The collapse `F(G(M')) → M'` is natural in `M'`.** -/
theorem retractComparison_naturality {P Q : CoordinateDualRetractPair C R} (f : P ⟶ Q)
    (z : CompletedConnection.baseChangeCarrier p D R.ring
      (CompletedConnection.baseChangeCarrier p R.ring D P.carrier)) :
    CompletedConnection.retractComparison p R.ring D Q.carrier Q.isPAdicallyComplete
        (CompletedConnection.baseChangeModuleMap p D R.ring _ _
          (CompletedConnection.baseChangeModuleMap p R.ring D P.carrier Q.carrier f.toLinearMap)
          z) =
      f.toLinearMap (CompletedConnection.retractComparison p R.ring D P.carrier
        P.isPAdicallyComplete z) := by
  have hQ := Q.isPAdicallyComplete
  exact DFunLike.congr_fun (baseChangeCarrier_baseChangeCarrier_ext p R.ring D R.ring P.carrier
    hQ.toIsHausdorff
    ((CompletedConnection.retractComparison p R.ring D Q.carrier Q.isPAdicallyComplete) ∘ₗ
      (CompletedConnection.baseChangeModuleMap p D R.ring _ _
        (CompletedConnection.baseChangeModuleMap p R.ring D P.carrier Q.carrier f.toLinearMap)))
    (f.toLinearMap ∘ₗ (CompletedConnection.retractComparison p R.ring D P.carrier
      P.isPAdicallyComplete))
    (fun m ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [CompletedConnection.baseChangeModuleMap_inclusion,
        CompletedConnection.baseChangeModuleMap_inclusion,
        CompletedConnection.retractComparison_inclusion,
        CompletedConnection.retractComparison_inclusion])) z

/-- **`F ∘ G ≅ 𝟭`**: the collapse of the round trip along `a ∘ b = id_{D'}`, "Since
`a ∘ b = id_{D'}` we see that `F ∘ G` is the identity functor". -/
def retractCounitIso :
    retractBackFunctor C R ⋙ retractForwardFunctor C R ≅ 𝟭 (CoordinateDualRetractPair C R) :=
  NatIso.ofComponents
    (fun P ↦ CoordinateDualRetractPair.isoOfHorizontalEquiv C R (P := (retractBackFunctor C R ⋙
      retractForwardFunctor C R).obj P)
      (CompletedConnection.retractComparisonEquiv p R.ring D P.carrier P.isPAdicallyComplete)
      (fun x ↦ by
        rw [← CompletedConnection.valuesMap_eq]
        exact CompletedConnection.baseChange_retractComparison p R.ring D P.carrier R.forms C.forms
          C.diff (R.psiB 1) (R.psiA 1) P.nabla P.isPAdicallyComplete R.diff_add R.diff_mul
          C.diff_add C.diff_mul R.psiB_diff R.psiA_diff R.psiA_psiB x))
    fun {P Q} f ↦ CoordinateDualRetractPairHom.ext (LinearMap.ext fun z ↦
      retractComparison_naturality C R f z)

/-- **The equivalence of categories of [Stacks, Lemma 60.17.5, Tag 07L5], for any family of
coordinates**, between the pairs over `D` satisfying (07JB)–(07JE) and the pairs over `D'`
satisfying them, induced by the base change functors `F` along `a` and `G` along `b`. -/
def retractPairEquivalence :
    Pair.{u, u, u, u} p D C.forms C.dx C.diff ≌ CoordinateDualRetractPair C R :=
  CategoryTheory.Equivalence.mk (retractForwardFunctor C R) (retractBackFunctor C R)
    (retractUnitIso C R) (retractCounitIso C R)

end Equivalence

end CoordinateDual

end Crystalline

end
