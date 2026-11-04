module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteEtaleCoverStratificationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening

/-!
# The filtration of a finite order thickening by first order thickenings

Let `X ⊂ X'` be a thickening of algebraic spaces over a scheme `S`, cut out by the sheaf of ideals
`𝓘 ⊂ 𝒪_{X'}`.  The text of [Stacks Project, Section 05ZJ] observes that if `X'` is an `n`th order
thickening of `X` then the filtration
`0 ⊂ 𝓘^n ⊂ 𝓘^{n-1} ⊂ … ⊂ 𝓘 ⊂ 𝒪_{X'}`
exhibits `X'` as filtered by closed subspaces
`X = X_0 ⊂ X_1 ⊂ … ⊂ X_{n-1} ⊂ X_n = X'`
such that each pair `X_k ⊂ X_{k+1}` is a first order thickening.  (The source prints the last
term as `X_{n+1}`; the filtration of ideals has `n + 1` steps, so the last space is `X_n`.)

The closed subspace `X_k` is the one cut out by `𝓘^{k+1}`, the `(k+1)`-fold sum `X + X + ⋯ + X`
of the closed subspace `X` with itself, the sum being the one of [Stacks Project, Tag 083U]
(`AlgebraicGeometry.Space.sumClosedSubspaces`), which is cut out by the product of the defining
ideals.

## Main definitions

* `AlgebraicGeometry.Space.thickeningFiltration`: the closed subspaces `X_k` of `X'`, the
  `(k+1)`-fold sum of `X` with itself.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_thickeningFiltration`: `X_k` is cut out by `𝓘^{k+1}`.
* `AlgebraicGeometry.Space.le_thickeningFiltration` and
  `AlgebraicGeometry.Space.thickeningFiltration_le_succ`: `X ⊂ X_k ⊂ X_{k+1}`.
* `AlgebraicGeometry.Space.thickeningFiltration_eq_top`: if `𝓘^{n+1} = 0` then `X_n = X'`.
* `AlgebraicGeometry.Space.isFirstOrderThickening_thickeningFiltration`: each `X_k ⊂ X_{k+1}` is
  a first order thickening.
* `AlgebraicGeometry.Space.exists_firstOrderThickening_filtration`: **[Stacks Project, Section
  05ZJ]**, the filtration of an `n`th order thickening by first order thickenings.

## References

* [Stacks Project, Section 05ZJ](https://stacks.math.columbia.edu/tag/05ZJ)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- If `I * I ⊂ J` and the extension of `J` along `φ` vanishes, then so does the product of the
extension of `I` with itself. -/
private theorem map_mul_self_eq_bot_of_mul_self_le {R T : Type*} [CommSemiring R]
    [CommSemiring T] (φ : R →+* T) {I J : Ideal R} (hIJ : I * I ≤ J)
    (hJ : Ideal.map φ J = ⊥) : Ideal.map φ I * Ideal.map φ I = ⊥ := by
  rw [← Ideal.map_mul]
  exact le_bot_iff.1 (hJ ▸ Ideal.map_mono hIJ)

/-! ### A closed subspace containing a thickening is a thickening -/

/-- **A closed subspace containing a thickening is a thickening.** If `Z ⊂ W ⊂ X` with `Z` a
thickening of `X` and `W` a closed subspace, then `W` is a thickening of `X`. -/
theorem isThickening_of_le {Z W : Subfunctor X.1} (hZ : IsThickening B S hS X Z)
    (hW : IsClosedSubspace B S hS W) (h : Z ≤ W) : IsThickening B S hS X W := by
  refine ⟨hW, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := hZ.2 x
  refine ⟨pointsMap B S hS Z.toFunctor (Subfunctor.homOfLe h) z, ?_⟩
  have hcomp := congrFun (pointsMap_comp B S hS Z.toFunctor (Subfunctor.homOfLe h) W.ι) z
  rw [Subfunctor.homOfLe_ι] at hcomp
  exact hcomp.symm

/-- The defining ideal of a closed subspace equal to the whole space vanishes on every chart. -/
private theorem definingIdealAt_eq_bot_of_eq_top (W : AlgebraicSpaces B S hS)
    (C : ClosedSubspaces B S hS W.1) (hC : C.1 = ⊤) (U : SmallEtale B S hS W.1) :
    definingIdealAt B S hS W C (op U) = ⊥ := by
  obtain ⟨htop, h0⟩ := isNthOrderThickening'_top B S hS 0 W
  have h1 := h0 (op U)
  rw [zero_add, Submodule.pow_one] at h1
  rw [show C = ⟨⊤, htop⟩ from Subtype.ext hC]
  exact h1

/-! ### The filtration -/

/-- **The closed subspaces `X_k` of the filtration of a thickening.** For a closed subspace `Z`
of `X`, the closed subspace `X_k` cut out by the `(k+1)`st power of the defining ideal of `Z`:
the `(k+1)`-fold sum `Z + Z + ⋯ + Z` of Stacks 083U. -/
noncomputable def thickeningFiltration (Z : ClosedSubspaces B S hS X.1) :
    ℕ → ClosedSubspaces B S hS X.1
  | 0 => Z
  | k + 1 => sumClosedSubspaces B S hS X Z (thickeningFiltration Z k)

variable (Z : ClosedSubspaces B S hS X.1)

/-- The first closed subspace of the filtration is `Z`. -/
@[simp]
theorem thickeningFiltration_zero : thickeningFiltration B S hS X Z 0 = Z :=
  rfl

/-- The closed subspace `X_{k+1}` is the sum of `Z` and `X_k`. -/
theorem thickeningFiltration_succ (k : ℕ) :
    thickeningFiltration B S hS X Z (k + 1) =
      sumClosedSubspaces B S hS X Z (thickeningFiltration B S hS X Z k) :=
  rfl

/-- **`X_k` is cut out by `𝓘^{k+1}`.** On an affine étale chart lying over the chart on which
the sums are formed, the defining ideal of `X_k` is the `(k+1)`st power of the defining ideal of
`Z`. -/
theorem definingIdealAt_thickeningFiltration (A : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left)]
    (m : A ⟶ sumAtlasChart B S hS X) (k : ℕ) :
    definingIdealAt B S hS X (thickeningFiltration B S hS X Z k) (op A) =
      definingIdealAt B S hS X Z (op A) ^ (k + 1) := by
  induction k with
  | zero => rw [zero_add, Submodule.pow_one]; rfl
  | succ k ih =>
    rw [thickeningFiltration_succ,
      definingIdealAt_sumClosedSubspaces_of_isAffine B S hS X Z _ A m, ih]
    exact (Submodule.pow_succ' _ (Nat.succ_ne_zero k)).symm

/-- `Z = X_0` is contained in every `X_k`. -/
theorem le_thickeningFiltration (k : ℕ) : Z.1 ≤ (thickeningFiltration B S hS X Z k).1 := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_sumClosedSubspaces_left X Z _

/-- The closed subspaces `X_k` increase with `k`. -/
theorem thickeningFiltration_le_succ (k : ℕ) :
    (thickeningFiltration B S hS X Z k).1 ≤ (thickeningFiltration B S hS X Z (k + 1)).1 :=
  le_sumClosedSubspaces_right X Z _

/-- **`𝓘_{X_k} 𝓘_{X_k} ⊂ 𝓘_{X_{k+1}}` on every étale chart.** -/
theorem definingIdealAt_thickeningFiltration_sq_le (k : ℕ) (V : SmallEtale B S hS X.1) :
    definingIdealAt B S hS X (thickeningFiltration B S hS X Z k) (op V) *
        definingIdealAt B S hS X (thickeningFiltration B S hS X Z k) (op V) ≤
      definingIdealAt B S hS X (thickeningFiltration B S hS X Z (k + 1)) (op V) := by
  rw [Ideal.mul_le]
  intro a ha b hb
  exact mul_mem_definingIdealAt_sumClosedSubspaces B S hS X Z _ (op V)
    (definingIdealAt_antitone B S hS X Z _ (le_thickeningFiltration B S hS X Z k) V ha) hb

/-- **`X_n = X'` for an `n`th order thickening.** If the `(n+1)`st power of the defining ideal
of `Z` vanishes on every étale chart, then `X_n` is the whole space. -/
theorem thickeningFiltration_eq_top {n : ℕ}
    (hZ : ∀ U : SmallEtale B S hS X.1, definingIdealAt B S hS X Z (op U) ^ (n + 1) = ⊥) :
    (thickeningFiltration B S hS X Z n).1 = ⊤ := by
  have hsheaf : definingIdealSheaf B S hS X (thickeningFiltration B S hS X Z n) =
      definingIdealSheaf B S hS X ⟨⊤, isClosedSubspace_top B S hS X⟩ := by
    refine structureSubmodule_ext_of_forall_isAffine_hom B S hS X (sumAtlasChart B S hS X)
      (sumAtlasChart_isSurjective B S hS X) _ _ fun A hA m => ?_
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
    rw [definingIdealSheaf_obj, definingIdealSheaf_obj,
      definingIdealAt_thickeningFiltration B S hS X Z A m n, hZ A,
      definingIdealAt_eq_bot_of_eq_top B S hS X ⟨⊤, isClosedSubspace_top B S hS X⟩ rfl A]
  exact congrArg Subtype.val (definingIdealSheaf_injective B S hS X hsheaf)

/-- **Each `X_k ⊂ X_{k+1}` is a first order thickening.** Let `Z` be a thickening of `X`.  Read
inside the algebraic space `X_{k+1}`, the closed subspace `X_k` is a first order thickening. -/
theorem isFirstOrderThickening_thickeningFiltration (hZ : IsThickening B S hS X Z.1) (k : ℕ) :
    IsFirstOrderThickening B S hS
      ⟨(thickeningFiltration B S hS X Z (k + 1)).1.toFunctor,
        (thickeningFiltration B S hS X Z (k + 1)).2.1⟩
      ((thickeningFiltration B S hS X Z k).1.preimage
        (thickeningFiltration B S hS X Z (k + 1)).1.ι) := by
  set F := thickeningFiltration B S hS X Z
  let Y : AlgebraicSpaces B S hS := ⟨(F (k + 1)).1.toFunctor, (F (k + 1)).2.1⟩
  let ι : Y ⟶ X := ObjectProperty.homMk (F (k + 1)).1.ι
  have hk : IsThickening B S hS X (F k).1 :=
    isThickening_of_le B S hS X hZ (F k).2 (le_thickeningFiltration B S hS X Z k)
  refine ⟨isThickening_preimage B S hS (F k).1 ι hk, fun W => ?_⟩
  obtain ⟨J, W', a, d, hdU, hWaff, hVaff, hcov⟩ :=
    exists_affine_chartDiagram_ofArrows B S hS ι W
  refine definingIdealAt_pow_eq_bot_of_ofArrows B S hS Y _ 1 W W' a hcov fun i => ?_
  have hVa : IsAffine ((BigFppfOver.toScheme B S hS).obj (d i).V.1.left) := hVaff i
  have hUa : IsAffine ((BigFppfOver.toScheme B S hS).obj (d i).U.1.left) := by
    rw [hdU i]; exact hWaff i
  have hkey := definingIdealAt_preimage_eq_map B S hS ι (F k) (d i).V (d i).U (d i).g
    (d i).comm.symm
  have hnext := definingIdealAt_preimage_eq_map B S hS ι (F (k + 1)) (d i).V (d i).U (d i).g
    (d i).comm.symm
  have hpre : (F (k + 1)).1.preimage ι.hom = ⊤ := top_unique fun _ x _ => x.2
  have hbot := definingIdealAt_eq_bot_of_eq_top B S hS Y (⟨(F (k + 1)).1.preimage ι.hom,
    isClosedSubspace_preimage B S hS ι.hom (F (k + 1)).1 X.2 Y.2 (F (k + 1)).2⟩ :
      ClosedSubspaces B S hS Y.1) hpre (d i).U
  rw [hnext] at hbot
  show definingIdealAt B S hS Y (⟨(F k).1.preimage ι.hom,
      isClosedSubspace_preimage B S hS ι.hom (F k).1 X.2 Y.2 (F k).2⟩ :
        ClosedSubspaces B S hS Y.1) (op (W' i)) ^ (1 + 1) = ⊥
  have key := map_mul_self_eq_bot_of_mul_self_le
    ((BigFppfOver.toScheme B S hS).map (d i).g).appTop.hom
    (definingIdealAt_thickeningFiltration_sq_le B S hS X Z k (d i).V) hbot
  rw [Submodule.pow_succ, Submodule.pow_one, ← hdU i, hkey]
  exact key

/-! ### Stacks Section 05ZJ -/

/-- **Stacks Section 05ZJ: an `n`th order thickening is filtered by first order thickenings.**
Let `X ⊂ X'` be an `n`th order thickening of algebraic spaces over `S`, cut out by the sheaf of
ideals `𝓘`.  Then there are closed subspaces
`X = X_0 ⊂ X_1 ⊂ ⋯ ⊂ X_n = X'`
of `X'` such that each pair `X_k ⊂ X_{k+1}` is a first order thickening; `X_k` is the closed
subspace cut out by `𝓘^{k+1}`, so that the filtration of `X'` comes from the filtration
`0 = 𝓘^{n+1} ⊂ 𝓘^n ⊂ ⋯ ⊂ 𝓘 ⊂ 𝒪_{X'}`.

The statement records `X_k` as cut out by `𝓘^{k+1}` on the affine étale charts over one surjective
étale chart `Uc` of `X'`, which determine a sheaf of ideals of `𝒪_{X'}`
(`AlgebraicGeometry.Space.structureSubmodule_ext_of_forall_isAffine_hom`).  The family is
indexed by all of `ℕ`, and is constant equal to `X'` from `n` on. -/
theorem exists_firstOrderThickening_filtration {n : ℕ} {G : Subfunctor X.1}
    (hG : IsNthOrderThickening B S hS n X G) :
    ∃ (Xs : ℕ → ClosedSubspaces B S hS X.1) (Uc : SmallEtale B S hS X.1),
      IsSurjective B S hS Uc.1.hom ∧
      (∀ A : SmallEtale B S hS X.1, IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) →
        (A ⟶ Uc) → ∀ k : ℕ,
          definingIdealAt B S hS X (Xs k) (op A) =
            definingIdealAt B S hS X ⟨G, hG.1.1⟩ (op A) ^ (k + 1)) ∧
      (Xs 0).1 = G ∧ (Xs n).1 = ⊤ ∧
      (∀ k : ℕ, (Xs k).1 ≤ (Xs (k + 1)).1) ∧
      ∀ k : ℕ, IsFirstOrderThickening B S hS
        ⟨(Xs (k + 1)).1.toFunctor, (Xs (k + 1)).2.1⟩ ((Xs k).1.preimage (Xs (k + 1)).1.ι) :=
  ⟨thickeningFiltration B S hS X ⟨G, hG.1.1⟩, sumAtlasChart B S hS X,
    sumAtlasChart_isSurjective B S hS X,
    fun A hA m k => by
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
      exact definingIdealAt_thickeningFiltration B S hS X _ A m k,
    rfl, thickeningFiltration_eq_top B S hS X _ hG.2,
    thickeningFiltration_le_succ B S hS X _,
    isFirstOrderThickening_thickeningFiltration B S hS X _ hG.1⟩

end AlgebraicGeometry.Space

end
