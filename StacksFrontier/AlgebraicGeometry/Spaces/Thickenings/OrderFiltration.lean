module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerAffineChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleDivisorDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderFiltration

/-!
# A finite order thickening is filtered by first order thickenings

Let `X ⊂ X'` be an `n`th order thickening of algebraic spaces over a scheme `S`, with ideal
sheaf `𝓘 ⊆ 𝒪_{X'}`, so that `𝓘^{n+1} = 0`.  The running text of Section 05ZJ of the Stacks
project ("Thickenings", More on Morphisms of Spaces) observes that the filtration
`0 = 𝓘^{n+1} ⊂ 𝓘^n ⊂ ⋯ ⊂ 𝓘 ⊂ 𝒪_{X'}` cuts out a chain of closed subspaces
`X = X_0 ⊂ X_1 ⊂ ⋯ ⊂ X_n = X'` such that each `X_k ⊂ X_{k+1}` is a first order thickening.
This file proves it.  (The source prints the last two terms of the chain as
`X_{n-1} ⊂ X_{n+1} = X'`; the index `n + 1` is a misprint for `n`, since `X_k` is cut out by
`𝓘^{k+1}` and it is `𝓘^{n+1}` that vanishes.)

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_succMultipleClosedSubspaces_of_isAffine`: on an
  affine étale chart, the closed subspace `X_k` cut out by `𝓘^{k+1}` has defining ideal
  `𝓘(U)^{k+1}`.
* `AlgebraicGeometry.Space.le_succMultipleClosedSubspaces`,
  `AlgebraicGeometry.Space.succMultipleClosedSubspaces_monotone` and
  `AlgebraicGeometry.Space.succMultipleClosedSubspaces_eq_top`: `X = X_0 ⊂ X_1 ⊂ ⋯`, and
  `X_n = X'` when `𝓘^{n+1} = 0`.
* `AlgebraicGeometry.Space.isFirstOrderThickening_succMultipleClosedSubspaces`: each
  `X_k ⊂ X_{k+1}` is a first order thickening.
* `AlgebraicGeometry.Space.exists_idealPow_firstOrderThickening_filtration`: **Section 05ZJ**,
  the filtration of an `n`th order thickening, with the ideal sheaf of `X_k` equal to `𝓘^{k+1}`.

## Implementation notes

The closed subspace `X_k` cut out by `𝓘^{k+1}` is the `(k+1)`-fold sum
`AlgebraicGeometry.Space.succMultipleClosedSubspaces` of `X` with itself in the sense of
Stacks 083U, whose ideal sheaf is `𝓘^{k+1}` by
`AlgebraicGeometry.Space.definingIdealSheaf_succMultipleClosedSubspaces` (`𝓘` being
quasi-coherent by `AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`).  So no
new closed subspace is constructed; by the injectivity half of Stacks 03MB the ideal sheaf
determines it.

To read `X_k ⊂ X_{k+1}` as a thickening, `X_{k+1}` is taken as an algebraic space in its own
right and `X_k` as the inverse image of `X_k` along the inclusion `X_{k+1} ⟶ X'`.  Its defining
ideal is computed on the cofinal family of affine charts of `X_{k+1}` lying over affine charts
of `X'` (Stacks 03G2, `AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`): there it
is the extension of `𝓘(V)^{k+1}` along the restriction map
(`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_map`), so its square is contained in the
extension of `𝓘(V)^{k+2}`, which is the defining ideal of `X_{k+1}` in itself and hence zero.
The vanishing descends from the covering family by
`AlgebraicGeometry.Space.definingIdealAt_pow_eq_bot_of_ofArrows`.

The source adds "over `B`": every `X_k` is a closed subspace of `X'`, so it is a space over `B`
through `X'`, and the inclusions are then morphisms over `B` by construction.

## References

* [Stacks Project, Tag 05ZJ](https://stacks.math.columbia.edu/tag/05ZJ)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}

/-- The square of the extension of `J^{k+1}` lies in the extension of `J^{k+2}`. -/
private theorem map_pow_succ_sq_le {R T : Type*} [CommSemiring R] [CommSemiring T]
    (φ : R →+* T) (J : Ideal R) (k : ℕ) :
    Ideal.map φ (J ^ (k + 1)) ^ (1 + 1) ≤ Ideal.map φ (J ^ (k + 1 + 1)) := by
  rw [← Ideal.map_pow, ← pow_mul]
  exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))

/-- **The defining ideal of `X_k` on an affine chart is `𝓘(U)^{k+1}`.** On an étale chart of `X`
with affine underlying scheme, the defining ideal of the `(k+1)`-fold sum of a closed subspace
`Z` with itself is the `(k+1)`st power of the defining ideal of `Z`. -/
theorem definingIdealAt_succMultipleClosedSubspaces_of_isAffine (Z : ClosedSubspaces B S hS X.1)
    (k : ℕ) (A : SmallEtale B S hS X.1)
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A)) :
    definingIdealAt B S hS X (succMultipleClosedSubspaces B S hS X Z k) (op A) =
      definingIdealAt B S hS X Z (op A) ^ (k + 1) := by
  have hZ := isQuasicoherentOnSite_definingIdealSheaf B S hS X Z
  have h := congrArg
    (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule => N.obj (op A))
    (definingIdealSheaf_succMultipleClosedSubspaces B S hS X Z hZ k)
  refine h.trans ?_
  refine (chartSubmodule_idealPowSubmodule_eq_of_isQuasicoherentOnSite B S hS X.1 X.2
    (definingIdealSheaf B S hS X Z) (k + 1) _
    (SheafOfModules.isQuasicoherentOnSite_unit _) hZ A hA).trans ?_
  exact Ideal.mul_top _

/-- The closed subspaces `X_k` grow with `k`. -/
theorem succMultipleClosedSubspaces_le_succ (Z : ClosedSubspaces B S hS X.1) (k : ℕ) :
    (succMultipleClosedSubspaces B S hS X Z k).1 ≤
      (succMultipleClosedSubspaces B S hS X Z (k + 1)).1 :=
  le_of_definingIdealSheaf_le B S hS X _ _
    (structureSubmodule_le_of_forall_isAffine B S hS X _ _ fun A hA => by
      show definingIdealAt B S hS X (succMultipleClosedSubspaces B S hS X Z (k + 1)) (op A) ≤
        definingIdealAt B S hS X (succMultipleClosedSubspaces B S hS X Z k) (op A)
      rw [definingIdealAt_succMultipleClosedSubspaces_of_isAffine B S hS Z (k + 1) A hA,
        definingIdealAt_succMultipleClosedSubspaces_of_isAffine B S hS Z k A hA]
      exact Ideal.pow_le_pow_right (by omega))

/-- **`X = X_0 ⊂ X_1 ⊂ ⋯`: the chain is monotone.** -/
theorem succMultipleClosedSubspaces_monotone (Z : ClosedSubspaces B S hS X.1) :
    Monotone fun k => (succMultipleClosedSubspaces B S hS X Z k).1 :=
  monotone_nat_of_le_succ (succMultipleClosedSubspaces_le_succ B S hS Z)

/-- Every `X_k` contains `X = X_0`. -/
theorem le_succMultipleClosedSubspaces (Z : ClosedSubspaces B S hS X.1) (k : ℕ) :
    Z.1 ≤ (succMultipleClosedSubspaces B S hS X Z k).1 :=
  succMultipleClosedSubspaces_monotone B S hS Z (Nat.zero_le k)

/-- **`X_n = X'`.** If the `(n+1)`st power of the defining ideal of `Z` vanishes on every étale
chart, the closed subspace cut out by that power is all of `X`. -/
theorem succMultipleClosedSubspaces_eq_top {n : ℕ} (Z : ClosedSubspaces B S hS X.1)
    (h : ∀ U : SmallEtale B S hS X.1, definingIdealAt B S hS X Z (op U) ^ (n + 1) = ⊥) :
    (succMultipleClosedSubspaces B S hS X Z n).1 = ⊤ :=
  top_unique (le_of_definingIdealSheaf_le B S hS X (topClosedSubspace B S hS X) _
    (structureSubmodule_le_of_forall_isAffine B S hS X _ _ fun A hA => by
      show definingIdealAt B S hS X (succMultipleClosedSubspaces B S hS X Z n) (op A) ≤ _
      rw [definingIdealAt_succMultipleClosedSubspaces_of_isAffine B S hS Z n A hA, h A]
      exact bot_le))

/-- **Each step `X_k ⊂ X_{k+1}` of the filtration of a thickening is a first order thickening.**
Let `G ⊂ X` be a thickening and `X_k` the closed subspace cut out by the `(k+1)`st power of its
ideal.  Reading `X_{k+1}` as an algebraic space, the inverse image of `X_k` along the inclusion
`X_{k+1} ⟶ X` is a first order thickening of `X_{k+1}`. -/
theorem isFirstOrderThickening_succMultipleClosedSubspaces {G : Subfunctor X.1}
    (hG : IsThickening B S hS X G) (k : ℕ) :
    IsFirstOrderThickening B S hS
      ⟨(succMultipleClosedSubspaces B S hS X ⟨G, hG.1⟩ (k + 1)).1.toFunctor,
        (succMultipleClosedSubspaces B S hS X ⟨G, hG.1⟩ (k + 1)).2.1⟩
      ((succMultipleClosedSubspaces B S hS X ⟨G, hG.1⟩ k).1.preimage
        (succMultipleClosedSubspaces B S hS X ⟨G, hG.1⟩ (k + 1)).1.ι) := by
  set Z : ClosedSubspaces B S hS X.1 := ⟨G, hG.1⟩ with hZdef
  set W : AlgebraicSpaces B S hS :=
    ⟨(succMultipleClosedSubspaces B S hS X Z (k + 1)).1.toFunctor,
      (succMultipleClosedSubspaces B S hS X Z (k + 1)).2.1⟩ with hWdef
  let ι : W ⟶ X := ObjectProperty.homMk (succMultipleClosedSubspaces B S hS X Z (k + 1)).1.ι
  have hk : IsThickening B S hS X (succMultipleClosedSubspaces B S hS X Z k).1 :=
    isThickening_of_le B S hS X hG (succMultipleClosedSubspaces B S hS X Z k).2
      (le_succMultipleClosedSubspaces B S hS Z k)
  refine ⟨isThickening_preimage B S hS _ ι hk, fun U => ?_⟩
  obtain ⟨J, Wf, a, d, hdU, hWaff, hVaff, hcov⟩ := exists_affine_chartDiagram_ofArrows B S hS ι U
  refine definingIdealAt_pow_eq_bot_of_ofArrows B S hS W _ 1 U Wf a hcov fun i => ?_
  have hVa : IsAffine ((BigFppfOver.toScheme B S hS).obj (d i).V.1.left) := hVaff i
  have hUa : IsAffine ((BigFppfOver.toScheme B S hS).obj (d i).U.1.left) := by
    rw [hdU i]; exact hWaff i
  have hkey := definingIdealAt_preimage_eq_map B S hS ι
    (succMultipleClosedSubspaces B S hS X Z k) (d i).V (d i).U (d i).g (d i).comm.symm
  have htop := definingIdealAt_preimage_eq_map B S hS ι
    (succMultipleClosedSubspaces B S hS X Z (k + 1)) (d i).V (d i).U (d i).g (d i).comm.symm
  -- The inverse image of `X_{k+1}` in itself is the whole space, with zero defining ideal.
  have hself : (⟨(succMultipleClosedSubspaces B S hS X Z (k + 1)).1.preimage ι.hom,
      isClosedSubspace_preimage B S hS ι.hom _ X.2 W.2
        (succMultipleClosedSubspaces B S hS X Z (k + 1)).2⟩ : ClosedSubspaces B S hS W.1) =
      topClosedSubspace B S hS W := by
    refine Subtype.ext ?_
    rw [topClosedSubspace_coe]
    exact (Subfunctor.preimage_eq_top_iff _ _).2 (by
      show Subfunctor.range (succMultipleClosedSubspaces B S hS X Z (k + 1)).1.ι ≤ _
      rw [Subfunctor.range_ι])
  rw [hself, definingIdealAt_topClosedSubspace B S hS W (d i).U hUa,
    definingIdealAt_succMultipleClosedSubspaces_of_isAffine B S hS Z (k + 1) (d i).V hVa]
    at htop
  rw [← hdU i]
  show definingIdealAt B S hS W
      ⟨(succMultipleClosedSubspaces B S hS X Z k).1.preimage ι.hom,
        isClosedSubspace_preimage B S hS ι.hom _ X.2 W.2
          (succMultipleClosedSubspaces B S hS X Z k).2⟩ (op (d i).U) ^ (1 + 1) = ⊥
  rw [hkey,
    definingIdealAt_succMultipleClosedSubspaces_of_isAffine B S hS Z k (d i).V hVa]
  exact le_bot_iff.1 ((map_pow_succ_sq_le
    ((BigFppfOver.toScheme B S hS).map (d i).g).appTop.hom _ k).trans htop.symm.le)

/-- **Section 05ZJ: an `n`th order thickening is filtered by first order thickenings.** Let
`X ⊂ X'` be an `n`th order thickening of algebraic spaces over `S`, with quasi-coherent ideal
sheaf `𝓘 ⊆ 𝒪_{X'}`.  There are closed subspaces `X_0, X_1, …` of `X'`, the `k`th one cut out by
`𝓘^{k+1}` (so the filtration `0 = 𝓘^{n+1} ⊂ 𝓘^n ⊂ ⋯ ⊂ 𝓘 ⊂ 𝒪_{X'}` is that of their ideal
sheaves), with `X = X_0 ⊂ X_1 ⊂ ⋯ ⊂ X_n = X'`, such that every `X_k ⊂ X_{k+1}` is a first order
thickening. -/
@[stacks 05ZJ "the paragraph after Lemma 05ZP: for an nth order thickening X ⊂ X' with ideal I, \
the filtration 0 = I^{n+1} ⊂ I^n ⊂ ... ⊂ I ⊂ O_{X'} gives closed subspaces \
X = X_0 ⊂ X_1 ⊂ ... ⊂ X_n = X', X_k cut out by I^{k+1}, with each X_k ⊂ X_{k+1} a first order \
thickening (the source's X_{n+1} = X' is a misprint for X_n = X')"]
theorem exists_idealPow_firstOrderThickening_filtration {n : ℕ} {G : Subfunctor X.1}
    (hG : IsNthOrderThickening B S hS n X G) :
    ∃ Xs : ℕ → ClosedSubspaces B S hS X.1,
      (Xs 0).1 = G ∧ (Xs n).1 = ⊤ ∧ Monotone (fun k => (Xs k).1) ∧
      (∀ k, definingIdealSheaf B S hS X (Xs k) =
        idealPowSubmodule (definingIdealSheaf B S hS X ⟨G, hG.1.1⟩) (k + 1)
          (SheafOfModules.unit (structureRingSheaf B S hS X))) ∧
      ∀ k, IsFirstOrderThickening B S hS ⟨(Xs (k + 1)).1.toFunctor, (Xs (k + 1)).2.1⟩
        ((Xs k).1.preimage (Xs (k + 1)).1.ι) :=
  ⟨succMultipleClosedSubspaces B S hS X ⟨G, hG.1.1⟩, rfl,
    succMultipleClosedSubspaces_eq_top B S hS _ hG.2,
    succMultipleClosedSubspaces_monotone B S hS _,
    fun k => definingIdealSheaf_succMultipleClosedSubspaces B S hS X _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X _) k,
    isFirstOrderThickening_succMultipleClosedSubspaces B S hS hG.1⟩

end AlgebraicGeometry.Space

end
