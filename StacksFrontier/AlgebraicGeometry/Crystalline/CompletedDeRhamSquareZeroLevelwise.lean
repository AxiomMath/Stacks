module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZeroFinite

/-!
# `IsSquareZero` from integrability over infinitely many coordinates

`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamSquareZero.lean` derives
`Crystalline.CompletedDeRham.IsSquareZero` from a **finite** coordinate expansion
`Crystalline.CompletedDeRham.IsFiniteCoordinateExpansion`, and
`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable_of_fintype` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamSquareZeroFinite.lean` produces that
finite expansion out of a plain one by taking the whole of `Finset.univ`, which costs `[Fintype ι]`
on the index type of the coordinates.

**This module removes that finiteness.**  What replaces it is a *levelwise* finite expansion: the
coordinate expansion of `Crystalline.IsCoordinateExpansion` is a `HasSum` in the `p`-adic topology
of `M ⊗̂_D Ω`, so at each level `pⁿ` it is already a finite sum, and the two substitutions the
computation of `∇²` makes can both be taken over one finset chosen for that level.

## Why a single finset suffices at each level

The cancellation in `Crystalline.CompletedDeRham.differential_differential_tmul` pairs the term
indexed `(j, k)` with the term indexed `(k, j)`, so the double sum must run over a **square**
`s ×ˢ s`: the finset of the outer substitution, which expands `∇ m`, and the finset of the inner
one, which expands `∇ (θ_j m)` for each `j` of the outer finset, have to be the same.  Taking the
union of the two does not close up — enlarging the outer finset enlarges the set of inner
expansions needed.

It closes up because of the following two facts, neither of which needs `ι` finite.

* `Crystalline.finite_notMem_pPowSmul_of_isCoordinateExpansion` — for each `m` and each `n` only
  finitely many `i` have `θ_i(m) ∉ pⁿ M`.  Outside that finite set the term
  `θ_i(m) ⊗ d x_i` already vanishes at level `n`
  (`Crystalline.CompletedDeRham.toCompletedTensor_tmul_val_eq_zero_of_mem_pPowSmul`), so the
  level-`n` expansion holds over *every* finset containing it, and in particular is stable under
  enlargement.
* `Crystalline.theta_mem_pPowSmul_of_mem_of_basis` — a coordinate operator carries `pⁿ M` into
  itself.  So at an index `j` outside the support of `m` the element `θ_j(m)` lies in `pⁿ M`, and
  then *every* `θ_k(θ_j m)` lies in `pⁿ M`: the support of `θ_j m` is empty and asks for nothing.

So the finset `s = supp(m) ∪ ⋃_{j ∈ supp(m)} supp(θ_j m)` carries the level-`n` expansion of `∇ m`
and of `∇(θ_j m)` for every `j ∈ s`, which is
`Crystalline.CompletedDeRham.IsLevelwiseCoordinateExpansion`, and that is all the computation of
the square needs.

## What the basis is for, and that it cannot be dropped

Both facts above are read off a `Module.Basis` of `Ω` on the coordinate differentials: the first is
`Crystalline.finite_notMem_pPowSmul_of_isCoordinateExpansion`, whose docstring records that
freeness cannot be dropped — `Crystalline.finite_thetaPow_notMem_pPowSmul` exhibits a situation in
which its conclusion fails while the quasi-nilpotence condition (07JE) of [Stacks, Tag 07JE]
holds — and the second is read off the same basis through the coordinate functional
`Crystalline.completedTensorCoordinateLevel`, which computes `θ_k(x) mod pⁿ` from `∇ x` alone.

It is finiteness of `ι` that is removed here, not the basis.  The basis is the source's own
hypothesis: the sentence after (60.17.1.1) of [Stacks, Tag 07J9] — "`Ω_D` … is free on `d x_i`" —
and it is carried in exactly the same way by
`Crystalline.isIntegrable_of_isThetaMonomialFamily` and
`Crystalline.isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily`, the two clauses (07JD) and
(07JE) of [Stacks, Tag 07JG] that the library proves.

Nothing else about the forms is weakened: the exterior properties
`Crystalline.CompletedDeRham.IsGradedExterior` are still needed, and
`Crystalline.CompletedDeRham.SquareZeroExamples.not_isSquareZero` still shows that integrability
alone does not give the conclusion.

## Main definitions

* `Crystalline.CompletedDeRham.IsLevelExpansionAt` — the coordinate expansion of `∇` at one
  element, read at one level `pⁿ`, as a finite sum over one finset of coordinates.
* `Crystalline.CompletedDeRham.IsLevelwiseCoordinateExpansion` — for every element and every level
  a finset carrying that element's expansion *and* the expansions of its coordinate translates.

## Main results

* `Crystalline.CompletedDeRham.differential_differential_tmul_val` — **the square of the
  differential vanishes at the level `pⁿ` on a pure tensor**, from one finset as above.
* `Crystalline.CompletedDeRham.isSquareZero_of_commute_of_isLevelwiseCoordinateExpansion` and
  `Crystalline.CompletedDeRham.isSquareZero_of_isLevelwiseCoordinateExpansion` — `IsSquareZero`
  with no finiteness on `ι`.
* `Crystalline.isLevelwiseCoordinateExpansion_of_finite_support` — the levelwise expansion from the
  finiteness of the supports and the invariance of `pⁿ M` under the coordinate operators.
* `Crystalline.theta_mem_pPowSmul_of_mem_of_basis` — **a coordinate operator carries `pⁿ M` into
  itself**, from a basis of `Ω` and nothing else; in particular with no additivity assumed on the
  operators.
* `Crystalline.isLevelwiseCoordinateExpansion_of_basis` — the levelwise expansion from a basis.
* `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable_of_basis` — **integrability and a basis
  of `Ω` on the coordinate differentials give `IsSquareZero`, with no `[Fintype ι]`**.
* `Crystalline.Pair.isSquareZero_of_basis` — the same for a `Crystalline.Pair`, whose integrability
  and coordinate operators are its own fields; this is the `[Fintype ι]`-free form of
  `Crystalline.Pair.isSquareZero`.

## What is and is not proved

**No `@[stacks]` attribute is placed here and no tag is proved.**  What is removed is one
hypothesis, `[Fintype ι]`, of the discharge of the square-zero condition; the exterior properties
of the forms remain hypotheses because the family of forms is a carried parameter, and
[Stacks, Tag 07LG] itself is untouched.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public section

open DividedPowers
open scoped TensorProduct

universe u v w uI

namespace Crystalline

namespace CompletedDeRham

/-! ### Level values of the image of the uncompleted tensor product -/

section Val

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M]

/-- **An element of `pⁿ (M ⊗_D Ω)` has level-`n` value zero in the completion.**  The level-`n`
value of the image of `y` is the class of `y` modulo `pⁿ`. -/
theorem toCompletedTensor_val_eq_zero_of_mem (n : ℕ) {y : M ⊗[D] Omega}
    (hy : y ∈ ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Omega))) :
    (toCompletedTensor p D Omega M y).val n = 0 := by
  rw [AdicCompletion.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hy

/-- **The ring element `pⁿ` lies in the `n`-th power of the `p`-adic ideal.** -/
theorem pow_mem_pAdicIdeal_pow (n : ℕ) : ((p : D) ^ n) ∈ (pAdicIdeal (A := D) p) ^ n := by
  rw [pAdicIdeal, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

/-- **A pure tensor whose left factor lies in `pⁿ M` has level-`n` value zero.**  This is the one
reason a coordinate whose operator lands in `pⁿ M` contributes nothing at level `n`, and so the
reason the level-`n` expansion of `∇` is stable under enlarging the finset of coordinates. -/
theorem toCompletedTensor_tmul_val_eq_zero_of_mem_pPowSmul (n : ℕ) {x : M} (omega : Omega)
    (hx : x ∈ pPowSmul p D M n) :
    (toCompletedTensor p D Omega M (x ⊗ₜ[D] omega)).val n = 0 := by
  obtain ⟨y, hy⟩ := (mem_pPowSmul_iff p D M).mp hx
  refine toCompletedTensor_val_eq_zero_of_mem p D Omega M n ?_
  rw [← hy, ← TensorProduct.smul_tmul']
  exact Submodule.smul_mem_smul (pow_mem_pAdicIdeal_pow p D n) Submodule.mem_top

/-- The level-`n` value of a finite sum is the sum of the level-`n` values. -/
theorem val_sum_apply {α : Type*} (t : Finset α) (f : α → CompletedTensor p D Omega M) (n : ℕ) :
    (∑ a ∈ t, f a).val n = ∑ a ∈ t, (f a).val n := by
  simp only [← AdicCompletion.eval_apply]
  exact map_sum (AdicCompletion.eval (pAdicIdeal (A := D) p) (M ⊗[D] Omega) n) f t

end Val

/-! ### The coordinate expansion read at one level -/

section LevelExpansion

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] {M : Type w} [AddCommGroup M] [Module D M] {ι : Type uI} (dx : ι → Omega)
  {dmap : D → Omega} (nabla : CompletedConnection p D Omega dmap M) (theta : ι → (M → M))

/-- **The coordinate expansion `∇ m = Σ_j θ_j m ⊗ d x_j` at the single element `m` and the single
level `pⁿ`, as a finite sum over the finset `s`.**

This is weaker than `Crystalline.CompletedDeRham.IsFiniteCoordinateExpansion` in two ways that
matter: it is an equation in the level-`n` quotient rather than in `M ⊗̂_D Ω`, and the finset is
allowed to depend on `m` and on `n`.  Both are what the `HasSum` of
`Crystalline.IsCoordinateExpansion` actually gives when the index type is infinite. -/
def IsLevelExpansionAt (n : ℕ) (s : Finset ι) (m : M) : Prop :=
  (nabla m).val n =
    (∑ j ∈ s, toCompletedTensor p D Omega M (theta j m ⊗ₜ[D] dx j)).val n

/-- **A levelwise coordinate expansion**: for every element `m` and every level `pⁿ` there is one
finset of coordinates over which both the expansion of `∇ m` and the expansions of all the
`∇ (θ_j m)` for `j` in that finset hold at level `n`.

The two clauses being carried by the *same* finset is the whole point: the computation of `∇²`
substitutes the expansion twice and cancels the term indexed `(j, k)` against the one indexed
`(k, j)`, which needs the double sum to run over a square. -/
def IsLevelwiseCoordinateExpansion : Prop :=
  ∀ (m : M) (n : ℕ), ∃ s : Finset ι,
    IsLevelExpansionAt p D Omega dx nabla theta n s m ∧
      ∀ j ∈ s, IsLevelExpansionAt p D Omega dx nabla theta n s (theta j m)

end LevelExpansion

/-! ### The square of the differential, level by level -/

section SquareZero

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap) {ι : Type uI} (dx : ι → Om 1)
  (theta : ι → (M → M))

/-- **Exterior multiplication by a fixed form is local at the levels**: the level-`n` value of
`ω ∧ −` depends on its argument only through the argument's level-`n` value.  It is the completion
of a `D`-linear map, hence computed level by level by `AdicCompletion.map_val_apply`. -/
theorem wedgeMap_val_congr (i n : ℕ) (ω : Om i) (x y : CompletedTensor p D (Om 1) M)
    (h : x.val n = y.val n) :
    (wedgeMap p D Om wedge M i ω x).val n = (wedgeMap p D Om wedge M i ω y).val n := by
  show (AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M (wedge i ω)) x).val n =
    (AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M (wedge i ω)) y).val n
  rw [AdicCompletion.map_val_apply, AdicCompletion.map_val_apply, h]

/-- **The differential of `M ⊗^∧_D Ω^*_D` on a pure tensor, at the level `pⁿ`, with the connection
expanded in coordinates over one finset.**

This is `Crystalline.CompletedDeRham.differential_toCompletedTensor_tmul` with the global finite
expansion replaced by the level-`n` one of `Crystalline.CompletedDeRham.IsLevelExpansionAt`, and it
is the one step the computation of the square iterates. -/
theorem differential_toCompletedTensor_tmul_val (i n : ℕ) (s : Finset ι) (m : M) (ω : Om i)
    (hexp : IsLevelExpansionAt p D (Om 1) dx nabla theta n s m) :
    (differential p D Om wedge deRham M nabla hleib i
        (toCompletedTensor p D (Om i) M (m ⊗ₜ[D] ω))).val n =
      ((∑ j ∈ s, toCompletedTensor p D (Om (i + 1)) M (theta j m ⊗ₜ[D] wedge i ω (dx j))) +
        toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i ω)).val n := by
  have hw : wedgeMap p D Om wedge M i ω
        (∑ j ∈ s, toCompletedTensor p D (Om 1) M (theta j m ⊗ₜ[D] dx j)) =
      ∑ j ∈ s, toCompletedTensor p D (Om (i + 1)) M (theta j m ⊗ₜ[D] wedge i ω (dx j)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ wedgeMap_of_tmul p D Om wedge M i ω _ _
  rw [differential_of_tmul, AdicCompletion.val_add_apply, AdicCompletion.val_add_apply,
    wedgeMap_val_congr p D Om wedge M i n ω _ _ hexp, hw]

/-- A pure tensor whose right factor is zero has zero image in the completed tensor product. -/
private theorem toCompletedTensor_tmul_eq_zero_of_eq_zero {Omega : Type v} [AddCommGroup Omega]
    [Module D Omega] {x : Omega} (m : M) (hx : x = 0) :
    toCompletedTensor p D Omega M (m ⊗ₜ[D] x) = 0 := by
  rw [hx, TensorProduct.tmul_zero, map_zero]

/-- Two pure tensors with the same left factor and right factors summing to zero add up to
zero in the completed tensor product. -/
private theorem toCompletedTensor_tmul_add_tmul_eq_zero {Omega : Type v} [AddCommGroup Omega]
    [Module D Omega] {x y : Omega} (m : M) (hxy : x + y = 0) :
    toCompletedTensor p D Omega M (m ⊗ₜ[D] x) + toCompletedTensor p D Omega M (m ⊗ₜ[D] y) = 0 := by
  rw [← map_add, ← TensorProduct.tmul_add]
  exact toCompletedTensor_tmul_eq_zero_of_eq_zero p D M m hxy

/-- **The double sum of the computation of `∇²` vanishes.**  The term indexed `(j, k)` cancels
against the term indexed `(k, j)`: the coordinate operators commute — integrability — and the wedge
of a one-form with itself is zero, so the diagonal terms vanish outright.

This is the group of terms `hA` of the proof of
`Crystalline.CompletedDeRham.differential_differential_tmul`, hoisted so that the levelwise proof
can reuse it. -/
theorem sum_sum_toCompletedTensor_wedge_eq_zero (hext : IsGradedExterior D Om wedge deRham)
    (hcomm : ∀ j k, theta j ∘ theta k = theta k ∘ theta j) (i : ℕ) (m : M) (ω : Om i)
    (s : Finset ι) :
    (∑ j ∈ s, ∑ k ∈ s, toCompletedTensor p D (Om (i + 1 + 1)) M
      (theta k (theta j m) ⊗ₜ[D] wedge (i + 1) (wedge i ω (dx j)) (dx k))) = 0 := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun a _ ↦ a.swap) (fun a _ ↦ ?_) (fun a _ hne ↦ ?_)
    (fun a ha ↦ ?_) (fun a _ ↦ ?_)
  · obtain ⟨j, k⟩ := a
    have hjk : theta j (theta k m) = theta k (theta j m) := congrFun (hcomm j k) m
    simp only [Prod.swap_prod_mk, hjk]
    exact toCompletedTensor_tmul_add_tmul_eq_zero p D M _
      (hext.wedge_comm D Om wedge deRham i ω (dx j) (dx k))
  · obtain ⟨j, k⟩ := a
    intro heq
    rw [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    refine hne ?_
    obtain ⟨rfl, -⟩ := heq
    exact toCompletedTensor_tmul_eq_zero_of_eq_zero p D M _ (hext.wedge_self _ _ _)
  · exact Finset.mem_product.2 ⟨(Finset.mem_product.1 ha).2, (Finset.mem_product.1 ha).1⟩
  · exact Prod.swap_swap a

/-- **The two single sums of the computation of `∇²` cancel each other.**  Their `j`-th terms add
to `θ_j m ⊗ (d (ω ∧ d x_j) + d ω ∧ d x_j)`, which is zero by the graded Leibniz rule for the de
Rham differential of the forms against the closed one-form `d x_j`.

This is the group of terms `hYZ` of the proof of
`Crystalline.CompletedDeRham.differential_differential_tmul`, hoisted so that the levelwise proof
can reuse it. -/
theorem sum_toCompletedTensor_deRham_wedge_add_eq_zero (hext : IsGradedExterior D Om wedge deRham)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (i : ℕ) (m : M) (ω : Om i) (s : Finset ι) :
    (∑ j ∈ s, toCompletedTensor p D (Om (i + 1 + 1)) M
        (theta j m ⊗ₜ[D] deRham (i + 1) (wedge i ω (dx j)))) +
      (∑ j ∈ s, toCompletedTensor p D (Om (i + 1 + 1)) M
        (theta j m ⊗ₜ[D] wedge (i + 1) (deRham i ω) (dx j))) = 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  exact toCompletedTensor_tmul_add_tmul_eq_zero p D M _ (hext.deRham_wedge i ω (dx j) (hdx j))

/-- **The square of the differential vanishes at the level `pⁿ` on a pure tensor**, given one
finset of coordinates carrying the level-`n` expansion of `∇ m` and of every `∇ (θ_j m)` for `j` in
it.

This is `Crystalline.CompletedDeRham.differential_differential_tmul` with the global finite
expansion replaced by the levelwise one, which is what an infinite family of coordinates
supplies.  The three groups of terms are the same and vanish for the same reasons: the double sum
by `Crystalline.CompletedDeRham.sum_sum_toCompletedTensor_wedge_eq_zero`, the two single sums by
`Crystalline.CompletedDeRham.sum_toCompletedTensor_deRham_wedge_add_eq_zero`, and `m ⊗ d (d ω)`
because `d ∘ d = 0`. -/
theorem differential_differential_tmul_val (hext : IsGradedExterior D Om wedge deRham)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (hcomm : ∀ j k, theta j ∘ theta k = theta k ∘ theta j)
    (i n : ℕ) (s : Finset ι) (m : M) (ω : Om i)
    (h0 : IsLevelExpansionAt p D (Om 1) dx nabla theta n s m)
    (h1 : ∀ j ∈ s, IsLevelExpansionAt p D (Om 1) dx nabla theta n s (theta j m)) :
    (differential p D Om wedge deRham M nabla hleib (i + 1)
      (differential p D Om wedge deRham M nabla hleib i
        (toCompletedTensor p D (Om i) M (m ⊗ₜ[D] ω)))).val n = 0 := by
  classical
  rw [differential_val_congr p D Om wedge deRham M nabla hleib (i + 1) n _ _
      (differential_toCompletedTensor_tmul_val p D Om wedge deRham M nabla hleib dx theta i n s
        m ω h0),
    map_add, map_sum, AdicCompletion.val_add_apply,
    val_sum_apply p D (Om (i + 1 + 1)) M s _ n]
  have hterm : ∀ j ∈ s, (differential p D Om wedge deRham M nabla hleib (i + 1)
        (toCompletedTensor p D (Om (i + 1)) M (theta j m ⊗ₜ[D] wedge i ω (dx j)))).val n =
      ((∑ k ∈ s, toCompletedTensor p D (Om (i + 1 + 1)) M
            (theta k (theta j m) ⊗ₜ[D] wedge (i + 1) (wedge i ω (dx j)) (dx k))) +
          toCompletedTensor p D (Om (i + 1 + 1)) M
            (theta j m ⊗ₜ[D] deRham (i + 1) (wedge i ω (dx j)))).val n := fun j hj ↦
    differential_toCompletedTensor_tmul_val p D Om wedge deRham M nabla hleib dx theta (i + 1) n s
      (theta j m) (wedge i ω (dx j)) (h1 j hj)
  rw [Finset.sum_congr rfl hterm,
    differential_toCompletedTensor_tmul_val p D Om wedge deRham M nabla hleib dx theta (i + 1) n s
      m (deRham i ω) h0,
    ← val_sum_apply p D (Om (i + 1 + 1)) M s _ n, ← AdicCompletion.val_add_apply]
  have hW : toCompletedTensor p D (Om (i + 1 + 1)) M
      (m ⊗ₜ[D] deRham (i + 1) (deRham i ω)) = 0 := by
    exact toCompletedTensor_tmul_eq_zero_of_eq_zero p D M _ (hext.deRham_deRham _ _)
  have hsplit : (∑ j ∈ s, ((∑ k ∈ s, toCompletedTensor p D (Om (i + 1 + 1)) M
          (theta k (theta j m) ⊗ₜ[D] wedge (i + 1) (wedge i ω (dx j)) (dx k))) +
        toCompletedTensor p D (Om (i + 1 + 1)) M
          (theta j m ⊗ₜ[D] deRham (i + 1) (wedge i ω (dx j))))) +
      ((∑ j ∈ s, toCompletedTensor p D (Om (i + 1 + 1)) M
          (theta j m ⊗ₜ[D] wedge (i + 1) (deRham i ω) (dx j))) +
        toCompletedTensor p D (Om (i + 1 + 1)) M
          (m ⊗ₜ[D] deRham (i + 1) (deRham i ω))) = 0 := by
    rw [Finset.sum_add_distrib,
      sum_sum_toCompletedTensor_wedge_eq_zero p D Om wedge deRham M dx theta hext hcomm i m ω s,
      zero_add, hW, add_zero]
    exact sum_toCompletedTensor_deRham_wedge_add_eq_zero p D Om wedge deRham M dx theta hext hdx
      i m ω s
  rw [hsplit, AdicCompletion.val_zero_apply]

/-- **The square of the differential vanishes at every level on the image of the whole uncompleted
tensor product `M ⊗_D Ω^i_D`**, not only on pure tensors.  The finset of coordinates is chosen per
pure tensor, which is why the induction goes through with no uniform choice. -/
theorem differential_differential_toCompletedTensor_val
    (hext : IsGradedExterior D Om wedge deRham)
    (hexp : IsLevelwiseCoordinateExpansion p D (Om 1) dx nabla theta)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (hcomm : ∀ j k, theta j ∘ theta k = theta k ∘ theta j)
    (i n : ℕ) (y : M ⊗[D] Om i) :
    (differential p D Om wedge deRham M nabla hleib (i + 1)
      (differential p D Om wedge deRham M nabla hleib i
        (toCompletedTensor p D (Om i) M y))).val n = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m ω =>
    obtain ⟨s, h0, h1⟩ := hexp m n
    exact differential_differential_tmul_val p D Om wedge deRham M nabla hleib dx theta hext hdx
      hcomm i n s m ω h0 h1
  | add a b ha hb =>
    rw [map_add, map_add, map_add, AdicCompletion.val_add_apply, ha, hb, add_zero]

/-- **The differentials of `M ⊗^∧_D Ω^*_D` compose to zero, with no finiteness on the index type of
the coordinates**, from the commutation of the one family of coordinate operators at hand.

The hypotheses are, exhaustively: the data of `Crystalline.CompletedDeRham.complex` itself, and

* `hext`, that the forms are exterior in the sense of
  `Crystalline.CompletedDeRham.IsGradedExterior`;
* `hexp`, a levelwise coordinate expansion
  `Crystalline.CompletedDeRham.IsLevelwiseCoordinateExpansion`;
* `hdx`, that the coordinate differentials `d x_j` are closed;
* `hcomm`, that the coordinate operators of `hexp` commute.

This is `Crystalline.CompletedDeRham.isSquareZero_of_commute` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/CompletedPoincareIntegrable.lean` with the
finite expansion over a fixed finset replaced by the levelwise one. -/
theorem isSquareZero_of_commute_of_isLevelwiseCoordinateExpansion
    (hext : IsGradedExterior D Om wedge deRham)
    (hexp : IsLevelwiseCoordinateExpansion p D (Om 1) dx nabla theta)
    (hdx : ∀ j, deRham 1 (dx j) = 0)
    (hcomm : ∀ j k, theta j ∘ theta k = theta k ∘ theta j) :
    IsSquareZero p D Om wedge deRham M nabla hleib := by
  intro i
  refine AddMonoidHom.ext fun x ↦ ?_
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective
    ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Om i)) (x.val n)
  have hxz : x.val n = (toCompletedTensor p D (Om i) M z).val n := hz.symm
  rw [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, AdicCompletion.val_zero_apply,
    differential_val_congr p D Om wedge deRham M nabla hleib (i + 1) n _ _
      (differential_val_congr p D Om wedge deRham M nabla hleib i n x _ hxz)]
  exact differential_differential_toCompletedTensor_val p D Om wedge deRham M nabla hleib dx theta
    hext hexp hdx hcomm i n z

/-- **The differentials of `M ⊗^∧_D Ω^*_D` compose to zero, with no finiteness on the index type of
the coordinates**, from integrability of the connection.

This is `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` with the finite coordinate
expansion replaced by the levelwise one; `Crystalline.IsIntegrable` is quantified over every family
of operators realizing the expansion, so it is applied to the family `theta` at hand through the
plain expansion `hco`. -/
theorem isSquareZero_of_isLevelwiseCoordinateExpansion
    (hext : IsGradedExterior D Om wedge deRham)
    (hco : IsCoordinateExpansion p D (Om 1) dx nabla theta)
    (hexp : IsLevelwiseCoordinateExpansion p D (Om 1) dx nabla theta)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (hint : IsIntegrable p D (Om 1) dx nabla) :
    IsSquareZero p D Om wedge deRham M nabla hleib :=
  isSquareZero_of_commute_of_isLevelwiseCoordinateExpansion p D Om wedge deRham M nabla hleib dx
    theta hext hexp hdx (hint theta hco)

end SquareZero

end CompletedDeRham

/-! ### The levelwise expansion from the finiteness of the supports -/

section Support

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M] {ι : Type uI} {dx : ι → Omega}
  {dmap : D → Omega} {nabla : CompletedConnection p D Omega dmap M} {theta : ι → (M → M)}

/-- **The level-`n` coordinate expansion holds over every finset containing the level-`n`
support.**

The expansion of `Crystalline.IsCoordinateExpansion` is a `HasSum` in the `p`-adic topology of
`M ⊗̂_D Ω`, which is not known to be Hausdorff; pushed through the level-`n` evaluation it becomes
a `HasSum` in a **discrete** quotient, where convergence of the net of partial sums means that the
partial sums are eventually equal to the limit.  So the expansion holds at level `n` over some
finset; and enlarging that finset changes nothing, because every added term has its left tensor
factor in `pⁿ M` and so vanishes at level `n` by
`Crystalline.CompletedDeRham.toCompletedTensor_tmul_val_eq_zero_of_mem_pPowSmul`. -/
theorem isLevelExpansionAt_of_support_subset
    (hco : IsCoordinateExpansion p D Omega dx nabla theta) (m : M) (n : ℕ) (t : Finset ι)
    (ht : ∀ i : ι, theta i m ∉ pPowSmul p D M n → i ∈ t) :
    CompletedDeRham.IsLevelExpansionAt p D Omega dx nabla theta n t m := by
  classical
  let := completedTensorTopology p D Omega M
  let := Ideal.adicModuleTopology (pAdicIdeal (A := D) p)
    ((M ⊗[D] Omega) ⧸ ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Omega)))
  have : DiscreteTopology ((M ⊗[D] Omega) ⧸
      ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Omega))) :=
    discreteTopology_quotient_pow_smul_top (pAdicIdeal (A := D) p) (M ⊗[D] Omega) n
  have hpush := (hco m).map
    (AdicCompletion.eval (pAdicIdeal (A := D) p) (M ⊗[D] Omega) n).toAddMonoidHom
    (continuous_adicCompletion_eval (pAdicIdeal (A := D) p) (M ⊗[D] Omega) n)
  have hT : Filter.Tendsto (fun u : Finset ι ↦ ∑ i ∈ u,
        ((AdicCompletion.eval (pAdicIdeal (A := D) p) (M ⊗[D] Omega) n).toAddMonoidHom ∘
          fun i ↦ toCompletedTensor p D Omega M (theta i m ⊗ₜ[D] dx i)) i)
      Filter.atTop (nhds ((AdicCompletion.eval (pAdicIdeal (A := D) p) (M ⊗[D] Omega) n)
        (nabla m))) := hpush
  rw [nhds_discrete] at hT
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp (Filter.tendsto_pure.mp hT)
  have hbig := ht₀ (t ∪ t₀) Finset.subset_union_right
  simp only [Function.comp_apply, LinearMap.toAddMonoidHom_coe, AdicCompletion.eval_apply] at hbig
  have hdiff : ∑ i ∈ (t ∪ t₀) \ t,
      (toCompletedTensor p D Omega M (theta i m ⊗ₜ[D] dx i)).val n = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    refine CompletedDeRham.toCompletedTensor_tmul_val_eq_zero_of_mem_pPowSmul p D Omega M n _ ?_
    by_contra hcon
    exact (Finset.mem_sdiff.mp hi).2 (ht i hcon)
  have hsd := Finset.sum_sdiff (f := fun i ↦
    (toCompletedTensor p D Omega M (theta i m ⊗ₜ[D] dx i)).val n)
    (Finset.subset_union_left (s₁ := t) (s₂ := t₀))
  rw [hdiff, zero_add] at hsd
  rw [CompletedDeRham.IsLevelExpansionAt, CompletedDeRham.val_sum_apply, hsd]
  exact hbig.symm

/-- **The levelwise coordinate expansion from the finiteness of the supports.**

The two inputs are: `hsupp`, that for every `m` and every `n` only finitely many coordinates have
`θ_i(m) ∉ pⁿ M`; and `hcl`, that each coordinate operator carries `pⁿ M` into itself.  Together
they make the construction close up.  Take

`s = supp(m, n) ∪ ⋃_{j ∈ supp(m, n)} supp(θ_j m, n)`.

Then `s` contains `supp(m, n)`, so it carries the level-`n` expansion of `∇ m`.  And for `j ∈ s`
it contains `supp(θ_j m, n)`: if `j ∈ supp(m, n)` because of the union, and otherwise because
`θ_j(m) ∈ pⁿ M`, whence `θ_k(θ_j m) ∈ pⁿ M` for every `k` by `hcl` and that support is empty.

`hcl` holds for an additive family by `Crystalline.map_mem_pPowSmul`, and for the coordinate
operators of a connection whose forms are free on the `d x_i` by
`Crystalline.theta_mem_pPowSmul_of_mem_of_basis`, with no additivity assumed. -/
theorem isLevelwiseCoordinateExpansion_of_finite_support
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    (hsupp : ∀ (m : M) (n : ℕ), {i : ι | theta i m ∉ pPowSmul p D M n}.Finite)
    (hcl : ∀ (n : ℕ) (k : ι) (x : M), x ∈ pPowSmul p D M n → theta k x ∈ pPowSmul p D M n) :
    CompletedDeRham.IsLevelwiseCoordinateExpansion p D Omega dx nabla theta := by
  classical
  intro m n
  refine ⟨(hsupp m n).toFinset ∪ (hsupp m n).toFinset.biUnion
    (fun j ↦ (hsupp (theta j m) n).toFinset), ?_, ?_⟩
  · refine isLevelExpansionAt_of_support_subset p D Omega M hco m n _ fun i hi ↦ ?_
    exact Finset.mem_union_left _ ((hsupp m n).mem_toFinset.mpr hi)
  · intro j hj
    refine isLevelExpansionAt_of_support_subset p D Omega M hco (theta j m) n _ fun k hk ↦ ?_
    by_cases hjs : j ∈ (hsupp m n).toFinset
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, hjs, (hsupp (theta j m) n).mem_toFinset.mpr hk⟩)
    · have hmem : theta j m ∈ pPowSmul p D M n := by
        by_contra hcon
        exact hjs ((hsupp m n).mem_toFinset.mpr hcon)
      exact absurd (hcl n k _ hmem) hk

end Support

/-! ### A coordinate operator carries `pⁿ M` into itself -/

section Closure

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M] {ι : Type uI} {dx : ι → Omega}
  {dmap : D → Omega} {nabla : CompletedConnection p D Omega dmap M} {theta : ι → (M → M)}

/-- **A coordinate operator carries `pⁿ M` into itself**, as soon as the coordinate differentials
are a basis of `Ω`.

Nothing is assumed about the operators beyond their realizing the expansion — in particular not
additivity, which is what `Crystalline.map_mem_pPowSmul` would want.  What is used is that the
basis computes `θ_k(x) mod pⁿ` from `∇ x` alone, by
`Crystalline.completedTensorCoordinateLevel_eq_of_hasSum`, through a `D`-**linear** functional.  An
element of `pⁿ M` is `pⁿ` times another, the connection is additive and hence commutes with that
integer multiple, and `pⁿ` annihilates `M ⧸ pⁿ M`. -/
theorem theta_mem_pPowSmul_of_mem_of_basis
    (hco : IsCoordinateExpansion p D Omega dx nabla theta) (b : Module.Basis ι D Omega)
    (hdx : ∀ i, dx i = b i) (n : ℕ) (k : ι) {x : M} (hx : x ∈ pPowSmul p D M n) :
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
    rw [← completedTensorCoordinateLevel_eq_of_hasSum p D Omega M hco b hdx k x n, hnabla,
      map_nsmul, ← Nat.cast_smul_eq_nsmul D, Nat.cast_pow]
    exact CompletedDeRham.smul_quotient_eq_zero p D
      (CompletedDeRham.pow_mem_pAdicIdeal_pow p D n) _
  exact (Submodule.Quotient.mk_eq_zero _).mp hzero

/-- **The levelwise coordinate expansion from a basis of `Ω` on the coordinate differentials.**

The two inputs of `Crystalline.isLevelwiseCoordinateExpansion_of_finite_support` are both read off
the basis: the finiteness of the supports is
`Crystalline.finite_notMem_pPowSmul_of_isCoordinateExpansion`, and the invariance of `pⁿ M` under
the coordinate operators is `Crystalline.theta_mem_pPowSmul_of_mem_of_basis`.

Freeness cannot be dropped: `Crystalline.finite_thetaPow_notMem_pPowSmul` exhibits a situation in
which the finiteness of the supports fails while the quasi-nilpotence condition (07JE) of
[Stacks, Tag 07JE] holds. -/
theorem isLevelwiseCoordinateExpansion_of_basis
    (hco : IsCoordinateExpansion p D Omega dx nabla theta) (b : Module.Basis ι D Omega)
    (hdx : ∀ i, dx i = b i) :
    CompletedDeRham.IsLevelwiseCoordinateExpansion p D Omega dx nabla theta :=
  isLevelwiseCoordinateExpansion_of_finite_support p D Omega M hco
    (fun m n ↦ finite_notMem_pPowSmul_of_isCoordinateExpansion p D Omega M hco b hdx m n)
    (fun n k _ hx ↦ theta_mem_pPowSmul_of_mem_of_basis p D Omega M hco b hdx n k hx)

end Closure

/-! ### `IsSquareZero` from integrability and a basis, with no finiteness -/

namespace CompletedDeRham

section Basis

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap) {ι : Type uI} (dx : ι → Om 1)
  (theta : ι → (M → M))

/-- **`Crystalline.CompletedDeRham.isSquareZero_of_commute` with `[Fintype ι]` traded for a basis
of `Ω` on the coordinate differentials.**  The levelwise expansion is supplied by
`Crystalline.isLevelwiseCoordinateExpansion_of_basis`. -/
theorem isSquareZero_of_commute_of_basis (hext : IsGradedExterior D Om wedge deRham)
    (hco : IsCoordinateExpansion p D (Om 1) dx nabla theta)
    (hdxb : ∀ j, deRham 1 (dx j) = 0) (b : Module.Basis ι D (Om 1))
    (hdx : ∀ i, dx i = b i) (hcomm : ∀ j k, theta j ∘ theta k = theta k ∘ theta j) :
    IsSquareZero p D Om wedge deRham M nabla hleib :=
  isSquareZero_of_commute_of_isLevelwiseCoordinateExpansion p D Om wedge deRham M nabla hleib dx
    theta hext (isLevelwiseCoordinateExpansion_of_basis p D (Om 1) M hco b hdx) hdxb hcomm

/-- **`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable_of_fintype` with `[Fintype ι]`
traded for a basis of `Ω` on the coordinate differentials.**

The hypotheses are, exhaustively: the data of `Crystalline.CompletedDeRham.complex` itself, and

* `hext`, that the forms are exterior, `Crystalline.CompletedDeRham.IsGradedExterior`;
* `hco`, a coordinate expansion of `∇` in the `d x_j`, `Crystalline.IsCoordinateExpansion`;
* `hdxb`, that the coordinate differentials are closed;
* `b` and `hdx`, a basis of `Ω` on the coordinate differentials;
* `hint`, **integrability**, `Crystalline.IsIntegrable`, [Stacks, Tag 07JD].

**The index type of the coordinates is arbitrary.**  The basis is the source's own hypothesis,
carried exactly as `Crystalline.isIntegrable_of_isThetaMonomialFamily` carries it, and
`Crystalline.isLevelwiseCoordinateExpansion_of_basis` records why it cannot be dropped. -/
theorem isSquareZero_of_isIntegrable_of_basis (hext : IsGradedExterior D Om wedge deRham)
    (hco : IsCoordinateExpansion p D (Om 1) dx nabla theta)
    (hdxb : ∀ j, deRham 1 (dx j) = 0) (b : Module.Basis ι D (Om 1))
    (hdx : ∀ i, dx i = b i) (hint : IsIntegrable p D (Om 1) dx nabla) :
    IsSquareZero p D Om wedge deRham M nabla hleib :=
  isSquareZero_of_commute_of_basis p D Om wedge deRham M nabla hleib dx theta hext hco hdxb b hdx
    (hint theta hco)

end Basis

end CompletedDeRham

/-! ### The de Rham differentials of a pair compose to zero, with no finiteness -/

section Pair

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1}
  (hleib : CompletedDeRham.IsGradedLeibniz D Om wedge deRham dmap) {ι : Type uI}
  (dx : ι → Om 1)

/-- **The completed de Rham differentials of a pair compose to zero, over an arbitrary family of
coordinates.**

This is `Crystalline.Pair.isSquareZero` with `[Fintype ι]` traded for a basis of `Ω` on the
coordinate differentials.  Both inputs beyond the forms are fields of the pair:
`Crystalline.Pair.hasCoordinateOperators` gives the coordinate expansion and
`Crystalline.Pair.isIntegrable` is integrability, [Stacks, Tag 07JD].  What remains carried is the
exterior character of the *forms*, closedness of the coordinate differentials, and the basis —
all three properties of the carried parameters `Om`, `wedge`, `deRham`, `dx` and of nothing else.

This is what makes the hypothesis `hsq` of the double complex of
[Stacks, Proposition 60.21.3, Tag 07LG] a theorem with no finiteness assumption on the
coordinates, which matters because the identification of the degree-zero forms of that tag pins
them to the completed direct sum over a set which is not finite. -/
theorem Pair.isSquareZero_of_basis (P : Pair p D (Om 1) dx dmap)
    (hext : CompletedDeRham.IsGradedExterior D Om wedge deRham)
    (hdxb : ∀ j, deRham 1 (dx j) = 0) (b : Module.Basis ι D (Om 1))
    (hdx : ∀ i, dx i = b i) :
    CompletedDeRham.IsSquareZero p D Om wedge deRham P.carrier P.nabla hleib := by
  obtain ⟨theta, hco⟩ := P.hasCoordinateOperators
  exact CompletedDeRham.isSquareZero_of_isIntegrable_of_basis p D Om wedge deRham P.carrier
    P.nabla hleib dx theta hext hco hdxb b hdx P.isIntegrable

end Pair

end Crystalline

end
