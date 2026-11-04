module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTensorFree
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorConvergence

/-!
# The hypothesis `hsupp` of the Taylor convergence theorem, from freeness of `Ω`

`Crystalline.exists_hasTaylorSum` and
`Crystalline.exists_hasTaylorSum_of_isTopologicallyQuasiNilpotent` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorConvergence.lean` carry one hypothesis that is
not the source's own:

`hsupp : ∀ n, {i | θ_i m ∉ p^n M}.Finite`.

It is the *uncompleted* form of the convergence of the coordinate expansion
`∇ m = ∑_i θ_i(m) d x_i`, which `Crystalline.IsCoordinateExpansion` states as a `HasSum` in the
`p`-adic topology of `M ⊗̂_D Ω`.  The docstrings there record why it was carried: getting from a
statement about `θ_i(m) ⊗ d x_i` in the completion back to one about `θ_i(m)` in `M` needs `Ω` to
be the free module on the `d x_i`.

**This module derives it.**  Freeness of `Ω` on the `d x_i` is the only input added, and it is a
real one: `hsupp` can fail without it, by the counterexample recorded in
`Crystalline.finite_thetaPow_notMem_pPowSmul`.  At the divided power polynomial algebra the
freeness is now a theorem, `Crystalline.dividedPowerDifferentialsBasis` of
`StacksFrontier/AlgebraicGeometry/Crystalline/DividedPowerPoincare.lean`.

The argument is in three steps, each stated on its own.

* The sum converges in the `p`-adic topology of the completion, which is an additive group
  topology whose basic neighbourhoods of `0` are the submodules `p^n • ⊤`
  (`Ideal.adicModuleTopology`, as located in
  `StacksFrontier/AlgebraicGeometry/Crystalline/TaylorHausdorff.lean`).  A convergent sum tends to
  `0` along the cofinite filter, so all but finitely many terms lie in `p^n • ⊤`.
* A term lying in `p^n • ⊤` *after* the map to the completion already lies in `p^n • ⊤` before
  it — the completion's `n`-th level kills `p^n`, so the `n`-th level of the image of `x` is
  `0`, which is membership of `x`.  This needs nothing about `Ω`.
* Finally the coordinate `θ_i(m)` is read off `θ_i(m) ⊗ d x_i` by the basis, through
  `TensorProduct.equivFinsuppOfBasisRight`.  This is the step that needs freeness.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
This module removes one hypothesis of the convergence theorem, replacing it by freeness of `Ω`;
the remaining inputs of the tag — that the reduction datum's functor is an equivalence, the
factorisation `hlift`, and the existence of a reduction datum at all — are not treated here.

## Main results

* `Crystalline.mem_pow_smul_top_of_of_mem` — if the image of `x` in the `I`-adic completion lies
  in `I^n • ⊤` then so does `x`.
* `Crystalline.mem_pow_smul_top_of_tmul_basis_mem` — the coordinate of a pure tensor against a
  basis vector inherits membership in `I^n • ⊤`.
* `Crystalline.finite_notMem_pPowSmul_of_isCoordinateExpansion` — **the hypothesis `hsupp`**,
  from the coordinate expansion and a basis of `Ω` on the `d x_i`.
* `Crystalline.exists_hasTaylorSum_of_isTopologicallyQuasiNilpotent_of_basis` — the Taylor
  convergence theorem with `hsupp` removed.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
-/

@[expose] public section

open scoped TensorProduct

universe u v uI w

namespace Crystalline

/-! ### Membership in `I^n • ⊤` descends from the completion -/

section Completion

variable {R : Type u} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]

/-- **An element whose image in the `I`-adic completion lies in `I^n • ⊤` lies in `I^n • ⊤`.**
The `n`-th level of the completion is `N ⧸ I^n • ⊤`, on which `I^n` acts by zero, so the `n`-th
level of the image of `x` is both `0` and the class of `x`. -/
theorem mem_pow_smul_top_of_of_mem (I : Ideal R) (n : ℕ) {x : N}
    (h : AdicCompletion.of I N x ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I N))) :
    x ∈ (I ^ n • ⊤ : Submodule R N) := by
  have h1 := map_mem_pow_smul_top_of_mem I (AdicCompletion.eval I N n) n h
  rw [AdicCompletion.eval_of] at h1
  have h2 : (I ^ n • (⊤ : Submodule R (N ⧸ (I ^ n • (⊤ : Submodule R N))))) = ⊥ := by
    have hmap := Submodule.map_smul'' (I ^ n) (⊤ : Submodule R N)
      (I ^ n • (⊤ : Submodule R N)).mkQ
    rw [Submodule.mkQ_map_self, Submodule.map_top, Submodule.range_mkQ] at hmap
    exact hmap.symm
  rw [h2, Submodule.mem_bot, Submodule.mkQ_apply] at h1
  exact (Submodule.Quotient.mk_eq_zero _).mp h1

end Completion

/-! ### Reading a coordinate off a pure tensor against a basis -/

section Coordinate

variable {D : Type u} [CommRing D] {Omega : Type v} [AddCommGroup Omega] [Module D Omega]
  {M : Type w} [AddCommGroup M] [Module D M] {ι : Type uI}

/-- **The coordinate of a pure tensor against a basis vector inherits membership in `I^n • ⊤`.**
A basis of `Ω` indexed by `ι` identifies `M ⊗_D Ω` with `ι →₀ M` through
`TensorProduct.equivFinsuppOfBasisRight`, carrying `x ⊗ b i` to the single-point family `x` at
`i`, and `Crystalline.map_mem_pow_smul_top_of_mem` carries the filtration along that identification
and along the evaluation at `i`. -/
theorem mem_pow_smul_top_of_tmul_basis_mem (b : Module.Basis ι D Omega) (I : Ideal D) (n : ℕ)
    (i : ι) {x : M} (h : x ⊗ₜ[D] b i ∈ (I ^ n • ⊤ : Submodule D (M ⊗[D] Omega))) :
    x ∈ (I ^ n • ⊤ : Submodule D M) := by
  classical
  have h1 := map_mem_pow_smul_top_of_mem I
    ((Finsupp.lapply (M := M) (R := D) i).comp
      (TensorProduct.equivFinsuppOfBasisRight b).toLinearMap) n h
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.equivFinsuppOfBasisRight_apply_tmul, Module.Basis.repr_self,
    Finsupp.mapRange_single, Finsupp.lapply_apply, Finsupp.single_eq_same, one_smul] using h1

end Coordinate

/-! ### The hypothesis `hsupp` -/

section Hsupp

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M] {ι : Type uI}

/-- **The hypothesis `hsupp` of the Taylor convergence theorem, from freeness of `Ω` on the
`d x_i`.**  If `∇ m = ∑_i θ_i(m) d x_i` converges in the `p`-adic topology of `M ⊗̂_D Ω` and the
`d x_i` are a basis of `Ω` over `D`, then for every `n` only finitely many indices `i` have
`θ_i(m) ∉ p^n M`.

The hypothesis `hdx` says that the family `d x_i` of the coordinate expansion is the given basis,
which is what makes the conclusion about the *same* indices.  No finiteness is assumed on `ι`.

Freeness cannot be dropped: `Crystalline.finite_thetaPow_notMem_pPowSmul` records a situation in
which the conclusion is false while the quasi-nilpotence condition (07JE) holds. -/
theorem finite_notMem_pPowSmul_of_isCoordinateExpansion {dx : ι → Omega} {dd : D → Omega}
    {nabla : CompletedConnection p D Omega dd M} {theta : ι → (M → M)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta) (b : Module.Basis ι D Omega)
    (hdx : ∀ i, dx i = b i) (m : M) (n : ℕ) :
    {i : ι | theta i m ∉ pPowSmul p D M n}.Finite := by
  classical
  let := (DividedPowers.pAdicIdeal (A := D) p).adicTopology
  let := completedTensorTopology p D Omega M
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
  refine mem_pow_smul_top_of_tmul_basis_mem b _ n i ?_
  rw [← hdx i]
  exact mem_pow_smul_top_of_of_mem _ n hmem

end Hsupp

/-! ### The Taylor convergence theorem with `hsupp` removed -/

section Taylor

variable (p : ℕ) (D : DividedPowerRing.{u}) (B : DividedPowerRing.{u})
  [Algebra (D : Type u) (B : Type u)] (Omega : Type v) [AddCommGroup Omega]
  [Module (D : Type u) Omega] (M : Type u) [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} (dx : ι → Omega) {dd : D.carrier → Omega}
  (nabla : CompletedConnection p (D : Type u) Omega dd M)
  {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}

/-- **The Taylor series of [Stacks, Tag 07JH] converges, with every hypothesis the source's own
once `Ω` is free on the `d x_i`.**  This is
`Crystalline.exists_hasTaylorSum_of_isTopologicallyQuasiNilpotent` with `hsupp` — the one
hypothesis of that theorem which is not the source's own — replaced by a basis of `Ω` on the
differentials of the coordinates, which
`Crystalline.finite_notMem_pPowSmul_of_isCoordinateExpansion` turns into `hsupp`.

The remaining hypotheses are the clauses of the composite coordinate operators, additivity of the
`θ_i`, the coordinate expansion itself, the quasi-nilpotence condition (07JE), and nilpotence of
`p` in `B`, which [Stacks, Tag 07HM] requires of every divided power thickening. -/
theorem exists_hasTaylorSum_of_isTopologicallyQuasiNilpotent_of_basis
    (hfam : IsThetaMonomialFamily M theta thetaPow)
    (hadd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hco : IsCoordinateExpansion p (D : Type u) Omega dx nabla theta)
    (hqn : IsTopologicallyQuasiNilpotent p (D : Type u) Omega dx nabla)
    (b : Module.Basis ι (D : Type u) Omega) (hdx : ∀ i, dx i = b i)
    (hpB : IsNilpotent ((p : (B : Type u)))) (xi : ι → (B : Type u)) (m : M) :
    ∃ t : (B : Type u) ⊗[(D : Type u)] M, HasTaylorSum p D B M thetaPow xi m t :=
  exists_hasTaylorSum_of_isTopologicallyQuasiNilpotent p D B Omega M dx nabla hfam hadd hco hqn
    hpB xi m
    (finite_notMem_pPowSmul_of_isCoordinateExpansion p (D : Type u) Omega M hco b hdx m)

end Taylor

end Crystalline

end
