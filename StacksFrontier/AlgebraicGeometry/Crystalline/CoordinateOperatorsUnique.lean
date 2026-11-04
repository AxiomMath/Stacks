module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateExpansionSupport
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorHausdorff

/-!
# Items (07JD) and (07JE) from the composite coordinate operators

`Crystalline.IsIntegrable` and `Crystalline.IsTopologicallyQuasiNilpotent` — items (07JD) and
(07JE) of [Stacks, Lemma 60.17.3, Tag 07JG] — are conditions on *every* family `θ` of coordinate
operators of a completed connection, not on a chosen one.  Before this module nothing in the tree
produced either of them except for a subsingleton module, for an empty family of coordinates, or
for a connection whose coordinate expansion is vacuous; in particular no nonzero module with a
nonempty coordinate family had them.

This module proves both, for an arbitrary module, from the structure the source's own proof
produces.  The source expands the comparison over `D(1)` as
`c(m ⊗ 1) = ∑_K θ_K(m) ⊗ ∏ ξ_i^{[k_i]}`, reads `∇(m) = ∑_i θ_i(m) d x_i` off its degree-one part,
and then compares coefficients over `D(2)` to get `θ_K = ∏ θ_i^{k_i}`; that last identity is
`Crystalline.IsThetaMonomialFamily`, and from it the two items are immediate —
`Crystalline.IsThetaMonomialFamily.comm` is already the commutation of (07JD), and a one-point
multi-index is an iterate by `Crystalline.IsThetaMonomialFamily.single`.

What was missing is the quantifier.  Both predicates range over all coordinate expansions of the
connection, and the monomial family is one of them.  The bridge is uniqueness:

**the coordinate operators of a completed connection are unique** as soon as the family `d x_i` is
a basis of `Ω` and the module is `p`-adically separated.

Both inputs are the source's: the basis is the sentence after (60.17.1.1) of
[Stacks, Tag 07J9] — "`Ω_D` … is free on `d x_i`", so "any element of `Ω_D` can be written
uniquely as `∑ f_i d x_i`" — and separatedness is the Hausdorff half of item (07JB), already a
field of `Crystalline.FirstOrderCrystal` and of `Crystalline.Pair`.  Neither predicate is weakened:
`Crystalline.IsIntegrable` and `Crystalline.IsTopologicallyQuasiNilpotent` are used exactly as
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnection.lean` states them.

## How uniqueness is proved

A coordinate expansion is a `HasSum` in the `p`-adic topology of `M ⊗̂_D Ω`, and the summands
`θ_i(m) ⊗ d x_i` are not determined by their sum in any topological group.  What determines them
is the basis: it gives a `D`-linear coordinate `M ⊗_D Ω → M` at each index, and a linear map
carries the `p`-adic filtration into the `p`-adic filtration, so the coordinate descends to the
quotients `M ⧸ p^n M` of the completion and is continuous there — the target being *discrete*, by
`Crystalline.discreteTopology_adicModuleTopology_of_eq_bot`.  Pushing the sum through it leaves a
single surviving term, so `θ_j(m) mod p^n` is computed from `∇(m)` alone, for every `n`; and a
separated module has nothing in every `p^n M`.

## Main definitions

* `Crystalline.tensorCoordinate` — the `j`-th coordinate `M ⊗_D Ω → M` of a basis of `Ω`.
* `Crystalline.completedTensorCoordinateLevel` — that coordinate read on `M ⊗̂_D Ω` with values in
  `M ⧸ p^n M`, which is the continuous functional the argument needs.

## Main results

* `Crystalline.completedTensorCoordinateLevel_eq_of_hasSum` — the `j`-th coordinate of `∇(m)`
  modulo `p^n` is `θ_j(m)`, for any coordinate expansion `θ`.
* `Crystalline.eq_of_isCoordinateExpansion` — **the coordinate operators are unique.**
* `Crystalline.isIntegrable_of_isThetaMonomialFamily` — **item (07JD)**.
* `Crystalline.isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily` — **item (07JE)**.
* `Crystalline.hasCoordinateOperators_of_isCoordinateExpansion` — the non-vacuity clause
  `hasCoordinateOperators` of `Crystalline.Pair`, from the same datum.
* `Crystalline.finite_thetaPow_notMem_pSmul_of_isTopologicallyQuasiNilpotent` — the converse of
  the hypothesis `hfin` of (07JE) above, so that hypothesis is not a strengthening of the
  conclusion but the same condition on the monomial family.

## What is and is not proved

Two of the four items of the target of [Stacks, Tag 07JG] are proved here, for an arbitrary module
with an arbitrary completed connection.  The functor of the tag, which carries `@[stacks 07JG]`, is
`Crystalline.GlobalCrystallineSituation.SmallSite.crystalPairFunctor` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalPairFunctor07JG.lean`.  Neither
statement quantifies over a `Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG`,
of which no term exists anywhere, nor over any other bundle: both are statements about an
arbitrary `D`-module with an arbitrary completed connection, and their hypotheses are the source's
own and are satisfiable — `Crystalline.trivialTaylorCrystal` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Reduction07JGWitness.lean` satisfies all of them at
once, and `Crystalline.TaylorCrystal` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCrystal07JG.lean` is the record of exactly
these hypotheses, whose functor to the pairs carries the attribute for the tag as a whole.

**The tag itself is not proved here.**  What is not in this module is the functor, whose source
is the crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`; what is proved is purely
algebraic — two of the four clauses of its target, from a basis of `Ω`, separatedness, and a
monomial family of coordinate operators.

**Three hypotheses are carried, each named and each the source's own.**

* `b` and `hdx` — a basis of `Ω` on the `d x_i`.  This is carried exactly as it is carried by
  `Crystalline.finite_notMem_pPowSmul_of_isCoordinateExpansion` and by the nine statements of
  `StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFree.lean` and
  `StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFreeFinite.lean`: the library has **no** statement that the differentials of
  the `p`-adically completed divided power envelope `D` are free, only
  `Crystalline.dividedPowerDifferentialsBasis` for the divided power *polynomial* algebra.  So the
  theorems below do not apply to `Ω_D` of the source's own situation until that is proved; they
  apply at once to the polynomial algebra, where the basis is known.
* `hfamM` — `θ_K = ∏ θ_i^{k_i}`, which the source derives by comparing coefficients in `D(2)`.
  This is the one genuinely geometric input and it is not derived here.
* `hfin` for (07JE) — the source's own "as the sum expressing `c(m ⊗ 1)` has to converge
  `p`-adically we conclude that for each `i` and each `m ∈ M` only a finite number of
  `θ_i^k(m)` are allowed to be nonzero modulo `p`", in the form of the finiteness of the set of
  multi-indices.  `Crystalline.finite_thetaPow_notMem_pSmul_of_isTopologicallyQuasiNilpotent`
  shows it follows from the conclusion, so nothing is smuggled in.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public section

open scoped TensorProduct

universe u v uI w w'

namespace Crystalline

/-! ### The coordinates of a basis of `Ω`, on `M ⊗_D Ω` and on its completion -/

section Coordinate

variable {D : Type u} [CommRing D] {Omega : Type v} [AddCommGroup Omega] [Module D Omega]
  {M : Type w} [AddCommGroup M] [Module D M] {ι : Type uI} [DecidableEq ι]

/-- **The `j`-th coordinate of `M ⊗_D Ω` against a basis of `Ω`.**  A basis of `Ω` indexed by `ι`
identifies `M ⊗_D Ω` with `ι →₀ M` through `TensorProduct.equivFinsuppOfBasisRight`, and this is
the evaluation of that family at `j`.  It is `D`-linear, which is what lets it be read on the
`p`-adic completion. -/
noncomputable def tensorCoordinate (b : Module.Basis ι D Omega) (j : ι) :
    (M ⊗[D] Omega) →ₗ[D] M :=
  (Finsupp.lapply (M := M) (R := D) j).comp
    (TensorProduct.equivFinsuppOfBasisRight b).toLinearMap

/-- The `j`-th coordinate of `x ⊗ b i` is `x` if `i = j` and `0` otherwise. -/
private theorem tensorCoordinate_tmul_basis (b : Module.Basis ι D Omega) (i j : ι) (x : M) :
    tensorCoordinate (M := M) b j (x ⊗ₜ[D] b i) = if i = j then x else 0 := by
  rw [tensorCoordinate]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.equivFinsuppOfBasisRight_apply_tmul, Module.Basis.repr_self,
    Finsupp.mapRange_single, Finsupp.lapply_apply, one_smul, Finsupp.single_apply]

/-- **The `j`-th coordinate of `x ⊗ b j` is `x`.**  Together with
`Crystalline.tensorCoordinate_tmul_basis_of_ne` this is the one computation the uniqueness
argument makes. -/
theorem tensorCoordinate_tmul_basis_self (b : Module.Basis ι D Omega) (j : ι) (x : M) :
    tensorCoordinate (M := M) b j (x ⊗ₜ[D] b j) = x := by
  simp [tensorCoordinate_tmul_basis]

/-- **The `j`-th coordinate of `x ⊗ b i` vanishes for `i ≠ j`.** -/
theorem tensorCoordinate_tmul_basis_of_ne (b : Module.Basis ι D Omega) {i j : ι} (hij : i ≠ j)
    (x : M) :
    tensorCoordinate (M := M) b j (x ⊗ₜ[D] b i) = 0 := by
  simp [tensorCoordinate_tmul_basis, hij]

end Coordinate

section Level

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M] {ι : Type uI} [DecidableEq ι]

/-- **The `p`-adic filtration level `p^n M`**, spelled as the submodule
`(p)^n • ⊤` the `p`-adic topology and `SModEq` use.  It is `Crystalline.pPowSmul` by definition,
by `Crystalline.pLevel_eq_pPowSmul`; the unfolded spelling is used throughout this module because
the quotients by it are the targets of maps the completion's `AdicCompletion.eval` produces, and
those are stated in the unfolded form. -/
abbrev pLevel (n : ℕ) : Submodule D M :=
  DividedPowers.pAdicIdeal (A := D) p ^ n • (⊤ : Submodule D M)

/-- `Crystalline.pLevel` is `Crystalline.pPowSmul`. -/
theorem pLevel_eq_pPowSmul (n : ℕ) : pLevel p D M n = pPowSmul p D M n := rfl

/-- **`p^n` annihilates `M ⧸ p^n M`.**  The quotient of a module by `p^n M` has no `p^n`-multiples
other than zero, which is what makes its `p`-adic topology discrete. -/
theorem pLevel_quotient_eq_bot (n : ℕ) :
    pLevel p D (M ⧸ pLevel p D M n) n = ⊥ := by
  have hmap := Submodule.map_smul'' (DividedPowers.pAdicIdeal (A := D) p ^ n)
    (⊤ : Submodule D M) (pLevel p D M n).mkQ
  rw [Submodule.mkQ_map_self, Submodule.map_top, Submodule.range_mkQ] at hmap
  exact hmap.symm

/-- **A linear map descends to the `p`-adic quotients.**  A `D`-linear map carries `p^n M` into
`p^n N`, so it induces a map `M ⧸ p^n M → N ⧸ p^n N`. -/
noncomputable def pLevelMapQ (N : Type w') [AddCommGroup N] [Module D N]
    (f : M →ₗ[D] N) (n : ℕ) : (M ⧸ pLevel p D M n) →ₗ[D] (N ⧸ pLevel p D N n) :=
  Submodule.mapQ (pLevel p D M n) (pLevel p D N n) f fun _ hx ↦
    map_mem_pow_smul_top_of_mem (DividedPowers.pAdicIdeal (A := D) p) f n hx

/-- The map `M ⧸ p^n M → N ⧸ p^n N` induced by `f` sends the class of `x` to the class of
`f x`. -/
@[simp] theorem pLevelMapQ_mk (N : Type w') [AddCommGroup N] [Module D N]
    (f : M →ₗ[D] N) (n : ℕ) (x : M) :
    pLevelMapQ p D M N f n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (p := pLevel p D N n) (f x) :=
  rfl

/-- **The `j`-th coordinate of `M ⊗̂_D Ω` modulo `p^n`.**  The completion is evaluated at level
`n`, which lands in `(M ⊗_D Ω) ⧸ p^n (M ⊗_D Ω)`, and the coordinate of the basis is applied
there.  This is the functional the uniqueness argument pushes a coordinate expansion through: its
target is discrete, so convergence in the source becomes an equality of finite data. -/
noncomputable def completedTensorCoordinateLevel (b : Module.Basis ι D Omega) (j : ι) (n : ℕ) :
    CompletedTensor p D Omega M →ₗ[D] (M ⧸ pLevel p D M n) :=
  (pLevelMapQ p D (M ⊗[D] Omega) M (tensorCoordinate b j) n).comp
    (AdicCompletion.eval (DividedPowers.pAdicIdeal (A := D) p) (M ⊗[D] Omega) n)

/-- On the image of `z ∈ M ⊗_D Ω` in the completion, the `j`-th coordinate modulo `p^n` is the
class of the `j`-th coordinate of `z`. -/
@[simp] theorem completedTensorCoordinateLevel_of (b : Module.Basis ι D Omega) (j : ι) (n : ℕ)
    (z : M ⊗[D] Omega) :
    completedTensorCoordinateLevel p D Omega M b j n (toCompletedTensor p D Omega M z) =
      Submodule.Quotient.mk (p := pLevel p D M n) (tensorCoordinate b j z) := by
  show pLevelMapQ p D (M ⊗[D] Omega) M (tensorCoordinate b j) n
      (AdicCompletion.eval (DividedPowers.pAdicIdeal (A := D) p) (M ⊗[D] Omega) n
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := D) p) (M ⊗[D] Omega) z)) = _
  rw [AdicCompletion.eval_of]
  rfl

/-- **The `j`-th coordinate modulo `p^n` is continuous.**  The submodules `p^n • ⊤` are a basis of
neighbourhoods of `0` for the `p`-adic topology of the completion, the functional kills the `n`-th
one because a linear map carries the filtration into the filtration and the target's `p^n` is
zero, and the target is discrete; so continuity at `0` — hence continuity, the source being a
topological additive group — is that one membership. -/
theorem continuous_completedTensorCoordinateLevel (b : Module.Basis ι D Omega) (j : ι) (n : ℕ) :
    letI := completedTensorTopology p D Omega M
    letI := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p)
      (M ⧸ pLevel p D M n)
    Continuous (completedTensorCoordinateLevel p D Omega M b j n) := by
  let := (DividedPowers.pAdicIdeal (A := D) p).adicTopology
  let := completedTensorTopology p D Omega M
  let := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p) (M ⧸ pLevel p D M n)
  have hbas := (DividedPowers.pAdicIdeal (A := D) p).ringFilterBasis.submodulesBasisIsBasis
    ((DividedPowers.pAdicIdeal (A := D) p).adic_module_basis (CompletedTensor p D Omega M))
  have hbasT := (DividedPowers.pAdicIdeal (A := D) p).ringFilterBasis.submodulesBasisIsBasis
    ((DividedPowers.pAdicIdeal (A := D) p).adic_module_basis (M ⧸ pLevel p D M n))
  have : IsTopologicalAddGroup (CompletedTensor p D Omega M) :=
    hbas.toModuleFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
  have : IsTopologicalAddGroup (M ⧸ pLevel p D M n) :=
    hbasT.toModuleFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
  have : DiscreteTopology (M ⧸ pLevel p D M n) :=
    discreteTopology_adicModuleTopology_of_eq_bot _ (M ⧸ pLevel p D M n)
      (pLevel_quotient_eq_bot p D M n)
  have hopen : IsOpen ((pLevel p D (CompletedTensor p D Omega M) n :
      Submodule D (CompletedTensor p D Omega M)) : Set (CompletedTensor p D Omega M)) :=
    (SubmodulesBasis.openAddSubgroup hbas n).isOpen'
  refine continuous_of_continuousAt_zero
    (completedTensorCoordinateLevel p D Omega M b j n) ?_
  have hmem : {x : CompletedTensor p D Omega M |
      completedTensorCoordinateLevel p D Omega M b j n x = 0} ∈
      nhds (0 : CompletedTensor p D Omega M) := by
    refine Filter.mem_of_superset (hopen.mem_nhds (Submodule.zero_mem _)) fun x hx ↦ ?_
    have h1 := map_mem_pow_smul_top_of_mem (DividedPowers.pAdicIdeal (A := D) p)
      (completedTensorCoordinateLevel p D Omega M b j n) n hx
    rw [show DividedPowers.pAdicIdeal (A := D) p ^ n •
      (⊤ : Submodule D (M ⧸ pLevel p D M n)) = ⊥ from pLevel_quotient_eq_bot p D M n,
      Submodule.mem_bot] at h1
    exact h1
  have hpure : nhds (completedTensorCoordinateLevel p D Omega M b j n 0) =
      pure (0 : M ⧸ pLevel p D M n) := by
    rw [map_zero, nhds_discrete]
  rw [ContinuousAt, hpure]
  exact Filter.tendsto_pure.mpr hmem

end Level

/-! ### Uniqueness of the coordinate operators -/

section Unique

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M] {ι : Type uI}
  {dx : ι → Omega} {dd : D → Omega} {nabla : CompletedConnection p D Omega dd M}

/-- **The `j`-th coordinate of `∇(m)` modulo `p^n` is `θ_j(m)`, for every coordinate expansion
`θ`.**  Pushing the convergent sum `∇ m = ∑_i θ_i(m) d x_i` through the continuous functional
`Crystalline.completedTensorCoordinateLevel` leaves the single term at `i = j`, and a sum with one
nonzero term is that term.

This is where the basis enters: without it the summands of a convergent sum are not determined by
the sum. -/
theorem completedTensorCoordinateLevel_eq_of_hasSum [DecidableEq ι] {theta : ι → (M → M)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta) (b : Module.Basis ι D Omega)
    (hdx : ∀ i, dx i = b i) (j : ι) (m : M) (n : ℕ) :
    completedTensorCoordinateLevel p D Omega M b j n (nabla m) =
      Submodule.Quotient.mk (p := pLevel p D M n) (theta j m) := by
  classical
  let := completedTensorTopology p D Omega M
  let := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p)
    (M ⧸ pLevel p D M n)
  have : DiscreteTopology (M ⧸ pLevel p D M n) :=
    discreteTopology_adicModuleTopology_of_eq_bot _ (M ⧸ pLevel p D M n)
      (pLevel_quotient_eq_bot p D M n)
  have hpush := (hco m).map
    (completedTensorCoordinateLevel p D Omega M b j n).toAddMonoidHom
    (continuous_completedTensorCoordinateLevel p D Omega M b j n)
  have hterm : ∀ i : ι,
      ((completedTensorCoordinateLevel p D Omega M b j n).toAddMonoidHom ∘
          fun i ↦ toCompletedTensor p D Omega M (theta i m ⊗ₜ[D] dx i)) i =
        if i = j then Submodule.Quotient.mk (p := pLevel p D M n) (theta j m) else 0 := by
    intro i
    show completedTensorCoordinateLevel p D Omega M b j n
        (toCompletedTensor p D Omega M (theta i m ⊗ₜ[D] dx i)) = _
    rw [completedTensorCoordinateLevel_of, hdx i, tensorCoordinate_tmul_basis]
    split_ifs with hij
    · subst hij
      rfl
    · exact (pLevel p D M n).mkQ.map_zero
  rw [funext hterm] at hpush
  exact (hasSum_ite_eq j (Submodule.Quotient.mk (p := pLevel p D M n)
    (theta j m))).unique hpush |>.symm

/-- **The coordinate operators of a completed connection are unique.**

Two families `θ`, `θ'` with `∇ m = ∑_i θ_i(m) d x_i = ∑_i θ'_i(m) d x_i` agree, provided the
`d x_i` are a basis of `Ω` and `M` is `p`-adically separated.  Both hypotheses are the source's:
the basis is the uniqueness of the expansion `∑ f_i d x_i` recorded after (60.17.1.1) of
[Stacks, Tag 07J9], and separatedness is the Hausdorff half of item (07JB).

This is what turns the two universally quantified items (07JD) and (07JE) into statements about
one family, and it is the only reason they are provable at all from a single coordinate
expansion. -/
theorem eq_of_isCoordinateExpansion {theta theta' : ι → (M → M)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    (hco' : IsCoordinateExpansion p D Omega dx nabla theta')
    (b : Module.Basis ι D Omega) (hdx : ∀ i, dx i = b i)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) M) :
    theta = theta' := by
  classical
  funext j m
  refine hM.haus' (theta j m - theta' j m) (fun n ↦ ?_) |> sub_eq_zero.mp
  rw [SModEq.zero]
  have h := (completedTensorCoordinateLevel_eq_of_hasSum p D Omega M hco b hdx j m n).symm.trans
    (completedTensorCoordinateLevel_eq_of_hasSum p D Omega M hco' b hdx j m n)
  rw [Submodule.Quotient.eq] at h
  exact h

end Unique

/-! ### Items (07JD) and (07JE) -/

section Items

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M] {ι : Type uI}
  {dx : ι → Omega} {dd : D → Omega} {nabla : CompletedConnection p D Omega dd M}
  {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}

/-- **The non-vacuity clause `hasCoordinateOperators`**, read off a coordinate expansion.  It is
the field of `Crystalline.Pair` and of `Crystalline.FirstOrderCrystal` asserting that the
connection has *some* family of coordinate operators, which is what keeps the two conditions below
from being vacuously true. -/
theorem hasCoordinateOperators_of_isCoordinateExpansion
    (hco : IsCoordinateExpansion p D Omega dx nabla theta) :
    ∃ theta : ι → (M → M), IsCoordinateExpansion p D Omega dx nabla theta :=
  ⟨theta, hco⟩

/-- **Item (07JD): the connection is integrable.**

The coordinate operators of a monomial family commute, by
`Crystalline.IsThetaMonomialFamily.comm`, which is the source's conclusion
"`θ_i ∘ θ_j = θ_j ∘ θ_i` (this provides an alternative proof of the integrability of `∇`)" read
off the identity `θ_K = ∏ θ_i^{k_i}`; and by `Crystalline.eq_of_isCoordinateExpansion` there is no
other family of coordinate operators to check.

`Crystalline.IsIntegrable` is the predicate unchanged: it still quantifies over every coordinate
expansion of `∇`. -/
theorem isIntegrable_of_isThetaMonomialFamily
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    (b : Module.Basis ι D Omega) (hdx : ∀ i, dx i = b i)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) M) :
    IsIntegrable p D Omega dx nabla := by
  intro theta' hco' i j
  rw [eq_of_isCoordinateExpansion p D Omega M hco' hco b hdx hM]
  exact hfamM.comm i j

/-- **Item (07JE): the connection is topologically quasi-nilpotent.**

The source concludes it from the `p`-adic convergence of the expansion of `c(m ⊗ 1)` over `D(1)`:
"only a finite number of `θ_i^k(m)` are allowed to be nonzero modulo `p`".  That convergence is
`hfin` below, the finiteness of the set of multi-indices `K` with `θ_K(m) ∉ p M`; the pairs
`(i, k)` with `k ≠ 0` inject into those multi-indices by `K = k · e_i`, along which
`θ_i^k = θ_{k · e_i}` by `Crystalline.IsThetaMonomialFamily.single`.  Uniqueness of the coordinate
operators removes the quantifier over coordinate expansions.

`hfin` is not a strengthening of the conclusion: it follows from it, by
`Crystalline.finite_thetaPow_notMem_pSmul_of_isTopologicallyQuasiNilpotent`. -/
theorem isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    (b : Module.Basis ι D Omega) (hdx : ∀ i, dx i = b i)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) M)
    (hfin : ∀ m : M, {K : ι →₀ ℕ | thetaPow K m ∉ pSmul p D M}.Finite) :
    IsTopologicallyQuasiNilpotent p D Omega dx nabla := by
  classical
  intro theta' hco' m
  rw [eq_of_isCoordinateExpansion p D Omega M hco' hco b hdx hM]
  refine Set.Finite.of_finite_image
    (f := fun q : ι × ℕ ↦ Finsupp.single q.1 q.2) ((hfin m).subset ?_) ?_
  · rintro K ⟨q, ⟨-, hq⟩, rfl⟩
    rw [Set.mem_setOf_eq, hfamM.single q.1 q.2]
    exact hq
  · rintro ⟨i, k⟩ ⟨hk, -⟩ ⟨i', k'⟩ ⟨hk', -⟩ hsingle
    rcases (Finsupp.single_eq_single_iff i i' k k').mp hsingle with ⟨rfl, rfl⟩ | ⟨h0, -⟩
    · rfl
    · exact absurd h0 hk

/-- **The finiteness hypothesis of (07JE) above follows from (07JE).**  The quasi-nilpotence
condition bounds the exponent in each variable and, with the support bound `hsupp` that a basis of
`Ω` supplies through
`Crystalline.finite_notMem_pPowSmul_of_isCoordinateExpansion`, the set of multi-indices `K` with
`θ_K(m) ∉ p M` is finite.

So `hfin` of `Crystalline.isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily` is the condition
itself, read on the monomial family, and not a stronger assumption. -/
theorem finite_thetaPow_notMem_pSmul_of_isTopologicallyQuasiNilpotent
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hadd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    (b : Module.Basis ι D Omega) (hdx : ∀ i, dx i = b i)
    (hqn : IsTopologicallyQuasiNilpotent p D Omega dx nabla) (m : M) :
    {K : ι →₀ ℕ | thetaPow K m ∉ pSmul p D M}.Finite := by
  have hone : pSmul p D M = pPowSmul p D M 1 := (pPowSmul_one p D M).symm
  rw [hone]
  refine finite_thetaPow_notMem_pPowSmul p D M hfamM hadd (fun i m' ↦ ?_) ?_
  · exact finite_iterate_notMem_pSmul_of_finite_prod p D M (hqn theta hco) i m'
  · exact finite_notMem_pPowSmul_of_isCoordinateExpansion p D Omega M hco b hdx m 1

end Items

end Crystalline

end
