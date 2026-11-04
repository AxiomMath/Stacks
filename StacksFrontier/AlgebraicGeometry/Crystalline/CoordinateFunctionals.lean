module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsUnique

/-!
# Items (07JD) and (07JE) from coordinate functionals rather than from a basis

`StacksFrontier/AlgebraicGeometry/Crystalline/CoordinateOperatorsUnique.lean` proves items (07JD)
and (07JE) of [Stacks, Lemma 60.17.3, Tag 07JG] — integrability and topological quasi-nilpotence
of the connection — from the composite coordinate operators `θ_K = ∏_i θ_i^{k_i}`, and the bridge
it uses is uniqueness of the coordinate operators of a completed connection.  That uniqueness is
stated there for a family `d x_i` which is a `Module.Basis` of `Ω`.

**A basis is more than the argument needs, and more than `Ω_D` has.**  The module of differentials
`Ω_D` of [Stacks, Tag 07J9] is the `p`-adic completion of the free module on the `d x_i`, which is
free on them only for finitely many coordinates: for an infinite index set an element of `Ω_D` is
a *convergent* series `∑ f_i d x_i` and not a finite linear combination, so no `Module.Basis`
exists and every statement in the tree asking for one is silent about the source's own situation.

What the uniqueness argument actually consumes is weaker, and this module isolates it: a family of
`D`-linear **functionals** `c_j : Ω → D` biorthogonal to the differentials,

`c_j (d x_i) = 1` if `i = j` and `0` otherwise.

Such a family is a `Crystalline.IsCoordinateDual`.  It exists for a completed direct sum — the
`j`-th coordinate of a completion is the completion of the `j`-th coordinate, and the index set may
be infinite — while a basis does not; and it is all that is used, because the argument only ever
pushes a convergent expansion through one functional at a time and never writes an element of `Ω`
out in coordinates.  `Crystalline.isCoordinateDual_coord` recovers the hypothesis of
`CoordinateOperatorsUnique.lean` from a basis, so nothing there is lost.

## Main definitions

Everything is in the namespace `Crystalline`.

* `Crystalline.completedTensorFunctionalLevel` — an arbitrary `D`-linear functional
  `M ⊗_D Ω → M`, read on the completion `M ⊗̂_D Ω` with values in `M ⧸ p^n M`.  This is
  `Crystalline.completedTensorCoordinateLevel` with the basis coordinate replaced by an arbitrary
  linear map; the continuity argument never looked at the basis.
* `Crystalline.IsCoordinateDual` — a family of `D`-linear functionals on `Ω` biorthogonal to the
  differentials `d x_i`.
* `Crystalline.dualTensorCoordinate` — the functional `M ⊗_D Ω → M`, `x ⊗ ω ↦ c(ω) · x`, induced
  by one such functional.

## Main results

* `Crystalline.continuous_completedTensorFunctionalLevel` — every `D`-linear functional is
  continuous when read modulo `p^n`, the target being discrete.
* `Crystalline.completedTensorFunctionalLevel_eq_of_hasSum` — the `j`-th coordinate of `∇(m)`
  modulo `p^n` is `θ_j(m)`, for every coordinate expansion `θ`, from a dual family alone.
* `Crystalline.eq_of_isCoordinateExpansion_of_isCoordinateDual` — **the coordinate operators are
  unique**, from a dual family and `p`-adic separatedness.
* `Crystalline.isIntegrable_of_isThetaMonomialFamily_of_isCoordinateDual` — **item (07JD)**.
* `Crystalline.isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily_of_isCoordinateDual` —
  **item (07JE)**.
* `Crystalline.isCoordinateDual_coord` — a `Module.Basis` of `Ω` on the differentials gives a dual
  family, so the statements of
  `StacksFrontier/AlgebraicGeometry/Crystalline/CoordinateOperatorsUnique.lean` are special cases of
  the ones here.

## What is and is not proved

No `@[stacks]` attribute is placed in this module.  The two items 07JD and 07JE are proved here in greater
generality than in `CoordinateOperatorsUnique.lean`, which carries the attribute for them, and
the hypotheses are the same except that the basis is replaced by the dual family it provides; the
remaining inputs — the monomial family `θ_K = ∏_i θ_i^{k_i}` that the source reads off `D(2)`, and
the `p`-adic convergence it reads off `D(1)` — are unchanged and are not derived here.

The dual family is **not** constructed here either: that `Ω_D` has one is
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDifferentialsDual.lean`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public section

open scoped TensorProduct

universe u v uI w

namespace Crystalline

/-! ### An arbitrary linear functional, read on the completion modulo `p^n` -/

section Functional

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M]

/-- **A `D`-linear functional `M ⊗_D Ω → M`, read on `M ⊗̂_D Ω` modulo `p^n`.**  The completion is
evaluated at level `n`, which lands in `(M ⊗_D Ω) ⧸ p^n (M ⊗_D Ω)`, and the functional is applied
there through `Crystalline.pLevelMapQ`.

This is `Crystalline.completedTensorCoordinateLevel` with the coordinate of a basis replaced by an
arbitrary linear map: the continuity argument of that module uses only linearity. -/
noncomputable def completedTensorFunctionalLevel (phi : (M ⊗[D] Omega) →ₗ[D] M) (n : ℕ) :
    CompletedTensor p D Omega M →ₗ[D] (M ⧸ pLevel p D M n) :=
  (pLevelMapQ p D (M ⊗[D] Omega) M phi n).comp
    (AdicCompletion.eval (DividedPowers.pAdicIdeal (A := D) p) (M ⊗[D] Omega) n)

/-- On the image of `z : M ⊗_D Ω` in the completion, the functional read modulo `p^n` is the
class of `phi z` in `M ⧸ p^n M`. -/
@[simp] theorem completedTensorFunctionalLevel_of (phi : (M ⊗[D] Omega) →ₗ[D] M) (n : ℕ)
    (z : M ⊗[D] Omega) :
    completedTensorFunctionalLevel p D Omega M phi n (toCompletedTensor p D Omega M z) =
      Submodule.Quotient.mk (p := pLevel p D M n) (phi z) := by
  show pLevelMapQ p D (M ⊗[D] Omega) M phi n
      (AdicCompletion.eval (DividedPowers.pAdicIdeal (A := D) p) (M ⊗[D] Omega) n
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := D) p) (M ⊗[D] Omega) z)) = _
  rw [AdicCompletion.eval_of]
  rfl

/-- **A `D`-linear functional read modulo `p^n` is continuous.**  The submodules `p^n • ⊤` are a
basis of neighbourhoods of `0` for the `p`-adic topology of the completion, a linear map carries
the filtration into the filtration, the target's own `p^n` is zero and the target is therefore
discrete; so continuity at `0` — hence continuity, the source being a topological additive
group — is that one membership.  Nothing about a basis of `Ω` enters. -/
theorem continuous_completedTensorFunctionalLevel (phi : (M ⊗[D] Omega) →ₗ[D] M) (n : ℕ) :
    letI := completedTensorTopology p D Omega M
    letI := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p)
      (M ⧸ pLevel p D M n)
    Continuous (completedTensorFunctionalLevel p D Omega M phi n) := by
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
    (completedTensorFunctionalLevel p D Omega M phi n) ?_
  have hmem : {x : CompletedTensor p D Omega M |
      completedTensorFunctionalLevel p D Omega M phi n x = 0} ∈
      nhds (0 : CompletedTensor p D Omega M) := by
    refine Filter.mem_of_superset (hopen.mem_nhds (Submodule.zero_mem _)) fun x hx ↦ ?_
    have h1 := map_mem_pow_smul_top_of_mem (DividedPowers.pAdicIdeal (A := D) p)
      (completedTensorFunctionalLevel p D Omega M phi n) n hx
    rw [show DividedPowers.pAdicIdeal (A := D) p ^ n •
      (⊤ : Submodule D (M ⧸ pLevel p D M n)) = ⊥ from pLevel_quotient_eq_bot p D M n,
      Submodule.mem_bot] at h1
    exact h1
  have hpure : nhds (completedTensorFunctionalLevel p D Omega M phi n 0) =
      pure (0 : M ⧸ pLevel p D M n) := by
    rw [map_zero, nhds_discrete]
  rw [ContinuousAt, hpure]
  exact Filter.tendsto_pure.mpr hmem

end Functional

/-! ### Coordinate functionals dual to the differentials -/

section Dual

variable {D : Type u} [CommRing D] {Omega : Type v} [AddCommGroup Omega] [Module D Omega]
  {ι : Type uI}

/-- **A family of coordinate functionals dual to the differentials.**  `D`-linear maps
`c_j : Ω → D` with `c_j (d x_i) = δ_{ij}`.

This is what the uniqueness of the coordinate operators of a completed connection runs on, and it
is strictly weaker than a `Module.Basis ι D Ω` on the `d x_i`: it asks for the functionals and not
for the expansion of a general element of `Ω`, so it is available for the completed direct sum
`Ω_D` of [Stacks, Tag 07J9] with an arbitrary, possibly infinite, family of coordinates, where a
basis is not. -/
structure IsCoordinateDual (dx : ι → Omega) (coord : ι → (Omega →ₗ[D] D)) : Prop where
  /-- The `i`-th functional takes the value `1` on the `i`-th differential. -/
  self : ∀ i, coord i (dx i) = 1
  /-- It vanishes on every other differential. -/
  of_ne : ∀ {i j : ι}, i ≠ j → coord j (dx i) = 0

/-- **A basis of `Ω` on the differentials gives a dual family**, namely its own coordinates.  So
every statement below applies in particular under the hypothesis `b` and `hdx` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CoordinateOperatorsUnique.lean`. -/
theorem isCoordinateDual_coord {dx : ι → Omega} (b : Module.Basis ι D Omega)
    (hdx : ∀ i, dx i = b i) : IsCoordinateDual dx (fun j ↦ b.coord j) where
  self i := by
    rw [hdx i, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  of_ne {i j} hij := by
    rw [hdx i, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne (Ne.symm hij)]

variable (M : Type w) [AddCommGroup M] [Module D M]

/-- **The functional `M ⊗_D Ω → M` induced by a functional on `Ω`**: `x ⊗ ω ↦ c(ω) · x`.  It is
`D`-linear, which is what lets it be read on the `p`-adic completion by
`Crystalline.completedTensorFunctionalLevel`. -/
noncomputable def dualTensorCoordinate (c : Omega →ₗ[D] D) : (M ⊗[D] Omega) →ₗ[D] M :=
  (TensorProduct.rid D M).toLinearMap.comp (LinearMap.lTensor M c)

/-- The functional induced by `c` sends `x ⊗ ω` to `c(ω) • x`. -/
@[simp] theorem dualTensorCoordinate_tmul (c : Omega →ₗ[D] D) (x : M) (omega : Omega) :
    dualTensorCoordinate M c (x ⊗ₜ[D] omega) = c omega • x := by
  rw [dualTensorCoordinate]
  simp

end Dual

/-! ### Uniqueness of the coordinate operators from a dual family -/

section Unique

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M] {ι : Type uI}
  {dx : ι → Omega} {dd : D → Omega} {nabla : CompletedConnection p D Omega dd M}

/-- **The `j`-th coordinate of `∇(m)` modulo `p^n` is `θ_j(m)`, for every coordinate expansion
`θ`.**  Pushing the convergent sum `∇ m = ∑_i θ_i(m) d x_i` through the continuous functional
`Crystalline.completedTensorFunctionalLevel` at `Crystalline.dualTensorCoordinate` of `c_j` leaves
the single term at `i = j`, and a sum with one nonzero term is that term.

This is where the dual family enters, and it is the only thing it is used for: without the
functionals the summands of a convergent sum are not determined by the sum. -/
theorem completedTensorFunctionalLevel_eq_of_hasSum {theta : ι → (M → M)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    {coord : ι → (Omega →ₗ[D] D)} (hc : IsCoordinateDual dx coord) (j : ι) (m : M) (n : ℕ) :
    completedTensorFunctionalLevel p D Omega M (dualTensorCoordinate M (coord j)) n (nabla m) =
      Submodule.Quotient.mk (p := pLevel p D M n) (theta j m) := by
  classical
  let := completedTensorTopology p D Omega M
  let := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p)
    (M ⧸ pLevel p D M n)
  have : DiscreteTopology (M ⧸ pLevel p D M n) :=
    discreteTopology_adicModuleTopology_of_eq_bot _ (M ⧸ pLevel p D M n)
      (pLevel_quotient_eq_bot p D M n)
  have hpush := (hco m).map
    (completedTensorFunctionalLevel p D Omega M (dualTensorCoordinate M (coord j)) n).toAddMonoidHom
    (continuous_completedTensorFunctionalLevel p D Omega M
      (dualTensorCoordinate M (coord j)) n)
  have hterm : ∀ i : ι,
      ((completedTensorFunctionalLevel p D Omega M
            (dualTensorCoordinate M (coord j)) n).toAddMonoidHom ∘
          fun i ↦ toCompletedTensor p D Omega M (theta i m ⊗ₜ[D] dx i)) i =
        if i = j then Submodule.Quotient.mk (p := pLevel p D M n) (theta j m) else 0 := by
    intro i
    show completedTensorFunctionalLevel p D Omega M (dualTensorCoordinate M (coord j)) n
        (toCompletedTensor p D Omega M (theta i m ⊗ₜ[D] dx i)) = _
    rw [completedTensorFunctionalLevel_of, dualTensorCoordinate_tmul]
    by_cases hij : i = j
    · subst hij
      rw [hc.self i, one_smul, if_pos rfl]
    · rw [hc.of_ne hij, zero_smul, if_neg hij]
      exact (pLevel p D M n).mkQ.map_zero
  rw [funext hterm] at hpush
  exact (hasSum_ite_eq j (Submodule.Quotient.mk (p := pLevel p D M n)
    (theta j m))).unique hpush |>.symm

/-- **The coordinate operators of a completed connection are unique**, from a dual family of
coordinate functionals and `p`-adic separatedness of the module.

This is `Crystalline.eq_of_isCoordinateExpansion` with the `Module.Basis` of `Ω` replaced by the
biorthogonal functionals it provides, which is all the argument uses.  The second hypothesis is
the Hausdorff half of item (07JB) of [Stacks, Lemma 60.17.3, Tag 07JG], unchanged. -/
theorem eq_of_isCoordinateExpansion_of_isCoordinateDual {theta theta' : ι → (M → M)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    (hco' : IsCoordinateExpansion p D Omega dx nabla theta')
    {coord : ι → (Omega →ₗ[D] D)} (hc : IsCoordinateDual dx coord)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) M) :
    theta = theta' := by
  classical
  funext j m
  refine hM.haus' (theta j m - theta' j m) (fun n ↦ ?_) |> sub_eq_zero.mp
  rw [SModEq.zero]
  have h := (completedTensorFunctionalLevel_eq_of_hasSum p D Omega M hco hc j m n).symm.trans
    (completedTensorFunctionalLevel_eq_of_hasSum p D Omega M hco' hc j m n)
  rw [Submodule.Quotient.eq] at h
  exact h

end Unique

/-! ### Items (07JD) and (07JE) from a dual family -/

section Items

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M] {ι : Type uI}
  {dx : ι → Omega} {dd : D → Omega} {nabla : CompletedConnection p D Omega dd M}
  {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}

/-- **Item (07JD) of [Stacks, Lemma 60.17.3, Tag 07JG]: the connection is integrable**, from a
dual family of coordinate functionals in place of a basis of `Ω`.

The carried operators commute by `Crystalline.IsThetaMonomialFamily.comm`, the source's
"`θ_i ∘ θ_j = θ_j ∘ θ_i`" read off `θ_K = ∏_i θ_i^{k_i}`, and by
`Crystalline.eq_of_isCoordinateExpansion_of_isCoordinateDual` there is no other family of
coordinate operators to check.  `Crystalline.IsIntegrable` is the predicate unchanged: it still
quantifies over every coordinate expansion of `∇`. -/
theorem isIntegrable_of_isThetaMonomialFamily_of_isCoordinateDual
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    {coord : ι → (Omega →ₗ[D] D)} (hc : IsCoordinateDual dx coord)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) M) :
    IsIntegrable p D Omega dx nabla := by
  intro theta' hco' i j
  rw [eq_of_isCoordinateExpansion_of_isCoordinateDual p D Omega M hco' hco hc hM]
  exact hfamM.comm i j

/-- **Item (07JE) of [Stacks, Lemma 60.17.3, Tag 07JG]: the connection is topologically
quasi-nilpotent**, from a dual family of coordinate functionals in place of a basis of `Ω`.

The pairs `(i, k)` with `k ≠ 0` inject into the multi-indices by `K = k · e_i`, along which
`θ_i^k = θ_{k · e_i}` by `Crystalline.IsThetaMonomialFamily.single`, so the carried finiteness of
`{K : θ_K(m) ∉ p M}` — the source's `p`-adic convergence of the expansion over `D(1)` — bounds
them; and uniqueness of the coordinate operators removes the quantifier. -/
theorem isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily_of_isCoordinateDual
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hco : IsCoordinateExpansion p D Omega dx nabla theta)
    {coord : ι → (Omega →ₗ[D] D)} (hc : IsCoordinateDual dx coord)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) M)
    (hfin : ∀ m : M, {K : ι →₀ ℕ | thetaPow K m ∉ pSmul p D M}.Finite) :
    IsTopologicallyQuasiNilpotent p D Omega dx nabla := by
  classical
  intro theta' hco' m
  rw [eq_of_isCoordinateExpansion_of_isCoordinateDual p D Omega M hco' hco hc hM]
  refine Set.Finite.of_finite_image
    (f := fun q : ι × ℕ ↦ Finsupp.single q.1 q.2) ((hfin m).subset ?_) ?_
  · rintro K ⟨q, ⟨-, hq⟩, rfl⟩
    rw [Set.mem_setOf_eq, hfamM.single q.1 q.2]
    exact hq
  · rintro ⟨i, k⟩ ⟨hk, -⟩ ⟨i', k'⟩ ⟨hk', -⟩ hsingle
    rcases (Finsupp.single_eq_single_iff i i' k k').mp hsingle with ⟨rfl, rfl⟩ | ⟨h0, -⟩
    · rfl
    · exact absurd h0 hk

end Items

end Crystalline

end
