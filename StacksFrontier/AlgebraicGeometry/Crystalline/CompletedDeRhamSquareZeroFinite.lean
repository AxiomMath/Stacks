module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsUnique

/-!
# `IsSquareZero` for a pair over finitely many coordinates

`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamSquareZero.lean` derives
`Crystalline.CompletedDeRham.IsSquareZero` — that the completed de Rham differentials of a module
with a connection compose to zero — from integrability [Stacks, Tag 07JD], the exterior
properties `Crystalline.CompletedDeRham.IsGradedExterior` of the carried forms, closedness of the
coordinate differentials, and a **finite** coordinate expansion
`Crystalline.CompletedDeRham.IsFiniteCoordinateExpansion` of the connection.

A `Crystalline.Pair` carries integrability outright, in the field `Crystalline.Pair.isIntegrable`,
and carries a coordinate expansion in the field `Crystalline.Pair.hasCoordinateOperators` — but in
the `HasSum` form `Crystalline.IsCoordinateExpansion`, not the finite form.  This module closes
that last step **when the coordinates are finite in number**, which is the case of
[Stacks, Lemma 60.17.3, Tag 07JG]: there `D` is the divided power envelope of a polynomial
algebra on the chosen presentation and the coordinates are its variables, and the assembly
`...SmallSite.reduction07JGWholeSpaceOfLevelwise` of that datum already requires `[Fintype ι]`.

So for a pair over a finite coordinate family, `IsSquareZero` is a **theorem** and not a
hypothesis: `Crystalline.Pair.isSquareZero`.

## How the finite expansion is obtained

`Crystalline.IsCoordinateExpansion` is a `HasSum` in the `p`-adic topology of `M ⊗̂_D Ω`, and
over a finite index type `Crystalline.hasSum_fintype` gives the finite sum as *a* sum of the same
family; the two agree only if limits are unique, that is if the topology is Hausdorff.  The
`p`-adic topology of the completion is **not** known to be Hausdorff by
`Crystalline.t2Space_pAdic_of_pow_eq_zero`, whose hypothesis `p^N = 0` fails in the completed
envelope — the completion exists precisely because `p` is not nilpotent there.

The step is therefore taken one level at a time.  Each level evaluation
`AdicCompletion.eval` of the completion lands in `(M ⊗_D Ω) ⧸ p^n (M ⊗_D Ω)`, whose `p`-adic
topology **is** discrete, because `p^n` annihilates it; it is continuous, because a linear map
carries the filtration into the filtration and the target's `p^n` level is `⊥`; and a discrete
topology is Hausdorff.  So the two sums agree at every level, and
`AdicCompletion.ext` assembles that into the equality of the sums themselves.  No completeness or
Hausdorffness of `M ⊗̂_D Ω` is used.

## Main results

* `Crystalline.pow_smul_top_quotient_eq_bot` — `I^n` annihilates `N ⧸ I^n N`, the generic form of
  `Crystalline.pLevel_quotient_eq_bot`.
* `Crystalline.continuous_adicCompletion_eval` — **the level evaluation of an adic completion is
  continuous** for the adic module topologies.
* `Crystalline.isFiniteCoordinateExpansion_univ_of_isCoordinateExpansion` — **over a finite index
  type a coordinate expansion is a finite coordinate expansion**, over `Finset.univ`.
* `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable_of_fintype` —
  `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` with the finite expansion replaced
  by a plain one.
* `Crystalline.Pair.isSquareZero` — **the de Rham differentials of a pair over finitely many
  coordinates compose to zero**, from the pair's own integrability and coordinate operators
  together with the exterior properties of the forms.

## What is and is not proved

**No `@[stacks]` attribute is placed here and no tag is proved.**  What is removed is the gap
between the two spellings of a coordinate expansion over a finite index type; integrability
[Stacks, Tag 07JD] is not proved here but taken from the pair, and the exterior properties of the
forms remain hypotheses because the family of forms is a carried parameter — they hold for the
genuine divided power forms of [Stacks, Tag 07HZ].

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public section

open DividedPowers
open scoped TensorProduct

universe u v w uI

namespace Crystalline

/-! ### The level evaluation of an adic completion is continuous -/

section Eval

variable {R : Type u} [CommRing R] (I : Ideal R) (N : Type w) [AddCommGroup N] [Module R N]

/-- **`I^n` annihilates `N ⧸ I^n N`.**  The image of `I^n • ⊤` under the quotient map is zero and
the image of `⊤` is `⊤`, so `I^n • ⊤` in the quotient is `⊥`.  This is the generic form of
`Crystalline.pLevel_quotient_eq_bot`, and it is what makes the `p`-adic topology of the quotient
discrete. -/
theorem pow_smul_top_quotient_eq_bot (n : ℕ) :
    I ^ n • (⊤ : Submodule R (N ⧸ (I ^ n • ⊤ : Submodule R N))) = ⊥ := by
  have hmap := Submodule.map_smul'' (I ^ n) (⊤ : Submodule R N)
    (I ^ n • (⊤ : Submodule R N)).mkQ
  rw [Submodule.mkQ_map_self, Submodule.map_top, Submodule.range_mkQ] at hmap
  exact hmap.symm

/-- **The `p`-adic topology of `N ⧸ I^n N` is discrete.** -/
theorem discreteTopology_quotient_pow_smul_top (n : ℕ) :
    @DiscreteTopology (N ⧸ (I ^ n • ⊤ : Submodule R N))
      (Ideal.adicModuleTopology I (N ⧸ (I ^ n • ⊤ : Submodule R N))) :=
  discreteTopology_adicModuleTopology_of_eq_bot I _ (pow_smul_top_quotient_eq_bot I N n)

/-- **The level-`n` evaluation `N^∧ ⟶ N ⧸ I^n N` of an adic completion is continuous** for the
adic module topologies on the two sides.

The submodules `I^k • ⊤` are a basis of neighbourhoods of `0` in the completion, each of them
open; the evaluation carries `I^n • ⊤` into `I^n • ⊤` of the target, which is `⊥` by
`Crystalline.pow_smul_top_quotient_eq_bot`; and the target is discrete.  So the map is continuous
at `0`, and the source being a topological additive group it is continuous. -/
theorem continuous_adicCompletion_eval (n : ℕ) :
    letI := Ideal.adicModuleTopology I (AdicCompletion I N)
    letI := Ideal.adicModuleTopology I (N ⧸ (I ^ n • ⊤ : Submodule R N))
    Continuous (AdicCompletion.eval I N n) := by
  let := I.adicTopology
  let := Ideal.adicModuleTopology I (AdicCompletion I N)
  let := Ideal.adicModuleTopology I (N ⧸ (I ^ n • ⊤ : Submodule R N))
  have hbas := I.ringFilterBasis.submodulesBasisIsBasis (I.adic_module_basis (AdicCompletion I N))
  have : IsTopologicalAddGroup (AdicCompletion I N) :=
    hbas.toModuleFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
  have : DiscreteTopology (N ⧸ (I ^ n • ⊤ : Submodule R N)) :=
    discreteTopology_quotient_pow_smul_top I N n
  have hopen : IsOpen ((I ^ n • (⊤ : Submodule R (AdicCompletion I N)) :
      Submodule R (AdicCompletion I N)) : Set (AdicCompletion I N)) :=
    (SubmodulesBasis.openAddSubgroup hbas n).isOpen'
  refine continuous_of_continuousAt_zero (AdicCompletion.eval I N n) ?_
  have hmem : {x : AdicCompletion I N | AdicCompletion.eval I N n x = 0} ∈
      nhds (0 : AdicCompletion I N) := by
    refine Filter.mem_of_superset (hopen.mem_nhds (Submodule.zero_mem _)) fun x hx ↦ ?_
    have h1 := map_mem_pow_smul_top_of_mem I (AdicCompletion.eval I N n) n hx
    rw [pow_smul_top_quotient_eq_bot I N n, Submodule.mem_bot] at h1
    exact h1
  have hpure : nhds (AdicCompletion.eval I N n 0) = pure (0 : N ⧸ (I ^ n • ⊤ : Submodule R N)) := by
    rw [map_zero, nhds_discrete]
  rw [ContinuousAt, hpure]
  exact Filter.tendsto_pure.mpr hmem

end Eval

/-! ### A coordinate expansion over a finite index type is a finite coordinate expansion -/

section Finite

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] {M : Type w} [AddCommGroup M] [Module D M] {ι : Type uI}

/-- **Over a finite index type a coordinate expansion is a finite coordinate expansion**, taken
over the whole of `Finset.univ`.

`Crystalline.IsCoordinateExpansion` is a `HasSum` in the `p`-adic topology of `M ⊗̂_D Ω`, which is
not known to be Hausdorff — the completed envelope has `p` non-nilpotent — so the sum cannot be
identified with the finite sum there directly.  It is identified level by level: each level
evaluation of the completion is continuous by
`Crystalline.continuous_adicCompletion_eval` and lands in a discrete, hence Hausdorff, quotient,
so the two sums agree at every level, and `AdicCompletion.ext` concludes. -/
theorem isFiniteCoordinateExpansion_univ_of_isCoordinateExpansion [Fintype ι] {dx : ι → Omega}
    {dmap : D → Omega} {nabla : CompletedConnection p D Omega dmap M} {theta : ι → (M → M)}
    (hco : IsCoordinateExpansion p D Omega dx nabla theta) :
    CompletedDeRham.IsFiniteCoordinateExpansion p D Omega dx nabla theta Finset.univ where
  sum_eq m := by
    classical
    refine AdicCompletion.ext fun n ↦ ?_
    let := completedTensorTopology p D Omega M
    let := Ideal.adicModuleTopology (pAdicIdeal (A := D) p)
      ((M ⊗[D] Omega) ⧸ (pAdicIdeal (A := D) p ^ n • ⊤ : Submodule D (M ⊗[D] Omega)))
    have : DiscreteTopology ((M ⊗[D] Omega) ⧸
        (pAdicIdeal (A := D) p ^ n • ⊤ : Submodule D (M ⊗[D] Omega))) :=
      discreteTopology_quotient_pow_smul_top (pAdicIdeal (A := D) p) (M ⊗[D] Omega) n
    have hpush := (hco m).map
      (AdicCompletion.eval (pAdicIdeal (A := D) p) (M ⊗[D] Omega) n).toAddMonoidHom
      (continuous_adicCompletion_eval (pAdicIdeal (A := D) p) (M ⊗[D] Omega) n)
    have heq := hpush.unique (hasSum_fintype _)
    simp only [Function.comp_apply, LinearMap.toAddMonoidHom_coe] at heq
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, map_sum]
    exact heq
  eq_zero_of_notMem j hj := absurd (Finset.mem_univ j) hj

end Finite

/-! ### `IsSquareZero` from integrability alone, over finitely many coordinates -/

namespace CompletedDeRham

section SquareZero

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap) {ι : Type uI} [Fintype ι] (dx : ι → Om 1)
  (theta : ι → (M → M))

/-- **`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` with the finite coordinate
expansion replaced by a plain one**, the index type being finite.  The finite expansion is
supplied by `Crystalline.isFiniteCoordinateExpansion_univ_of_isCoordinateExpansion`. -/
theorem isSquareZero_of_isIntegrable_of_fintype (hext : IsGradedExterior D Om wedge deRham)
    (hco : IsCoordinateExpansion p D (Om 1) dx nabla theta)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (hint : IsIntegrable p D (Om 1) dx nabla) :
    IsSquareZero p D Om wedge deRham M nabla hleib :=
  isSquareZero_of_isIntegrable p D Om wedge deRham M nabla hleib dx theta Finset.univ hext
    (isFiniteCoordinateExpansion_univ_of_isCoordinateExpansion p D (Om 1) hco) hdx hint

end SquareZero

end CompletedDeRham

/-! ### The de Rham differentials of a pair compose to zero -/

section Pair

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1}
  (hleib : CompletedDeRham.IsGradedLeibniz D Om wedge deRham dmap) {ι : Type uI} [Fintype ι]
  (dx : ι → Om 1)

/-- **The completed de Rham differentials of a pair over finitely many coordinates compose to
zero.**

Both inputs of `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable_of_fintype` beyond the
forms are fields of the pair: `Crystalline.Pair.hasCoordinateOperators` gives the coordinate
expansion and `Crystalline.Pair.isIntegrable` is integrability, [Stacks, Tag 07JD].  What remains
carried is the pair of properties of the *forms* — `Crystalline.CompletedDeRham.IsGradedExterior`
and closedness of the coordinate differentials — which hold for the divided power forms of
[Stacks, Tag 07HZ] and are hypotheses only because the family of forms is a carried parameter.

This is what makes the hypothesis `hsq` of the double complex of
[Stacks, Proposition 60.21.3, Tag 07LG] a theorem rather than an assumption about the crystal:
`hsq` is this statement at the pair the functor of [Stacks, Lemma 60.17.3, Tag 07JG] produces,
and that pair, like every pair, carries its own integrability. -/
theorem Pair.isSquareZero (P : Pair p D (Om 1) dx dmap)
    (hext : CompletedDeRham.IsGradedExterior D Om wedge deRham)
    (hdx : ∀ j, deRham 1 (dx j) = 0) :
    CompletedDeRham.IsSquareZero p D Om wedge deRham P.carrier P.nabla hleib := by
  obtain ⟨theta, hco⟩ := P.hasCoordinateOperators
  exact CompletedDeRham.isSquareZero_of_isIntegrable_of_fintype p D Om wedge deRham P.carrier
    P.nabla hleib dx theta hext hco hdx P.isIntegrable

end Pair

end Crystalline

end
