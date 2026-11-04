module

public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptional
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.ResidualFactorization

/-!
# Finite support of the residual ideal on the blowup of a regular surface

Let `(A, 𝔪)` be a two-dimensional regular local ring, let `b : X' ⟶ Spec A` be the blowup at the
closed point with exceptional ideal `E`, and let `J` be an ideal sheaf on `Spec A` with
`𝔪ⁿ ≤ J`. Write `b⁻¹J·𝒪_{X'} = E ^ d · Z` with `d` maximal. Then `Z` is supported at finitely
many closed points. This is clause (2) of [Stacks, Tag 0AGT].

The argument has three steps.

* The support of `Z` sits inside the support of `E`: the product `E ^ d · Z` is below `Z`, so
  `supp Z ⊆ supp(b⁻¹J·𝒪_{X'}) = b⁻¹(supp J) ⊆ b⁻¹(supp 𝔪) = supp E`.
* The support of `Z` is **strictly** inside the support of `E`. Were the two equal, `Z` and `E`
  would have the same radical; `E` is radical
  (`AlgebraicGeometry.radical_exceptionalIdeal_maximalIdeal`), so `Z ≤ E` and therefore
  `b⁻¹J·𝒪_{X'} = E ^ d · Z ≤ E ^ (d + 1)`, contradicting maximality of `d`. **This is the step
  that needs the exceptional divisor to be irreducible with a single generic point**: without it
  "the generic point of `E` is outside `supp Z`" is not available, and the support could meet
  every component of `E` without being all of it.
* A proper closed subset of an irreducible one-dimensional Noetherian sober space is a finite set
  of closed points — `Stacks.Topology.Dimension.finite_of_isClosed_of_ne_univ`. The exceptional
  divisor is irreducible by `AlgebraicGeometry.irreducibleSpace_exceptionalDivisor_maximalIdeal`
  and one-dimensional by
  `AlgebraicGeometry.topologicalKrullDim_exceptionalDivisor_residuePoint`.

## Main results

* `AlgebraicGeometry.finite_supportSet_of_subset_support_of_ne`: a closed subset strictly inside
  the support of an irreducible one-dimensional closed subscheme is a finite set of closed
  points, stated for the support of an ideal sheaf.
* `AlgebraicGeometry.finite_supportSet_of_eq_exceptionalIdeal_pow_mul`: the gluing, for an
  abstract divisor `E` that is irreducible, one-dimensional and radical.
* `AlgebraicGeometry.finite_supportSet_residual_maximalIdeal`: **clause (2) of
  [Stacks, Tag 0AGT]** for the blowup of a two-dimensional regular local ring at its closed
  point.

## Implementation notes

The second factor is taken as given, with the factorization `b⁻¹J·𝒪_{X'} = E ^ d · Z` as a
hypothesis, rather than constructed as a colon ideal: existence and uniqueness of that factor are
`AlgebraicGeometry.exists_comap_eq_exceptionalIdeal_pow_mul` and
`Stacks.BlowUpChartCover.existsUnique_comap_eq_exceptionalIdeal_pow_mul`, so nothing is lost and
the statement is about whichever construction a consumer has in hand.

The source's other bound `J ≤ 𝔪` is **not** assumed: only `𝔪ⁿ ≤ J` is used, and that only to
place `supp J` inside the closed point. Assuming less makes the statement stronger.

The topology happens inside the closed subscheme `E.subscheme`, where the dimension and
irreducibility statements live, and is transported back to the blowup along `subschemeι`, which
is a closed immersion (`AlgebraicGeometry.IsClosedImmersion`), so it carries closed sets to
closed sets and its range is exactly the support.

The finite-support half of clause (2) is registered on its own carrier here,
`AlgebraicGeometry.finite_supportSet_residual_maximalIdeal`, alongside the other members of the
covering set: `Stacks.Blowup.Colength.pos_order_of_le_center` for clause (1),
`Stacks.Blowup.Colength.exists_exceptionalIdeal_pow_mul_eq_comap` for the splitting half of
clause (2), and
`Stacks.Blowup.Colength.length_globalSections_ge_sum_length_stalkQuotient` for the second, `≥`,
inequality of clause (3). The first, strict, inequality of clause (3) is still not reached, so
the covering set is not yet complete; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Blowup/Colength/PositiveOrder.lean`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Finiteness inside a one-dimensional irreducible closed subscheme -/

/-- **A closed subset strictly inside an irreducible one-dimensional closed subscheme is a finite
set of closed points.** Here both the subscheme and the subset are presented as supports of ideal
sheaves `E` and `Z`.

The statement is proved inside `E.subscheme`, where
`Stacks.Topology.Dimension.finite_of_isClosed_of_ne_univ` applies, and transported along the
closed immersion `E.subschemeι`, whose range is `supp E`. -/
public theorem finite_supportSet_of_subset_support_of_ne {Y : Scheme.{u}} [IsNoetherian Y]
    (E Z : Y.IdealSheafData) (hirr : IrreducibleSpace E.subscheme)
    (hdim : topologicalKrullDim E.subscheme ≤ 1)
    (hsub : Z.supportSet ⊆ E.supportSet) (hne : Z.supportSet ≠ E.supportSet) :
    Z.supportSet.Finite ∧ ∀ z ∈ Z.supportSet, IsClosed ({z} : Set Y) := by
  have := hirr
  have : IsNoetherian E.subscheme := StacksTag09NX.isNoetherian_subscheme E
  have hrange : Set.range E.subschemeι.base = E.supportSet := E.range_subschemeι
  have hTc : IsClosed (E.subschemeι.base ⁻¹' Z.supportSet) :=
    Z.isClosed_supportSet.preimage E.subschemeι.base.hom.continuous
  have himg : E.subschemeι.base '' (E.subschemeι.base ⁻¹' Z.supportSet) = Z.supportSet := by
    rw [Set.image_preimage_eq_inter_range, hrange, Set.inter_eq_left]
    exact hsub
  have hTne : E.subschemeι.base ⁻¹' Z.supportSet ≠ Set.univ := by
    intro h
    refine hne ?_
    rw [← himg, h, Set.image_univ, hrange]
  refine ⟨?_, ?_⟩
  · rw [← himg]
    exact (Stacks.Topology.Dimension.finite_of_isClosed_of_ne_univ hdim hTc hTne).image _
  · intro z hz
    rw [← himg] at hz
    obtain ⟨t, htT, rfl⟩ := hz
    have hts :=
      Stacks.Topology.Dimension.isClosed_singleton_of_mem_of_ne_univ hdim hTc hTne htT
    simpa using E.subschemeι.isClosedEmbedding.isClosedMap _ hts

/-! ### The residual factor of an inverse image -/

/-- **Finiteness of the support of the residual factor.** Let `E` be an ideal sheaf whose
subscheme is irreducible of dimension at most one and which is radical, and suppose an ideal
sheaf `W` supported inside `supp E` factors as `W = E ^ d · Z` with `d` maximal among the
exponents `e` with `W ≤ E ^ e`. Then `Z` is supported at finitely many closed points.

Maximality is used exactly once: it rules out `Z ≤ E`, which by radicality of `E` is the same as
`supp Z = supp E`, so the support of `Z` is a *proper* closed subset of the support of `E`. -/
public theorem finite_supportSet_of_eq_exceptionalIdeal_pow_mul {Y : Scheme.{u}} [IsNoetherian Y]
    (E Z W : Y.IdealSheafData) (d : ℕ) (hirr : IrreducibleSpace E.subscheme)
    (hdim : topologicalKrullDim E.subscheme ≤ 1) (hErad : E.radical = E)
    (hfac : W = E ^ d * Z) (hmax : ∀ e : ℕ, W ≤ E ^ e → e ≤ d)
    (hWsub : W.supportSet ⊆ E.supportSet) :
    Z.supportSet.Finite ∧ ∀ z ∈ Z.supportSet, IsClosed ({z} : Set Y) := by
  -- the residual factor is above the product, so its support is inside that of `E`
  have hWZ : W ≤ Z := by
    intro U
    rw [hfac]
    show (E.ideal U) ^ d * Z.ideal U ≤ Z.ideal U
    exact Ideal.mul_le_right
  have hsub : Z.supportSet ⊆ E.supportSet :=
    fun z hz => hWsub (Scheme.IdealSheafData.support_antitone hWZ hz)
  refine finite_supportSet_of_subset_support_of_ne E Z hirr hdim hsub fun heq => ?_
  -- equal supports would make `Z` smaller than `E`, so `d` was not maximal
  have hZE : Z ≤ E :=
    calc Z ≤ Z.radical := Scheme.IdealSheafData.le_radical _
      _ = Scheme.IdealSheafData.vanishingIdeal Z.support :=
          Scheme.IdealSheafData.vanishingIdeal_support.symm
      _ = Scheme.IdealSheafData.vanishingIdeal E.support := by
          rw [show Z.support = E.support from TopologicalSpace.Closeds.ext heq]
      _ = E.radical := Scheme.IdealSheafData.vanishingIdeal_support
      _ = E := hErad
  have hle : W ≤ E ^ (d + 1) := by
    intro U
    rw [hfac]
    show (E.ideal U) ^ d * Z.ideal U ≤ (E.ideal U) ^ (d + 1)
    rw [pow_succ]
    exact Ideal.mul_mono le_rfl (hZE U)
  exact absurd (hmax (d + 1) hle) (by omega)

/-! ### Clause (2) of Tag 0AGT -/

/-- **Clause (2) of [Stacks, Tag 0AGT].** Let `A` be a two-dimensional regular local ring, `M` the
ideal sheaf of its closed point, and `b : X' ⟶ Spec A` the blowup in `M`. Let `J` be an ideal
sheaf with `M ^ n ≤ J`, and suppose the inverse image `b⁻¹J·𝒪_{X'}` factors as `E ^ d · Z` with
`E` the exceptional ideal and `d` maximal among the exponents `e` with `b⁻¹J·𝒪_{X'} ≤ E ^ e`.
Then `Z` is supported at finitely many closed points of the blowup. -/
@[stacks 0AGT "clause (2), the finite support: the residual factor left by dividing out the \
exceptional divisor is supported at finitely many closed points of the blowup"]
public theorem finite_supportSet_residual_maximalIdeal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (M : (Spec (CommRingCat.of A)).IdealSheafData)
    (hM : M = Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A)))
    (J : (Spec (CommRingCat.of A)).IdealSheafData) (n : ℕ) (hmn : M ^ n ≤ J)
    (d : ℕ) (Z : (blowUp M).IdealSheafData)
    (hfac : J.comap (blowUpToBase M) = exceptionalIdeal M ^ d * Z)
    (hmax : ∀ e : ℕ, J.comap (blowUpToBase M) ≤ exceptionalIdeal M ^ e → e ≤ d) :
    Z.supportSet.Finite ∧ ∀ z ∈ Z.supportSet, IsClosed ({z} : Set (blowUp M)) := by
  subst hM
  set M := Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (maximalIdeal A))
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsNoetherian (blowUp M) := Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _
  -- the exceptional divisor is irreducible of dimension one
  have hirr := irreducibleSpace_exceptionalDivisor_maximalIdeal A hdim
  have hdim1 : topologicalKrullDim (exceptionalDivisor M) ≤ 1 := by
    have h := topologicalKrullDim_exceptionalDivisor_residuePoint A hdim
    rw [ker_residuePoint_eq_ofIdealTop_map] at h
    exact le_of_eq h
  -- the support of the inverse image lies over the closed point, hence inside the divisor
  have hJM : J.support ≤ M.support := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero] at hmn
      rw [top_le_iff.mp hmn, Scheme.IdealSheafData.support_top]
      exact bot_le
    · have h := Scheme.IdealSheafData.support_antitone hmn
      rwa [Scheme.IdealSheafData.support_pow _ n hn.ne'] at h
  have hWsub : (J.comap (blowUpToBase M)).support ≤ (exceptionalIdeal M).support := by
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    exact fun z hz => hJM hz
  exact finite_supportSet_of_eq_exceptionalIdeal_pow_mul _ _ _ d hirr hdim1
    (radical_exceptionalIdeal_maximalIdeal A hdim) hfac hmax fun z hz => hWsub hz

end AlgebraicGeometry

end
