module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Extension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Specialization
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField

/-!
# Stacks Tag 0BXW: the projective completion of a reduced curve has discrete valuation boundary

[Stacks, Tag 0BXW] says that a *reduced* separated scheme `X` of finite type over a field `k`
with `dim(X) ≤ 1` admits an open immersion `j : X ⟶ X'` with

1. `X'` H-projective over `k`, i.e. a closed subscheme of `ℙᵈ_k` for some `d`;
2. `j(X) ⊆ X'` dense and scheme-theoretically dense;
3. `X' \ X = {x₁, …, xₙ}` a finite set of closed points of `X'`;
4. the local rings `𝒪_{X', xᵢ}` discrete valuation rings.

The source's proof takes the completion `X ⟶ X̄` of [Stacks, Tag 0BXV] and replaces `X̄` by the
normalization `X'` of `X̄` in `X`. That normalization is finite over `X̄` by [Stacks, Tag 0BXS],
hence projective by [Stacks, Tag 0B3I], hence H-projective by [Stacks, Tag 087S], hence
H-projective over `k` by [Stacks, Tag 01WE]; the points of `X'` above the boundary of `X̄` have
one-dimensional local rings, so those local rings are discrete valuation rings by
[Stacks, Tag 0BXB].

## Main results

* `Stacks.CurveProjectiveCompletion.ringKrullDim_stalk_eq_one_of_notMem_genericPoints`: on a
  scheme of dimension at most one locally of finite type over a field, the local ring at a point
  which is not a generic point of an irreducible component has Krull dimension exactly one. This
  is the step "`dim(𝒪_{X', x'ᵢ}) = 1`" of the source's proof.
* `Stacks.CurveProjectiveCompletion.isHQuasiProjective_of_isReduced`: [Stacks, Tag 0A25] for a
  reduced scheme.
* `Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced`:
  **[Stacks, Tag 0BXW]**.
* `Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation`:
  the same statement with an additional, unused hypothesis `h09NZ`.

## Implementation notes

The first step of the proof is [Stacks, Tag 0A25]. Since `X` is reduced, the ample invertible
sheaf it needs is supplied by the reduced case [Stacks, Tag 09NX],
`Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one`,
rather than by [Stacks, Tag 09NZ].

**Clause (1) does not use [Stacks, Tag 0B3I] or [Stacks, Tag 087S]**, because the base `Spec k`
is affine. Let `i : X̄ ⟶ ℙⁿ_k` be the closed immersion of [Stacks, Tag 0BXV] and `ν : X' ⟶ X̄`
the normalization. Then:

* `ν ≫ i` is an affine morphism — `ν` is finite and `i` is a closed immersion — so the pullback
  along it of the hyperplane sheaf `𝒪(1)` of `ℙⁿ_k`, which is ample because `Spec k` is affine
  (`Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf`), is an ample invertible module
  on `X'` by [Stacks, Tag 0B3E] for an affine morphism
  (`Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`).
* `X' ⟶ Spec k` is of finite type, so [Stacks, Tag 01VS] in the form
  `AlgebraicGeometry.isHQuasiProjective_of_exists_isAmple` makes it H-quasi-projective.
* `X' ⟶ Spec k` is proper, being a finite morphism followed by an H-projective one.
* Clause (2) of [Stacks, Tag 0BCL],
  `AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper`, turns
  H-quasi-projective plus proper into H-projective.

This replaces the chain Tag 0B3I → Tag 087S(1) → Tag 01WE by Tag 0B3E → Tag 01VS → Tag 0BCL(2).
It is the same mathematics read in the opposite order: rather than make the finite morphism `ν`
projective over `X̄` and compose, it makes `X'` directly a closed subscheme of a projective space
over `k`.

**The dimension bound on `X'`** comes from the open immersion `X ⟶ X'`, not from a comparison
along `ν`. Both `X` and `X'` are locally of finite type over `k` and `X` is dense in `X'`, so
`Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion` gives
`dim(X') ≤ dim(X) ≤ 1` with no reference to `X̄`.

**Scheme-theoretic density** uses that `X'` is reduced — the normalization of a reduced scheme is
reduced — so the dense open `X` is scheme-theoretically dense: a dominant morphism out of a
reduced scheme is scheme-theoretically dominant.

**Clause (4) is spelled with the domain structure bundled**, as
`∃ _ : IsDomain (𝒪_{X',y}), IsDiscreteValuationRing (𝒪_{X',y})`, because
`IsDiscreteValuationRing` cannot be stated without an `IsDomain` instance.

## References

* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
* [Stacks Project, Tag 0BXV](https://stacks.math.columbia.edu/tag/0BXV)
* [Stacks Project, Tag 0A25](https://stacks.math.columbia.edu/tag/0A25)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 0BXS](https://stacks.math.columbia.edu/tag/0BXS)
* [Stacks Project, Tag 0BXB](https://stacks.math.columbia.edu/tag/0BXB)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.CurveProjectiveCompletion

/-! ### The local ring at a point which is not generic -/

/-- **On a scheme of dimension at most one locally of finite type over a field, the local ring at
a point outside a set containing all the generic points has Krull dimension one.**

Some generic point `η` specializes to the given point `z`, and `η ≠ z` because `z` is outside the
set; a nontrivial specialization strictly raises the Krull dimension of the local ring
([Stacks, Tag 0A21]), so that dimension is positive, and it is at most the dimension of the whole
scheme. -/
theorem ringKrullDim_stalk_eq_one_of_notMem_genericPoints (k : Type u) [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (hdim : topologicalKrullDim (Z : Type u) ≤ 1) {U : Set Z}
    (hgeneric : genericPoints Z ⊆ U) {z : Z} (hz : z ∉ U) :
    ringKrullDim (Z.presheaf.stalk z) = 1 := by
  obtain ⟨η, hηz, hηU⟩ := exists_specializes_mem_of_genericPoints_subset hgeneric z
  have hne : η ≠ z := fun h => hz (h ▸ hηU)
  have hlt := krullDimOfRing_stalk_lt_of_specialization k Z g hηz hne
  have hle : ringKrullDim (Z.presheaf.stalk z) ≤ 1 :=
    (Stacks.AlgebraicGeometry.NormalizationQuotient.ringKrullDim_stalk_le_topologicalKrullDim
      Z z).trans hdim
  have hpos : 0 < ringKrullDim (Z.presheaf.stalk z) :=
    lt_of_le_of_lt (ringKrullDim_nonneg_of_nontrivial) hlt
  cases hd : ringKrullDim (Z.presheaf.stalk z) with
  | bot => simp [hd] at hpos
  | coe d =>
    cases d with
    | top =>
      have hfalse : (1 : WithBot ℕ∞) = ⊤ := by simpa [hd] using hle
      exact absurd (WithBot.coe_injective hfalse) (WithTop.coe_ne_top (a := (1 : ℕ)))
    | coe m =>
      have hm : m = 1 := by
        norm_num [hd] at hpos hle
        omega
      simp [hm]

/-! ### Stacks Tag 0BXW -/

/-- **[Stacks, Tag 0A25] for a reduced scheme.** A reduced separated scheme of finite type over
a field `k` of topological Krull dimension at most one is H-quasi-projective over `k`.

The ample invertible module comes from the reduced case of [Stacks, Tag 09NX],
`Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one`. -/
theorem isHQuasiProjective_of_isReduced (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    AlgebraicGeometry.IsHQuasiProjective p := by
  have : AlgebraicGeometry.IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field p
  have : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field p
  obtain ⟨L, hLinv, hLamp⟩ :=
    Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one
      X hdim
  have := hLinv
  exact Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isAmple p L
    ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).mpr hLamp)

/-- **The four clauses of [Stacks, Tag 0BXW] from an H-quasi-projective structure morphism.**
For a reduced separated scheme of finite type over a field `k` with `dim(X) ≤ 1` whose structure
morphism is a quasi-compact immersion into a relative projective space, the projective
completion of [Stacks, Tag 0BXV] has discrete valuation rings at the points of its boundary. -/
theorem exists_projective_completion_discreteValuation_of_isHQuasiProjective
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X]
    (hqp : AlgebraicGeometry.IsHQuasiProjective p)
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Y) (hj : IsOpenImmersion j),
      letI : IsOpenImmersion j := hj
      j ≫ q = p ∧ IsProjectiveMorphism q ∧ IsDominant j ∧
        Scheme.Opens.IsSchemeTheoreticallyDense j.opensRange ∧
        ((Set.range j.base)ᶜ).Finite ∧
        ∀ y : Y, y ∉ Set.range j.base →
          IsClosed ({y} : Set Y) ∧
            ∃ _ : IsDomain (Y.presheaf.stalk y),
              IsDiscreteValuationRing (Y.presheaf.stalk y) := by
  -- Step 1: the completion of Tag 0BXV, with its closed immersion into `ℙⁿ_k`.
  obtain ⟨Y, q, j, hj, hjq, hproj, hqft, -, hdom, -, -, -⟩ :=
    exists_projective_completion_aux_of_isHQuasiProjective k p hqp hdim
  have : IsOpenImmersion j := hj
  have : LocallyOfFiniteType q := hqft
  have : IsProper q := isProper_of_isProjectiveMorphism q hproj
  have hjqc : QuasiCompact j := by
    have : QuasiCompact (j ≫ q) := by rw [hjq]; infer_instance
    exact QuasiCompact.of_comp j q
  have : QuasiCompact j := hjqc
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  -- Step 2: the normalization of the completion in `X`, finite by Tag 0BXS.
  have hfin : IsFinite j.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType_over_field k q p j hjq
  have : IsFinite j.fromNormalization := hfin
  have : LocallyOfFiniteType j := inferInstance
  have : IsSeparated j := inferInstance
  have : LocallyQuasiFinite j := inferInstance
  have : IsOpenImmersion j.toNormalization := inferInstance
  have hcomp : j.toNormalization ≫ (j.fromNormalization ≫ q) = p := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
    exact hjq
  have hNft : LocallyOfFiniteType (j.fromNormalization ≫ q) := inferInstance
  have hNqc : QuasiCompact (j.fromNormalization ≫ q) := inferInstance
  have hNproper : IsProper (j.fromNormalization ≫ q) := inferInstance
  -- Step 3: clause (1). An ample invertible module on the normalization, pulled back from
  -- `𝒪(1)` on `ℙⁿ_k` along the affine morphism `ν ≫ i`.
  obtain ⟨n, i, hi, -⟩ := hproj
  have : IsClosedImmersion i := hi
  have hampleN : ∃ (L : j.normalization.Modules) (hL : Stacks.Ample.IsInvertibleModule _ L),
      have : Stacks.Ample.IsInvertibleModule j.normalization L := hL
      Stacks.Ample.IsAmple j.normalization L := by
    refine ⟨Stacks.AmpleLocallyClosed.pullbackModule (j.fromNormalization ≫ i)
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n
        (Spec (CommRingCat.of k))), inferInstance, ?_⟩
    exact Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom _ _
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n (Spec (CommRingCat.of k)))
  have hNproj : IsProjectiveMorphism (j.fromNormalization ≫ q) :=
    isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
      ⟨isHQuasiProjective_of_exists_isAmple _ hNft hNqc hampleN, hNproper⟩
  -- Step 4: the normalization is Noetherian and again of dimension at most one.
  have : IsLocallyNoetherian j.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (j.fromNormalization ≫ q)
  have : CompactSpace j.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (j.fromNormalization ≫ q)
  have : AlgebraicGeometry.IsNoetherian j.normalization := AlgebraicGeometry.IsNoetherian.mk
  have hNdense : Dense (Set.range j.toNormalization.base) :=
    (inferInstance : IsDominant j.toNormalization).denseRange
  have hNdim : topologicalKrullDim (j.normalization : Type u) ≤ 1 :=
    (topologicalKrullDim_le_of_dense_isOpenImmersion k j.toNormalization p
      (j.fromNormalization ≫ q) hcomp hNdense).trans hdim
  -- Step 5: clause (3), the boundary is a finite set of closed points.
  have hNgen : genericPoints j.normalization ⊆ Set.range j.toNormalization.base :=
    (isDominant_iff_genericPoints_subset_range j.toNormalization).mp inferInstance
  obtain ⟨hfinite, hclosed⟩ :=
    finite_compl_of_genericPoints_subset j.toNormalization.isOpenEmbedding.isOpen_range
      hNdim hNgen
  -- Step 6: clause (2), scheme-theoretic density, from reducedness of the normalization.
  have hNstd :
      Scheme.Opens.IsSchemeTheoreticallyDense j.toNormalization.opensRange := by
    intro V
    have hU : Dense (j.toNormalization.opensRange : Set j.normalization) := by
      simpa only [Scheme.Hom.coe_opensRange] using hNdense
    have : IsDominant ((V.ι ⁻¹ᵁ j.toNormalization.opensRange).ι) :=
      Opens.isDominant_ι (hU.preimage V.ι.isOpenEmbedding.isOpenMap)
    have : AlgebraicGeometry.IsReduced V.toScheme := inferInstance
    exact IsSchemeTheoreticallyDominant.of_isDominant _
  -- Step 7: clause (4), the boundary local rings are discrete valuation rings.
  have hNagata : IsNagataScheme Y := isNagataScheme_of_locallyOfFiniteType_over_field k q
  refine ⟨j.normalization, j.fromNormalization ≫ q, j.toNormalization, inferInstance, hcomp,
    hNproj, inferInstance, hNstd, hfinite, fun y hy => ⟨hclosed y hy, ?_⟩⟩
  have hdim1 : ringKrullDim (j.normalization.presheaf.stalk y) = 1 :=
    ringKrullDim_stalk_eq_one_of_notMem_genericPoints k (j.fromNormalization ≫ q) hNdim
      hNgen hy
  have hempty : IsEmpty (j.toNormalization.fiber y) := by
    refine ⟨fun z => hy ⟨j.toNormalization.fiberι y z, ?_⟩⟩
    have hp := (j.toNormalization.fiberHomeo y z).property
    change j.toNormalization.base ((j.toNormalization.fiberHomeo y z).1) = y at hp
    rw [Scheme.Hom.fiberHomeo_apply] at hp
    exact hp
  exact isDiscreteValuationRing_stalk_normalization_of_isEmpty_fiber j hNagata y hdim1 hempty

/-- The projective completion with discrete valuation boundary, with a superfluous hypothesis.

This is
`Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced`
with [Stacks, Tag 09NZ] taken as an extra hypothesis `h09NZ`, which the proof does not use: for
a reduced scheme the ample invertible sheaf that tag supplies is the reduced case of
[Stacks, Tag 09NX]. Tag 09NZ itself is
`Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one`.
-/
theorem exists_projective_completion_discreteValuation
    (h09NZ : Stacks.HQuasiProjectiveDimensionOne.AmpleOfNoetherianSeparatedDimLEOne.{u})
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Y) (hj : IsOpenImmersion j),
      letI : IsOpenImmersion j := hj
      j ≫ q = p ∧ IsProjectiveMorphism q ∧ IsDominant j ∧
        Scheme.Opens.IsSchemeTheoreticallyDense j.opensRange ∧
        ((Set.range j.base)ᶜ).Finite ∧
        ∀ y : Y, y ∉ Set.range j.base →
          IsClosed ({y} : Set Y) ∧
            ∃ _ : IsDomain (Y.presheaf.stalk y),
              IsDiscreteValuationRing (Y.presheaf.stalk y) :=
  exists_projective_completion_discreteValuation_of_isHQuasiProjective k p
    (Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_ampleOfNoetherianSeparatedDimLEOne
      h09NZ p hdim) hdim

/-- **[Stacks, Tag 0BXW].** Let `X` be a reduced separated scheme of finite type over a field `k`
with `dim(X) ≤ 1`. Then there is an open immersion `j : X ⟶ X'` such that `X'` is H-projective
over `k`, the image of `j` is dense and scheme-theoretically dense in `X'`, the complement
`X' ∖ j(X)` is a finite set of closed points, and the local ring of `X'` at each of those points
is a discrete valuation ring.

The first step of the proof, [Stacks, Tag 0A25], is used in its reduced case
`Stacks.CurveProjectiveCompletion.isHQuasiProjective_of_isReduced`. -/
@[stacks 0BXW]
theorem exists_projective_completion_discreteValuation_of_isReduced
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Y) (hj : IsOpenImmersion j),
      letI : IsOpenImmersion j := hj
      j ≫ q = p ∧ IsProjectiveMorphism q ∧ IsDominant j ∧
        Scheme.Opens.IsSchemeTheoreticallyDense j.opensRange ∧
        ((Set.range j.base)ᶜ).Finite ∧
        ∀ y : Y, y ∉ Set.range j.base →
          IsClosed ({y} : Set Y) ∧
            ∃ _ : IsDomain (Y.presheaf.stalk y),
              IsDiscreteValuationRing (Y.presheaf.stalk y) :=
  exists_projective_completion_discreteValuation_of_isHQuasiProjective k p
    (isHQuasiProjective_of_isReduced k p hdim) hdim

end Stacks.CurveProjectiveCompletion

end
