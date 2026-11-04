module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.Topology.Sober.Defs

/-!
# The point space of a decent algebraic space is sober

Let `X` be a decent algebraic space over a scheme `S`. Then `|X|` is sober: it is Kolmogorov,
and every irreducible closed subset of it has a generic point. This is **Stacks 03K6**.

## Main results

* `AlgebraicGeometry.Space.t0Space_points_of_isDecentSpace`: `|X|` is Kolmogorov.
* `AlgebraicGeometry.Space.quasiSober_points_of_isDecentSpace`: every irreducible closed
  subset of `|X|` has a generic point.
* `AlgebraicGeometry.Space.stacksSober_points_of_isDecentSpace`: **Stacks 03K6**, soberness in
  the sense of Stacks 004X.

## Implementation notes

The Kolmogorov property is Stacks 03K3, read through the implication from decency to
condition `(α)` of Stacks 03JX.

For an irreducible closed `T ⊆ |X|` the generic point is produced on the reduced closed
subspace `Z ⊆ X` supported on `T`, which is Stacks 03IQ. That the inclusion of `Z` is a closed
immersion — in particular representable — is the part of Stacks 03IQ carried by the hypothesis
of effective descent for closed immersions along a surjective étale morphism of the site; that
hypothesis is now discharged outright, a closed immersion being affine, so the unconditional
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace` is used here.
Representability makes `Z` decent by Stacks 03KF, so Stacks 086U gives a dense open subspace
`G ⊆ Z` which is a scheme.

The point set `R` of `G` inside `|X|` is then dense in `T`: the inclusion of `Z` is a closed
embedding on points by Stacks 0ABJ, and a closed embedding carries the closure of a set to the
closure of its image. Being dense in an irreducible set, `R` is itself irreducible, and it is
quasi-sober because the inclusion of `G` into `X` is an immersion, hence a homeomorphism onto
`R`, and `|G|` is the point space of a scheme. An irreducible quasi-sober space has a generic
point, and the closure in `|X|` of that point is the closure of `R`, namely `T`.

## References

* [Stacks Project, Tag 004X](https://stacks.math.columbia.edu/tag/004X)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03K3](https://stacks.math.columbia.edu/tag/03K3)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- A subset whose closure is an irreducible set and which is quasi-sober in the subspace
topology supplies a generic point for that closure. -/
private theorem exists_isGenericPoint_of_quasiSober_of_closure_eq {α : Type*}
    [TopologicalSpace α] (R : Set α) {T : Set α} (hT : IsIrreducible T) (hRT : closure R = T)
    (hsober : QuasiSober R) : ∃ x, IsGenericPoint x T := by
  have := hsober
  have hRne : R.Nonempty := by
    rcases Set.eq_empty_or_nonempty R with h | h
    · rw [h, closure_empty] at hRT
      exact absurd hRT.symm hT.1.ne_empty
    · exact h
  have hRirr : IsIrreducible R := ⟨hRne, isPreirreducible_iff_closure.mp (hRT ▸ hT.2)⟩
  have : IrreducibleSpace R := Subtype.irreducibleSpace hRirr
  have hsub : R ⊆ closure ({(genericPoint R : α)} : Set α) := by
    have h1 : (Subtype.val : R → α) '' closure ({genericPoint R} : Set R) ⊆
        closure ((Subtype.val : R → α) '' ({genericPoint R} : Set R)) :=
      image_closure_subset_closure_image continuous_subtype_val
    rwa [genericPoint_closure, Set.image_univ, Subtype.range_coe, Set.image_singleton] at h1
  refine ⟨(genericPoint R : α), subset_antisymm ?_ ?_⟩
  · rw [← hRT]
    exact closure_mono (Set.singleton_subset_iff.mpr (genericPoint R).2)
  · rw [← hRT]
    exact closure_minimal hsub isClosed_closure

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03K3.** The point space of a decent algebraic space over `S` is Kolmogorov: decency
is condition (4) of Stacks 03JV at every point, which gives condition `(α)` of Stacks 03JX, and
Stacks 03K3 concludes.

Kolmogorov is `T0Space`; `StacksFrontier.Topology.Sober.Defs` identifies Definition 004X's
Kolmogorov condition with `T0Space` in `kolmogorov_iff`. -/
@[stacks 03K3]
theorem t0Space_points_of_isDecentSpace (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) : T0Space (points B S hS X) :=
  t0Space_points_of_hasFiniteChartFibers B S hS hX
    (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec)

/-- Every irreducible closed subset of the point space of a decent algebraic space over `S` has
a generic point: the reduced closed subspace supported on it is decent, so it has a dense open
subspace which is a scheme, and the point set of that subspace is an irreducible quasi-sober
subset of the point space whose closure is the given set. -/
theorem quasiSober_points_of_isDecentSpace (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) : QuasiSober (points B S hS X) := by
  refine ⟨fun {T} hTirr hTcl ↦ ?_⟩
  -- the reduced closed subspace supported on `T`, and its inclusion
  obtain ⟨hZalg, hZci⟩ :
      IsClosedSubspace B S hS (reducedClosedSubspace B S hS X hX T hTcl) :=
    isClosedSubspace_reducedClosedSubspace B S hS X hX T hTcl
  have hZcemb : Topology.IsClosedEmbedding
      (pointsMap B S hS (reducedClosedSubspace B S hS X hX T hTcl).toFunctor
        (reducedClosedSubspace B S hS X hX T hTcl).ι) := by
    refine ⟨isEmbedding_pointsMap_of_isImmersion B S hS hX _
      (isImmersion_of_isClosedImmersion B S hS hZci), ?_⟩
    rw [range_pointsMap_ι_reducedClosedSubspace]
    exact hTcl
  -- a dense open subspace of it which is a scheme
  obtain ⟨G, hGopen, hGrep, hGdense⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS hZalg
      (isDecentSpace_of_relativelyRepresentable B S hS hZalg _ hZci.rep hdec)
  have _ : G.toFunctor.IsRepresentable := hGrep
  have _ : QuasiSober (points B S hS G.toFunctor) :=
    ((pointsHomeomorphOfIso B S hS G.toFunctor.reprW).symm.trans
      (schemePointsHomeomorph B S hS G.toFunctor.reprX)).isOpenEmbedding.quasiSober
  -- its point set inside `|X|` is quasi-sober and has closure `T`
  have hwemb : Topology.IsEmbedding (pointsMap B S hS G.toFunctor
      (G.ι ≫ (reducedClosedSubspace B S hS X hX T hTcl).ι)) :=
    isEmbedding_pointsMap_of_isImmersion B S hS hX _
      (isImmersion_comp B S hS G.ι _ (isImmersion_of_isOpenImmersion B S hS hGopen.2)
        (isImmersion_of_isClosedImmersion B S hS hZci))
  have hRsober : QuasiSober (Set.range (pointsMap B S hS G.toFunctor
      (G.ι ≫ (reducedClosedSubspace B S hS X hX T hTcl).ι))) :=
    hwemb.toHomeomorph.symm.isOpenEmbedding.quasiSober
  refine exists_isGenericPoint_of_quasiSober_of_closure_eq _ hTirr ?_ hRsober
  rw [pointsMap_comp, Set.range_comp, hZcemb.closure_image_eq, hGdense.closure_eq,
    Set.image_univ, range_pointsMap_ι_reducedClosedSubspace]

/-- **Stacks 03K6.** The point space of a decent algebraic space over `S` is sober in the sense
of Stacks 004X: it is Kolmogorov, and every irreducible closed subset of it has a unique
generic point. -/
@[stacks 03K6]
theorem stacksSober_points_of_isDecentSpace (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) : StacksSober (points B S hS X) :=
  stacksSober_iff_t0_and_quasiSober.mpr
    ⟨t0Space_points_of_isDecentSpace B S hS hX hdec,
      quasiSober_points_of_isDecentSpace B S hS hX hdec⟩

end AlgebraicGeometry.Space

end
