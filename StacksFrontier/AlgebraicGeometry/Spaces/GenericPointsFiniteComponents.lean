module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.GermInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableImpliesFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RepresentablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.ReasonableFromGenericPoints

/-!
# Generic points of an algebraic space with finitely many irreducible components

Stacks 0BB9 states three equivalent conditions on an algebraic space `X` over a scheme `S`:

1. `X` is decent and `|X|` has finitely many irreducible components;
2. every quasi-compact scheme étale over `X` has finitely many irreducible components, only
   finitely many points of `|X|` have codimension `0`, and each of those can be represented by
   a monomorphism `Spec(k) ⟶ X`;
3. there is a dense open `X' ⊂ X` which is a scheme, `|X'|` has finitely many irreducible
   components, and the morphism `x' ⟶ X` attached to each of their generic points is
   quasi-compact.

The three conditions are stated and the equivalence is proved, around the cycle
(1) ⟹ (3) ⟹ (2) ⟹ (1), together with the source's two concluding assertions: that such an
algebraic space is reasonable, and that the generic points of the dense open subscheme are
exactly the generic points of the irreducible components of `|X|`.

## Main definitions

* `AlgebraicGeometry.Space.IsDecentWithFinitelyManyComponents` is condition (1).
* `AlgebraicGeometry.Space.HasFiniteEtaleIrreducibleComponents`,
  `AlgebraicGeometry.Space.HasFiniteCodimensionZeroPoints` and
  `AlgebraicGeometry.Space.HasMonomorphicCodimensionZeroPoints` are the three clauses of
  condition (2), and
  `AlgebraicGeometry.Space.HasFiniteEtaleComponentsAndCodimensionZeroPoints` is their
  conjunction, condition (2).
* `AlgebraicGeometry.Space.HasQuasiCompactGenericDenseOpenScheme` is condition (3).

## Main results

* `isDecentWithFinitelyManyComponents_tfae`, in the namespace `AlgebraicGeometry.Space`, is
  the equivalence of the three conditions.
* The three arrows of the cycle are
  `IsDecentWithFinitelyManyComponents.hasQuasiCompactGenericDenseOpenScheme`,
  `HasQuasiCompactGenericDenseOpenScheme.hasFiniteEtaleComponentsAndCodimensionZeroPoints` and
  `HasFiniteEtaleComponentsAndCodimensionZeroPoints.isDecentWithFinitelyManyComponents`. The
  middle one is assembled from
  `HasQuasiCompactGenericDenseOpenScheme.hasFiniteEtaleIrreducibleComponents`,
  `HasQuasiCompactGenericDenseOpenScheme.hasFiniteCodimensionZeroPoints` and
  `HasQuasiCompactGenericDenseOpenScheme.hasMonomorphicCodimensionZeroPoints`;
  `IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints` is the clause of
  condition (2) which decency gives outright.
* `IsDecentWithFinitelyManyComponents.isReasonableSpace` and
  `HasFiniteEtaleComponentsAndCodimensionZeroPoints.isReasonableSpace` are the source's
  concluding assertion that the space is reasonable, and
  `image_genericPoints_eq_genericPoints_of_denseRange` is its concluding assertion about
  generic points.
* `isDecentSpace_of_isReasonableSpace`: a reasonable algebraic space over `S` is decent.
* `isOpenEmbedding_pointsMap_ι`: the inclusion of an open subspace is an open embedding on
  point sets.
* `mem_genericPoints_of_localRingDimension_eq_zero_of_isOpenSubspace` and
  `localRingDimension_eq_zero_of_mem_genericPoints_of_isOpenSubspace`: a point of a
  representable open subspace is the generic point of an irreducible component exactly when
  its image has codimension `0`.
* `hasMonomorphicFieldRepresentative_pointsMap_ι_of_isRepresentable`: the image of a point of
  a representable open subspace is represented by a monomorphism from the spectrum of a field.
* `mem_range_pointsMap_ι_of_mem_genericPoints`: a generic point of an irreducible component of
  an étale chart with finitely many irreducible components lies over a dense open subspace.

## Implementation notes

Codimension `0` is `AlgebraicGeometry.Space.localRingDimension`, the dimension of the local
ring of Stacks 04NA, as in Stacks 0BAQ; "quasi-compact scheme étale over `X`" is an object of
the site with compact underlying scheme and an étale morphism to `X`, as in condition (1) of
Stacks 03JV; the dense open subscheme of condition (3) is a representable open subspace whose
point set is dense, which is the shape Stacks 086U produces; and the quasi-compactness of
`x' ⟶ X` is `AlgebraicGeometry.Space.HasQuasiCompactFieldRepresentative`, condition (5) of
Stacks 03JV. The point set carries the topology of Stacks 03BX, made a local instance here.

**Where the three arrows come from.** (1) implies (3) is Stacks 086U, in the form
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace`,
plus the transfer of finiteness of the irreducible components along an open embedding.
(2) implies (1) is Stacks 0BB8,
`AlgebraicGeometry.Space.isReasonableSpace_of_finite_irreducibleComponents_of_mono`, whose two
hypotheses are literally the first and third clauses of condition (2), followed by
`AlgebraicGeometry.Space.isDecentSpace_of_isReasonableSpace`; the finiteness of the
irreducible components of `|X|` does not come from the source's route but from the second
clause together with Stacks 0BAR, the density of the points of codimension `0`. (3) implies
(2) is the source's own geometric argument, recorded below.

**The argument for (3) implies (2).** Let `a : U ⟶ X` be étale with `U` compact, and let
`V ⊂ U` be the preimage of `|X'|`. It is open, and dense because `|U| → |X|` is open on
points. A generic point of an irreducible component of `U` lying in `V` has codimension `0`
on `X` by Stacks 0BAQ, so its image is the image of a generic point of an irreducible
component of `|X'|`; there are finitely many of those, and the fibre of `|U| → |X|` above each
is finite because the attached morphism `Spec(k) ⟶ X` is quasi-compact
(`AlgebraicGeometry.Space.finite_setFibre_of_isQuasiCompact_fieldMorphism`). So `V` contains
only finitely many generic points, and that bounds the irreducible components of `U`: the
closures of those finitely many points cover `V`, hence cover `U` by density, and every
irreducible component of `U` is one of them. Once that is known, every generic point of a
chart *does* lie in `V` — a component of a space with finitely many components has interior —
and the remaining two clauses follow, the third from
`AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_yoneda` applied to the scheme `X'`
and the monomorphism `X' ⟶ X`.

**The private topological lemmas.** `mem_of_mem_closure_singleton`,
`finite_irreducibleComponents_of_dense_open`, `mem_of_mem_genericPoints_of_dense`,
`finite_irreducibleComponents_of_dense_sUnion` and `mem_genericPoints_map_iff` are the
topological bookkeeping of the three arrows. They are kept private because they are stated for
a bare topological space and are used only here. That an open embedding cannot increase the
number of irreducible components is the same bookkeeping, but it is not restated here:
`AlgebraicGeometry.finite_irreducibleComponents_of_isOpenEmbedding` already has it.

`AlgebraicGeometry.Space.finite_irreducibleComponents_of_denseRange` is the opposite direction:
a space receiving a continuous map of dense range from a space with finitely many irreducible
components has finitely many itself. It is public because it transports the hypothesis of
Stacks 0GUL that `|X|` has finitely many irreducible components from a chart to the spaces built
over it.

## References

* [Stacks Project, Tag 0BB9](https://stacks.math.columbia.edu/tag/0BB9)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 0BB8](https://stacks.math.columbia.edu/tag/0BB8)
* [Stacks Project, Tag 0BAR](https://stacks.math.columbia.edu/tag/0BAR)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-! ### Topological preliminaries -/

/-- A point whose closure contains a point of an open set lies in that open set. -/
theorem mem_of_mem_closure_singleton {Y : Type*} [TopologicalSpace Y] {t y : Y}
    {V : Set Y} (hV : IsOpen V) (hy : y ∈ V) (h : y ∈ closure ({t} : Set Y)) : t ∈ V := by
  obtain ⟨z, hzV, hzt⟩ := mem_closure_iff.1 h V hV hy
  have hzt' : z = t := hzt
  exact hzt' ▸ hzV

/-- A space with a dense open subset containing only finitely many generic points of
irreducible components has finitely many irreducible components. -/
private theorem finite_irreducibleComponents_of_dense_open
    {Y : Type*} [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] {V : Set Y}
    (hVopen : IsOpen V) (hVdense : Dense V) (hfin : (genericPoints Y ∩ V).Finite) :
    (irreducibleComponents Y).Finite := by
  classical
  -- Every point of `V` is a specialization of a generic point lying in `V`.
  have hVsub : V ⊆ ⋃ t ∈ genericPoints Y ∩ V, closure ({t} : Set Y) := by
    intro y hy
    have hc : irreducibleComponent y ∈ irreducibleComponents Y :=
      irreducibleComponent_mem_irreducibleComponents y
    have hcl : closure ({(genericPoints.ofComponent (⟨irreducibleComponent y, hc⟩ :
        irreducibleComponents Y)).1} : Set Y) = irreducibleComponent y :=
      genericPoints.isGenericPoint_ofComponent _
    have hyt : y ∈ closure ({(genericPoints.ofComponent (⟨irreducibleComponent y, hc⟩ :
        irreducibleComponents Y)).1} : Set Y) := by
      rw [hcl]
      exact mem_irreducibleComponent
    exact Set.mem_biUnion
      ⟨(genericPoints.ofComponent (⟨irreducibleComponent y, hc⟩ :
        irreducibleComponents Y)).2, mem_of_mem_closure_singleton hVopen hy hyt⟩ hyt
  have hclosed : IsClosed (⋃ t ∈ genericPoints Y ∩ V, closure ({t} : Set Y)) :=
    hfin.isClosed_biUnion fun _ _ => isClosed_closure
  have huniv : ∀ y : Y, y ∈ ⋃ t ∈ genericPoints Y ∩ V, closure ({t} : Set Y) := by
    intro y
    have hsub : closure V ⊆ ⋃ t ∈ genericPoints Y ∩ V, closure ({t} : Set Y) :=
      hclosed.closure_subset_iff.2 hVsub
    exact hsub (hVdense.closure_eq ▸ Set.mem_univ y)
  -- Hence every generic point already lies in the finite set.
  have hgen : genericPoints Y ⊆ genericPoints Y ∩ V := by
    intro t' ht'
    obtain ⟨t, htT, ht'cl⟩ := Set.mem_iUnion₂.1 (huniv t')
    have hsub : closure ({t'} : Set Y) ⊆ closure ({t} : Set Y) :=
      closure_minimal (Set.singleton_subset_iff.2 ht'cl) isClosed_closure
    have hirr : IsIrreducible (closure ({t} : Set Y)) := isIrreducible_singleton.closure
    have hmax : Maximal IsIrreducible (closure ({t'} : Set Y)) := ht'
    have heq : closure ({t} : Set Y) = closure ({t'} : Set Y) :=
      le_antisymm (hmax.2 hirr hsub) hsub
    have htt' : t = t' := (inseparable_iff_closure_eq.2 heq).eq
    exact htt' ▸ htT
  have hgenfin : (genericPoints Y).Finite := hfin.subset hgen
  have : Finite (genericPoints Y) := hgenfin
  exact Finite.of_equiv (genericPoints Y) (genericPoints.equiv (α := Y))

/-- In a space with finitely many irreducible components, every dense open subset contains
every generic point of an irreducible component. -/
theorem mem_of_mem_genericPoints_of_dense
    {Y : Type*} [TopologicalSpace Y] {V : Set Y} (hVopen : IsOpen V) (hVdense : Dense V)
    (hfin : (irreducibleComponents Y).Finite) {t : Y} (ht : t ∈ genericPoints Y) : t ∈ V := by
  classical
  have hAclosed : IsClosed (⋃ Z ∈ irreducibleComponents Y \ {closure ({t} : Set Y)}, Z) :=
    (hfin.subset Set.sdiff_subset).isClosed_biUnion fun Z hZ =>
      isClosed_of_mem_irreducibleComponents Z hZ.1
  have htA : t ∉ ⋃ Z ∈ irreducibleComponents Y \ {closure ({t} : Set Y)}, Z := by
    intro hmem
    obtain ⟨Z, hZ, htZ⟩ := Set.mem_iUnion₂.1 hmem
    have hsub : closure ({t} : Set Y) ⊆ Z :=
      (isClosed_of_mem_irreducibleComponents Z hZ.1).closure_subset_iff.2
        (Set.singleton_subset_iff.2 htZ)
    have hmax : Maximal IsIrreducible (closure ({t} : Set Y)) := ht
    exact hZ.2 (le_antisymm (hmax.2 hZ.1.1 hsub) hsub)
  obtain ⟨y, hyA, hyV⟩ := (dense_iff_inter_open.1 hVdense) _ hAclosed.isOpen_compl ⟨t, htA⟩
  have hyc : y ∈ closure ({t} : Set Y) := by
    by_contra hy
    refine hyA (Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩
      mem_irreducibleComponent)
    intro hEq
    exact hy (hEq ▸ mem_irreducibleComponent)
  exact mem_of_mem_closure_singleton hVopen hyV hyc

/-- A space covered up to closure by finitely many irreducible subsets has finitely many
irreducible components: each component, being irreducible and covered by the finitely many
closures, lies in one of them and so equals it. -/
private theorem finite_irreducibleComponents_of_dense_sUnion
    {Y : Type*} [TopologicalSpace Y] {s : Set (Set Y)} (hs : s.Finite)
    (hirr : ∀ C ∈ s, IsIrreducible C) (hdense : Dense (⋃₀ s)) :
    (irreducibleComponents Y).Finite := by
  classical
  have himg : (closure '' s).Finite := hs.image closure
  have hcov : ∀ z : Y, z ∈ ⋃₀ (closure '' s) := by
    intro z
    have hz : z ∈ closure (⋃₀ s) := hdense.closure_eq ▸ Set.mem_univ z
    rw [hs.closure_sUnion] at hz
    obtain ⟨C, hC, hzC⟩ := Set.mem_iUnion₂.1 hz
    exact ⟨closure C, ⟨C, hC, rfl⟩, hzC⟩
  have hclosed : ∀ z ∈ himg.toFinset, IsClosed z := by
    intro z hz
    rw [himg.mem_toFinset] at hz
    obtain ⟨C, -, rfl⟩ := hz
    exact isClosed_closure
  refine Set.Finite.subset himg ?_
  intro Z hZ
  have hsub : Z ⊆ ⋃₀ (himg.toFinset : Set (Set Y)) := by
    rw [himg.coe_toFinset]
    exact fun z _ => hcov z
  obtain ⟨z, hzF, hZz⟩ := isIrreducible_iff_sUnion_isClosed.1 hZ.1 himg.toFinset hclosed hsub
  rw [himg.mem_toFinset] at hzF
  obtain ⟨C, hC, hCz⟩ := hzF
  refine ⟨C, hC, ?_⟩
  rw [hCz]
  exact (le_antisymm hZz (hZ.2 (hCz ▸ (hirr C hC).closure) hZz)).symm

/-- **A space receiving a continuous map of dense range from a space with finitely many
irreducible components has finitely many irreducible components.**

The images of the irreducible components of the source are finitely many irreducible subsets
of the target whose union is the range of the map, which is dense; so
`AlgebraicGeometry.Space.finite_irreducibleComponents_of_dense_sUnion` applies.

This is the converse direction to
`AlgebraicGeometry.finite_irreducibleComponents_of_isOpenEmbedding`, and it needs neither
openness of the map nor any separation hypothesis on either space. Applied to the point map of
a morphism with dense point range — an open immersion with dense image, say — it transports the
hypothesis "finitely many irreducible components" from the source to the target. -/
theorem finite_irreducibleComponents_of_denseRange {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {f : Z → Y} (hf : Continuous f) (hdense : DenseRange f)
    (hfin : (irreducibleComponents Z).Finite) :
    (irreducibleComponents Y).Finite := by
  refine finite_irreducibleComponents_of_dense_sUnion (hfin.image (f '' ·)) ?_ ?_
  · rintro C ⟨D, hD, rfl⟩
    exact hD.1.image f hf.continuousOn
  · refine Dense.mono ?_ hdense
    rintro y ⟨z, rfl⟩
    exact ⟨f '' irreducibleComponent z,
      ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z, rfl⟩,
      Set.mem_image_of_mem f mem_irreducibleComponent⟩

/-- An open embedding sends generic points of irreducible components of its source to generic
points of irreducible components of its target. -/
private theorem mem_genericPoints_of_isOpenEmbedding {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {f : Z → Y} (hf : Topology.IsOpenEmbedding f) {t : Z}
    (h : t ∈ genericPoints Z) : f t ∈ genericPoints Y := by
  have hcl : closure ({t} : Set Z) = f ⁻¹' closure ({f t} : Set Y) := by
    rw [hf.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
  obtain ⟨W, hW, hWsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({f t} : Set Y)) isIrreducible_singleton.closure
  have hne : (W ∩ Set.range f).Nonempty := ⟨f t, hWsub (subset_closure rfl), t, rfl⟩
  have hpre : f ⁻¹' W ∈ irreducibleComponents Z :=
    preimage_mem_irreducibleComponents hW hf hne
  have hsub : closure ({t} : Set Z) ⊆ f ⁻¹' W := hcl ▸ Set.preimage_mono hWsub
  have heq : f ⁻¹' W = closure ({t} : Set Z) := le_antisymm (h.2 hpre.1 hsub) hsub
  have hWclosure : closure (f '' (f ⁻¹' W)) = W :=
    closure_image_preimage_of_isPreirreducible f hf.isOpenMap W
      (heq ▸ ⟨t, subset_closure rfl⟩) hW.1.2 (isClosed_of_mem_irreducibleComponents W hW)
  have hWle : W ⊆ closure ({f t} : Set Y) := by
    rw [← hWclosure, heq]
    refine closure_minimal ?_ isClosed_closure
    refine subset_trans (image_closure_subset_closure_image hf.continuous) ?_
    rw [Set.image_singleton]
  change closure ({f t} : Set Y) ∈ irreducibleComponents Y
  rwa [← le_antisymm hWle hWsub]

/-- An open embedding matches up the generic points of the irreducible components of its source
with those generic points of its target which lie in its range. -/
private theorem mem_genericPoints_map_iff {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {f : Z → Y} (hf : Topology.IsOpenEmbedding f) (t : Z) :
    f t ∈ genericPoints Y ↔ t ∈ genericPoints Z := by
  refine ⟨fun h => ?_, mem_genericPoints_of_isOpenEmbedding hf⟩
  have hcl : closure ({t} : Set Z) = f ⁻¹' closure ({f t} : Set Y) := by
    rw [hf.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
  have hpre := preimage_mem_irreducibleComponents h hf ⟨f t, subset_closure rfl, t, rfl⟩
  rwa [← hcl] at hpre

/-! ### The three conditions -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

section Conditions

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 0BB9, condition (1).** The algebraic space is decent and its space of points has
finitely many irreducible components. -/
def IsDecentWithFinitelyManyComponents : Prop :=
  IsDecentSpace B S hS X ∧ (irreducibleComponents (points B S hS X)).Finite

/-- **Stacks 0BB9, condition (2), first clause.** Every quasi-compact scheme étale over the
algebraic space has finitely many irreducible components. -/
def HasFiniteEtaleIrreducibleComponents : Prop :=
  ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X),
    CompactSpace ((BigFppfOver.toScheme B S hS).obj U) → IsEtale B S hS a →
      (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)).Finite

/-- **Stacks 0BB9, condition (2), second clause.** Only finitely many points of the space of
points have codimension `0`. -/
def HasFiniteCodimensionZeroPoints : Prop :=
  {x : points B S hS X | localRingDimension B S hS x = 0}.Finite

/-- **Stacks 0BB9, condition (2), third clause.** Every point of codimension `0` is
represented by a monomorphism from the spectrum of a field. -/
def HasMonomorphicCodimensionZeroPoints : Prop :=
  ∀ x : points B S hS X, localRingDimension B S hS x = 0 →
    HasMonomorphicFieldRepresentative B S hS X x

/-- **Stacks 0BB9, condition (2).** Every quasi-compact scheme étale over the algebraic space
has finitely many irreducible components, only finitely many points have codimension `0`, and
each of those is represented by a monomorphism from the spectrum of a field. -/
def HasFiniteEtaleComponentsAndCodimensionZeroPoints : Prop :=
  HasFiniteEtaleIrreducibleComponents B S hS X ∧
    HasFiniteCodimensionZeroPoints B S hS X ∧
      HasMonomorphicCodimensionZeroPoints B S hS X

/-- **Stacks 0BB9, condition (3).** There is an open subspace which is a scheme and whose
point set is dense, with finitely many irreducible components, each of whose generic points is
represented by a quasi-compact morphism from the spectrum of a field. -/
def HasQuasiCompactGenericDenseOpenScheme : Prop :=
  ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
    DenseRange (pointsMap B S hS G.toFunctor G.ι) ∧
    (irreducibleComponents (points B S hS G.toFunctor)).Finite ∧
      ∀ x' : points B S hS G.toFunctor, x' ∈ genericPoints (points B S hS G.toFunctor) →
        HasQuasiCompactFieldRepresentative B S hS X
          (pointsMap B S hS G.toFunctor G.ι x')

end Conditions

/-! ### Condition (1) gives the third clause of condition (2) -/

/-- **Stacks 0BB9, condition (1) implies the third clause of condition (2).** A decent
algebraic space has a monomorphic field-valued representative at every point, in particular at
every point of codimension `0`. -/
@[stacks 0BB9 "condition (1) implies the third clause of condition (2)"]
theorem IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : IsDecentWithFinitelyManyComponents B S hS X) :
    HasMonomorphicCodimensionZeroPoints B S hS X :=
  fun x _ => IsDecentSpace.hasMonomorphicFieldRepresentative B S hS X h.1 x

/-! ### Points of a representable open subspace -/

/-- The point set of a representable presheaf on the big fppf site of `S` is a `T0` space,
being homeomorphic to the underlying space of a representing scheme. -/
private theorem t0Space_points_of_isRepresentable
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hrep : X.IsRepresentable) :
    T0Space (points B S hS X) :=
  have : X.IsRepresentable := hrep
  ((schemePointsHomeomorph B S hS X.reprX).symm.trans
    (pointsHomeomorphOfIso B S hS X.reprW)).t0Space

/-- Transporting a point along the isomorphism with a representing presheaf and back is the
identity. -/
private theorem pointsMap_reprW_symm {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    [F.IsRepresentable] (x : points B S hS F) :
    pointsMap B S hS (yoneda.obj F.reprX) F.reprW.hom
      ((pointsHomeomorphOfIso B S hS F.reprW).symm x) = x :=
  (pointsHomeomorphOfIso B S hS F.reprW).apply_symm_apply x

/-- The composite of a representing isomorphism with the inclusion of a representable open
subspace sends the corresponding point to the image of the given point. -/
private theorem pointsMap_reprW_symm_comp {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G : Subfunctor X} [G.toFunctor.IsRepresentable] (x' : points B S hS G.toFunctor) :
    pointsMap B S hS (yoneda.obj G.toFunctor.reprX) (G.toFunctor.reprW.hom ≫ G.ι)
      ((pointsHomeomorphOfIso B S hS G.toFunctor.reprW).symm x') =
        pointsMap B S hS G.toFunctor G.ι x' := by
  rw [pointsMap_comp_apply, pointsMap_reprW_symm]

/-- The inclusion of a representable open subspace, precomposed with a representing
isomorphism, is étale. -/
private theorem isEtale_reprW_hom_comp_ι {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G) [G.toFunctor.IsRepresentable] :
    IsEtale B S hS (G.toFunctor.reprW.hom ≫ G.ι) :=
  isEtale_comp B S hS (isEtale_of_isIso B S hS G.toFunctor.reprW.hom)
    (isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS hG.2))

/-- **A point of a representable open subspace whose image has codimension `0` is the generic
point of an irreducible component of that open subspace.**

The inclusion of the open subspace is étale, so a representing scheme of the open subspace is
an étale chart of the ambient algebraic space; the point of that scheme above the given point
is a generic point of an irreducible component by condition (3) of Stacks 0BAQ, and the
identification of the scheme with the point set of the open subspace is a homeomorphism. -/
theorem mem_genericPoints_of_localRingDimension_eq_zero_of_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G) (hrep : G.toFunctor.IsRepresentable)
    (x' : points B S hS G.toFunctor)
    (h : localRingDimension B S hS (pointsMap B S hS G.toFunctor G.ι x') = 0) :
    x' ∈ genericPoints (points B S hS G.toFunctor) := by
  have : G.toFunctor.IsRepresentable := hrep
  have hc := isEtale_reprW_hom_comp_ι B S hS hG (G := G)
  have hchart := chartPoint_pointsToScheme B S hS G.toFunctor.reprX
    (G.toFunctor.reprW.hom ≫ G.ι)
    ((pointsHomeomorphOfIso B S hS G.toFunctor.reprW).symm x')
  rw [pointsMap_reprW_symm_comp] at hchart
  have hgen : pointsToScheme B S hS G.toFunctor.reprX
      ((pointsHomeomorphOfIso B S hS G.toFunctor.reprW).symm x') ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj G.toFunctor.reprX) :=
    (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX _).1 h
      G.toFunctor.reprX (G.toFunctor.reprW.hom ≫ G.ι) _ hc hchart
  have hgen' : (pointsHomeomorphOfIso B S hS G.toFunctor.reprW).symm x' ∈
      genericPoints (points B S hS (yoneda.obj G.toFunctor.reprX)) :=
    ((schemePointsHomeomorph B S hS G.toFunctor.reprX).mem_genericPoints_iff _).1 hgen
  exact pointsMap_reprW_symm B S hS x' ▸
    (pointsHomeomorphOfIso B S hS G.toFunctor.reprW).mem_genericPoints hgen'

/-- **A point of a representable open subspace is represented by a monomorphism from the
spectrum of a field.** The residue field at the corresponding point of a representing scheme
does it, followed by the inclusion of the open subspace, which is a monomorphism. -/
theorem hasMonomorphicFieldRepresentative_pointsMap_ι_of_isRepresentable
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G : Subfunctor X}
    (hrep : G.toFunctor.IsRepresentable) (x' : points B S hS G.toFunctor) :
    HasMonomorphicFieldRepresentative B S hS X (pointsMap B S hS G.toFunctor G.ι x') := by
  have : G.toFunctor.IsRepresentable := hrep
  obtain ⟨r, hrp, hrmono⟩ := hasMonomorphicFieldRepresentative_yoneda B S hS
    G.toFunctor.reprX ((pointsHomeomorphOfIso B S hS G.toFunctor.reprW).symm x')
  refine ⟨FieldValuedPoint.map B S hS _ (G.toFunctor.reprW.hom ≫ G.ι) r, ?_, ?_⟩
  · rw [← pointsMap_class, hrp, pointsMap_reprW_symm_comp]
  · rw [fieldMorphism_map]
    exact mono_comp' hrmono
      (mono_comp' (mono_of_mono_fac G.toFunctor.reprW.hom_inv_id) inferInstance)

/-! ### Condition (3) implies condition (2) -/

/-- The preimage, in an étale chart, of the point set of a dense open subspace is open and
dense. -/
private theorem isOpen_and_dense_preimage_range_pointsMap_ι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G)
    (hdense : DenseRange (pointsMap B S hS G.toFunctor G.ι))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (ha : IsEtale B S hS a) :
    IsOpen ((fun y : (BigFppfOver.toScheme B S hS).obj U =>
      pointsMap B S hS (yoneda.obj U) a ((schemePointsHomeomorph B S hS U).symm y)) ⁻¹'
        Set.range (pointsMap B S hS G.toFunctor G.ι)) ∧
    Dense ((fun y : (BigFppfOver.toScheme B S hS).obj U =>
      pointsMap B S hS (yoneda.obj U) a ((schemePointsHomeomorph B S hS U).symm y)) ⁻¹'
        Set.range (pointsMap B S hS G.toFunctor G.ι)) :=
  ⟨(isOpen_range_pointsMap_of_isOpenImmersion B S hS G.ι hG.2).preimage
      ((continuous_pointsMap B S hS a).comp (schemePointsHomeomorph B S hS U).symm.continuous),
    hdense.preimage ((isOpenMap_pointsMap_of_etale B S hS hX U a
      (presheaf_etale_of_isEtale B S hS ha)).comp
      (schemePointsHomeomorph B S hS U).symm.isOpenMap)⟩

/-- **Stacks 0BB9, condition (3) implies the first clause of condition (2).** If an algebraic
space over `S` has a dense open subspace which is a scheme with finitely many irreducible
components whose generic points are represented by quasi-compact morphisms, then every
quasi-compact scheme étale over it has finitely many irreducible components.

Let `a : U ⟶ X` be étale with `U` compact, and let `V ⊂ U` be the preimage of the point set of
the open subspace: it is open, and dense because an étale morphism is open on points. A
generic point of an irreducible component of `U` lying in `V` has codimension `0` on `X` by
condition (2) of Stacks 0BAQ, so its image is the image of a generic point of the open
subspace; there are finitely many of those, and the fibre of `|U| → |X|` above each is finite
because the morphism representing it is quasi-compact. So `V` meets only finitely many generic
points, which bounds the irreducible components of `U`. -/
@[stacks 0BB9 "condition (3) implies the first clause of condition (2)"]
theorem HasQuasiCompactGenericDenseOpenScheme.hasFiniteEtaleIrreducibleComponents
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : HasQuasiCompactGenericDenseOpenScheme B S hS X) :
    HasFiniteEtaleIrreducibleComponents B S hS X := by
  classical
  obtain ⟨G, hG, hrep, hdense, hcomp, hqc⟩ := h
  intro U a hUcpt ha
  obtain ⟨hVopen, hVdense⟩ :=
    isOpen_and_dense_preimage_range_pointsMap_ι B S hS hX hG hdense U a ha
  have := t0Space_points_of_isRepresentable B S hS hrep
  have hgpfin : (genericPoints (points B S hS G.toFunctor)).Finite :=
    genericPoints.finite hcomp
  -- The fibre of `|U| → |X|` above a quasi-compact generic point of `X'` is finite.
  have hfam : ∀ x' ∈ genericPoints (points B S hS G.toFunctor),
      ((fun y : (BigFppfOver.toScheme B S hS).obj U =>
        pointsMap B S hS (yoneda.obj U) a ((schemePointsHomeomorph B S hS U).symm y)) ⁻¹'
          {pointsMap B S hS G.toFunctor G.ι x'}).Finite := by
    intro x' hx'
    obtain ⟨q, hqcl, hqqc⟩ := hqc x' hx'
    have hfib : (setFibre B S hS a q).Finite :=
      finite_setFibre_of_isQuasiCompact_fieldMorphism B S hS q hqqc hUcpt ha
    refine Set.Finite.subset
      (hfib.preimage (schemePointsHomeomorph B S hS U).symm.injective.injOn) ?_
    intro y hy
    have hy' : pointsMap B S hS (yoneda.obj U) a
        ((schemePointsHomeomorph B S hS U).symm y) =
      pointsMap B S hS G.toFunctor G.ι x' := hy
    change pointsMap B S hS (yoneda.obj U) a ((schemePointsHomeomorph B S hS U).symm y) =
      q.class B S hS X
    rw [hy', hqcl]
  refine finite_irreducibleComponents_of_dense_open hVopen hVdense
    (Set.Finite.subset (Set.Finite.biUnion hgpfin hfam) ?_)
  -- A generic point of `U` lying over `X'` lies over a generic point of `X'`.
  intro t ht
  have htgen : t ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) := ht.1
  have htmem : pointsMap B S hS (yoneda.obj U) a
      ((schemePointsHomeomorph B S hS U).symm t) ∈
      Set.range (pointsMap B S hS G.toFunctor G.ι) := ht.2
  obtain ⟨x', hx'⟩ := htmem
  have hst : pointsToScheme B S hS U ((schemePointsHomeomorph B S hS U).symm t) = t :=
    (schemePointsHomeomorph B S hS U).apply_symm_apply t
  have hdim : localRingDimension B S hS (pointsMap B S hS (yoneda.obj U) a
      ((schemePointsHomeomorph B S hS U).symm t)) = 0 :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX _).2
      ⟨U, a, pointsToScheme B S hS U ((schemePointsHomeomorph B S hS U).symm t), ha,
        chartPoint_pointsToScheme B S hS U a _, by rw [hst]; exact htgen⟩
  have hx'gen : x' ∈ genericPoints (points B S hS G.toFunctor) :=
    mem_genericPoints_of_localRingDimension_eq_zero_of_isOpenSubspace B S hS hX hG hrep x'
      (by rw [hx']; exact hdim)
  exact Set.mem_biUnion hx'gen hx'.symm

/-- **A generic point of a chart lies over a dense open subspace, once the chart has finitely
many irreducible components.** In a space with finitely many irreducible components a dense
open subset contains every generic point of an irreducible component, and the preimage of a
dense open subspace in an étale chart is dense and open. -/
theorem mem_range_pointsMap_ι_of_mem_genericPoints
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G)
    (hdense : DenseRange (pointsMap B S hS G.toFunctor G.ι))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (ha : IsEtale B S hS a)
    (hfin : (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)).Finite)
    (p : points B S hS (yoneda.obj U))
    (hp : pointsToScheme B S hS U p ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :
    pointsMap B S hS (yoneda.obj U) a p ∈
      Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  obtain ⟨hVopen, hVdense⟩ :=
    isOpen_and_dense_preimage_range_pointsMap_ι B S hS hX hG hdense U a ha
  have hmem := mem_of_mem_genericPoints_of_dense hVopen hVdense hfin hp
  have hmem' : pointsMap B S hS (yoneda.obj U) a ((schemePointsHomeomorph B S hS U).symm
      (pointsToScheme B S hS U p)) ∈
    Set.range (pointsMap B S hS G.toFunctor G.ι) := hmem
  have key : (schemePointsHomeomorph B S hS U).symm (pointsToScheme B S hS U p) = p :=
    (schemePointsHomeomorph B S hS U).symm_apply_apply p
  rwa [key] at hmem'

/-- Every point of codimension `0` lies over a dense open subspace, once the quasi-compact
étale charts have finitely many irreducible components. -/
private theorem exists_pointsMap_ι_eq_of_localRingDimension_eq_zero
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G)
    (hdense : DenseRange (pointsMap B S hS G.toFunctor G.ι))
    (hetale : HasFiniteEtaleIrreducibleComponents B S hS X) (x : points B S hS X)
    (hdim : localRingDimension B S hS x = 0) :
    ∃ x' : points B S hS G.toFunctor, pointsMap B S hS G.toFunctor G.ι x' = x := by
  obtain ⟨W, b, hWaff, hbetale, p, hp⟩ := exists_affine_etale_chart_at_point B S hS X hX x
  have hb : IsEtale B S hS b := isEtale_of_presheaf_etale B S hS hbetale
  have hWcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) :=
    have := hWaff
    inferInstance
  have hgen : pointsToScheme B S hS W p ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj W) :=
    (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX x).1 hdim W b _ hb
      (hp ▸ chartPoint_pointsToScheme B S hS W b p)
  obtain ⟨x', hx'⟩ := mem_range_pointsMap_ι_of_mem_genericPoints B S hS hX hG hdense W b hb
    (hetale W b hWcpt hb) p hgen
  exact ⟨x', by rw [hx', hp]⟩

/-- **Stacks 0BB9, condition (3) implies the second clause of condition (2).** Only finitely
many points have codimension `0`: each of them lies over the dense open subspace, and is the
image of a generic point of one of its finitely many irreducible components. -/
@[stacks 0BB9 "condition (3) implies the second clause of condition (2)"]
theorem HasQuasiCompactGenericDenseOpenScheme.hasFiniteCodimensionZeroPoints
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : HasQuasiCompactGenericDenseOpenScheme B S hS X) :
    HasFiniteCodimensionZeroPoints B S hS X := by
  have hetale := h.hasFiniteEtaleIrreducibleComponents B S hS hX
  obtain ⟨G, hG, hrep, hdense, hcomp, hqc⟩ := h
  have := t0Space_points_of_isRepresentable B S hS hrep
  refine Set.Finite.subset ((genericPoints.finite hcomp).image
    (pointsMap B S hS G.toFunctor G.ι)) ?_
  intro x hx
  have hdim : localRingDimension B S hS x = 0 := hx
  obtain ⟨x', hx'⟩ := exists_pointsMap_ι_eq_of_localRingDimension_eq_zero B S hS hX hG hdense
    hetale x hdim
  exact ⟨x', mem_genericPoints_of_localRingDimension_eq_zero_of_isOpenSubspace B S hS hX hG hrep
    x' (by rw [hx']; exact hdim), hx'⟩

/-- **Stacks 0BB9, condition (3) implies the third clause of condition (2).** A point of
codimension `0` lies over the dense open subspace, which is a scheme, so the residue field at
the corresponding point of that scheme presents it by a monomorphism. -/
@[stacks 0BB9 "condition (3) implies the third clause of condition (2)"]
theorem HasQuasiCompactGenericDenseOpenScheme.hasMonomorphicCodimensionZeroPoints
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : HasQuasiCompactGenericDenseOpenScheme B S hS X) :
    HasMonomorphicCodimensionZeroPoints B S hS X := by
  have hetale := h.hasFiniteEtaleIrreducibleComponents B S hS hX
  obtain ⟨G, hG, hrep, hdense, hcomp, hqc⟩ := h
  intro x hdim
  obtain ⟨x', hx'⟩ := exists_pointsMap_ι_eq_of_localRingDimension_eq_zero B S hS hX hG hdense
    hetale x hdim
  exact hx' ▸ hasMonomorphicFieldRepresentative_pointsMap_ι_of_isRepresentable B S hS hrep x'

/-- **Stacks 0BB9, condition (3) implies condition (2).** The three clauses together. -/
@[stacks 0BB9 "condition (3) implies condition (2)"]
theorem HasQuasiCompactGenericDenseOpenScheme.hasFiniteEtaleComponentsAndCodimensionZeroPoints
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : HasQuasiCompactGenericDenseOpenScheme B S hS X) :
    HasFiniteEtaleComponentsAndCodimensionZeroPoints B S hS X :=
  ⟨h.hasFiniteEtaleIrreducibleComponents B S hS hX,
    h.hasFiniteCodimensionZeroPoints B S hS hX,
    h.hasMonomorphicCodimensionZeroPoints B S hS hX⟩

/-! ### Reasonable implies decent -/

/-- **A reasonable algebraic space over `S` is decent.** This is the absolute form of
`AlgebraicGeometry.Space.isDecent_of_isReasonable`: reasonableness is property `(δ)` of
Stacks 03JX, which gives property `(γ)` by
`AlgebraicGeometry.Space.hasFiniteChartAndRelationFibersAtEveryPoint_of_isReasonableSpace`, and
property `(γ)` is decency by the equivalences of Stacks 03JV. -/
theorem isDecentSpace_of_isReasonableSpace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hr : IsReasonableSpace B S hS X) :
    IsDecentSpace B S hS X :=
  (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS X hX).mpr
    (hasFiniteChartAndRelationFibersAtEveryPoint_of_isReasonableSpace B S hS X hX hr)

/-! ### The point set of an open subspace as an open subspace of points -/

/-- **The map on points induced by the inclusion of an open subspace is an open embedding.**
It is continuous, injective because the inclusion is a monomorphism, and open because the
inclusion is an open immersion. -/
theorem isOpenEmbedding_pointsMap_ι {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G : Subfunctor X}
    (hG : IsOpenSubspace B S hS G) :
    Topology.IsOpenEmbedding (pointsMap B S hS G.toFunctor G.ι) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_pointsMap B S hS G.ι) (pointsMap_injective_of_mono B S hS G.ι)
    (isOpenMap_pointsMap_of_isOpenImmersion B S hS G.ι hG.2)

/-- **The generic point of an irreducible component of a representable open subspace has
codimension `0` in the ambient algebraic space.** This is the converse of
`AlgebraicGeometry.Space.mem_genericPoints_of_localRingDimension_eq_zero_of_isOpenSubspace`:
a representing scheme of the open subspace is an étale chart of the ambient space, the point
of that scheme corresponding to the given one is a generic point of an irreducible component,
and condition (2) of Stacks 0BAQ reads off the dimension. -/
theorem localRingDimension_eq_zero_of_mem_genericPoints_of_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G) (hrep : G.toFunctor.IsRepresentable)
    (x' : points B S hS G.toFunctor)
    (h : x' ∈ genericPoints (points B S hS G.toFunctor)) :
    localRingDimension B S hS (pointsMap B S hS G.toFunctor G.ι x') = 0 := by
  have : G.toFunctor.IsRepresentable := hrep
  have hc := isEtale_reprW_hom_comp_ι B S hS hG (G := G)
  have hiff := (pointsHomeomorphOfIso B S hS G.toFunctor.reprW).mem_genericPoints_iff
    ((pointsHomeomorphOfIso B S hS G.toFunctor.reprW).symm x')
  rw [pointsHomeomorphOfIso_apply, pointsMap_reprW_symm] at hiff
  have hsch : pointsToScheme B S hS G.toFunctor.reprX
      ((pointsHomeomorphOfIso B S hS G.toFunctor.reprW).symm x') ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj G.toFunctor.reprX) :=
    (schemePointsHomeomorph B S hS G.toFunctor.reprX).mem_genericPoints (hiff.1 h)
  rw [← pointsMap_reprW_symm_comp]
  exact (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX _).2
    ⟨G.toFunctor.reprX, G.toFunctor.reprW.hom ≫ G.ι, _, hc,
      chartPoint_pointsToScheme B S hS G.toFunctor.reprX _ _, hsch⟩

/-! ### Condition (1) implies condition (3) -/

/-- **Stacks 0BB9, condition (1) implies condition (3).** A decent algebraic space over `S`
whose space of points has finitely many irreducible components has a dense open subspace which
is a scheme, with finitely many irreducible components, each of whose generic points is
represented by a quasi-compact morphism from the spectrum of a field.

The dense open subscheme is Stacks 086U, in the form
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace`.
Its components are finite in number because the inclusion is an open embedding on points and
an open embedding pulls components back onto components
(`AlgebraicGeometry.finite_irreducibleComponents_of_isOpenEmbedding`), which is the
source's "taking closures sends irreducible components of `|X'|` to irreducible components of
`|X|`". The quasi-compactness of the generic-point morphisms is decency itself, with the
monomorphism condition of Stacks 03JV (4) dropped to Stacks 03JV (5). -/
@[stacks 0BB9 "condition (1) implies condition (3)"]
theorem IsDecentWithFinitelyManyComponents.hasQuasiCompactGenericDenseOpenScheme
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : IsDecentWithFinitelyManyComponents B S hS X) :
    HasQuasiCompactGenericDenseOpenScheme B S hS X := by
  obtain ⟨hdec, hfin⟩ := h
  obtain ⟨G, hG, hrep, hdense⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS hX hdec
  refine ⟨G, hG, hrep, hdense,
    finite_irreducibleComponents_of_isOpenEmbedding (pointsMap B S hS G.toFunctor G.ι)
      (isOpenEmbedding_pointsMap_ι B S hS hG) hfin, ?_⟩
  intro x' _
  obtain ⟨p, hpx, -, hqc⟩ := hdec (pointsMap B S hS G.toFunctor G.ι x')
  exact ⟨p, hpx, hqc⟩

/-! ### Condition (2) implies condition (1) -/

/-- **Condition (2) of Stacks 0BB9 makes the algebraic space reasonable.** This is Stacks 0BB8,
`AlgebraicGeometry.Space.isReasonableSpace_of_finite_irreducibleComponents_of_mono`, whose two
hypotheses are the first and third clauses of condition (2). -/
@[stacks 0BB9 "condition (2) implies the conclusion that the space is reasonable"]
theorem HasFiniteEtaleComponentsAndCodimensionZeroPoints.isReasonableSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : HasFiniteEtaleComponentsAndCodimensionZeroPoints B S hS X) :
    IsReasonableSpace B S hS X :=
  isReasonableSpace_of_finite_irreducibleComponents_of_mono B S hS X hX
    (fun U hU f hf => h.1 U f hU (isEtale_of_presheaf_etale B S hS hf))
    (fun x hx => h.2.2 x hx)

/-- **Stacks 0BB9, condition (2) implies condition (1).** Decency comes from Stacks 0BB8: the
first and third clauses of condition (2) make the space reasonable, and a reasonable algebraic
space is decent. Finiteness of the irreducible components of `|X|` comes from the second
clause together with Stacks 0BAR: the points of codimension `0` are dense, there are finitely
many of them, and so the finitely many irreducible closed sets they generate cover a dense
subset of `|X|`, which bounds the components. -/
@[stacks 0BB9 "condition (2) implies condition (1)"]
theorem HasFiniteEtaleComponentsAndCodimensionZeroPoints.isDecentWithFinitelyManyComponents
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : HasFiniteEtaleComponentsAndCodimensionZeroPoints B S hS X) :
    IsDecentWithFinitelyManyComponents B S hS X := by
  refine ⟨isDecentSpace_of_isReasonableSpace B S hS hX (h.isReasonableSpace B S hS hX), ?_⟩
  refine finite_irreducibleComponents_of_dense_sUnion
    (h.2.1.image fun x => closure ({x} : Set (points B S hS X))) ?_ ?_
  · rintro C ⟨x, -, rfl⟩
    exact isIrreducible_singleton.closure
  · refine (codimensionZeroPoints_dense B S hS hX).mono ?_
    intro x hx
    exact ⟨closure ({x} : Set (points B S hS X)), ⟨x, hx, rfl⟩, subset_closure rfl⟩

/-! ### The equivalence -/

/-- **Stacks 0BB9.** For an algebraic space `X` over a scheme `S` the three conditions are
equivalent: `X` is decent with finitely many irreducible components; every quasi-compact scheme
étale over `X` has finitely many irreducible components, there are finitely many points of
codimension `0` and each is represented by a monomorphism from the spectrum of a field; and
there is a dense open subspace which is a scheme with finitely many irreducible components
whose generic points are represented by quasi-compact morphisms. -/
@[stacks 0BB9]
theorem isDecentWithFinitelyManyComponents_tfae
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) :
    [IsDecentWithFinitelyManyComponents B S hS X,
      HasFiniteEtaleComponentsAndCodimensionZeroPoints B S hS X,
      HasQuasiCompactGenericDenseOpenScheme B S hS X].TFAE := by
  tfae_have 1 → 3 := fun h => h.hasQuasiCompactGenericDenseOpenScheme B S hS hX
  tfae_have 3 → 2 := fun h =>
    h.hasFiniteEtaleComponentsAndCodimensionZeroPoints B S hS hX
  tfae_have 2 → 1 := fun h => h.isDecentWithFinitelyManyComponents B S hS hX
  tfae_finish

/-- **Stacks 0BB9, the concluding assertion that the space is reasonable.** An algebraic space
over `S` which is decent and has finitely many irreducible components is reasonable. -/
@[stacks 0BB9 "the conclusion that the space is reasonable"]
theorem IsDecentWithFinitelyManyComponents.isReasonableSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : IsDecentWithFinitelyManyComponents B S hS X) :
    IsReasonableSpace B S hS X :=
  ((h.hasQuasiCompactGenericDenseOpenScheme B S hS
    hX).hasFiniteEtaleComponentsAndCodimensionZeroPoints B S hS hX).isReasonableSpace B S hS hX

/-- **Stacks 0BB9, the concluding assertion about generic points.** If the space of points of
an algebraic space over `S` has finitely many irreducible components and `X' ⊂ X` is an open
subspace whose point set is dense, then the generic points of the irreducible components of
`|X'|` map exactly onto the generic points of the irreducible components of `|X|`.

The inclusion is an open embedding on points, and an open embedding matches up the generic
points of its source with those of its target lying in its range; the range is all of them
because a dense open subset of a space with finitely many irreducible components contains every
generic point. -/
@[stacks 0BB9 "the conclusion identifying the generic points of the dense open subscheme"]
theorem image_genericPoints_eq_genericPoints_of_denseRange
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G : Subfunctor X} (hG : IsOpenSubspace B S hS G)
    (hdense : DenseRange (pointsMap B S hS G.toFunctor G.ι))
    (hfin : (irreducibleComponents (points B S hS X)).Finite) :
    pointsMap B S hS G.toFunctor G.ι '' genericPoints (points B S hS G.toFunctor) =
      genericPoints (points B S hS X) := by
  have hemb : Topology.IsOpenEmbedding (pointsMap B S hS G.toFunctor G.ι) :=
    isOpenEmbedding_pointsMap_ι B S hS hG
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro y ⟨t, ht, rfl⟩
    exact (mem_genericPoints_map_iff hemb t).2 ht
  · intro y hy
    obtain ⟨t, rfl⟩ : y ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) :=
      mem_of_mem_genericPoints_of_dense hemb.isOpen_range hdense hfin hy
    exact ⟨t, (mem_genericPoints_map_iff hemb t).1 hy, rfl⟩

end AlgebraicGeometry.Space

end
