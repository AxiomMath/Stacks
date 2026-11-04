module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionOpenness
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite

/-!
# An algebraic space locally of finite type over a one-point base

Stacks 0ACA compares five conditions on an algebraic space `X` locally of finite type over a
field `k`: that `|X|` is finite, that `|X|` is discrete, that `dim(|X|) = 0`, that
`dim(X) = 0`, and that `X ⟶ Spec(k)` is locally quasi-finite. The source asserts that the last
four are equivalent, and that the first implies them when `X` is decent. What is true is that
conditions (2), (4) and (5) are equivalent with no further hypothesis, that condition (3)
implies them once `|X|` is Kolmogorov — in particular when `X` is decent — and that condition
(1) implies them when `X` is decent; the arrow out of condition (3) in the generality the
source claims is false, and
`Stacks.Examples.DimensionVersusPointSet.exists_zeroTopologicalDimension_not_discretePoints`
is the counterexample.

This file proves the implications among them which the available library supports:
`dim(X) = 0` is *equivalent* to local quasi-finiteness, and local quasi-finiteness *implies*
that `|X|` is discrete, which in turn implies `dim(|X|) ≤ 0`. The converse implications out of
the two topological conditions are not proved here; see the implementation notes.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.locallyQuasiFinite_iff_discreteTopology_of_subsingleton`: a morphism of
  schemes locally of finite type whose target has at most one point is locally quasi-finite
  exactly when its source is discrete.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton`: over a target
  with at most one point the fibre of a morphism of schemes has the same local dimension at a
  point as the whole source does.
* `AlgebraicGeometry.Space.zero_le_dimensionAtPoint`: the dimension of an algebraic space at a
  point is nonnegative.
* `AlgebraicGeometry.Space.hasRelativeDimensionAt_zero_iff_dimensionAtPoint_eq_zero`: over a
  one-point base the relative dimension at a point is zero exactly when the dimension of the
  space at that point is zero.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_dimension_le_zero` is Stacks 0ACA,
  condition (4) equivalent to condition (5).
* `AlgebraicGeometry.Space.discreteTopology_points_of_isLocallyQuasiFinite` is Stacks 0ACA,
  condition (5) implies condition (2).
* `AlgebraicGeometry.Space.topologicalKrullDim_points_le_zero_of_discreteTopology` is Stacks
  0ACA, condition (2) implies condition (3).

## Implementation notes

The source's hypothesis is that the base is the spectrum of a field. Nothing below uses more
about it than that its underlying scheme has **at most one point**, so that is the hypothesis
taken here: `Subsingleton ((BigFppfOver.toScheme B S hS).obj k)`, which `Spec` of a field
satisfies. This is a strict generalization of the source statement, and it is what makes the
results directly applicable to the base `Spec(k)` presented by a field-valued point, where the
`Subsingleton` instance is the one of `Spec (CommRingCat.of p.carrier)`.

Two scheme-level reductions carry the one-point hypothesis. The first is that the fibre of
`h : U ⟶ V` through a point `u` is all of `U`: the preimage of `h u` is everything, so Mathlib's
`AlgebraicGeometry.Scheme.Hom.fiberHomeo` identifies the fibre with `U`, and the local
dimensions agree. Combined with `AlgebraicGeometry.Space.hasRelativeDimensionAt_pointsMap_iff`
(Tag 04NC read on one chart square) and
`AlgebraicGeometry.Space.dimensionAtPoint_eq_of_etale_chart` (Tag 04N5), this turns the
relative dimension of Tag 04NM into the absolute dimension of Tag 04N5 at the same point, and
Tag 04NV then gives the equivalence of conditions (4) and (5). The chart square used is the one
over the identity of the target, which is a chart square because the target is representable.

The second reduction is that local quasi-finiteness over a one-point base is discreteness of
the source: `AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton` asks every
fibre to be discrete, and there is only the one fibre. This is the source's chain through Tags
01T6, 0397 and 0AAX, which Mathlib carries as
`AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero` and its `DiscreteTopology`
instance. Discreteness then passes from an étale atlas to `|X|` because the atlas is open and
surjective on points, Tag 03BX clause (3).

**What is not proved.** The implications from condition (2) or (3) back to condition (4) or (5)
are not here. The source obtains them from the transcendence-degree argument: a nontrivial
specialization `u ⇝ u'` in a chart `U` strictly drops the transcendence degree over `k`, so the
two points have distinct images in `|X|`, and that contradicts discreteness of `|X|` or
`dim(|X|) = 0`. The strict drop is the missing input; the étale invariance of the local
dimension (Tag 04N4) is not a substitute for it, because the local dimension is constant along
a specialization inside one irreducible component. Condition (1) for a decent space IS now treated,
  at
`AlgebraicGeometry.Space.discreteTopology_points_of_finite_of_isDecentSpace`
(`Spaces/DimensionZeroOverFieldDecent.lean:111`), by way of Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace` and the `Finite` + `JacobsonSpace`
discreteness instance. Both Tag 03JU (`Spaces/RelationFibreTransfer.lean:371,404`) and Tag 03JV
(`Spaces/QuasiCompactPointsFiniteFibres.lean:161,241,277`) are proved here.

`AlgebraicGeometry.Space.dimension` of Tag 04N6 is a supremum in `WithBot ℕ∞`, so an algebraic
space with no points has dimension `⊥` and not `0`. The empty space is discrete and locally
quasi-finite over any base, so the equivalence of conditions (4) and (5) is false in the `= 0`
form and is stated here as `dimension B S hS X hX ≤ 0`; the `= 0` form is recovered under a
nonemptiness hypothesis in
`AlgebraicGeometry.Space.dimension_eq_zero_of_isLocallyQuasiFinite`. The same convention makes
condition (3) an inequality here.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 0397](https://stacks.math.columbia.edu/tag/0397)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 0AAX](https://stacks.math.columbia.edu/tag/0AAX)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### Two reductions over a one-point base, at the level of schemes -/

/-- The local dimension of a subspace which is the whole space, read at a point of it. -/
private theorem topologicalKrullDimAt_subtype_of_eq_univ {T : Type*} [TopologicalSpace T]
    {s : Set T} (hs : s = Set.univ) (t : T) (ht : t ∈ s) :
    topologicalKrullDimAt s ⟨t, ht⟩ = topologicalKrullDimAt T t := by
  subst hs
  exact topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.Set.univ T) ⟨t, ht⟩

/-- **The fibre over a one-point base is the whole source.** If the target of a morphism of
schemes has at most one point, then the local dimension of the fibre through a point of the
source equals the local dimension of the source there.

The preimage of the image point is everything, and
`AlgebraicGeometry.Scheme.Hom.fiberHomeo` identifies the fibre with that preimage. -/
theorem topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton {U V : Scheme.{u}} (h : U ⟶ V)
    [Subsingleton V] (u : U) :
    topologicalKrullDimAt (h.fiber (h u)) (h.asFiber u) = topologicalKrullDimAt U u := by
  rw [topologicalKrullDimAt_fiber_asFiber_eq_preimage]
  exact topologicalKrullDimAt_subtype_of_eq_univ
    (Set.eq_univ_of_forall fun w ↦ Subsingleton.elim (h w) (h u)) u _

/-- **Local quasi-finiteness over a one-point base is discreteness.** A morphism of schemes
locally of finite type whose target has at most one point is locally quasi-finite exactly when
its source is a discrete topological space.

This is the source's chain "locally of finite type over a field is locally Noetherian, of
dimension zero, hence a disjoint union of spectra of Artinian local rings, hence discrete"
(Tags 01T6, 0397, 0AAX), packaged by Mathlib as
`AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton`: there is only one
fibre, and it is the whole source. -/
@[ega "II 6.1.7" "special case"]
theorem locallyQuasiFinite_iff_discreteTopology_of_subsingleton {U V : Scheme.{u}} (h : U ⟶ V)
    [Subsingleton V] [LocallyOfFiniteType h] :
    LocallyQuasiFinite h ↔ DiscreteTopology U := by
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  constructor
  · intro hd
    rcases isEmpty_or_nonempty U with hU | hU
    · exact ⟨Subsingleton.elim _ _⟩
    obtain ⟨u⟩ := hU
    have heq : (h : U → V) ⁻¹' {h u} = Set.univ :=
      Set.eq_univ_of_forall fun w ↦ Subsingleton.elim (h w) (h u)
    have hdisc := isDiscrete_iff_discreteTopology.1 (hd (h u))
    rw [heq] at hdisc
    exact (Homeomorph.Set.univ U).symm.isEmbedding.discreteTopology
  · intro hd x
    rw [isDiscrete_iff_discreteTopology]
    infer_instance

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {k : BigFppfOver B S hS}

/-! ### The chart square over the identity of a representable base -/

/-- The identity of a representable base is étale in the sense of the étale presheaf property. -/
private theorem presheaf_etale_id_yoneda (k : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj k)) := by
  have := isMultiplicative_presheaf_etale B S hS
  exact MorphismProperty.id_mem _ _

/-- A morphism between representables is the Yoneda image of its preimage, up to the identity. -/
private theorem yoneda_map_preimage_comp_id {U k : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ yoneda.obj k) :
    yoneda.map (yoneda.preimage f) ≫ 𝟙 (yoneda.obj k) = f := by
  rw [Category.comp_id, yoneda.map_preimage]

/-! ### The dimension at a point is nonnegative -/

/-- The dimension of an algebraic space at one of its points is nonnegative: it is the local
dimension of an étale scheme chart at a point above it, and a local dimension is never `⊥`. -/
theorem zero_le_dimensionAtPoint (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) :
    0 ≤ dimensionAtPoint B S hS X hX x := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS X hX x
  rw [dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a ha p hp]
  exact topologicalKrullDimAt_nonneg _

/-! ### Conditions (4) and (5): dimension zero and local quasi-finiteness -/

/-- **Over a one-point base the relative dimension is the absolute dimension.** For a morphism
`g : X ⟶ Spec(k)` of algebraic spaces over `S` whose target is representable by a scheme with
at most one point, the relative dimension of Tag 04NM at a point `x` is zero exactly when the
dimension of Tag 04N5 of `X` at `x` is zero.

Both sides are read on one étale scheme chart at `x`: the relative one by
`AlgebraicGeometry.Space.hasRelativeDimensionAt_pointsMap_iff`, the absolute one by
`AlgebraicGeometry.Space.dimensionAtPoint_eq_of_etale_chart`, and the two agree because the
fibre of the chart morphism is the whole chart. -/
theorem hasRelativeDimensionAt_zero_iff_dimensionAtPoint_eq_zero
    (hX : IsAlgebraicSpace B S hS X)
    (hk : Subsingleton ((BigFppfOver.toScheme B S hS).obj k)) (g : X ⟶ yoneda.obj k)
    (x : points B S hS X) :
    HasRelativeDimensionAt 0 B S hS g x ↔ dimensionAtPoint B S hS X hX x = 0 := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS X hX x
  have hcl : (pointsEquivScheme B S hS U).symm (schemePoint B S hS U p) =
      p.class B S hS (yoneda.obj U) :=
    (pointsEquivScheme B S hS U).symm_apply_eq.2 rfl
  have hx : x = pointsMap B S hS (yoneda.obj U) a
      ((pointsEquivScheme B S hS U).symm (schemePoint B S hS U p)) := by
    rw [hcl]
    exact hp.symm
  rw [dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a ha p hp, hx,
    hasRelativeDimensionAt_pointsMap_iff B S hS 0 g U k a (𝟙 (yoneda.obj k))
      (yoneda.preimage (a ≫ g)) ha (presheaf_etale_id_yoneda B S hS k)
      (yoneda_map_preimage_comp_id B S hS _) (schemePoint B S hS U p),
    topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton]
  exact Iff.rfl

/-- **Stacks 0ACA, condition (4) is equivalent to condition (5).** An algebraic space over `S`
locally of finite type over a representable base whose scheme has at most one point has
dimension at most zero exactly when the structure morphism is locally quasi-finite.

The source states condition (4) as `dim(X) = 0`; the dimension of Tag 04N6 is a supremum in
`WithBot ℕ∞`, so the empty space has dimension `⊥` while being locally quasi-finite over any
base, and the faithful unconditional form of the equivalence is therefore the inequality. See
`AlgebraicGeometry.Space.dimension_eq_zero_of_isLocallyQuasiFinite` for the `= 0` form. -/
@[stacks 0ACA "unconditional part (2) <=> (4) <=> (5): the arrow (4) <=> (5), dim <= 0 form",
  ega "IV 4.1.2" "(ii), case Y = Spec(k)"]
theorem isLocallyQuasiFinite_iff_dimension_le_zero (hX : IsAlgebraicSpace B S hS X)
    (hk : Subsingleton ((BigFppfOver.toScheme B S hS).obj k)) (g : X ⟶ yoneda.obj k)
    (hg : IsLocallyOfFiniteType B S hS g) :
    IsLocallyQuasiFinite B S hS g ↔ dimension B S hS X hX ≤ 0 := by
  rw [isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS g hg, iSup_le_iff]
  refine forall_congr' fun x ↦ ?_
  rw [hasRelativeDimensionAt_zero_iff_dimensionAtPoint_eq_zero B S hS hX hk g x]
  exact ⟨le_of_eq, fun h ↦ le_antisymm h (zero_le_dimensionAtPoint B S hS hX x)⟩

/-- **Stacks 0ACA, condition (5) implies condition (4).** The `= 0` form of the dimension
statement, which needs the space to have a point: the dimension of Tag 04N6 is a supremum, so
the empty space has dimension `⊥`. -/
@[stacks 0ACA "(2) <=> (4) <=> (5), the dim = 0 form: (5) => (4) for a nonempty space"]
theorem dimension_eq_zero_of_isLocallyQuasiFinite (hX : IsAlgebraicSpace B S hS X)
    (hk : Subsingleton ((BigFppfOver.toScheme B S hS).obj k)) (g : X ⟶ yoneda.obj k)
    (hg : IsLocallyOfFiniteType B S hS g) (hqf : IsLocallyQuasiFinite B S hS g)
    (hne : Nonempty (points B S hS X)) :
    dimension B S hS X hX = 0 :=
  le_antisymm ((isLocallyQuasiFinite_iff_dimension_le_zero B S hS hX hk g hg).mp hqf)
    (le_iSup_of_le hne.some (zero_le_dimensionAtPoint B S hS hX _))

/-- An algebraic space of dimension zero has a point: the dimension of Tag 04N6 is a supremum
over its points, and an empty supremum in `WithBot ℕ∞` is `⊥`. -/
theorem nonempty_points_of_dimension_eq_zero (hX : IsAlgebraicSpace B S hS X)
    (hdim : dimension B S hS X hX = 0) : Nonempty (points B S hS X) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  rw [show dimension B S hS X hX = ⊥ from iSup_of_empty _] at hdim
  simp at hdim

/-! ### Condition (5) implies condition (2), and condition (2) implies condition (3) -/

/-- **Stacks 0ACA, condition (5) implies condition (2).** If the structure morphism of an
algebraic space over `S` to a representable base whose scheme has at most one point is locally
quasi-finite, then the point space of Tag 03BU is discrete.

An étale atlas `U ⟶ X` by a scheme gives a chart square over the identity of the base, so
`U ⟶ Spec(k)` is locally quasi-finite, hence `U` is discrete; and `|U| → |X|` is open and
surjective on points, so each singleton of `|X|` is the image of a singleton of `|U|`. -/
@[stacks 0ACA "unconditional part (2) <=> (4) <=> (5): the arrow (5) => (2)"]
theorem discreteTopology_points_of_isLocallyQuasiFinite (hX : IsAlgebraicSpace B S hS X)
    (hk : Subsingleton ((BigFppfOver.toScheme B S hS).obj k)) (g : X ⟶ yoneda.obj k)
    (hqf : IsLocallyQuasiFinite B S hS g) :
    DiscreteTopology (points B S hS X) := by
  obtain ⟨U, a, hasurj, ha⟩ := hX.exists_atlas
  obtain ⟨hft, hlqf⟩ := hqf U k a (𝟙 (yoneda.obj k)) (yoneda.preimage (a ≫ g)) ha
    (presheaf_etale_id_yoneda B S hS k) (yoneda_map_preimage_comp_id B S hS _)
  have hdU : DiscreteTopology ((BigFppfOver.toScheme B S hS).obj U) :=
    (locallyQuasiFinite_iff_discreteTopology_of_subsingleton
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g)))).mp hlqf
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    isSurjective_of_presheafSurjective B S hS a hasurj
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  obtain ⟨w, rfl⟩ := hsurj x
  have hw : @IsOpen _ (pointTopology B S hS (yoneda.obj U)) {w} := by
    rw [isOpen_pointTopology_yoneda_iff_isOpen_image]
    exact Set.image_singleton ▸ isOpen_discrete _
  have := isOpenMap_pointsMap_of_presheafEtale B S hS a ha {w} hw
  rwa [Set.image_singleton] at this

/-- **Stacks 0ACA, condition (2) implies condition (3).** A discrete point space has dimension
at most zero. The source writes condition (3) as `dim(|X|) = 0`; the empty space is discrete and
has dimension `⊥`, so the unconditional form is the inequality. -/
@[stacks 0ACA "the arrow into (3): (2) => (3), unconditional, dim <= 0 form"]
theorem topologicalKrullDim_points_le_zero_of_discreteTopology
    (h : DiscreteTopology (points B S hS X)) :
    topologicalKrullDim (points B S hS X) ≤ 0 :=
  have := h
  topologicalKrullDim_zero_of_discreteTopology _

end Space

end AlgebraicGeometry

end
