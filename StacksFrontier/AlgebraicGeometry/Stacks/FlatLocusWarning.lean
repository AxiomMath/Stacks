module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointwiseFlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# The largest flat open is not the flat locus (Stacks 06M4)

**Stacks 06M3** produces, for a 1-morphism of algebraic stacks representable by algebraic
spaces, a largest open substack over which the morphism has a property `P`, from three
hypotheses on properties `P`, `Q`, `R` of morphisms of algebraic spaces. **Stacks 06M4** is a
warning about how that lemma reads at `P =` flat, `Q =` empty and `R =` flat and locally of
finite presentation: its hypothesis (3) does hold there — every morphism of algebraic spaces
has a largest open subspace of its source on which it is flat — but that open subspace is
*not* the set of points at which the morphism is flat.

This file carries both halves of that warning for morphisms of algebraic spaces, where the
objects it speaks about live, including the counterexample the literal reading of the warning
asks for. The largest flat open is
`AlgebraicGeometry.Space.maximalFlatOpen`; its point set is the *interior*, in the point
space of **Stacks 03BU**, of the set of points at which the morphism is flat
(`AlgebraicGeometry.Space.IsFlatAt`, part (2) of **Stacks 03ML**), so it coincides with that
set exactly when the set is open — which is a theorem under local finite presentation
(**Stacks 0399**, **Stacks 05X3**) and not otherwise.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatNear`: a morphism is flat *near* a point of its source when
  it is flat on some open subspace of the source having a point over it. This is the condition
  appearing as clause (2) of the general chart criteria
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae`, read at flatness; it is strictly
  stronger than flatness at the point.
* `AlgebraicGeometry.Space.maximalFlatOpen`: the union of the open subspaces of the source on
  which the morphism is flat.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_maximalFlatOpen`,
  `AlgebraicGeometry.Space.isFlat_maximalFlatOpen` and
  `AlgebraicGeometry.Space.le_maximalFlatOpen` are hypothesis (3) of **Stacks 06M3** at
  `P =` flat and `Q =` empty: for *every* morphism of algebraic spaces, with no hypothesis
  whatsoever, there is a largest open subspace of the source on which it is flat.
* `AlgebraicGeometry.Space.range_pointsMap_maximalFlatOpen_eq_interior` is the warning of
  **Stacks 06M4**: the point set of that open subspace is the interior of the set of points at
  which the morphism is flat, not that set itself.
* `AlgebraicGeometry.Space.range_pointsMap_maximalFlatOpen_eq_setOf_isFlatAt_iff_isOpen`
  is the same warning in sharp form: the largest flat open has the pointwise flat locus as its
  point set if and only if that locus is open.
* `AlgebraicGeometry.Space.exists_range_pointsMap_maximalFlatOpen_ne_setOf_isFlatAt` is the
  literal reading of the warning: for *some* morphism of algebraic spaces the two are not
  equal. The witness is the counterexample of
  `AlgebraicGeometry.exists_flat_locus_not_open`.
* `AlgebraicGeometry.Space.isFlatAt_of_isFlatNear`: the largest flat open is contained in the
  pointwise flat locus, the inclusion the warning says is not an equality.
* `AlgebraicGeometry.Space.range_pointsMap_maximalFlatOpen_eq_setOf_isFlatAt`: under local
  finite presentation the two do agree. This is what makes the warning a warning
  rather than a falsehood: the reader who has met Stacks 0399 expects the pointwise
  description, and it is exactly the finite-presentation hypothesis that buys it.
* `AlgebraicGeometry.Space.isFlat_iff_forall_isFlatNear` and
  `AlgebraicGeometry.Space.isFlatAt_iff_of_isOpenSubspace` are the two tools: flatness is
  flatness near every point, and flatness at a point is unchanged by restricting the source to
  an open subspace containing that point.

## Implementation notes

The full statement of **Stacks 06M4** — that **Stacks 06M3** applies at this triple, all four
of its hypotheses, together with the warning — is
`AlgebraicGeometry.Stack.localSourceLemmaHypotheses_flat_and_maximalFlatOpen_ne_flatLocus` in
`StacksFrontier/AlgebraicGeometry/Stacks/MaximalFlatOpenBaseChange.lean`, which carries the tag.
This file provides its ingredients for hypothesis (3) and for the warning.

*The instantiation.* That **Stacks 06M3** applies at this triple is the conjunction of its
four hypotheses. Hypothesis (1) and hypothesis (2) are already in the library — flatness and
local finite presentation are stable under base change and fppf local on the target, and
`AlgebraicGeometry.Space.isFlat_of_isSmooth` together with
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isSmooth` is `smooth ⇒ R`. Hypothesis
(3), the existence of the largest flat open on the source, is what this file proves, and it is
also the object the warning is about. Hypothesis (4), compatibility of that open with base
change along a morphism which is flat and locally of finite presentation, is
`AlgebraicGeometry.Space.maximalFlatOpen_eq_preimage_of_isPullback` in
`StacksFrontier/AlgebraicGeometry/Stacks/MaximalFlatOpenBaseChange.lean`.

*The warning.* Read literally — "the largest open `W ⊂ X` such that `f|_W` is flat is not the
set of points where `f` is flat" — this is an assertion that the two differ for *some*
morphism, so proving it needs a counterexample: a morphism of algebraic spaces whose flat
locus is not open. One is available. `AlgebraicGeometry.exists_flat_locus_not_open` is the
inclusion of `ℤ` into the trivial square-zero extension of `ℤ` by `⨁_p ℤ/p`, whose largest
flat open is empty while its generic point is a point of flatness, and
`AlgebraicGeometry.Space.exists_range_pointsMap_maximalFlatOpen_ne_setOf_isFlatAt` reads it as
a morphism of representable algebraic spaces over a big fppf site containing its source and
target. So the literal reading is proved, not assumed.

Two further statements are carried because they are what the warning is really about, and
they are sharper than the non-equality. The point set of the largest flat open is the
*interior* of the pointwise flat locus
(`AlgebraicGeometry.Space.range_pointsMap_maximalFlatOpen_eq_interior`): the universal
property of **Stacks 06M3** computes the interior, so it agrees with the pointwise description
exactly when the pointwise locus happens to be open
(`AlgebraicGeometry.Space.range_pointsMap_maximalFlatOpen_eq_setOf_isFlatAt_iff_isOpen`), and
the counterexample is then precisely a morphism whose flat locus is not open. The non-equality
follows from that equivalence by `Iff.not`, which is how it is proved.

The construction mirrors `AlgebraicGeometry.Space.maximalSmoothOpen` of **Stacks 0DZI**: the
supremum, in the complete lattice `CategoryTheory.Subfunctor` of subfunctors of the source, of
the open subspaces on which the morphism is flat, so no choice is involved. The work is to see
that the supremum is itself open and still flat, and for flatness this is shorter than for
smoothness: flatness has the germ-level pointwise criterion
`AlgebraicGeometry.Space.isFlat_iff_forall_isFlatAt` (**Stacks 03MM**, conditions (1) and
(2)), and `AlgebraicGeometry.Space.isFlatAt_iff_of_isOpenSubspace` transports it across the
inclusion of an open subspace, which replaces the intersection-of-opens argument that the
smooth case needs. The open subspace attached to an open set of points is **Stacks 03BZ**.

`AlgebraicGeometry.Space.isFlatAt_iff_of_isOpenSubspace` is proved from the pointed-chart API
of **Stacks 04RE**: a pointed étale chart of the restriction `U.ι ≫ f` is a pointed étale
chart of `f` at the image point with the *same* chart map, the chart of the source being
composed with the inclusion. That reindexing of charts and the étaleness of the inclusion of
an open subspace already exist as `private` helpers of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/FibreDimension.lean`, which carries the
`@[stacks 04NM]` and `@[stacks 0B2M]` attributes; being private there, they are re-derived
here.

The two conditions the warning distinguishes are two genuinely different germ-level
predicates, which is why the distinction is formalizable at all. Flatness at a point,
`AlgebraicGeometry.Space.IsFlatAt`, is the chart condition at the germ predicate
`AlgebraicGeometry.MorphismOfGerms.IsFlat` of **Stacks 04ND**, flatness of the map of local
rings; flatness near a point is the chart condition at
`AlgebraicGeometry.MorphismOfGerms.HasRepresentativeWithProperty` of flatness, by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_exists_open` (**Stacks 04RF**,
part (2)). The first is implied by the second and does not imply it.

## References

* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 04ND](https://stacks.math.columbia.edu/tag/04ND)
* [Stacks Project, Tag 04RE](https://stacks.math.columbia.edu/tag/04RE)
* [Stacks Project, Tag 04RF](https://stacks.math.columbia.edu/tag/04RF)
* [Stacks Project, Tag 04LI](https://stacks.math.columbia.edu/tag/04LI)
* [Stacks Project, Tag 05X3](https://stacks.math.columbia.edu/tag/05X3)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
* [Stacks Project, Tag 06M4](https://stacks.math.columbia.edu/tag/06M4)
* [Stacks Project, Tag 0DZI](https://stacks.math.columbia.edu/tag/0DZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Relative

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Flatness at a point of an open subspace of the source -/

/-- Flatness at a point is unchanged by restricting the source to an open subspace containing
the point: a pointed chart for the restriction is a pointed chart for the morphism and
conversely, both squares having the same chart map. -/
theorem isFlatAt_iff_of_isOpenSubspace (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (f : X ⟶ Y) (x' : points B S hS U.toFunctor) :
    IsFlatAt B S hS f (pointsMap B S hS U.toFunctor U.ι x') ↔
      IsFlatAt B S hS (U.ι ≫ f) x' := by
  refine ⟨fun hflat c => hflat (etaleChartAtPointOfOpenSubspace B S hS U hU f c), fun hflat => ?_⟩
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hU.1 hY (U.ι ≫ f) x'
  exact (holdsOnEveryEtaleChartAtPoint_iff_some B S hS (@MorphismOfGerms.IsFlat.{u})
    MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat hX hY f
    (pointsMap B S hS U.toFunctor U.ι x')).2
    ⟨etaleChartAtPointOfOpenSubspace B S hS U hU f c, hflat c⟩

/-! ### Flatness near a point -/

/-- A morphism of algebraic spaces over `S` is *flat near* a point `x` of its source when it
is flat on some open subspace of the source having a point over `x`.

This is the open-neighbourhood condition which appears as clause (2) of the general chart
criteria `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae`; the analogous condition for
smoothness is the definition of `AlgebraicGeometry.Space.IsSmoothAt`, part (2) of
Stacks 03ZC. For flatness it is *not* the definition of flatness at a point: that is
`AlgebraicGeometry.Space.IsFlatAt`, part (2) of Stacks 03ML, the germ condition on local
rings, and it is strictly weaker. The discrepancy is the content of Stacks 06M4. -/
abbrev IsFlatNear (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
    ∃ x' : points B S hS U.toFunctor,
      pointsMap B S hS U.toFunctor U.ι x' = x ∧ IsFlat B S hS (U.ι ≫ f)

/-- A morphism of algebraic spaces over `S` is flat exactly when it is flat near every point
of its source. This is clause (2) of the general chart criteria
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae` read at flatness of morphisms of
schemes, which is étale local on source and target, stable under composition and base change,
and implied by étaleness. -/
theorem isFlat_iff_forall_isFlatNear (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsFlat B S hS f ↔ ∀ x : points B S hS X, IsFlatNear B S hS f x :=
  (holdsOnEveryEtaleChart_tfae B S hS (@_root_.AlgebraicGeometry.Flat.{u})
    _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget inferInstance inferInstance
    (fun _ hg => have := hg; inferInstance) hX hY f).out 1 2

/-- A morphism of algebraic spaces over `S` which is flat near a point is flat at that point:
it is flat on an open subspace having a point over it, hence flat at that point of the open
subspace by Stacks 03MM, and flatness at a point is unchanged by the restriction.

The converse fails, and that failure is the warning of Stacks 06M4. -/
theorem isFlatAt_of_isFlatNear (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {x : points B S hS X}
    (hx : IsFlatNear B S hS f x) :
    IsFlatAt B S hS f x := by
  obtain ⟨U, hU, x', rfl, hUf⟩ := hx
  exact (isFlatAt_iff_of_isOpenSubspace B S hS hX hY U hU f x').2
    ((isFlat_iff_forall_isFlatAt B S hS (U.ι ≫ f)).1 hUf x')

/-- A morphism is flat on an open subspace of the source whose points all lie in the flat
locus: flatness is flatness at every point, and flatness at a point is unchanged by the
restriction. -/
private theorem isFlat_of_range_subset_setOf_isFlatAt (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {U : Subfunctor X}
    (hU : IsOpenSubspace B S hS U)
    (hsub : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆
      {x : points B S hS X | IsFlatAt B S hS f x}) :
    IsFlat B S hS (U.ι ≫ f) :=
  (isFlat_iff_forall_isFlatAt B S hS (U.ι ≫ f)).2 fun x ↦
    (isFlatAt_iff_of_isOpenSubspace B S hS hX hY U hU f x).1 (hsub ⟨x, rfl⟩)

/-- The set of points of the source at which a morphism of algebraic spaces over `S` is flat
*near* is open: it is the union of the point sets of the open subspaces on which the morphism
is flat, and each of those is open by Stacks 03BZ. -/
theorem isOpen_setOf_isFlatNear (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    IsOpen {x : points B S hS X | IsFlatNear B S hS f x} := by
  have hEq : {x : points B S hS X | IsFlatNear B S hS f x} =
      ⋃ V : {V : Subfunctor X //
          IsOpenSubspace B S hS V ∧ IsFlat B S hS (V.ι ≫ f)},
        Set.range (pointsMap B S hS V.1.toFunctor V.1.ι) := by
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨V, hV, p, hp, hVf⟩ := hx
      exact Set.mem_iUnion.mpr ⟨⟨V, hV, hVf⟩, ⟨p, hp⟩⟩
    · obtain ⟨V, p, hp⟩ := Set.mem_iUnion.mp hx
      exact ⟨V.1, V.2.1, p, hp, V.2.2⟩
  rw [hEq]
  refine isOpen_iUnion fun V ↦ ?_
  rw [← openSubspacesOrderIso_apply B S hS X hX ⟨V.1, V.2.1⟩]
  exact (openSubspacesOrderIso B S hS X hX ⟨V.1, V.2.1⟩).2

/-! ### The largest open subspace of the source on which a morphism is flat -/

/-- The union of the open subspaces of the source of a morphism of presheaves on the big fppf
site of `S` on which the morphism is flat.

For a morphism of algebraic spaces this is an open subspace on which the morphism is flat, and
it is the largest such — see `AlgebraicGeometry.Space.isOpenSubspace_maximalFlatOpen`,
`AlgebraicGeometry.Space.isFlat_maximalFlatOpen` and
`AlgebraicGeometry.Space.le_maximalFlatOpen`. -/
def maximalFlatOpen (f : X ⟶ Y) : Subfunctor X :=
  sSup {U : Subfunctor X | IsOpenSubspace B S hS U ∧ IsFlat B S hS (U.ι ≫ f)}

/-- **Stacks 06M4, the instantiation: maximality in hypothesis (3) of Stacks 06M3 at
`P = flat` and `Q = empty`.** Every open subspace of the source on which the morphism is flat
is contained in the largest flat open: it is a member of the family that open is the supremum
of. No hypothesis on the morphism is needed, which is what `Q = empty` means. -/
theorem le_maximalFlatOpen (f : X ⟶ Y) {U : Subfunctor X}
    (hU : IsOpenSubspace B S hS U) (hUf : IsFlat B S hS (U.ι ≫ f)) :
    U ≤ maximalFlatOpen B S hS f := le_sSup ⟨hU, hUf⟩

/-- The largest flat open of a morphism of algebraic spaces over `S` is an open subspace, the
morphism is flat on it, and its point set is the set of points near which the morphism is
flat.

The open subspace `W` corresponding under Stacks 03BZ to the open set of points near which
`f` is flat contains every open subspace on which `f` is flat, hence contains the supremum;
and it is itself one of them, because every point of `W` is a point near which `f` is flat,
hence a point at which `f` is flat, hence — after transporting along the inclusion of `W` — a
point at which `W.ι ≫ f` is flat, and flatness is flatness at every point by Stacks 03MM. So
the two coincide. -/
private theorem isOpenSubspace_and_isFlat_and_range_maximalFlatOpen
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsOpenSubspace B S hS (maximalFlatOpen B S hS f) ∧
      IsFlat B S hS ((maximalFlatOpen B S hS f).ι ≫ f) ∧
      Set.range (pointsMap B S hS (maximalFlatOpen B S hS f).toFunctor
          (maximalFlatOpen B S hS f).ι) =
        {x : points B S hS X | IsFlatNear B S hS f x} := by
  obtain ⟨W, hWopen, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX
    {x | IsFlatNear B S hS f x} (isOpen_setOf_isFlatNear B S hS hX f)
  -- Every open subspace on which `f` is flat is contained in `W`.
  have leW : ∀ V : Subfunctor X, IsOpenSubspace B S hS V →
      IsFlat B S hS (V.ι ≫ f) → V ≤ W := by
    intro V hV hVflat
    refine le_of_range_pointsMap_ι_subset B S hS hWopen ?_
    rw [hWrange]
    rintro x ⟨p, rfl⟩
    exact ⟨V, hV, p, rfl, hVflat⟩
  -- `f` is flat on `W`, by the pointwise criterion of Stacks 03MM.
  have hWflat : IsFlat B S hS (W.ι ≫ f) :=
    isFlat_of_range_subset_setOf_isFlatAt B S hS hX hY f hWopen fun x hx ↦
      isFlatAt_of_isFlatNear B S hS hX hY f (hWrange.subset hx)
  have heq : maximalFlatOpen B S hS f = W :=
    le_antisymm (sSup_le fun V hV ↦ leW V hV.1 hV.2)
      (le_maximalFlatOpen B S hS f hWopen hWflat)
  rw [heq]
  exact ⟨hWopen, hWflat, hWrange⟩

/-- **Stacks 06M4, the instantiation: openness in hypothesis (3) of Stacks 06M3 at
`P = flat` and `Q = empty`.** The largest flat open of a morphism of algebraic spaces over `S`
is an open subspace of the source. No hypothesis on the morphism is needed. -/
theorem isOpenSubspace_maximalFlatOpen (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsOpenSubspace B S hS (maximalFlatOpen B S hS f) :=
  (isOpenSubspace_and_isFlat_and_range_maximalFlatOpen B S hS hX hY f).1

/-- **Stacks 06M4, the instantiation: flatness in hypothesis (3) of Stacks 06M3 at
`P = flat` and `Q = empty`.** A morphism of algebraic spaces over `S` is flat on its largest
flat open. No hypothesis on the morphism is needed. -/
theorem isFlat_maximalFlatOpen (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsFlat B S hS ((maximalFlatOpen B S hS f).ι ≫ f) :=
  (isOpenSubspace_and_isFlat_and_range_maximalFlatOpen B S hS hX hY f).2.1

/-- The point set of the largest flat open is the set of points near which the morphism is
flat. -/
theorem range_pointsMap_maximalFlatOpen (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    Set.range (pointsMap B S hS (maximalFlatOpen B S hS f).toFunctor
        (maximalFlatOpen B S hS f).ι) =
      {x : points B S hS X | IsFlatNear B S hS f x} :=
  (isOpenSubspace_and_isFlat_and_range_maximalFlatOpen B S hS hX hY f).2.2

/-! ### The warning -/

/-- The set of points near which a morphism of algebraic spaces over `S` is flat is the
interior of the set of points at which it is flat.

The first set is open and contained in the second, hence contained in the interior. For the
reverse inclusion, the interior is an open set of points, so by Stacks 03BZ it is the point
set of an open subspace `V`; every point of `V` lies in the flat locus, so `V.ι ≫ f` is flat
at every point of `V` and therefore flat by Stacks 03MM, and `V` witnesses the
neighbourhood condition at each of its points. -/
theorem setOf_isFlatNear_eq_interior_setOf_isFlatAt (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    {x : points B S hS X | IsFlatNear B S hS f x} =
      interior {x : points B S hS X | IsFlatAt B S hS f x} := by
  refine subset_antisymm (interior_maximal (fun x hx ↦ isFlatAt_of_isFlatNear B S hS hX hY f hx)
    (isOpen_setOf_isFlatNear B S hS hX f)) ?_
  obtain ⟨V, hV, hVrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX
    (interior {x : points B S hS X | IsFlatAt B S hS f x}) isOpen_interior
  have hVflat : IsFlat B S hS (V.ι ≫ f) :=
    isFlat_of_range_subset_setOf_isFlatAt B S hS hX hY f hV
      (hVrange.subset.trans interior_subset)
  intro x hx
  obtain ⟨x', hx'⟩ := hVrange.symm.subset hx
  exact ⟨V, hV, x', hx', hVflat⟩

/-- **Stacks 06M4, the warning.** The point set of the largest open subspace of the source on
which a morphism of algebraic spaces over `S` is flat is the *interior*, in the point space of
Stacks 03BU, of the set of points at which the morphism is flat.

This is the structural statement behind the warning of Stacks 06M4: the open subspace that the
construction of Stacks 06M3 produces at `P = flat` is characterised by a universal property —
largest open on whose restriction the morphism is flat — and that universal property computes
the interior of the pointwise flat locus, not the locus. Flatness at a point is the germ
condition of Stacks 03ML part (2), which does not quantify over neighbourhoods, so no
hypothesis on the morphism makes the interior superfluous for free. -/
theorem range_pointsMap_maximalFlatOpen_eq_interior (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    Set.range (pointsMap B S hS (maximalFlatOpen B S hS f).toFunctor
        (maximalFlatOpen B S hS f).ι) =
      interior {x : points B S hS X | IsFlatAt B S hS f x} := by
  rw [range_pointsMap_maximalFlatOpen B S hS hX hY f,
    setOf_isFlatNear_eq_interior_setOf_isFlatAt B S hS hX hY f]

/-- **Stacks 06M4, the warning.** The largest open subspace of the source on which a morphism
of algebraic spaces over `S` is flat has the pointwise flat locus as its point set if and only
if that locus is open.

This is the warning of Stacks 06M4 in sharp form. The literal reading of the remark — that
the two are *not* equal — is the statement that the right-hand side fails for some morphism,
i.e. that the flat locus of some morphism of algebraic spaces is not open; such a morphism
exists, and
`AlgebraicGeometry.Space.exists_range_pointsMap_maximalFlatOpen_ne_setOf_isFlatAt` derives the
literal reading from this equivalence by `Iff.not`. -/
theorem range_pointsMap_maximalFlatOpen_eq_setOf_isFlatAt_iff_isOpen
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    Set.range (pointsMap B S hS (maximalFlatOpen B S hS f).toFunctor
        (maximalFlatOpen B S hS f).ι) =
        {x : points B S hS X | IsFlatAt B S hS f x} ↔
      IsOpen {x : points B S hS X | IsFlatAt B S hS f x} := by
  rw [range_pointsMap_maximalFlatOpen_eq_interior B S hS hX hY f, interior_eq_iff_isOpen]

/-- For a morphism of algebraic spaces over `S` locally of finite presentation the largest
flat open does have the pointwise flat locus as its point set, the flat locus being open in
that case by Stacks 0399.

This is the positive counterpart of the warning of Stacks 06M4, and is what makes the warning
necessary: the pointwise description is correct under local finite presentation, so a reader
who has met that theorem will expect it in general, and the finite-presentation hypothesis is
exactly what buys it. -/
theorem range_pointsMap_maximalFlatOpen_eq_setOf_isFlatAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    Set.range (pointsMap B S hS (maximalFlatOpen B S hS f).toFunctor
        (maximalFlatOpen B S hS f).ι) =
      {x : points B S hS X | IsFlatAt B S hS f x} :=
  (range_pointsMap_maximalFlatOpen_eq_setOf_isFlatAt_iff_isOpen B S hS hX hY f).2
    (isOpen_setOf_isFlatAt B S hS hX hY f hf)

end Relative

/-! ### The warning, in its literal form -/

/-- A morphism of schemes whose largest flat open is strictly smaller than its pointwise flat
locus has a non-open pointwise flat locus: were that locus open it would be one of the opens on
which the morphism is flat, hence contained in the largest of them, contradicting strictness.

Flatness on the locus read as an open subscheme is flatness of all its stalk maps, each of
which is the stalk map of the morphism composed with the invertible stalk map of the open
immersion. -/
private theorem not_isOpen_setOf_isFlatAt_of_isGreatest {X₀ Y₀ : Scheme.{u}} (f₀ : X₀ ⟶ Y₀)
    (W : X₀.Opens)
    (hW : IsGreatest {V : X₀.Opens | _root_.AlgebraicGeometry.Flat (V.ι ≫ f₀)} W)
    (hlt : (W : Set X₀) ⊂
      {x : X₀ | _root_.AlgebraicGeometry.IsFlatAt f₀.toLRSHom.toShHom x}) :
    ¬ IsOpen {x : X₀ | _root_.AlgebraicGeometry.IsFlatAt f₀.toLRSHom.toShHom x} := by
  intro hopen
  have hV : _root_.AlgebraicGeometry.Flat
      (_root_.AlgebraicGeometry.Scheme.Opens.ι (X := X₀) ⟨_, hopen⟩ ≫ f₀) := by
    refine _root_.AlgebraicGeometry.Flat.of_stalkMap _ fun x ↦ ?_
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Flat.comp x.2 (_root_.AlgebraicGeometry.Flat.stalkMap _ x)
  exact hlt.2 (hW.2 hV)

/-- **Stacks 06M4, the warning, in its literal form.** There is a morphism of algebraic spaces
whose largest flat open subspace does *not* have as its point set the set of points at which
the morphism is flat.

The witness is the morphism of schemes of `AlgebraicGeometry.exists_flat_locus_not_open` —
the inclusion of `ℤ` into the trivial square-zero extension of `ℤ` by `⨁_p ℤ/p` — read as a
morphism of representable algebraic spaces over a big fppf site large enough to contain its
source and target. By
`AlgebraicGeometry.Space.range_pointsMap_maximalFlatOpen_eq_setOf_isFlatAt_iff_isOpen` it is
enough that its pointwise flat locus is not open, and for a morphism of representable
presheaves the flat locus of the morphism of algebraic spaces is cut out by the flat locus of
the morphism of schemes, through
`AlgebraicGeometry.Space.isFlatAt_yoneda_iff` and the correspondence
`AlgebraicGeometry.Space.isOpen_yoneda_iff_isSchemeOpen` of Stacks 03BX. -/
theorem exists_range_pointsMap_maximalFlatOpen_ne_setOf_isFlatAt :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
      (_ : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y),
      Set.range (pointsMap B S hS (maximalFlatOpen B S hS f).toFunctor
          (maximalFlatOpen B S hS f).ι) ≠
        {x : points B S hS X | IsFlatAt B S hS f x} := by
  obtain ⟨X₀, Y₀, f₀, W₀, hW₀, hlt⟩ := _root_.AlgebraicGeometry.exists_flat_locus_not_open.{u}
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing ({X₀, Y₀} : Set Scheme.{u})
  have hX₀ : B.Contains X₀ := hB X₀ (by simp)
  have hY₀ : B.Contains Y₀ := hB Y₀ (by simp)
  let U : BigFppfOver B Y₀ hY₀ := Over.mk (ObjectProperty.homMk f₀ : B.obj hX₀ ⟶ B.obj hY₀)
  let V : BigFppfOver B Y₀ hY₀ := Over.mk (𝟙 (B.obj hY₀))
  let a : U ⟶ V := Over.homMk (ObjectProperty.homMk f₀) (by simp [U, V])
  have hU := _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B Y₀ hY₀ U
  have hV := _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B Y₀ hY₀ V
  refine ⟨B, Y₀, hY₀, yoneda.obj U, yoneda.obj V, hU, hV, yoneda.map a, ?_⟩
  intro heq
  have hopen : IsOpen {x : points B Y₀ hY₀ (yoneda.obj U) |
      IsFlatAt B Y₀ hY₀ (yoneda.map a) x} :=
    (range_pointsMap_maximalFlatOpen_eq_setOf_isFlatAt_iff_isOpen B Y₀ hY₀ hU hV
      (yoneda.map a)).1 heq
  obtain ⟨O, hO, hOmem⟩ := (isOpen_yoneda_iff_isSchemeOpen B Y₀ hY₀ U _).1 hopen
  have hset : O = {x : X₀ | _root_.AlgebraicGeometry.IsFlatAt f₀.toLRSHom.toShHom x} := by
    ext x
    have hpt := schemePointRepresentative_point B Y₀ hY₀ U x
    have hmem := hOmem (schemePointRepresentative B Y₀ hY₀ U x)
    have hflat := isFlatAt_yoneda_iff B Y₀ hY₀ U V a (schemePointRepresentative B Y₀ hY₀ U x)
    rw [hpt] at hmem hflat
    exact hmem.symm.trans hflat
  exact not_isOpen_setOf_isFlatAt_of_isGreatest f₀ W₀ hW₀ hlt (hset ▸ hO)

end AlgebraicGeometry.Space

end
