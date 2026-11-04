module

public import StacksFrontier.AlgebraicGeometry.Size.AtlasOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# Density of the schematic locus

Tag 086U, Rydh's theorem, says that a decent algebraic space over a scheme has a dense open
subspace which is a scheme. This file proves the step of that argument which turns a *local*
supply of schematic open subspaces into a *global* dense one: if every nonempty open set of
points of `X` contains the point set of a nonempty representable open subspace, then the
largest representable open subspace of `X` — the schematic locus of Tag 03JH,
`AlgebraicGeometry.Space.schematicLocus` — is dense in the point topology of Tag 03BX.

This is the reduction with which the source opens, and it is the reason the source may
assume, after replacing `X` by an open subspace disjoint from the schematic locus, that `X`
has *no* nonempty representable open subspace at all, and then derive a contradiction.

Everything else in the file strips hypotheses off that reduction, until the only unproved input
left is `hnonempty`, the local nonemptiness statement described in the implementation notes
below. In particular the size obligation of Tag 03JH is discharged here, for an
algebraic space: the scheme representing an open subspace receives a surjective étale morphism
from an open subscheme of an étale atlas, and such a morphism bounds the size of its *target*,
so one cardinal built from the atlas bounds every representing object at once. With that bound
and the smallness of the family of open subspaces, the glueing which produces the schematic
locus takes place inside the site and Tag 01JJ is not needed either.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_ι_le`: the point set of a subspace grows with the
  subspace.
* `AlgebraicGeometry.Space.range_pointsMap_ι_le_schematicLocus`: the point set of a
  representable open subspace is contained in the point set of the schematic locus.
* `AlgebraicGeometry.Space.denseRange_pointsMap_schematicLocus_ι`: the schematic locus is
  dense on points as soon as every nonempty open set of points contains the point set of a
  nonempty representable open subspace. This is the mathematical content of the file, and it
  needs no unproved input at all.
* `AlgebraicGeometry.Space.denseRange_pointsMap_schematicLocus_ι_of_isAlgebraicSpace` is the
  same with the hypothesis in the shape the source uses it, a nonempty open *subspace*
  containing a nonempty representable one; the first part of Tag 03BZ, which converts between
  the two shapes, is `AlgebraicGeometry.Space.exists_isOpenSubspace_range_pointsMap_eq` and
  is no longer a hypothesis.
* `AlgebraicGeometry.Space.small_points` and
  `AlgebraicGeometry.Space.small_isRepresentable_isOpenSubspace`: the point set of an
  algebraic space, and its family of representable open subspaces, are small.
  `AlgebraicGeometry.Space.mk_lt_cutoff_of_injective_points` bounds the number of open
  subspaces by the site's cutoff.
* `AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_iSup_size_lt`: a third route into
  the site, asking only that the index type and the supremum of the sizes of the members be
  below the cutoff.
* `AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_contains`:
  the two unproved clauses of Tag 03JH with the cofinality hypothesis of
  `StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus` traded for the containment obligation
  of `StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCover`.
* `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace` is the
  conclusion of Tag 086U from the geometric core together with the two clauses of Tag 03JH;
  `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_contains`
  replaces those clauses by a cofinal family and the containment obligation, and
  `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_size_le`
  removes the family altogether, leaving `hnonempty` and one uniform size bound.
* `AlgebraicGeometry.Space.exists_lt_cutoff_size_le_of_isOpenSubspace`: the size obligation of
  Tag 03JH, proved — one cardinal below the site's cutoff bounds the size of every scheme
  representing an open subspace of an algebraic space. The uniform bound it feeds on is
  `AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas`, in
  `StacksFrontier.AlgebraicGeometry.Size.AtlasOpenSubspace`.
* `AlgebraicGeometry.Space.isRepresentable_sheafify_iSup_of_size_le`,
  `AlgebraicGeometry.Space.isOpenSubspace_sheafify_iSup_of_size_le`,
  `AlgebraicGeometry.Space.schematicLocus_eq_sheafify_iSup_of_size_le` and
  `AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_size_le`: the
  two clauses of Tag 03JH from the two cardinal bounds, with no appeal to Tag 01JJ.
* `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace`
  is Tag 086U for an algebraic space over `S` with `hnonempty` as its single hypothesis.

## Implementation notes

Nothing in *this file* carries the tag 086U: the results below are reductions carrying named
hypotheses, in the style of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`. The tag itself is
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace`,
in `StacksFrontier/AlgebraicGeometry/Spaces/DenseSchematicLocusDecent.lean`, which discharges the
one hypothesis these reductions leave. After the reductions that hypothesis is:

* `hnonempty`, that a nonempty open subspace of `X` contains a nonempty representable open
  subspace. This is the geometric content, and it is where decency enters the source's proof.
  It is not derivable *here*: the first part of Tag 03BZ, which was previously carried
  alongside it as `hopenSubspace`, only converts open sets of points into open subspaces and
  supplies no representable one. It is proved, for a decent space, as
  `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_nonempty_of_isDecentSpace`.

`hnonempty` carries **no tag of its own** in the source. It is not Tag 086T: that tag is the
*degree stratification* of a flat, locally finitely presented, separated, locally quasi-finite
morphism from a scheme, `X = X₀ ⊇ X₁ ⊇ X₂ ⊇ …`, with the strata detecting fibre degree. What
the source does is derive `hnonempty` for a decent space inside the proof of Tag 086U itself,
from four inputs at once: the chain of open subspaces of Tag 086T for a chosen affine étale
chart, the reasonable case Tag 03JI applied to the open subspace swept out by a chart whose
fibre degrees are bounded, the nonemptiness of the limit of a descending chain of nonempty
affines of Tag 01Z2, and decency, which forbids the resulting field-valued point from having
infinite fibre degree. So the hypothesis stands in for that whole argument, not for a single
upstream lemma, and the four tags above are what a proof of it owes.

All four inputs are now available, and `hnonempty` is proved from them in
`StacksFrontier/AlgebraicGeometry/Spaces/DenseSchematicLocusDecent.lean`.

* Tag 086T is `AlgebraicGeometry.Space.exists_antitone_isOpenSubspace_iff_fibre_degree_ge`, in
  `StacksFrontier/AlgebraicGeometry/Spaces/FibreDegreeStratification.lean`.
* Decency's contribution is
  `AlgebraicGeometry.Space.exists_not_fibre_degree_ge_of_isDecentSpace` in the same file: above
  every field-valued point of a decent algebraic space, an étale chart with quasi-compact
  source has a fibre of finite degree, so the point lies outside some member of the chain of
  Tag 086T. This is exactly the contradiction the source draws from the limit point.
* Tag 01Z2 is `AlgebraicGeometry.Scheme.nonempty_of_isLimit` in Mathlib, with the index
  universes freed in `AlgebraicGeometry.Scheme.nonempty_of_isLimit'` and the shape the argument
  consumes — a point in every member of a descending chain of nonempty affine opens — in
  `AlgebraicGeometry.Scheme.exists_mem_iInter_of_antitone_isAffineOpen`.
* Tag 03JI is
  `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isReasonableSpace`,
  and it is consumed through its corollary for a *single* bounded affine chart,
  `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_boundedAffineChart`.

That last distinction is worth keeping. Condition (1) of Tag 03JT is a **jointly surjective
family** of bounded étale charts, and a jointly surjective family need not have a surjective
member, so it does not by itself supply the one surjective chart the argument wants — even
though the implication Tag 03JT (2) ⇒ (1) is proved, as
`AlgebraicGeometry.Space.exists_boundedEtaleCover_of_isReasonableSpace` in
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableEtaleCover`. The argument therefore
manufactures its own surjective chart, by passing to the open subspace swept out by a chart —
Tag 06NF, `AlgebraicGeometry.Space.exists_isOpenSubspace_etaleImage` — where the chart becomes
surjective onto its image, and transporting the fibre bound along the monomorphic inclusion of
that image.

The two hypotheses which *were* carried alongside it are now discharged, and it is worth
being precise about how.

Tag 01JJ for the big fppf site of `S`, `AlgebraicGeometry.HasZariskiGluing`, is *proved*:
`AlgebraicGeometry.hasZariskiGluing` in
`StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover` (`ZariskiGluingCover.lean:437`)
establishes it for every big fppf site, every `S` contained in it and every index type, with
no cardinal hypothesis. Nothing in this file carries it any more; the `_of_contains` family
below reaches it through
`AlgebraicGeometry.Space.exists_representing_cover_sheafify_iSup`, which no longer carries it
either. What those statements still ask for is the *containment* of the glued scheme in the
size-bounded site, which is a genuinely separate obligation.

The glueing which produces the schematic locus needs the glued scheme to stay inside the site,
and by the open-cover bound of Tag 000Q that asks two things of the family of charts: that the
index type be small, and that the sizes of the charts be bounded. The first holds because the
family of *all* representable open subspaces is indexed by a type of the working universe — an
open subspace is determined by its point set and the point set is dominated by the étale atlas
— which is what the source obtains instead from the bijection between open subspaces and
invariant open subschemes of an atlas. The second is a statement about the *representing
objects* rather than about the subspaces, and it does not follow from the same argument: the
representing object of an open subspace receives a surjective étale morphism from an open
subscheme of the atlas, which bounds the cardinality of its point set but not the cardinality
of its rings of sections. Bounding those needs the injectivity of `𝒪(V) → 𝒪(W)` for a
surjective flat `W → V`, which is
`AlgebraicGeometry.Scheme.Hom.injective_app_of_flat_of_surjective`; with it,
`AlgebraicGeometry.Scheme.size_le_of_flat_of_surjective` bounds the size of the representing
object doubly exponentially in the size of the atlas, which is below the cutoff because the
cutoff is closed under powersets.

With both bounds available neither the cofinality route nor the containment obligation is
needed: `AlgebraicGeometry.isRepresentable_of_openCharts` glues the charts inside the big
fppf category over `S` from exactly those two bounds, and the cofinality hypothesis of
`StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus` and the containment obligation of
`StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCover` are both replaced by them. The
`_of_size_le` family of statements below is the result, and it supersedes
the `_of_contains` family, which is kept because the containment obligation is the weaker ask
when a caller has it in that shape.

The hypotheses are stated inline rather than as named predicates, because none of them is a
reusable notion: each is a statement of Tag 086U or of Tag 03JH relativized to a single `X`.
In particular the core hypothesis is strictly weaker than the conclusion — it asks
only for *nonemptiness* inside each open set of points, not for density in `X` — which is what
makes this a reduction rather than a restatement.

Decency is not among the hypotheses, although Tag 086U assumes it: the reduction never uses
it, because everything decency is there to supply is already inside the core hypothesis.
Carrying it abstractly also makes the reduction usable for the reasonable case, Tag 03JI,
whose conclusion has the same shape.

The topology on the points is installed as a local instance rather than written into each
statement with `letI`, so that the statements read as ordinary `DenseRange` and `IsOpen`
assertions; the elaborated terms are the same.

## References

* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 01Z2](https://stacks.math.columbia.edu/tag/01Z2)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### A third route into the site -/

/-- A scheme covered by the images of open immersions from a family of schemes is contained
in a big fppf site as soon as the cardinality of the index type *and the supremum of the
sizes of the members* are both below the site's cutoff.

This is weaker than both hypotheses used so far, and is exactly what the open-cover bound of
Tag 000Q consumes:
`AlgebraicGeometry.BigFppfSite.contains_of_openCover` asks for `#ι < B.cutoff.ord.cof`, which
bounds the supremum by cofinality but is supplied only for countable index types, and
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_size_le` asks for one cardinal
dominating every member. Here the supremum is bounded directly, so an index type of size
below the cutoff — for instance a set of opens of one object of the site, the cutoff being a
strong prelimit cardinal — is admissible. -/
theorem BigFppfSite.contains_of_openCover_of_iSup_size_lt (B : BigFppfSite.{u})
    {Y : Scheme.{u}} {ι : Type u} [Nonempty ι] (hι : Cardinal.mk ι < B.cutoff)
    {X : ι → Scheme.{u}} (g : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hcov : ∀ y : Y, ∃ i, y ∈ Set.range (g i))
    (hX : (⨆ i, (X i).size) < B.cutoff) : B.Contains Y :=
  B.contains_of_openCover_of_size_le (max_lt hι hX) (le_max_left _ _) g hcov
    fun i => le_max_of_le_right (le_ciSup Cardinal.bddAbove_of_small i)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point set of a subspace grows with the subspace: if `G ≤ G'` then every point of `F`
coming from `G` comes from `G'`. -/
theorem range_pointsMap_ι_le {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G G' : Subfunctor F}
    (h : G ≤ G') :
    Set.range (pointsMap B S hS G.toFunctor G.ι) ⊆
      Set.range (pointsMap B S hS G'.toFunctor G'.ι) := by
  rw [← Subfunctor.homOfLe_ι h, pointsMap_comp]
  exact Set.range_comp_subset_range _ _

/-- The point set of a representable open subspace is contained in the point set of the
schematic locus of Tag 03JH. -/
theorem range_pointsMap_ι_le_schematicLocus {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (G : Subfunctor F) (hG : IsOpenSubspace B S hS G)
    (hGrep : G.toFunctor.IsRepresentable) :
    Set.range (pointsMap B S hS G.toFunctor G.ι) ⊆
      Set.range (pointsMap B S hS (schematicLocus B S hS F).toFunctor
        (schematicLocus B S hS F).ι) :=
  range_pointsMap_ι_le B S hS (le_schematicLocus B S hS F G hG hGrep)

/-- **The reduction step of Tag 086U.** If every nonempty open set of points of `X` contains
the point set of a nonempty representable open subspace, then the schematic locus of
Tag 03JH is dense on points.

The hypothesis is a *local* nonemptiness statement and the conclusion is a global density
statement, so this is where the source's "largest schematic open subspace" argument happens.
Nothing unproved is used: the schematic locus and its maximality are available, and the
point topology of Tag 03BX is an explicit construction. -/
theorem denseRange_pointsMap_schematicLocus_ι {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hcore : ∀ W : Set (points B S hS X), IsOpen W → W.Nonempty →
      ∃ H : Subfunctor X, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        Set.range (pointsMap B S hS H.toFunctor H.ι) ⊆ W ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty) :
    DenseRange (pointsMap B S hS (schematicLocus B S hS X).toFunctor
      (schematicLocus B S hS X).ι) := by
  refine dense_iff_inter_open.2 fun W hWopen hWne ↦ ?_
  obtain ⟨H, hH, hHrep, hHsub, x, hx⟩ := hcore W hWopen hWne
  exact ⟨x, hHsub hx, range_pointsMap_ι_le_schematicLocus B S hS H hH hHrep hx⟩

/-- The hypothesis of `AlgebraicGeometry.Space.denseRange_pointsMap_schematicLocus_ι`, from
the two inputs in the shape the source of Tag 086U uses them: the first part of Tag 03BZ,
that an open set of points is the point set of an open subspace, and the statement that a
nonempty open subspace contains a nonempty representable open subspace. -/
theorem exists_isRepresentable_isOpenSubspace_range_subset
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hopenSubspace : ∀ W : Set (points B S hS X), IsOpen W →
      ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧
        Set.range (pointsMap B S hS G.toFunctor G.ι) = W)
    (hnonempty : ∀ G : Subfunctor X, IsOpenSubspace B S hS G →
      (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty →
      ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧
        H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty)
    (W : Set (points B S hS X)) (hWopen : IsOpen W) (hWne : W.Nonempty) :
    ∃ H : Subfunctor X, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
      Set.range (pointsMap B S hS H.toFunctor H.ι) ⊆ W ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  obtain ⟨G, hG, hGrange⟩ := hopenSubspace W hWopen
  obtain ⟨H, hHle, hH, hHrep, hHne⟩ := hnonempty G hG (by rw [hGrange]; exact hWne)
  exact ⟨H, hH, hHrep, hGrange ▸ range_pointsMap_ι_le B S hS hHle, hHne⟩

/-- The hypothesis of `AlgebraicGeometry.Space.denseRange_pointsMap_schematicLocus_ι` for an
algebraic space, from the single input that a nonempty open subspace contains a nonempty
representable open subspace.

The first part of Tag 03BZ is no longer a hypothesis: for an algebraic space it is
`AlgebraicGeometry.Space.exists_isOpenSubspace_range_pointsMap_eq`, which is proved
unconditionally. So the geometric core `hcore` of Tag 086U is *equivalent*, over an algebraic
space, to the local nonemptiness statement `hnonempty`, which carries no tag of its own; see
the implementation notes of this file for what a proof of it owes. -/
theorem exists_isRepresentable_isOpenSubspace_range_subset_of_isAlgebraicSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hnonempty : ∀ G : Subfunctor X, IsOpenSubspace B S hS G →
      (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty →
      ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧
        H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty)
    (W : Set (points B S hS X)) (hWopen : IsOpen W) (hWne : W.Nonempty) :
    ∃ H : Subfunctor X, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
      Set.range (pointsMap B S hS H.toFunctor H.ι) ⊆ W ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty :=
  exists_isRepresentable_isOpenSubspace_range_subset B S hS
    (fun W' hW' => exists_isOpenSubspace_range_pointsMap_eq B S hS hX W' hW')
    hnonempty W hWopen hWne

/-- The schematic locus of an algebraic space is dense on points as soon as every nonempty
open subspace contains a nonempty representable open subspace.

This is `AlgebraicGeometry.Space.denseRange_pointsMap_schematicLocus_ι` with its hypothesis
replaced by the input the source of Tag 086U actually produces, the first part of Tag 03BZ
being discharged. -/
theorem denseRange_pointsMap_schematicLocus_ι_of_isAlgebraicSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hnonempty : ∀ G : Subfunctor X, IsOpenSubspace B S hS G →
      (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty →
      ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧
        H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty) :
    DenseRange (pointsMap B S hS (schematicLocus B S hS X).toFunctor
      (schematicLocus B S hS X).ι) :=
  denseRange_pointsMap_schematicLocus_ι B S hS
    (exists_isRepresentable_isOpenSubspace_range_subset_of_isAlgebraicSpace B S hS hX hnonempty)

/-- An algebraic space over `S` with a point has a representable open subspace, as soon as
every nonempty open subspace contains one: apply the hypothesis to the whole point set, which
is the point set of an open subspace by the first part of Tag 03BZ. -/
theorem exists_isRepresentable_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hpt : (Set.univ : Set (points B S hS X)).Nonempty)
    (hnonempty : ∀ G : Subfunctor X, IsOpenSubspace B S hS G →
      (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty →
      ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧
        H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable := by
  obtain ⟨H, hH, hHrep, -, -⟩ :=
    exists_isRepresentable_isOpenSubspace_range_subset_of_isAlgebraicSpace B S hS hX hnonempty
      Set.univ isOpen_univ hpt
  exact ⟨H, hH, hHrep⟩

/-! ### The representable open subspaces of an algebraic space form a small family -/

/-- The point set of an algebraic space over `S` is small: it is a quotient of a type of
field-valued points, which lives one universe up, but the atlas of Tag 025Y is surjective on
it by Tag 03MD, and the point set of a representable presheaf is the point set of the
representing scheme by `AlgebraicGeometry.Space.pointsEquivScheme`. -/
theorem small_points {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) : Small.{u} (points B S hS X) := by
  obtain ⟨U, f, hsurj, -⟩ := hX.exists_atlas
  have : Small.{u} (points B S hS (yoneda.obj U)) :=
    small_of_injective (injective_pointsToScheme B S hS U)
  exact small_of_surjective (isSurjective_of_presheafSurjective B S hS f hsurj)

/-- **Stacks 03BZ, part (1).** An open subspace of an algebraic space over `S` is determined
by its point set: both inclusions are
`AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset`. -/
theorem eq_of_range_pointsMap_ι_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G H : Subfunctor X} (hG : IsOpenSubspace B S hS G) (hH : IsOpenSubspace B S hS H)
    (h : Set.range (pointsMap B S hS G.toFunctor G.ι) =
      Set.range (pointsMap B S hS H.toFunctor H.ι)) :
    G = H :=
  le_antisymm (le_of_range_pointsMap_ι_subset B S hS hH h.le)
    (le_of_range_pointsMap_ι_subset B S hS hG h.ge)

/-- **The set-theoretic input of Stacks 03JH.** The open subspaces of an algebraic space over
`S` form a small family: an open subspace is determined by its point set, and the point set
is small.

This is what lets the schematic locus be exhibited as the union of a family indexed by a type
of the working universe, which is what the glueing of Tag 01JJ requires. The source instead
reads the open subspaces off an étale atlas, through the bijection with the invariant open
subschemes of the atlas. -/
theorem small_isOpenSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    Small.{u} {G : Subfunctor X // IsOpenSubspace B S hS G} := by
  have : Small.{u} (points B S hS X) := small_points B S hS hX
  exact small_of_injective
    (f := fun G : {G : Subfunctor X // IsOpenSubspace B S hS G} =>
      Set.range (pointsMap B S hS G.1.toFunctor G.1.ι))
    fun G H h => Subtype.ext (eq_of_range_pointsMap_ι_eq B S hS G.2 H.2 h)

/-- A type of the working universe which injects into the sets of points of an algebraic
space over `S` has cardinality below the site's cutoff.

Taking preimages along the atlas, which is surjective on points, injects the sets of points of
`X` into the sets of points of the atlas, and those number `2 ^ #U < B.cutoff`: a scheme has
at most `2 ^ size` points by `AlgebraicGeometry.Scheme.mk_le_two_pow_size`, and the cutoff is
a strong prelimit cardinal.

Applied to the point sets of open subspaces — which determine them, by
`AlgebraicGeometry.Space.eq_of_range_pointsMap_ι_eq` — this bounds the number of open
subspaces, which is the half of the size obligation of Tag 03JH that Tag 086U can
discharge. -/
theorem mk_lt_cutoff_of_injective_points {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {ι : Type u} (f : ι → Set (points B S hS X))
    (hf : Function.Injective f) : Cardinal.mk ι < B.cutoff := by
  obtain ⟨U, g, hsurj, -⟩ := hX.exists_atlas
  have he : Function.Surjective (fun x : (BigFppfOver.toScheme B S hS).obj U =>
      pointsMap B S hS (yoneda.obj U) g ((pointsEquivScheme B S hS U).symm x)) :=
    (isSurjective_of_presheafSurjective B S hS g hsurj).comp
      (pointsEquivScheme B S hS U).symm.surjective
  refine (Cardinal.mk_le_of_injective (f := fun i =>
    (fun x : (BigFppfOver.toScheme B S hS).obj U => pointsMap B S hS (yoneda.obj U) g
      ((pointsEquivScheme B S hS U).symm x)) ⁻¹' f i)
    fun a b h => hf (Set.preimage_injective.2 he h)).trans_lt ?_
  rw [Cardinal.mk_set]
  exact B.cutoff_isStrongPrelimit
    (((BigFppfOver.toScheme B S hS).obj U).mk_le_two_pow_size.trans_lt
      (B.cutoff_isStrongPrelimit U.left.property))

/-- The representable open subspaces of an algebraic space over `S` form a small family. -/
theorem small_isRepresentable_isOpenSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    Small.{u} {G : Subfunctor X //
      IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable} := by
  have : Small.{u} (points B S hS X) := small_points B S hS hX
  exact small_of_injective
    (f := fun G : {G : Subfunctor X //
        IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable} =>
      Set.range (pointsMap B S hS G.1.toFunctor G.1.ι))
    fun G H h => Subtype.ext (eq_of_range_pointsMap_ι_eq B S hS G.2.1 H.2.1 h)

/-! ### The two clauses of Tag 03JH without the cofinality hypothesis -/

/-- The sheafification of a union of representable open subspaces is representable, with the
cofinality hypothesis of `AlgebraicGeometry.Space.isRepresentable_sheafify_iSup` replaced by
the containment obligation of
`AlgebraicGeometry.exists_representing_cover_of_zariskiCover`: any scheme covered by open
immersions from the representing objects of the members is contained in the site.

The point of the exchange is that the cofinality bound `#ι < B.cutoff.ord.cof` is supplied
only for countable index types, whereas the family of representable open subspaces of an
algebraic space is indexed by invariant opens of an étale atlas. The containment obligation
is implied by `Cardinal.mk ι < B.cutoff` together with a bound on the supremum of the sizes
of the representing objects, through
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_iSup_size_lt`. -/
theorem isRepresentable_sheafify_iSup_of_contains
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable)
    (hcontains : ∀ T : ι → BigFppfOver B S hS,
      (∀ i, Nonempty (yoneda.obj (T i) ≅ (X i).toFunctor)) → ∀ (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (T i) ⟶ Z),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z) :
    ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor.IsRepresentable := by
  obtain ⟨Y, e, -⟩ :=
    exists_representing_cover_sheafify_iSup B S hS hF X hXopen hXrep hcontains
  exact Functor.IsRepresentable.mk' e.symm

/-- The sheafification of a union of open subspaces is an open subspace once it is
representable. -/
private theorem isOpenSubspace_sheafify_iSup_of_isRepresentable
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    [((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor.IsRepresentable] :
    IsOpenSubspace B S hS ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)) :=
  ⟨(isAlgebraicSpace_yoneda B S hS _).of_iso
      ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor.reprW,
    isOpenImmersion_sheafify_iSup_ι B S hS hF X hXopen⟩

/-- If the sheafified union of a family is a representable open subspace and every
representable open subspace lies in the union, the schematic locus is the sheafified union. -/
private theorem schematicLocus_eq_sheafify_iSup_of_isOpenSubspace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ι : Type u} (X : ι → Subfunctor F)
    (hcof : ∀ G : Subfunctor F, IsOpenSubspace B S hS G → G.toFunctor.IsRepresentable →
      G ≤ ⨆ i, X i)
    (hopen : IsOpenSubspace B S hS ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)))
    (hrep : ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor.IsRepresentable) :
    schematicLocus B S hS F = (⨆ i, X i).sheafify (BigFppfOver.topology B S hS) :=
  le_antisymm
    (sSup_le fun G hG => (hcof G hG.1 hG.2).trans ((⨆ i, X i).le_sheafify _))
    (le_schematicLocus B S hS F _ hopen hrep)

/-- The sheafification of a union of representable open subspaces is an open subspace, with
the cofinality hypothesis of `AlgebraicGeometry.Space.isOpenSubspace_sheafify_iSup` replaced
by the containment obligation.

Openness of the inclusion is `AlgebraicGeometry.Space.isOpenImmersion_sheafify_iSup_ι`, which
needs no size hypothesis at all; only representability does. -/
theorem isOpenSubspace_sheafify_iSup_of_contains
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable)
    (hcontains : ∀ T : ι → BigFppfOver B S hS,
      (∀ i, Nonempty (yoneda.obj (T i) ≅ (X i).toFunctor)) → ∀ (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (T i) ⟶ Z),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z) :
    IsOpenSubspace B S hS ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)) := by
  have := isRepresentable_sheafify_iSup_of_contains B S hS hF X hXopen hXrep hcontains
  exact isOpenSubspace_sheafify_iSup_of_isRepresentable B S hS hF X hXopen

/-- If the representable open subspaces of an algebraic space are all contained in the union
of a family of them satisfying the containment obligation, then the schematic locus is that
union, sheafified.

This is `AlgebraicGeometry.Space.schematicLocus_eq_sheafify_iSup` with the cofinality
hypothesis traded for the containment obligation. -/
theorem schematicLocus_eq_sheafify_iSup_of_contains
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenSubspace B S hS (X i))
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable)
    (hcof : ∀ G : Subfunctor F, IsOpenSubspace B S hS G → G.toFunctor.IsRepresentable →
      G ≤ ⨆ i, X i)
    (hcontains : ∀ T : ι → BigFppfOver B S hS,
      (∀ i, Nonempty (yoneda.obj (T i) ≅ (X i).toFunctor)) → ∀ (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (T i) ⟶ Z),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z) :
    schematicLocus B S hS F = (⨆ i, X i).sheafify (BigFppfOver.topology B S hS) :=
  schematicLocus_eq_sheafify_iSup_of_isOpenSubspace B S hS X hcof
      (isOpenSubspace_sheafify_iSup_of_contains B S hS hF.isSheaf X
        (fun i => (hXopen i).2) hXrep hcontains)
      (isRepresentable_sheafify_iSup_of_contains B S hS hF.isSheaf X
        (fun i => (hXopen i).2) hXrep hcontains)

/-- **Stacks 03JH, openness and representability**, conditional on Tag 01JJ for the big fppf
site of `S` and on a cofinal family of representable open subspaces satisfying the
containment obligation.

This is `AlgebraicGeometry.Space.isOpenSubspace_schematicLocus` and
`AlgebraicGeometry.Space.isRepresentable_schematicLocus` with the cofinality hypothesis
`Cardinal.mk ι < B.cutoff.ord.cof` traded for the containment obligation, which is the shape
Tag 086U can hope to discharge. -/
theorem isOpenSubspace_and_isRepresentable_schematicLocus_of_contains
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenSubspace B S hS (X i))
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable)
    (hcof : ∀ G : Subfunctor F, IsOpenSubspace B S hS G → G.toFunctor.IsRepresentable →
      G ≤ ⨆ i, X i)
    (hcontains : ∀ T : ι → BigFppfOver B S hS,
      (∀ i, Nonempty (yoneda.obj (T i) ≅ (X i).toFunctor)) → ∀ (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (T i) ⟶ Z),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z) :
    IsOpenSubspace B S hS (schematicLocus B S hS F) ∧
      (schematicLocus B S hS F).toFunctor.IsRepresentable := by
  rw [schematicLocus_eq_sheafify_iSup_of_contains B S hS hF X hXopen hXrep hcof
    hcontains]
  exact ⟨isOpenSubspace_sheafify_iSup_of_contains B S hS hF.isSheaf X
      (fun i => (hXopen i).2) hXrep hcontains,
    isRepresentable_sheafify_iSup_of_contains B S hS hF.isSheaf X
      (fun i => (hXopen i).2) hXrep hcontains⟩

/-- The containment obligation of
`AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_contains` from
the two cardinal facts it is really made of: the index type has cardinality below the cutoff,
and the sizes of the representing objects of the members have supremum below the cutoff.

For Tag 086U the first is available — the family is indexed by the invariant opens of one
étale atlas `U`, so `Cardinal.mk ι ≤ 2 ^ 2 ^ (size U) < B.cutoff`, the cutoff being a strong
prelimit cardinal — and the second is what remains to be proved. -/
theorem contains_of_iSup_size_lt {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {ι : Type u} [Nonempty ι] (hι : Cardinal.mk ι < B.cutoff) (X : ι → Subfunctor F)
    (hsize : ∀ T : ι → BigFppfOver B S hS,
      (∀ i, Nonempty (yoneda.obj (T i) ≅ (X i).toFunctor)) →
      (⨆ i, ((BigFppfOver.toScheme B S hS).obj (T i)).size) < B.cutoff) :
    ∀ T : ι → BigFppfOver B S hS,
      (∀ i, Nonempty (yoneda.obj (T i) ≅ (X i).toFunctor)) → ∀ (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (T i) ⟶ Z),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z :=
  fun T hT _ k hk hcov => by
    have := hk
    exact B.contains_of_openCover_of_iSup_size_lt hι k hcov (hsize T hT)

/-- **Tag 086U, reduced to its geometric core.** Let `X` be a presheaf on the big fppf site
of `S`. Assume

* `hopen`, `hrep`: the schematic locus of `X` is an open subspace and is representable,
  which are the two unproved clauses of Tag 03JH;
* `hcore`: every nonempty open set of points of `X` contains the point set of a nonempty
  representable open subspace, which is where decency enters the source's proof.

Then `X` has an open subspace which is representable and whose point set is dense: the
conclusion of Tag 086U, realized by the schematic locus. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hopen : IsOpenSubspace B S hS (schematicLocus B S hS X))
    (hrep : (schematicLocus B S hS X).toFunctor.IsRepresentable)
    (hcore : ∀ W : Set (points B S hS X), IsOpen W → W.Nonempty →
      ∃ H : Subfunctor X, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        Set.range (pointsMap B S hS H.toFunctor H.ι) ⊆ W ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) :=
  ⟨schematicLocus B S hS X, hopen, hrep,
    denseRange_pointsMap_schematicLocus_ι B S hS hcore⟩

/-- **Tag 086U, reduced to local nonemptiness and the size of the schematic locus.**

Let `X` be an algebraic space over `S`. Assume

* `Y`, `hYopen`, `hYrep`, `hcof`: a family of representable open subspaces containing every
  representable open subspace in its union, which is the set-theoretic input of Tag 03JH;
* `hcontains`: the containment obligation, implied by
  `AlgebraicGeometry.Space.contains_of_iSup_size_lt` from `Cardinal.mk ι < B.cutoff` and a
  bound on the supremum of the sizes of the representing objects of the members;
* `hnonempty`: every nonempty open subspace of `X` contains a nonempty representable open
  subspace, which the source derives for a decent space from Tags 086T, 03JI and 01Z2; it
  carries no tag of its own.

Then `X` has a representable open subspace whose point set is dense: the conclusion of
Tag 086U, realized by the schematic locus.

Against `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace` the two
clauses of Tag 03JH are no longer hypotheses, and the first part of Tag 03BZ has disappeared
from `hcore`; decency enters only through `hnonempty`. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_contains
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {ι : Type u} (Y : ι → Subfunctor X) (hYopen : ∀ i, IsOpenSubspace B S hS (Y i))
    (hYrep : ∀ i, (Y i).toFunctor.IsRepresentable)
    (hcof : ∀ G : Subfunctor X, IsOpenSubspace B S hS G → G.toFunctor.IsRepresentable →
      G ≤ ⨆ i, Y i)
    (hcontains : ∀ T : ι → BigFppfOver B S hS,
      (∀ i, Nonempty (yoneda.obj (T i) ≅ (Y i).toFunctor)) → ∀ (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (T i) ⟶ Z),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z)
    (hnonempty : ∀ G : Subfunctor X, IsOpenSubspace B S hS G →
      (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty →
      ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧
        H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) := by
  obtain ⟨hopen, hrep⟩ := isOpenSubspace_and_isRepresentable_schematicLocus_of_contains
    B S hS hX Y hYopen hYrep hcof hcontains
  exact ⟨schematicLocus B S hS X, hopen, hrep,
    denseRange_pointsMap_schematicLocus_ι_of_isAlgebraicSpace B S hS hX hnonempty⟩

/-- Every representable open subspace is a member of the family indexed by the shrunk type of
all of them. -/
private theorem le_iSup_equivShrink_symm {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    [Small.{u} {G : Subfunctor X // IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable}]
    (G : Subfunctor X) (h1 : IsOpenSubspace B S hS G) (h2 : G.toFunctor.IsRepresentable) :
    G ≤ ⨆ i : Shrink.{u} {G : Subfunctor X //
      IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable}, ((equivShrink _).symm i).1 := by
  refine le_trans (le_of_eq ?_) (le_iSup _ (equivShrink _ ⟨G, h1, h2⟩))
  rw [Equiv.symm_apply_apply]

/-- The shrunk type of all representable open subspaces of an algebraic space has cardinality
below the site's cutoff. -/
private theorem mk_shrink_lt_cutoff {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    [Small.{u} {G : Subfunctor X // IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable}] :
    Cardinal.mk (Shrink.{u} {G : Subfunctor X //
      IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable}) < B.cutoff := by
  refine mk_lt_cutoff_of_injective_points B S hS hX
    (fun i => Set.range (pointsMap B S hS ((equivShrink _).symm i).1.toFunctor
      ((equivShrink _).symm i).1.ι)) fun a b h => ?_
  exact (equivShrink _).symm.injective (Subtype.ext (eq_of_range_pointsMap_ι_eq B S hS
    ((equivShrink _).symm a).2.1 ((equivShrink _).symm b).2.1 h))

/-- **Tag 086U, reduced to local nonemptiness and one uniform size bound.**

Let `X` be an algebraic space over `S`. Assume

* `hne`: `X` has at least one representable open subspace;
* `hμ`, `hbound`: one cardinal below the site's cutoff bounds the size of *every* scheme
  representing an open subspace of `X`;
* `hnonempty`: every nonempty open subspace of `X` contains a nonempty representable open
  subspace — derived in the source for a decent space from Tags 086T, 03JI and 01Z2, and
  carrying no tag of its own.

Then `X` has a representable open subspace whose point set is dense: the conclusion of
Tag 086U.

No family of open subspaces appears any more. The cofinal family of Tag 03JH is the family of
*all* representable open subspaces, which is indexed by a type of the working universe by
`AlgebraicGeometry.Space.small_isRepresentable_isOpenSubspace` and has cardinality below the
cutoff by `AlgebraicGeometry.Space.mk_lt_cutoff_of_injective_points`; the only size fact left
over is `hbound`, on the *representing objects* rather than on the subspaces, and that is
where the argument still stops. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_size_le
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hne : ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hbound : ∀ (V : BigFppfOver B S hS) (G : Subfunctor X), IsOpenSubspace B S hS G →
      Nonempty (yoneda.obj V ≅ G.toFunctor) →
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ)
    (hnonempty : ∀ G : Subfunctor X, IsOpenSubspace B S hS G →
      (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty →
      ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧
        H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) := by
  classical
  have hsmall := small_isRepresentable_isOpenSubspace B S hS hX
  obtain ⟨G₀, hG₀⟩ := hne
  have : Nonempty (Shrink.{u} {G : Subfunctor X //
      IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable}) := ⟨equivShrink _ ⟨G₀, hG₀⟩⟩
  refine exists_denseRange_isRepresentable_isOpenSubspace_of_contains B S hS hX
    (ι := Shrink.{u} {G : Subfunctor X //
      IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable})
    (fun i => ((equivShrink _).symm i).1) (fun i => ((equivShrink _).symm i).2.1)
    (fun i => ((equivShrink _).symm i).2.2) (le_iSup_equivShrink_symm B S hS)
    (fun T hT Z k hk hcov => ?_)
    hnonempty
  have := hk
  exact B.contains_of_openCover_of_iSup_size_lt (mk_shrink_lt_cutoff B S hS hX) k hcov
    ((ciSup_le' fun i => hbound (T i) _ ((equivShrink _).symm i).2.1 (hT i)).trans_lt hμ)

/-! ### The size of a scheme representing an open subspace -/

/-- **The remaining size obligation of Tag 03JH, for an algebraic space.** One cardinal below
the site's cutoff bounds the size of *every* scheme representing an open subspace of an
algebraic space over `S`.

The cardinal is `2 ^ 2 ^ size U` for an étale atlas `U` of Tag 025Y: it bounds every
representing object by
`AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas`, and it lies below the cutoff
because the cutoff is a strong prelimit cardinal and `size U` lies below it, the object `U`
being in the site. Uncountability of the cutoff is not needed, since
`Cardinal.IsStrongPrelimit` is exactly closure under powersets. -/
theorem exists_lt_cutoff_size_le_of_isOpenSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    ∃ μ : Cardinal.{u}, μ < B.cutoff ∧ ∀ (V : BigFppfOver B S hS) (G : Subfunctor X),
      IsOpenSubspace B S hS G → Nonempty (yoneda.obj V ≅ G.toFunctor) →
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ := by
  obtain ⟨U, a, hsurj, hetale⟩ := hX.exists_atlas
  refine ⟨(2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ ((BigFppfOver.toScheme B S hS).obj U).size,
    B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit U.left.property),
    fun V G hG ⟨e⟩ => size_le_two_pow_two_pow_size_of_atlas B S hS hsurj hetale
      (MorphismProperty.RespectsIso.precomp _ e.hom G.ι hG.2)⟩

/-! ### The two clauses of Tag 03JH from two cardinal bounds -/

/-- The sheafification of a union of representable open subspaces is representable, with both
the cofinality hypothesis of `AlgebraicGeometry.Space.isRepresentable_sheafify_iSup` and the
containment obligation of
`AlgebraicGeometry.Space.isRepresentable_sheafify_iSup_of_contains` replaced by two cardinal
bounds: the index type is below the cutoff and the representing objects of the members have
size below a common cardinal which is.

Unlike those two statements this needs no containment obligation at all, and Tag 01JJ is not
invoked even in its proved form: the charts of the sheafification supplied by
`AlgebraicGeometry.Space.exists_charts_sheafify_iSup` are exactly the input of
`AlgebraicGeometry.isRepresentable_of_openCharts`, which glues them inside the site using the
two bounds in place of Tag 01JJ. No nonemptiness of the index type is needed either. -/
theorem isRepresentable_sheafify_iSup_of_size_le {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable) (hι : Cardinal.mk ι < B.cutoff)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hsize : ∀ (i : ι) (T : BigFppfOver B S hS), Nonempty (yoneda.obj T ≅ (X i).toFunctor) →
      ((BigFppfOver.toScheme B S hS).obj T).size ≤ μ) :
    ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor.IsRepresentable := by
  obtain ⟨T, w, f, -, hfopen, hfls⟩ := exists_charts_sheafify_iSup B S hS X hXopen hXrep
  exact isRepresentable_of_openCharts
    ⟨((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor,
      (isSheaf_iff_isSheaf_of_type _ _).2
        ((⨆ i, X i).sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type _ _).1 hF))⟩
    T f hfopen hι hμ (fun i => hsize i (T i) ⟨w i⟩) hfls

/-- The sheafification of a union of representable open subspaces is an open subspace, from the
two cardinal bounds and with no containment obligation and no appeal to Tag 01JJ.

Openness of the inclusion is `AlgebraicGeometry.Space.isOpenImmersion_sheafify_iSup_ι`, which
needs no size hypothesis at all; only representability does. -/
theorem isOpenSubspace_sheafify_iSup_of_size_le {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable) (hι : Cardinal.mk ι < B.cutoff)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hsize : ∀ (i : ι) (T : BigFppfOver B S hS), Nonempty (yoneda.obj T ≅ (X i).toFunctor) →
      ((BigFppfOver.toScheme B S hS).obj T).size ≤ μ) :
    IsOpenSubspace B S hS ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)) := by
  have := isRepresentable_sheafify_iSup_of_size_le B S hS hF X hXopen hXrep hι hμ hsize
  exact isOpenSubspace_sheafify_iSup_of_isRepresentable B S hS hF X hXopen

/-- If the representable open subspaces of an algebraic space are all contained in the union of
a family of them obeying the two cardinal bounds, then the schematic locus is that union,
sheafified.

This is `AlgebraicGeometry.Space.schematicLocus_eq_sheafify_iSup_of_contains` with the
containment obligation traded for the two cardinal bounds. -/
theorem schematicLocus_eq_sheafify_iSup_of_size_le {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenSubspace B S hS (X i))
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable)
    (hcof : ∀ G : Subfunctor F, IsOpenSubspace B S hS G → G.toFunctor.IsRepresentable →
      G ≤ ⨆ i, X i)
    (hι : Cardinal.mk ι < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hsize : ∀ (i : ι) (T : BigFppfOver B S hS), Nonempty (yoneda.obj T ≅ (X i).toFunctor) →
      ((BigFppfOver.toScheme B S hS).obj T).size ≤ μ) :
    schematicLocus B S hS F = (⨆ i, X i).sheafify (BigFppfOver.topology B S hS) :=
  schematicLocus_eq_sheafify_iSup_of_isOpenSubspace B S hS X hcof
      (isOpenSubspace_sheafify_iSup_of_size_le B S hS hF.isSheaf X
        (fun i => (hXopen i).2) hXrep hι hμ hsize)
      (isRepresentable_sheafify_iSup_of_size_le B S hS hF.isSheaf X
        (fun i => (hXopen i).2) hXrep hι hμ hsize)

/-- **Stacks 03JH, openness and representability**, from a cofinal family of representable open
subspaces obeying the two cardinal bounds, and *unconditionally in Tag 01JJ*.

This is `AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_contains`
with the containment obligation replaced by `Cardinal.mk ι < B.cutoff` together with a bound on
the sizes of the representing objects of the members: those two bounds are precisely what
`AlgebraicGeometry.isRepresentable_of_openCharts` asks in its place, so Tag 01JJ is not
invoked at all. -/
theorem isOpenSubspace_and_isRepresentable_schematicLocus_of_size_le
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenSubspace B S hS (X i))
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable)
    (hcof : ∀ G : Subfunctor F, IsOpenSubspace B S hS G → G.toFunctor.IsRepresentable →
      G ≤ ⨆ i, X i)
    (hι : Cardinal.mk ι < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hsize : ∀ (i : ι) (T : BigFppfOver B S hS), Nonempty (yoneda.obj T ≅ (X i).toFunctor) →
      ((BigFppfOver.toScheme B S hS).obj T).size ≤ μ) :
    IsOpenSubspace B S hS (schematicLocus B S hS F) ∧
      (schematicLocus B S hS F).toFunctor.IsRepresentable := by
  rw [schematicLocus_eq_sheafify_iSup_of_size_le B S hS hF X hXopen hXrep hcof hι hμ hsize]
  exact ⟨isOpenSubspace_sheafify_iSup_of_size_le B S hS hF.isSheaf X
      (fun i => (hXopen i).2) hXrep hι hμ hsize,
    isRepresentable_sheafify_iSup_of_size_le B S hS hF.isSheaf X
      (fun i => (hXopen i).2) hXrep hι hμ hsize⟩

/-- **Tag 086U, reduced to local nonemptiness alone.**

Let `X` be an algebraic space over `S` and assume `hnonempty`: every nonempty open subspace of
`X` contains a nonempty representable open subspace. Then `X` has a representable open subspace
whose point set is dense, which is the conclusion of Tag 086U, realized by the schematic locus
of Tag 03JH.

Nothing else is assumed. Against
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_size_le` three
hypotheses have gone:

* the uniform size bound `hμ`, `hbound` is now proved, as
  `AlgebraicGeometry.Space.exists_lt_cutoff_size_le_of_isOpenSubspace`: the representing object
  of an open subspace receives a surjective étale morphism from an open of the atlas, and such
  a morphism bounds the size of its *target* by
  `AlgebraicGeometry.Scheme.size_le_of_flat_of_surjective`;
* the containment obligation is gone, because with both cardinal bounds in hand the glueing
  is carried out inside the site by `AlgebraicGeometry.isRepresentable_of_openCharts`, so
  Tag 01JJ is not invoked even in its proved form
  `AlgebraicGeometry.hasZariskiGluing`;
* `hne`, the existence of one representable open subspace, was only there to make the index
  type nonempty for the open-cover bound, and the glueing above does not ask for it.

The cofinal family of Tag 03JH is the family of *all* representable open subspaces: it is
indexed by a type of the working universe by
`AlgebraicGeometry.Space.small_isRepresentable_isOpenSubspace` and has cardinality below the
cutoff by `AlgebraicGeometry.Space.mk_lt_cutoff_of_injective_points`.

Decency is still not a hypothesis, and `hnonempty` is still not derivable here: it is the
step the source takes inside the proof of Tag 086U, from Tags 086T, 03JI and 01Z2 together
with decency. All four are available, and `hnonempty` is discharged for a decent space in
`StacksFrontier/AlgebraicGeometry/Spaces/DenseSchematicLocusDecent.lean`, which is where the tag
086U sits; this declaration is the reduction it feeds, and carries no tag. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hnonempty : ∀ G : Subfunctor X, IsOpenSubspace B S hS G →
      (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty →
      ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧
        H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) := by
  classical
  obtain ⟨μ, hμ, hbound⟩ := exists_lt_cutoff_size_le_of_isOpenSubspace B S hS hX
  have hsmall := small_isRepresentable_isOpenSubspace B S hS hX
  obtain ⟨hopen, hrep⟩ := isOpenSubspace_and_isRepresentable_schematicLocus_of_size_le
    B S hS hX (fun i => ((equivShrink _).symm i).1)
    (fun i => ((equivShrink _).symm i).2.1) (fun i => ((equivShrink _).symm i).2.2)
    (le_iSup_equivShrink_symm B S hS)
    (mk_shrink_lt_cutoff B S hS hX) hμ (fun i T hT => hbound T _ ((equivShrink _).symm i).2.1 hT)
  exact ⟨schematicLocus B S hS X, hopen, hrep,
    denseRange_pointsMap_schematicLocus_ι_of_isAlgebraicSpace B S hS hX hnonempty⟩

end AlgebraicGeometry.Space

end
