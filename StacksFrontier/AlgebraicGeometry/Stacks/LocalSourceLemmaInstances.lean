module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Bounded relative dimension as an instance of the local-source lemma

**Stacks 06M3** takes three properties `𝒫`, `𝒬`, `ℛ` of morphisms of algebraic spaces and
produces, for a 1-morphism of algebraic stacks representable by algebraic spaces and having
`𝒬`, a maximal open substack of the source on which it has `𝒫`, compatible with base change
along a morphism with `ℛ`. Its four hypotheses are: (1) all three properties are fppf local on
the target and stable under arbitrary base change; (2) smoothness implies `ℛ`; (3) every
morphism `f : X ⟶ Y` of algebraic spaces with `𝒬` has a largest open subspace
`W(𝒫, f) ⊆ X` on which `f` has `𝒫`; and (4) for such an `f` and any `g : Y' ⟶ Y` with `ℛ`,
the identity `Y' ×_Y W(𝒫, f) = W(𝒫, f')` holds for the base change `f'`.

**Stacks 06M4** warns that the hypotheses must be checked before the lemma is used, and
**Stacks 06M5** answers that warning with a list of triples for which they do hold, giving
references for (3) and (4) and omitting (1) and (2). This file carries the first entry of that
list, at `𝒬 = ` locally of finite type and `𝒫 = ` relative dimension `≤ d` (**Stacks 06LR**),
whose references are **Stacks 04NT** and **Stacks 04NS**. The entry's `ℛ` is written `∅` in the
source, that is, no condition is imposed on the base change; accordingly hypothesis (4) is
proved here for an *arbitrary* base change, which is what **Stacks 04NS** supplies and which
covers every reading of that `∅`.

The construction is the source's and is the one **Stacks 04NW** performs at `d = 0`. The set of
points of `X` at which the relative dimension of `f` is at most `d` is open by **Stacks 04NT**,
so the correspondence of **Stacks 03BZ** between the open subspaces of an algebraic space and
the open subsets of its space of points turns it into an open subspace. That the restriction of
`f` to it has relative dimension `≤ d`, and that it contains every open subspace with that
property, both reduce to the invariance of the relative dimension at a point under restricting
the source to an open subspace. Hypothesis (4) is the invariance of the relative dimension at a
point under base change.

## Main definitions

* `AlgebraicGeometry.Space.boundedRelativeDimensionPart`: the open subspace of the source cut
  out by the points at which the relative dimension is at most `d`. At `d = 0` this is
  `AlgebraicGeometry.Space.locallyQuasiFinitePart`, the open subspace of **Stacks 04NW**, whose
  construction this generalizes to an arbitrary bound.

## Main results

* `AlgebraicGeometry.Space.exists_isGreatest_hasRelativeDimensionLE` is hypothesis (3) of
  **Stacks 06M3** for the first entry of **Stacks 06M5**.
* `AlgebraicGeometry.Space.boundedRelativeDimensionPart_preimage_of_isPullback` and
  `AlgebraicGeometry.Space.eq_preimage_of_isGreatest_hasRelativeDimensionLE` are hypothesis (4)
  for that entry, the first for the canonical open subspace and the second for an arbitrary
  pair of largest open subspaces, which is the form **Stacks 06M3** consumes.
* `AlgebraicGeometry.Space.hasRelativeDimensionLE_boundedRelativeDimensionPart` and
  `AlgebraicGeometry.Space.le_boundedRelativeDimensionPart` are the two halves of the
  greatest-element property, stated separately because they are what the proofs of the other
  entries of the list would reuse.

## Implementation notes

The statements are those of the source's hypotheses with `ℛ` unrestricted, and no hypothesis
beyond algebraicity of the corners and `𝒬` for the morphism is carried. The three auxiliary
facts the construction needs are available only as `private` declarations inside
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/FibreDimension.lean`, so they are re-derived
here from public statements: invariance of the relative dimension under restriction to an open
subspace is `AlgebraicGeometry.Space.hasRelativeDimensionAt_comp_iff` applied to the inclusion,
which is étale as a morphism of presheaves by
`AlgebraicGeometry.Space.presheaf_etale_of_isOpenImmersion`; and the point set of an inverse
image of a subfunctor is read off the cartesian square of **Stacks 083Q** through
`AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback`.

The bound is a natural number and the relative dimension at a point an element of `ℕ∞`, so the
open set of **Stacks 04NT** is stated with an `ℕ∞`-valued witness while **Stacks 06LR** uses an
`ℕ`-valued one; `AlgebraicGeometry.Space.setOf_hasRelativeDimensionLEAt_eq` identifies the two,
a witness bounded by a natural number being finite.

Only the first entry of the list is carried here. The other four, at `𝒫 = ` locally
quasi-finite, unramified, flat and étale, are
`AlgebraicGeometry.Space.exists_isGreatest_isLocallyQuasiFinite`,
`AlgebraicGeometry.Space.exists_isGreatest_isUnramified`,
`AlgebraicGeometry.Space.exists_isGreatest_isFlat` and
`AlgebraicGeometry.Space.exists_isGreatest_isEtale` for hypothesis (3), with the corresponding
`eq_preimage_of_isGreatest_*` declarations for hypothesis (4).

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 04NT](https://stacks.math.columbia.edu/tag/04NT)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
* [Stacks Project, Tag 06M4](https://stacks.math.columbia.edu/tag/06M4)
* [Stacks Project, Tag 06M5](https://stacks.math.columbia.edu/tag/06M5)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two facts re-derived from public statements -/

/-- The point set of the inverse image of a subfunctor along a morphism of presheaves is the
preimage of its point set.

The inverse image sits in a cartesian square over the subfunctor (**Stacks 083Q**), and taking
point sets carries a cartesian square to the corresponding preimage identity. -/
private alias range_pointsMap_preimage_eq_preimage_range := pointsRange_preimage

/-- The point set of an open subspace, in the coerced form in which the order isomorphism of
**Stacks 03BZ** presents it. -/
private theorem coe_openSubspacesOrderIso_eq_range {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (W : {W : Subfunctor X // IsOpenSubspace B S hS W}) :
    ((openSubspacesOrderIso B S hS X hX W : TopologicalSpace.Opens (points B S hS X)) :
        Set (points B S hS X)) =
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) :=
  openSubspacesOrderIso_apply B S hS X hX W

/-- Relative dimension at a point is unchanged by restricting the source to an open subspace
containing the point.

The inclusion of an open subspace is étale as a morphism of presheaves, so this is
`AlgebraicGeometry.Space.hasRelativeDimensionAt_comp_iff` at that inclusion. -/
private theorem hasRelativeDimensionAt_restrict_iff
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (W : Subfunctor X) (hW : IsOpenSubspace B S hS W) (f : X ⟶ Y)
    (x' : points B S hS W.toFunctor) (d : ℕ∞) :
    HasRelativeDimensionAt d B S hS (W.ι ≫ f) x' ↔
      HasRelativeDimensionAt d B S hS f (pointsMap B S hS W.toFunctor W.ι x') :=
  hasRelativeDimensionAt_comp_iff B S hS d W.ι f
    (presheaf_etale_of_isOpenImmersion B S hS hW.2) hW.1 hY x'

/-! ### The open subspace of bounded relative dimension -/

/-- The set of points at which the relative dimension is at most a natural number `d`, as
**Stacks 06LR** states it with an `ℕ`-valued witness, is the set **Stacks 04NT** proves open,
stated with an `ℕ∞`-valued one: a witness bounded by `d` cannot be `⊤`. -/
private theorem setOf_hasRelativeDimensionLEAt_eq
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (d : ℕ) :
    {x : points B S hS X | HasRelativeDimensionLEAt d B S hS f x} =
      {x : points B S hS X |
        ∃ e : ℕ∞, e ≤ (d : ℕ∞) ∧ HasRelativeDimensionAt e B S hS f x} := by
  ext x
  constructor
  · rintro ⟨e, hed, hdim⟩
    exact ⟨(e : ℕ∞), by exact_mod_cast hed, hdim⟩
  · rintro ⟨e, hed, hdim⟩
    lift e to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top d) hed
    exact ⟨e, by exact_mod_cast hed, hdim⟩

/-- **The open subspace of bounded relative dimension.** For a morphism `f : X ⟶ Y` of
algebraic spaces over `S` which is locally of finite type and a natural number `d`, the open
subspace of `X` cut out by the points at which the relative dimension of `f` is at most `d`.

The set of such points is open by **Stacks 04NT**, and the correspondence of **Stacks 03BZ**
reads it as an open subspace. At `d = 0` this is
`AlgebraicGeometry.Space.locallyQuasiFinitePart`, the open subspace of **Stacks 04NW**. -/
noncomputable def boundedRelativeDimensionPart (d : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    {W : Subfunctor X // IsOpenSubspace B S hS W} :=
  (openSubspacesOrderIso B S hS X hX).symm
    ⟨{x | ∃ e : ℕ∞, e ≤ (d : ℕ∞) ∧ HasRelativeDimensionAt e B S hS f x},
      isOpen_setOf_hasRelativeDimensionAt_le B S hS hX hY f hf d⟩

/-- The points of `AlgebraicGeometry.Space.boundedRelativeDimensionPart` are exactly the points
at which the relative dimension is at most `d`. -/
theorem range_pointsMap_boundedRelativeDimensionPart (d : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    Set.range (pointsMap B S hS
        (boundedRelativeDimensionPart B S hS d hX hY f hf).1.toFunctor
        (boundedRelativeDimensionPart B S hS d hX hY f hf).1.ι) =
      {x : points B S hS X | HasRelativeDimensionLEAt d B S hS f x} := by
  rw [setOf_hasRelativeDimensionLEAt_eq B S hS f d]
  simpa only [boundedRelativeDimensionPart, OrderIso.apply_symm_apply] using
    (openSubspacesOrderIso_apply B S hS X hX
      (boundedRelativeDimensionPart B S hS d hX hY f hf)).symm

/-- **Hypothesis (3) of Stacks 06M3 for the first entry of Stacks 06M5: the property holds on
the open subspace.** The restriction of `f` to
`AlgebraicGeometry.Space.boundedRelativeDimensionPart` has relative dimension `≤ d`.

Every point of the open subspace has relative dimension at most `d` for `f`, and relative
dimension at a point is unchanged by restricting the source to an open subspace. -/
theorem hasRelativeDimensionLE_boundedRelativeDimensionPart (d : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    HasRelativeDimensionLE d B S hS
      ((boundedRelativeDimensionPart B S hS d hX hY f hf).1.ι ≫ f) := by
  intro x'
  obtain ⟨e, hed, hdim⟩ :
      HasRelativeDimensionLEAt d B S hS f (pointsMap B S hS
        (boundedRelativeDimensionPart B S hS d hX hY f hf).1.toFunctor
        (boundedRelativeDimensionPart B S hS d hX hY f hf).1.ι x') := by
    rw [← Set.mem_ofPred_eq (p := fun x => HasRelativeDimensionLEAt d B S hS f x),
      ← range_pointsMap_boundedRelativeDimensionPart B S hS d hX hY f hf]
    exact ⟨x', rfl⟩
  exact ⟨e, hed, (hasRelativeDimensionAt_restrict_iff B S hS hY _
    (boundedRelativeDimensionPart B S hS d hX hY f hf).2 f x' (e : ℕ∞)).2 hdim⟩

/-- **Hypothesis (3) of Stacks 06M3 for the first entry of Stacks 06M5: maximality.** Every
open subspace of the source on which `f` has relative dimension `≤ d` is contained in
`AlgebraicGeometry.Space.boundedRelativeDimensionPart`.

Each of its points has relative dimension at most `d` for the restriction of `f`, hence for `f`
itself, so its point set is contained in the point set of the open subspace; the correspondence
of **Stacks 03BZ** preserves the order. -/
theorem le_boundedRelativeDimensionPart (d : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (V : {V : Subfunctor X // IsOpenSubspace B S hS V})
    (hV : HasRelativeDimensionLE d B S hS (V.1.ι ≫ f)) :
    V ≤ boundedRelativeDimensionPart B S hS d hX hY f hf := by
  have hle : ((openSubspacesOrderIso B S hS X hX V :
        TopologicalSpace.Opens (points B S hS X)) : Set (points B S hS X)) ⊆
      ((openSubspacesOrderIso B S hS X hX (boundedRelativeDimensionPart B S hS d hX hY f hf) :
        TopologicalSpace.Opens (points B S hS X)) : Set (points B S hS X)) := by
    rw [coe_openSubspacesOrderIso_eq_range, coe_openSubspacesOrderIso_eq_range,
      range_pointsMap_boundedRelativeDimensionPart]
    rintro x ⟨x', rfl⟩
    obtain ⟨e, hed, hdim⟩ := hV x'
    exact ⟨e, hed, (hasRelativeDimensionAt_restrict_iff B S hS hY V.1 V.2 f x' (e : ℕ∞)).1 hdim⟩
  exact (openSubspacesOrderIso B S hS X hX).le_iff_le.mp hle

/-- `AlgebraicGeometry.Space.boundedRelativeDimensionPart` is a largest open subspace on which the
restriction of `f` has relative dimension `≤ d`. -/
private theorem isGreatest_boundedRelativeDimensionPart (d : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
      HasRelativeDimensionLE d B S hS (V.1.ι ≫ f)}
      (boundedRelativeDimensionPart B S hS d hX hY f hf) :=
  ⟨hasRelativeDimensionLE_boundedRelativeDimensionPart B S hS d hX hY f hf,
    fun V hV => le_boundedRelativeDimensionPart B S hS d hX hY f hf V hV⟩

/-! ### Hypotheses (3) and (4) of Stacks 06M3 for bounded relative dimension -/

/-- **Stacks 06M5, first entry, hypothesis (3) of Stacks 06M3.** For `𝒬 = ` locally of finite
type and `𝒫 = ` relative dimension `≤ d` (**Stacks 06LR**): every morphism `f : X ⟶ Y` of
algebraic spaces over `S` which is locally of finite type has a largest open subspace of `X` on
which it has relative dimension `≤ d`.

The open subspace is `AlgebraicGeometry.Space.boundedRelativeDimensionPart`, built from the
openness statement **Stacks 04NT** through the correspondence of **Stacks 03BZ**; the two
clauses of being greatest are
`AlgebraicGeometry.Space.hasRelativeDimensionLE_boundedRelativeDimensionPart` and
`AlgebraicGeometry.Space.le_boundedRelativeDimensionPart`. -/
@[stacks 06M5 "entry (1), hypothesis (3) of Stacks 06M3 at 𝒬 = locally of finite type and \
𝒫 = relative dimension ≤ d: the existence of a largest open subspace of the source on which \
the morphism has relative dimension ≤ d, from Stacks 06LR and Stacks 04NT"]
theorem exists_isGreatest_hasRelativeDimensionLE (d : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    ∃ W : {W : Subfunctor X // IsOpenSubspace B S hS W},
      IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
        HasRelativeDimensionLE d B S hS (V.1.ι ≫ f)} W :=
  ⟨_, isGreatest_boundedRelativeDimensionPart B S hS d hX hY f hf⟩

/-- **Stacks 06M5, first entry, hypothesis (4) of Stacks 06M3, for the canonical open
subspace.** In a cartesian square of algebraic spaces over `S` whose right vertical arrow `f`
is locally of finite type, the base change `f'` is locally of finite type and its open subspace
of relative dimension `≤ d` is the inverse image of that of `f`.

No condition is imposed on the base change: the source writes `ℛ = ∅` for this entry, and
**Stacks 04NS** gives the invariance of the relative dimension at a point under an arbitrary
base change. On points both sides are the locus of relative dimension at most `d`, by
`AlgebraicGeometry.Space.range_pointsMap_boundedRelativeDimensionPart` and the identification of
the point set of an inverse image; the two open subspaces then agree because **Stacks 03BZ** is
injective. -/
@[stacks 06M5 "entry (1), hypothesis (4) of Stacks 06M3 at 𝒬 = locally of finite type and \
𝒫 = relative dimension ≤ d, for the canonical open subspace: the formation of the largest open \
subspace commutes with base change, for an arbitrary base change since the entry's ℛ is ∅, \
from Stacks 04NS"]
theorem boundedRelativeDimensionPart_preimage_of_isPullback (d : ℕ)
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    ∃ hf' : IsLocallyOfFiniteType B S hS f',
      (boundedRelativeDimensionPart B S hS d hX' hY' f' hf').1 =
        (boundedRelativeDimensionPart B S hS d hX hY f hf).1.preimage g' := by
  have hcat : IsPullback
      (ObjectProperty.homMk g' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk f' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y', hY'⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk g : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq
  have hf' : IsLocallyOfFiniteType B S hS f' :=
    (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hcat hf
  refine ⟨hf', congrArg Subtype.val (?_ :
    boundedRelativeDimensionPart B S hS d hX' hY' f' hf' =
      ⟨(boundedRelativeDimensionPart B S hS d hX hY f hf).1.preimage g',
        isOpenSubspace_preimage B S hS g'
          (boundedRelativeDimensionPart B S hS d hX hY f hf).1 hX hX'
          (boundedRelativeDimensionPart B S hS d hX hY f hf).2⟩)⟩
  refine (openSubspacesOrderIso B S hS X' hX').injective (TopologicalSpace.Opens.ext ?_)
  rw [coe_openSubspacesOrderIso_eq_range, coe_openSubspacesOrderIso_eq_range,
    range_pointsMap_boundedRelativeDimensionPart, range_pointsMap_preimage_eq_preimage_range,
    range_pointsMap_boundedRelativeDimensionPart]
  ext x'
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  exact ⟨fun ⟨e, hed, hdim⟩ => ⟨e, hed,
      (hasRelativeDimensionAt_iff_of_isPullback B S hS sq hX hY' hY hf x' (e : ℕ∞)).2 hdim⟩,
    fun ⟨e, hed, hdim⟩ => ⟨e, hed,
      (hasRelativeDimensionAt_iff_of_isPullback B S hS sq hX hY' hY hf x' (e : ℕ∞)).1 hdim⟩⟩

/-- **Stacks 06M5, first entry, hypothesis (4) of Stacks 06M3, in the form the lemma consumes.**
In a cartesian square of algebraic spaces over `S` whose right vertical arrow `f` is locally of
finite type, any largest open subspace of the source of the base change on which the base
change has relative dimension `≤ d` is the inverse image of any largest open subspace of `X` on
which `f` has relative dimension `≤ d`.

**Stacks 06M3** takes hypothesis (4) in this shape, quantified over largest open subspaces
rather than over a chosen one. A greatest element of an ordered type is unique, so both are the
canonical `AlgebraicGeometry.Space.boundedRelativeDimensionPart` and the statement reduces to
`AlgebraicGeometry.Space.boundedRelativeDimensionPart_preimage_of_isPullback`. -/
@[stacks 06M5 "entry (1), hypothesis (4) of Stacks 06M3 at 𝒬 = locally of finite type and \
𝒫 = relative dimension ≤ d, quantified over largest open subspaces as the lemma takes it, for \
an arbitrary base change since the entry's ℛ is ∅"]
theorem eq_preimage_of_isGreatest_hasRelativeDimensionLE (d : ℕ)
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (W : {W : Subfunctor X // IsOpenSubspace B S hS W})
    (hW : IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
      HasRelativeDimensionLE d B S hS (V.1.ι ≫ f)} W)
    (W' : {W' : Subfunctor X' // IsOpenSubspace B S hS W'})
    (hW' : IsGreatest {V : {V : Subfunctor X' // IsOpenSubspace B S hS V} |
      HasRelativeDimensionLE d B S hS (V.1.ι ≫ f')} W') :
    W'.1 = W.1.preimage g' := by
  obtain ⟨hf', hpre⟩ :=
    boundedRelativeDimensionPart_preimage_of_isPullback B S hS d sq hX' hX hY' hY hf
  rw [hW'.unique (isGreatest_boundedRelativeDimensionPart B S hS d hX' hY' f' hf'),
    hW.unique (isGreatest_boundedRelativeDimensionPart B S hS d hX hY f hf), hpre]

end AlgebraicGeometry.Space

end
