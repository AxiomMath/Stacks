module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAtPointFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatLocusWarning

/-!
# Locally quasi-finite, unramified, flat and étale loci as instances of the local-source lemma

**Stacks 06M3** takes three properties `𝒫`, `𝒬`, `ℛ` of morphisms of algebraic spaces and
produces, for a 1-morphism of algebraic stacks representable by algebraic spaces and having `𝒬`,
a largest open substack of the source on which it has `𝒫`, compatible with base change along a
morphism with `ℛ`. Of its four hypotheses, (3) asks that every morphism `f : X ⟶ Y` of
algebraic spaces with `𝒬` have a largest open subspace `W(𝒫, f) ⊆ X` on which `f` has `𝒫`, and
(4) that for such an `f` and any `Y' ⟶ Y` with `ℛ` the identity `Y' ×_Y W(𝒫, f) = W(𝒫, f')`
hold for the base change `f' : X_{Y'} ⟶ Y'`.

**Stacks 06M5** lists triples for which (3) and (4) hold, with references. Its first entry,
relative dimension `≤ d`, is `AlgebraicGeometry.Space.exists_isGreatest_hasRelativeDimensionLE`
together with `AlgebraicGeometry.Space.eq_preimage_of_isGreatest_hasRelativeDimensionLE`; this
file carries the other four:

* entry (2): `𝒬 = ` locally of finite type, `ℛ = ∅`, `𝒫 = ` locally quasi-finite, from
  **Stacks 04NW**;
* entry (3): `𝒬 = ` locally of finite type, `ℛ = ∅`, `𝒫 = ` unramified, from **Stacks 05W2**;
* entry (4): `𝒬 = ` locally of finite presentation, `ℛ = ` flat and locally of finite
  presentation, `𝒫 = ` flat, from **Stacks 05WV** and **Stacks 05WW**;
* entry (5): `𝒬 = ` locally of finite presentation, `ℛ = ` flat and locally of finite
  presentation, `𝒫 = ` étale, by combining entries (3) and (4) through **Stacks 06LU**.

In each of entries (3)–(5) the largest open subspace is the one whose point set is the locus of
points at which `f` has the pointwise form of `𝒫`: unramified at the point
(`AlgebraicGeometry.Space.IsUnramifiedAt`), flat at the point (`AlgebraicGeometry.Space.IsFlatAt`),
or both. That locus is open — for flatness because `f` is locally of finite presentation — and
the open subspace with that point set is greatest because, for an open subspace `V`, `f`
restricted to `V` has `𝒫` exactly when `f` has the pointwise property at every point of `V`.
For flatness this last step is where `𝒬` enters, and it is the remark of the source that
`W(𝒫, f)` is then exactly the set of points at which `f` is flat, as opposed to the situation of
**Stacks 06M4**. Hypothesis (4) is then the invariance of the pointwise property under base
change: under any base change for unramifiedness (`f` being locally of finite type), and under
a flat base change for flatness.

## Main results

* `AlgebraicGeometry.Space.exists_isGreatest_isLocallyQuasiFinite`,
  `AlgebraicGeometry.Space.eq_preimage_of_isGreatest_isLocallyQuasiFinite`: hypotheses (3) and
  (4) of **Stacks 06M3** for entry (2) of **Stacks 06M5**.
* `AlgebraicGeometry.Space.exists_isGreatest_isUnramified`,
  `AlgebraicGeometry.Space.eq_preimage_of_isGreatest_isUnramified`: the same for entry (3).
* `AlgebraicGeometry.Space.exists_isGreatest_isFlat`,
  `AlgebraicGeometry.Space.eq_preimage_of_isGreatest_isFlat`: the same for entry (4).
* `AlgebraicGeometry.Space.exists_isGreatest_isEtale`,
  `AlgebraicGeometry.Space.eq_preimage_of_isGreatest_isEtale`: the same for entry (5).
* `AlgebraicGeometry.Space.isUnramifiedAt_iff_of_isOpenSubspace`: unramifiedness at a point is
  unchanged by restricting the source to an open subspace containing it.

## Implementation notes

Hypothesis (4) is stated, as for the first entry, quantified over largest open subspaces of the
two sources, which is the form **Stacks 06M3** consumes; a cartesian square of presheaves whose
four corners are algebraic spaces stands for the base change. For entries (2) and (3) the
source writes `ℛ = ∅`, and the statements impose no condition on the base change. For entries
(4) and (5) the source's `ℛ` is flat and locally of finite presentation; the proofs use only
flatness of the base change, so the statements assume only that, which covers every morphism
with `ℛ`.

For entries (3)–(5) hypothesis (3) is stated together with the point set of the largest open
subspace, which is the content of the source's references (**Stacks 05W2** part (1),
**Stacks 05WV**) and is what the proof of (4) uses.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
* [Stacks Project, Tag 05W2](https://stacks.math.columbia.edu/tag/05W2)
* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
* [Stacks Project, Tag 05WW](https://stacks.math.columbia.edu/tag/05WW)
* [Stacks Project, Tag 06LU](https://stacks.math.columbia.edu/tag/06LU)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
* [Stacks Project, Tag 06M4](https://stacks.math.columbia.edu/tag/06M4)
* [Stacks Project, Tag 06M5](https://stacks.math.columbia.edu/tag/06M5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Largest open subspaces cut out by an open set of points -/

/-- If membership of a family of open subspaces of an algebraic space is the condition that the
point set lie in a given open set `O` of points, then the open subspace corresponding to `O`
under **Stacks 03BZ** is the greatest member of the family. -/
private theorem isGreatest_openSubspacesOrderIso_symm {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (O : TopologicalSpace.Opens (points B S hS X))
    (P : {V : Subfunctor X // IsOpenSubspace B S hS V} → Prop)
    (hP : ∀ V, P V ↔ ∀ v, pointsMap B S hS V.1.toFunctor V.1.ι v ∈ O) :
    IsGreatest {V | P V} ((openSubspacesOrderIso B S hS X hX).symm O) := by
  refine ⟨(hP _).2 (Set.range_subset_iff.1 ?_), fun V hV => ?_⟩
  · rw [← openSubspacesOrderIso_apply B S hS X hX, OrderIso.apply_symm_apply]
    rfl
  · rw [← (openSubspacesOrderIso B S hS X hX).le_iff_le, OrderIso.apply_symm_apply,
      ← SetLike.coe_subset_coe]
    exact Set.range_subset_iff.2 ((hP V).1 hV)

/-- Under the hypothesis of `isGreatest_openSubspacesOrderIso_symm`, the point set of any
greatest member of the family is `O`: a greatest element is unique. -/
private theorem range_pointsMap_eq_of_isGreatest {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (O : TopologicalSpace.Opens (points B S hS X))
    (P : {V : Subfunctor X // IsOpenSubspace B S hS V} → Prop)
    (hP : ∀ V, P V ↔ ∀ v, pointsMap B S hS V.1.toFunctor V.1.ι v ∈ O)
    (W : {W : Subfunctor X // IsOpenSubspace B S hS W}) (hW : IsGreatest {V | P V} W) :
    Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) = (O : Set (points B S hS X)) := by
  rw [hW.unique (isGreatest_openSubspacesOrderIso_symm B S hS hX O P hP),
    ← openSubspacesOrderIso_apply B S hS X hX, OrderIso.apply_symm_apply]
  rfl

/-- Two families of open subspaces of `X` and of `X'`, each cut out as in
`isGreatest_openSubspacesOrderIso_symm` by an open set of points, the second of which is the
preimage of the first under `g' : X' ⟶ X`: a greatest member of the second family is the
inverse image of a greatest member of the first.

Both are determined by their point sets through **Stacks 03BZ**, and the point set of an
inverse image is the preimage of the point set, by the cartesian square of **Stacks 083Q**. -/
private theorem eq_preimage_of_isGreatest_of_preimage_eq
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (g' : X' ⟶ X)
    (O : TopologicalSpace.Opens (points B S hS X)) (O' : TopologicalSpace.Opens (points B S hS X'))
    (hO : (O' : Set (points B S hS X')) = pointsMap B S hS X' g' ⁻¹' (O : Set (points B S hS X)))
    (P : {V : Subfunctor X // IsOpenSubspace B S hS V} → Prop)
    (hP : ∀ V, P V ↔ ∀ v, pointsMap B S hS V.1.toFunctor V.1.ι v ∈ O)
    (P' : {V : Subfunctor X' // IsOpenSubspace B S hS V} → Prop)
    (hP' : ∀ V, P' V ↔ ∀ v, pointsMap B S hS V.1.toFunctor V.1.ι v ∈ O')
    (W : {W : Subfunctor X // IsOpenSubspace B S hS W}) (hW : IsGreatest {V | P V} W)
    (W' : {W' : Subfunctor X' // IsOpenSubspace B S hS W'}) (hW' : IsGreatest {V | P' V} W') :
    W'.1 = W.1.preimage g' := by
  have hrange : Set.range (pointsMap B S hS (W.1.preimage g').toFunctor (W.1.preimage g').ι) =
      pointsMap B S hS X' g' ⁻¹' Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) := by
    rw [← Set.image_univ, ← Set.image_univ (f := pointsMap B S hS W.1.toFunctor W.1.ι),
      preimage_image_pointsMap_of_isPullback B S hS (Subfunctor.isPullback_preimage g' W.1)
        Set.univ, Set.preimage_univ, Set.image_univ]
  have key : W' = ⟨W.1.preimage g', isOpenSubspace_preimage B S hS g' W.1 hX hX' W.2⟩ := by
    refine (openSubspacesOrderIso B S hS X' hX').injective (TopologicalSpace.Opens.ext ?_)
    exact (range_pointsMap_eq_of_isGreatest B S hS hX' O' P' hP' W' hW').trans
      (hO.trans ((congrArg _ (range_pointsMap_eq_of_isGreatest B S hS hX O P hP W hW).symm).trans
        hrange.symm))
  exact congrArg Subtype.val key

/-- If membership of a family of open subspaces of an algebraic space is the condition that the
point set lie in an open set `O` of points, the family has a greatest member, whose point set is
`O`. -/
private theorem exists_isGreatest_of_forall_mem {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (O : TopologicalSpace.Opens (points B S hS X))
    (P : {V : Subfunctor X // IsOpenSubspace B S hS V} → Prop)
    (hP : ∀ V, P V ↔ ∀ v, pointsMap B S hS V.1.toFunctor V.1.ι v ∈ O) :
    ∃ W : {W : Subfunctor X // IsOpenSubspace B S hS W}, IsGreatest {V | P V} W ∧
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) = (O : Set (points B S hS X)) :=
  have hG := isGreatest_openSubspacesOrderIso_symm B S hS hX O P hP
  ⟨_, hG, range_pointsMap_eq_of_isGreatest B S hS hX O P hP _ hG⟩

/-- A cartesian square of algebraic spaces over `S` is one in the category of algebraic spaces. -/
private theorem isPullback_homMk {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y) :
    IsPullback
      (ObjectProperty.homMk g' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk f' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y', hY'⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk g : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
  IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq

/-! ### Entry (2): locally quasi-finite morphisms -/

/-- **Stacks 06M5, entry (2), hypothesis (3) of Stacks 06M3.** For `𝒬 = ` locally of finite
type and `𝒫 = ` locally quasi-finite: every morphism `f : X ⟶ Y` of algebraic spaces over `S`
which is locally of finite type has a largest open subspace of `X` on which it is locally
quasi-finite.

It is `AlgebraicGeometry.Space.locallyQuasiFinitePart`, the open subspace of **Stacks 04NW**,
which is the case `d = 0` of the first entry by **Stacks 04NV**. -/
@[stacks 06M5 "entry (2), locally quasi-finite: hypothesis (3) of 06M3"]
theorem exists_isGreatest_isLocallyQuasiFinite
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    ∃ W : {W : Subfunctor X // IsOpenSubspace B S hS W},
      IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
        IsLocallyQuasiFinite B S hS (V.1.ι ≫ f)} W :=
  ⟨locallyQuasiFinitePart B S hS hX hY f hf,
    isLocallyQuasiFinite_locallyQuasiFinitePart B S hS hX hY f hf,
    fun V hV => le_locallyQuasiFinitePart B S hS hX hY f hf V hV⟩

/-- **Stacks 06M5, entry (2), hypothesis (4) of Stacks 06M3.** In a cartesian square of
algebraic spaces over `S` whose right vertical arrow `f` is locally of finite type, any largest
open subspace of the source of the base change `f'` on which `f'` is locally quasi-finite is the
inverse image of any largest open subspace of `X` on which `f` is locally quasi-finite.

The source writes `ℛ = ∅` for this entry, and no condition is imposed on the base change. Both
greatest elements are the canonical open subspaces of **Stacks 04NW**, whose formation commutes
with arbitrary base change,
`AlgebraicGeometry.Space.locallyQuasiFinitePart_preimage_of_isPullback`. -/
@[stacks 06M5 "entry (2), locally quasi-finite: hypothesis (4) of 06M3"]
theorem eq_preimage_of_isGreatest_isLocallyQuasiFinite
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (W : {W : Subfunctor X // IsOpenSubspace B S hS W})
    (hW : IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
      IsLocallyQuasiFinite B S hS (V.1.ι ≫ f)} W)
    (W' : {W' : Subfunctor X' // IsOpenSubspace B S hS W'})
    (hW' : IsGreatest {V : {V : Subfunctor X' // IsOpenSubspace B S hS V} |
      IsLocallyQuasiFinite B S hS (V.1.ι ≫ f')} W') :
    W'.1 = W.1.preimage g' := by
  obtain ⟨hf', hpre⟩ :=
    locallyQuasiFinitePart_preimage_of_isPullback B S hS sq hX' hX hY' hY hf
  have hWeq : W = locallyQuasiFinitePart B S hS hX hY f hf :=
    hW.unique ⟨isLocallyQuasiFinite_locallyQuasiFinitePart B S hS hX hY f hf,
      fun V hV => le_locallyQuasiFinitePart B S hS hX hY f hf V hV⟩
  have hW'eq : W' = locallyQuasiFinitePart B S hS hX' hY' f' hf' :=
    hW'.unique ⟨isLocallyQuasiFinite_locallyQuasiFinitePart B S hS hX' hY' f' hf',
      fun V hV => le_locallyQuasiFinitePart B S hS hX' hY' f' hf' V hV⟩
  rw [hW'eq, hWeq, hpre]

/-! ### Entry (3): unramified morphisms -/

/-- Unramifiedness at a point is unchanged by restricting the source to an open subspace
containing the point: a pointed étale chart of the restriction is one of the morphism with the
same chart map, and unramifiedness of germs is étale local on source and target, so it may be
read in any one pointed chart. -/
theorem isUnramifiedAt_iff_of_isOpenSubspace {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (U : Subfunctor X)
    (hU : IsOpenSubspace B S hS U) (f : X ⟶ Y) (x' : points B S hS U.toFunctor) :
    IsUnramifiedAt B S hS f (pointsMap B S hS U.toFunctor U.ι x') ↔
      IsUnramifiedAt B S hS (U.ι ≫ f) x' := by
  have hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget
      (MorphismOfGerms.HasRepresentativeWithProperty
        (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})) :=
    MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget _
      _root_.AlgebraicGeometry.unramified_isEtaleLocalOnSourceAndTarget
  rw [isUnramifiedAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hX hY,
    isUnramifiedAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hU.1 hY]
  refine ⟨fun h c => h (etaleChartAtPointOfOpenSubspace B S hS U hU f c), fun h => ?_⟩
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hU.1 hY (U.ι ≫ f) x'
  exact (holdsOnEveryEtaleChartAtPoint_iff_some B S hS _ hQ hX hY f
    (pointsMap B S hS U.toFunctor U.ι x')).2
    ⟨etaleChartAtPointOfOpenSubspace B S hS U hU f c, h c⟩

/-- A morphism of algebraic spaces over `S` is unramified on an open subspace of its source
exactly when it is unramified at every point of that open subspace. -/
private theorem isUnramified_comp_ι_iff {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : Subfunctor X) (hV : IsOpenSubspace B S hS V) :
    IsUnramified B S hS (V.ι ≫ f) ↔
      ∀ v : points B S hS V.toFunctor,
        IsUnramifiedAt B S hS f (pointsMap B S hS V.toFunctor V.ι v) :=
  ⟨fun h v => isUnramifiedAt_of_isOpenSubspace B S hS V hV h v, fun h =>
    ((isUnramified_tfae B S hS hV.1 hY (V.ι ≫ f)).out 1 2).2 fun v =>
      (isUnramifiedAt_iff_of_isOpenSubspace B S hS hX hY V hV f v).1 (h v)⟩

/-- The open set of points at which a morphism of algebraic spaces is unramified. -/
private noncomputable abbrev unramifiedPoints {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) : TopologicalSpace.Opens (points B S hS X) :=
  ⟨{x | IsUnramifiedAt B S hS f x}, isOpen_setOf_isUnramifiedAt B S hS f⟩

/-- **Stacks 06M5, entry (3), hypothesis (3) of Stacks 06M3.** For `𝒫 = ` unramified: every
morphism `f : X ⟶ Y` of algebraic spaces over `S` has a largest open subspace of `X` on which it
is unramified, and its point set is the set of points at which `f` is unramified.

This is **Stacks 05W2**, part (1): the set of points at which `f` is unramified is open, the
corresponding open subspace (**Stacks 03BZ**) is `AlgebraicGeometry.Space.unramifiedLocus`, and
an open subspace on which `f` is unramified is one at all of whose points `f` is unramified. The
entry's `𝒬`, locally of finite type, is not needed for this hypothesis; it is needed for (4). -/
@[stacks 06M5 "entry (3), unramified: hypothesis (3) of 06M3"]
theorem exists_isGreatest_isUnramified
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    ∃ W : {W : Subfunctor X // IsOpenSubspace B S hS W},
      IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
        IsUnramified B S hS (V.1.ι ≫ f)} W ∧
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) =
        {x : points B S hS X | IsUnramifiedAt B S hS f x} := by
  exact exists_isGreatest_of_forall_mem B S hS hX (unramifiedPoints B S hS f) _ fun V =>
    isUnramified_comp_ι_iff B S hS hX hY f V.1 V.2

/-- **Stacks 06M5, entry (3), hypothesis (4) of Stacks 06M3.** In a cartesian square of
algebraic spaces over `S` whose right vertical arrow `f` is locally of finite type, any largest
open subspace of the source of the base change `f'` on which `f'` is unramified is the inverse
image of any largest open subspace of `X` on which `f` is unramified.

The source writes `ℛ = ∅` for this entry, and no condition is imposed on the base change. By
hypothesis (3) both open subspaces are the loci of points at which the morphisms are
unramified, and those correspond under base change by **Stacks 05W2**, part (2),
`AlgebraicGeometry.Space.isUnramifiedAt_iff_of_isPullback`. -/
@[stacks 06M5 "entry (3), unramified: hypothesis (4) of 06M3"]
theorem eq_preimage_of_isGreatest_isUnramified
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (W : {W : Subfunctor X // IsOpenSubspace B S hS W})
    (hW : IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
      IsUnramified B S hS (V.1.ι ≫ f)} W)
    (W' : {W' : Subfunctor X' // IsOpenSubspace B S hS W'})
    (hW' : IsGreatest {V : {V : Subfunctor X' // IsOpenSubspace B S hS V} |
      IsUnramified B S hS (V.1.ι ≫ f')} W') :
    W'.1 = W.1.preimage g' := by
  refine eq_preimage_of_isGreatest_of_preimage_eq B S hS hX' hX g' (unramifiedPoints B S hS f)
    (unramifiedPoints B S hS f') ?_ _
    (fun V => isUnramified_comp_ι_iff B S hS hX hY f V.1 V.2) _
    (fun V => isUnramified_comp_ι_iff B S hS hX' hY' f' V.1 V.2) W hW W' hW'
  ext x'
  exact (isUnramifiedAt_iff_of_isPullback B S hS sq hX' hX hY' hY hf x').symm

/-! ### Entry (4): flat morphisms -/

/-- A morphism of algebraic spaces over `S` is flat on an open subspace of its source exactly
when it is flat at every point of that open subspace. -/
private theorem isFlat_comp_ι_iff {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : Subfunctor X) (hV : IsOpenSubspace B S hS V) :
    IsFlat B S hS (V.ι ≫ f) ↔
      ∀ v : points B S hS V.toFunctor,
        IsFlatAt B S hS f (pointsMap B S hS V.toFunctor V.ι v) := by
  rw [isFlat_iff_forall_isFlatAt B S hS (V.ι ≫ f)]
  exact forall_congr' fun v => (isFlatAt_iff_of_isOpenSubspace B S hS hX hY V hV f v).symm

/-- The open set of points at which a morphism of algebraic spaces locally of finite
presentation is flat (**Stacks 05WV** for the structure sheaf). -/
private noncomputable abbrev flatPoints {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    TopologicalSpace.Opens (points B S hS X) :=
  ⟨{x | IsFlatAt B S hS f x}, isOpen_setOf_isFlatAt B S hS hX hY f hf⟩

/-- **Stacks 06M5, entry (4), hypothesis (3) of Stacks 06M3.** For `𝒬 = ` locally of finite
presentation and `𝒫 = ` flat: every morphism `f : X ⟶ Y` of algebraic spaces over `S` which is
locally of finite presentation has a largest open subspace of `X` on which it is flat, and its
point set is exactly the set of points at which `f` is flat.

The set of points at which `f` is flat is open by **Stacks 05WV** for the structure sheaf,
`AlgebraicGeometry.Space.isOpen_setOf_isFlatAt`, and an open subspace on which `f` is flat is one
at all of whose points `f` is flat. The second clause is the source's remark that, because `f`
has `𝒬`, `W(𝒫, f)` is the set of points at which `f` is flat; without `𝒬` it is only the interior
of that set, which is the warning of **Stacks 06M4**. -/
@[stacks 06M5 "entry (4), flat: hypothesis (3) of 06M3"]
theorem exists_isGreatest_isFlat
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    ∃ W : {W : Subfunctor X // IsOpenSubspace B S hS W},
      IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
        IsFlat B S hS (V.1.ι ≫ f)} W ∧
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) =
        {x : points B S hS X | IsFlatAt B S hS f x} := by
  exact exists_isGreatest_of_forall_mem B S hS hX (flatPoints B S hS hX hY f hf) _ fun V =>
    isFlat_comp_ι_iff B S hS hX hY f V.1 V.2

/-- **Stacks 06M5, entry (4), hypothesis (4) of Stacks 06M3.** In a cartesian square of
algebraic spaces over `S` whose right vertical arrow `f` is locally of finite presentation and
whose bottom arrow `g` is flat, any largest open subspace of the source of the base change `f'`
on which `f'` is flat is the inverse image of any largest open subspace of `X` on which `f` is
flat.

The entry's `ℛ` is flat and locally of finite presentation; only flatness of `g` is used. By
hypothesis (3) both open subspaces are the loci of points at which the morphisms are flat, the
base change being locally of finite presentation as well, and those correspond under a flat
base change, which is **Stacks 05WW** for the structure sheaf,
`AlgebraicGeometry.Space.isFlatAt_iff_of_isPullback_of_isFlat`. -/
@[stacks 06M5 "entry (4), flat: hypothesis (4) of 06M3"]
theorem eq_preimage_of_isGreatest_isFlat
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFinitePresentation B S hS f) (hg : IsFlat B S hS g)
    (W : {W : Subfunctor X // IsOpenSubspace B S hS W})
    (hW : IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
      IsFlat B S hS (V.1.ι ≫ f)} W)
    (W' : {W' : Subfunctor X' // IsOpenSubspace B S hS W'})
    (hW' : IsGreatest {V : {V : Subfunctor X' // IsOpenSubspace B S hS V} |
      IsFlat B S hS (V.1.ι ≫ f')} W') :
    W'.1 = W.1.preimage g' := by
  have hcat := isPullback_homMk B S hS sq hX' hX hY' hY
  have hf' : IsLocallyOfFinitePresentation B S hS f' :=
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hcat hf
  refine eq_preimage_of_isGreatest_of_preimage_eq B S hS hX' hX g' (flatPoints B S hS hX hY f hf)
    (flatPoints B S hS hX' hY' f' hf') ?_ _
    (fun V => isFlat_comp_ι_iff B S hS hX hY f V.1 V.2) _
    (fun V => isFlat_comp_ι_iff B S hS hX' hY' f' V.1 V.2) W hW W' hW'
  ext x'
  exact isFlatAt_iff_of_isPullback_of_isFlat B S hS hcat hg x'

/-! ### Entry (5): étale morphisms -/

/-- A morphism of algebraic spaces over `S` which is locally of finite presentation is étale on
an open subspace of its source exactly when it is unramified and flat at every point of that
open subspace: an étale morphism is unramified (**Stacks 06CR**) and flat, and conversely a
flat, unramified morphism locally of finite presentation is étale (**Stacks 06LU**). -/
private theorem isEtale_comp_ι_iff {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (V : Subfunctor X) (hV : IsOpenSubspace B S hS V) :
    IsEtale B S hS (V.ι ≫ f) ↔
      ∀ v : points B S hS V.toFunctor,
        IsUnramifiedAt B S hS f (pointsMap B S hS V.toFunctor V.ι v) ∧
          IsFlatAt B S hS f (pointsMap B S hS V.toFunctor V.ι v) := by
  refine ⟨fun h v =>
    ⟨(isUnramified_comp_ι_iff B S hS hX hY f V hV).1 (isUnramified_of_isEtale B S hS h) v,
      (isFlat_comp_ι_iff B S hS hX hY f V hV).1 (isFlat_of_isEtale B S hS h) v⟩, fun h => ?_⟩
  have hlfp : IsLocallyOfFinitePresentation B S hS (V.ι ≫ f) :=
    isLocallyOfFinitePresentation_comp B S hS hV.1 hX hY V.ι f
      (isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_ι_of_isOpenSubspace hV)) hf
  exact isEtale_of_isFlat_of_isUnramified B S hS hV.1 hY (V.ι ≫ f) hlfp
    ((isFlat_comp_ι_iff B S hS hX hY f V hV).2 fun v => (h v).2)
    ((isUnramified_comp_ι_iff B S hS hX hY f V hV).2 fun v => (h v).1)

/-- The open set of points at which a morphism of algebraic spaces locally of finite
presentation is both unramified and flat. -/
private noncomputable abbrev etalePoints {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    TopologicalSpace.Opens (points B S hS X) :=
  unramifiedPoints B S hS f ⊓ flatPoints B S hS hX hY f hf

/-- **Stacks 06M5, entry (5), hypothesis (3) of Stacks 06M3.** For `𝒬 = ` locally of finite
presentation and `𝒫 = ` étale: every morphism `f : X ⟶ Y` of algebraic spaces over `S` which is
locally of finite presentation has a largest open subspace of `X` on which it is étale, and its
point set is the set of points at which `f` is both unramified and flat.

This combines entries (3) and (4): the two sets of points are open, and on an open subspace `f`
is étale exactly when it is unramified and flat there, because an unramified morphism which is
flat and locally of finite presentation is étale (**Stacks 06LU**). -/
@[stacks 06M5 "entry (5), étale: hypothesis (3) of 06M3"]
theorem exists_isGreatest_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    ∃ W : {W : Subfunctor X // IsOpenSubspace B S hS W},
      IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
        IsEtale B S hS (V.1.ι ≫ f)} W ∧
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) =
        {x : points B S hS X | IsUnramifiedAt B S hS f x ∧ IsFlatAt B S hS f x} := by
  exact exists_isGreatest_of_forall_mem B S hS hX (etalePoints B S hS hX hY f hf) _ fun V =>
    isEtale_comp_ι_iff B S hS hX hY f hf V.1 V.2

/-- **Stacks 06M5, entry (5), hypothesis (4) of Stacks 06M3.** In a cartesian square of
algebraic spaces over `S` whose right vertical arrow `f` is locally of finite presentation and
whose bottom arrow `g` is flat, any largest open subspace of the source of the base change `f'`
on which `f'` is étale is the inverse image of any largest open subspace of `X` on which `f` is
étale.

The entry's `ℛ` is flat and locally of finite presentation; only flatness of `g` is used. By
hypothesis (3) both open subspaces are the loci of points at which the morphisms are unramified
and flat, and both conditions correspond under the base change: unramifiedness under any base
change (**Stacks 05W2**, part (2)) and flatness under a flat one (**Stacks 05WW** for the
structure sheaf). -/
@[stacks 06M5 "entry (5), étale: hypothesis (4) of 06M3"]
theorem eq_preimage_of_isGreatest_isEtale
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFinitePresentation B S hS f) (hg : IsFlat B S hS g)
    (W : {W : Subfunctor X // IsOpenSubspace B S hS W})
    (hW : IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} |
      IsEtale B S hS (V.1.ι ≫ f)} W)
    (W' : {W' : Subfunctor X' // IsOpenSubspace B S hS W'})
    (hW' : IsGreatest {V : {V : Subfunctor X' // IsOpenSubspace B S hS V} |
      IsEtale B S hS (V.1.ι ≫ f')} W') :
    W'.1 = W.1.preimage g' := by
  have hcat := isPullback_homMk B S hS sq hX' hX hY' hY
  have hf' : IsLocallyOfFinitePresentation B S hS f' :=
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hcat hf
  have hft : IsLocallyOfFiniteType B S hS f :=
    isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf
  refine eq_preimage_of_isGreatest_of_preimage_eq B S hS hX' hX g'
    (etalePoints B S hS hX hY f hf) (etalePoints B S hS hX' hY' f' hf') ?_ _
    (fun V => isEtale_comp_ι_iff B S hS hX hY f hf V.1 V.2) _
    (fun V => isEtale_comp_ι_iff B S hS hX' hY' f' hf' V.1 V.2) W hW W' hW'
  ext x'
  exact and_congr (isUnramifiedAt_iff_of_isPullback B S hS sq hX' hX hY' hY hft x').symm
    (isFlatAt_iff_of_isPullback_of_isFlat B S hS hcat hg x')

end AlgebraicGeometry.Space

end
