module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAtPointFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatLocusWarning
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyLocusOnSpaces

/-!
# The local-source lemma at the flat triple (Stacks 06M4)

**Stacks 06M4** says that **Stacks 06M3** applies at `P =` flat, `Q =` empty (no condition)
and `R =` flat and locally of finite presentation, and warns that for a morphism of algebraic
spaces `f : X ⟶ Y` the largest open subspace `W ⊆ X` on which `f` is flat is *not* the set of
points at which `f` is flat. This file proves all of it.

That 06M3 applies is the conjunction of its four hypotheses at this triple:

1. the three properties are stable under base change and fppf local on the target: for
   flatness this is `AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange` and
   `AlgebraicGeometry.Space.isFlat_isLocalAtTarget_fpqc` (fpqc, hence fppf), for local finite
   presentation `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isStableUnderBaseChange`
   and `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf`, and for the
   empty condition and the intersection they are Mathlib's instances for `⊤` and `⊓`;
2. smoothness implies flatness (**Stacks 04TA**) and local finite presentation
   (**Stacks 04AJ**);
3. every morphism of algebraic spaces has a largest open subspace of its source on which it is
   flat, `AlgebraicGeometry.Space.maximalFlatOpen` of `StacksFrontier/.../FlatLocusWarning.lean`;
4. that open subspace is compatible with base change along a morphism which is flat and locally
   of finite presentation: `AlgebraicGeometry.Space.maximalFlatOpen_eq_preimage_of_isPullback`,
   proved here.

The warning is carried in two forms: the point set of the largest flat open is the *interior*
of the pointwise flat locus (`AlgebraicGeometry.Space.range_pointsMap_maximalFlatOpen_eq_interior`),
and for some morphism the two differ
(`AlgebraicGeometry.Space.exists_range_pointsMap_maximalFlatOpen_ne_setOf_isFlatAt`).

## Main results

* `AlgebraicGeometry.Space.maximalFlatOpen_eq_preimage_of_isPullback`: hypothesis (4) of
  Stacks 06M3 at the flat triple, for the canonical largest flat open.
* `AlgebraicGeometry.Stack.localSourceLemmaHypotheses_flat_and_maximalFlatOpen_ne_flatLocus`:
  **Stacks 06M4** in full — hypotheses (1)–(4) of Stacks 06M3 for `P =` flat, `Q = ⊤`,
  `R =` flat and locally of finite presentation, in the form of
  `AlgebraicGeometry.Stack.SmoothImplies`,
  `AlgebraicGeometry.Stack.HasRelativePropertyLocusOnSpaces`
  and `AlgebraicGeometry.Stack.RelativePropertyLocusBaseChange` that the formalization of
  Stacks 06M3 consumes, together with both forms of the warning.

## Implementation notes

Hypothesis (4) is proved on points. By the correspondence of **Stacks 03BZ** an open subspace is
determined by its point set, and the point set of the largest flat open is the interior of the
pointwise flat locus. Along the base change `g' : X' ⟶ X` of a flat morphism the pointwise flat
locus of `f'` is the inverse image of that of `f`
(`AlgebraicGeometry.Space.isFlatAt_iff_of_isPullback_of_isFlat`, the structure sheaf case of
**Stacks 05VW**). Taking interiors commutes with the inverse image along a continuous open map,
and `g'` is open on points because it is flat and locally of finite presentation, being a base
change of `g` (**Stacks 042S**). Finally the inverse image of an open subspace has as point set
the inverse image of its point set, the square being cartesian. The pointwise flat locus itself
need not be open, so the interior is essential, and local finite presentation of `g` is used
exactly for the openness of `g'`.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
* [Stacks Project, Tag 06M4](https://stacks.math.columbia.edu/tag/06M4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Hypothesis (4) of Stacks 06M3 at `P =` flat and `R =` flat and locally of finite
presentation.** For a cartesian square of algebraic spaces over `S` whose base morphism `g` is
flat and locally of finite presentation, the largest open subspace of the source of the base
change `f'` on which `f'` is flat is the inverse image along `g'` of the largest open subspace
of the source of `f` on which `f` is flat. No hypothesis on `f` is needed.

Both sides are open subspaces, so it suffices to compare point sets (Stacks 03BZ). The left is
the interior of the pointwise flat locus of `f'`, which is the inverse image of the pointwise
flat locus of `f` (Stacks 05VW for the structure sheaf); `g'` is a base change of `g`, hence
flat and locally of finite presentation, hence continuous and open on points (Stacks 042S), so
the interior of that inverse image is the inverse image of the interior, which is the point set
of the right side. -/
theorem maximalFlatOpen_eq_preimage_of_isPullback {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hg : IsFlat B S hS g) (hglfp : IsLocallyOfFinitePresentation B S hS g) :
    maximalFlatOpen B S hS f' = (maximalFlatOpen B S hS f).preimage g' := by
  have hcat : IsPullback
      (ObjectProperty.homMk g' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk f' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y', hY'⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk g : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq
  have hg'flat : IsFlat B S hS g' :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hcat.flip hg
  have hg'lfp : IsLocallyOfFinitePresentation B S hS g' :=
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hcat.flip hglfp
  have hopen : IsOpenMap (pointsMap B S hS X' g') :=
    isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS hX' hX g' hg'flat
      hg'lfp
  have hcont : Continuous (pointsMap B S hS X' g') := continuous_pointsMap B S hS g'
  have hflatAt : {x' : points B S hS X' | IsFlatAt B S hS f' x'} =
      pointsMap B S hS X' g' ⁻¹' {x : points B S hS X | IsFlatAt B S hS f x} :=
    Set.ext fun x' => isFlatAt_iff_of_isPullback_of_isFlat B S hS hcat hg x'
  have hW := isOpenSubspace_maximalFlatOpen B S hS hX hY f
  have hP : IsOpenSubspace B S hS ((maximalFlatOpen B S hS f).preimage g') :=
    isOpenSubspace_preimage B S hS g' _ hX hX' hW
  have hrange : Set.range (pointsMap B S hS ((maximalFlatOpen B S hS f).preimage g').toFunctor
        ((maximalFlatOpen B S hS f).preimage g').ι) =
      pointsMap B S hS X' g' ⁻¹' Set.range (pointsMap B S hS
        (maximalFlatOpen B S hS f).toFunctor (maximalFlatOpen B S hS f).ι) := by
    rw [← Set.image_univ, ← Set.image_univ (f := pointsMap B S hS
        (maximalFlatOpen B S hS f).toFunctor (maximalFlatOpen B S hS f).ι),
      preimage_image_pointsMap_of_isPullback B S hS
        (Subfunctor.isPullback_preimage g' (maximalFlatOpen B S hS f)) Set.univ,
      Set.preimage_univ, Set.image_univ]
  have key : (⟨maximalFlatOpen B S hS f', isOpenSubspace_maximalFlatOpen B S hS hX' hY' f'⟩ :
      {V : Subfunctor X' // IsOpenSubspace B S hS V}) =
      ⟨(maximalFlatOpen B S hS f).preimage g', hP⟩ := by
    refine (openSubspacesOrderIso B S hS X' hX').injective (TopologicalSpace.Opens.ext ?_)
    refine (range_pointsMap_maximalFlatOpen_eq_interior B S hS hX' hY' f').trans ?_
    refine Eq.trans ?_ hrange.symm
    rw [hflatAt, ← hopen.preimage_interior_eq_interior_preimage hcont,
      range_pointsMap_maximalFlatOpen_eq_interior B S hS hX hY f]
  exact congrArg Subtype.val key

/-- The largest flat open, as an open subspace, is the greatest open subspace of the source on
which the morphism is flat. -/
theorem isGreatest_maximalFlatOpen {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsGreatest {V : {V : Subfunctor X // IsOpenSubspace B S hS V} | IsFlat B S hS (V.1.ι ≫ f)}
      ⟨maximalFlatOpen B S hS f, isOpenSubspace_maximalFlatOpen B S hS hX hY f⟩ :=
  ⟨isFlat_maximalFlatOpen B S hS hX hY f, fun V hV => le_maximalFlatOpen B S hS f V.2 hV⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06M4.** Lemma 06M3 applies to `P =` flat, `Q =` empty and `R =` flat and locally
of finite presentation, but the largest open subspace on which a morphism of algebraic spaces
is flat is not the set of points at which it is flat.

Precisely, with `P` flatness, `Q = ⊤` the empty condition and `R = P ⊓ ` local finite
presentation, as properties of morphisms of algebraic spaces over `S`:

* hypothesis (1) of Stacks 06M3: `P`, `Q` and `R` are stable under base change and local on the
  target for the fppf precoverage;
* hypothesis (2): smoothness implies `R` (`AlgebraicGeometry.Stack.SmoothImplies`);
* hypothesis (3): every morphism with `Q` has a greatest open subspace of its source on which it
  has `P` (`AlgebraicGeometry.Stack.HasRelativePropertyLocusOnSpaces`);
* hypothesis (4): that greatest open subspace is compatible with base change along a morphism
  with `R` (`AlgebraicGeometry.Stack.RelativePropertyLocusBaseChange`);
* the warning: for every morphism `f` of algebraic spaces over `S` the point set of the largest
  open subspace on which `f` is flat is the interior of the set of points at which `f` is flat,
  and there is a morphism of algebraic spaces for which it is not that set.

Hypothesis (4) is `AlgebraicGeometry.Space.maximalFlatOpen_eq_preimage_of_isPullback`,
the greatest open subspaces of hypotheses (3) and (4) being unique. -/
@[stacks 06M4 "06M3 applies at P = flat, Q = empty, R = flat and locally of finite \
presentation (its hypotheses (1)-(4)); the largest flat open is the interior of the flat locus, \
and for some morphism of algebraic spaces it is not the flat locus"]
theorem localSourceLemmaHypotheses_flat_and_maximalFlatOpen_ne_flatLocus :
    let P : MorphismProperty (AlgebraicSpaces B S hS) := fun _ _ k => Space.IsFlat B S hS k.hom
    let L : MorphismProperty (AlgebraicSpaces B S hS) :=
      fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k.hom
    let R : MorphismProperty (AlgebraicSpaces B S hS) := P ⊓ L
    (P.IsStableUnderBaseChange ∧
      P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) ∧
      (⊤ : MorphismProperty (AlgebraicSpaces B S hS)).IsStableUnderBaseChange ∧
      (⊤ : MorphismProperty (AlgebraicSpaces B S hS)).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, u} B S hS) ∧
      R.IsStableUnderBaseChange ∧
      R.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)) ∧
    SmoothImplies B S hS R ∧
    HasRelativePropertyLocusOnSpaces B S hS P ⊤ ∧
    RelativePropertyLocusBaseChange B S hS P ⊤ R ∧
    (∀ (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
        (_ : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y),
      Set.range (Space.pointsMap B S hS (Space.maximalFlatOpen B S hS f).toFunctor
          (Space.maximalFlatOpen B S hS f).ι) =
        interior {x : Space.points B S hS X | Space.IsFlatAt B S hS f x}) ∧
    ∃ (B' : BigFppfSite.{u}) (S' : Scheme.{u}) (hS' : B'.Contains S')
      (X Y : (BigFppfOver B' S' hS')ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B' S' hS' X)
      (_ : IsAlgebraicSpace B' S' hS' Y) (f : X ⟶ Y),
      Set.range (Space.pointsMap B' S' hS' (Space.maximalFlatOpen B' S' hS' f).toFunctor
          (Space.maximalFlatOpen B' S' hS' f).ι) ≠
        {x : Space.points B' S' hS' X | Space.IsFlatAt B' S' hS' f x} := by
  intro P L R
  have hPbc : P.IsStableUnderBaseChange := Space.isFlat_isStableUnderBaseChange B S hS
  have hPloc : P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hLbc : L.IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hLloc : L.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS
  have hRbc : R.IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf (P := P) (Q := L)
  have hRloc : R.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.inf P L
  refine ⟨⟨hPbc, hPloc, inferInstance, inferInstance, hRbc, hRloc⟩, ?_, ?_, ?_,
    fun X Y hX hY f => Space.range_pointsMap_maximalFlatOpen_eq_interior B S hS hX hY f,
    Space.exists_range_pointsMap_maximalFlatOpen_ne_setOf_isFlatAt⟩
  · exact fun X Y hX hY g hg => ⟨Space.isFlat_of_isSmooth B S hS g hg,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hg⟩
  · exact fun X Y hX hY f _ => ⟨_, Space.isGreatest_maximalFlatOpen B S hS hX hY f⟩
  · intro X' X Y' Y hX' hX hY' hY g' f' f g sq _ hRg W hW W' hW'
    have hW₀ : W = ⟨Space.maximalFlatOpen B S hS f,
        Space.isOpenSubspace_maximalFlatOpen B S hS hX hY f⟩ :=
      hW.unique (Space.isGreatest_maximalFlatOpen B S hS hX hY f)
    have hW'₀ : W' = ⟨Space.maximalFlatOpen B S hS f',
        Space.isOpenSubspace_maximalFlatOpen B S hS hX' hY' f'⟩ :=
      hW'.unique (Space.isGreatest_maximalFlatOpen B S hS hX' hY' f')
    rw [hW₀, hW'₀]
    exact Space.maximalFlatOpen_eq_preimage_of_isPullback B S hS sq hX' hX hY' hY hRg.1 hRg.2

end AlgebraicGeometry.Stack

end
