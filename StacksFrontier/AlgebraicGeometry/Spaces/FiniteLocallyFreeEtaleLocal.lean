module

public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange

/-!
# Finite local freeness of a morphism of algebraic spaces is étale local on the target

Stacks 03ZW asserts the equivalence of four conditions on a morphism `f : X ⟶ Y` of algebraic
spaces over a scheme `S`:

1. `f` is representable and finite locally free,
2. `f` is finite locally free,
3. there exists a scheme `V` and a surjective étale morphism `V ⟶ Y` such that `V ×_Y X ⟶ V`
   is finite locally free, and
4. there exists a Zariski covering `Y = ⋃ Yᵢ` such that each `f⁻¹(Yᵢ) ⟶ Yᵢ` is finite locally
   free.

This file proves the equivalence of conditions (1) and (3), both for finite local freeness and
for finite local freeness of a fixed rank, and in two shapes: with the chart existentially
quantified, as the source states condition (3), and at one given surjective étale chart, which
is the shape a consumer that already has a chart in hand needs.  The second shape comes in two
variants, according to whether surjectivity of the chart is given in the relatively
representable sense or on the point sets of Tag 03BU; the two agree by Tag 03MD.

Condition (1) is read as `CategoryTheory.MorphismProperty.presheaf` of the inverse image along
`AlgebraicGeometry.BigFppfOver.toScheme` of the corresponding property of morphisms of schemes:
that is exactly "`f` is representable and every represented base change of `f` is finite locally
free", which is what "finite locally free in the sense of Section 03HA" means for a
representable morphism. Condition (3) is read the same way for the base change of `f` along the
chart, so that it says both that `V ×_Y X` is a scheme and that `V ×_Y X ⟶ V` is finite locally
free.

**Condition (2) is not treated here.** For the two properties of Stacks 03ZP the analogous
condition (2) *is* the affine-base-change pattern, which is why
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal` can state Stacks 03ZQ with
condition (2) on the left. Finite local freeness is different: condition (2) of Stacks 03ZW is
the definition of Stacks 03ZV, `AlgebraicGeometry.Space.IsFiniteLocallyFree`, which asks that
`f` be affine and that the direct image `f_*𝒪_X` be a finite locally free `𝒪_Y`-module on the
small étale ringed site of `Y`. The comparison of that definition with condition (1) is a
separate statement, Stacks 03ZU, and it is not available in this development; see the
implementation notes.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.presheaf_iff_exists_etaleChart` and
  `AlgebraicGeometry.Space.presheaf_iff_of_surjectiveEtaleChart`: the two shapes of the
  equivalence, for an arbitrary property `Q` of scheme morphisms satisfying the hypotheses of
  `AlgebraicGeometry.Space.HoldsOnAffineBaseChange.of_etaleChart`.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_exists_etaleChart`: **Stacks 03ZW,
  conditions (1) and (3)**, and
  `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_of_surjectiveEtaleChart`, the same
  equivalence at a chart the consumer already holds.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_iff_exists_etaleChart` and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_iff_of_surjectiveEtaleChart`: the
  same equivalence for a fixed rank, which is the form the stratification of Stacks 07S8 is
  stated in.
* `Space.presheaf_iff_of_etaleChart_surjectiveOnPoints`,
  `Space.isFiniteLocallyFree_presheaf_iff_of_etaleChart_surjectiveOnPoints` and
  `Space.isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints` (in the
  namespace `AlgebraicGeometry`): the same three statements with the chart assumed étale and
  surjective *on points*, which is the shape in which the stratification files of Tag 07S8
  carry their chart.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFree` and
  `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFreeOfRank`:
  effective descent along a surjective étale morphism of the site for the two classes, which is
  Stacks 03I2 at those classes.

## Implementation notes

The whole content is already in
`AlgebraicGeometry.Space.holdsOnAffineBaseChange_iff_exists_etaleChart`, which proves the
equivalence for an arbitrary property `Q` of scheme morphisms that is Zariski local at the
target, has affine source over an affine target, respects isomorphisms, descends along the
surjective flat morphisms of finite presentation, and admits effective descent along the
surjective étale morphisms of the site. What this file does is discharge those five hypotheses
for finite local freeness, with and without a rank, and translate the affine-base-change shape
of the conclusion into the representable shape in which condition (3) of Stacks 03ZW is stated.

*The five hypotheses.* Respecting isomorphisms and Zariski locality at the target are the
instances of `StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.LocalAtTarget` and
`StacksDraft.AlgebraicGeometry.F3b.FiniteLocallyFreeRank.LocalAtTarget`. Descent along the
surjective flat morphisms of finite presentation is the fppf weakening, by
`AlgebraicGeometry.descendsAlong_fppf_of_descendsAlong_fpqc`, of the fpqc descent step of
Tag 02VO. Affineness of the source over an affine target is immediate from
`Stacks.Morphisms.IsFiniteLocallyFree.toIsAffineHom`. Effective descent is reduced to the finite
case, `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isFinite`, along
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_le`: a finite locally free
morphism is finite by Tag 02KB.

*From the affine-base-change shape to the representable shape.* In one direction this is
`AlgebraicGeometry.Space.HoldsOnAffineBaseChange.of_presheaf`, whose affineness side condition is
the same `hQaff`; in the other it is relative Tag 03JH,
`AlgebraicGeometry.Space.presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`, which needs
only Zariski locality. At a *given* chart the represented base change `hf.snd a` of the
representability witness is used instead of `CategoryTheory.Limits.pullback.snd f a`; the two
differ by the isomorphism of two pullbacks of one cospan, which
`CategoryTheory.MorphismProperty.cancel_left_of_respectsIso` absorbs, and the scheme-level
statement is recovered from the representable one by
`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`.

*What Stacks 03ZU would add.* Condition (2) is `AlgebraicGeometry.Space.IsFiniteLocallyFree`
(`StacksFrontier/AlgebraicGeometry/Spaces/FiniteLocallyFree.lean`), stated through
`AlgebraicGeometry.Space.pushforwardStructureModule` on the small étale ringed site of `Y`.
Nothing in either tree refers to that module outside the file defining it, so no comparison of
it with the conditions treated here exists, and Stacks 03ZU — whose own dependencies are
Tags 03LX, 03DN, 03I2, 02KD, 02VO and 0245 — is what would supply one. Until it is available the
equivalence of condition (2) with conditions (1), (3) and (4) is out of reach, and no statement
here mentions the direct image of the structure sheaf.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Scheme-level facts about finite locally free morphisms -/

/-- A finite locally free morphism of schemes is finite. This is one conjunct of Tag 02KB. -/
theorem isFiniteLocallyFree_le_isFinite :
    (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u}) ≤
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
  fun _ _ f hf =>
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      f).mp hf).1

/-- A morphism of schemes which is finite locally free of rank `r` is finite. -/
theorem isFiniteLocallyFreeOfRank_le_isFinite (r : ℕ) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r ≤
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
  fun _ _ f hf =>
    have _ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r := hf
    isFiniteLocallyFree_le_isFinite.{u} _ _ f
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f r)

/-- Finite local freeness satisfies fppf descent. This is the fppf weakening of the descent step
of Tag 02VO, and it is the form consumed by the effective-descent machinery of
`StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent`. -/
theorem isFiniteLocallyFree_descendsAlong_fppf :
    MorphismProperty.DescendsAlong
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have _ := Stacks.Morphisms.isFiniteLocallyFree_descendsAlong.{u}
  _root_.AlgebraicGeometry.descendsAlong_fppf_of_descendsAlong_fpqc _

/-- Finite local freeness of a fixed rank satisfies fppf descent. -/
theorem isFiniteLocallyFreeOfRank_descendsAlong_fppf (r : ℕ) :
    MorphismProperty.DescendsAlong
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have _ := Stacks.Morphisms.isFiniteLocallyFreeOfRank_descendsAlong.{u} r
  _root_.AlgebraicGeometry.descendsAlong_fppf_of_descendsAlong_fpqc _

/-- A finite locally free morphism of schemes has affine source over an affine target. -/
theorem isAffine_of_isFiniteLocallyFree {Z W : Scheme.{u}} (p : W ⟶ Z)
    (hp : Stacks.Morphisms.IsFiniteLocallyFree p) (hZ : IsAffine Z) : IsAffine W :=
  have _ := hp.toIsAffineHom
  have _ := hZ
  isAffine_of_isAffineHom p

/-- A morphism of schemes which is finite locally free of rank `r` has affine source over an
affine target. -/
theorem isAffine_of_isFiniteLocallyFreeOfRank {r : ℕ} {Z W : Scheme.{u}} (p : W ⟶ Z)
    (hp : Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r p) (hZ : IsAffine Z) :
    IsAffine W :=
  have h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r := hp
  isAffine_of_isFiniteLocallyFree p h.isFiniteLocallyFree hZ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Effective descent along a surjective étale morphism -/

/-- **Effective descent for finite locally free morphisms along a surjective étale morphism of
the site.** This is Stacks 03I2 at the class of finite locally free morphisms of schemes.

It follows from the finite case, because a finite locally free morphism is finite by Tag 02KB
and finite local freeness satisfies fppf descent. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFree :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u}) :=
  have _ := isFiniteLocallyFree_descendsAlong_fppf.{u}
  isEffectiveDescentAlongSurjectiveEtale_of_le
    (isEffectiveDescentAlongSurjectiveEtale_isFinite B S hS) isFiniteLocallyFree_le_isFinite.{u}

/-- **Effective descent for morphisms which are finite locally free of rank `r`, along a
surjective étale morphism of the site.** This is Stacks 03I2 at that class. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFreeOfRank (r : ℕ) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r) :=
  have _ := isFiniteLocallyFreeOfRank_descendsAlong_fppf.{u} r
  isEffectiveDescentAlongSurjectiveEtale_of_le
    (isEffectiveDescentAlongSurjectiveEtale_isFinite B S hS)
    (isFiniteLocallyFreeOfRank_le_isFinite.{u} r)

/-! ### The equivalence of conditions (1) and (3) for an arbitrary property -/

/-- **Conditions (1) and (3) are equivalent, for an arbitrary property `Q` of scheme morphisms**
satisfying the hypotheses of `AlgebraicGeometry.Space.HoldsOnAffineBaseChange.of_etaleChart`: a
morphism of algebraic spaces over `S` is representable with `Q` on its represented base changes
exactly when there is one surjective étale morphism from a representable presheaf onto its
target along which its base change is.

This is `AlgebraicGeometry.Space.holdsOnAffineBaseChange_iff_exists_etaleChart` with both sides
translated into the representable shape, which is the shape in which condition (3) of
Stacks 03ZW is stated: the base change over the chart is asserted to be *represented* by a
scheme over the chart with `Q`, not merely to have `Q` on its affine base changes. -/
theorem presheaf_iff_exists_etaleChart
    {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hQ : IsZariskiLocalAtTarget Q)
    (hQaff : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → IsAffine Z → IsAffine W)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS Q)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f ↔
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) := by
  refine ⟨fun hf => ?_, fun ⟨V, g, hs, he, h₃⟩ =>
    presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS hQ hX hY
      (HoldsOnAffineBaseChange.of_etaleChart B S hS hQ hQaff hdesc hX hY hs he
        (HoldsOnAffineBaseChange.of_presheaf hQaff h₃))⟩
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := yoneda (C := BigFppfOver B S hS)) (Q.inverseImage (BigFppfOver.toScheme B S hS))
  obtain ⟨V, g, hs, he⟩ := hY.exists_atlas
  exact ⟨V, g, hs, he,
    MorphismProperty.of_isPullback (P := (Q.inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf) (IsPullback.of_hasPullback f g) hf⟩

/-- **Conditions (1) and (3) are equivalent at a given surjective étale chart**, for an
arbitrary property `Q` of scheme morphisms satisfying the hypotheses of
`AlgebraicGeometry.Space.HoldsOnAffineBaseChange.of_etaleChart` and stable under base change: a
representable morphism of algebraic spaces over `S` has `Q` on all of its represented base
changes exactly when the represented base change along one surjective étale chart has `Q`.

This is the form in which a consumer already holding a chart uses the equivalence; the
existentially quantified form is
`AlgebraicGeometry.Space.presheaf_iff_exists_etaleChart`. -/
theorem presheaf_iff_of_surjectiveEtaleChart
    {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso] [Q.IsStableUnderBaseChange]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hQ : IsZariskiLocalAtTarget Q)
    (hQaff : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → IsAffine Z → IsAffine W)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS Q)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {A : BigFppfOver B S hS} {a : yoneda.obj A ⟶ Y}
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f ↔
      Q ((BigFppfOver.toScheme B S hS).map (hf.snd a)) := by
  refine ⟨fun h => h.property a (hf.fst a) (hf.snd a) (hf.isPullback a), fun h => ?_⟩
  have hsq : ((IsPullback.of_hasPullback f a).isoIsPullback _ _ (hf.isPullback a)).hom ≫
      yoneda.map (hf.snd a) = pullback.snd f a :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  refine (presheaf_iff_exists_etaleChart B S hS hQ hQaff hdesc hX hY f).2 ⟨A, a, hs, he, ?_⟩
  rw [← hsq]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS Q (hf.snd a)).2 h)

/-! ### Stacks 03ZW for finite locally free morphisms -/

/-- **Stacks 03ZW, conditions (1) and (3).** A morphism of algebraic spaces over `S` is
representable and finite locally free exactly when there is one surjective étale morphism from a
representable presheaf onto its target along which its base change is representable and finite
locally free. -/
@[stacks 03ZW "conditions (1) and (3)"]
theorem isFiniteLocallyFree_presheaf_iff_exists_etaleChart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage
          (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) :=
  have _ := isFiniteLocallyFree_descendsAlong_fppf.{u}
  presheaf_iff_exists_etaleChart B S hS inferInstance
    (fun p hp hZ => isAffine_of_isFiniteLocallyFree p hp hZ)
    (isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFree B S hS) hX hY f

/-- **Stacks 03ZW, conditions (1) and (3), at a given surjective étale chart.** A representable
morphism of algebraic spaces over `S` is finite locally free exactly when its represented base
change along one surjective étale chart of the target is.

This carries no attribute: condition (3) of the source is existentially quantified over the
chart, which is
`AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_exists_etaleChart`, and that one
theorem is already a covering set for the equivalence. The present form is the same equivalence
specialized to a chart the consumer already holds, and it follows from the existential form
together with the atlas of the target. -/
theorem isFiniteLocallyFree_presheaf_iff_of_surjectiveEtaleChart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {A : BigFppfOver B S hS} {a : yoneda.obj A ⟶ Y}
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map (hf.snd a)) :=
  have _ := isFiniteLocallyFree_descendsAlong_fppf.{u}
  have _ : MorphismProperty.IsStableUnderBaseChange
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u}) :=
    inferInstance
  presheaf_iff_of_surjectiveEtaleChart B S hS inferInstance
    (fun p hp hZ => isAffine_of_isFiniteLocallyFree p hp hZ)
    (isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFree B S hS) hX hY hf hs he

/-! ### The same equivalence for a fixed rank -/

/-- **The rank refinement of Stacks 03ZW, conditions (1) and (3).** A morphism of algebraic
spaces over `S` is representable and finite locally free of rank `r` exactly when there is one
surjective étale morphism from a representable presheaf onto its target along which its base
change is representable and finite locally free of rank `r`.

Stacks 03ZW states no rank, so this carries no attribute; the rank clause of the definition is
Stacks 03ZV, and the corresponding rank clause of the fpqc locality which makes the argument work
is the second assertion of Tag 02VO. This is the form the stratification of Stacks 07S8 is stated
in. -/
theorem isFiniteLocallyFreeOfRank_presheaf_iff_exists_etaleChart (r : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage
          (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
          (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) :=
  have _ := isFiniteLocallyFreeOfRank_descendsAlong_fppf.{u} r
  presheaf_iff_exists_etaleChart B S hS inferInstance
    (fun p hp hZ => isAffine_of_isFiniteLocallyFreeOfRank p hp hZ)
    (isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFreeOfRank B S hS r) hX hY f

/-- **The rank refinement of Stacks 03ZW, conditions (1) and (3), at a given surjective étale
chart.** A representable morphism of algebraic spaces over `S` is finite locally free of rank `r`
exactly when its represented base change along one surjective étale chart of the target is.

This is the bridge from the chart-level scheme predicate
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank` to a predicate on the morphism of algebraic spaces
itself, in the shape the stratification of Stacks 07S8 consumes. It carries no attribute for the
reason recorded on
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_iff_exists_etaleChart`. -/
theorem isFiniteLocallyFreeOfRank_presheaf_iff_of_surjectiveEtaleChart (r : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {A : BigFppfOver B S hS} {a : yoneda.obj A ⟶ Y}
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((BigFppfOver.toScheme B S hS).map (hf.snd a)) r :=
  have _ := isFiniteLocallyFreeOfRank_descendsAlong_fppf.{u} r
  presheaf_iff_of_surjectiveEtaleChart B S hS inferInstance
    (fun p hp hZ => isAffine_of_isFiniteLocallyFreeOfRank p hp hZ)
    (isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFreeOfRank B S hS r) hX hY hf hs he

/-! ### The chart hypotheses in the shape of a chart surjective on points -/

/-- **Conditions (1) and (3) at a chart which is étale and surjective on points**, for an
arbitrary property `Q` as in `AlgebraicGeometry.Space.presheaf_iff_of_surjectiveEtaleChart`.

The chart hypotheses are the ones the stratification files of Tag 07S8 carry — étaleness in the
relatively representable sense, surjectivity on the point sets of Tag 03BU — rather than
surjectivity in the relatively representable sense. The two forms of surjectivity agree by
Tag 03MD, `AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective`, applied to the chart,
whose representability is part of its étaleness. -/
theorem presheaf_iff_of_etaleChart_surjectiveOnPoints
    {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso] [Q.IsStableUnderBaseChange]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hQ : IsZariskiLocalAtTarget Q)
    (hQaff : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → IsAffine Z → IsAffine W)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS Q)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {A : BigFppfOver B S hS} {a : yoneda.obj A ⟶ Y}
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hasurj : Function.Surjective (pointsMap B S hS (yoneda.obj A) a)) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f ↔
      Q ((BigFppfOver.toScheme B S hS).map (hf.snd a)) :=
  presheaf_iff_of_surjectiveEtaleChart B S hS hQ hQaff hdesc hX hY hf
    ((presheafSurjective_iff_isSurjective B S hS (isAlgebraicSpace_yoneda B S hS A) hY a
      he.rep).2 hasurj) he

/-- **Stacks 03ZW, conditions (1) and (3), at a chart which is étale and surjective on
points.** -/
theorem isFiniteLocallyFree_presheaf_iff_of_etaleChart_surjectiveOnPoints
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {A : BigFppfOver B S hS} {a : yoneda.obj A ⟶ Y}
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hasurj : Function.Surjective (pointsMap B S hS (yoneda.obj A) a)) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map (hf.snd a)) :=
  have _ := isFiniteLocallyFree_descendsAlong_fppf.{u}
  have _ : MorphismProperty.IsStableUnderBaseChange
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u}) :=
    inferInstance
  presheaf_iff_of_etaleChart_surjectiveOnPoints B S hS inferInstance
    (fun p hp hZ => isAffine_of_isFiniteLocallyFree p hp hZ)
    (isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFree B S hS) hX hY hf he hasurj

/-- **The rank refinement of Stacks 03ZW, conditions (1) and (3), at a chart which is étale and
surjective on points.** A representable morphism of algebraic spaces over `S` is finite locally
free of rank `r` exactly when its represented base change along one chart which is étale and
surjective on points is.

This is the form of the bridge whose chart hypotheses are literally those carried by
`AlgebraicGeometry.Space.isClosed_image_pointsMap_isFiniteLocallyFreeOfRank_locus`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartFibrePropertyDescent.lean`), so that the
stratification of Tag 07S8 may pass its own chart straight into it. It carries no attribute for
the reason recorded on
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_iff_exists_etaleChart`. -/
theorem isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints (r : ℕ)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {A : BigFppfOver B S hS} {a : yoneda.obj A ⟶ Y}
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hasurj : Function.Surjective (pointsMap B S hS (yoneda.obj A) a)) :
    (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((BigFppfOver.toScheme B S hS).map (hf.snd a)) r :=
  have _ := isFiniteLocallyFreeOfRank_descendsAlong_fppf.{u} r
  presheaf_iff_of_etaleChart_surjectiveOnPoints B S hS inferInstance
    (fun p hp hZ => isAffine_of_isFiniteLocallyFreeOfRank p hp hZ)
    (isEffectiveDescentAlongSurjectiveEtale_isFiniteLocallyFreeOfRank B S hS r) hX hY hf he
    hasurj

end AlgebraicGeometry.Space

end
