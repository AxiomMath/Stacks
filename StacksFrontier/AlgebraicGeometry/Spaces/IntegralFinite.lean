module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Comparison lemmas for integral and finite morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *integral*, respectively *finite*, when
its base change along every morphism from an affine object of the big fppf site of `S` is
represented by an affine object of the site whose projection to the test object is an
integral, respectively finite, morphism of schemes. Both properties are instances of a
single pattern: a property `Q` of scheme morphisms tested on exactly those base changes.

This file isolates that pattern as
`AlgebraicGeometry.Space.HoldsOnAffineBaseChange`, identifies the two properties of
Stacks 03ZP with its instances, and proves, for an arbitrary `Q`, the comparisons with the
other three conditions of Stacks 03ZQ which do not require descent along a covering.

## Main definitions

* `AlgebraicGeometry.Space.HoldsOnAffineBaseChange` says that a property `Q` of scheme
  morphisms holds on the represented base changes of a morphism of presheaves along the
  morphisms out of the affine objects of the site.

## Main results

* `AlgebraicGeometry.Space.isIntegralHom_iff_holdsOnAffineBaseChange` and
  `AlgebraicGeometry.Space.isFinite_iff_holdsOnAffineBaseChange` identify
  `AlgebraicGeometry.Space.IsIntegralHom` and `AlgebraicGeometry.Space.IsFinite` with the
  instances of the pattern at Mathlib's `AlgebraicGeometry.IsIntegralHom` and
  `AlgebraicGeometry.IsFinite`.
* `AlgebraicGeometry.Space.isZariskiLocalAtTarget_isIntegralHom` and
  `AlgebraicGeometry.Space.isZariskiLocalAtTarget_isFinite`: integrality and finiteness of a
  morphism of schemes are Zariski local at the target.
* `AlgebraicGeometry.Space.HoldsOnAffineBaseChange.of_isPullback` is stability of the
  pattern under base change.
* `AlgebraicGeometry.Space.HoldsOnAffineBaseChange.of_presheaf` derives the pattern from
  representability together with `Q` on every represented base change, the implication
  (1) ⇒ (2) of Stacks 03ZQ.
* `AlgebraicGeometry.Space.HoldsOnAffineBaseChange.exists_etaleChart` and
  `AlgebraicGeometry.Space.HoldsOnAffineBaseChange.exists_zariskiCover` propagate the
  pattern to a surjective étale chart of the target and to the trivial Zariski covering of
  the target, the implications (2) ⇒ (3) and (2) ⇒ (4) of Stacks 03ZQ.
* `AlgebraicGeometry.Space.HoldsOnAffineBaseChange.exists_affine_coproduct_atlas` refines the
  first of these to the chart of Stacks 03FX, a disjoint union of affine objects of the site,
  over each summand of which the base change of the morphism is *represented* by an affine
  object of the site with `Q`.
* `AlgebraicGeometry.Space.isAffine_of_isIntegralHom` and
  `AlgebraicGeometry.Space.isAffine_of_isFinite` are the affineness of the source of an
  integral, respectively finite, morphism of schemes with affine target.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A property `Q` of scheme morphisms *holds on the affine base changes* of a morphism
`f : X ⟶ Y` of presheaves on the big fppf site of `S` when, for every object `Z` of the site
with affine underlying scheme and every morphism `g` from `yoneda.obj Z` to `Y`, the base
change of `f` along `g` is represented by an object `W` of the site with affine underlying
scheme whose projection to `Z` has `Q`. -/
abbrev HoldsOnAffineBaseChange (Q : MorphismProperty Scheme.{u})
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ (Z : BigFppfOver B S hS),
    IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
    ∀ (g : yoneda.obj Z ⟶ Y),
      ∃ (W : BigFppfOver B S hS) (p : W ⟶ Z) (q : yoneda.obj W ⟶ X),
        IsPullback q (yoneda.map p) f g ∧
          IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
          Q ((BigFppfOver.toScheme B S hS).map p)

variable {B S hS}

/-- Integrality of a morphism of algebraic spaces is the general affine-base-change pattern
at Mathlib's `AlgebraicGeometry.IsIntegralHom`. -/
theorem isIntegralHom_iff_holdsOnAffineBaseChange
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsIntegralHom B S hS f ↔
      HoldsOnAffineBaseChange B S hS @_root_.AlgebraicGeometry.IsIntegralHom f :=
  Iff.rfl

/-- Finiteness of a morphism of algebraic spaces is the general affine-base-change pattern at
Mathlib's `AlgebraicGeometry.IsFinite`. -/
theorem isFinite_iff_holdsOnAffineBaseChange
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsFinite B S hS f ↔
      HoldsOnAffineBaseChange B S hS @_root_.AlgebraicGeometry.IsFinite f := by
  refine ⟨fun h Z hZ g ↦ ?_, fun h Z hZ g ↦ ?_⟩
  · obtain ⟨W, p, q, hW, hQ, hpb⟩ := h Z hZ g
    exact ⟨W, p, q, hpb, hW, hQ⟩
  · obtain ⟨W, p, q, hpb, hW, hQ⟩ := h Z hZ g
    exact ⟨W, p, q, hW, hQ, hpb⟩

/-- An integral morphism of schemes has affine source over an affine target. -/
@[ega "II 6.1.2" "affine base"]
theorem isAffine_of_isIntegralHom {Z W : Scheme.{u}} (p : W ⟶ Z)
    (hp : _root_.AlgebraicGeometry.IsIntegralHom p) (hZ : IsAffine Z) : IsAffine W :=
  isAffine_of_isAffineHom p

/-- A finite morphism of schemes has affine source over an affine target. -/
theorem isAffine_of_isFinite {Z W : Scheme.{u}} (p : W ⟶ Z)
    (hp : _root_.AlgebraicGeometry.IsFinite p) (hZ : IsAffine Z) : IsAffine W :=
  isAffine_of_isAffineHom p

/-- Integrality of a morphism of schemes is Zariski local at the target. -/
@[sga "4 IV 8.5.5" "special case"]
theorem isZariskiLocalAtTarget_isIntegralHom :
    IsZariskiLocalAtTarget (@_root_.AlgebraicGeometry.IsIntegralHom.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    _root_.AlgebraicGeometry.IsIntegralHom.hasAffineProperty

/-- Finiteness of a morphism of schemes is Zariski local at the target. -/
@[ega "II 6.3.10"]
theorem isZariskiLocalAtTarget_isFinite :
    IsZariskiLocalAtTarget (@_root_.AlgebraicGeometry.IsFinite.{u}) := by
  rw [_root_.AlgebraicGeometry.IsFinite.eq_inf]
  have h₁ := isZariskiLocalAtTarget_isIntegralHom.{u}
  have h₂ : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FiniteType)
  exact .inf _ _

variable {Q : MorphismProperty Scheme.{u}} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The general affine-base-change pattern is stable under base change: if `f'` is the base
change of `f` along an arbitrary morphism of presheaves, in the sense that it sits in a
Cartesian square over `f`, then `Q` holds on the affine base changes of `f'` as soon as it
holds on those of `f`. -/
theorem HoldsOnAffineBaseChange.of_isPullback
    {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {k : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback k f' f g)
    (hf : HoldsOnAffineBaseChange B S hS Q f) :
    HoldsOnAffineBaseChange B S hS Q f' := by
  intro Z hZ h
  obtain ⟨W, p, q, hpb, hW, hQ⟩ := hf Z hZ (h ≫ g)
  exact ⟨W, p, _, IsPullback.of_right' hpb sq, hW, hQ⟩

/-- Suppose that a morphism of schemes with `Q` and affine target has affine source. If `f` is
representable and all of its represented base changes have `Q`, then `Q` holds on the affine
base changes of `f`. -/
theorem HoldsOnAffineBaseChange.of_presheaf
    (hQaff : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → IsAffine Z → IsAffine W)
    {f : X ⟶ Y}
    (hf : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf f) :
    HoldsOnAffineBaseChange B S hS Q f := fun _ hZ g ↦
  ⟨hf.rep.pullback g, hf.rep.snd g, hf.rep.fst g, hf.rep.isPullback g,
    hQaff _ (hf.property_snd g) hZ, hf.property_snd g⟩

/-- If `Q` holds on the affine base changes of `f`, then it does so after base change along some
surjective étale morphism from a representable presheaf onto the target. -/
theorem HoldsOnAffineBaseChange.exists_etaleChart {f : X ⟶ Y}
    (hY : IsAlgebraicSpace B S hS Y) (hf : HoldsOnAffineBaseChange B S hS Q f) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g ∧
      HoldsOnAffineBaseChange B S hS Q (pullback.snd f g) := by
  obtain ⟨U, g, hsurj, hetale⟩ := hY.exists_atlas
  exact ⟨U, g, hsurj, hetale, hf.of_isPullback (IsPullback.of_hasPullback f g)⟩

/-- If `Q` holds on the affine base changes of `f`, then it does so on the base changes of `f`
along the members of some Zariski covering of the target. -/
theorem HoldsOnAffineBaseChange.exists_zariskiCover {f : X ⟶ Y}
    (hY : IsAlgebraicSpace B S hS Y) (hf : HoldsOnAffineBaseChange B S hS Q f) :
    ∃ (I : Type u) (U : I → Subfunctor Y),
      IsZariskiCover B S hS I U ∧
        ∀ i, HoldsOnAffineBaseChange B S hS Q (pullback.snd f (U i).ι) :=
  ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hY,
    fun _ ↦ hf.of_isPullback (IsPullback.of_hasPullback _ _)⟩

/-- Suppose that `Q` holds on the affine base changes of `f`. Then the target carries a
surjective étale chart `g` whose underlying scheme is the disjoint union of the underlying schemes
of affine objects `W i` of the site, each of them an affine étale chart of the target in its own
right; `Q` holds on the affine base changes of the induced morphism over the chart; and over each
summand `W i` the base change of `f` is represented by an affine object `V` of the site whose
projection to `W i` has `Q`. -/
theorem HoldsOnAffineBaseChange.exists_affine_coproduct_atlas {f : X ⟶ Y}
    (hY : IsAlgebraicSpace B S hS Y) (hf : HoldsOnAffineBaseChange B S hS Q f) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y) (I : Type u)
      (W : I → BigFppfOver B S hS) (j : ∀ i, W i ⟶ U)
      (e : (∐ fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) ≅
        (BigFppfOver.toScheme B S hS).obj U),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (W i))) ∧
      (∀ i, Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) i ≫ e.hom =
        (BigFppfOver.toScheme B S hS).map (j i)) ∧
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (j i))) ∧
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (j i) ≫ g)) ∧
      HoldsOnAffineBaseChange B S hS Q (pullback.snd f g) ∧
      ∀ i, ∃ (V : BigFppfOver B S hS) (p : V ⟶ W i) (q : yoneda.obj V ⟶ X),
        IsPullback q (yoneda.map p) f (yoneda.map (j i) ≫ g) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        Q ((BigFppfOver.toScheme B S hS).map p) := by
  obtain ⟨U, g, I, W, j, e, hgS, hgE, hWaff, hje, hjimm, hjetale, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS Y hY
  exact ⟨U, g, I, W, j, e, hgS, hgE, hWaff, hje, hjimm, hjetale,
    hf.of_isPullback (IsPullback.of_hasPullback f g),
    fun i ↦ hf (W i) (hWaff i) (yoneda.map (j i) ≫ g)⟩

end AlgebraicGeometry.Space

end
