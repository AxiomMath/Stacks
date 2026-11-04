module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat

/-!
# Descending the flatness of a restriction to an open of the base

`AlgebraicGeometry.exists_flat_baseChange_of_limitBaseChange` is Stacks tag 04AI: a morphism
`f₀ : X₀ ⟶ Y₀` over a stage `Y₀` of a cofiltered inverse system of schemes, locally of finite
presentation, whose base change to the limit `Y = lim Y_i` is flat, is already flat after base
change to some later stage. It is stated in the `CategoryTheory.Over` idiom, about
`((Over.pullback g).map f₀).left`.

Step (6) of the Stacks proof of tag 0EVC applies that tag not to `f₀` but to its restriction
`f₀ ∣_ V₀` over an open `V₀ ⊆ Y₀`, and reads the hypothesis and the conclusion as statements
about the honest restrictions `f ∣_ V` and `f₁ ∣_ V₁`. This module supplies the missing
identification: the base change of `f₀ ∣_ V₀` along `p : Y ⟶ Y₀`, in the form
`CategoryTheory.Over.pullback` produces it, is the restriction of the base change of `f₀` to the
inverse image `p ⁻¹ᵁ V₀`.

## Main definitions

* `AlgebraicGeometry.morphismRestrictOver` is `f₀ ∣_ V₀` read as a morphism of schemes over `Y₀`,
  which is the shape `CategoryTheory.Over.pullback` consumes.

## Main results

* `AlgebraicGeometry.exists_isPullback_morphismRestrict`: the restriction of a base change is a
  base change of the restriction, along the restricted base-change morphism `p ∣_ V₀`.
* `AlgebraicGeometry.prop_morphismRestrict_iff_overPullback`: consequently a property of
  morphisms which respects isomorphisms holds for the restriction of a base change exactly when
  it holds for the morphism `CategoryTheory.Over.pullback` produces from `f₀ ∣_ V₀`.
* `AlgebraicGeometry.exists_flat_morphismRestrict_of_limit`: **Stacks tag 04AI for a
  restriction** — if the restriction of the base change to the limit is flat, then the
  restriction of the base change to some later stage is flat.

## Implementation notes

Both squares in play are pullbacks of the same cospan. On one side,
`AlgebraicGeometry.overPullback_isPullback` exhibits `((Over.pullback p).map (f₀ ∣_ V₀)).left` as
a base change of `f₀ ∣_ V₀` along the first projection `pullback V₀.ι p ⟶ V₀`. On the other,
Mathlib's `AlgebraicGeometry.isPullback_morphismRestrict` for `f` pastes with the square
presenting `f` as a base change of `f₀` to exhibit `f ∣_ (p ⁻¹ᵁ V₀)` as a base change of `f₀`
along `(p ⁻¹ᵁ V₀).ι ≫ p`; that composite factors as `(p ∣_ V₀) ≫ V₀.ι`, so cancelling the
pullback square of `f₀ ∣_ V₀` on the right exhibits `f ∣_ (p ⁻¹ᵁ V₀)` as a base change of
`f₀ ∣_ V₀` along `p ∣_ V₀`. The two base-change morphisms agree under
`AlgebraicGeometry.pullbackRestrictIsoRestrict`, so the two squares have literally the same
cospan and `CategoryTheory.IsPullback.isoIsPullback` compares their corners.

## References

* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

variable {X₀ Y₀ : Scheme.{u}}

/-- The restriction `f₀ ∣_ V₀` of a morphism `f₀ : X₀ ⟶ Y₀` to an open `V₀ ⊆ Y₀`, read as a
morphism in `CategoryTheory.Over Y₀` from the preimage `f₀ ⁻¹ᵁ V₀` to `V₀`. -/
def morphismRestrictOver (f₀ : X₀ ⟶ Y₀) (V₀ : Y₀.Opens) :
    (Over.mk ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀) : Over Y₀) ⟶ Over.mk V₀.ι :=
  Over.homMk (f₀ ∣_ V₀) (morphismRestrict_ι f₀ V₀)

/-- The morphism of schemes underlying `morphismRestrictOver f₀ V₀` is `f₀ ∣_ V₀`. -/
@[simp]
lemma morphismRestrictOver_left (f₀ : X₀ ⟶ Y₀) (V₀ : Y₀.Opens) :
    (morphismRestrictOver f₀ V₀).left = f₀ ∣_ V₀ :=
  rfl

/-- **The restriction of a base change is a base change of the restriction.** If `fW` is
cartesian over `f₀ : X₀ ⟶ Y₀` along `p : Y ⟶ Y₀`, then the restriction of `fW` to the inverse
image `p ⁻¹ᵁ V₀` of an open `V₀ ⊆ Y₀` is a base change of `f₀ ∣_ V₀` along the restricted
morphism `p ∣_ V₀`. -/
lemma exists_isPullback_morphismRestrict {Y XW : Scheme.{u}} (f₀ : X₀ ⟶ Y₀) (V₀ : Y₀.Opens)
    {p : Y ⟶ Y₀} {fW : XW ⟶ Y} {q : XW ⟶ X₀} (sq : IsPullback fW q p f₀) :
    ∃ r : (fW ⁻¹ᵁ p ⁻¹ᵁ V₀).toScheme ⟶ (f₀ ⁻¹ᵁ V₀).toScheme,
      IsPullback r (fW ∣_ (p ⁻¹ᵁ V₀)) (f₀ ∣_ V₀) (p ∣_ V₀) := by
  have t : IsPullback (f₀ ⁻¹ᵁ V₀).ι (f₀ ∣_ V₀) f₀ V₀.ι := (isPullback_morphismRestrict f₀ V₀).flip
  have big : IsPullback ((fW ⁻¹ᵁ p ⁻¹ᵁ V₀).ι ≫ q) (fW ∣_ (p ⁻¹ᵁ V₀)) f₀ ((p ∣_ V₀) ≫ V₀.ι) := by
    rw [morphismRestrict_ι p V₀]
    exact ((isPullback_morphismRestrict fW (p ⁻¹ᵁ V₀)).paste_vert sq).flip
  have hw : ((fW ⁻¹ᵁ p ⁻¹ᵁ V₀).ι ≫ q) ≫ f₀ =
      ((fW ∣_ (p ⁻¹ᵁ V₀)) ≫ (p ∣_ V₀)) ≫ V₀.ι := by
    rw [Category.assoc]; exact big.w
  refine ⟨t.lift _ _ hw, IsPullback.of_right ?_ (t.lift_snd _ _ hw) t⟩
  rw [t.lift_fst]
  exact big

/-- **The restriction of a base change, as the morphism `CategoryTheory.Over.pullback`
produces.** A property of morphisms of schemes which respects isomorphisms holds for the
restriction of a base change of `f₀` to the inverse image of `V₀` exactly when it holds for the
base change of `f₀ ∣_ V₀` in the `CategoryTheory.Over` idiom. -/
lemma prop_morphismRestrict_iff_overPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {Y XW : Scheme.{u}} (f₀ : X₀ ⟶ Y₀) (V₀ : Y₀.Opens)
    {p : Y ⟶ Y₀} {fW : XW ⟶ Y} {q : XW ⟶ X₀} (sq : IsPullback fW q p f₀) :
    P (fW ∣_ (p ⁻¹ᵁ V₀)) ↔ P ((Over.pullback p).map (morphismRestrictOver f₀ V₀)).left := by
  obtain ⟨r, hA⟩ := exists_isPullback_morphismRestrict f₀ V₀ sq
  obtain ⟨ε, hε⟩ : ∃ ε : pullback V₀.ι p ≅ (p ⁻¹ᵁ V₀).toScheme,
      ε.hom ≫ (p ∣_ V₀) = pullback.fst V₀.ι p :=
    ⟨pullbackSymmetry V₀.ι p ≪≫ pullbackRestrictIsoRestrict p V₀, by simp⟩
  have hB : IsPullback (pullback.fst ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀) p)
      ((Over.pullback p).map (morphismRestrictOver f₀ V₀)).left (f₀ ∣_ V₀)
      (pullback.fst V₀.ι p) :=
    overPullback_isPullback p (Over.mk ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀)) (Over.mk V₀.ι)
      (morphismRestrictOver f₀ V₀)
  have hB' : IsPullback (pullback.fst ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀) p)
      (((Over.pullback p).map (morphismRestrictOver f₀ V₀)).left ≫ ε.hom)
      (f₀ ∣_ V₀) (p ∣_ V₀) :=
    hB.of_iso (Iso.refl _) (Iso.refl _) ε (Iso.refl _) (by simp) (by simp) (by simp)
      (by simpa using hε.symm)
  refine MorphismProperty.arrow_mk_iso_iff P
    (Arrow.isoMk (hA.isoIsPullback _ _ hB') ε.symm ?_)
  have hsnd := hA.isoIsPullback_hom_snd ((f₀ ⁻¹ᵁ V₀).toScheme) ((p ⁻¹ᵁ V₀).toScheme) hB'
  simp only [Arrow.mk_hom, Iso.symm_hom]
  rw [← cancel_mono ε.hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hsnd

/-- **Stacks Project, Tag 04AI for the restriction to an open of the base.** Let `Y = lim D` be
the limit of a cofiltered inverse system of schemes with affine transition morphisms, let
`f₀ : X₀ ⟶ D.obj i₀` be a morphism over a stage and let `V₀ ⊆ D.obj i₀` be an open over which
`f₀` is locally of finite presentation. If `f` is cartesian over `f₀` along the cone leg and the
restriction `f ∣_ (c.π.app i₀ ⁻¹ᵁ V₀)` is flat, then there is a later stage at which the
restriction of the base change of `f₀` to the inverse image of `V₀` is already flat. -/
lemma exists_flat_morphismRestrict_of_limit {I : Type v} [Category.{w} I] [EssentiallySmall.{u} I]
    [IsCofiltered I] (D : Functor I Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ D.obj i₀) (V₀ : (D.obj i₀).Opens)
    [CompactSpace (f₀ ⁻¹ᵁ V₀).toScheme] [QuasiSeparatedSpace (f₀ ⁻¹ᵁ V₀).toScheme]
    [CompactSpace V₀.toScheme] [QuasiSeparatedSpace V₀.toScheme]
    [LocallyOfFinitePresentation (f₀ ∣_ V₀)]
    {X : Scheme.{u}} {f : X ⟶ c.pt} {x : X ⟶ X₀} (sq : IsPullback f x (c.π.app i₀) f₀)
    (hflat : Flat (f ∣_ (c.π.app i₀ ⁻¹ᵁ V₀))) :
    ∃ (i : I) (g : i ⟶ i₀), Flat (pullback.fst (D.map g) f₀ ∣_ (D.map g ⁻¹ᵁ V₀)) := by
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : CompactSpace (Over.mk ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀) : Over (D.obj i₀)).left :=
    ‹CompactSpace (f₀ ⁻¹ᵁ V₀).toScheme›
  have : QuasiSeparatedSpace (Over.mk ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀) : Over (D.obj i₀)).left :=
    ‹QuasiSeparatedSpace (f₀ ⁻¹ᵁ V₀).toScheme›
  have : CompactSpace (Over.mk V₀.ι : Over (D.obj i₀)).left := ‹CompactSpace V₀.toScheme›
  have : QuasiSeparatedSpace (Over.mk V₀.ι : Over (D.obj i₀)).left :=
    ‹QuasiSeparatedSpace V₀.toScheme›
  have : LocallyOfFinitePresentation (morphismRestrictOver f₀ V₀).left :=
    ‹LocallyOfFinitePresentation (f₀ ∣_ V₀)›
  have : Flat ((Over.pullback (c.π.app i₀)).map (morphismRestrictOver f₀ V₀)).left :=
    (prop_morphismRestrict_iff_overPullback (@Flat) f₀ V₀ sq).1 hflat
  obtain ⟨i, g, hg⟩ := exists_flat_baseChange_of_limitBaseChange D c i₀
    (Over.mk ((f₀ ⁻¹ᵁ V₀).ι ≫ f₀)) (Over.mk V₀.ι) (morphismRestrictOver f₀ V₀) hc
  exact ⟨i, g, (prop_morphismRestrict_iff_overPullback (@Flat) f₀ V₀
    (IsPullback.of_hasPullback (D.map g) f₀)).2 hg⟩

end AlgebraicGeometry

end
