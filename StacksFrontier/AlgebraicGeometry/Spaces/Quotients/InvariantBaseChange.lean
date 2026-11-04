module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace

/-!
# Base change of a pre-relation along an invariant morphism

Let `j : R ⟶ U ×_Z U` be a pre-relation over a base `Z` and let `φ : U ⟶ X` be a morphism
which is invariant under `j`, that is which identifies the target and the source of every
arrow. Then both `U` and `R` may be pulled back along any `f : X' ⟶ X`, and the pullbacks
carry a canonical pre-relation over `Z`: invariance is exactly what makes the source map of
`j` descend to the pullback of `U`, the target map descending for free.

The construction preserves each of the three conditions of a pre-equivalence relation, of a
relation and of an equivalence relation.

## Main definitions

* `AlgebraicGeometry.Space.baseChangedObject` and
  `AlgebraicGeometry.Space.baseChangedArrows`: the pullbacks of the object and of the arrow
  space, read over the base.
* `AlgebraicGeometry.Space.baseChangedObjectProj` and
  `AlgebraicGeometry.Space.baseChangedArrowsProj`: their projections to `U` and to `R`.
* `AlgebraicGeometry.Space.baseChangedPreRelation`: **Stacks 048G** and **Stacks 048H**, the
  canonical pre-relation on them, together with the four equations fixing it.

## Main results

* `AlgebraicGeometry.Space.baseChangedPreRelation_target_fst`,
  `AlgebraicGeometry.Space.baseChangedPreRelation_target_snd`,
  `AlgebraicGeometry.Space.baseChangedPreRelation_source_fst` and
  `AlgebraicGeometry.Space.baseChangedPreRelation_source_snd`: the four equations fixing the
  base-changed pre-relation, read off its specification.
* `AlgebraicGeometry.Space.rel_baseChanged_iff`: two points of the base-changed
  object space are related exactly when they have the same image in `X'` and their images in
  `U` are related.
* `AlgebraicGeometry.Space.isPreEquivalenceRelation_baseChangedPreRelation`: **Stacks 048G**,
  base change preserves pre-equivalence relations.
* `AlgebraicGeometry.Space.mono_baseChangedPreRelation`: **Stacks 048G**, base change
  preserves relations.
* `AlgebraicGeometry.Space.isEquivalenceRelation_baseChangedPreRelation`: **Stacks 048G**,
  base change preserves equivalence relations.

## Implementation notes

Everything is stated in the slice `CategoryTheory.Over Z` of presheaves on the big fppf site,
which is where `AlgebraicGeometry.Space.PreRelation` and
`AlgebraicGeometry.Space.IsPreEquivalenceRelation` live; the codomain `X` of the invariant
morphism is likewise an arbitrary presheaf, not necessarily an algebraic space and not
necessarily over the base. Presheaf categories have all pullbacks, so no limit hypothesis is
needed, and by **Stacks 02X2** the pullback of algebraic spaces is the presheaf pullback, so
the construction specializes to the one of the source.

The invariance hypothesis is `AlgebraicGeometry.Space.IsInvariant` of **Stacks 048E**, which
is stated over an arbitrary base object of an arbitrary category whose slice has binary
products and so applies to the slice of presheaves used here.

`baseChangedPreRelation` bundles the pre-relation with the four equations which identify its
target and source maps through both projections of the pullbacks; those equations, and not the
chosen `CategoryTheory.Limits.prod.lift`, are what the results about it use, so clients should
read them off `.property` rather than unfold the definition.

Flat base change of a pre-relation is the same construction with
`AlgebraicGeometry.Space.IsFlat` imposed on `f`, so no separate definition is introduced for
it; the tag is registered on that property.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 048E](https://stacks.math.columbia.edu/tag/048E)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 048H](https://stacks.math.columbia.edu/tag/048H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}
  {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The base-changed object and arrow spaces -/

/-- The object space of a pre-relation after base change along `f : X' ⟶ X`, read over the
base: the pullback of `f` and of a morphism `φ` out of `U`. -/
noncomputable abbrev baseChangedObject (φ : U.left ⟶ X) (f : X' ⟶ X) : Over Z :=
  Over.mk (pullback.snd f φ ≫ U.hom)

/-- The arrow space of a pre-relation after base change along `f : X' ⟶ X`, read over the
base: the pullback of `f` and of the composite of the target map with `φ`. -/
noncomputable abbrev baseChangedArrows (j : PreRelation R U) (φ : U.left ⟶ X)
    (f : X' ⟶ X) : Over Z :=
  Over.mk (pullback.snd f (j.target.left ≫ φ) ≫ R.hom)

/-- The projection of the base-changed object space to `U`, a morphism over the base. -/
noncomputable def baseChangedObjectProj (φ : U.left ⟶ X) (f : X' ⟶ X) :
    baseChangedObject φ f ⟶ U :=
  Over.homMk (pullback.snd f φ) rfl

/-- The projection of the base-changed arrow space to `R`, a morphism over the base. -/
noncomputable def baseChangedArrowsProj (j : PreRelation R U) (φ : U.left ⟶ X) (f : X' ⟶ X) :
    baseChangedArrows j φ f ⟶ R :=
  Over.homMk (pullback.snd f (j.target.left ≫ φ)) rfl

/-- The projection of the base-changed object space to `U` is the second projection of the
pullback. -/
@[simp]
theorem baseChangedObjectProj_left (φ : U.left ⟶ X) (f : X' ⟶ X) :
    (baseChangedObjectProj φ f).left = pullback.snd f φ := rfl

/-- The projection of the base-changed arrow space to `R` is the second projection of the
pullback. -/
@[simp]
theorem baseChangedArrowsProj_left (j : PreRelation R U) (φ : U.left ⟶ X) (f : X' ⟶ X) :
    (baseChangedArrowsProj j φ f).left = pullback.snd f (j.target.left ≫ φ) := rfl

/-! ### The base-changed pre-relation -/

/-- **Stacks 048G** and **Stacks 048H.** The canonical pre-relation on the base changes of the
object and of the arrow space of an invariant pre-relation. Its target and source maps are
fixed by their composites with the two projections of the pullbacks: both preserve the
component in `X'`, and on the component in `U` they are the target and the source of `j`. -/
@[stacks 048G "base_changed_pre_relation", stacks 048H "base change of the pre-relation"]
noncomputable def baseChangedPreRelation (j : PreRelation R U) (φ : U.left ⟶ X) (f : X' ⟶ X)
    (hφ : IsInvariant j φ) :
    { j' : PreRelation (baseChangedArrows j φ f) (baseChangedObject φ f) //
      ((j'.target.left ≫ pullback.fst f φ =
          pullback.fst f (j.target.left ≫ φ)) ∧
        (j'.target.left ≫ pullback.snd f φ =
          pullback.snd f (j.target.left ≫ φ) ≫ j.target.left)) ∧
      ((j'.source.left ≫ pullback.fst f φ =
          pullback.fst f (j.target.left ≫ φ)) ∧
        (j'.source.left ≫ pullback.snd f φ =
          pullback.snd f (j.target.left ≫ φ) ≫ j.source.left)) } := by
  let targetLift : pullback f (j.target.left ≫ φ) ⟶ pullback f φ :=
    pullback.lift (pullback.fst f (j.target.left ≫ φ))
      (pullback.snd f (j.target.left ≫ φ) ≫ j.target.left) (by
        simpa only [Category.assoc] using pullback.condition)
  let sourceLift : pullback f (j.target.left ≫ φ) ⟶ pullback f φ :=
    pullback.lift (pullback.fst f (j.target.left ≫ φ))
      (pullback.snd f (j.target.left ≫ φ) ≫ j.source.left) (by
        simpa only [Category.assoc, ← hφ] using pullback.condition)
  let targetMap : baseChangedArrows j φ f ⟶ baseChangedObject φ f :=
    Over.homMk targetLift (by
      change targetLift ≫ pullback.snd f φ ≫ U.hom =
        pullback.snd f (j.target.left ≫ φ) ≫ R.hom
      rw [← Category.assoc, show targetLift ≫ pullback.snd f φ = _ from
        pullback.lift_snd _ _ _, Category.assoc, Over.w j.target])
  let sourceMap : baseChangedArrows j φ f ⟶ baseChangedObject φ f :=
    Over.homMk sourceLift (by
      change sourceLift ≫ pullback.snd f φ ≫ U.hom =
        pullback.snd f (j.target.left ≫ φ) ≫ R.hom
      rw [← Category.assoc, show sourceLift ≫ pullback.snd f φ = _ from
        pullback.lift_snd _ _ _, Category.assoc, Over.w j.source])
  refine ⟨prod.lift targetMap sourceMap, ?_⟩
  have htarget : (PreRelation.target (prod.lift targetMap sourceMap)).left = targetLift :=
    congrArg Over.Hom.left (prod.lift_fst targetMap sourceMap)
  have hsource : (PreRelation.source (prod.lift targetMap sourceMap)).left = sourceLift :=
    congrArg Over.Hom.left (prod.lift_snd targetMap sourceMap)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [htarget]; exact pullback.lift_fst _ _ _
  · rw [htarget]; exact pullback.lift_snd _ _ _
  · rw [hsource]; exact pullback.lift_fst _ _ _
  · rw [hsource]; exact pullback.lift_snd _ _ _

/-! ### The four equations fixing the base-changed pre-relation -/

section Accessors

variable (j : PreRelation R U) (φ : U.left ⟶ X) (f : X' ⟶ X) (hφ : IsInvariant j φ)

/-- The target map of the base-changed pre-relation preserves the component in `X'`. -/
theorem baseChangedPreRelation_target_fst :
    (baseChangedPreRelation j φ f hφ).val.target.left ≫ pullback.fst f φ =
      pullback.fst f (j.target.left ≫ φ) :=
  (baseChangedPreRelation j φ f hφ).property.1.1

/-- On the component in `U` the target map of the base-changed pre-relation is the target map
of `j`. -/
theorem baseChangedPreRelation_target_snd :
    (baseChangedPreRelation j φ f hφ).val.target.left ≫ pullback.snd f φ =
      pullback.snd f (j.target.left ≫ φ) ≫ j.target.left :=
  (baseChangedPreRelation j φ f hφ).property.1.2

/-- The source map of the base-changed pre-relation preserves the component in `X'`. -/
theorem baseChangedPreRelation_source_fst :
    (baseChangedPreRelation j φ f hφ).val.source.left ≫ pullback.fst f φ =
      pullback.fst f (j.target.left ≫ φ) :=
  (baseChangedPreRelation j φ f hφ).property.2.1

/-- On the component in `U` the source map of the base-changed pre-relation is the source map
of `j`. -/
theorem baseChangedPreRelation_source_snd :
    (baseChangedPreRelation j φ f hφ).val.source.left ≫ pullback.snd f φ =
      pullback.snd f (j.target.left ≫ φ) ≫ j.source.left :=
  (baseChangedPreRelation j φ f hφ).property.2.2

end Accessors

/-! ### Preservation of the three conditions

The two preservation arguments use only the four equations which fix the target and the source
of the base-changed pre-relation, so they are given for an arbitrary pre-relation satisfying
them and then specialized to the canonical one.
-/

section Spec

variable {j : PreRelation R U} {φ : U.left ⟶ X} {f : X' ⟶ X}
  {j' : PreRelation (baseChangedArrows j φ f) (baseChangedObject φ f)}

/-- Two test points of the base-changed object space are related by the base-changed
pre-relation exactly when they have the same image in `X'` and their images in `U` are related
by `j`. -/
theorem rel_baseChanged_iff
    (htf : j'.target.left ≫ pullback.fst f φ = pullback.fst f (j.target.left ≫ φ))
    (hts : j'.target.left ≫ pullback.snd f φ =
      pullback.snd f (j.target.left ≫ φ) ≫ j.target.left)
    (hsf : j'.source.left ≫ pullback.fst f φ = pullback.fst f (j.target.left ≫ φ))
    (hss : j'.source.left ≫ pullback.snd f φ =
      pullback.snd f (j.target.left ≫ φ) ≫ j.source.left)
    {T : BigFppfOver B S hS} {b : yoneda.obj T ⟶ Z}
    (x y : TestPoint T b (baseChangedObject φ f)) :
    j'.Rel b x y ↔
      (x.1 ≫ pullback.fst f φ = y.1 ≫ pullback.fst f φ) ∧
        j.Rel b (mapTestPoint (baseChangedObjectProj φ f) x)
          (mapTestPoint (baseChangedObjectProj φ f) y) := by
  constructor
  · rintro ⟨r, hrx, hry⟩
    refine ⟨?_, mapTestPoint (baseChangedArrowsProj j φ f) r, ?_, ?_⟩
    · rw [← hrx, ← hry, Category.assoc, Category.assoc, htf, hsf]
    · show (r.1 ≫ pullback.snd f (j.target.left ≫ φ)) ≫ j.target.left =
        x.1 ≫ pullback.snd f φ
      rw [Category.assoc, ← hts, ← Category.assoc, hrx]
    · show (r.1 ≫ pullback.snd f (j.target.left ≫ φ)) ≫ j.source.left =
        y.1 ≫ pullback.snd f φ
      rw [Category.assoc, ← hss, ← Category.assoc, hry]
  · rintro ⟨hfst, r, hrx, hry⟩
    have hrx' : r.1 ≫ j.target.left = x.1 ≫ pullback.snd f φ := hrx
    have hry' : r.1 ≫ j.source.left = y.1 ≫ pullback.snd f φ := hry
    have hw : (x.1 ≫ pullback.fst f φ) ≫ f = r.1 ≫ (j.target.left ≫ φ) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← hrx', Category.assoc]
    refine ⟨⟨pullback.lift (x.1 ≫ pullback.fst f φ) r.1 hw, ?_⟩, ?_, ?_⟩
    · show pullback.lift _ _ hw ≫ pullback.snd f (j.target.left ≫ φ) ≫ R.hom = b
      rw [← Category.assoc, pullback.lift_snd]
      exact r.2
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, htf, pullback.lift_fst]
      · rw [Category.assoc, hts, ← Category.assoc, pullback.lift_snd, hrx']
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hsf, pullback.lift_fst, hfst]
      · rw [Category.assoc, hss, ← Category.assoc, pullback.lift_snd, hry']

/-- Base change along an invariant morphism preserves the pointwise equivalence property. -/
theorem isPreEquivalenceRelation_baseChanged
    (htf : j'.target.left ≫ pullback.fst f φ = pullback.fst f (j.target.left ≫ φ))
    (hts : j'.target.left ≫ pullback.snd f φ =
      pullback.snd f (j.target.left ≫ φ) ≫ j.target.left)
    (hsf : j'.source.left ≫ pullback.fst f φ = pullback.fst f (j.target.left ≫ φ))
    (hss : j'.source.left ≫ pullback.snd f φ =
      pullback.snd f (j.target.left ≫ φ) ≫ j.source.left)
    (hj : IsPreEquivalenceRelation j) :
    IsPreEquivalenceRelation j' := by
  intro T b
  refine ⟨fun x ↦ (rel_baseChanged_iff htf hts hsf hss x x).2 ⟨rfl, (hj T b).refl _⟩,
    fun {x y} hxy ↦ ?_, fun {x y z} hxy hyz ↦ ?_⟩
  · obtain ⟨hfst, hrel⟩ := (rel_baseChanged_iff htf hts hsf hss x y).1 hxy
    exact (rel_baseChanged_iff htf hts hsf hss y x).2 ⟨hfst.symm, (hj T b).symm hrel⟩
  · obtain ⟨hfst₁, hrel₁⟩ := (rel_baseChanged_iff htf hts hsf hss x y).1 hxy
    obtain ⟨hfst₂, hrel₂⟩ := (rel_baseChanged_iff htf hts hsf hss y z).1 hyz
    exact (rel_baseChanged_iff htf hts hsf hss x z).2
      ⟨hfst₁.trans hfst₂, (hj T b).trans hrel₁ hrel₂⟩

/-- Base change along an invariant morphism preserves relations, that is monomorphy of the map
to the product. -/
theorem mono_baseChanged
    (htf : j'.target.left ≫ pullback.fst f φ = pullback.fst f (j.target.left ≫ φ))
    (hts : j'.target.left ≫ pullback.snd f φ =
      pullback.snd f (j.target.left ≫ φ) ≫ j.target.left)
    (hss : j'.source.left ≫ pullback.snd f φ =
      pullback.snd f (j.target.left ≫ φ) ≫ j.source.left)
    [Mono j] : Mono j' := by
  refine ⟨fun {W} g h hgh ↦ ?_⟩
  have hcomp (k : _ ⟶ baseChangedObject φ f) : g.left ≫ (j' ≫ k).left = h.left ≫ (j' ≫ k).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, hgh, Category.assoc]
  have htl := hcomp prod.fst
  have hsl := hcomp prod.snd
  have hfst : g.left ≫ pullback.fst f (j.target.left ≫ φ) =
      h.left ≫ pullback.fst f (j.target.left ≫ φ) := by
    rw [← htf, ← Category.assoc, htl, Category.assoc]
  have hcancel (a : _ ⟶ pullback f φ) (b : R.left ⟶ U.left)
      (hab : a ≫ pullback.snd f φ = pullback.snd f (j.target.left ≫ φ) ≫ b)
      (hl : g.left ≫ a = h.left ≫ a) :
      (g.left ≫ pullback.snd f (j.target.left ≫ φ)) ≫ b =
        (h.left ≫ pullback.snd f (j.target.left ≫ φ)) ≫ b := by
    rw [Category.assoc, Category.assoc, ← hab, ← Category.assoc, hl, Category.assoc]
  have hsnd : g ≫ baseChangedArrowsProj j φ f = h ≫ baseChangedArrowsProj j φ f :=
    (cancel_mono j).mp (prod.hom_ext (Over.OverMorphism.ext (hcancel _ _ hts htl))
      (Over.OverMorphism.ext (hcancel _ _ hss hsl)))
  apply Over.OverMorphism.ext
  refine pullback.hom_ext hfst ?_
  simpa only [Over.comp_left, baseChangedArrowsProj_left] using congrArg Over.Hom.left hsnd

end Spec

/-- **Stacks 048G.** Base change along an invariant morphism preserves the pointwise
equivalence property of a pre-relation. -/
@[stacks 048G "pre_equivalence_preserved"]
theorem isPreEquivalenceRelation_baseChangedPreRelation (j : PreRelation R U)
    (φ : U.left ⟶ X) (f : X' ⟶ X) (hφ : IsInvariant j φ)
    (hj : IsPreEquivalenceRelation j) :
    IsPreEquivalenceRelation (baseChangedPreRelation j φ f hφ).val :=
  isPreEquivalenceRelation_baseChanged
    (baseChangedPreRelation j φ f hφ).property.1.1
    (baseChangedPreRelation j φ f hφ).property.1.2
    (baseChangedPreRelation j φ f hφ).property.2.1
    (baseChangedPreRelation j φ f hφ).property.2.2 hj

/-- **Stacks 048G.** Base change along an invariant morphism preserves relations, that is
monomorphy of the map to the product. -/
@[stacks 048G "relation_preserved"]
theorem mono_baseChangedPreRelation (j : PreRelation R U) (φ : U.left ⟶ X) (f : X' ⟶ X)
    (hφ : IsInvariant j φ) [Mono j] :
    Mono (baseChangedPreRelation j φ f hφ).val :=
  mono_baseChanged
    (baseChangedPreRelation j φ f hφ).property.1.1
    (baseChangedPreRelation j φ f hφ).property.1.2
    (baseChangedPreRelation j φ f hφ).property.2.2

/-- **Stacks 048G.** Base change along an invariant morphism preserves equivalence relations:
the base-changed pre-relation of an invariant equivalence relation is again an internal
categorical equivalence relation. -/
@[stacks 048G "equivalence_preserved"]
instance isEquivalenceRelation_baseChangedPreRelation (j : PreRelation R U) (φ : U.left ⟶ X)
    (f : X' ⟶ X) (hφ : IsInvariant j φ)
    [IsEquivalenceRelation j.target j.source] :
    IsEquivalenceRelation
      (PreRelation.target (baseChangedPreRelation j φ f hφ).val)
      (PreRelation.source (baseChangedPreRelation j φ f hφ).val) := by
  obtain ⟨hmono, hpre⟩ :=
    (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp ‹_›
  have : Mono j := hmono
  exact (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    (baseChangedPreRelation j φ f hφ).val).mpr
      ⟨mono_baseChangedPreRelation j φ f hφ,
        isPreEquivalenceRelation_baseChangedPreRelation j φ f hφ hpre⟩

-- Flat base change of a pre-relation is the same construction with flatness imposed on the
-- morphism along which it is taken, so the tag is registered on that property.
add_to_stacks 048H "flat base change" AlgebraicGeometry.Space.IsFlat

end AlgebraicGeometry.Space

end
