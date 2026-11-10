module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs

/-!
# Restriction of an étale equivalence relation

Restricting an étale equivalence relation along an étale morphism again gives an étale
equivalence relation.

## Main results

* `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_restrict` says that the restriction of
  an étale equivalence relation along an étale morphism is an étale equivalence relation.

## Implementation notes

Schemes over `S` are represented as objects of `CategoryTheory.Over S`. The restricted
relation is the pullback relation `AlgebraicGeometry.PreRelation.restrict`; the étaleness
hypothesis on the morphism is imposed on its underlying morphism of schemes.

Preservation of the equivalence-relation half is `AlgebraicGeometry.PreRelation` theory and is
inherited. For the two étaleness fields, the source and target of the restricted relation
become the source and target of the original after composition with the morphism, so it is
enough to know that the second projection of the pullback defining the restriction is étale;
that in turn reduces to étaleness of the product of the morphism with itself, which the
identification of the product in `Over S` with a fibre product of schemes turns into a base
change.

## References

* [Stacks Project, Tag 02WT](https://stacks.math.columbia.edu/tag/02WT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}} {R U U' : Over S}

/-- The product of an étale morphism of `S`-schemes with itself is étale on underlying
schemes. -/
private lemma etale_prod_map (g : U' ⟶ U) [Etale g.left] : Etale (prod.map g g).left := by
  let : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun f g hf hg ↦ Etale.etale_comp g (f := f)⟩
  let e' := Over.prodLeftIsoPullback U' U'
  let e := Over.prodLeftIsoPullback U U
  apply (MorphismProperty.cancel_left_of_respectsIso
    (@Etale : MorphismProperty Scheme.{u}) e'.inv _).mp
  apply (MorphismProperty.cancel_right_of_respectsIso
    (@Etale : MorphismProperty Scheme.{u}) _ e.hom).mp
  have h : e'.inv ≫ (prod.map g g).left ≫ e.hom =
      pullback.map U'.hom U'.hom U.hom U.hom g.left g.left (𝟙 S)
        (by simp) (by simp) := by
    ext
    · simp only [Category.assoc, e, Over.prodLeftIsoPullback_hom_fst]
      rw [← Category.assoc]
      change e'.inv ≫ (prod.map g g ≫ prod.fst).left = _
      rw [prod.map_fst, Over.comp_left]
      simp only [Over.prodLeftIsoPullback_inv_fst_assoc, pullback.map, e']
      rw [pullback.lift_fst]
    · simp only [Category.assoc, e, Over.prodLeftIsoPullback_hom_snd]
      rw [← Category.assoc]
      change e'.inv ≫ (prod.map g g ≫ prod.snd).left = _
      rw [prod.map_snd, Over.comp_left]
      simp only [Over.prodLeftIsoPullback_inv_snd_assoc, pullback.map, e']
      rw [pullback.lift_snd]
  rw [Category.assoc, h]
  exact MorphismProperty.pullbackMap (P := (@Etale : MorphismProperty Scheme.{u}))
    inferInstance inferInstance
    (by simp) (by simp)

/-- The second projection of a pullback of `S`-schemes along an étale morphism is étale on
underlying schemes. -/
private lemma etale_pullback_snd_over {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale f.left] : Etale (pullback.snd f g).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((IsPullback.of_hasPullback f g).map (Over.forget S)) (by
      change Etale f.left
      infer_instance)

/-- Restricting an étale equivalence relation along an étale morphism again gives an étale
equivalence relation. -/
@[stacks 02WT]
instance isEtaleEquivalenceRelation_restrict (j : Stacks.Groupoids.PreRelation R U)
    (g : U' ⟶ U) [Stacks.Groupoids.IsEtaleEquivalenceRelation j] [Etale g.left] :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (AlgebraicGeometry.PreRelation.restrict j g) := by
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · infer_instance
  all_goals
    apply MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ g.left inferInstance
    rw [← Over.comp_left]
    first
    | rw [show (AlgebraicGeometry.PreRelation.restrict j g).source ≫ g =
          pullback.snd (prod.map g g) j ≫ j.source by
            simp only [Stacks.Groupoids.PreRelation.source, Category.assoc]
            rw [← prod.map_snd g g, ← Category.assoc, pullback.condition]
            simp only [Category.assoc]]
    | rw [show (AlgebraicGeometry.PreRelation.restrict j g).target ≫ g =
          pullback.snd (prod.map g g) j ≫ j.target by
            simp only [Stacks.Groupoids.PreRelation.target, Category.assoc]
            rw [← prod.map_fst g g, ← Category.assoc, pullback.condition]
            simp only [Category.assoc]]
    rw [Over.comp_left]
    have : Etale (prod.map g g).left := etale_prod_map g
    have : Etale (pullback.snd (prod.map g g) j).left :=
      etale_pullback_snd_over (prod.map g g) j
    infer_instance

end AlgebraicGeometry.Space

end
