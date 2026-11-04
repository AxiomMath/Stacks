module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative diagonal of a base change

Let `f : X ⟶ Y` and `g : Y' ⟶ Y` be morphisms of a category with pullbacks, and write
`f' := pullback.snd f g` for the base change of `f` along `g`. The two projections of
`X ×_Y Y'` to `X` induce a canonical comparison morphism

`(X ×_Y Y') ×_{Y'} (X ×_Y Y') ⟶ X ×_Y X`

between the relative self-products, and this file records the two cartesian squares it sits in:

* the comparison morphism is itself a base change of `g`, along the morphism
  `X ×_Y X ⟶ Y` which is either projection followed by `f`;
* the relative diagonal of `f'` is the base change of the relative diagonal of `f` along the
  comparison morphism.

Together they say that the relative diagonal commutes with base change. That is what lets a
property of morphisms defined by a condition on the relative diagonal — being separated,
locally separated or quasi-separated — inherit stability under base change and locality on the
target from the condition imposed on the diagonal.

## Main results

* `CategoryTheory.Limits.isPullback_pullbackSelfProductMap`: the comparison morphism is a base
  change of `g`.
* `CategoryTheory.Limits.isPullback_diagonal_pullbackSnd`: the diagonal of the base change is
  the base change of the diagonal.

## Implementation notes

Mathlib's `CategoryTheory.Limits.pullback_fst_map_snd_isPullback` is the second square for an
arbitrary pair of morphisms into `X ×_Y Y'`. Specialising it to the pair of identities does not
give the square below on the nose: the top left corner becomes the pullback of two identity
morphisms rather than `X ×_Y Y'` itself, and the identities stay composed into the morphisms of
the specialised square, so neither its corners nor its edges match. Both squares are therefore
produced here from the universal property of the pullback directly.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {X Y Y' : C} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The canonical comparison morphism from the relative self-product of the base change
`pullback.snd f g` of `f` along `g` to the relative self-product of `f`, induced by the two
projections of `X ×_Y Y'` to `X`. -/
@[ega "IV 16.4.1" "special case"]
noncomputable abbrev pullbackSelfProductMap :
    pullback (pullback.snd f g) (pullback.snd f g) ⟶ pullback f f :=
  pullback.map (pullback.snd f g) (pullback.snd f g) f f
    (pullback.fst f g) (pullback.fst f g) g
    pullback.condition.symm pullback.condition.symm

/-- The first projection of the comparison morphism of relative self-products. -/
@[reassoc (attr := simp)]
theorem pullbackSelfProductMap_fst :
    pullbackSelfProductMap f g ≫ pullback.fst f f =
      pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

/-- The second projection of the comparison morphism of relative self-products. -/
@[reassoc (attr := simp)]
theorem pullbackSelfProductMap_snd :
    pullbackSelfProductMap f g ≫ pullback.snd f f =
      pullback.snd (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g :=
  pullback.lift_snd _ _ _

section

variable {W : C} (a : W ⟶ Y') (b : W ⟶ pullback f f)
  (hc : a ≫ g = b ≫ pullback.fst f f ≫ f)

include hc

/-- The first of the two morphisms `W ⟶ X ×_Y Y'` out of a cone over the cospan of `g` and
`X ×_Y X ⟶ Y`: it is the first projection of the cone's leg to `X ×_Y X`, together with its leg
to `Y'`. -/
private noncomputable def coneLegFst : W ⟶ pullback f g :=
  pullback.lift (b ≫ pullback.fst f f) a (by simpa using hc.symm)

/-- The second of the two morphisms `W ⟶ X ×_Y Y'` out of a cone over the cospan of `g` and
`X ×_Y X ⟶ Y`: it is the second projection of the cone's leg to `X ×_Y X`, together with its leg
to `Y'`. -/
private noncomputable def coneLegSnd : W ⟶ pullback f g :=
  pullback.lift (b ≫ pullback.snd f f) a
    (by rw [Category.assoc, ← pullback.condition]; simpa using hc.symm)

/-- The projection of `coneLegFst` to `X`. -/
private theorem coneLegFst_fst :
    coneLegFst f g a b hc ≫ pullback.fst f g = b ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

/-- The projection of `coneLegFst` to `Y'`. -/
private theorem coneLegFst_snd : coneLegFst f g a b hc ≫ pullback.snd f g = a :=
  pullback.lift_snd _ _ _

/-- The projection of `coneLegSnd` to `X`. -/
private theorem coneLegSnd_fst :
    coneLegSnd f g a b hc ≫ pullback.fst f g = b ≫ pullback.snd f f :=
  pullback.lift_fst _ _ _

/-- The projection of `coneLegSnd` to `Y'`. -/
private theorem coneLegSnd_snd : coneLegSnd f g a b hc ≫ pullback.snd f g = a :=
  pullback.lift_snd _ _ _

end

/-- The comparison morphism of relative self-products is a base change of `g`: the square
whose other edges are the projection `(X ×_Y Y') ×_{Y'} (X ×_Y Y') ⟶ Y'` and the morphism
`X ×_Y X ⟶ Y` given by the first projection followed by `f` is cartesian. -/
theorem isPullback_pullbackSelfProductMap :
    IsPullback (pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.snd f g)
      (pullbackSelfProductMap f g) g (pullback.fst f f ≫ f) := by
  refine ⟨⟨by simp [pullback.condition]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift (coneLegFst f g s.fst s.snd s.condition)
      (coneLegSnd f g s.fst s.snd s.condition)
      (by rw [coneLegFst_snd, coneLegSnd_snd])) ?_ ?_ ?_⟩⟩
  · intro s
    rw [← Category.assoc, pullback.lift_fst, coneLegFst_snd]
  · intro s
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackSelfProductMap_fst, ← Category.assoc, pullback.lift_fst,
        coneLegFst_fst]
    · rw [Category.assoc, pullbackSelfProductMap_snd, ← Category.assoc, pullback.lift_snd,
        coneLegSnd_fst]
  · intro s m hm₁ hm₂
    have hA : m ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) =
        coneLegFst f g s.fst s.snd s.condition := by
      refine pullback.hom_ext ?_ ?_
      · rw [coneLegFst_fst, Category.assoc, ← pullbackSelfProductMap_fst, ← Category.assoc, hm₂]
      · rw [coneLegFst_snd, Category.assoc, hm₁]
    have hB : m ≫ pullback.snd (pullback.snd f g) (pullback.snd f g) =
        coneLegSnd f g s.fst s.snd s.condition := by
      refine pullback.hom_ext ?_ ?_
      · rw [coneLegSnd_fst, Category.assoc, ← pullbackSelfProductMap_snd, ← Category.assoc, hm₂]
      · rw [coneLegSnd_snd, Category.assoc,
          ← pullback.condition (f := pullback.snd f g) (g := pullback.snd f g), hm₁]
    refine pullback.hom_ext ?_ ?_
    · rw [hA, pullback.lift_fst]
    · rw [hB, pullback.lift_snd]

/-- A cone over the cospan of the diagonal of `f` and the comparison morphism has its leg
to the comparison morphism's source projecting to the cone's other leg through both
projections of `X ×_Y X`. -/
private theorem cone_snd_comp_pullbackSelfProductMap
    (s : PullbackCone (pullback.diagonal f) (pullbackSelfProductMap f g)) :
    s.snd ≫ pullbackSelfProductMap f g ≫ pullback.fst f f = s.fst ∧
      s.snd ≫ pullbackSelfProductMap f g ≫ pullback.snd f f = s.fst := by
  constructor <;> (rw [← Category.assoc, ← s.condition]; simp)

/-- The relative diagonal of the base change `pullback.snd f g` of `f` along `g` is the base
change of the relative diagonal of `f` along the comparison morphism of relative
self-products. -/
theorem isPullback_diagonal_pullbackSnd :
    IsPullback (pullback.fst f g) (pullback.diagonal (pullback.snd f g))
      (pullback.diagonal f) (pullbackSelfProductMap f g) := by
  refine ⟨⟨by ext <;> simp⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g)) ?_ ?_ ?_⟩⟩
  · intro s
    simpa using (cone_snd_comp_pullbackSelfProductMap f g s).1
  · intro s
    have hfs : s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) =
        s.snd ≫ pullback.snd (pullback.snd f g) (pullback.snd f g) := by
      refine pullback.hom_ext ?_ ?_
      · obtain ⟨h1, h2⟩ := cone_snd_comp_pullbackSelfProductMap f g s
        simp only [pullbackSelfProductMap_fst, pullbackSelfProductMap_snd] at h1 h2
        simp only [Category.assoc]
        rw [h1, h2]
      · simp only [Category.assoc, pullback.condition]
    refine pullback.hom_ext ?_ ?_ <;> simp [hfs]
  · intro s m hm₁ hm₂
    rw [← hm₂]
    simp

end CategoryTheory.Limits

end
