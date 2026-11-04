module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import StacksCore.Tactic.StacksAttribute

/-!
# Iterated base change along a composable pair

Let `f : X ⟶ S` be a morphism of schemes and let `S₂ ⟶ S₁ ⟶ S` be a composable pair over `S`
whose composite is identified, as an `S`-scheme, with a third morphism `d : T ⟶ S`. Base
changing `f` along `S₁ ⟶ S` and then along `S₂ ⟶ S₁` gives the same scheme as base changing it
along `d` in one step, compatibly with both projections.

Also collected here is the comparison morphism of base changes induced by a morphism of the
source, and the fact that it is a closed immersion when that morphism is.

## Main definitions

* `Stacks.IteratedBaseChange.iso`: the identification
  `(X ×_S S₁) ×_{S₁} S₂ ≅ X ×_S T`.
* `Stacks.IteratedBaseChange.sourceMap`: for `i : Y ⟶ X` the induced morphism
  `Y ×_S T ⟶ X ×_S T`.

## Main results

* `Stacks.IteratedBaseChange.iso_hom_fst` and `Stacks.IteratedBaseChange.iso_hom_snd`: the
  identification is compatible with both projections.
* `Stacks.IteratedBaseChange.isClosedImmersion_sourceMap`: the comparison morphism of base
  changes is a closed immersion when the morphism of sources is.
* `Stacks.IteratedBaseChange.ker_ι_le_ker_of_range_le`: a morphism whose image lies in an open
  `V` factors through `V`, so the ideal sheaf of `V` is contained in its kernel.

## Implementation notes

The identification of the two fibre products is the composite of
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`, which rewrites the iterated pullback as the
pullback along the composite `S₂ ⟶ S`, with the pullback functoriality map along the given
isomorphism of `S`-schemes. The isomorphism is supplied as an isomorphism in
`CategoryTheory.Over S` rather than a bare isomorphism plus a commuting triangle, because that
is the shape tag 080I states; `CategoryTheory.Over.forget` turns it into an isomorphism of
schemes and `CategoryTheory.Over.Hom.w` into the triangle.

## References

* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.IteratedBaseChange

variable {X S S₁ S₂ T : Scheme.{u}}

/-- Base changing `f : X ⟶ S` along `b : S₁ ⟶ S` and then along `c : S₂ ⟶ S₁` is base changing
it along any `d : T ⟶ S` identified with `c ≫ b` as an `S`-scheme. -/
public def iso (f : X ⟶ S) (b : S₁ ⟶ S) (c : S₂ ⟶ S₁) (d : T ⟶ S)
    (e : Over.mk (c ≫ b) ≅ Over.mk d) :
    Limits.pullback (pullback.snd f b) c ≅ Limits.pullback f d :=
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  pullbackLeftPullbackSndIso f b c ≪≫
    asIso (pullback.map f (c ≫ b) f d (𝟙 X) e.hom.left (𝟙 S) (by simp)
      (by simpa using e.hom.w.symm))

/-- The identification of the two fibre products is compatible with the projections to `X`. -/
public lemma iso_hom_fst (f : X ⟶ S) (b : S₁ ⟶ S) (c : S₂ ⟶ S₁) (d : T ⟶ S)
    (e : Over.mk (c ≫ b) ≅ Over.mk d) :
    (iso f b c d e).hom ≫ pullback.fst f d =
      pullback.fst (pullback.snd f b) c ≫ pullback.fst f b := by
  rw [iso, Iso.trans_hom, asIso_hom, Category.assoc, pullback.map, pullback.lift_fst,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

/-- The identification of the two fibre products is compatible with the projections to the base
change, up to the given isomorphism of `S`-schemes. -/
public lemma iso_hom_snd (f : X ⟶ S) (b : S₁ ⟶ S) (c : S₂ ⟶ S₁) (d : T ⟶ S)
    (e : Over.mk (c ≫ b) ≅ Over.mk d) :
    (iso f b c d e).hom ≫ pullback.snd f d =
      pullback.snd (pullback.snd f b) c ≫ e.hom.left := by
  rw [iso, Iso.trans_hom, asIso_hom, Category.assoc, pullback.map, pullback.lift_snd,
    ← Category.assoc, pullbackLeftPullbackSndIso_hom_snd]

variable {Y : Scheme.{u}}

/-- The comparison morphism of base changes induced by a morphism `i : Y ⟶ X` of sources. -/
public def sourceMap (i : Y ⟶ X) (f : X ⟶ S) (b : T ⟶ S) :
    Limits.pullback (i ≫ f) b ⟶ Limits.pullback f b :=
  pullback.lift (pullback.fst (i ≫ f) b ≫ i) (pullback.snd (i ≫ f) b)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The comparison morphism `sourceMap i f b` followed by the first projection to `X` is the first
projection to `Y` followed by `i`. -/
@[simp]
public lemma sourceMap_fst (i : Y ⟶ X) (f : X ⟶ S) (b : T ⟶ S) :
    sourceMap i f b ≫ pullback.fst f b = pullback.fst (i ≫ f) b ≫ i :=
  pullback.lift_fst _ _ _

/-- The comparison morphism `sourceMap i f b` commutes with the second projections to `T`. -/
@[simp]
public lemma sourceMap_snd (i : Y ⟶ X) (f : X ⟶ S) (b : T ⟶ S) :
    sourceMap i f b ≫ pullback.snd f b = pullback.snd (i ≫ f) b :=
  pullback.lift_snd _ _ _

/-- The comparison morphism of base changes along a closed immersion is a closed immersion. -/
public instance isClosedImmersion_sourceMap (i : Y ⟶ X) (f : X ⟶ S) (b : T ⟶ S)
    [IsClosedImmersion i] : IsClosedImmersion (sourceMap i f b) := by
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  simpa only [pullback.map, Category.comp_id, sourceMap] using
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) (f := i ≫ f) (g := b) (f' := f)
      (g' := b) (i₁ := i) (i₂ := 𝟙 T) inferInstance inferInstance rfl (Category.id_comp b).symm

/-- A morphism whose set-theoretic image lies in an open `V` factors through `V`, hence the
ideal sheaf cut out by `V` is contained in its kernel. -/
public lemma ker_ι_le_ker_of_range_le (V : X.Opens) (f : Y ⟶ X)
    (hf : Set.range f.base ⊆ V) : V.ι.ker ≤ f.ker := by
  have hl : IsOpenImmersion.lift V.ι f (by simpa using hf) ≫ V.ι = f :=
    IsOpenImmersion.lift_fac V.ι f _
  rw [← hl]
  exact Scheme.Hom.le_ker_comp _ _

end Stacks.IteratedBaseChange

end
