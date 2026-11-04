module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RefinementSiteData

/-!
# Properties of a relation on an affine object

[Stacks, Tag 04S4] asks of the ambient relation `j = (t, s) : R ⟶ U ×_S U` that it be separated,
locally quasi-finite and locally of finite type, on top of `U` being affine.  The last two are
inherited from the source map, since `j` followed by the second projection *is* the source map;
the first holds for free once `U` is affine, because then `R` is a separated scheme — it is a
subobject of `U ×_S U`, which is separated over `U`, which is separated absolutely.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.isPullback_prod_left`: the product in the slice over `S`, read on
  underlying schemes, is the fibre product over `S`.
* `AlgebraicGeometry.isSeparated_prod_left_of_isAffine`: the product of two affine objects of the
  slice over `S` is a separated scheme.
* `AlgebraicGeometry.PreRelation.isSeparated_left_of_isAffine` and
  `AlgebraicGeometry.PreRelation.isSeparated_of_isAffine`: for a monic pre-relation on an affine
  object, the relation scheme is separated and the pre-relation is a separated morphism.
* `AlgebraicGeometry.PreRelation.locallyOfFiniteType_of_source` and
  `AlgebraicGeometry.PreRelation.locallyQuasiFinite_of_source`: the pre-relation inherits local
  finite type and local quasi-finiteness from its source map.

## Implementation notes

`isPullback_prod_left` is `CategoryTheory.Over.prodLeftIsoPullback` turned into a cartesian
square, which is the form in which stability of a morphism property under base change consumes
it.  Nothing here is specific to the big fppf site: the statements are about objects of
`Over S` and are used at the point where [Stacks, Tag 04S4] is applied to the restriction of a
groupoid to an affine étale neighbourhood.

## References

* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 01KO](https://stacks.math.columbia.edu/tag/01KO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The binary product in the slice category over `S`, read on underlying schemes, is the fibre
product over `S`. -/
theorem isPullback_prod_left (X Y : Over S) :
    IsPullback (prod.fst : (X ⨯ Y : Over S) ⟶ X).left
      (prod.snd : (X ⨯ Y : Over S) ⟶ Y).left X.hom Y.hom := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (Over.prodLeftIsoPullback X Y) ?_ ?_
  · rw [Over.w (prod.fst : (X ⨯ Y : Over S) ⟶ X), Over.w (prod.snd : (X ⨯ Y : Over S) ⟶ Y)]
  · exact Over.prodLeftIsoPullback_hom_fst X Y
  · exact Over.prodLeftIsoPullback_hom_snd X Y

/-- A scheme with a separated morphism to a separated scheme is separated. -/
private theorem isSeparated_of_isSeparated_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [Y.IsSeparated] : X.IsSeparated := by
  constructor
  rw [← terminal.comp_from f]
  infer_instance

/-- The product of two objects of the slice over `S` with affine underlying schemes is a
separated scheme: the second projection is a base change of a separated structure morphism, and
an affine scheme is separated. -/
theorem isSeparated_prod_left_of_isAffine (X Y : Over S) [IsAffine X.left] [IsAffine Y.left] :
    (X ⨯ Y : Over S).left.IsSeparated := by
  have : IsSeparated (prod.snd : (X ⨯ Y : Over S) ⟶ Y).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_prod_left X Y) inferInstance
  exact isSeparated_of_isSeparated_hom (prod.snd : (X ⨯ Y : Over S) ⟶ Y).left

namespace PreRelation

variable {R U : Over S}

/-- The relation scheme of a monic pre-relation on an affine object of the slice over `S` is a
separated scheme. -/
theorem isSeparated_left_of_isAffine (j : PreRelation R U) [IsAffine U.left] [Mono j] :
    R.left.IsSeparated := by
  have := isSeparated_prod_left_of_isAffine U U
  have : Mono j.left := mono_left_of_mono_over j
  exact isSeparated_of_isSeparated_hom j.left

/-- A monic pre-relation on an affine object of the slice over `S` is a separated morphism of
schemes: its source is a separated scheme. -/
theorem isSeparated_of_isAffine (j : PreRelation R U) [IsAffine U.left] [Mono j] :
    IsSeparated j.left := by
  have := isSeparated_left_of_isAffine j
  infer_instance

/-- A pre-relation followed by the second projection is its source map, on underlying schemes. -/
private theorem left_comp_snd_left (j : PreRelation R U) :
    j.left ≫ (prod.snd : (U ⨯ U : Over S) ⟶ U).left = j.source.left := by
  rw [← Over.comp_left]

/-- A pre-relation is locally of finite type when its source map is: the source map is the
pre-relation followed by the second projection. -/
theorem locallyOfFiniteType_of_source (j : PreRelation R U)
    [LocallyOfFiniteType j.source.left] : LocallyOfFiniteType j.left := by
  have : LocallyOfFiniteType (j.left ≫ (prod.snd : (U ⨯ U : Over S) ⟶ U).left) :=
    left_comp_snd_left j ▸ inferInstance
  exact locallyOfFiniteType_of_comp j.left (prod.snd : (U ⨯ U : Over S) ⟶ U).left

/-- A pre-relation is locally quasi-finite when its source map is. -/
theorem locallyQuasiFinite_of_source (j : PreRelation R U)
    [LocallyQuasiFinite j.source.left] : LocallyQuasiFinite j.left := by
  have : LocallyQuasiFinite (j.left ≫ (prod.snd : (U ⨯ U : Over S) ⟶ U).left) :=
    left_comp_snd_left j ▸ inferInstance
  exact LocallyQuasiFinite.of_comp j.left (prod.snd : (U ⨯ U : Over S) ⟶ U).left

end PreRelation

end AlgebraicGeometry

end
