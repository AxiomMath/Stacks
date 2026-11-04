module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.ComponentBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# The pieces of a disjoint union decomposition of a morphism

Let `f : X ⟶ Y` be a morphism of schemes, let `X = ∐_{i ∈ I} X_i` and `Y = ∐_{j ∈ J} Y_j` be
decompositions into open and closed subschemes and let `a : I → J` satisfy `f(X_i) ⊆ Y_{a(i)}`.
Then `f` restricts to a morphism `f_i : X_i ⟶ Y_{a(i)}` for every `i`, and for a test scheme
`g : T ⟶ Y_{a(i)}` the base change `X_i ×_{Y_{a(i)}} T` is an open subscheme of `X ×_Y T`,
namely the preimage of `X_i` under the projection to `X`.

This file collects those identifications, together with the fact that a decomposition into open
and closed subschemes pulls back to one along any morphism. They are the geometric input of
Stacks 0FDZ, which decomposes the group of bivariant classes for `f` as the product of the groups
of bivariant classes for the `f_i`.

## Main definitions

* `Stacks.Chow.pieceMap` — the restriction `f_i : X_i ⟶ Y_{a(i)}` of `f` to a piece.
* `Stacks.Chow.pieceComparison` — the open immersion `X_i ×_{Y_{a(i)}} T ⟶ X ×_Y T`.

## Main results

* `Stacks.Chow.IsClopenDecomposition.preimage` — a decomposition into open and closed subschemes
  pulls back to one along any morphism.
* `Stacks.Chow.opensRange_pieceComparison` — the image of the comparison is the preimage of the
  piece `X_i` under the projection `X ×_Y T ⟶ X`.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace Stacks.Chow

/-! ### Pulling back a decomposition into open and closed subschemes -/

/-- A decomposition of a scheme into open and closed subschemes pulls back to one along any
morphism: preimages of disjoint opens are disjoint, and preimages of a cover cover. -/
theorem IsClopenDecomposition.preimage {X W : Scheme.{u}} {I : Type v} {U : I → X.Opens}
    (h : IsClopenDecomposition U) (φ : W ⟶ X) :
    IsClopenDecomposition fun i ↦ φ ⁻¹ᵁ U i where
  disjoint i j hij := by
    rw [disjoint_iff]
    refine Opens.ext ?_
    have hij' : ((U i ⊓ U j : X.Opens) : Set X) = ∅ := by
      rw [disjoint_iff.mp (h.disjoint i j hij)]; rfl
    calc ((φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j : W.Opens) : Set W)
        = φ.base ⁻¹' ((U i ⊓ U j : X.Opens) : Set X) := by
          simp only [Opens.coe_inf, Scheme.Hom.coe_preimage, Set.preimage_inter]
      _ = ((⊥ : W.Opens) : Set W) := by rw [hij', Set.preimage_empty]; rfl
  iSup_eq_top := by
    refine Opens.ext ?_
    have hX : ⋃ i, (U i : Set X) = Set.univ := by
      rw [← Opens.coe_iSup, h.iSup_eq_top]; rfl
    rw [Opens.coe_iSup, Opens.coe_top]
    simp only [Scheme.Hom.coe_preimage, ← Set.preimage_iUnion]
    rw [hX, Set.preimage_univ]

/-! ### The restriction of a morphism to a piece -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type v} (UX : I → X.Opens) (UY : J → Y.Opens)
  (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i))

/-- The restriction `f_i : X_i ⟶ Y_{a(i)}` of `f` to the piece `X_i` of its source, which lands
in the piece `Y_{a(i)}` of its target by hypothesis. -/
def pieceMap (i : I) : (UX i : Scheme.{u}) ⟶ (UY (a i) : Scheme.{u}) :=
  f.resLE (UY (a i)) (UX i) (ha i)

/-- The restriction of `f` to a piece is the restriction of `f`: it agrees with `f` after
composing with the two piece inclusions. -/
@[simp, reassoc]
theorem pieceMap_comp_ι (i : I) :
    pieceMap f UX UY a ha i ≫ (UY (a i)).ι = (UX i).ι ≫ f :=
  Scheme.Hom.resLE_comp_ι f (ha i)

/-- The restriction of a morphism locally of finite type to a piece is locally of finite type. -/
instance locallyOfFiniteType_pieceMap [LocallyOfFiniteType f] (i : I) :
    LocallyOfFiniteType (pieceMap f UX UY a ha i) :=
  inferInstanceAs (LocallyOfFiniteType (f.resLE (UY (a i)) (UX i) (ha i)))

/-! ### The base change of a piece -/

variable {T : Scheme.{u}} (i : I)

/-- The comparison `X_i ×_{Y_{a(i)}} T ⟶ X ×_Y T` attached to a test morphism
`g : T ⟶ Y_{a(i)}`, the second pullback being taken along `g` followed by the inclusion of the
piece. It is an open immersion, by
`Stacks.Chow.isOpenImmersion_opensPullbackComparison`. -/
abbrev pieceComparison (g : T ⟶ (UY (a i) : Scheme.{u})) :
    pullback (pieceMap f UX UY a ha i) g ⟶ pullback f (g ≫ (UY (a i)).ι) :=
  opensPullbackComparison f (UX i) (UY (a i)) (pieceMap f UX UY a ha i)
    (pieceMap_comp_ι f UX UY a ha i) g

variable (g : T ⟶ (UY (a i) : Scheme.{u}))

/-- The comparison commutes with the structure morphisms over the base scheme: it carries the
structure morphism of `X ×_Y T` to the structure morphism of `X_i ×_{Y_{a(i)}} T`, the latter
being taken through the inclusion of the piece. -/
theorem pieceComparison_comp_structureMorphism {S : Scheme.{u}} (sX : X ⟶ S) :
    pieceComparison f UX UY a ha i g ≫ (pullback.fst f (g ≫ (UY (a i)).ι) ≫ sX) =
      pullback.fst (pieceMap f UX UY a ha i) g ≫ ((UX i).ι ≫ sX) := by
  rw [← Category.assoc, opensPullbackComparison_fst, Category.assoc]

/-- The image of the comparison is the preimage of the piece `X_i` under the projection
`X ×_Y T ⟶ X`: the comparison is a base change of the inclusion of `X_i`, by
`Stacks.Chow.isPullback_opensPullbackComparison`. -/
theorem opensRange_pieceComparison :
    (pieceComparison f UX UY a ha i g).opensRange =
      pullback.fst f (g ≫ (UY (a i)).ι) ⁻¹ᵁ UX i := by
  have hsq := isPullback_opensPullbackComparison f (UX i) (UY (a i))
    (pieceMap f UX UY a ha i) (pieceMap_comp_ι f UX UY a ha i) g
  have he := hsq.isoPullback_hom_snd
  have hsurj : Function.Surjective hsq.isoPullback.hom.base := fun y ↦
    ⟨hsq.isoPullback.inv.base y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
  refine Opens.ext ?_
  show Set.range (opensPullbackComparison f (UX i) (UY (a i)) (pieceMap f UX UY a ha i)
    (pieceMap_comp_ι f UX UY a ha i) g).base = _
  rw [← he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ,
    IsOpenImmersion.range_pullbackSnd (UX i).ι (pullback.fst f (g ≫ (UY (a i)).ι))]
  simp

end Stacks.Chow

end
