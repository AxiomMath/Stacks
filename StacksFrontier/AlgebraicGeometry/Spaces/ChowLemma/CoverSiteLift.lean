module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverMorphism

/-!
# Promoting a scheme-level lift into the cover of Stacks 089J to a morphism of the site

The valuative-criterion step of Stacks 089J produces its lift as a morphism of *schemes* into
the scheme-theoretic image `Z`: the valuative criterion of properness is applied to one of the
projections `gᵢ : Z ⟶ Y`, which is a morphism of schemes. The lift of the valuative square the
refined criterion asks for is instead a morphism of *presheaves on the site*, out of the
representable presheaf of an object of the site and into the representable presheaf of
`X' = ⋃ᵢ gᵢ⁻¹(W)`.

This file performs that passage. A morphism of schemes between underlying schemes of objects
of the site which commutes with the structure morphisms is the image of a morphism of the site
by `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`, and a morphism of the site whose range
lies in an open factors through the corresponding open subobject by
`AlgebraicGeometry.Space.openSubObjLift`. The range condition is read off the factorisation of
`z ≫ gᵢ` through the chart, exactly as
`AlgebraicGeometry.Space.range_subset_preimage_chartOpensRange` reads it.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_hom_openSubObj_of_range_subset`: a morphism of schemes over
  the base whose range lies in an open of the target is the image of a morphism of the site
  into the corresponding open subobject.
* `AlgebraicGeometry.Space.exists_hom_chowCoverObj_of_comp_chowProj_eq`: **the scheme-level lift
  into the scheme-theoretic image is a morphism of the site into `X'`**, as soon as its
  composite with one projection `gᵢ` factors through the chart.

## What is and is not proved

Stacks 089J is **not** proved here and no declaration in this file carries a Stacks attribute;
both statements are transports between the site and schemes, resting on
`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`, which carries no tag.

The valuative lift itself is **not** produced. What is missing between this file and the
valuative lifting condition of
`AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion` is the construction of the
scheme morphism `z` into the scheme-theoretic image and of the index `i` with its
factorisation: `z` comes from the valuative criterion of properness for `gᵢ`, which is
`AlgebraicGeometry.exists_valuativeLift_of_isProper` together with
`AlgebraicGeometry.Space.isProper_chowProj`, and the index `i` from matching the enlarged lift
with one of the `d` projections of the complement of the diagonals, which is
`AlgebraicGeometry.Space.exists_eq_of_hasUniversallyBoundedFibers`. Neither step is taken here,
and nor is the `special_comm` field of the lift, which needs the uniqueness half of Stacks 03IX
for the separated structure morphism of the algebraic space —
`AlgebraicGeometry.Space.valuativeCriterion_uniqueness_of_isSeparated`.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of schemes over the base whose range lies in an open of the target comes from
a morphism of the site into the corresponding open subobject.**

`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq` turns the morphism of schemes into a
morphism of the site, and `AlgebraicGeometry.Space.openSubObjLift` factors that through the
open subobject. -/
theorem exists_hom_openSubObj_of_range_subset (T A : BigFppfOver B S hS)
    (U : T.left.obj.Opens)
    (z : (BigFppfOver.toScheme B S hS).obj A ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hz : z ≫ B.inclusion.map T.hom = B.inclusion.map A.hom)
    (hrange : Set.range ⇑z ⊆ (U : Set T.left.obj)) :
    ∃ w : A ⟶ BigFppfOver.openSubObj B S hS T U,
      (BigFppfOver.toScheme B S hS).map w ≫ U.ι = z := by
  obtain ⟨a, ha⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS z hz
  refine ⟨openSubObjLift B S hS T U a (by rw [ha]; exact hrange), ?_⟩
  rw [openSubObjLift_toScheme_comp, ha]

variable (X : AlgebraicSpaces B S hS) (Wch : BigFppfOver B S hS)
    (c : yoneda.obj Wch ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    (Yo : BigFppfOver B S hS) (j : Wch ⟶ Yo) (n : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B S hS X
      (SpacesEtale.diagonalComplement B S hS X
        (SpacesEtale.chartObj B S hS X Wch c hc) (n + 1) hsep)).obj)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))

/-- **A scheme-level lift into the scheme-theoretic image of Stacks 089J whose composite with
one projection factors through the chart is a morphism of the site into `X'`.**

The factorisation of `z ≫ gᵢ` through the open immersion `j : W ⟶ Y` puts the range of `z`
inside `gᵢ⁻¹(W)`, hence inside the union `⋃ₖ gₖ⁻¹(W)` which is `X'`; the morphism of schemes is
then promoted by `AlgebraicGeometry.Space.exists_hom_openSubObj_of_range_subset`.

This is the passage the valuative-criterion step of Stacks 089J needs: the lift it obtains from
the valuative criterion of properness for `gᵢ` is a morphism of schemes, while the refined
valuative criterion asks for a morphism into the presheaf represented by `X'`. -/
theorem exists_hom_chowCoverObj_of_comp_chowProj_eq (A : BigFppfOver B S hS)
    (z : (BigFppfOver.toScheme B S hS).obj A ⟶
      (chowImageObj B S hS X Wch c hc hsep Yo j n V e).left.obj)
    (hz : z ≫ B.inclusion.map (chowImageObj B S hS X Wch c hc hsep Yo j n V e).hom =
      B.inclusion.map A.hom)
    (i : Fin (n + 1))
    (b : (BigFppfOver.toScheme B S hS).obj A ⟶ (BigFppfOver.toScheme B S hS).obj Wch)
    (hb : z ≫ chowProj B S hS X Wch c hc hsep Yo j n V e i =
      b ≫ (BigFppfOver.toScheme B S hS).map j) :
    ∃ w : A ⟶ chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj,
      (BigFppfOver.toScheme B S hS).map w ≫
          (unionPreimageOpens B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
            (chowProj B S hS X Wch c hc hsep Yo j n V e)
            (chartOpensRange B S hS j hj)).ι = z := by
  have hpre : Set.range ⇑z ⊆
      ((chowProj B S hS X Wch c hc hsep Yo j n V e i ⁻¹ᵁ chartOpensRange B S hS j hj :
        (chowImageObj B S hS X Wch c hc hsep Yo j n V e).left.obj.Opens) :
          Set (chowImageObj B S hS X Wch c hc hsep Yo j n V e).left.obj) :=
    range_subset_preimage_chartOpensRange B S hS j hj _ z b hb
  refine exists_hom_openSubObj_of_range_subset B S hS
    (chowImageObj B S hS X Wch c hc hsep Yo j n V e) A
    (unionPreimageOpens B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
      (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj)) z hz ?_
  refine hpre.trans ?_
  intro y hy
  exact (mem_unionPreimageOpens B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
    (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj) y).2 ⟨i, hy⟩

end AlgebraicGeometry.Space

end
