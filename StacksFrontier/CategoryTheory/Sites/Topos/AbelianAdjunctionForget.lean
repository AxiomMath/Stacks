module

public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact

/-!
# The adjunction of abelian sheaves transposes as the geometric one

For a morphism of topoi `f`, the inverse image and direct image of abelian sheaves are the
geometric ones carried through the identification of abelian sheaves with commutative group
objects, and `Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward` is the
adjunction between them. Forgetting the abelian-group operations recovers the geometric functors
(`Stacks.Topos.AbelianInverseImage.abelianInverseImage_forgetIso` and
`Stacks.Topos.AbelianPushforward.abelianPushforward_forgetIso`, both the identity), but nothing
said what forgetting does to the *transposition*. This file says it: the abelian hom-set
bijection is the geometric one on underlying sheaves of sets, in both directions.

This is the abelian counterpart of `CategoryTheory.MorphismOfTopoi.ringAdjunction_homEquiv_forget`
and its symmetric partner for sheaves of commutative rings.

The point of the statement is that an abelian transposition can then be computed on sheaves of
sets, where the geometric adjunction's own identities are available — for instance the cone law
of Stacks 0D70,
`CategoryTheory.SimplicialSiteSituation.Augmentation.homEquiv_componentPushforwardTransition_iff`,
which is stated for sheaves of sets and has no abelian form.

## Main results

* `Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_unit_forget`: the unit of
  the abelian adjunction forgets to the unit of the geometric one.
* `Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_homEquiv_forget` and
  `.abelianInverseImageAdjPushforward_homEquiv_symm_forget`: the abelian hom-set bijection
  forgets to the geometric one, in both directions.

## Implementation notes

The three units in play — the two halves of the identification of abelian sheaves with
commutative group objects, and the unit `CategoryTheory.Adjunction.mapCommGrp` builds from the
geometric one — are all the identity on underlying sheaves of sets, and the composite unit is
therefore the geometric unit followed by the direct image of an identity. That last factor is
the only thing standing between the two sides and definitional equality, so the proof is one
`rfl` against that spelling followed by `CategoryTheory.Functor.map_id`.

The equations are taken by `Eq.trans` against explicit terms rather than by `rw`. The source and
target of the morphisms involved are spelled differently on the two sides — `(𝟭 _).obj G` against
`G`, and the composite of three functors against the abelian direct image — and a rewrite
elaborates its motive at a reduced transparency and fails on those.

## References

* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 00YR](https://stacks.math.columbia.edu/tag/00YR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' w w'

namespace Stacks.Topos.AbelianPushforward

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- **The unit of the abelian adjunction is the geometric unit.** Forgetting the abelian-group
operations takes the unit of `abelianInverseImageAdjPushforward` to the unit of the geometric
adjunction `f⁻¹ ⊣ f_*`. -/
theorem abelianInverseImageAdjPushforward_unit_forget (G : Sheaf K AddCommGrpCat.{w'}) :
    (sheafCompose K (forget AddCommGrpCat.{w'})).map
        ((abelianInverseImageAdjPushforward J f).unit.app G) =
      f.adj.unit.app ((sheafCompose K (forget AddCommGrpCat.{w'})).obj G) := by
  have key : (sheafCompose K (forget AddCommGrpCat.{w'})).map
        ((abelianInverseImageAdjPushforward J f).unit.app G) =
      f.adj.unit.app ((sheafCompose K (forget AddCommGrpCat.{w'})).obj G) ≫
        f.pushforward.map (𝟙 (f.inverseImage.obj
          ((sheafCompose K (forget AddCommGrpCat.{w'})).obj G))) := rfl
  refine key.trans (Eq.trans (congrArg (fun t =>
    f.adj.unit.app ((sheafCompose K (forget AddCommGrpCat.{w'})).obj G) ≫ t)
      (f.pushforward.map_id _)) ?_)
  exact Category.comp_id _

/-- **The abelian transposition is the geometric one.** Forgetting the abelian-group operations
of the transpose of a morphism out of the abelian inverse image gives the transpose of the
forgotten morphism along the geometric adjunction. -/
theorem abelianInverseImageAdjPushforward_homEquiv_forget (G : Sheaf K AddCommGrpCat.{w'})
    (F : Sheaf J AddCommGrpCat.{w}) (α : (Sites.abelianInverseImage f).obj G ⟶ F) :
    (sheafCompose K (forget AddCommGrpCat.{w'})).map
        ((abelianInverseImageAdjPushforward J f).homEquiv G F α) =
      f.adj.homEquiv _ _ ((sheafCompose J (forget AddCommGrpCat.{w})).map α) := by
  refine Eq.trans ?_
    (f.adj.homEquiv_unit _ _ ((sheafCompose J (forget AddCommGrpCat.{w})).map α)).symm
  refine Eq.trans (congrArg (sheafCompose K (forget AddCommGrpCat.{w'})).map
    ((abelianInverseImageAdjPushforward J f).homEquiv_unit G F α)) ?_
  refine Eq.trans ((sheafCompose K (forget AddCommGrpCat.{w'})).map_comp _ _) ?_
  exact congrArg (fun t => t ≫ f.pushforward.map
      ((sheafCompose J (forget AddCommGrpCat.{w})).map α))
    (abelianInverseImageAdjPushforward_unit_forget J f G)

/-- **The abelian transposition is the geometric one, the other way.** Forgetting the
abelian-group operations of the transpose of a morphism into the abelian direct image gives the
transpose of the forgotten morphism along the geometric adjunction. -/
theorem abelianInverseImageAdjPushforward_homEquiv_symm_forget (G : Sheaf K AddCommGrpCat.{w'})
    (F : Sheaf J AddCommGrpCat.{w}) (β : G ⟶ (abelianPushforward J f).obj F) :
    (sheafCompose J (forget AddCommGrpCat.{w})).map
        (((abelianInverseImageAdjPushforward J f).homEquiv G F).symm β) =
      (f.adj.homEquiv _ _).symm ((sheafCompose K (forget AddCommGrpCat.{w'})).map β) := by
  refine (Equiv.eq_symm_apply _).2 ?_
  refine Eq.trans (abelianInverseImageAdjPushforward_homEquiv_forget J f G F
    (((abelianInverseImageAdjPushforward J f).homEquiv G F).symm β)).symm ?_
  exact congrArg (sheafCompose K (forget AddCommGrpCat.{w'})).map
    (((abelianInverseImageAdjPushforward J f).homEquiv G F).apply_symm_apply β)

end Stacks.Topos.AbelianPushforward

end
