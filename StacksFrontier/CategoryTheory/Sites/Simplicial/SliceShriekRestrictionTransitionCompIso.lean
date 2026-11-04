module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceAbelianLowerShriekCompIsoCanonical
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceFreeAbelianLowerShriekNaturality

/-!
# The shriek restriction transition of a simplex map, at the canonical simplicial spelling

Let `(C, J)` be a small site and `K` a simplicial object of `SR(C)`. A simplex map `φ : m ⟶ n`
gives the morphism `K_φ : K_n ⟶ K_m` of semi-representable objects, and
`CategoryTheory.SemiRepresentable.shriekRestrictionTransition` applies to it: it is the canonical
transformation `j_{n!}j_n^{-1} ⟶ j_{m!}j_m^{-1}` of Stacks 0D87. This module expresses that
transformation with its comparison of left adjoints spelled as
`CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso`, the composition
comparison the simplicial structure maps of the Čech resolution are phrased at.

## Main results

* `CategoryTheory.SemiRepresentable.hasWeakSheafifyComponentOver`: sheafification of abelian
  presheaves on `∐ i, C / L_i` exists, for any topology on it.
* `SimplicialSemiRepresentable.shriekRestrictionTransition_app_sliceAbelianLowerShriekCompIso`:
  the shriek restriction transition of a simplex map, with its comparison of left adjoints
  spelled as the simplicial composition comparison.

## Implementation notes

The component site of simplicial degree `p` has two spellings whose category instances are
definitionally but not syntactically equal: `(situation J K).component p`, carrying
`CategoryTheory.Cat.str`, and `ComponentOver (K.obj (op p))`, carrying the instance of a sigma
type of slice categories. `shriekRestrictionTransition` is stated at the second spelling, the
registered `HasWeakSheafify` instances for the component topology deliver the first, and instance
search at reducible transparency does not identify them. The instance is therefore supplied as the
term `hasWeakSheafifyComponentOver` applied to the component topology, whose type fixes the
`ComponentOver` spelling. Annotating `GrothendieckTopology.hasSheafify_addCommGrpCat` with
`(C := ComponentOver (K.obj (op p)))` does not work.

## References

* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SemiRepresentable

variable {C : Type u} [SmallCategory C]

/-- **Abelian presheaves on `∐ i, C / L_i` admit sheafification**, for any topology on it, the
category being small at the universe of the site. -/
theorem hasWeakSheafifyComponentOver {L : FormalCoproduct.{u} C}
    (T : GrothendieckTopology (ComponentOver L)) :
    HasWeakSheafify T AddCommGrpCat.{u} :=
  inferInstance

end CategoryTheory.SemiRepresentable

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **The shriek restriction transition of a simplex map, with its comparison of left adjoints
spelled as the simplicial composition comparison.** For `φ : m ⟶ n` the transition
`j_{n!}j_n^{-1} ⟶ j_{m!}j_m^{-1}` of the morphism `K_φ : K_n ⟶ K_m` at a sheaf `Y` is the inverse
of `CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso` at `j_n^{-1}Y`,
followed by the extension by zero along `j_m` of the `r_φ`-part: the reindexing of `j_n^{-1}Y`
into `r_φ^{-1}j_m^{-1}Y`, then the counit of `r_{φ!} ⊣ r_φ^{-1}`. -/
theorem shriekRestrictionTransition_app_sliceAbelianLowerShriekCompIso {m n : SimplexCategory}
    (φ : m ⟶ n) (Y : Sheaf J AddCommGrpCat.{u}) :
    haveI := hasWeakSheafifyComponentOver (L := K.obj (op n))
      ((situation J K).componentTopology n)
    haveI := hasWeakSheafifyComponentOver (L := K.obj (op m))
      ((situation J K).componentTopology m)
    haveI : (componentOverForget (K.obj (op n))).IsContinuous
        ((situation J K).componentTopology n) J := sliceForget_isContinuous J K n
    haveI : (componentOverForget (K.obj (op m))).IsContinuous
        ((situation J K).componentTopology m) J := sliceForget_isContinuous J K m
    (shriekRestrictionTransition J (K.map φ.op) ((situation J K).componentTopology n)
          ((situation J K).componentTopology m) AddCommGrpCat.{u}).app Y =
      (sliceAbelianLowerShriekCompIso J K φ).inv.app
          (((sliceForget K (op n)).sheafPushforwardContinuous AddCommGrpCat.{u}
            ((situation J K).componentTopology n) J).obj Y) ≫
        (sliceAbelianLowerShriek J K m).map
          ((transitionAbelianLowerShriek J K φ).map
              ((sliceAbelianRestrictionCompIso J K φ).inv.app Y) ≫
            (transitionAbelianLowerShriekAdjunction J K φ).counit.app
              (((sliceForget K (op m)).sheafPushforwardContinuous AddCommGrpCat.{u}
                ((situation J K).componentTopology m) J).obj Y)) := by
  have := hasWeakSheafifyComponentOver (L := K.obj (op n))
    ((situation J K).componentTopology n)
  have := hasWeakSheafifyComponentOver (L := K.obj (op m))
    ((situation J K).componentTopology m)
  have : (componentOverForget (K.obj (op n))).IsContinuous
      ((situation J K).componentTopology n) J := sliceForget_isContinuous J K n
  have : (componentOverForget (K.obj (op m))).IsContinuous
      ((situation J K).componentTopology m) J := sliceForget_isContinuous J K m
  refine Eq.trans (shriekRestrictionTransition_app_lowerShriekComp J (K.map φ.op)
    ((situation J K).componentTopology n) ((situation J K).componentTopology m)
    AddCommGrpCat.{u} Y) ?_
  exact eq_whisker (NatTrans.congr_app
    (congrArg Iso.inv (sliceAbelianLowerShriekCompIso_eq_lowerShriekComp J K φ)).symm _) _

end CategoryTheory.SimplicialSemiRepresentable

end
