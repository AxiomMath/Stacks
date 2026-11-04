module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-!
# The two factorizations of the single functor through the bounded-below homotopy category

`DerivedCategory.Plus.singleFunctorIsoCompQh` and
`CategoryTheory.Functor.singleFunctorPlusIsoCompQh` both factor the single functor
`A ⥤ DerivedCategory.Plus A` through the bounded-below homotopy category. This file shows that
they agree.

## Main results

* `DerivedCategory.Plus.singleFunctorIsoCompQh_hom_app_eq` and
  `DerivedCategory.Plus.singleFunctorIsoCompQh_inv_app_eq`:
  `DerivedCategory.Plus.singleFunctorIsoCompQh` *is*
  `CategoryTheory.Functor.singleFunctorPlusIsoCompQh`, the two chains of comparisons they cancel
  the embedding along differing only by factors with identity components.

## Implementation notes

The identification of the image of `DerivedCategory.Plus.singleFunctorIsoCompQh` under the
embedding with the unbounded comparison is proved inline, as a local `have`, from the definition
of `DerivedCategory.Plus.singleFunctorIsoCompQh` through
`CategoryTheory.Functor.fullyFaithfulCancelRight_hom_app`.

## References

* [Stacks Project, Tag 013K](https://stacks.math.columbia.edu/tag/013K)
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

universe v w u

namespace DerivedCategory.Plus

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **The two factorizations of the single functor into the bounded-below derived category
through the bounded-below homotopy category agree.** Both
`DerivedCategory.Plus.singleFunctorIsoCompQh` and
`CategoryTheory.Functor.singleFunctorPlusIsoCompQh` are obtained by cancelling the fully
faithful embedding `DerivedCategory.Plus.ι` on the right of the unbounded comparison
`DerivedCategory.singleFunctorIsoCompQh`; the first inserts three further comparisons, all of
which have identity components. So the two are preimages of the same morphism under a faithful
functor. -/
lemma singleFunctorIsoCompQh_hom_app_eq (Z : A) :
    (singleFunctorIsoCompQh A 0).hom.app Z =
      (CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app Z := by
  have hι : DerivedCategory.Plus.ι.map ((singleFunctorIsoCompQh A 0).hom.app Z) =
      (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z := by
    have hstep : DerivedCategory.Plus.ι.map ((singleFunctorIsoCompQh A 0).hom.app Z) =
        𝟙 _ ≫ (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.Plus.singleFunctorCompιIso A 0).inv.app Z) ≫ 𝟙 _ := by
      rw [singleFunctorIsoCompQh, Functor.fullyFaithfulCancelRight_hom_app,
        CategoryTheory.Functor.map_preimage]
      rfl
    have hid : (HomotopyCategory.Plus.singleFunctorCompιIso A 0).inv.app Z = 𝟙 _ := rfl
    have hz : DerivedCategory.Qh.map
        ((HomotopyCategory.Plus.singleFunctorCompιIso A 0).inv.app Z) ≫ 𝟙 _ = 𝟙 _ :=
      (Category.comp_id _).trans ((congrArg DerivedCategory.Qh.map hid).trans
        (CategoryTheory.Functor.map_id DerivedCategory.Qh _))
    refine hstep.trans ((Category.id_comp _).trans ?_)
    refine Eq.trans (congrArg
      (fun z => (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z ≫ z) hz) ?_
    exact Category.comp_id _
  have h : DerivedCategory.Plus.ι.map
        ((CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app Z) =
      (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z :=
    DerivedCategory.Plus.ι.map_preimage _
  exact DerivedCategory.Plus.ι.map_injective (hι.trans h.symm)

/-- `DerivedCategory.Plus.singleFunctorIsoCompQh_hom_app_eq` for the inverse, by uniqueness of
inverses. -/
lemma singleFunctorIsoCompQh_inv_app_eq (Z : A) :
    (singleFunctorIsoCompQh A 0).inv.app Z =
      (CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app Z :=
  congrArg Iso.inv (Iso.ext (singleFunctorIsoCompQh_hom_app_eq Z) :
    (singleFunctorIsoCompQh A 0).app Z =
      (CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := A) 0).app Z)

end DerivedCategory.Plus

end
