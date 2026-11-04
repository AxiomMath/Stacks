module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceIsoClass
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# The projections of a represented 2-fibre product (Stacks 04SD)

`AlgebraicGeometry.Stack.fibreProductIsoRepresenting` identifies a presheaf `T` representing the
2-fibre product `𝒳 ×_𝒵 𝒴` of represented categories fibred in groupoids with the fibre product
`F ×_H G` of the representing presheaves. This module records that the identification carries the
two projections of the fibre product of presheaves to the morphisms of representing presheaves
induced by the two projections of the canonical 2-fibre product square.

## Main results

* `AlgebraicGeometry.Stack.twoFibreProductIsoClassSectionEquiv_val_snd`: the second-component
  companion of `AlgebraicGeometry.Stack.twoFibreProductIsoClassSectionEquiv_val_fst`.
* `AlgebraicGeometry.Stack.fibreProductIsoRepresenting_hom_comp_representingMap_fst` and
  `AlgebraicGeometry.Stack.fibreProductIsoRepresenting_hom_comp_representingMap_snd`: the
  compatibility with the two projections.
* `AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProduct`: hence the square of
  morphisms of representing presheaves induced by the canonical 2-fibre product square is
  cartesian.

## Implementation notes

Without this compatibility the identification of Stacks 04SD is not usable for comparing a
1-morphism into a 2-fibre product with a morphism into a fibre product of algebraic spaces: the
isomorphism alone says that the two presheaves agree, not that the comparison respects the
projections, and it is the projections that a diagram of Stacks 0CIF or Stacks 06FM is phrased
through.

Each statement is read off sections: every section of `T` over an object names an isomorphism
class in the fibre of the 2-fibre product over it, the morphism induced by a projection sends
that class to its image class (`AlgebraicGeometry.Stack.morphismSpaceEquiv_app_isoClassSection`),
and the pair attached to the class has that image class as its corresponding component. The
statements are in the `.hom` direction because
`AlgebraicGeometry.Stack.fibreProductIsoRepresenting_hom_app` holds by `rfl` while the inverse
direction does not reduce — `AlgebraicGeometry.Stack.twoFibreProductIsoClassSectionEquiv` is
built from `CategoryTheory.Functor.twoFibreProductIsoClassEquiv`, which is noncomputable.

The apex of the canonical square `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` and
the structure functor `AlgebraicGeometry.Stack.twoFibreProductStructureFunctor` the
identification is stated over are definitionally equal, but only at default transparency: a
`simp only` whose rewrite crosses the two spellings fails with a type-correctness complaint
rather than with a missing rewrite, which is why the proofs below use `rw` on named equations and
close with `exact` rather than with `simp`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver
    𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
  (eH : StacksRepresentableCFG.EquivalenceOver
    𝒵.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
  (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵)

/-- **The second component of the pair attached to a class in the fibre of a 2-fibre product.**
It is the section of `G` named by the image of that class under the second projection: both sides
are the section named by the second component of a representative.

This is the companion of `AlgebraicGeometry.Stack.twoFibreProductIsoClassSectionEquiv_val_fst`. -/
theorem twoFibreProductIsoClassSectionEquiv_val_snd
    [(twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFibered]
    (U : BigFppfOver B S hS)
    (c : _root_.Quotient (isIsomorphicSetoid
      ((twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).Fiber U))) :
    letI : 𝒴.val.p.IsFibered := 𝒴.property.isFibered
    (twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g U c).val.2 =
      PresheafOfCategories.isoClassSection eG U
        ((Functor.isoClassMap (p := twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g)
          (q := 𝒴.val.p)
          (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.property
            TwoFibreProductOver.snd_comp_eq)).app (op U) c) := by
  induction c using _root_.Quotient.ind with
  | _ x => rfl

variable [(twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFibered]
  (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eT : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g)
    (presheafOfCategories (T ⋙ typeToCat)).p)

/-- **Stacks 04SD for represented stacks, first projection.** Under the identification of a
presheaf `T` representing the 2-fibre product `𝒳 ×_𝒵 𝒴` with the fibre product `F ×_H G` of the
representing presheaves, the morphism `T ⟶ F` induced by the first projection of the canonical
2-fibre product square is the first projection of `F ×_H G`. -/
theorem fibreProductIsoRepresenting_hom_comp_representingMap_fst :
    (fibreProductIsoRepresenting B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g T eT).hom ≫
        representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒳 T F eT eF
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst =
      Presheaf.fibreProductFst (representingMap B S hS 𝒳 𝒵 F H eF eH f)
        (representingMap B S hS 𝒴 𝒵 G H eG eH g) := by
  apply NatTrans.ext
  funext U
  obtain ⟨W⟩ := U
  apply ConcreteCategory.hom_ext
  intro s
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, fibreProductIsoRepresenting_hom_app]
  have h1 := morphismSpaceEquiv_app_isoClassSection B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒳 T F eT eF
    ⟨CatFiberedInGroupoids.homFunctor
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst,
      CatFiberedInGroupoids.homFunctor_comp_p
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst⟩
    W ((twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g W).symm s)
  have h2 := twoFibreProductIsoClassSectionEquiv_val_fst B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g W
    ((twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g W).symm s)
  rw [Equiv.apply_symm_apply] at h2
  exact h1.trans h2.symm

/-- **Stacks 04SD for represented stacks, second projection.** Under the identification of a
presheaf `T` representing the 2-fibre product `𝒳 ×_𝒵 𝒴` with the fibre product `F ×_H G` of the
representing presheaves, the morphism `T ⟶ G` induced by the second projection of the canonical
2-fibre product square is the second projection of `F ×_H G`. -/
theorem fibreProductIsoRepresenting_hom_comp_representingMap_snd :
    (fibreProductIsoRepresenting B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g T eT).hom ≫
        representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒴 T G eT eG
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd =
      Presheaf.fibreProductSnd (representingMap B S hS 𝒳 𝒵 F H eF eH f)
        (representingMap B S hS 𝒴 𝒵 G H eG eH g) := by
  apply NatTrans.ext
  funext U
  obtain ⟨W⟩ := U
  apply ConcreteCategory.hom_ext
  intro s
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, fibreProductIsoRepresenting_hom_app]
  have h1 := morphismSpaceEquiv_app_isoClassSection B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒴 T G eT eG
    ⟨CatFiberedInGroupoids.homFunctor
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd,
      CatFiberedInGroupoids.homFunctor_comp_p
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd⟩
    W ((twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g W).symm s)
  have h2 := twoFibreProductIsoClassSectionEquiv_val_snd B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g W
    ((twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g W).symm s)
  rw [Equiv.apply_symm_apply] at h2
  exact h1.trans h2.symm

/-- **Stacks 04SD for represented stacks, as a cartesian square.** Under the identification of a
presheaf `T` representing the 2-fibre product `𝒳 ×_𝒵 𝒴` with the fibre product `F ×_H G` of the
representing presheaves, the square of morphisms of representing presheaves induced by the
canonical 2-fibre product square is cartesian.

This is the form in which the identification is consumed: a 1-morphism into a 2-fibre product of
represented categories becomes a morphism into a fibre product of algebraic spaces, so a property
of morphisms of algebraic spaces stable under base change along the relevant leg can be
transported to the projection. The two compatibilities above are what make the transport along
`AlgebraicGeometry.Stack.fibreProductIsoRepresenting` legitimate. -/
theorem isPullback_representingMap_twoFibreProduct :
    IsPullback
      (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒴 T G eT eG
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd)
      (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒳 T F eT eF
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst)
      (representingMap B S hS 𝒴 𝒵 G H eG eH g)
      (representingMap B S hS 𝒳 𝒵 F H eF eH f) :=
  (Presheaf.isPullback_fibreProduct _ _).flip.of_iso
    (fibreProductIsoRepresenting B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g T eT) (Iso.refl G)
    (Iso.refl F) (Iso.refl H)
    (by simpa using (fibreProductIsoRepresenting_hom_comp_representingMap_snd B S hS 𝒳 𝒴 𝒵
      F G H eF eG eH f g T eT).symm)
    (by simpa using (fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS 𝒳 𝒴 𝒵
      F G H eF eG eH f g T eT).symm)
    (by simp) (by simp)

end AlgebraicGeometry.Stack

end
