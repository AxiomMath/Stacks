module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Naturality of the comparison for shifted heart objects

Let `F` be an exact endofunctor of the bounded derived category of an abelian category `A` and let
`α` be a natural isomorphism between the inclusion of `A` in degree zero and its composite with
`F`. Shifting `α` and using the shift isomorphism of `F` extends the comparison to objects
concentrated in any one degree, and for morphisms between objects concentrated in the same degree
the resulting square commutes.

## Main definitions

* `AlgebraicGeometry.shiftedRestrictionIso`: the comparison isomorphism on a shifted heart object.

## Main results

* `AlgebraicGeometry.shiftedRestrictionIso_naturality`: the commutative square of Tag 0FZX.

## Implementation notes

The equation is stated for an arbitrary morphism between two heart objects shifted by the same
integer, which is the initial case of the source's subsequent argument for arbitrary width-one
objects.

## References

* [Stacks Project, Tag 0FZX](https://stacks.math.columbia.edu/tag/0FZX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {F : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A}
  [F.CommShift ℤ]

/-- The comparison on a degree-zero object, transported to a shift of that object. -/
public noncomputable def shiftedRestrictionIso
    (α : boundedSingleFunctor A ≅ boundedSingleFunctor A ⋙ F) (n : ℤ) (X : A) :
    ((boundedSingleFunctor A).obj X)⟦n⟧ ≅ F.obj (((boundedSingleFunctor A).obj X)⟦n⟧) :=
  (shiftFunctor (DerivedCategory.Bounded A) n).mapIso (α.app X) ≪≫
    ((F.commShiftIso n).app ((boundedSingleFunctor A).obj X)).symm

/-- **Stacks Project, Tag 0FZX.** The shifted comparison with a functor agreeing with the
identity on the heart commutes with morphisms between objects concentrated in the same degree. -/
@[stacks 0FZX]
public theorem shiftedRestrictionIso_naturality
    (α : boundedSingleFunctor A ≅ boundedSingleFunctor A ⋙ F)
    (n : ℤ) (X Y : A)
    (f : ((boundedSingleFunctor A).obj X)⟦n⟧ ⟶ ((boundedSingleFunctor A).obj Y)⟦n⟧) :
    f ≫ (shiftedRestrictionIso α n Y).hom =
      (shiftedRestrictionIso α n X).hom ≫ F.map f := by
  let B := boundedSingleFunctor A
  let S := shiftFunctor (DerivedCategory.Bounded A) n
  let hS : S.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful S
  let hB : B.FullyFaithful := Functor.FullyFaithful.ofCompFaithful
    ((Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor A 0)).ofIso
      (boundedSingleFunctorCompιIso A).symm)
  obtain ⟨g₀, rfl⟩ := hS.map_surjective f
  obtain ⟨g, rfl⟩ := hB.map_surjective g₀
  simp only [shiftedRestrictionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom]
  change S.map (B.map g) ≫ S.map (α.hom.app Y) ≫ (F.commShiftIso n).inv.app (B.obj Y) =
    (S.map (α.hom.app X) ≫ (F.commShiftIso n).inv.app (B.obj X)) ≫
      F.map (S.map (B.map g))
  rw [← Category.assoc, ← S.map_comp, α.hom.naturality g, Functor.comp_map,
    S.map_comp, Category.assoc,
    Functor.commShiftIso_inv_naturality, ← Category.assoc]

end AlgebraicGeometry

end
