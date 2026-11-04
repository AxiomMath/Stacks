module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Sheaves

/-!
# Inverse image along the localization at a semi-representable object

Let `(C, J)` be a site and `K = ⨿ i, K.obj i` a semi-representable object of `C`. The site
`C / K` localized at `K` is the disjoint union of the slice sites `C / K.obj i`, so a sheaf on
it is a family of sheaves on those slices. Under that identification the inverse image
`j⁻¹ : Sh(C) ⥤ Sh(C / K)` along the localization is the family of the one-object inverse images
`CategoryTheory.GrothendieckTopology.overPullback`, one for each component.

This file constructs that functor for sheaves valued in an arbitrary category, identifies it
with componentwise restriction, and extends it to complexes of abelian sheaves. The last step
is what makes the functor usable in homological algebra, for instance in the statement that it
preserves K-injective complexes.

## Main definitions

* `CategoryTheory.SemiRepresentable.componentInverseImage`: the family of component inverse
  images `Sh(C) ⥤ ∏ i, Sh(C / K.obj i)`.
* `CategoryTheory.SemiRepresentable.localizationInverseImage`: the inverse image
  `Sh(C) ⥤ Sh(C / K)` along the localization.
* `CategoryTheory.SemiRepresentable.localizationInverseImageMapHomologicalComplex`: its
  extension to cochain complexes of abelian sheaves.

## Main results

* `CategoryTheory.SemiRepresentable.localizationInverseImageCompEquivalenceIso`: the
  localization inverse image becomes componentwise restriction under the canonical equivalence
  of sheaf categories.
* `CategoryTheory.SemiRepresentable.localizationInverseImageMapHomologicalComplexComponentIso`:
  the same identification on complexes, as an isomorphism of functors on complexes rather than
  unrelated isomorphisms of their terms.

## Implementation notes

The localized site and its topology are `CategoryTheory.SemiRepresentable.ComponentOver` and
`CategoryTheory.SemiRepresentable.componentwiseTopology`; the equivalence of its sheaf category
with the product of the component sheaf categories, together with its canonical restriction
isomorphisms, is `CategoryTheory.SemiRepresentable.formalCoproductSliceSheavesEquivalence`. The
localization inverse image is obtained from componentwise restriction by the inverse of that
equivalence, so it is a quasi-inverse of a chosen equivalence and not a second construction.

The functors on complexes take the ambient zero-morphism structures as instance arguments.
Those structures are unique (`HasZeroMorphisms` is a subsingleton), but the one inherited from
the full subcategory of presheaves need not be definitionally equal to the one supplied by an
`Abelian` instance; keeping them as parameters makes the complex inverse image usable with
homological constructions without restricting the universes or assuming sheafification. The
zero-preservation statements are proved for one choice and transported to any other by
`Subsingleton.elim`.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public section

namespace CategoryTheory.SemiRepresentable

open CategoryTheory CategoryTheory.Limits

universe u v w u' v'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)

/-- Inverse image along the localization at a semi-representable object, presented as the
family of the inverse images along the localizations at its components. -/
def componentInverseImage (A : Type u') [Category.{v'} A] :
    Sheaf J A ⥤ ((i : K.I) → Sheaf (J.over (K.obj i)) A) :=
  Functor.pi' fun i => J.overPullback A (K.obj i)

/-- Inverse image from a site to its localization at a semi-representable object: the inverse
of the canonical decomposition turns the family of component restrictions into a single sheaf
on the disjoint-union site `C / K`. -/
noncomputable def localizationInverseImage (A : Type u') [Category.{v'} A] :
    Sheaf J A ⥤ Sheaf (componentwiseTopology J K) A :=
  componentInverseImage J K A ⋙
    (formalCoproductSliceSheavesEquivalence J K A).1.inverse

/-- Evaluating the family of component inverse images at the index `i` gives the inverse image
along the localization at `K.obj i`. -/
def componentInverseImageCompEvalIso (A : Type u') [Category.{v'} A] (i : K.I) :
    componentInverseImage J K A ⋙ Pi.eval (fun j : K.I ↦ Sheaf (J.over (K.obj j)) A) i ≅
      J.overPullback A (K.obj i) :=
  Functor.pi'CompEval (fun j : K.I ↦ J.overPullback A (K.obj j)) i

/-- Under the canonical equivalence of `Sh(C / K)` with the product of the component sheaf
categories, the localization inverse image is componentwise restriction. -/
noncomputable def localizationInverseImageCompEquivalenceIso (A : Type u') [Category.{v'} A] :
    localizationInverseImage J K A ⋙
        (formalCoproductSliceSheavesEquivalence J K A).1.functor ≅
      componentInverseImage J K A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (componentInverseImage J K A)
      (formalCoproductSliceSheavesEquivalence J K A).1.counitIso ≪≫
    Functor.rightUnitor _

/-- Restricting the localization inverse image of a sheaf to the `i`-th component of `C / K`
recovers the inverse image along the localization at `K.obj i`. -/
noncomputable def localizationInverseImageCompEvalIso (A : Type u') [Category.{v'} A]
    (i : K.I) :
    localizationInverseImage J K A ⋙
        ((formalCoproductSliceSheavesEquivalence J K A).1.functor ⋙
          Pi.eval (fun j : K.I ↦ Sheaf (J.over (K.obj j)) A) i) ≅
      J.overPullback A (K.obj i) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (localizationInverseImageCompEquivalenceIso J K A) _ ≪≫
    componentInverseImageCompEvalIso J K A i

section Abelian

/-- The componentwise zero morphisms on a product of categories of abelian sheaves. -/
private instance hasZeroMorphismsSheafFamily :
    HasZeroMorphisms ((i : K.I) → Sheaf (J.over (K.obj i)) AddCommGrpCat.{u'}) where
  zero X Y := ⟨fun i => 0⟩
  comp_zero := by
    intro X Y f Z
    change (fun i => f i ≫ (0 : Y i ⟶ Z i)) = fun i => (0 : X i ⟶ Z i)
    funext i
    exact CategoryTheory.Limits.comp_zero (f := f i)
  zero_comp := by
    intro X Y Z f
    change (fun i => (0 : X i ⟶ Y i) ≫ f i) = fun i => (0 : X i ⟶ Z i)
    funext i
    exact CategoryTheory.Limits.zero_comp (f := f i)

private theorem overPullback_preservesZeroMorphisms_aux (i : K.I) :
    (J.overPullback AddCommGrpCat.{u'} (K.obj i)).PreservesZeroMorphisms := by
  constructor
  intro X Y
  ext U x
  rfl

private theorem localizationInverseImage_preservesZeroMorphisms_aux :
    (localizationInverseImage J K AddCommGrpCat.{u'}).PreservesZeroMorphisms := by
  have : (componentInverseImage J K AddCommGrpCat.{u'}).PreservesZeroMorphisms := by
    constructor
    intro X Y
    show (fun i => (J.overPullback AddCommGrpCat.{u'} (K.obj i)).map (0 : X ⟶ Y)) =
      fun i => 0
    funext i
    exact (overPullback_preservesZeroMorphisms_aux J K i).map_zero X Y
  exact Functor.preservesZeroMorphisms_comp _ _

private theorem componentRestriction_preservesZeroMorphisms_aux (i : K.I) :
    ((formalCoproductSliceSheavesEquivalence J K AddCommGrpCat.{u'}).1.functor ⋙
      Pi.eval (fun j : K.I ↦ Sheaf (J.over (K.obj j))
        AddCommGrpCat.{u'}) i).PreservesZeroMorphisms := by
  let e := (formalCoproductSliceSheavesEquivalence J K AddCommGrpCat.{u'}).1
  have : e.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have : (Pi.eval (fun j : K.I ↦ Sheaf (J.over (K.obj j))
      AddCommGrpCat.{u'}) i).PreservesZeroMorphisms :=
    ⟨fun _ _ => rfl⟩
  exact Functor.preservesZeroMorphisms_comp _ _

/-- Inverse image along the localization at a semi-representable object respects any choices of
zero morphisms on the two categories of abelian sheaves. -/
instance localizationInverseImage_preservesZeroMorphisms
    [HasZeroMorphisms (Sheaf J AddCommGrpCat.{u'})]
    [HasZeroMorphisms (Sheaf (componentwiseTopology J K) AddCommGrpCat.{u'})] :
    (localizationInverseImage J K AddCommGrpCat.{u'}).PreservesZeroMorphisms := by
  convert localizationInverseImage_preservesZeroMorphisms_aux J K using 1 <;>
    exact Subsingleton.elim _ _

/-- Restriction of an abelian sheaf from the disjoint-union site `C / K` to one component
respects any choices of zero morphisms. -/
instance componentRestriction_preservesZeroMorphisms (i : K.I)
    [HasZeroMorphisms (Sheaf (componentwiseTopology J K) AddCommGrpCat.{u'})]
    [HasZeroMorphisms (Sheaf (J.over (K.obj i)) AddCommGrpCat.{u'})] :
    ((formalCoproductSliceSheavesEquivalence J K AddCommGrpCat.{u'}).1.functor ⋙
      Pi.eval (fun j : K.I ↦ Sheaf (J.over (K.obj j))
        AddCommGrpCat.{u'}) i).PreservesZeroMorphisms := by
  convert componentRestriction_preservesZeroMorphisms_aux J K i using 1 <;>
    exact Subsingleton.elim _ _

/-- Inverse image along the localization at a single component respects any choices of zero
morphisms. -/
instance overPullback_preservesZeroMorphisms (i : K.I)
    [HasZeroMorphisms (Sheaf J AddCommGrpCat.{u'})]
    [HasZeroMorphisms (Sheaf (J.over (K.obj i)) AddCommGrpCat.{u'})] :
    (J.overPullback AddCommGrpCat.{u'} (K.obj i)).PreservesZeroMorphisms := by
  convert overPullback_preservesZeroMorphisms_aux J K i using 1 <;>
    exact Subsingleton.elim _ _

/-- The inverse image along the localization at a semi-representable object, applied to every
term and every differential of a cochain complex of abelian sheaves. -/
noncomputable def localizationInverseImageMapHomologicalComplex
    [HasZeroMorphisms (Sheaf J AddCommGrpCat.{u'})]
    [HasZeroMorphisms (Sheaf (componentwiseTopology J K) AddCommGrpCat.{u'})] :
    CochainComplex (Sheaf J AddCommGrpCat.{u'}) ℤ ⥤
      CochainComplex (Sheaf (componentwiseTopology J K) AddCommGrpCat.{u'}) ℤ :=
  (localizationInverseImage J K AddCommGrpCat.{u'}).mapHomologicalComplex (ComplexShape.up ℤ)

/-- On complexes, the localization inverse image followed by restriction to the `i`-th component
is the inverse image along the localization at `K.obj i`, as an isomorphism of functors on
complexes and not merely as unrelated isomorphisms of their terms. -/
noncomputable def localizationInverseImageMapHomologicalComplexComponentIso (i : K.I)
    [HasZeroMorphisms (Sheaf J AddCommGrpCat.{u'})]
    [HasZeroMorphisms (Sheaf (componentwiseTopology J K) AddCommGrpCat.{u'})]
    [HasZeroMorphisms (Sheaf (J.over (K.obj i)) AddCommGrpCat.{u'})] :
    localizationInverseImageMapHomologicalComplex J K ⋙
        (((formalCoproductSliceSheavesEquivalence J K AddCommGrpCat.{u'}).1.functor ⋙
          Pi.eval (fun j : K.I ↦ Sheaf (J.over (K.obj j))
            AddCommGrpCat.{u'}) i).mapHomologicalComplex (ComplexShape.up ℤ)) ≅
      (J.overPullback AddCommGrpCat.{u'} (K.obj i)).mapHomologicalComplex
        (ComplexShape.up ℤ) := by
  let α := localizationInverseImageCompEvalIso J K AddCommGrpCat.{u'} i
  exact NatIso.ofComponents (fun L => HomologicalComplex.Hom.isoOfComponents
      (fun n => α.app (L.X n)) (fun n m _ => by
        dsimp [localizationInverseImageMapHomologicalComplex, Functor.mapHomologicalComplex]
        simpa [Functor.map_comp] using (α.hom.naturality (L.d n m)).symm))
    (fun {L M} f => by
      refine HomologicalComplex.hom_ext _ _ fun n => ?_
      dsimp [localizationInverseImageMapHomologicalComplex, Functor.mapHomologicalComplex]
      exact α.hom.naturality (f.f n))

end Abelian

end CategoryTheory.SemiRepresentable

end
