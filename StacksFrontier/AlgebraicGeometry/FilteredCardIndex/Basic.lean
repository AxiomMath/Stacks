module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.CategoryTheory.Subobject.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import StacksFrontier.CategoryTheory.WellPowered.Sheaf

/-!
# A filtered colimit is a directed colimit indexed by a preorder in `Type u`

A colimit over a filtered, essentially `w`-small category is also a colimit over a nonempty
directed preorder in `Type w`, and every object of the new diagram is an object of the old one.
The second half of the file specialises this to diagrams of quasi-coherent, finite, finitely
presented algebra sheaves on a scheme.

## Main results

* `Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered`: a colimit over a filtered,
  essentially `w`-small index is a colimit over a nonempty directed preorder in `Type w`,
  preserving any property of the objects of the diagram.
* `Stacks.FilteredCardIndex.exists_finite_finitePresentation_index_of_isFiltered`: an algebra
  sheaf which is the colimit of a filtered, essentially `u`-small diagram of quasi-coherent,
  finite, finitely presented algebra sheaves is the colimit of such a diagram indexed by a
  nonempty directed preorder in `Type u`.
* `Stacks.FilteredCardIndex.exists_finite_finitePresentation_index_of_subobject`: the same with
  the index a filtered full subcategory of `CategoryTheory.Subobject A`, with no smallness
  hypothesis.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
* [Alexander Grothendieck and Jean-Louis Verdier, *Exposé I : Préfaisceaux*, SGA 4 I 8.1.6]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v₂ u₂ v₁ u₁ u

namespace Stacks.FilteredCardIndex

section General

variable {C : Type u₁} [Category.{v₁} C]

/-- The objects of a full subcategory of a `w`-small category form a `w`-small type: the
inclusion on objects is injective, the property being a `Prop`. -/
instance small_fullSubcategory [Small.{w} C] (P : ObjectProperty C) :
    Small.{w} P.FullSubcategory :=
  small_of_injective (f := fun B : P.FullSubcategory => B.obj)
    fun _ _ h => ObjectProperty.FullSubcategory.ext h

/-- If `D` is a filtered, essentially `w`-small category and `A` is the colimit of a diagram
`G : D ⥤ C` under the cocone `t`, then `A` is also the colimit of a diagram indexed by a nonempty
directed preorder lying in `Type w`, and every object of the new diagram is an object of the old
one — so any property `P` holding throughout `G` holds throughout the new diagram. -/
theorem exists_directed_index_of_isFiltered {D : Type u₂} [Category.{v₂} D]
    [IsFiltered D] [EssentiallySmall.{w} D] {G : D ⥤ C} {A : C}
    (t : G ⟶ (Functor.const D).obj A) (ht : IsColimit (Cocone.mk A t))
    (P : C → Prop) (hP : ∀ d, P (G.obj d)) :
    ∃ (I : Type w) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ C) (s : F ⟶ (Functor.const I).obj A) (_ : IsColimit (Cocone.mk A s)),
      ∀ i, P (F.obj i) := by
  have : IsFiltered (SmallModel.{w} D) := IsFiltered.of_equivalence (equivSmallModel.{w} D)
  obtain ⟨α, _, _, _, F₀, _⟩ := IsFiltered.exists_directed (SmallModel.{w} D)
  let e : SmallModel.{w} D ≌ D := (equivSmallModel.{w} D).symm
  refine ⟨α, inferInstance, inferInstance, inferInstance, F₀ ⋙ e.functor ⋙ G,
    (((Cocone.mk A t).whisker e.functor).whisker F₀).ι, ?_, fun i => hP _⟩
  exact (Functor.Final.isColimitWhiskerEquiv F₀ _).symm (ht.whiskerEquivalence e)

end General

section AlgebraSheaf

open Stacks.RelativeSpec

variable {X : Scheme.{u}}

/-- If the algebra sheaf `A` is the colimit of a filtered, essentially `u`-small diagram of
quasi-coherent, finite, finitely presented algebra sheaves, then `A` is the colimit of a diagram
of quasi-coherent, finite, finitely presented algebra sheaves indexed by a nonempty directed
preorder in `Type u`. -/
theorem exists_finite_finitePresentation_index_of_isFiltered (A : AlgebraSheaf X)
    {D : Type u₂} [Category.{v₂} D] [IsFiltered D] [EssentiallySmall.{u} D]
    {G : D ⥤ AlgebraSheaf X} (t : G ⟶ (Functor.const D).obj A)
    (ht : IsColimit (Cocone.mk A t))
    (hG : ∀ d, (G.obj d).IsQuasicoherent ∧ (G.obj d).IsFinite ∧
      (G.obj d).IsFinitePresentation) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧
        (F.obj i).IsFinitePresentation :=
  exists_directed_index_of_isFiltered t ht
    (fun B => B.IsQuasicoherent ∧ B.IsFinite ∧ B.IsFinitePresentation) hG

/-- If the algebra sheaf `A` is the colimit of a diagram of quasi-coherent, finite, finitely
presented algebra sheaves indexed by a filtered full subcategory of `CategoryTheory.Subobject A`,
then `A` is the colimit of a diagram of quasi-coherent, finite, finitely presented algebra
sheaves indexed by a nonempty directed preorder in `Type u`. -/
theorem exists_finite_finitePresentation_index_of_subobject (A : AlgebraSheaf X)
    (P : ObjectProperty (Subobject A)) [IsFiltered P.FullSubcategory]
    {G : P.FullSubcategory ⥤ AlgebraSheaf X} (t : G ⟶ (Functor.const _).obj A)
    (ht : IsColimit (Cocone.mk A t))
    (hG : ∀ B, (G.obj B).IsQuasicoherent ∧ (G.obj B).IsFinite ∧
      (G.obj B).IsFinitePresentation) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧
        (F.obj i).IsFinitePresentation :=
  exists_finite_finitePresentation_index_of_isFiltered A t ht hG

end AlgebraSheaf

end Stacks.FilteredCardIndex

end
