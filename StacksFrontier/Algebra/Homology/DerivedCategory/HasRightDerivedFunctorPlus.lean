module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Existence of the right derived functor on the bounded below homotopy category, at its head

`CategoryTheory.Functor.rightAcyclic` and `CategoryTheory.Functor.rightDerivedFunctorPlus` are
stated for a functor `F : C ⥤ D` whose composite `K⁺(C) ⥤ D⁺(C) ⥤ D⁺(D)` has a right derived
functor. For an additive `F` out of an abelian category with enough injectives that condition
holds, by the injective derivability structure, and Mathlib relies on instance search to find it.
That search is deep: as soon as a handful of unrelated instances are in scope it exhausts the
default `synthInstance.maxHeartbeats` and `CategoryTheory.Functor.rightAcyclic` can then not even
be *written down*. This module records the conclusion at its head, in an import closure small
enough for the search to succeed, so that downstream it is one step.

## Main results

* `CategoryTheory.Functor.hasRightDerivedFunctor_mapHomotopyCategoryPlus_comp_Qh`
-/

@[expose] public section

universe t t' v v' u u'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- **An additive functor out of an abelian category with enough injectives has a right derived
functor on the bounded below homotopy category.** This is the side condition of
`CategoryTheory.Functor.rightAcyclic`, recorded at its head so that instance search need not
rebuild the injective derivability structure. -/
public instance (priority := 2000) hasRightDerivedFunctor_mapHomotopyCategoryPlus_comp_Qh
    {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D] (F : C ⥤ D) [F.Additive]
    [EnoughInjectives C] :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C) :=
  inferInstance

end CategoryTheory.Functor

end
