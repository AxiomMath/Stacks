module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtLocalToGlobal

/-!
# The derived functor of an equivalence of abelian categories, at any universes

An equivalence `e : C ≌ D` of abelian categories with additive functors induces an equivalence
of derived categories `D(C) ≌ D(D)`, for categories at arbitrary universes.

## Main results

* `Stacks.SheafOfModules.mapDerivedCategory_isEquivalence_general`: `e.functor.mapDerivedCategory`
  is an equivalence.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.SheafOfModules

/-- The derived functor of an equivalence of abelian categories is an equivalence. -/
theorem mapDerivedCategory_isEquivalence_general {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    e.functor.mapDerivedCategory.IsEquivalence := by
  let Φ := e.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let Ψ := e.inverse.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let ec := e.mapHomologicalComplex (ComplexShape.up ℤ)
  have hΦ : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_unit_of_unit Ψ ec.unitIso.hom ec.counitIso.inv
      (fun K => inferInstanceAs (QuasiIso (ec.unitIso.app K).hom))
      (fun K => inferInstanceAs (QuasiIso (ec.counitIso.app K).inv))
  let _ : CatCommSq Φ.functor DerivedCategory.Q DerivedCategory.Q
      e.functor.mapDerivedCategory := ⟨e.functor.mapDerivedCategoryFactors.symm⟩
  exact Φ.isEquivalence DerivedCategory.Q DerivedCategory.Q e.functor.mapDerivedCategory

end Stacks.SheafOfModules

end
