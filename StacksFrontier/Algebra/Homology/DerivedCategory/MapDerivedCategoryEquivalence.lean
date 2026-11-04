module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public noncomputable section

/-!
# An equivalence of abelian categories induces an equivalence of derived categories

An exact functor between abelian categories with derived categories acts on them degreewise,
through `CategoryTheory.Functor.mapDerivedCategory`. This file records that this action is an
equivalence as soon as the functor itself is: the induced functor on cochain complexes is an
equivalence, it is induced on the quasi-isomorphisms, and hence it is a localized equivalence
for the localizations defining the derived categories.

## Main results

* `Stacks.Injectives.mapDerivedCategory_isEquivalence`: the degreewise action on derived
  categories of an additive equivalence of abelian categories is an equivalence.
-/

open CategoryTheory Limits

namespace Stacks.Injectives

/-- An additive equivalence of abelian categories with derived categories induces an equivalence
of those derived categories. -/
lemma mapDerivedCategory_isEquivalence {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [G.IsEquivalence] :
    G.mapDerivedCategory.IsEquivalence := by
  let : (G.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence :=
    (G.asEquivalence.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  let : (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.IsEquivalence :=
    inferInstanceAs (G.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence
  let : (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsInduced := by
    refine ⟨?_⟩
    ext K L f
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f G
  let : (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsLocalizedEquivalence :=
    LocalizerMorphism.isLocalizedEquivalence_of_isInduced _
  let : CatCommSq (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).isEquivalence
    DerivedCategory.Q DerivedCategory.Q _

end Stacks.Injectives
