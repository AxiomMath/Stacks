module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# An explicit complex computing a right derived functor on `D⁺`

Let `G : C ⥤ D` be an additive functor between abelian categories, with `C` having enough
injectives, and let `X` be an object of `DerivedCategory.Plus C` lying in degrees `≥ n`. Then `X`
is the image of a cochain complex `J` of injective objects of `C` concentrated in degrees `≥ n`,
and the value `G.rightDerivedFunctorPlus.obj X` is the image in the derived category of the
complex obtained by applying `G` to `J` termwise.

This is the statement that a right derived functor is computed on an injective resolution, in the
form that produces an explicit cochain complex representing the value: that complex is what a
model-dependent argument — a vanishing checked after tensoring with an explicit complex, say —
consumes.

## Main results

* `Stacks.InjectiveModel.rightDerivedFunctorPlusUnitIso`: the unit of the right derived functor
  at a bounded below complex of injective objects, as an isomorphism; its invertibility is a
  Mathlib instance.
* `Stacks.InjectiveModel.exists_nonempty_Q_obj_iso_rightDerivedFunctorPlus`: the injective
  resolution and the resulting isomorphism in the unbounded derived category of `D`.
* `Stacks.InjectiveModel.acyclic_mapHomologicalComplex_of_acyclic`: an additive functor carries a
  bounded below acyclic complex of injective objects to an acyclic complex.

## Implementation notes

Mathlib's `CategoryTheory.Functor.rightDerivedFunctorPlusUnith` is a natural transformation out of
`G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh`, so its source at a complex `K` is the
image of `K` under the localization functor factored through the homotopy category. The two
localization functors `DerivedCategory.Plus.Q` and
`HomotopyCategory.Plus.quotient ⋙ DerivedCategory.Plus.Qh` are compared by
`Stacks.InjectiveModel.plusQhIsoPlusQ`, which is Mathlib's
`DerivedCategory.quotientCompQhIso` read through the fully faithful inclusion of
`DerivedCategory.Plus C` into `DerivedCategory C`.

The invertibility of the unit at a complex of injective objects is available to typeclass
inference, through the derivability structure of
`Mathlib/Algebra/Homology/DerivedCategory/DerivabilityStructureInjectives.lean`;
`Stacks.InjectiveModel.rightDerivedFunctorPlusUnitIso` packages it as an isomorphism.

`Stacks.InjectiveModel.acyclic_mapHomologicalComplex_of_acyclic` needs no derived category: a
bounded below complex of injective objects is K-injective
(`CochainComplex.isKInjective_of_injective`), so if it is moreover acyclic its identity is
null-homotopic (`CochainComplex.IsKInjective.homotopyZero`), which says it is a zero object of the
homotopy category — and that is preserved by the functor an additive functor induces on homotopy
categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace Stacks.InjectiveModel

section Acyclic

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (G : C ⥤ D) [G.Additive]

/-- **A bounded below acyclic complex of injective objects stays acyclic under an additive
functor.** Such a complex is a zero object of the homotopy category, and the functor induced on
homotopy categories carries zero objects to zero objects. -/
theorem acyclic_mapHomologicalComplex_of_acyclic (J : CochainComplex C ℤ) (n : ℤ)
    [J.IsStrictlyGE n] [∀ i, Injective (J.X i)] (hJ : J.Acyclic) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J).Acyclic := by
  have hKI : J.IsKInjective := CochainComplex.isKInjective_of_injective J n
  have h : Homotopy (𝟙 J) 0 := CochainComplex.IsKInjective.homotopyZero (𝟙 J) hJ
  have h0 : IsZero ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj J) := by
    rw [IsZero.iff_id_eq_zero, ← (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_id J,
      HomotopyCategory.eq_of_homotopy _ _ h, Functor.map_zero]
  have h2 : IsZero ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :=
    (Functor.map_isZero (G.mapHomotopyCategory (ComplexShape.up ℤ)) h0).of_iso
      ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app J)
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) i).app _).isZero_iff.mp
    ((HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) i).map_isZero h2)

end Acyclic

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D]

/-- **The two localizations of bounded below complexes agree.** The image of a bounded below
cochain complex in `D⁺(C)`, formed directly or through the bounded below homotopy category. -/
def plusQhIsoPlusQ (M : CochainComplex.Plus C) :
    DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj M) ≅
      DerivedCategory.Plus.Q.obj M :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.quotientCompQhIso C).app ((CochainComplex.Plus.ι C).obj M))

variable (G : C ⥤ D) [G.Additive] [EnoughInjectives C]

/-- The unit of a right derived functor at a bounded below complex of injective objects, as an
isomorphism. -/
def rightDerivedFunctorPlusUnitIso (J : CochainComplex.Plus (InjectiveObject C)) :
    DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient C).obj
          ((InjectiveObject.ι C).mapCochainComplexPlus.obj J))) ≅
      G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient C).obj
          ((InjectiveObject.ι C).mapCochainComplexPlus.obj J))) :=
  asIso (G.rightDerivedFunctorPlusUnith.app _)

/-- **A right derived functor is computed on an injective resolution.** An object `X` of `D⁺(C)`
lying in degrees `≥ n` is the image of a complex `J` of injective objects in degrees `≥ n`, and
`G.rightDerivedFunctorPlus.obj X` is then the image of `G` applied to `J` termwise. -/
theorem exists_nonempty_Q_obj_iso_rightDerivedFunctorPlus
    (X : DerivedCategory.Plus C) (n : ℤ) [X.IsGE n] :
    ∃ J : CochainComplex.Plus (InjectiveObject C), J.obj.IsStrictlyGE n ∧
      Nonempty (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj J.obj)) ≅
        DerivedCategory.Plus.ι.obj (G.rightDerivedFunctorPlus.obj X)) := by
  obtain ⟨J, hJ, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso X n
  refine ⟨J, hJ, ⟨?_⟩⟩
  exact DerivedCategory.Plus.ι.mapIso ((plusQhIsoPlusQ (G.mapCochainComplexPlus.obj
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj J))).symm ≪≫
    rightDerivedFunctorPlusUnitIso G J ≪≫
    G.rightDerivedFunctorPlus.mapIso
      (plusQhIsoPlusQ ((InjectiveObject.ι C).mapCochainComplexPlus.obj J) ≪≫ e))

end Stacks.InjectiveModel

end
