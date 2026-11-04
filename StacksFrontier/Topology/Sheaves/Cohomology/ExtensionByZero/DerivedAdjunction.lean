module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleAdjunction
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero and restriction on unbounded derived categories

Let `X` be a ringed space and `U ⊆ X` an open subset, with `j_! ⊣ j^*` the
extension-by-zero/restriction adjunction between sheaves of `O|_U`-modules on `U` and sheaves of
`O`-modules on `X`. Both functors are exact, and the induced functors on the unbounded derived
categories are again adjoint: `D(j_!) ⊣ D(j^*)`.

## Main definitions

* `CategoryTheory.Adjunction.mapDerivedCategory`: the derived form of an adjunction between
  exact additive functors of abelian categories with derived categories.

## Main results

* `CategoryTheory.mapDerivedCategoryAdjunction_unit_app_Q`: the unit of the derived adjunction
  on the image of a complex.
* `Stacks.ExtensionByZero.exists_derivedJShriek_restriction_adjunction`: the functor on unbounded
  derived categories induced by extension by zero is left adjoint to the one induced by
  restriction.
* `Stacks.ExtensionByZero.jStar_additive_and_exact`: restriction to an open subset is exact.
* `Stacks.ExtensionByZero.jShriek_additive_and_exact`: extension by zero from an open subset is
  exact.

## References

* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
* [Stacks Project, Tag 00A7](https://stacks.math.columbia.edu/tag/00A7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace CategoryTheory.Adjunction

/-- An adjunction between exact additive functors of abelian categories with derived
categories induces an adjunction between the derived functors. -/
@[sga "4 XVII 5.1.3" "more general"]
noncomputable def mapDerivedCategory
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  let : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) _ _

end CategoryTheory.Adjunction

namespace CategoryTheory

/-- The unit of the derived adjunction, on the image of a complex. -/
theorem mapDerivedCategoryAdjunction_unit_app_Q
    {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    [Category* B] [Abelian B] [HasDerivedCategory B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (X : CochainComplex A ℤ) :
    (CategoryTheory.Adjunction.mapDerivedCategory adj).unit.app
        (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app X) ≫
        G.mapDerivedCategoryFactors.inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) := by
  simp only [CategoryTheory.Adjunction.mapDerivedCategory,
    Adjunction.localization_unit_app]
  rfl

end CategoryTheory

namespace Stacks.ExtensionByZero

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

/-- For an open subset `U` of a ringed space `X`, extension by zero and restriction to `U` are
exact, and the functor on unbounded derived categories induced by extension by zero is left
adjoint to the functor induced by restriction to `U`. -/
@[stacks 08BT]
theorem exists_derivedJShriek_restriction_adjunction
    (X : SheafedSpace RingCat.{u}) (U : Opens X.carrier) :
    ∃ (h₁ : (jShriek00A7 X U).Additive)
      (h₂ : PreservesFiniteLimits (jShriek00A7 X U))
      (h₃ : PreservesFiniteColimits (jShriek00A7 X U))
      (h₄ : (restMod X U).Additive)
      (h₅ : PreservesFiniteLimits (restMod X U))
      (h₆ : PreservesFiniteColimits (restMod X U)),
      letI := h₁
      letI := h₂
      letI := h₃
      letI := h₄
      letI := h₅
      letI := h₆
      Nonempty ((jShriek00A7 X U).mapDerivedCategory ⊣ (restMod X U).mapDerivedCategory) := by
  have : (jShriek00A7 X U).IsLeftAdjoint := (jShriekAdjunction X U).isLeftAdjoint
  have : PreservesColimitsOfSize (jShriek00A7 X U) :=
    (jShriekAdjunction X U).leftAdjoint_preservesColimits
  have : PreservesLimitsOfSize (restMod X U) :=
    (jShriekAdjunction X U).rightAdjoint_preservesLimits
  have : (restMod X U).IsLeftAdjoint :=
    (ExtensionByZeroModules.jStarAdjunction U (OXSh X)).isLeftAdjoint
  have : (jShriek00A7 X U).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : (restMod X U).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : (jShriek00A7 X U).PreservesMonomorphisms :=
    ExtensionByZeroModules.jShriek_preservesMonomorphisms U (OXSh X)
  have : (jShriek00A7 X U).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  have : PreservesFiniteLimits (jShriek00A7 X U) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(jShriekAdjunction X U).mapDerivedCategory⟩⟩

/-- Restriction to an open subset is exact: it is additive and preserves finite limits and
finite colimits. -/
public lemma jStar_additive_and_exact {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (V : Opens X) :
    (ExtensionByZeroModules.jStar V O).Additive ∧
      PreservesFiniteLimits (ExtensionByZeroModules.jStar V O) ∧
      PreservesFiniteColimits (ExtensionByZeroModules.jStar V O) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Extension by zero from an open subset is exact: it is additive and preserves finite limits
and finite colimits. -/
@[sga "4 XVII 5.1.3" "partial"]
public lemma jShriek_additive_and_exact {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (V : Opens X) :
    (ExtensionByZeroModules.jShriek V O).Additive ∧
      PreservesFiniteLimits (ExtensionByZeroModules.jShriek V O) ∧
      PreservesFiniteColimits (ExtensionByZeroModules.jShriek V O) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end Stacks.ExtensionByZero
