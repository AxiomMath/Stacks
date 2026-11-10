module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.AcyclicityAndBoundedBelow
public import StacksFrontier.Homology.DerivedIndexing.CompositeCommShift

/-!
# The comparison of Stacks 01F1 commutes with the shift

Let `X` be a ringed space and `U` an open subset. Stacks 01F1 part (1), for bounded below
complexes, is the isomorphism

`R⁺Γ(U, -) ⋙ R⁺(forget) ≅ R⁺(toSheaf) ⋙ R⁺Γ_{Ab}(U, -)`

of `Stacks.Cohomology.ModuleComparison.rightDerivedFunctorPlus_sections_forget_iso`, between the
derived sections over `U` computed in sheaves of modules and then forgotten, and those of the
underlying complex of abelian sheaves. Both sides are composites of bounded below right derived
functors, and each commutes with the shift by `ℤ`. This file shows that the comparison does too.

Both factors of the comparison are, by definition, canonical maps `R(Q ∘ P) ⟶ RQ ∘ RP` of
[Stacks, Tag 05T2] out of the right derived functor of the same composite `Γ(U, -) ∘ forget`,
namely `Stacks.DerivedIndexing.rightDerivedPlusCompTrans`, which commutes with the shift by
`Stacks.DerivedIndexing.natTransCommShift_rightDerivedPlusCompTrans`.

## Main results

* `natTransCommShift_rightDerivedFunctorPlus_sections_forget_iso`:
  **the comparison of Stacks 01F1 for bounded below complexes commutes with the shift.**

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.ModuleComparison

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- The comparison for module-valued sections is the canonical map of the composite of
[Stacks, Tag 05T2]. -/
theorem moduleSectionsComparison_eq :
    moduleSectionsComparison X U =
      Stacks.DerivedIndexing.rightDerivedPlusCompTrans
        (SheafOfModules.evaluation (structureSheafRing X) (op U))
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}) :=
  rfl

/-- The comparison for the underlying abelian sheaves is the canonical map of the composite of
[Stacks, Tag 05T2]. -/
theorem abelianSectionsComparison_eq :
    abelianSectionsComparison X U =
      Stacks.DerivedIndexing.rightDerivedPlusCompTrans
        (SheafOfModules.toSheaf (structureSheafRing X))
        ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op U)) :=
  rfl

/-- The comparison for module-valued sections commutes with the shift. -/
instance natTransCommShift_moduleSectionsComparison :
    NatTrans.CommShift (moduleSectionsComparison X U) ℤ :=
  Stacks.DerivedIndexing.natTransCommShift_rightDerivedPlusCompTrans _ _

/-- The two composites `Γ(U, -) ∘ forget` and `Γ_{Ab}(U, -) ∘ toSheaf` are the same functor. -/
theorem evaluation_comp_forget_eq :
    (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
        forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}) =
      (SheafOfModules.toSheaf (structureSheafRing X) ⋙
        (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op U)) :=
  rfl

/-- The shift structures on the bounded below right derived functors of the two equal composites
`Γ(U, -) ∘ forget` and `Γ_{Ab}(U, -) ∘ toSheaf` agree. -/
theorem commShiftRightDerivedFunctorPlus_eq :
    Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
        (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
          forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u}) =
      Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
        (SheafOfModules.toSheaf (structureSheafRing X) ⋙
          (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op U)) :=
  rfl

/-- The comparison for the underlying abelian sheaves commutes with the shift. -/
instance natTransCommShift_abelianSectionsComparison :
    NatTrans.CommShift (abelianSectionsComparison X U) ℤ :=
  @Stacks.DerivedIndexing.natTransCommShift_rightDerivedPlusCompTrans _ _ _ _ _ _ _ _ _ _ _ _
    _ _ (SheafOfModules.toSheaf (structureSheafRing X))
    ((sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op U)) _ _

/-- **The comparison of Stacks 01F1 for bounded below complexes commutes with the shift.** -/
instance natTransCommShift_rightDerivedFunctorPlus_sections_forget_iso :
    NatTrans.CommShift (rightDerivedFunctorPlus_sections_forget_iso X U).hom ℤ := by
  have h₁ : NatTrans.CommShift (asIso (moduleSectionsComparison X U)).hom ℤ :=
    natTransCommShift_moduleSectionsComparison X U
  have h₂ : NatTrans.CommShift (asIso (moduleSectionsComparison X U)).symm.hom ℤ :=
    NatTrans.CommShift.of_iso_symm _ _
  have h₃ : NatTrans.CommShift (asIso (abelianSectionsComparison X U)).hom ℤ :=
    natTransCommShift_abelianSectionsComparison X U
  exact NatTrans.CommShift.comp _ _ _

end Stacks.Cohomology.ModuleComparison

end
