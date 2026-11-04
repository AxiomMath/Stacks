module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.Homology.DerivedCategory.Bridge.PushforwardUnitQ

/-!
# The splitting of [Stacks, Tag 0FUW] does not depend on the model

The canonical map `Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` of the blowing up is the class of the canonical map
of de Rham complexes followed by the comparison of the degreewise direct image with the derived
one. A retraction of it at the standard models of the derived categories gives one at any models:
the comparison equivalence of the models carries the one map to the other, up to isomorphism.

## Main results

* `Stacks.DeRham.BlowupTriangle.exists_retraction_toBlowUp_of_standard`: the transport.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage

universe u w

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.BlowupTriangle

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- **A retraction of `Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` at the standard models gives one at any models
of the derived categories.** -/
theorem exists_retraction_toBlowUp_of_standard
    [hX : HasDerivedCategory.{w} (ModuleSheaves (inverseImageBase f))]
    [hX' : HasDerivedCategory.{w} (ModuleSheaves (inverseImageBase (blowupMap i ≫ f)))]
    (h : letI := HasDerivedCategory.standard (ModuleSheaves (inverseImageBase f))
      letI := HasDerivedCategory.standard (ModuleSheaves (inverseImageBase (blowupMap i ≫ f)))
      ∃ r : blowUpDeRham f i ⟶ deRham f, toBlowUp f i ≫ r = 𝟙 _) :
    ∃ r : blowUpDeRham f i ⟶ deRham f, toBlowUp f i ≫ r = 𝟙 _ := by
  unfold toBlowUp at h ⊢
  simp only [Category.assoc] at h ⊢
  exact StacksDraft.DerivedModel.exists_retraction_unitQ_of_model (coefficientBlowup f i)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) hX' hX
    (chain (blowupMap i) f) h

end Stacks.DeRham.BlowupTriangle

end
