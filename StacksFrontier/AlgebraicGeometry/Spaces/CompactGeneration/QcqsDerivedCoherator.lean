module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsCompactGeneration

/-!
# The derived coherator of a quasi-compact quasi-separated algebraic space

For a quasi-compact and quasi-separated algebraic space `X`, the inclusion
`D_QCoh(𝒪_X) ⟶ D(𝒪_X)` has a right adjoint `DQ_X`, which is exact (Stacks 0CR4). This is Brown
representability: `D_QCoh(𝒪_X)` has direct sums preserved by the inclusion (Stacks 08F3) and is
compactly generated (Stacks 09IY).

## Main results

* `AlgebraicGeometry.Space.exists_isTriangulated_rightAdjoint_ι_qcohDerived`
* `AlgebraicGeometry.Space.isLeftAdjoint_ι_qcohDerived`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- For a quasi-compact and quasi-separated algebraic space `X`, the inclusion
`D_QCoh(𝒪_X) ⟶ D(𝒪_X)` has a right adjoint `DQ_X`, with a shift structure making the
adjunction triangulated. -/
theorem exists_isTriangulated_rightAdjoint_ι_qcohDerived (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ (DQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
        QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
      (adj : (QcohDerived B S hS X).ι ⊣ DQ) (_ : DQ.CommShift ℤ), adj.IsTriangulated := by
  obtain ⟨G, hGc, hG⟩ := exists_isCompactObject_isWeakTriangulatedGenerator_of_qcqs B S hS hZ X
    hqc hqs
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  have := enoughInjectives_modules_ringUniverse B S hS X.1 X.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X.1 X.2
  have := fun I : Type u => isClosedUnderColimitsOfShape_qcohDerived B S hS X I
  have := hGc
  exact exists_isTriangulated_rightAdjoint_of_compact_generator _ G hG

/-- For a quasi-compact and quasi-separated algebraic space `X`, the inclusion
`D_QCoh(𝒪_X) ⟶ D(𝒪_X)` has a right adjoint. -/
theorem isLeftAdjoint_ι_qcohDerived (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    (QcohDerived B S hS X).ι.IsLeftAdjoint :=
  let ⟨_, adj, _, _⟩ := exists_isTriangulated_rightAdjoint_ι_qcohDerived hZ X hqc hqs
  adj.isLeftAdjoint

end AlgebraicGeometry.Space

end
