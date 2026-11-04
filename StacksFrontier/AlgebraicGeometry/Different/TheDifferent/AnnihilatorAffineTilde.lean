module

public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.AffineGlobalSections
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic

/-!
# The annihilator of the cokernel of a section of `ω_{Y/X}` on an affine source

The annihilator of the cokernel of `𝒪_Y → ω_{Y/X}` given by a global section is quasi-coherent,
so on an affine `Y` it is the sheaf of ideals attached to its ideal of global sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Discriminant

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f]

/-- The annihilator of the cokernel of the map `𝒪_Y → ω_{Y/X}` given by a global section is
quasi-coherent. -/
theorem isQuasicoherent_annihilatorSectionCokernel (ω : RelativeDualizingModuleData f)
    (s : Γ(ω.sheaf, ⊤)) :
    ((annihilatorSectionCokernel ω s).toSheafOfModules : Y.Modules).IsQuasicoherent := by
  have h : _root_.SheafOfModules.IsCoherent
      ((annihilatorSectionCokernel ω s).toSheafOfModules : Y.Modules) :=
    (_root_.SheafOfModules.isCoherent_iff _).mpr (isCoherent_annihilatorSectionCokernel ω s)
  exact (@Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent Y _ h).1

/-- On an affine `Y`, the annihilator of the cokernel of the map `𝒪_Y → ω_{Y/X}` given by a
global section is the sheaf of ideals attached to its ideal of global sections. -/
theorem annihilatorSectionCokernel_eq_unitSubmodule_ofIdealTop [IsAffine Y]
    (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤)) :
    annihilatorSectionCokernel ω s = (Scheme.IdealSheafData.ofIdealTop
      (show Ideal Γ(Y, ⊤) from
        (annihilatorSectionCokernel ω s).toSubmodule.obj (op ⊤))).unitSubmodule :=
  @Stacks.Divisors.eq_unitSubmodule_ofIdealTop Y _ (annihilatorSectionCokernel ω s)
    (isQuasicoherent_annihilatorSectionCokernel ω s)

end Stacks.Discriminant

end
