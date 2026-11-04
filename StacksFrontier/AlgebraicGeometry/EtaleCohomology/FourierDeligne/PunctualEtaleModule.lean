module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseOpenUnitIsoProof

/-!
# Punctual sheaves

A sheaf `P` of `Λ`-modules on `X_étale` is **punctual** when it vanishes on a nonempty open of
`X`. On a curve these are the sheaves supported on finitely many closed points, the sheaves which
the single-level argument for the irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) has to separate from the lisse ones.

Punctual sheaves are stable under subobjects and quotients, the inverse image to an open being
exact. A morphism from a punctual sheaf `P` to a sheaf `F` vanishes as soon as the unit
`F ⟶ j_* j⁻¹ F` is a monomorphism for the open `j` on which `P` vanishes: the composite with the
unit is adjoint to `j⁻¹ P ⟶ j⁻¹ F`, whose source is zero. On an integral normal scheme this
applies to every locally constant `F` (Tag 09Z5 (2),
`Stacks.EtaleCohomology.lisseOpenUnitIsoInput`).

## Main definitions

* `Stacks.EtaleCohomology.IsPunctualEtaleModule`.

## Main results

* `Stacks.EtaleCohomology.IsPunctualEtaleModule.of_mono`,
  `Stacks.EtaleCohomology.IsPunctualEtaleModule.of_epi`.
* `Stacks.EtaleCohomology.eq_zero_of_isZero_inverseImage_of_mono_unit`.
* `Stacks.EtaleCohomology.IsPunctualEtaleModule.eq_zero_of_isLocallyConstantWith`: no nonzero
  morphism from a punctual sheaf to a locally constant one on an integral normal scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasSheafify_over_etaleModules_locallyConstantSections

variable (Λ : Type) [Ring Λ] {X : Scheme.{u}}

/-- A sheaf of `Λ`-modules on `X_étale` is **punctual** when it vanishes on a nonempty open of
`X`. -/
def IsPunctualEtaleModule (P : EtaleModules.{u, 0} Λ X) : Prop :=
  ∃ (U : Scheme.{u}) (jU : U ⟶ X), IsOpenImmersion jU ∧ Nonempty U ∧
    IsZero ((etaleModuleInverseImage.{u, 0} Λ jU).obj P)

variable {Λ}

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits in
/-- **A subsheaf of a punctual sheaf is punctual.** -/
theorem IsPunctualEtaleModule.of_mono {P A : EtaleModules.{u, 0} Λ X} (ι : P ⟶ A) [Mono ι]
    (hA : IsPunctualEtaleModule Λ A) : IsPunctualEtaleModule Λ P := by
  obtain ⟨U, jU, h₁, h₂, h₃⟩ := hA
  exact ⟨U, jU, h₁, h₂, h₃.of_mono ((etaleModuleInverseImage.{u, 0} Λ jU).map ι)⟩

attribute [local instance] etaleModuleInverseImage_preservesFiniteColimits in
/-- **A quotient of a punctual sheaf is punctual.** -/
theorem IsPunctualEtaleModule.of_epi {A Q : EtaleModules.{u, 0} Λ X} (π : A ⟶ Q) [Epi π]
    (hA : IsPunctualEtaleModule Λ A) : IsPunctualEtaleModule Λ Q := by
  obtain ⟨U, jU, h₁, h₂, h₃⟩ := hA
  exact ⟨U, jU, h₁, h₂, h₃.of_epi ((etaleModuleInverseImage.{u, 0} Λ jU).map π)⟩

/-- **A morphism from a sheaf vanishing on an open `j` to a sheaf `F` with injective unit
`F ⟶ j_* j⁻¹ F` vanishes**: its composite with the unit is adjoint to a morphism out of
`j⁻¹ P = 0`. -/
theorem eq_zero_of_isZero_inverseImage_of_mono_unit {U : Scheme.{u}} (jU : U ⟶ X)
    {P F : EtaleModules.{u, 0} Λ X} (hP : IsZero ((etaleModuleInverseImage.{u, 0} Λ jU).obj P))
    [Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jU).unit.app F)] (f : P ⟶ F) : f = 0 := by
  refine (cancel_mono ((etaleModuleInverseImageAdj.{u, 0} Λ jU).unit.app F)).1 ?_
  refine ((etaleModuleInverseImageAdj.{u, 0} Λ jU).unit_naturality f).symm.trans ?_
  rw [hP.eq_of_src ((etaleModuleInverseImage.{u, 0} Λ jU).map f) 0, Functor.map_zero, comp_zero,
    zero_comp]

/-- **A morphism from a punctual sheaf to a locally constant sheaf on an integral normal scheme
vanishes**: the unit of the restriction to every nonempty open is an isomorphism there
(Tag 09Z5 (2)). -/
theorem IsPunctualEtaleModule.eq_zero_of_isLocallyConstantWith [IsIntegral X] [IsNormal X]
    {P F : EtaleModules.{u, 0} Λ X} (hP : IsPunctualEtaleModule Λ P)
    (Q : ModuleCat.{u + 1} Λ → Prop)
    (hF : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q F) (f : P ⟶ F) :
    f = 0 := by
  obtain ⟨U, jU, h₁, h₂, h₃⟩ := hP
  have := h₁
  have := h₂
  have hI := lisseOpenUnitIsoInput.{u} jU Λ Q F hF
  exact @eq_zero_of_isZero_inverseImage_of_mono_unit Λ _ X U jU P F h₃
    (@IsIso.mono_of_iso _ _ _ _ _ hI) f

end Stacks.EtaleCohomology

end
