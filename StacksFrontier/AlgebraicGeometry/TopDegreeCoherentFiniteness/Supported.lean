module

public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.IdealSupport
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass

/-!
# Finiteness of cohomology for coherent modules supported in a closed subset

A dévissage ([Stacks, Tag 01YG]) restricted to the coherent modules supported in a closed subset
`T`: if `Hⁿ(X, i_* ℐ)` is finite-dimensional for every nonzero coherent ideal `ℐ` on an integral
closed subscheme `i : W ⟶ X` contained in `T`, then `Hⁿ(X, 𝒬)` is finite-dimensional for every
coherent `𝒬` supported in `T`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.TopDegree

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Supported dévissage.** -/
theorem finiteDimensional_of_supp_subset [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ)
    (T : Set X) (hTc : IsClosed T)
    (hW : ∀ {W : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
      (I : (SheafOfModules.unit W.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsCoherent → ¬ IsZero I.toSheafOfModules → Set.range i.base ⊆ T →
        FiniteDimensional k (cohomologyOverField k (i ≫ f) I.toSheafOfModules n))
    (Q : X.Modules) (hQ : _root_.SheafOfModules.IsCoherent Q)
    (hsupp : SheafOfModules.supp Q ⊆ T) :
    FiniteDimensional k (cohomologyOverField k f Q n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := (isNoetherian_iff X).2 ⟨inferInstance, inferInstance⟩
  refine Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent X
    (fun G ↦ SheafOfModules.supp G ⊆ T → FiniteDimensional k (cohomologyOverField k f G n))
    ?_ ?_ ?_ Q hQ hsupp
  · intro _
    exact finiteDimensional_of_isZero k
      (isZero_cohomologyOverField_of_isZero k f
        Stacks.AlgebraicGeometry.CoherentDevissage.isZero_terminal n)
  · intro S hS _ _ _ h₁ h₃ h₂
    have : Mono S.f := hS.mono_f
    have : Epi S.g := hS.epi_g
    exact finiteDimensional_cohomologyOverField_of_shortExact k f hS n
      (h₁ ((Stacks.Chow.supp_subset_of_mono S.f).trans h₂))
      (h₃ ((Stacks.Chow.supp_subset_of_epi S.g).trans h₂))
  · intro Z i _ _ I hI hsuppI
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    have hIcoh : I.toSheafOfModules.IsCoherent :=
      @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono Z inferInstance
        (SheafOfModules.unit Z.ringCatSheaf) I.toSheafOfModules
        (Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z) inferInstance
        I.ι (SheafOfModules.Submodule.instMonoι I)
    by_cases hz : IsZero I.toSheafOfModules
    · exact finiteDimensional_of_isZero k
        (isZero_cohomologyOverField_of_isZero k f
          ((Scheme.Modules.pushforward i).map_isZero hz) n)
    · have hrange : Set.range i.base ⊆ T :=
        range_subset_of_supp_pushforward_ideal_subset i I hz T hTc hsuppI
      exact finiteDimensional_cohomologyOverField_pushforward_of_isClosedImmersion k i f
        I.toSheafOfModules n (hW i I hIcoh hz hrange)

end AlgebraicGeometry.TopDegree

end
