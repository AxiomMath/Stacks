module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.RingTheory.Rig.FlatIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeLocalityRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined
import all StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatBaseChange

/-!
# Rig-flatness is stable under base change by a morphism locally of finite type: the refined forms

We show that a property of morphisms local on weakly admissible adic\* rings is local on
Noetherian adic rings, deduce that being adic and topologically of finite type is local on
Noetherian adic rings, and package the base change of rig-flatness by morphisms that are adic and
topologically of finite type together with the locality of both properties.

## Main results

* `TopologicalRing.propertyIsLocalNoetherian_of_adicStar'`: a property local on weakly admissible
  adic\* rings is local on Noetherian adic rings.
* `TopologicalRing.adicAndFiniteType_propertyIsLocalNoetherian'`: being adic and topologically of
  finite type is local on Noetherian adic rings.
* `AlgebraicGeometry.FormalSpace.rigFlat_isStableUnderBaseChangeByAdicFiniteType'`: rig-flatness
  is stable under base change by morphisms that are adic and topologically of finite type, given
  the base-change condition as a hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

/-- A property of morphisms which is local on the weakly admissible adic\* rings of **Stacks
0ANH** is local on the Noetherian adic rings of **Stacks 0ANI**: presentation independence and
the three locality axioms restrict all the rings involved to the ambient subcategory, and a
Noetherian adic ring has a finitely generated ideal of definition. -/
theorem propertyIsLocalNoetherian_of_adicStar'
    {P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop}
    (hP : TopologicalRing.AdicStarPropertyIsLocal'.{u} P) :
    TopologicalRing.PropertyIsLocalNoetherian'.{u} P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eB eA heB heBs heA heAs f hf hB hA hB'
      hA'
    refine hP.isomorphismInvariant eB eA heB heBs heA heAs f hf ?_ ?_ ?_ ?_ <;>
      exact exists_fg_isAdic_of_isAdic_and_isNoetherian ‹_›
  · repeat' intro
    refine hP.localizationPreserves ‹_› ?_ ?_ ?_ ?_ ‹_› <;>
      exact exists_fg_isAdic_of_isAdic_and_isNoetherian ‹_›
  · repeat' intro
    refine hP.faithfullyFlatDescent ‹_› ?_ ?_ ?_ ?_ ‹_› ‹_› <;>
      exact exists_fg_isAdic_of_isAdic_and_isNoetherian ‹_›
  · intro R _ _ _ _ hR hRcount ι _ A _ _ _ _ hA hAcount φ hφ hRmem hAmem hprop
    exact hP.finiteProduct hR hRcount A hA hAcount φ hφ
      (exists_fg_isAdic_of_isAdic_and_isNoetherian hRmem)
      (fun i ↦ exists_fg_isAdic_of_isAdic_and_isNoetherian (hAmem i)) hprop

/-- **Stacks 0GBW** read in the Noetherian subcategory of Stacks 0ANI: being adic and
topologically of finite type is a local property of morphisms of Noetherian adic topological
rings. -/
theorem adicAndFiniteType_propertyIsLocalNoetherian' :
    TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) :=
  propertyIsLocalNoetherian_of_adicStar' TopologicalRing.adicAndFiniteType_propertyIsLocal'

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

section BaseChangeHypothesis

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Stacks 0GGR packaged as the bundle `TopologicalRing.IsStableUnderBaseChangeBy'`, which
carries the locality of both properties as further fields. Both localities are proved: that of
rig-flatness is Stacks 0GGU and that of "adic and topologically of finite type" is Stacks 0GBW.
The base-change condition itself — all that Remark 0GBG defines and all that Stacks 0GGR
asserts — is the hypothesis `hbc`. -/
theorem rigFlat_isStableUnderBaseChangeByAdicFiniteType'
    (hbc : RigFlatBaseChangeByAdicFiniteType.{u}) :
    TopologicalRing.IsStableUnderBaseChangeBy'.{u}
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        Rig.RingHom.IsRigFlat φ)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) where
  isLocalP := Rig.rigFlat_isLocalNoetherian'
  isLocalQ := TopologicalRing.adicAndFiniteType_propertyIsLocalNoetherian'
  baseChange h₀ h₁ h₂ hc₁ hc₂ hP hQ := hbc h₀ h₁ h₂ hc₁ hc₂ hP hQ

end BaseChangeHypothesis

end AlgebraicGeometry.FormalSpace

end
