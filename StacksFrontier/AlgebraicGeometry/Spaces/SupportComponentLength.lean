module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardModuleLength
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingGenericPointField
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthPointIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.Topology.Dimension.TopDimensionalComponents

/-!
# Lengths at the generic points of the components of a closed set of points

Let `X` be an algebraic space, let `T ⊆ |X|` be a closed set of points and let `C` be an
irreducible component of `T`, with a geometric point `x̄` lying over its generic point.  For an
`𝒪_X`-module `H` supported in `T` the length of `H` at `x̄` is the multiplicity with which `C`
occurs in `H`.  This file records the facts about these lengths that the numerical comparison of
Stacks 0EDE needs, for the modules met in a dévissage of a coherent module supported in `T`.

## Main results

* `AlgebraicGeometry.Space.geometricLength_eq_zero_of_image_notMem`: the length of a
  quasi-coherent module at a geometric point over a point off its support is zero.
* `AlgebraicGeometry.Space.geometricLength_pos_iff_image_mem`: and it is positive at a
  geometric point over a point of the support.
* `AlgebraicGeometry.Space.geometricLength_ne_top_of_isGenericPoint_component`: the length of a
  coherent module supported in `T` at a geometric point over the generic point of a component of
  `T` is finite.  If the generic point lies in the support, the component is a component of the
  support and Stacks 0EE4 applies; otherwise the length is zero.
* `AlgebraicGeometry.Space.toNat_geometricLength_add_of_shortExact`: these lengths, read as
  natural numbers, are additive along a short exact sequence of coherent modules whose middle
  term is supported in `T`.
* `AlgebraicGeometry.Space.geometricLength_modulePushforward_unit_eq_one`: the direct image of
  the structure sheaf of the reduced closed subspace on an irreducible closed set `W` has length
  one at every geometric point over the generic point of `W`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The length off the support is zero.**  At a geometric point over a point outside the
support of a quasi-coherent module the geometric stalk is trivial, by Stacks 07TZ, so its length
vanishes. -/
theorem geometricLength_eq_zero_of_image_notMem (H : Modules.{u, u} B S hS X.1 X.2)
    [H.IsQuasicoherentOnSite] (x : GeometricPoint B S hS X.1)
    (hx : x.image ∉ moduleSupportSet B S hS X H) : geometricLength B S hS X x H = 0 := by
  rw [geometricLength, Module.length_eq_zero_iff, ← not_nontrivial_iff_subsingleton]
  exact fun h => hx ((mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver
    B S hS X H x x.image rfl).2 h)

/-- **The length is positive exactly on the support.**  For a quasi-coherent module, a geometric
point lies over a point of the support exactly when the geometric stalk there is nontrivial, by
Stacks 07TZ, which is exactly when its length is positive. -/
theorem geometricLength_pos_iff_image_mem (H : Modules.{u, u} B S hS X.1 X.2)
    [H.IsQuasicoherentOnSite] (x : GeometricPoint B S hS X.1) :
    0 < geometricLength B S hS X x H ↔ x.image ∈ moduleSupportSet B S hS X H := by
  rw [geometricLength, Module.length_pos_iff]
  exact (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS X H x x.image
    rfl).symm

/-- **The length at the generic point of a component of `T` is finite** for a coherent module
supported in the closed set `T`, on a decent locally Noetherian algebraic space.

If the generic point lies off the support the length is zero.  If it lies on the support, the
component is a component of the support, which is a closed subset of `T`
(`preimage_mem_irreducibleComponents_of_isGenericPoint_mem`), and Stacks 0EE4
(`AlgebraicGeometry.Space.geometricLength_ne_top_and_pos_of_isGenericPoint_supportOfSheaf`)
gives finiteness. -/
theorem geometricLength_ne_top_of_isGenericPoint_component
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hdec : IsDecentSpace B S hS X.1) {T : Set (points B S hS X.1)}
    {C : Set T} (hC : C ∈ irreducibleComponents T) (x : GeometricPoint B S hS X.1)
    (hx : IsGenericPoint x.image (Subtype.val '' C))
    (H : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 H]
    (hHT : moduleSupportSet B S hS X H ⊆ T) : geometricLength B S hS X x H ≠ ⊤ := by
  by_cases hmem : x.image ∈ moduleSupportSet B S hS X H
  · have hScl : IsClosed (moduleSupportSet B S hS X H) :=
      isClosed_supportOfSheaf_of_isCoherentOnSite B S hS X H
    have hcomp := preimage_mem_irreducibleComponents_of_isGenericPoint_mem hC hx hScl hHT hmem
    refine (geometricLength_ne_top_and_pos_of_isGenericPoint_supportOfSheaf B S hS X hLN hdec H
      hmem ⟨_, hcomp⟩ ?_ x rfl).1
    rw [isGenericPoint_def,
      hScl.isClosedEmbedding_subtypeVal.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton, hx.def]
  · rw [geometricLength_eq_zero_of_image_notMem B S hS X H x hmem]
    exact ENat.zero_ne_top

/-- **Additivity of the lengths at the generic point of a component of `T`, as natural numbers**,
along a short exact sequence of coherent modules whose middle term is supported in `T`.  The
outer terms are supported in the support of the middle one, so all three lengths are finite
(`AlgebraicGeometry.Space.geometricLength_ne_top_of_isGenericPoint_component`), and on finite
values `ENat.toNat` is additive. -/
theorem toNat_geometricLength_add_of_shortExact
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hdec : IsDecentSpace B S hS X.1) {T : Set (points B S hS X.1)}
    {C : Set T} (hC : C ∈ irreducibleComponents T) (x : GeometricPoint B S hS X.1)
    (hx : IsGenericPoint x.image (Subtype.val '' C))
    (σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) (hσ : σ.ShortExact)
    [IsCoherent B S hS X.1 X.2 σ.X₁] [IsCoherent B S hS X.1 X.2 σ.X₂]
    [IsCoherent B S hS X.1 X.2 σ.X₃] (hT : moduleSupportSet B S hS X σ.X₂ ⊆ T) :
    (geometricLength B S hS X x σ.X₂).toNat =
      (geometricLength B S hS X x σ.X₁).toNat + (geometricLength B S hS X x σ.X₃).toNat := by
  have h₁ : moduleSupportSet B S hS X σ.X₁ ⊆ T :=
    (moduleSupportSet_subset_of_mono B S hS X σ.f hσ.mono_f).trans hT
  have h₃ : moduleSupportSet B S hS X σ.X₃ ⊆ T :=
    (moduleSupportSet_subset_of_epi B S hS X σ.g hσ.epi_g).trans hT
  rw [geometricLength_add_of_shortExact B S hS X x σ hσ,
    ENat.toNat_add (geometricLength_ne_top_of_isGenericPoint_component B S hS X hLN hdec hC x hx
      σ.X₁ h₁)
    (geometricLength_ne_top_of_isGenericPoint_component B S hS X hLN hdec hC x hx σ.X₃ h₃)]

/-- **The structure sheaf of an integral closed subspace has length one at its generic point.**
Let `Z ⊆ X` be an integral closed subspace and `x̄` a geometric point of `X` over the generic
point of `Z`.  Then `i_*𝒪_Z` has length one at `x̄`.

A geometric point `z̄` of `Z` over its generic point maps to a geometric point of `X` over the
same point as `x̄`, at which the length is the same by Stacks 0EE1
(`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`); there it is the length of `𝒪_Z` at
`z̄`, by Stacks 0EE3, and that is one because the étale local ring of an integral space at a
geometric generic point is a field. -/
theorem geometricLength_modulePushforward_unit_eq_one (Z : IntegralClosedSubspace B S hS X.1)
    (x : GeometricPoint B S hS X.1) (hx : x.image = Z.ambientGenericPoint B S hS) :
    geometricLength B S hS X x ((modulePushforward B S hS
      (closedSubfunctorι B S hS Z.isClosedSubspace)).obj (SheafOfModules.unit _)) = 1 := by
  obtain ⟨z, hz⟩ := exists_geometricRepresentative B S hS Z.subspace.toFunctor
    (Z.genericPoint B S hS)
  have : SheafOfModules.IsQuasicoherentOnSite (chartDirectImage B S hS
      (closedSubfunctorι B S hS Z.isClosedSubspace) Z.isClosedSubspace.2
      (SheafOfModules.unit _)) :=
    isQuasicoherentOnSite_closedSubspacePushforwardStructureSheaf B S hS X.2 Z.subspace
      Z.isClosedSubspace
  rw [geometricLength_eq_of_iso B S hS X x (modulePushforwardIsoChartDirectImage B S hS
      (closedSubfunctorι B S hS Z.isClosedSubspace) Z.isClosedSubspace.2 _),
    geometricLength_eq_of_image_eq B S hS X.2 x (geometricPointMap Z.subspace.ι z)
      (by rw [geometricPointMap_image, hz, hx]; rfl)]
  refine (geometricLength_closedSubspacePushforwardStructureSheaf B S hS X.2 Z.subspace
    Z.isClosedSubspace z).trans ?_
  refine geometricLength_structureSheafModule_eq_one_of_isIntegralSpace B S hS
    ⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ Z.isIntegralSpace z ?_
  rw [hz]
  let := Z.irreducibleSpace_points B S hS
  change closure {Z.genericPoint B S hS} ∈ irreducibleComponents _
  rw [Z.closure_singleton_genericPoint B S hS]
  exact ⟨IrreducibleSpace.isIrreducible_univ _, fun _ _ _ => Set.subset_univ _⟩

end AlgebraicGeometry.Space

end
