module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne

/-!
# The isomorphism locus at a codimension-one point with a discrete valuation local ring

Let `f : Y ⟶ X` be a proper birational morphism of schemes with `X` Noetherian and `Y` reduced,
and let `U ⊆ X` be the maximal open over which `f` is an isomorphism.  [Stacks, Tag 0BFP] lists
four kinds of point that `U` contains; item (2) is a point `x` of codimension one on `X` whose
local ring `𝒪_{X,x}` is a discrete valuation ring, and that is what is proved here.

## Main results

* `AlgebraicGeometry.residueField_isAlgebraic_of_isBirational`: a birational morphism induces an
  algebraic extension of residue fields at every generic point of its source.
* `AlgebraicGeometry.finite_preimage_singleton_of_isBirational_of_ringKrullDim_stalk_le_one`: a
  proper birational morphism has a finite fibre over every point whose local ring is Noetherian
  of dimension at most one.
* `AlgebraicGeometry.exists_isIso_restrict_of_isDiscreteValuationRing`: such a morphism, with
  reduced source, is an isomorphism over a neighbourhood of a point whose local ring is a
  discrete valuation ring.
* `AlgebraicGeometry.mem_maximal_isomorphism_open_of_isDiscreteValuationRing`:
  **[Stacks, Tag 0BFP] item (2)** — the maximal open over which `f` is an isomorphism contains
  every such point.

## Implementation notes

The source's hypothesis "`x` is of codimension one on `X`" is `dim 𝒪_{X,x} = 1`, which a discrete
valuation ring satisfies (`IsDiscreteValuationRing.ringKrullDim_eq_one`), so it is not carried as
a separate hypothesis.  `[IsDomain _]` appears because Mathlib's `IsDiscreteValuationRing` takes
it as an instance parameter.  "The maximal open where `f` is an isomorphism" is spelled
`IsGreatest { V : X.Opens | IsIso (f ∣_ V) } U`.

## References

* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0AB6](https://stacks.math.columbia.edu/tag/0AB6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry

universe u

/-! ### Codimension-one points whose local ring is a discrete valuation ring -/

/-- At a generic point of an irreducible component of its source, a birational morphism induces
an algebraic — indeed surjective — extension of residue fields. -/
public theorem residueField_isAlgebraic_of_isBirational
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : IsBirational f) (η : Y)
    (hη : η ∈ genericPoints Y) :
    letI := (f.residueFieldMap η).hom.toAlgebra
    Algebra.IsAlgebraic (X.residueField (f η)) (Y.residueField η) := by
  let _ := (f.residueFieldMap η).hom.toAlgebra
  have : IsIso (f.stalkMap η) := hf.isIso_stalkMap η hη
  have : IsIso (f.residueFieldMap η) :=
    ((IsLocalRing.ResidueField.mapEquiv
      (asIso (f.stalkMap η)).commRingCatIsoToRingEquiv).toCommRingCatIso).isIso_hom
  refine Algebra.isAlgebraic_iff_isIntegral.mpr (Algebra.isIntegral_of_surjective fun z ↦ ?_)
  obtain ⟨w, rfl⟩ := (asIso (f.residueFieldMap η)).commRingCatIsoToRingEquiv.surjective z
  exact ⟨w, rfl⟩

/-- **A proper birational morphism has a finite fibre over every point whose local ring is
Noetherian of dimension at most one.** -/
public theorem finite_preimage_singleton_of_isBirational_of_ringKrullDim_stalk_le_one
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f] (hf : IsBirational f) (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    (f ⁻¹' {x}).Finite := by
  refine (f.isCompact_preimage_singleton x).finite ?_
  rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
  rintro ⟨y, rfl⟩
  rw [← (f.fiberHomeo (f y)).symm.isOpen_image, Set.image_singleton]
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp
    (quasiFiniteAt_of_target_stalk_dimension_le_one f (f y) inferInstance hdim
      (Or.inl (residueField_isAlgebraic_of_isBirational f hf)) y rfl).2

/-- **A proper birational morphism with reduced source is an isomorphism over a neighbourhood of
every point whose local ring is a discrete valuation ring.** -/
public theorem exists_isIso_restrict_of_isDiscreteValuationRing
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f] [IsReduced Y]
    (hf : IsBirational f) (x : X) [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsIso (f ∣_ U) :=
  exists_isIso_restrict_of_finite_fiber_of_normal f hf x
    (finite_preimage_singleton_of_isBirational_of_ringKrullDim_stalk_le_one f hf x
      (IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk x)).le)

/-- Let `f : Y ⟶ X` be a proper birational morphism, where `X` is Noetherian and `Y` is reduced.
The maximal open over which `f` is an isomorphism contains every point whose local ring is a
discrete valuation ring. Such a point has codimension one on `X`, the dimension of a discrete
valuation ring being one. -/
@[stacks 0BFP "item (2): a codimension-one point whose local ring is a discrete valuation ring"]
public theorem mem_maximal_isomorphism_open_of_isDiscreteValuationRing
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f] [IsReduced Y]
    (hf : IsBirational f) (U : X.Opens)
    (hU : IsGreatest { V : X.Opens | IsIso (f ∣_ V) } U) (x : X)
    [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    x ∈ U :=
  mem_maximal_isomorphism_open_of_exists_isIso_restrict f U hU x
    (exists_isIso_restrict_of_isDiscreteValuationRing f hf x)

end AlgebraicGeometry

end
