module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.RingTheory.KrullDimension.GoingUpGoingDown
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksCore.Tactic.StacksAttribute

/-!
# Dimension under an integral morphism

An integral morphism of schemes cannot increase dimension from its target to its source. If the
morphism is also surjective, the source and target have the same dimension.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom` gives the dimension inequality for
  an integral morphism.
* `AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective` gives equality for a
  surjective integral morphism.

## Implementation notes

Dimension is expressed by `topologicalKrullDim`, and integrality and surjectivity by Mathlib's
morphism typeclasses `AlgebraicGeometry.IsIntegralHom` and `AlgebraicGeometry.Surjective`.

## References

* [Stacks Project, Tag 0ECG](https://stacks.math.columbia.edu/tag/0ECG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The dimension of an affine open equals the Krull dimension of its ring of sections. -/
private lemma topologicalKrullDim_affineOpen_eq_ringKrullDim {X : Scheme.{u}}
    (U : X.Opens) (hU : IsAffineOpen U) :
    topologicalKrullDim (↥U) = ringKrullDim Γ(X, U) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph

/-- The dimension of the source of an integral morphism is at most the dimension of its target. -/
@[stacks 0ECG "dimension inequality", ega "0 16.1.5" "dim(B) ≤ dim(A)"]
lemma topologicalKrullDim_le_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let V : X.Opens := f ⁻¹ᵁ U
  calc
    TopologicalSpace.localKrullDim X x ≤ topologicalKrullDim (↥V) :=
      iInf_le_of_le V (iInf_le_of_le V.2 (iInf_le _ hxU))
    _ ≤ topologicalKrullDim (↥U) := by
      rw [topologicalKrullDim_affineOpen_eq_ringKrullDim V (hU.preimage f),
        topologicalKrullDim_affineOpen_eq_ringKrullDim U hU]
      exact (integral_dim_up (f.app U).hom (f.isIntegral_app U hU)).1
    _ ≤ topologicalKrullDim Y := topologicalKrullDim_subspace_le Y U

/-- A surjective integral morphism has source and target of the same dimension. -/
@[stacks 0ECG "surjective case", ega "0 16.1.5" "equality case"]
lemma topologicalKrullDim_eq_of_isIntegralHom_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [Surjective f] :
    topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm (topologicalKrullDim_le_of_isIntegralHom f)
    (Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
      (f : X → Y) f.continuous ((surjective_iff f).mp inferInstance)
      (Or.inl f.isClosedMap.specializingMap))

end AlgebraicGeometry
