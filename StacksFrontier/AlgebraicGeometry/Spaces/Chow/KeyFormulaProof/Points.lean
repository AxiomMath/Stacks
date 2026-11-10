module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection

/-!
# Generic points of prime divisors and of images of integral closed subspaces

Three point-set facts used in the assembly of the key formula, Stacks 0EQV:

* `AlgebraicGeometry.Space.PrimeDivisor.eq_of_genericPoint_eq`: a prime divisor of an algebraic
  space is determined by its generic point.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.pointsMap_eq_genericPoint_pushforward`: a closed
  immersion sends a generic point of an integral closed subspace to the generic point of its image.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.subspacePointSet_subset_of_genericPoint_mem`: an
  integral closed subspace lies in every closed set containing its generic point.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

include hX in
/-- **A prime divisor is determined by its generic point**: its points are the closure of the
generic point, and an integral closed subspace is determined by its points. -/
theorem PrimeDivisor.eq_of_genericPoint_eq {Z W : PrimeDivisor B S hS X}
    (h : Z.genericPoint B S hS X = W.genericPoint B S hS X) : Z = W := by
  have hZ := (Z.isGenericPoint_genericPoint B S hS X).def
  have hW := (W.isGenericPoint_genericPoint B S hS X).def
  have hsupp : Z.support B S hS X = W.support B S hS X := by
    rw [← hZ, ← hW, h]
  have hICS : (⟨Z.subspace, Z.closed, Z.integral⟩ : IntegralClosedSubspace B S hS X) =
      ⟨W.subspace, W.closed, W.integral⟩ :=
    injective_integralClosedSubspaceSupport B S hS hX (IrreducibleCloseds.ext (by exact hsupp))
  exact PrimeDivisor.eq_of_subspace_eq B S hS (congrArg IntegralClosedSubspace.subspace hICS)

/-- **A closed immersion sends a generic point of an integral closed subspace to the generic point
of its image.** -/
theorem IntegralClosedSubspace.pointsMap_eq_genericPoint_pushforward
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X} (hi : IsClosedImmersion B S hS i)
    (Z : IntegralClosedSubspace B S hS Y) (ξ : points B S hS Y)
    (hξ : IsGenericPoint ξ (subspacePointSet B S hS Y Z.subspace)) :
    pointsMap B S hS Y i ξ =
      pointsMap B S hS
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi Z).subspace.toFunctor
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi Z).subspace.ι
        ((IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi Z).genericPoint B S hS) := by
  refine eq_pointsMap_genericPoint_of_isGenericPoint B S hS hX _ _ ?_
  rw [IntegralClosedSubspace.subspacePointSet_pushforward]
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hX hi
  have e : ({pointsMap B S hS Y i ξ} : Set (points B S hS X)) = pointsMap B S hS Y i '' {ξ} :=
    Set.image_singleton.symm
  change closure _ = _
  rw [e, hemb.closure_image_eq, hξ.def]

include hX in
/-- **An integral closed subspace lies in every closed set containing its generic point.** -/
theorem IntegralClosedSubspace.subspacePointSet_subset_of_genericPoint_mem
    (Z : IntegralClosedSubspace B S hS X) {T : Set (points B S hS X)} (hT : IsClosed T)
    (h : pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι (Z.genericPoint B S hS) ∈ T) :
    subspacePointSet B S hS X Z.subspace ⊆ T := by
  rw [← (isGenericPoint_pointsMap_genericPoint B S hS hX Z).def]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) hT

end AlgebraicGeometry.Space

end
