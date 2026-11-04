module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantTwistBoundExact
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DeterminantInvertible

/-!
# The twist bound on a regular surface, from coherence alone

On an integral regular scheme of dimension at most two the finiteness and invertibility
hypotheses of `AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_exact_pushforward` are
consequences of coherence of the two modules: the exterior powers and their duals are of finite
presentation, the reflexive hulls are line bundles by the first assertion of
[Stacks, Tag 0B3T], and the stalks are finite modules.

## Main results

* `AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_isCoherent`: **the bounded Cartier
  twist on a regular surface, from coherence and generic rank.**

## Implementation notes

What is still carried is the datum of the prime divisor `Z` on which the twist is measured —
that the local ring at its generic point is a discrete valuation ring, and the identification
`e` of the cokernel of the stalk map there with `κ ^ s`.  Those are the last hypotheses of
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap` not yet derived from the tag's own, so
there is still no `@[stacks]` attribute here.

No Noetherian hypothesis is assumed beyond what regularity gives: the colength argument behind
the twist bound asks only for `AlgebraicGeometry.IsLocallyNoetherian`, which is one of the
equivalent descriptions of regularity.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry

open Scheme.Modules Stacks.SheafOfModules

/-- **The determinant line bundles of the first two terms of a complex of coherent modules of
generic rank `r`, whose last term lives on an effective Cartier divisor, differ by at most
`min s r` copies of that divisor.** -/
theorem exists_pow_le_min_tensorIso_detMap_of_isCoherent (X : Scheme.{u}) [IsIntegral X]
    (hX : AlgebraicGeometry.IsRegular X) (hXdim : topologicalKrullDim X ≤ 2)
    (D : X.IdealSheafData) (hDint : IsIntegral D.subscheme)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    {G : D.subscheme.Modules} (S : ShortComplex X.Modules)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] (hS : S.Exact)
    (hquot : S.X₃ ≅ (Scheme.Modules.pushforward D.subschemeι).obj G)
    (r s : ℕ) (U : X.Opens) (hU : ∃ x : X, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.X₁.over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.X₂.over U) r]
    (Z : PrimeDivisor X) (hZ : Z.genericPoint ∈ ((D.support : Closeds X) : Set X))
    [IsLocalRing (ringStalk X.sheaf Z.genericPoint)]
    [IsDiscreteValuationRing (ringStalk X.sheaf Z.genericPoint)]
    (e : (modStalk S.X₂ Z.genericPoint ⧸ LinearMap.range (stalkHom S.f Z.genericPoint))
      ≃ₗ[ringStalk X.sheaf Z.genericPoint]
        (Fin s → IsLocalRing.ResidueField (ringStalk X.sheaf Z.genericPoint))) :
    ∃ k : ℕ, k ≤ min s r ∧ Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
          (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj
        ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj
        ((reflexiveHull (exteriorPower S.X₁ (r : ℤ))))) ≅
      reflexiveHull (exteriorPower S.X₂ (r : ℤ))) := by
  have : IsLocallyNoetherian X := (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).1
  have := isQuasicoherent_of_isCoherent S.X₁
  have := isQuasicoherent_of_isCoherent S.X₂
  have : (exteriorPower S.X₁ (r : ℤ)).IsFinitePresentation :=
    _root_.isFinitePresentation_of_isCoherent _
  have : (exteriorPower S.X₂ (r : ℤ)).IsFinitePresentation :=
    _root_.isFinitePresentation_of_isCoherent _
  have : (dualSheaf (exteriorPower S.X₁ (r : ℤ))).IsFinitePresentation :=
    isFinitePresentation_dualSheaf _
  have : (dualSheaf (exteriorPower S.X₂ (r : ℤ))).IsFinitePresentation :=
    isFinitePresentation_dualSheaf _
  have := isInvertible_reflexiveHull_exteriorPower_of_genericRank X hX hXdim S.X₁ r U hU
  have := isInvertible_reflexiveHull_exteriorPower_of_genericRank X hX hXdim S.X₂ r U hU
  have : Module.Finite (ringStalk X.sheaf Z.genericPoint) (modStalk S.X₁ Z.genericPoint) :=
    Scheme.Modules.finite_stalk_of_isCoherent S.X₁ Z.genericPoint
  have : Module.Finite (ringStalk X.sheaf Z.genericPoint) (modStalk S.X₂ Z.genericPoint) :=
    Scheme.Modules.finite_stalk_of_isCoherent S.X₂ Z.genericPoint
  exact exists_pow_le_min_tensorIso_detMap_of_exact_pushforward S r s U hS hU D hDint hD
    hquot Z hZ e

end AlgebraicGeometry

end
