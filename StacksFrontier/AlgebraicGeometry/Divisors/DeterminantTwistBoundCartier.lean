module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantTwistBoundCoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierPrimeDivisor

/-!
# The twist bound measured on the divisor itself

An integral effective Cartier divisor is a prime divisor, and the local ring at its generic
point is a discrete valuation ring.  Feeding those to
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_isCoherent` leaves the identification
of the cokernel of the stalk map there with `κ ^ s` as the only hypothesis of
[Stacks, Tag 0B3T] not yet derived from the tag's own.

## Main results

* `AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_isEffectiveCartierDivisor`: **the
  bounded Cartier twist, with the prime divisor and its discrete valuation ring supplied.**

## Implementation notes

**No `@[stacks]` attribute.** The cokernel identification `e` is still a hypothesis here; on the
tag's own hypotheses it comes from finite local freeness of rank `s` of the module `G` on the
divisor, and that transport to the stalk of the direct image is in the library, as
`AlgebraicGeometry.linearEquiv_quotient_range_stalkHom_fin` of
`StacksFrontier/AlgebraicGeometry/Divisors/DivisorStalkResidueCokernel.lean`; the tag is carried,
with `e` discharged, by
`AlgebraicGeometry.exists_reflexiveHull_exteriorPower_iso_tensor_cartier` of
`StacksFrontier/AlgebraicGeometry/Divisors/DeterminantTwistBoundDivisorQuotient.lean`. An earlier
version of this paragraph said the library does not yet transport it; that is false.

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
generic rank `r`, whose last term lives on an integral effective Cartier divisor, differ by at
most `min s r` copies of that divisor.**  The prime divisor on which the twist is measured is
the divisor itself, and the discrete valuation ring at its generic point is Tag 0AG9. -/
theorem exists_pow_le_min_tensorIso_detMap_of_isEffectiveCartierDivisor (X : Scheme.{u})
    [IsIntegral X] (hX : AlgebraicGeometry.IsRegular X)
    (hXdim : topologicalKrullDim X ≤ 2)
    (D : X.IdealSheafData) [IsIntegral D.subscheme]
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    {G : D.subscheme.Modules} (S : ShortComplex X.Modules)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] (hS : S.Exact)
    (hquot : S.X₃ ≅ (Scheme.Modules.pushforward D.subschemeι).obj G)
    (r s : ℕ) (U : X.Opens) (hU : ∃ x : X, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.X₁.over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.X₂.over U) r]
    (e : (modStalk S.X₂ (D.subschemeι (_root_.genericPoint (D.subscheme : Type u))) ⧸
        LinearMap.range
          (stalkHom S.f (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))))
      ≃ₗ[ringStalk X.sheaf (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))]
        (Fin s → IsLocalRing.ResidueField (ringStalk X.sheaf
          (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))))) :
    ∃ k : ℕ, k ≤ min s r ∧ Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
          (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj
          ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj
          ((reflexiveHull (exteriorPower S.X₁ (r : ℤ))))) ≅
      reflexiveHull (exteriorPower S.X₂ (r : ℤ))) := by
  have : IsLocallyNoetherian X := (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).1
  obtain ⟨_, hdvr⟩ := isDiscreteValuationRing_ringStalk_genericPoint D hD
  have : IsDiscreteValuationRing
      (ringStalk X.sheaf (PrimeDivisor.ofEffectiveCartier D hD).genericPoint) := hdvr
  exact exists_pow_le_min_tensorIso_detMap_of_isCoherent X hX hXdim D inferInstance hD S hS
    hquot r s U hU (PrimeDivisor.ofEffectiveCartier D hD)
    (PrimeDivisor.genericPoint_ofEffectiveCartier_mem_support D hD) e

end AlgebraicGeometry

end
