module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantTwistBoundGenericRank
public import StacksFrontier.AlgebraicGeometry.Divisors.StalkSurjectiveOffDivisor

/-!
# The twist bound for a complex whose quotient lives on the divisor

[Stacks, Tag 0B3T] states its second assertion for a right-exact sequence whose last term is
the direct image of a module on an effective Cartier divisor `D`.  That shape is what supplies
the surjectivity hypotheses of
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_genericRank`: the stalk map of the
first arrow is surjective wherever the stalk of the last term vanishes, which is everywhere off
`D`, and in particular at the generic point of `X`.

## Main results

* `AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_exact_pushforward`: **the bounded
  Cartier twist for a complex with quotient supported on the divisor.**

## Implementation notes

What the statement still asks for is the data at the generic point of the prime divisor: that
the local ring there is a discrete valuation ring, that the stalks are finite, and the
identification `e` of the cokernel with `κ ^ s`.  Those are the hypotheses of
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap` that remain, so there is still no
`@[stacks]` attribute here.

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

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (S : ShortComplex X.Modules)
  (r s : ℕ) (U : X.Opens)
  [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.X₁.over U) r]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.X₂.over U) r]
  [(exteriorPower S.X₁ (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower S.X₁ (r : ℤ))).IsFinitePresentation]
  [(exteriorPower S.X₂ (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower S.X₂ (r : ℤ))).IsFinitePresentation]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
    (reflexiveHull (exteriorPower S.X₁ (r : ℤ)))]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
    (reflexiveHull (exteriorPower S.X₂ (r : ℤ)))]

/-- **The determinant line bundles of the first two terms of a complex whose last term lives on
an effective Cartier divisor differ by at most `min s r` copies of that divisor.**  Both
surjectivity hypotheses of
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_genericRank` come from the vanishing of
the stalks of the last term off the divisor. -/
theorem exists_pow_le_min_tensorIso_detMap_of_exact_pushforward (hS : S.Exact)
    (hU : ∃ x : X, x ∈ U)
    (D : X.IdealSheafData) (hDint : IsIntegral D.subscheme)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    {G : D.subscheme.Modules} (hquot : S.X₃ ≅ (Scheme.Modules.pushforward D.subschemeι).obj G)
    (Z : PrimeDivisor X) (hZ : Z.genericPoint ∈ ((D.support : Closeds X) : Set X))
    [IsDiscreteValuationRing (ringStalk X.sheaf Z.genericPoint)]
    [Module.Finite (ringStalk X.sheaf Z.genericPoint) (modStalk S.X₁ Z.genericPoint)]
    [Module.Finite (ringStalk X.sheaf Z.genericPoint) (modStalk S.X₂ Z.genericPoint)]
    (e : (modStalk S.X₂ Z.genericPoint ⧸ LinearMap.range (stalkHom S.f Z.genericPoint))
      ≃ₗ[ringStalk X.sheaf Z.genericPoint]
        (Fin s → IsLocalRing.ResidueField (ringStalk X.sheaf Z.genericPoint))) :
    ∃ k : ℕ, k ≤ min s r ∧ Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj
          ((reflexiveHull (exteriorPower S.X₁ (r : ℤ))))) ≅
      reflexiveHull (exteriorPower S.X₂ (r : ℤ))) :=
  exists_pow_le_min_tensorIso_detMap_of_genericRank S.f r s U hU D hDint hD Z hZ e
    (Scheme.Modules.surjective_stalkHom_of_notMem_supportSet hS hquot
      (genericPoint_notMem_supportSet_of_isEffectiveCartierDivisor hD))
    fun _x hx => Scheme.Modules.surjective_stalkHom_of_notMem_supportSet hS hquot hx

end AlgebraicGeometry

end
