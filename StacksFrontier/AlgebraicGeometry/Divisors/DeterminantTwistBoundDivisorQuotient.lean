module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantTwistBoundCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorStalkResidueCokernel

/-!
# The bounded Cartier twist of [Stacks, Tag 0B3T]

In a right-exact sequence of coherent modules on an integral regular surface whose quotient is
the direct image of a finite locally free module of rank `s` on an integral effective Cartier
divisor, the determinant line bundles of the first two terms differ by at most `min s r`
copies of that divisor.

## Main results

* `AlgebraicGeometry.exists_reflexiveHull_exteriorPower_iso_tensor_cartier`: **the bounded
  Cartier twist**, the second clause of [Stacks, Tag 0B3T].

## Implementation notes

**The hypotheses are the source's own.** All the chain asks of `X` beyond integrality and
regularity of dimension at most two is `AlgebraicGeometry.IsLocallyNoetherian X`, which
regularity supplies. The twist exponent comes from
`AlgebraicGeometry.exists_pow_eq_of_supportSet_subset`, which reads the order of vanishing at
the single generic point of the divisor instead of choosing one divisor per irreducible
component of a closed subscheme as the general Tag 0AGB does, so the quasi-compactness such a
choice needs — and with it `AlgebraicGeometry.IsNoetherian X` — is never used.

The last hypothesis of
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_isEffectiveCartierDivisor`, the
identification of the cokernel of the stalk map at the generic point of the divisor with
`κ ^ s`, is discharged by
`AlgebraicGeometry.linearEquiv_quotient_range_stalkHom_fin`.

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

/-- **Stacks Project, Tag 0B3T.**  In a right-exact sequence of coherent modules of generic
rank `r` on an integral regular scheme of dimension at most two, whose quotient is the direct
image of a module of rank `s` finite locally free on an integral effective Cartier divisor
`D`, the determinant line bundles of the first two terms differ by at most `min s r` copies
of `D`.

The cokernel of the stalk map at the generic point of `D` is `κ ^ s` by
`AlgebraicGeometry.linearEquiv_quotient_range_stalkHom_fin`, which is the one hypothesis of
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_isEffectiveCartierDivisor` still
open.  Local Noetherianness, all the proof needs, comes from regularity. -/
@[stacks 0B3T "bounded Cartier twist"]
theorem exists_reflexiveHull_exteriorPower_iso_tensor_cartier (X : Scheme.{u})
    [IsIntegral X] (hX : AlgebraicGeometry.IsRegular X)
    (hXdim : topologicalKrullDim X ≤ 2)
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    [IsIntegral D.subscheme]
    (G : D.subscheme.Modules) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G s]
    (S : ShortComplex X.Modules) [S.X₁.IsCoherent] [S.X₂.IsCoherent]
    (hS : S.Exact) [Epi S.g]
    (hquot : S.X₃ ≅ (Scheme.Modules.pushforward D.subschemeι).obj G)
    (r : ℕ) (U : X.Opens) (hU : ∃ x : X, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.X₁.over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.X₂.over U) r] :
    ∃ k : ℕ, k ≤ min s r ∧ Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj
          ((reflexiveHull (exteriorPower S.X₁ (r : ℤ))))) ≅
      reflexiveHull (exteriorPower S.X₂ (r : ℤ))) := by
  obtain ⟨e⟩ := linearEquiv_quotient_range_stalkHom_fin hS s hquot
  exact exists_pow_le_min_tensorIso_detMap_of_isEffectiveCartierDivisor X hX hXdim D hD S hS
    hquot r s U hU e

end AlgebraicGeometry

end
