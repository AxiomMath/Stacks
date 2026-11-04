module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantGenericKernel
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantTwistBound

/-!
# The twist bound with its rank and determinant hypotheses discharged

`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap` takes four hypotheses that
[Stacks, Tag 0B3T] does not state and that its proof derives: the rank `hr`, `hr'` of the
torsion-free quotients of the two stalks at the generic point of the divisor, the
non-vanishing `hf` of the determinant comparison map, and its stalkwise surjectivity `hoff`
off the divisor. All four follow from what the tag *does* state — that `F` and `F'` are finite
locally free of the same rank `r` over a nonempty open — together with surjectivity of the
stalk map of `f` off the divisor, and that is what is assembled here.

What the statement still asks for is the data of the divisor: that the local ring at the
generic point of the prime divisor is a discrete valuation ring, that the stalks there are
finite, and the identification `e` of the cokernel with `κ ^ s`.

## Main results

* `AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_genericRank`: **the bounded Cartier
  twist, from the generic rank and surjectivity off the divisor.**

## Implementation notes

**Surjectivity at the generic point of `X` is a separate hypothesis from surjectivity off the
divisor**, even though the former follows from the latter: deducing it needs the generic point
of an integral scheme to lie off the support of an effective Cartier divisor, which is a fact
about `IdealSheafData.supportSet` that the library does not record. Carrying both keeps this
file free of that gap.

**No `@[stacks]` attribute.** The remaining hypotheses are exactly the ones
`StacksFrontier/AlgebraicGeometry/Divisors/DeterminantTwistBound.lean` records as not yet derived
from the tag's own hypotheses, so this is still a step of the proof rather than the assertion.

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

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {F F' : X.Modules} (f : F ⟶ F')
  (r s : ℕ) (U : X.Opens)
  [F.IsQuasicoherent] [F'.IsQuasicoherent]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F'.over U) r]
  [(exteriorPower F (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
  [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
    (reflexiveHull (exteriorPower F (r : ℤ)))]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
    (reflexiveHull (exteriorPower F' (r : ℤ)))]

/-- **The determinant line bundles of two modules of the same generic rank differ by at most
`min s r` copies of the divisor.** The rank hypotheses of
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap`, the non-vanishing of the determinant
comparison map and its stalkwise surjectivity off the divisor are all supplied from finite
local freeness of rank `r` over a nonempty open together with surjectivity of the stalk maps
of `f`. -/
theorem exists_pow_le_min_tensorIso_detMap_of_genericRank (hU : ∃ x : X, x ∈ U)
    (D : X.IdealSheafData) (hDint : IsIntegral D.subscheme)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (Z : PrimeDivisor X) (hZ : Z.genericPoint ∈ ((D.support : Closeds X) : Set X))
    [IsDiscreteValuationRing (ringStalk X.sheaf Z.genericPoint)]
    [Module.Finite (ringStalk X.sheaf Z.genericPoint) (modStalk F Z.genericPoint)]
    [Module.Finite (ringStalk X.sheaf Z.genericPoint) (modStalk F' Z.genericPoint)]
    (e : (modStalk F' Z.genericPoint ⧸ LinearMap.range (stalkHom f Z.genericPoint))
      ≃ₗ[ringStalk X.sheaf Z.genericPoint]
        (Fin s → IsLocalRing.ResidueField (ringStalk X.sheaf Z.genericPoint)))
    (hsurjη : Function.Surjective (stalkHom f (genericPoint X)))
    (hsurj : ∀ x : X, x ∉ D.supportSet → Function.Surjective (stalkHom f x)) :
    ∃ k : ℕ, k ≤ min s r ∧ Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj
          ((reflexiveHull (exteriorPower F (r : ℤ))))) ≅
      reflexiveHull (exteriorPower F' (r : ℤ))) :=
  exists_pow_le_min_tensorIso_detMap f r s D hDint hD Z hZ e
    (finrank_quotient_torsion_modStalk_eq_of_isFiniteLocallyFreeOfRank_over F U r hU
      Z.genericPoint)
    (finrank_quotient_torsion_modStalk_eq_of_isFiniteLocallyFreeOfRank_over F' U r hU
      Z.genericPoint)
    (detMap_ne_zero_of_surjective_stalkHom_genericPoint f r U hU hsurjη)
    (fun x hx ↦ surjective_mapFun_detMap_of_surjective_of_genericRank f r U hU hsurjη x
      (hsurj x hx))

end AlgebraicGeometry

end
