module

public import StacksCore.RingTheory.Spectrum.Prime.Fiber
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Stacks 0H9M: the local ring of the fibre at a point

Let `R → S` be a ring map and `𝔮 ⊂ S` a prime lying over `𝔭 ⊂ R`. By Remark 00E6 the prime `𝔮`
corresponds to a unique prime `𝔮̄` of the fibre ring `F = S ⊗_R κ(𝔭)`; Mathlib's
`PrimeSpectrum.primesOverOrderIsoFiber` is that correspondence, and `Ideal.Fiber.primeOfLiesOver`
below reads off `𝔮̄`. Remark 0H9M says

  `F_𝔮̄ ≅ S_𝔮 ⊗_{R_𝔭} κ(𝔭) ≅ S_𝔮 / 𝔭 S_𝔮`.

The localisation `F_𝔮̄ ≅ S_𝔮 / 𝔭S_𝔮` is Mathlib's `Ideal.Fiber.algEquivAux₂`, stated there for a
prime of the fibre and the prime of `S` under it. The second isomorphism is base change along
`R_𝔭 → κ(𝔭) = R_𝔭 / 𝔭R_𝔭` (`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`). The
`R_𝔭`-algebra structure on `S_𝔮` is any one that is the canonical one, in the sense of Mathlib's
`Localization.AtPrime.IsLiesOverAlgebra`; `Localization.AtPrime.algebraOfLiesOver` provides it.
-/

@[expose] public section

open Algebra

namespace Ideal

section LocalRingFibre

open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver p]

/-- The prime `𝔮̄` of the fibre ring `κ(𝔭) ⊗_R S` corresponding to a prime `𝔮` of `S` lying over
`𝔭` (Stacks Remark 00E6), through Mathlib's `PrimeSpectrum.primesOverOrderIsoFiber`. -/
noncomputable def Fiber.primeOfLiesOver : Ideal (p.Fiber S) :=
  (PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨q, ‹q.IsPrime›, ‹q.LiesOver p›⟩).asIdeal

instance Fiber.isPrime_primeOfLiesOver : (Fiber.primeOfLiesOver p q).IsPrime :=
  PrimeSpectrum.isPrime _

/-- The prime `𝔮̄` of the fibre pulls back to `𝔮` along `S → κ(𝔭) ⊗_R S`. -/
theorem Fiber.comap_primeOfLiesOver :
    (Fiber.primeOfLiesOver p q).comap Algebra.TensorProduct.includeRight = q := by
  have := congrArg Subtype.val ((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply
    ⟨q, ‹q.IsPrime›, ‹q.LiesOver p›⟩)
  rwa [PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply] at this

/-- `F_Q ≃ S_𝔮 / 𝔭S_𝔮` for any prime `Q` of the fibre ring `F = κ(𝔭) ⊗_R S` whose pullback to
`S` is `𝔮`: Mathlib's `Ideal.Fiber.algEquivAux₂`, with the ideal `𝔭S_𝔮` extended directly
from `R`. -/
noncomputable def Fiber.localizationAlgEquivQuotientOfComapEq (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    (h : Q.comap Algebra.TensorProduct.includeRight = q) :
    Localization.AtPrime Q ≃ₐ[R]
      Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)) := by
  subst h
  exact (Fiber.algEquivAux₂ p Q).trans (Ideal.quotientEquivAlgOfEq R
    (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]))

/-- **Stacks 0H9M**, the composite isomorphism: for a prime `𝔮 ⊂ S` over `𝔭 ⊂ R` and the
corresponding prime `𝔮̄` of the fibre ring `F = κ(𝔭) ⊗_R S`, `F_𝔮̄ ≅ S_𝔮 / 𝔭 S_𝔮`. -/
@[stacks 0H9M "composite: F localised at the prime over 𝔮 is S_𝔮/𝔭S_𝔮, as R-algebras"]
noncomputable def Fiber.localizationPrimeOfLiesOverAlgEquivQuotient :
    Localization.AtPrime (Fiber.primeOfLiesOver p q) ≃ₐ[R]
      Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)) :=
  Fiber.localizationAlgEquivQuotientOfComapEq p q _ (Fiber.comap_primeOfLiesOver p q)

variable [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

/-- **Stacks 0H9M**, the second isomorphism: `S_𝔮 ⊗_{R_𝔭} κ(𝔭) ≅ S_𝔮 / 𝔭 S_𝔮`, because
`κ(𝔭) = R_𝔭 / 𝔭R_𝔭`. An isomorphism of `S_𝔮`-algebras. -/
@[stacks 0H9M "second isomorphism: S_𝔮 ⊗ κ(𝔭) over R_𝔭 is S_𝔮/𝔭S_𝔮, as S_𝔮-algebras"]
noncomputable def Fiber.localizationTensorResidueFieldAlgEquivQuotient :
    Localization.AtPrime q ⊗[Localization.AtPrime p] p.ResidueField ≃ₐ[Localization.AtPrime q]
      Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime q)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p))).symm.trans <|
    Ideal.quotientEquivAlgOfEq (Localization.AtPrime q) <| by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq]

/-- **Stacks 0H9M**, the first isomorphism: for a prime `𝔮 ⊂ S` over `𝔭 ⊂ R` and the
corresponding prime `𝔮̄` of the fibre ring `F = κ(𝔭) ⊗_R S`,
`F_𝔮̄ ≅ S_𝔮 ⊗_{R_𝔭} κ(𝔭)`. -/
@[stacks 0H9M "first isomorphism: F localised at the prime over 𝔮 is S_𝔮 ⊗ κ(𝔭) over R_𝔭"]
noncomputable def Fiber.localizationPrimeOfLiesOverRingEquivTensor :
    Localization.AtPrime (Fiber.primeOfLiesOver p q) ≃+*
      Localization.AtPrime q ⊗[Localization.AtPrime p] p.ResidueField :=
  (Fiber.localizationPrimeOfLiesOverAlgEquivQuotient p q).toRingEquiv.trans
    (Fiber.localizationTensorResidueFieldAlgEquivQuotient p q).symm.toRingEquiv

end LocalRingFibre

end Ideal
