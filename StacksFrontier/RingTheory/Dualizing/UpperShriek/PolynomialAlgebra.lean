module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingDiagonal

/-!
# The relative dualizing complex of a polynomial algebra

For a ring `R` and `P = R[x_1, …, x_n]`, the relative dualizing complex of `R → P` read at the
tautological presentation of `P` (the identity of `P`, in `n` variables) is `P[n]`:
`ω^•_{P/R} = RHom_P(P, R ⊗_R^L P)[n] = P[n]`. This is the algebraic form of
`p^! 𝒪_Y = 𝒪_{𝐀^n_Y}[n]`.

## Main definitions

* `Dualizing.PolynomialPresentation.mvPolynomial`: the tautological presentation of
  `R → R[x_1, …, x_n]`.

## Main results

* `Dualizing.PolynomialPresentation.mvPolynomialUpperShriekUnitIso`: `ω^•_{P/R} ≅ P[n]`.

## References

* [Stacks Project, Tag 0BV8](https://stacks.math.columbia.edu/tag/0BV8)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing.PolynomialPresentation

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The tautological presentation of `R → R[x_1, …, x_n]`: the polynomial algebra itself, in its
`n` variables, with the identity as surjection. -/
def mvPolynomial :
    PolynomialPresentation (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) where
  variableCount := n
  toRingHom := RingHom.id _
  commutes := rfl
  surjective := Function.surjective_id

/-- **The relative dualizing complex of a polynomial algebra is the algebra shifted by the number
of variables**: `ω^•_{P/R} = RHom_P(P, R ⊗_R^L P)[n] ≅ P[n]` for `P = R[x_1, …, x_n]`, read at
the tautological presentation. -/
def mvPolynomialUpperShriekUnitIso :
    (mvPolynomial R n).upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
        (ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R)))⟦(n : ℤ)⟧ :=
  (shiftFunctor (DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin n) R))) (n : ℤ)).mapIso
    ((DiagonalCondition.derivedHomIdIso (MvPolynomial (Fin n) R)).app _ ≪≫
      (mvPolynomial R n).derivedExtension.{u, 0}.mapIso
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
          (ULift.moduleEquiv : ULift.{0} R ≃ₗ[R] R).toModuleIso.symm) ≪≫
      (mvPolynomial R n).derivedExtensionTensorUnitIso.{u, 0} ≪≫
      derivedTensorUnitIsoSingle.{u, 0} (MvPolynomial (Fin n) R) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).mapIso
        (ULift.moduleEquiv : ULift.{u} (MvPolynomial (Fin n) R) ≃ₗ[MvPolynomial (Fin n) R]
          MvPolynomial (Fin n) R).toModuleIso)

end Dualizing.PolynomialPresentation

end
