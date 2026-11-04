module

public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula

/-!
# Base change of the inverse of an invertible quotient line, unconditionally

`StacksFrontier/AlgebraicGeometry/InvertibleQuotient/Basic.lean` builds Tag 0B3V's comparison
`g^*(L^{⊗ -1}) ≅ (g^*L)^{⊗ -1}` as `Stacks.Divisors.inverseQuotientBaseChangeIso`, taking as a
hypothesis the trivializing pairing `g^*(L^{⊗ -1}) ⊗ g^*L ≅ 𝒪_{X'}` — which is Tag 01CD at the
one pair `(L^{⊗ -1}, L)`. That tag is now available outright
(`Stacks.RingedSpace.isIso_comparison`), so the pairing is a theorem and the comparison needs
no hypothesis.

## Main results

* `Stacks.Divisors.inverseQuotientBaseChangePairing`: the pairing
  `g^*(L^{⊗ -1}) ⊗_{𝒪_{X'}} g^*L ≅ 𝒪_{X'}`, for any invertible `L` on `X` and any morphism of
  schemes `g : X' ⟶ X`. It is the pullback, by `Stacks.RingedSpace.tensorIsoUnitPullback`, of
  the canonical trivialization `Stacks.SheafOfModules.Invertible.tensorPowerSuccIso` in degree
  `-1`.
* `Stacks.Divisors.inverseQuotientBaseChange`: Tag 0B3V's inverse-line comparison for a pair of
  invertible quotients with `Q'.L ≅ g^* Q.L`, with no hypothesis beyond that identification.
  `Stacks.Divisors.inverseQuotientBaseChange_eq` records that it is
  `inverseQuotientBaseChangeIso` at that pairing, so
  `Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne_hom_tensor` still pins it down.

## Implementation notes

Three spellings of one object meet here and all three coincide by `rfl`, which is why nothing
has to be transported:

* `X.ringCatSheaf = structureSheafRing X.toRingedSpace`;
* `AlgebraicGeometry.Scheme.Modules.pullback g =
  RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom`, both being
  `SheafOfModules.pullback` of the same morphism of sheaves of rings;
* `Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.presheaf X.ringCatSheaf.2 A B =
  (Stacks.RingedSpace.tensorSheaf X.toRingedSpace).obj (A, B)`.

So the invertible-quotient vocabulary, which is stated in the `Scheme.Modules` model, consumes
Tag 01CD as proved in the `RingedSpaceModuleAdjunction` model with no bridge.

`tensorPower O hO L 0` is `SheafOfModules.unit _` by `rfl`
(`Stacks.SheafOfModules.Invertible.tensorPower_zero`), so `tensorPowerSuccIso` in degree `-1`
already has the shape of a trivializing pairing.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (IsInvertible)
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Divisors

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- **The inverse of an invertible module sheaf pairs trivially with it after pullback.**

The canonical trivialization `L^{⊗ -1} ⊗_{𝒪_X} L ≅ 𝒪_X` of
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso` in degree `-1` is pulled back along `g`
by `Stacks.RingedSpace.tensorIsoUnitPullback`, whose Tag 01CD input is
`Stacks.RingedSpace.isIso_comparison`.

This is the hypothesis `hpair` of `Stacks.Divisors.inverseQuotientBaseChangeIso`. -/
noncomputable def inverseQuotientBaseChangePairing
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
      X.ringCatSheaf.2))
    [IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X'.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X'.presheaf) (forget₂ CommRingCat RingCat)
          (X'.ringCatSheaf.2)⟩).obj (((Scheme.Modules.pullback g).obj
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1))))).obj
          (((Scheme.Modules.pullback g).obj L))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf X'.presheaf
        X'.ringCatSheaf.2) :=
  Stacks.RingedSpace.tensorIsoUnitPullback g.toLRSHom.toShHom
    (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L
    (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L (-1))
    (Stacks.RingedSpace.isIso_comparison _ _ _)

/-- **Tag 0B3V's inverse-line comparison, with no hypothesis beyond the identification of the
quotient lines**: for invertible quotients `Q` of `E` on `X` and `Q'` of `E'` on `X'` with
`Q'.L ≅ g^* Q.L`, the pullback of `Q.L^{⊗ -1}` is `Q'.L^{⊗ -1}`.

This is `Stacks.Divisors.inverseQuotientBaseChangeIso` with its Tag 01CD hypothesis discharged
by `inverseQuotientBaseChangePairing`. -/
noncomputable def inverseQuotientBaseChange
    (E : X.Modules) (E' : X'.Modules)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L) :
    (Scheme.Modules.pullback g).obj
      (letI := Q.invertible
       Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) ≅
      (letI := Q'.invertible
       Stacks.SheafOfModules.Invertible.tensorPower X'.presheaf X'.ringCatSheaf.2 Q'.L (-1)) :=
  letI := Q.invertible
  inverseQuotientBaseChangeIso g E E' Q Q' hL (inverseQuotientBaseChangePairing g Q.L)

/-- `inverseQuotientBaseChange` is `inverseQuotientBaseChangeIso` applied to the pairing
`inverseQuotientBaseChangePairing g Q.L`. -/
lemma inverseQuotientBaseChange_eq
    (E : X.Modules) (E' : X'.Modules)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L) :
    inverseQuotientBaseChange g E E' Q Q' hL =
      letI := Q.invertible
      inverseQuotientBaseChangeIso g E E' Q Q' hL
        (inverseQuotientBaseChangePairing g Q.L) := rfl

end Stacks.Divisors

end
