module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemePower
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Basic

/-!
# The ideal sheaf of the zero scheme of a regular section is the inverse tensor power

Let `L` be an invertible `𝒪_X`-module on a scheme and let `t` be a regular global section of
`L^{⊗ n}`. The defining ideal sheaf of the zero scheme `Z(t)` is then isomorphic to
`L^{⊗ -n}`.

This is the sheaf appearing on the left of the canonical sequence

`0 ⟶ L^{⊗ -n} ⟶ 𝒪_X ⟶ 𝒪_{Z(t)} ⟶ 0`

that the Enriques–Severi–Zariski connectedness theorem [Stacks, Tag 0FD9] runs the long exact
cohomology sequence on: the sequence itself is
`Stacks.IdealSheafSequence.divisorIdeal_shortExact` with the ideal sheaf as its first term, and
what this file supplies is the identification of that first term as a negative twist, so that
the vanishing theorems [Stacks, Tag 0FD7] and [Stacks, Tag 0FD8] apply to it.

## Main results

* `Stacks.AmpleSectionConnected.dualIsoTensorPowerNegOne`: `L^∨ ≅ L^{⊗ -1}` for an arbitrary
  invertible module. This is [Stacks, Tag 01WX (1)] freed of its effective-Cartier hypothesis.
* `Stacks.AmpleSectionConnected.tensorPowerNegIso`: `L^{⊗ -n} ≅ (L^{⊗ n})^{⊗ -1}`.
* `Stacks.AmpleSectionConnected.idealSheafIsoTensorPowerNeg`: the identification above.

## Implementation notes

The first two isomorphisms are instances of one construction,
`Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne`: a module whose tensor product with an
invertible `L` is the structure sheaf *is* `L^{⊗ -1}`. The two inputs are, respectively, the
evaluation pairing of the dual (`Stacks.SheafOfModules.evaluationIsoOfIsInvertible`) and the
canonical multiplication `L^{⊗ -n} ⊗ L^{⊗ n} ≅ L^{⊗ 0}` of [Stacks, Tag 01CU]
(`Stacks.SheafOfModules.Invertible.TensorPowerCoherence.mulIso`). The third is their composite
with the isomorphism `L^∨ ≅ ℐ_{Z(t)}` of `AlgebraicGeometry.isIso_zeroSchemeIdealHom`.

**Two invertibility predicates and two spellings of the structure sheaf of rings.** The
evaluation pairing is stated for `Stacks.SheafOfModules.IsInvertible` while the tensor powers,
the zero scheme and the ideal-sheaf isomorphism are stated for
`AlgebraicGeometry.SheafOfModules.IsInvertible`; the two agree
(`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry`) but instance search is syntactic, so
the transport is made by hand with `letI`. Likewise the hypothesis is taken in the
`X.toRingedSpace.presheaf` spelling, because that is the one the tensor-power instances of
`StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemePower.lean` are stated in, and
`AlgebraicGeometry.isInvertible_sheafObj_of_isInvertible_toRingedSpace` carries it to the
`X.sheaf.obj` spelling that `AlgebraicGeometry.zeroScheme` asks for.

The library carries two duals of a sheaf of modules, `Stacks.SheafOfModules.dualSheaf` over a
presheaf of rings together with a sheaf condition and
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf` over a scheme. On a scheme they are the
same object, equal by `rfl` — the equation is
`AlgebraicGeometry.VectorBundleKZero.dualSheaf_eq_dualSheafRingedSpace` and is not restated
here — which is what lets the evaluation pairing, stated for the first, feed the ideal-sheaf
isomorphism, stated for the second.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AmpleSectionConnected

variable {X : Scheme.{u}}

variable (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- **The dual of an invertible module is its inverse tensor power.** The evaluation pairing
`L^∨ ⊗ L ≅ 𝒪_X` exhibits `L^∨` as the inverse of `L`, and `L^{⊗ -1}` is that inverse. -/
def dualIsoTensorPowerNegOne :
    Stacks.SheafOfModules.dualSheaf X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L ≅
      tensorPowerModule' L (-1) := by
  letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  exact isoTensorPowerNegOne _ _ L _ (Stacks.SheafOfModules.evaluationIsoOfIsInvertible L)

/-- **`L^{⊗ -n}` is the inverse of `L^{⊗ n}`.** The canonical multiplication of
[Stacks, Tag 01CU] gives `L^{⊗ -n} ⊗ L^{⊗ n} ≅ L^{⊗ 0} = 𝒪_X`, and the inverse of an
invertible module is its `(-1)`st tensor power. -/
def tensorPowerNegIso (n : ℤ) :
    tensorPowerModule' L (-n) ≅ tensorPowerModule' (tensorPowerModule' L n) (-1) :=
  isoTensorPowerNegOne _ _ _ _
    ((tensorPowerCoherence X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L).mulIso (-n) n ≪≫
      tensorPowerReindex X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L
          (show -n + n = 0 by ring) ≪≫
        eqToIso (tensorPower_zero X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L))

/-- **The defining ideal of the zero scheme of a regular section of `L^{⊗ n}` is `L^{⊗ -n}`.**

`AlgebraicGeometry.isIso_zeroSchemeIdealHom` identifies the ideal sheaf with the dual of
`L^{⊗ n}`; `dualIsoTensorPowerNegOne` turns that dual into `(L^{⊗ n})^{⊗ -1}`; and
`tensorPowerNegIso` turns that into `L^{⊗ -n}`. -/
def idealSheafIsoTensorPowerNeg (n : ℕ)
    (t : (tensorPowerModule' L (n : ℤ)).sections)
    (ht : AlgebraicGeometry.IsRegularSection X.sheaf.obj X.ringCatSheaf.property t) :
    Stacks.Divisors.idealSheafOfModules
        (zeroScheme X (tensorPowerModule' L (n : ℤ)) (t.eval (op ⊤))) ≅
      tensorPowerModule' L (-(n : ℤ)) :=
  have _ := AlgebraicGeometry.isIso_zeroSchemeIdealHom (tensorPowerModule' L (n : ℤ))
    (t.eval (op ⊤)) (AlgebraicGeometry.injective_smul_res_of_isRegularSection _ t ht)
  (asIso (AlgebraicGeometry.zeroSchemeIdealHom (tensorPowerModule' L (n : ℤ))
      (t.eval (op ⊤)))).symm ≪≫
    dualIsoTensorPowerNegOne (tensorPowerModule' L (n : ℤ)) ≪≫
      (tensorPowerNegIso L (n : ℤ)).symm

end Stacks.AmpleSectionConnected

end
