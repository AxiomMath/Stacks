module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Coproduct
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Graded
public import StacksFrontier.AlgebraicGeometry.TopIdeals.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded pieces of the ideal-adic filtration

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals and `ℱ` a quasi-coherent
`𝒪_X`-module, filtered by the subsheaves `ℐᵖℱ`. The `p`-th graded piece of that filtration is
the quotient `ℐᵖℱ / ℐᵖ⁺¹ℱ`. It is the third term of a short exact sequence
`0 → ℐᵖ⁺¹ℱ → ℐᵖℱ → ℐᵖℱ/ℐᵖ⁺¹ℱ → 0`, it is coherent as soon as `ℱ` is and `X` is locally
Noetherian, and its support is contained in the support of `ℱ`.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealAdicFiltration.idealPowGradedShortComplex` is the short complex
  `ℐᵖ⁺¹ℱ → ℐᵖℱ → ℐᵖℱ/ℐᵖ⁺¹ℱ`.

## Main results

* `Stacks.AlgebraicGeometry.IdealAdicFiltration.idealPowGradedShortComplex_shortExact`: that
  short complex is short exact.
* `Stacks.AlgebraicGeometry.IdealAdicFiltration.isCoherent_idealPowGradedPiece`: the graded piece
  of a coherent module on a locally Noetherian scheme is coherent.
* `Stacks.AlgebraicGeometry.IdealAdicFiltration.supp_idealPowGradedPiece_subset`: the support of
  the graded piece is contained in the support of `ℱ`.

## Implementation notes

The graded piece is `cokernel (Stacks.AlgebraicGeometry.IrreducibleDevissage.idealPowStep I F p)`
and is given no abbreviation of its own, so that the annihilation of the graded piece by `ℐ(U)`
over every affine open `U`, which is
`IrreducibleDevissage.smul_top_cokernel_idealPowStep_of_isLocallyNoetherian` in the namespace
`Stacks.AlgebraicGeometry`, applies to the objects below as it stands. Together with
[Stacks, Tag 087T] that annihilation exhibits the graded piece as a direct image from the closed
subscheme cut out by `ℐ`, and [Stacks, Tag 01Y9] makes the filtration of a coherent module
supported in that subscheme finite; the two are what [Stacks, Tag 0FDT] combines with the short
exact sequence below.

Two subsheaves `ℐᵖℱ` of `ℱ` coexist in this repository,
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` and
`Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul`; they agree for quasi-coherent `ℱ` by
`Stacks.AlgebraicGeometry.IdealPowerComparison.idealPowerMultiple_eq_idealPowSmul`. The second
is used here, since it is the one whose sections over an affine open are computed, which is what
the annihilation statement needs.

## References

* [Stacks Project, Tag 0FDT](https://stacks.math.columbia.edu/tag/0FDT)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.IdealAdicFiltration

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)

/-- The short complex `ℐᵖ⁺¹ℱ → ℐᵖℱ → ℐᵖℱ/ℐᵖ⁺¹ℱ`: one step of the ideal-adic filtration followed
by the projection onto its cokernel. -/
@[sga "1 III 6.9"]
def idealPowGradedShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk (IrreducibleDevissage.idealPowStep I F p)
    (cokernel.π (IrreducibleDevissage.idealPowStep I F p)) (cokernel.condition _)

/-- **The graded piece of the ideal-adic filtration sits in a short exact sequence**
`0 → ℐᵖ⁺¹ℱ → ℐᵖℱ → ℐᵖℱ/ℐᵖ⁺¹ℱ → 0`. The inclusion of one step of the filtration into the
previous one is a monomorphism, and the projection onto its cokernel is an epimorphism
realising that cokernel. -/
theorem idealPowGradedShortComplex_shortExact :
    (idealPowGradedShortComplex I F p).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  · exact IrreducibleDevissage.mono_idealPowStep I F p
  · exact inferInstanceAs (Epi (cokernel.π (IrreducibleDevissage.idealPowStep I F p)))

/-- **The graded piece `ℐᵖℱ/ℐᵖ⁺¹ℱ` of a coherent module is coherent.** On a locally Noetherian
scheme both `ℐᵖ⁺¹ℱ` and `ℐᵖℱ` are coherent, and the cokernel of a morphism of coherent modules
is coherent by [Stacks, Tag 01BY]. -/
@[ega "IV 6.10.1" "partial"]
theorem isCoherent_idealPowGradedPiece [IsLocallyNoetherian X] [F.IsCoherent] :
    (cokernel (IrreducibleDevissage.idealPowStep I F p)).IsCoherent :=
  IrreducibleDevissage.isCoherent_cokernel' _
    (IdealPowerSmul.isCoherent_idealPowSmul I (p + 1) F)
    (IdealPowerSmul.isCoherent_idealPowSmul I p F)

/-- **The support of the graded piece `ℐᵖℱ/ℐᵖ⁺¹ℱ` is contained in the support of `ℱ`.** It is a
quotient of the subsheaf `ℐᵖℱ`, whose support is contained in that of `ℱ`. -/
theorem supp_idealPowGradedPiece_subset :
    SheafOfModules.supp (cokernel (IrreducibleDevissage.idealPowStep I F p)) ⊆
      SheafOfModules.supp F :=
  (IrreducibleDevissage.supp_cokernel_subset _).trans
    (Tag01YHTopIdeals.supp_subset_of_mono (IdealPowerSmul.idealPowSmulHom I p F)
      (inferInstanceAs (Mono (IdealPowerSmul.idealPowSmul I p F).ι)))

end Stacks.AlgebraicGeometry.IdealAdicFiltration

end
