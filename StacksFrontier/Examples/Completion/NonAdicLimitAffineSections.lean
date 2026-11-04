module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.Examples.Completion.NonAdicLimitChart
public import StacksFrontier.RingTheory.MvPowerSeries.Noetherian
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The Noetherian hypotheses behind the affine sections of `ℱₙ`, Stacks 0EH8

Stacks 0EH8's "computation omitted" is the computation of `Γ(X, ℱₙ)` for `ℱₙ = 𝒪_X/Iⁿ𝒪_X` on
`X = Spec(A) ∖ V(𝔞)`, `A = k[x,y][[s,t]]/(xs − yt)`, and the shape of that computation is an
equalizer: `X` is the union of the two affine opens `D(x)` and `D(y)`, so the sheaf condition
presents `Γ(X, ℱₙ)` as the pairs of sections over the two charts agreeing over `D(xy)`. The two
chart *rings* are computed in `StacksFrontier/Examples/Completion/NonAdicLimitChart.lean`:
`Stacks.Examples.NonAdicLimit.chartTruncationEquivX` and `.chartTruncationEquivY`.

What stands between those two chart isomorphisms and the equalizer is the identification of the
sections of `ℱₙ` over an *affine* open `U` with the module quotient `𝒪_X(U) ⧸ Iⁿ·𝒪_X(U)`. That
identification is not new work either: it is
`Stacks.Algebraization.completionQuotientSectionsEquiv`, whose content is the quasi-coherence
computation of the affine sections of `Iⁿ𝒪_X`
(`Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine`). What it asks for, and what
this file supplies, are its two hypotheses about this example: that `X` is locally Noetherian,
and that `𝒪_X` is coherent on it, the latter packaging `𝒪_X` as an object of the coherent modules
that the completion functor is defined on.

Both reduce to `A` being Noetherian, which it is: `k[x,y]` is Noetherian by the Hilbert basis
theorem, `k[x,y][[s,t]]` is then Noetherian by its power series analogue
(`mvPowerSeries_fin_isNoetherianRing`, Stacks 0306), and `A` is a quotient of that.

## Main definitions

* `Stacks.Examples.NonAdicLimit.formalModuleCoherent` — `𝒪_X` as a coherent module, the shape
  `Stacks.Algebraization.completionFunctor` takes its argument in.

## Main results

* `Stacks.Examples.NonAdicLimit.isNoetherianRing_exampleRing` — `A` is Noetherian.
* `Stacks.Examples.NonAdicLimit.isLocallyNoetherian_puncturedSpectrum` — `X` is locally
  Noetherian, being an open subscheme of `Spec A`.
* `Stacks.Examples.NonAdicLimit.isCoherent_formalModule` — `𝒪_X` is coherent.

## Implementation notes

The completion functor indexes its system by `n ↦ 𝒪_X/Iⁿ⁺¹𝒪_X`, while
`Stacks.Algebraization.formalSections` — the system whose limit is this example's `M` — evaluates
`Stacks.Algebraization.adicQuotientSystem` at `n ↦ 𝒪_X/Iⁿ𝒪_X`. Identifying the two up to that
shift is what remains before `completionQuotientSectionsEquiv` can be read as a statement about
`Γ(U, ℱₙ)`, and it is a comparison of two towers, not a new computation: both terms are
`Stacks.Algebraization.idealPowerQuotient` of the same ideal-power subsheaf.
-/
@[expose] public noncomputable section

universe u

namespace Stacks.Examples.NonAdicLimit

open _root_.Stacks.AlgebraicGeometry CategoryTheory Opposite

variable (k : Type u) [Field k]

/-- **`k[x,y][[s,t]]` is Noetherian**, by the power series analogue of the Hilbert basis theorem
(Stacks 0306) over the Noetherian ring `k[x,y]`. -/
instance isNoetherianRing_ambient : IsNoetherianRing (ambient k) :=
  mvPowerSeries_fin_isNoetherianRing (MvPolynomial (Fin 2) k) 2

/-- **`A = k[x,y][[s,t]]/(xs − yt)` is Noetherian**, being a quotient of a Noetherian ring. -/
instance isNoetherianRing_exampleRing : IsNoetherianRing (exampleRing k) :=
  inferInstanceAs (IsNoetherianRing (ambient k ⧸ Ideal.span {relation k}))

/-- **`X = Spec(A) ∖ V(𝔞)` is locally Noetherian**, being an open subscheme of the spectrum of a
Noetherian ring. This is one of the two hypotheses of
`Stacks.Algebraization.completionQuotientSectionsEquiv`, which computes the sections of `ℱₙ`
over an affine open. -/
instance isLocallyNoetherian_puncturedSpectrum :
    AlgebraicGeometry.IsLocallyNoetherian (puncturedSpectrum k) :=
  inferInstance

/-- **`𝒪_X` is coherent** (Stacks 01XZ, `X` being locally Noetherian). This is the other
hypothesis of `Stacks.Algebraization.completionQuotientSectionsEquiv`: it is what makes
`Stacks.Examples.NonAdicLimit.formalModule` an object of the coherent modules on which the
completion functor is defined. -/
theorem isCoherent_formalModule : _root_.SheafOfModules.IsCoherent (formalModule k) :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent (puncturedSpectrum k)

/-- `𝒪_X` as an object of the coherent modules on `X`, which is the shape
`Stacks.Algebraization.completionFunctor` and
`Stacks.Algebraization.completionQuotientSectionsEquiv` take their argument in. -/
def formalModuleCoherent :
    AlgebraicGeometry.SheafOfModules.CoherentModules (puncturedSpectrum k).ringCatSheaf :=
  ⟨formalModule k, isCoherent_formalModule k⟩

end Stacks.Examples.NonAdicLimit

end
