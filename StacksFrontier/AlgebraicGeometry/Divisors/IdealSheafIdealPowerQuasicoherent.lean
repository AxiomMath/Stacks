module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient

/-!
# Quasi-coherence of the ideal multiples and quotients of an ideal sheaf

Let `X` be a scheme and let `I` and `E` be sheaves of ideals on `X`. This file registers, as
instances, the quasi-coherence of the subsheaf `I ⁿ ℐ_E` of the ideal sheaf `ℐ_E = 𝒪_X(-E)` of
the closed subscheme cut out by `E`, and of the quotient `ℐ_E / I ⁿ ℐ_E`.

## Main results

* `Stacks.Divisors.isQuasicoherent_idealPowerMultiple_negativeTwist` — the subsheaf
  `I ⁿ · 𝒪_X(-E)` is quasi-coherent.
* `Stacks.Divisors.isQuasicoherent_idealPowerQuotient_negativeTwist` — the quotient
  `𝒪_X(-E) / I ⁿ · 𝒪_X(-E)` is quasi-coherent.

Both hold for arbitrary sheaves of ideals `I` and `E` on an arbitrary scheme; neither needs `E`
to be an effective Cartier divisor.

## Implementation notes

**Every half of this is already proved; what is new is only that the halves meet.**
`Stacks.Algebraization.idealPowerMultiple_isQuasicoherent` is the quasi-coherence of `I ⁿ F` for
a quasi-coherent `F`; `Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf`
is the quasi-coherence of `ℐ_E` (Tag 01QO, clause (5)); and
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel` is the cokernel half of
Tag 01LB over an arbitrary scheme.

What the composite needs is a **spelling crossing**, the one recorded in the docstring of
`isQuasicoherent_kernel` in `StacksFrontier/AlgebraicGeometry/Meromorphic/IdealTimesModule.lean`.
`Stacks.Divisors.negativeTwist` lands in `SheafOfModules (structureSheafRing X.toRingedSpace)`,
while the module argument of `Stacks.Algebraization.idealPowerMultiple` is typed
`AlgebraicGeometry.Scheme.Modules`, which is a `def` for `SheafOfModules X.ringCatSheaf`. The two
indices are equal by `rfl` but not at the reducible transparency at which instances are matched,
so `infer_instance` closes neither statement below, nor the quasi-coherence side condition of
`idealPowerMultiple_isQuasicoherent` at this module — while an *explicit application* of the same
lemma, which elaborates at default transparency, closes all three. That is why each statement
below is a proof term rather than `by infer_instance`, and why the quasi-coherence of `ℐ_E` is
bound by hand at the `X.ringCatSheaf` index before it is used.

Nothing here carries a `@[stacks]` attribute: these are composites of tagged results, not
statements of the source.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- **The ideal-power multiple `I ⁿ ℐ_E` of the ideal sheaf of a closed subscheme is
quasi-coherent.**

`ℐ_E` is quasi-coherent by Tag 01QO, and an ideal-power multiple of a quasi-coherent module is
quasi-coherent; no hypothesis on `E` — effective Cartier or otherwise — is needed. The crossing
of the two spellings of the sheaf of rings is why the two halves are applied explicitly rather
than inferred; see the implementation notes of this file. -/
public instance isQuasicoherent_idealPowerMultiple_negativeTwist {X : Scheme.{u}}
    (I E : X.IdealSheafData) (n : ℕ) :
    (Stacks.Algebraization.idealPowerMultiple I n
      (negativeTwist E)).toSheafOfModules.IsQuasicoherent :=
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (negativeTwist E) :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf E.subschemeι
  Stacks.Algebraization.idealPowerMultiple_isQuasicoherent I n (negativeTwist E)

/-- **The quotient `ℐ_E / I ⁿ ℐ_E` of the ideal sheaf of a closed subscheme is quasi-coherent.**

It is the cokernel of the inclusion of `I ⁿ ℐ_E`, both ends of which are quasi-coherent, so the
cokernel half of Tag 01LB applies. Again no hypothesis on `E` is needed. -/
public instance isQuasicoherent_idealPowerQuotient_negativeTwist {X : Scheme.{u}}
    (I E : X.IdealSheafData) (n : ℕ) :
    (Stacks.Algebraization.idealPowerQuotient I n (negativeTwist E)).IsQuasicoherent :=
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (negativeTwist E) :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf E.subschemeι
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
    (Stacks.Algebraization.idealPowerMultiple I n (negativeTwist E)).ι

end Stacks.Divisors

end
