module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafIdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete

/-!
# Quasi-coherence of the graded piece of an ideal sheaf along a closed subscheme

Let `X` be a scheme, let `D` and `E` be sheaves of ideals on `X`, and let `i : D.subscheme ⟶ X`
be the closed immersion `D` cuts out. This file registers, as an instance, the quasi-coherence of

`i_* i^* 𝒪_X(-E)`,

the sheaf whose global sections are the graded piece of the filtration of `𝒪_X` by the powers of
`D` in the sequence of [Stacks, Tag 0C4T].

## Main results

* `Stacks.Divisors.isQuasicoherent_pushforward_pullback_negativeTwist` — `i_* i^* 𝒪_X(-E)` is
  quasi-coherent, for arbitrary sheaves of ideals `D` and `E` on an arbitrary scheme.

## Implementation notes

**This corrects a recorded blocker.** The implementation notes of
`StacksFrontier/AlgebraicGeometry/Divisors/EffectiveCartier/SumSequenceMultiplication.lean` state
that the statement of the one-step multiplicativity law covering *arbitrary* sections of the
graded piece — as opposed to the local pure tensors that
`Stacks.Divisors.app_idealTensorMul_comp_unit_comp_thickeningKernelMap_tmul` covers — needs the
surjectivity of the unit of `i^* ⊣ i_*` over an affine open, that all three statements supplying
that surjectivity ask for `SheafOfModules.IsQuasicoherent` of the module they are applied to, and
that for this module, the *target* end of the unit, the instance

> is **not** derivable, with or without an affine ambient scheme.

That is false, and the two ingredients that refute it are named in the same paragraph. Tag 0EL1,
`Stacks.Algebraization.idealQuotientPushforwardIso`, identifies `i_* i^* F` with the quotient
`F / I ⁿ F` whenever `i` has ideal sheaf `I ⁿ` and `F` is quasi-coherent; and the quotient at
`F = 𝒪_X(-E)` is quasi-coherent by
`Stacks.Divisors.isQuasicoherent_idealPowerQuotient_negativeTwist`, the neighbouring instance in
this directory. Transporting the second along the first gives the target end outright, with no
hypothesis on either `D` or `E` and no affineness assumption. The ideal sheaf of `i` is `D`
itself, which is `D ^ 1` — the shape Tag 0EL1 asks for — by
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι` and `pow_one`.

The quasi-coherence of the *source* end `𝒪_X(-E)` is bound by hand at the `X.ringCatSheaf` index,
for the reason set out at length in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Divisors/IdealSheafIdealPowerQuasicoherent.lean`: `negativeTwist`
lands at the `structureSheafRing X.toRingedSpace` spelling of the sheaf of rings, the two indices
are equal by `rfl` but not at the transparency instances are matched at, so the statement is a
proof term and the halves are applied explicitly rather than inferred.

Nothing here carries a `@[stacks]` attribute: this is a composite of tagged results — Tag 0EL1
and the cokernel half of Tag 01LB — and not a statement of the source.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- **The graded piece `i_* i^* 𝒪_X(-E)` along a closed subscheme is quasi-coherent**, where
`i : D.subscheme ⟶ X` is the closed immersion cut out by a sheaf of ideals `D`.

By Tag 0EL1 it is the quotient `𝒪_X(-E) / D · 𝒪_X(-E)`, and that quotient is quasi-coherent by
`Stacks.Divisors.isQuasicoherent_idealPowerQuotient_negativeTwist`. No hypothesis on `D` or `E` —
effective Cartier or otherwise — and no affineness of `X` is needed; see the implementation notes
of this file, which record that this instance was believed not to be derivable. -/
public instance isQuasicoherent_pushforward_pullback_negativeTwist {X : Scheme.{u}}
    (D E : X.IdealSheafData) :
    ((Scheme.Modules.pushforward D.subschemeι).obj
      ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist E))).IsQuasicoherent :=
  have hv : D.subschemeι.ker = D ^ 1 :=
    (Scheme.IdealSheafData.ker_subschemeι D).trans (pow_one D).symm
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (negativeTwist E) :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf E.subschemeι
  Stacks.Descent.isQuasicoherent_of_iso
    (Stacks.Algebraization.idealQuotientPushforwardIso D 1 (negativeTwist E) D.subschemeι hv)
    (isQuasicoherent_idealPowerQuotient_negativeTwist D E 1)

end Stacks.Divisors

end
