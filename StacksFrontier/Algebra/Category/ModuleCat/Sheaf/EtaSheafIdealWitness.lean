module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroCartier

import StacksCore.Tactic.StacksAttribute

/-!
# A non-degenerate invertible ideal sheaf, assembled

The décalage development of `EtaSheaf*.lean` — Tags 0GT3 to 0GT9 — is stated throughout for a
ringed space `X` carrying an invertible ideal subsheaf `ι : I ⟶ O_X`, and never instantiates
them.  The only inhabitants of that datum available by synthesis are the *unit* ideal
(`Stacks.SheafOfModules.isInvertible_unit`, and
`Cohomology.Torsors.isInvertible_unit_structureSheaf` at exactly the development's spelling) and
the empty closed subscheme `Stacks.Divisors.IsEffectiveCartierDivisor.top`, which is the same
thing.  Both are degenerate for the décalage: modulo the unit ideal `O_X/I` is zero, so both
sides of Tag 0GT9 are zero and every comparison in the development is trivially an isomorphism.

This file assembles a non-degenerate one, so that the development's statements can be tested
against a datum that is not vacuous and not degenerate.  Nothing here is new mathematics: the
chain already existed in full and had simply never been composed.

## Main results

* `zeroDivisorIdealι`: the inclusion `I_{D₀} ⟶ O_X` of the ideal sheaf of the zero divisor
  `D₀ ⊆ ℙ¹_S`, a monomorphism by `Divisors.Eta.mono_idealSheafι`.
* `isInvertible_zeroDivisorIdeal`: it is invertible, at the spelling the décalage uses.  The
  only hypothesis is `S : Scheme`, by `Chow.lineZeroDivisor_isEffectiveCartierDivisor`.
* The structure-sheaf stalks are local rings, by Mathlib's instance on a locally ringed space,
  `AlgebraicGeometry.LocallyRingedSpace.isLocalRing`: this is what
  `Reduction.exists_stalkGenerator` needs and what no one-point or skyscraper model supplies.

Specialized at `S = Spec ℤ` these give a ringed space, an invertible ideal subsheaf and a
monomorphism, all concrete and all assuming nothing.  `D₀` is cut out on the affine chart by the
coordinate `T`, so the ideal is *not* the unit ideal: this is a genuinely non-degenerate witness.

## Implementation notes

The one step of the binder list this does *not* reach is a nonzero `I`-torsion-free module at
this instance.  The route is `IdealTorsion.isIdealTorsionFree_of_isFlat` applied to
`SheafOfModules.unit`, whose flatness is `RingedSpace.isFlat_unit_of_ringedSpace`, with
`IdealTorsion.isLocallyGeneratedByRegular_of_isInvertible` supplying the regular generation.
That last lemma is stated over `TensorStalkRingedSpace.structureSheafRing X` and `X.presheaf`,
while the ideal here lives over `structureSheaf X.toRingedSpace.sheaf`, and the two spellings are
not interchangeable at the use site.  Bridging them is a separate piece of work and is not done
here.

## References

* [Stacks Project, Tag 0GT3](https://stacks.math.columbia.edu/tag/0GT3)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.IdealTorsion.Witness

variable (S : Scheme.{u})

/-- The projective line `ℙ¹_S`, as the ambient scheme of the witness. -/
public noncomputable abbrev line : Scheme.{u} := Stacks.Chow.relativeProjectiveLine S

/-- The ideal sheaf of the zero divisor `D₀ ⊆ ℙ¹_S`, as a sheaf of `O_X`-modules. -/
public noncomputable abbrev zeroDivisorIdeal :
    SheafOfModules.{u} (structureSheaf (line S).toRingedSpace.sheaf) :=
  Stacks.Divisors.Eta.idealSheaf (X := line S) (Stacks.Chow.lineZeroDivisor S)

/-- The inclusion `I_{D₀} ⟶ O_X` of the ideal sheaf of the zero divisor of `ℙ¹_S`.  It is a
monomorphism by `Divisors.Eta.mono_idealSheafι`, a kernel inclusion. -/
public noncomputable abbrev zeroDivisorIdealι :
    zeroDivisorIdeal S ⟶ SheafOfModules.unit (structureSheaf (line S).toRingedSpace.sheaf) :=
  Stacks.Divisors.Eta.idealSheafι (X := line S) (Stacks.Chow.lineZeroDivisor S)

/-- **The ideal sheaf of the zero divisor of `ℙ¹_S` is an invertible ideal subsheaf**, at the
spelling the décalage development of `EtaSheaf*.lean` uses.  `D₀` is an effective Cartier divisor
for every `S` (`Chow.lineZeroDivisor_isEffectiveCartierDivisor`, Tag 02RQ part (3)), and the
ideal sheaf of an effective Cartier divisor is invertible
(`Divisors.Eta.isInvertible_idealSheaf`, Tag 01CS).

Unlike the unit ideal, this one is proper: on the affine chart `D₀` is cut out by the coordinate
`T`.  So it is the first non-degenerate datum available to the development. -/
public theorem isInvertible_zeroDivisorIdeal :
    Stacks.SheafOfModules.IsInvertible (line S).toRingedSpace.sheaf.obj
      (structureSheaf (line S).toRingedSpace.sheaf).property (zeroDivisorIdeal S) := by
  have := Stacks.Chow.lineZeroDivisor_isEffectiveCartierDivisor S
  infer_instance

/-! ### The concrete instance -/

/-- `ℙ¹` over `Spec ℤ`: a concrete ringed space, assuming nothing. -/
public noncomputable abbrev lineZ : Scheme.{0} := line (Spec (CommRingCat.of ℤ))

/-- **The witness, concretely.**  On `ℙ¹_ℤ` the ideal sheaf of the zero divisor is a proper
invertible ideal subsheaf with monomorphic inclusion and local structure-sheaf stalks — every
ambient datum of Tags 0GT3 to 0GT9 at once, built from declarations that assume nothing. -/
public theorem isInvertible_zeroDivisorIdeal_specZ :
    Stacks.SheafOfModules.IsInvertible lineZ.toRingedSpace.sheaf.obj
        (structureSheaf lineZ.toRingedSpace.sheaf).property
        (zeroDivisorIdeal (Spec (CommRingCat.of ℤ))) ∧
      Mono (zeroDivisorIdealι (Spec (CommRingCat.of ℤ))) :=
  ⟨isInvertible_zeroDivisorIdeal _,
    Stacks.Divisors.Eta.mono_idealSheafι (X := lineZ) (Stacks.Chow.lineZeroDivisor _)⟩

end Stacks.IdealTorsion.Witness

end
