module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A morphism admitting a relatively very ample sheaf is separated

Stacks Tag 01VQ reads: *if `L` is relatively very ample on `X/S` then `f : X ⟶ S` is separated.*

Relative very ampleness, `Stacks.Tag01VMRelativeVeryAmple.IsRelativelyVeryAmple`, produces an
immersion `i : X ⟶ 𝐏(E)` with `i ≫ (𝐏(E) ⟶ S) = f`. Separatedness of `f` is then forced by two
facts about the factorisation, and uses nothing about the twist that relative very ampleness also
produces — not its invertibility and not its being a degree-one twist. So the hypothesis is
consumed only through its immersion, and the caveat recorded in the module documentation of
`Stacks.Tag01VMRelativeVeryAmple` — that `𝒪_{𝐏(E)}(1)` is not constructed in this repository, so
`IsDegreeOneTwist` stands in for it — does not touch this tag: a predicate quantifying the twist
differently would give the same immersion and hence the same conclusion.

The two facts are:

* `𝐏(E) ⟶ S` is separated. This is
  `Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase` applied to the graded
  algebra `Sym(E)`, since `𝐏(E)` is `relativeProj (symAlgebra E)` by definition.
* an immersion is separated. An immersion is a preimmersion, a preimmersion is a monomorphism,
  and a monomorphism is separated — Mathlib's `AlgebraicGeometry.IsSeparated.isSeparated_of_mono`.

Separatedness is stable under composition, so the composite is separated, and it is `f`.

## Main results

* `Stacks.Tag01VMRelativeVeryAmple.isSeparated_of_isRelativelyVeryAmple`: **Stacks Tag 01VQ.**

## References

* [Stacks Project, Tag 01VQ](https://stacks.math.columbia.edu/tag/01VQ)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01KP](https://stacks.math.columbia.edu/tag/01KP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Ample
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.Tag01VMRelativeVeryAmple

/-- **Stacks Tag 01VQ: a morphism admitting a relatively very ample invertible sheaf is
separated.**

Relative very ampleness gives an immersion `i : X ⟶ 𝐏(E)` over the base. The structure morphism
of `𝐏(E) = relativeProj (symAlgebra E)` is separated, an immersion is a monomorphism and hence
separated, and separatedness is stable under composition; the composite is `f`. -/
@[stacks 01VQ, ega "II 4.4.2"]
public theorem isSeparated_of_isRelativelyVeryAmple {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsRelativelyVeryAmple f L) :
    IsSeparated f := by
  obtain ⟨E, hE, -, -, -, i, him, rfl, -⟩ := hL
  have := hE
  have hsep : IsSeparated (relativeProj (symAlgebra E)).toBase :=
    RelativeProjSeparated.isSeparated_toBase (symAlgebra E) (relativeProj (symAlgebra E))
  infer_instance

end Stacks.Tag01VMRelativeVeryAmple

end
