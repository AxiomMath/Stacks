module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafCondition
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Koszul-regular and `H₁`-regular sequences of sections

Let `X` be a ringed space and let `f₁, …, f_r ∈ Γ(X, O_X)`. Stacks tag 063C's section defines the
family to be a *Koszul-regular sequence* when the Koszul complex `K_•(O_X, f₁, …, f_r)` of Stacks
tag 062L is a resolution of `O_X/(f₁, …, f_r)`, that is, when its homology vanishes in every
positive degree; and an *`H₁`-regular sequence* when only `H₁` vanishes.

`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafCondition` makes `K_•(O_X, f_•)` a chain complex
of sheaves of modules, which is what lets these two conditions be stated at all.

## Main definitions

* `Stacks.AlgebraicGeometry.SeqKoszul.IsKoszulRegularSequence`: the Koszul complex of the family is
  acyclic in positive degrees.
* `Stacks.AlgebraicGeometry.SeqKoszul.IsH1RegularSequence`: its `H₁` vanishes.

## Main results

* `Stacks.AlgebraicGeometry.SeqKoszul.isH1RegularSequence_of_isKoszulRegularSequence`: a
  Koszul-regular sequence is `H₁`-regular, which is the first implication of Stacks tag 063C.

## Implementation notes

**The acyclicity is the vanishing of homology of the complex of sheaves, not of presheaves.** The
two differ: a kernel of sheaves of modules is computed sectionwise, but an image is not, so the
homology of the underlying complex of presheaves is in general larger. The sheaf condition proved
in `StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafCondition` is exactly what allows the complex
to be formed in the abelian category of sheaves of modules, where the source's homology lives.

**Only "acyclic in positive degrees" is asked for, not "is a resolution of `O_X/(f_•)`".** Stacks
states Koszul-regularity as the Koszul complex being a resolution of the quotient; that `H₀` is the
quotient holds for every family, with no hypothesis, so the condition on the family is the
vanishing of the higher homology. The same reading is already used at the ring level by
`Koszul.IsKoszulRegular` in `StacksFrontier.RingTheory.Koszul.Defs`, tagged 062E, and these
definitions are its sheaf analogue so that the two can be compared.

## References

* [Stacks Project, Tag 063C](https://stacks.math.columbia.edu/tag/063C)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasiRegular

universe u

namespace Stacks.AlgebraicGeometry.SeqKoszul

variable (X : RingedSpace.{u, u}) {r : ℕ} (f : Fin r → X.presheaf.obj (op (⊤ : Opens X)))

/-- **A Koszul-regular sequence of sections of the structure sheaf**: the Koszul complex
`K_•(O_X, f₁, …, f_r)` has vanishing homology in every nonzero degree, i.e. it is a resolution of
`O_X/(f₁, …, f_r)`. -/
def IsKoszulRegularSequence : Prop :=
  ∀ i ≠ 0, IsZero ((sheafComplex X r f).homology i)

/-- **An `H₁`-regular sequence of sections of the structure sheaf**: the Koszul complex
`K_•(O_X, f₁, …, f_r)` has vanishing `H₁`. -/
def IsH1RegularSequence : Prop :=
  IsZero ((sheafComplex X r f).homology 1)

/-- **Stacks Project, Tag 063C.** A Koszul-regular sequence is `H₁`-regular: degree `1` is one of
the positive degrees in which the Koszul complex of a Koszul-regular sequence is acyclic. -/
@[stacks 063C "Koszul-regular implies H₁-regular", ega "IV 19.5.1" "b) => b')"]
theorem isH1RegularSequence_of_isKoszulRegularSequence
    (h : IsKoszulRegularSequence X f) : IsH1RegularSequence X f :=
  h 1 one_ne_zero

end Stacks.AlgebraicGeometry.SeqKoszul

end
