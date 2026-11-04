module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.EffectiveCartierConormalSheaf
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Punctured
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normal bundle of an effective Cartier divisor as a line bundle

For an effective Cartier divisor `D ⊆ X` the degree-one conormal sheaf `𝒞_{D/X}` is invertible, so
the data of `D.subscheme` together with that sheaf is a `Stacks.LineBundle.Situation`. This file
records that presentation and its zero section.

## Main definitions

* `Stacks.Conormal.conormalSituation`: the conormal line-bundle situation of an effective Cartier
  divisor, with base `D.subscheme` and module
  `Stacks.Conormal.conormalSheafDegreeOne D.subschemeι`.
* `Stacks.Conormal.conormalZeroSection`: the zero section of that situation, the morphism written
  `o` in [Stacks, Tag 0FEB].

## References

* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Conormal

variable {X : Scheme.{u}} (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- The conormal line-bundle situation of an effective Cartier divisor `D`: its base is
`D.subscheme`, its module is the degree-one conormal sheaf `conormalSheafDegreeOne D.subschemeι`,
which is invertible, and its structure morphism is the identity of `D.subscheme`. -/
@[ega "II 8.9.4", ega "IV 19.4.1" "more general"]
def conormalSituation : Stacks.LineBundle.Situation.{u} where
  X := D.subscheme
  S := D.subscheme
  f := CategoryTheory.CategoryStruct.id _
  L := conormalSheafDegreeOne D.subschemeι
  invertible := isInvertible_conormalSheafDegreeOne_of_isEffectiveCartierDivisor D

/-- The base scheme of `conormalSituation D` is `D.subscheme`. -/
@[simp]
theorem conormalSituation_X : (conormalSituation D).X = D.subscheme := rfl

/-- The module of `conormalSituation D` is the degree-one conormal sheaf of `D.subschemeι`. -/
@[simp]
theorem conormalSituation_L :
    (conormalSituation D).L = conormalSheafDegreeOne D.subschemeι := rfl

/-- The zero section of the conormal line bundle of `D`, the morphism written `o` in
[Stacks, Tag 0FEB]. -/
def conormalZeroSection :
    (conormalSituation D).X ⟶ (conormalSituation D).totalSpace :=
  Stacks.LineBundle.Situation.zeroSection (conormalSituation D)

end Stacks.Conormal

end
