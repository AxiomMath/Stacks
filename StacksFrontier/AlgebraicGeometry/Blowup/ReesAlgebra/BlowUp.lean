module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The blowup of a scheme in a quasi-coherent ideal

The blowup of a scheme `X` in a quasi-coherent ideal sheaf `I` is the relative `Proj` of the
Rees algebra `⨁_{n ≥ 0} Iⁿ`. Its exceptional divisor is the inverse image of the closed
subscheme cut out by `I`, as a closed subscheme of the blowup.

## Main definitions

* `AlgebraicGeometry.reesSituation` is the Rees algebra of `I`, packaged as a relative `Proj`
  situation.
* `AlgebraicGeometry.blowUp` is the blowup of `X` in `I` and
  `AlgebraicGeometry.blowUpToBase` its structure morphism to `X`.
* `AlgebraicGeometry.exceptionalIdeal` is the inverse-image ideal sheaf of `I` on the blowup,
  and `AlgebraicGeometry.exceptionalDivisor` the closed subscheme it cuts out.

## Implementation notes

The relative `Proj` of a quasi-coherent nonnegatively graded algebra is
`Stacks.RelativeProj.Situation.relativeProj`, so the blowup is obtained by exhibiting the Rees
algebra as such a situation: commutativity, the vanishing of the negative pieces and
quasi-coherence of each piece are exactly the fields of
`AlgebraicGeometry.ReesAlgebraData` that the situation asks for. The canonical affine charts of
the blowup are therefore those of the relative `Proj`,
`Stacks.RelativeProj.Situation.relativeProjChart`, and the identification of the part of the
blowup lying over an affine open of the base is
`Stacks.RelativeProj.Situation.relativeProjChart_isPullback`.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace Opposite

universe u

/-- The Rees algebra of a quasi-coherent ideal sheaf, as a relative `Proj` situation: a scheme
carrying a commutative, nonnegatively graded, quasi-coherent algebra over its structure
sheaf. -/
@[sga "2 XII 4.2" "partial"]
public noncomputable abbrev reesSituation {X : Scheme.{u}} (I : X.IdealSheafData) :
    Stacks.RelativeProj.Situation.{u} where
  base := X
  algebra := (reesAlgebraData I).algebra
  mul_comm := (reesAlgebraData I).mul_comm
  negative_isZero := (reesAlgebraData I).negative_isZero
  isQuasicoherent := (reesAlgebraData I).isQuasicoherent

/-- **Stacks Project, Tag 01OG.** The blowup of `X` in the quasi-coherent ideal `I`: the
relative `Proj` of the Rees algebra `⨁ₙ Iⁿ`. -/
@[stacks 01OG "blowup morphism", ega "II 8.1.3" "qcoh ideal case", ega "IV 19.4.1" "X'=Proj(⊕J^n)"]
public noncomputable abbrev blowUp {X : Scheme.{u}} (I : X.IdealSheafData) : Scheme.{u} :=
  (reesSituation I).relativeProj

/-- **Stacks Project, Tag 01OG.** The blowup morphism: the structure morphism of the blowup of
`X` in `I` to `X`. -/
@[stacks 01OG "blowup morphism",
  ega "II 8.1.3" "qcoh ideal case",
  ega "IV 19.4.1" "structural morphism f"]
public noncomputable abbrev blowUpToBase {X : Scheme.{u}} (I : X.IdealSheafData) :
    blowUp I ⟶ X :=
  (reesSituation I).relativeProjToBase

/-- The inverse-image ideal defining the exceptional divisor. -/
@[stacks 01OG "exceptional ideal sheaf"]
public noncomputable abbrev exceptionalIdeal {X : Scheme.{u}} (I : X.IdealSheafData) :
    (blowUp I).IdealSheafData :=
  I.comap (blowUpToBase I)

/-- **Stacks Project, Tag 01OG.** The exceptional divisor is the inverse image of the
closed subscheme cut out by `I`. -/
@[stacks 01OG "exceptional divisor scheme", ega "IV 19.4.1" "Y'=f^{-1}(Y)", sga "7 XVIII 2.1"]
public noncomputable abbrev exceptionalDivisor {X : Scheme.{u}} (I : X.IdealSheafData) :
    Scheme.{u} :=
  (exceptionalIdeal I).subscheme

end AlgebraicGeometry

end
