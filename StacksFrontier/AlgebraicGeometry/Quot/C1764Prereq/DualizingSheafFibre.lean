module

public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafShape
public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafFibreRestriction

/-!
# The relative dualizing sheaf of a prestable family on its fibres

Let `f : X ⟶ S` be a prestable family of curves and `(ω^•_{X/S}, τ)` a relative dualizing
complex (Stacks 0E5X). The relative dualizing sheaf `ω_{X/S} = H^{-1}(ω^•_{X/S})` (Stacks 0E6Q)
restricts on every fibre `X_s`, presented by a scheme over `Spec κ(s)`, to the dualizing sheaf of
Stacks 0BS2 of the fibre: formation of `ω_{X/S}` commutes with base change to the residue fields
(Stacks 0E6P, 0E6Q), by
`AlgebraicGeometry.C1764Prereq.nonempty_baseChangeModule_dualizingSheafOfComplex_iso`.

## Main results

* `AlgebraicGeometry.C1764Prereq.isDualizingOnFibres_dualizingSheafOfComplex`: `ω_{X/S}`
  restricts on every fibre to its dualizing sheaf.

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The relative dualizing sheaf `H^{-1}(ω^•_{X/S})` of a prestable family restricts on
every fibre `X_s` to the dualizing sheaf of Stacks 0BS2 of the fibre over `κ(s)`. -/
theorem C1764Prereq.isDualizingOnFibres_dualizingSheafOfComplex {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (D : Space.RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) :
    CurveFamily.IsDualizingOnFibres B hZ X (X.dualizingSheafOfComplex D) :=
  fun _ _ _ _ h => C1764Prereq.nonempty_baseChangeModule_dualizingSheafOfComplex_iso hX D h

end AlgebraicGeometry
