module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty

/-!
# Finiteness of morphisms of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`. Finiteness of a morphism of algebraic
spaces over `S` (**Stacks 03ZP**) is local on the base for the fpqc topology of
**Stacks 03YH**: a morphism is finite exactly when its base change to every member of some fpqc
covering family of its target is finite. This is **Stacks 0426**.

A morphism of algebraic spaces is finite exactly when it is proper and locally quasi-finite
(**Stacks 0A4X**, conditions (1) and (2)), properness is fpqc local on the base by
**Stacks 0422** and local quasi-finiteness by **Stacks 0427**, and locality on the base passes
to an infimum of morphism properties.

## Main definitions

* `AlgebraicGeometry.Space.finiteMorphismProperty`: finiteness of a morphism (Stacks 03ZP) as a
  `CategoryTheory.MorphismProperty` on `AlgebraicGeometry.AlgebraicSpaces`, the spelling at
  which locality on the base is stated.

## Main results

* `AlgebraicGeometry.Space.finiteMorphismProperty_eq_inf`: finiteness *is* properness together
  with local quasi-finiteness, as morphism properties.
* `AlgebraicGeometry.Space.isFinite_isLocalAtTarget_fpqc`: **Stacks 0426**.
* `AlgebraicGeometry.Space.isFinite_isLocalAtTarget_fppf`: the same statement at the fppf
  precoverage, which is the form the relative properties of Stacks 03YK consume.

## Implementation notes

The source argues instead from the characterization of a finite morphism as an integral morphism
which is locally of finite type (Stacks 0414), combining Stacks 041S, being locally of finite
type is fpqc local on the base, with Stacks 0425, integrality is fpqc local on the base. That
route is not taken here: integrality is affineness together with universal closedness, so it
inherits from affineness the descent step of Stacks 041Z, which this development reaches only
from Gabber's Stacks 0APL — see
`AlgebraicGeometry.Space.integralMorphismProperty_isLocalAtTarget_fpqc_of_isAffineHom`. The
decomposition along Stacks 0A4X has no such dependence: a proper locally quasi-finite morphism
is finite because finiteness can be checked on an étale neighbourhood of each point of the
target and is Zariski local there (Stacks 03ZQ).

The index universe of a covering family is a free universe parameter of
`AlgebraicGeometry.Space.Topology.precoverage` and stays free here, as it does in Stacks 0422
and Stacks 0427.

## References

* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 0426](https://stacks.math.columbia.edu/tag/0426)
* [Stacks Project, Tag 0427](https://stacks.math.columbia.edu/tag/0427)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being finite (**Stacks 03ZP**), as a property of morphisms in the category of algebraic
spaces over `S`. This is the spelling at which locality on the base, Stacks 03YH, is stated. -/
abbrev finiteMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsFinite B S hS f.hom

/-- **Stacks 0A4X, conditions (1) and (2), at the packaged spelling**: finiteness of morphisms
of algebraic spaces over `S` is the infimum of properness (Stacks 03ZM) and local
quasi-finiteness (Stacks 03XJ, part (1)) as morphism properties. -/
theorem finiteMorphismProperty_eq_inf :
    finiteMorphismProperty B S hS =
      properProperty B S hS ⊓ locallyQuasiFiniteProperty B S hS := by
  funext X Y f
  exact propext
    ⟨isProper_and_isLocallyQuasiFinite_of_isFinite B S hS X.property Y.property f.hom,
      fun h ↦ isFinite_of_isProper_of_isLocallyQuasiFinite B S hS X.property Y.property f.hom
        h.1 h.2⟩

/-- **Stacks 0426.** Finiteness of morphisms of algebraic spaces over `S` is local on the base
for the fpqc topology of Stacks 03YH: a morphism is finite exactly when its base change to every
member of some fpqc covering family of its target is finite.

A morphism is finite exactly when it is proper and locally quasi-finite (**Stacks 0A4X**),
properness is fpqc local on the base by **Stacks 0422** and local quasi-finiteness by
**Stacks 0427**, so their conjunction is. -/
@[stacks 0426, sga "4 IV 8.5.5" "more general"]
instance isFinite_isLocalAtTarget_fpqc :
    (finiteMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  rw [finiteMorphismProperty_eq_inf]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

/-- **Stacks 0426** at the fppf precoverage: finiteness of morphisms of algebraic spaces over
`S` is local on the target for the fppf topology. This is the form in which Stacks 03YK's
relative properties ask for it, and it follows from the fpqc form because every fppf covering
family of algebraic spaces is an fpqc covering family. -/
instance isFinite_isLocalAtTarget_fppf :
    (finiteMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
