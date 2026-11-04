module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Fpqc
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat

/-!
# Flatness is local on the source for the étale topology (Stacks 04R3, 03MO)

Flatness of morphisms of schemes is local on the source for the étale topology, and so, by the
chain Tag 04R3 to Tag 03MJ to Tag 0AMM, flatness of morphisms of algebraic spaces is stable
under base change.

Étale locality on the source needs no new descent argument: flatness is already fpqc local on
the source, which is `AlgebraicGeometry.flat_isLocalAtSource_fpqc` (Tag 036K), and an étale
covering is an fpqc covering. The containment is Mathlib's, factoring through the pro-étale
precoverage: an étale morphism is open, so an étale covering family is quasi-compact in the
sense of `AlgebraicGeometry.Scheme.qcPrecoverage`, and it is flat because étale morphisms are.

Locality on the source and target is then the formal half of Tag 04R2, which is
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource`. Its two remaining inputs
are formal for flatness: a flat morphism stays flat after postcomposition with an étale
morphism, because an étale morphism is flat and flat morphisms compose, and flatness is stable
under base change in Mathlib. In particular the fibre-degree induction of Tag 04R2 is not used.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Flat.isLocalAtSource_etalePrecoverage`: flatness of morphisms of schemes is
  local on the source for the étale topology.
* `AlgebraicGeometry.Flat.respectsRight_etale`: postcomposition with an étale morphism preserves
  flatness.
* `AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget`: **Stacks 04R3**, flat case.
* `AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange`: **Stacks 03MO**, flatness of
  morphisms of algebraic spaces is stable under base change.

## Implementation notes

`AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget` and
`AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange` are unconditional: every instance
argument they would otherwise carry is discharged here, so the tags record exactly the Stacks
statements. This is why the general, hypothesis-carrying forms in
`StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource` and
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange` are untagged.

## References

* [Stacks Project, Tag 036K](https://stacks.math.columbia.edu/tag/036K)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Flatness of morphisms of schemes is local on the source for the étale topology.

An étale covering is an fpqc covering, so this is a special case of the fpqc statement
`AlgebraicGeometry.flat_isLocalAtSource_fpqc` (Tag 036K). -/
instance Flat.isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource (@Flat : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  MorphismProperty.IsLocalAtSource.of_le
    (Scheme.etalePrecoverage_le_proetalePrecoverage.trans
      Scheme.proetalePrecoverage_le_fpqcPrecoverage)

/-- Postcomposition with an étale morphism preserves flatness: an étale morphism is flat, and
flat morphisms compose. -/
theorem Flat.respectsRight_etale :
    MorphismProperty.RespectsRight (@Flat : MorphismProperty Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) where
  postcomp i hi f hf := by
    let : Etale i := hi
    let : Flat f := hf
    exact inferInstance

/-- **Stacks Project, Tag 04R3, flat case.** Being a flat morphism of schemes is étale local on
the source and target. -/
@[stacks 04R3 "flat"]
theorem Flat.isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (@Flat : MorphismProperty Scheme.{u}) :=
  let := Flat.respectsRight_etale.{u}
  IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource _

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Project, Tag 03MO.** Flatness of morphisms of algebraic spaces over `S` is stable
under base change. -/
@[stacks 03MO]
theorem isFlat_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsFlat B S hS f.hom) :=
  holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS
    (@Flat.{u} : MorphismProperty Scheme.{u}) Flat.isEtaleLocalOnSourceAndTarget

end Space

end AlgebraicGeometry

end
