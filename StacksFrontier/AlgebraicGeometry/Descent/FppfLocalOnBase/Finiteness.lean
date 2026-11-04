module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.BaseChangeQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal

/-!
# The finiteness entries of the list of Tag 02WH

Tag 02WH lists the properties of morphisms of schemes which, being stable under base change,
are moreover *fpqc local on the base*, hence a fortiori *fppf local on the base*. This file
records the entries of that list which are finiteness conditions: being of finite type, being
(locally) quasi-finite, being (locally) of finite presentation, and being locally of finite
type of relative dimension `d`.

## Main results

* `Stacks.Descent.finiteType_isLocalAtTarget_fppf`: being of finite type is fppf local on the
  base.
* `Stacks.Descent.locallyOfFiniteType_inf_locallyQuasiFinite_isStableUnderBaseChange` and
  `Stacks.Descent.locallyOfFiniteType_inf_locallyQuasiFinite_isLocalAtTarget_fppf`: being
  locally quasi-finite is stable under base change and fppf local on the base.
* `Stacks.Descent.finiteType_inf_locallyQuasiFinite_isLocalAtTarget_fppf`: being quasi-finite
  is fppf local on the base.
* `Stacks.Descent.locallyOfFinitePresentation_isLocalAtTarget_fppf` and
  `Stacks.Descent.finitePresentation_isLocalAtTarget_fppf`: being locally of finite
  presentation, respectively of finite presentation, is fppf local on the base.
* `Stacks.Descent.locallyOfFiniteTypeRelativeDimension_isLocalAtTarget_fppf`: being locally of
  finite type of relative dimension `d` is fppf local on the base.

## Implementation notes

Each entry of the list of Tag 02WH is stated, and carries the tag, as a single conjunction in
`StacksFrontier/AlgebraicGeometry/Descent/FppfLocalOnBase/Entries.lean`: the property is stable
under arbitrary base change, it is local on the base for the fpqc precoverage, **and** it is
local on the base for the fppf precoverage. This file supplies the "a fortiori" half of the
remark, that the property is local on the base for the fppf precoverage, obtained from the fpqc
half by `Stacks.Descent.isLocalAtTarget_fppfPrecoverage`. These instances deliberately do not
carry the tag themselves: one record per entry is what makes the tag's coverage readable, and
the conjunction that does carry it asserts this fppf locality itself, so none of the remark's
content rests on an untagged declaration.

Being locally of finite type is the remaining half of the entry "(locally) of finite type". Its
fppf locality is `Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fppf`, recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Diagonal.lean`, which carries the tag for that half
already; the half itself is stated in full by its own conjunction in `Entries.lean`.

Following the shape in which Descent, Lemma 02VI is registered, being locally quasi-finite is
`@LocallyOfFiniteType ⊓ @LocallyQuasiFinite` and being quasi-finite is
`(@LocallyOfFiniteType ⊓ @QuasiCompact) ⊓ @LocallyQuasiFinite`, the Stacks Project's notion of
a (locally) quasi-finite morphism carrying a finite type condition which
`AlgebraicGeometry.LocallyQuasiFinite` alone does not.

## References

* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-! ### Morphisms of finite type -/

/-- **Stacks 02WH**, entry (10), finite type case. Being of finite type is fppf local on the
base. -/
public instance finiteType_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Locally quasi-finite morphisms -/

/-- Being locally quasi-finite is stable under arbitrary base change, both halves of the
conjunction being so. -/
public instance locallyOfFiniteType_inf_locallyQuasiFinite_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u}) := .inf

/-- **Stacks 02WH**, entry (11), locally quasi-finite case. Being locally quasi-finite is fppf
local on the base. -/
public instance locallyOfFiniteType_inf_locallyQuasiFinite_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Quasi-finite morphisms -/

/-- **Stacks 02WH**, entry (11), quasi-finite case. Being quasi-finite is fppf local on the
base. -/
public instance finiteType_inf_locallyQuasiFinite_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      ((@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ⊓
        @LocallyQuasiFinite) Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Morphisms locally of finite presentation -/

/-- **Stacks 02WH**, entry (12), locally of finite presentation case. Being locally of finite
presentation is fppf local on the base. -/
@[sga "4 IV 8.5.5" "special case"]
public instance locallyOfFinitePresentation_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Morphisms of finite presentation -/

/-- **Stacks 02WH**, entry (12), finite presentation case. Being of finite presentation is fppf
local on the base. -/
@[sga "4 IV 8.5.5" "special case"]
public instance finitePresentation_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@FinitePresentation : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Morphisms locally of finite type of relative dimension `d` -/

/-- **Stacks 02WH**, entry (13). Being locally of finite type of relative dimension `d` is fppf
local on the base. -/
public instance locallyOfFiniteTypeRelativeDimension_isLocalAtTarget_fppf (d : ℕ) :
    MorphismProperty.IsLocalAtTarget (locallyOfFiniteTypeRelativeDimension.{u} d)
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

end Stacks.Descent

end
