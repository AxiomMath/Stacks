module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.IdealSheaf
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# Regular and quasi-regular immersions, and the relative notions

An immersion of schemes `i : Z ⟶ X` factors as a closed immersion into the open subscheme
`i.coborderRange` of `X` followed by the inclusion of that open.  Its *defining ideal* is the
sectionwise kernel of the structure-sheaf map of that closed factor, read as an ideal subsheaf
of the structure sheaf of `i.coborderRange`.  The immersion is *regular* (resp.
*quasi-regular*) when that ideal sheaf is regular (resp. quasi-regular) in the sense of Stacks
tag 063D.

Over a base, an immersion into a scheme `X ⟶ S` is a *relative quasi-regular immersion* when
`Z ⟶ S` is flat and `i` is a quasi-regular immersion.

## Main definitions

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom`: the embedded kernel ideal of the
  structure-sheaf map of a morphism of schemes.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal`: the embedded kernel ideal of the
  canonical closed factor of an immersion, on `i.coborderRange`.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion`: part (1) of Stacks tag 063J.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion`: part (4) of Stacks tag
  063J.
* `Stacks.AlgebraicGeometry.IsRelativeQuasiRegularImmersion`: part (1) of Stacks tag 063S.  Part
  (2), relative `H₁`-regularity, is `AlgebraicGeometry.IsRelativeH1RegularImmersion`.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.mem_definingIdealOfHom` and
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.eq_definingIdealOfHom_of_mem_iff`: membership in the
  defining ideal is vanishing in the pushforward structure sheaf, and that characterizes it
  uniquely.

## Implementation notes

The canonical open on which an immersion is closed is `i.coborderRange`, with closed factor
`i.liftCoborder`;  both are Mathlib's.  An ideal subsheaf is a `SheafOfModules.Submodule` of
the rank-one structure sheaf module `structureSheafModule`, and the defining ideal is the
kernel of `SheafOfModules.unitToPushforwardObjUnit (structureSheafHom …)`, i.e. the sectionwise
kernel of the map `O_U ⟶ j_* O_Z`.  `kernelSubmodule` builds that kernel as an embedded
submodule sheaf;  its sheaf condition is separatedness of the target, so no sheafification is
involved and membership is literally vanishing of the section, which is
`mem_definingIdealOfHom`.

Parts (2) and (3) of tag 063J, Koszul-regularity and `H₁`-regularity, need the Koszul complex
of a sheaf of modules (Stacks tag 062K) and are not defined here;  neither is the
independence-of-the-chosen-open characterization of tag 063J, which no statement in this file
needs.

## References

* [Stacks Project, Definition 31.21.1 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Definition 31.22.2 (Tag 063S)](https://stacks.math.columbia.edu/tag/063S)
* [SGA 6, Exposé VII, Definition 1.4]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RingedSpace

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

/-- **Part (1) of Stacks tag 063S.** An immersion into a scheme over a base is a *relative
quasi-regular immersion* when the immersed scheme is flat over the base and the immersion is
quasi-regular. -/
@[stacks 063S "part (1): relative quasi-regular immersion"]
abbrev IsRelativeQuasiRegularImmersion {Z X S : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsImmersion i] : Prop :=
  Flat (i ≫ f) ∧ IsQuasiRegularImmersion i

end Stacks.AlgebraicGeometry

end
