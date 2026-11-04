module
public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic
import all StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# BasicUnconditional

Stronger forms of declarations of `StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic`,
stated as separate declarations beside the ones there: over more general coefficient universes,
or with inputs that are carried there as hypotheses discharged, together with the new results
built on them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.SheafifyCommRing

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

attribute [-instance] Stacks.SheafifyCommRing.hasSheafifyCommRingCat in
/-- Sheafification of presheaves of commutative rings exists and is left exact, with the rings
in any universe `w` containing the universes of the site. The universe of the rings is a
variable constrained by `UnivLE` rather than a `max`, so that instance search finds the
instance at a coefficient universe equal to that of the site, such as `u + 1` for the small
étale site of a `Scheme.{u}`: a `max u v w` there poses the universe problem
`u + 1 =?= max (u + 1) ?w`, which unification cannot solve. -/
instance hasSheafifyCommRingCat_general [UnivLE.{max u v, w}] : HasSheafify J CommRingCat.{w} := by
  let : PreservesFilteredColimitsOfSize.{max u v, max u v} (forget CommRingCat.{w}) :=
    preservesFilteredColimitsOfSize_of_univLE (forget CommRingCat.{w})
  let : HasColimitsOfSize.{max u v, max u v} CommRingCat.{w} :=
    hasColimitsOfSizeOfUnivLE CommRingCat.{w}
  infer_instance

end Stacks.SheafifyCommRing

end
