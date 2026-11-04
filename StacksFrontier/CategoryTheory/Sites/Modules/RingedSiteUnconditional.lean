module
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import all StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsUnconditional

/-!
# The underlying sheaf of rings of a ringed site

The structure sheaf of a ringed site, viewed as a sheaf of (not necessarily commutative) rings.

## Main definitions

* `AlgebraicGeometry.RingedSite.ringSheaf`: The structure sheaf of a ringed site, with
  commutativity forgotten.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace RingedSite

end RingedSite

end AlgebraicGeometry

end

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t s u v w

namespace AlgebraicGeometry

namespace RingedSite

/-- The structure sheaf of a ringed site, with commutativity forgotten. Sheaves of modules on
a ringed site are sheaves of modules over this sheaf of rings. -/
noncomputable abbrev ringSheaf (X : RingedSite.{u, v, w}) : Sheaf X.J RingCat.{w} :=
  letI := X.hasSheafCompose_forget₂_ringCat
  SheafOfModules.underlyingRingSheafOfSite X.O

end RingedSite

end AlgebraicGeometry

end
