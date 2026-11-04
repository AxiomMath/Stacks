module
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsUnderlyingRingSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
import all StacksFrontier.CategoryTheory.Sites.Modules.Differentials

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.SmallSiteSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# DifferentialsUnconditional

Stronger forms of declarations of `StacksFrontier.CategoryTheory.Sites.Modules.Differentials`,
stated as separate declarations beside the ones there: over more general coefficient universes,
or with inputs that are carried there as hypotheses discharged, together with the new results
built on them.
-/

@[expose] public section

open CategoryTheory

universe v v₁ u u₁ w₀

namespace AlgebraicGeometry.SheafOfModules

universe w

end AlgebraicGeometry.SheafOfModules
