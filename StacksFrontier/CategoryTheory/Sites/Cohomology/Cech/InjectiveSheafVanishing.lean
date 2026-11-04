module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectivePresheafVanishing
import StacksCore.Tactic.StacksAttribute

/-! # Čech cohomology of an injective abelian sheaf

Let `C` be a site and let `E = {U_i → U}` be a family of morphisms of `C` with fixed target, all of
whose finite nonempty fibre products exist. Stacks 03AW computes the Čech cohomology of an
injective abelian sheaf `I`: it is `I(U)` in degree zero and vanishes in positive degrees. The
degree-zero clause is `Stacks.CechSite.cechCohomology_zero_iso`; this file proves the
positive-degree clause, together with the fact (Stacks 03F6) that an injective sheaf is injective
as a presheaf.

## Main results

* `CategoryTheory.sheafToPresheaf_preservesInjectiveObjects`: for sheaves valued in any category
  admitting sheafification, the inclusion of sheaves into presheaves preserves injective objects.
* `CategoryTheory.Sheaf.injective_obj`: an injective sheaf is injective as a presheaf.
* `Stacks.CechSite.injective_sheaf_cechCohomology_isZero`: Stacks 03AW in positive degrees.

## References

* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
* [Stacks Project, Tag 03F6](https://stacks.math.columbia.edu/tag/03F6)
* [Stacks Project, Tag 03OR](https://stacks.math.columbia.edu/tag/03OR)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

universe a w v u v' u'

namespace CategoryTheory

open CategoryTheory.Limits

/-- The inclusion of sheaves into presheaves preserves injective objects. -/
@[stacks 03OV "the forgetful functor from sheaves to presheaves preserves injectives",
  sga "4 V 3.1" "special case"]
theorem sheafToPresheaf_preservesInjectiveObjects {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (A : Type u') [Category.{v'} A] [HasSheafify J A] :
    (sheafToPresheaf J A).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafificationAdjunction J A)

/-- An injective sheaf is injective as a presheaf. -/
@[stacks 03F6]
theorem Sheaf.injective_obj {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u'} [Category.{v'} A] [HasSheafify J A]
    (I : Sheaf J A) [Injective I] : Injective I.obj :=
  have := sheafToPresheaf_preservesInjectiveObjects J A
  (sheafToPresheaf J A).injective_obj_of_injective (X := I) inferInstance

end CategoryTheory

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

/-- **Stacks 03AW (positive degrees).** The positive-degree Čech cohomology of an injective
abelian sheaf, with respect to a family of morphisms with fixed target whose finite nonempty
fibre products exist, vanishes. Sheafification of abelian presheaves exists at this universe
convention and is not assumed. -/
theorem injective_sheaf_cechCohomology_isZero {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {U : C} (E : PreZeroHypercover.{w} U)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (I : Sheaf J Ab.{max a u v w}) [Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E I.obj p) := by
  let Jsmall := (equivSmallModel.{max u v a w, v, u} C).inverse.inducedTopology J
  let : UnivLE.{max u v, max u v a w} := inferInstance
  let : UnivLE.{max (max u v a w) u v, max u v a w} := inferInstance
  let : HasFiniteLimits AddCommGrpCat.{max u v a w} := inferInstance
  let : PreservesLimits (forget AddCommGrpCat.{max u v a w}) :=
    AddCommGrpCat.forget_preservesLimits
  let : ∀ X : SmallModel.{max u v a w} C,
      Small.{max u v a w, max u v a w} (Jsmall.Cover X)ᵒᵖ := fun X => inferInstance
  let : HasSheafify Jsmall AddCommGrpCat.{max u v a w} := inferInstance
  let : HasSheafify J AddCommGrpCat.{max u v a w} :=
    hasSheafifyEssentiallySmallSite.{v, max u v a w, u, (max u v a w) + 1, max u v a w}
      J AddCommGrpCat
  let : Injective I.obj := I.injective_obj
  exact injective_presheaf_cechCohomology_isZero.{w, v, u, a} (I := I.obj) E p hp

end Stacks.CechSite
