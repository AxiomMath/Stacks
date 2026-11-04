module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Lower shriek on abelian sheaves

Let `f : C ⥤ D` be a continuous functor of sites. When restriction `g^{-1} =
f.sheafPushforwardContinuous` of abelian sheaves along `f` has a left adjoint, that left adjoint
is `CategoryTheory.Functor.sheafPullback`; in the notation of Stacks 07AC it is the functor
`g_!^{Ab} : Ab(C) ⥤ Ab(D)`, the lower shriek of the same morphism of sites taken with the
constant sheaf of integers as structure sheaf.

This file names that functor and does nothing else. It is the one object shared by the
lower-shriek development of Stacks 0798 and 07AC, which compares it with lower shriek on sheaves
of modules, and by the comparison of global cohomology on a bigger site of Stacks 03YU, which
uses it through its adjunction; stating it once here keeps the two from spelling out the same
functor. The two sites, their morphisms and the abelian groups lie in mutually independent
universes, and the only hypotheses are the two that `sheafPullback` itself asks for.

## Main definitions

* `Stacks.Cohomology.lowerShriekAbelian`: `g_!^{Ab}`, the left adjoint of restriction of abelian
  sheaves along a continuous functor of sites.

## References

* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology

/-- Lower shriek `g_!^{Ab} : Ab(C) ⥤ Ab(D)` on abelian sheaves, the left adjoint of restriction
of abelian sheaves along the functor of sites. This is the functor written `g_!^{Ab}` in the
notation of Stacks 07AC, and the source of the comparison of Stacks 0798. -/
abbrev lowerShriekAbelian {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D) [f.IsContinuous J K]
    [(f.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint] :
    Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w} :=
  f.sheafPullback AddCommGrpCat.{w} J K

end Stacks.Cohomology

end
