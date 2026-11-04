module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the stalk functor on abelian sheaves and presheaves

Let `(C, J)` be a site and `Φ` a point of it. This file records Stacks 04EP: taking the stalk
at `Φ` is an exact functor `Ab(C) ⥤ Ab` on abelian sheaves, and `PAb(C) ⥤ Ab` on abelian
presheaves, and sheafification of an abelian presheaf does not change its stalk.

## Main results

* `Stacks.exactFunctor_abelianSheafFiber`: part (1), the stalk functor on abelian sheaves is
  exact.
* `Stacks.exactFunctor_abelianPresheafFiber`: part (2), the stalk functor on abelian presheaves
  is exact.
* `Stacks.isIso_abelianPresheafFiber_map_toSheafify`: part (3), the canonical map
  `F_p ⟶ (F^#)_p` is an isomorphism.

## Implementation notes

A point of the site is Mathlib's `CategoryTheory.GrothendieckTopology.Point`, as in Stacks 04EN
(`StacksFrontier/CategoryTheory/Sites/Point/StalkPreservesFiniteLimits.lean`) and in the module
version Stacks 04EQ (`StacksFrontier/CategoryTheory/Sites/Point/ModuleStalkSheafExact.lean`). Its
stalk functor is a filtered colimit over the category of elements of the fibre functor, so it
is left exact because filtered colimits of abelian groups are exact (AB5), and right exact
because it commutes with all colimits. Part (3) is stated as the invertibility of the stalk of
the unit `F ⟶ F^#` of sheafification, which records that the identification of the source is
the canonical one.

## References

* [Stacks Project, Tag 04EP](https://stacks.math.columbia.edu/tag/04EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks

universe w v u

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w})

/-- **Stacks Project, Tag 04EP, part (1).** Taking the stalk at a point of a site is an exact
functor from abelian sheaves to abelian groups. -/
@[stacks 04EP "part (1)"]
theorem exactFunctor_abelianSheafFiber :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) AddCommGrpCat.{w}
      (Φ.sheafFiber (A := AddCommGrpCat.{w})) :=
  (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 04EP, part (2).** Taking the stalk at a point of a site is an exact
functor from abelian presheaves to abelian groups. -/
@[stacks 04EP "part (2)"]
theorem exactFunctor_abelianPresheafFiber :
    exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{w}) AddCommGrpCat.{w}
      (Φ.presheafFiber (A := AddCommGrpCat.{w})) :=
  (exactFunctor_iff _).mpr
    ⟨inferInstance, PreservesColimitsOfSize.preservesFiniteColimits _⟩

omit [LocallySmall.{w} C] in
/-- **Stacks Project, Tag 04EP, part (3).** Sheafification of an abelian presheaf `F` does not
change its stalk: the stalk at `Φ` of the canonical map `F ⟶ F^#` is an isomorphism
`F_p ≅ (F^#)_p`. -/
@[stacks 04EP "part (3)"]
theorem isIso_abelianPresheafFiber_map_toSheafify [HasWeakSheafify J AddCommGrpCat.{w}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    IsIso ((Φ.presheafFiber (A := AddCommGrpCat.{w})).map (toSheafify J F)) :=
  inferInstance

end Stacks
