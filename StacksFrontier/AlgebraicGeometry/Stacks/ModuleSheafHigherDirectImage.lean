module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality

/-!
# Higher direct images of sheaves of modules on fibred categories

A 1-morphism `f : 𝒳 ⥤ 𝒴` of categories fibred in groupoids over the big fppf category of a
scheme `S` induces an adjoint pair of inverse- and direct-image functors on sheaves of modules
over the structure sheaves of Stacks 06TV, for each of the associated topologies of Stacks 06TP;
that is Stacks 06WE, available as `AlgebraicGeometry.Stack.modulePullback` and
`AlgebraicGeometry.Stack.moduleSheafPushforward`. This file constructs the *higher* direct
images `R^i f_*` of sheaves of modules as the right derived functors of the direct image.

Three things are needed for the right derived functors to exist, and each is supplied here. The
direct image is additive, being a right adjoint whose left adjoint is additive — and the left
adjoint is objectwise restriction along `f`, so its additivity holds on the nose. The source
category is abelian, which is Mathlib's instance for sheaves of modules. And the source category
has enough injectives, which is
`SheafOfModules.enoughInjectives_of_univLE` at the associated topology: the site, its homs and
the structure rings all inject into the module universe, which is the one the direct image needs
anyway.

In degree zero nothing new appears: the direct image is a right adjoint, hence preserves finite
limits, so `R^0 f_*` is `f_*`.

## Main definitions

* `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`: the higher direct image `R^i f_*` of
  sheaves of modules along a 1-morphism of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.additive_modulePullback` and
  `AlgebraicGeometry.Stack.additive_moduleSheafPushforward`: the two functors of Stacks 06WE are
  additive.
* `AlgebraicGeometry.Stack.enoughInjectives_moduleSheaves`: sheaves of modules over the
  structure sheaf of a category fibred in groupoids have enough injectives.
* `AlgebraicGeometry.Stack.preservesFiniteLimits_moduleSheafPushforward`: the direct image
  preserves finite limits.
* `AlgebraicGeometry.Stack.moduleSheafHigherDirectImageZeroIso`: `R^0 f_* = f_*`.

## Implementation notes

The module universe of the higher direct image is `max u v w v' w'`, the one in which the direct
image of Stacks 06WE is constructed: its limits are indexed by the two sites, so no smaller
universe is available. Enough injectives, by contrast, needs only that the site, its homs and
the structure rings inject into the module universe, so it is stated at an independent universe
`m` under those three `UnivLE` hypotheses and applied at `max u v w v' w'`.

Sheafification of abelian sheaves at that module universe is a hypothesis rather than a
theorem, exactly as in `AlgebraicGeometry.Stack.derivedPresheafDirectImage` for abelian sheaves:
the associated topology lives on a category whose objects and morphisms are in unrelated
universes, and the two conditions are what the abelian structure on sheaves of modules is built
from. They hold for the sites of the source's five topologies on a category fibred in groupoids
over `(Sch/S)_fppf`.

Additivity of the inverse image is proved by `rfl` on morphisms: by
`AlgebraicGeometry.Stack.modulePullback_obj_val_presheaf` the functor is precomposition with
`f.op` followed by a transport of scalars along an equality of presheaves of rings, and neither
step changes the addition of a morphism of presheaves of modules.

No tag is recorded. The higher direct image of modules on the sites of a stack is not itself an
assertion of the source; it is the functor whose statements the source makes, Stacks 075Z, 0764
and 076Z among them.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w v' w' m

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The inverse image of sheaves of modules of Stacks 06WE is additive: it is precomposition
with `f.op` followed by a transport of scalars along an equality of presheaves of rings, and
neither changes the addition of a morphism. -/
instance additive_modulePullback :
    (modulePullback.{u, v, w, max u v w v' w', v', w'} B S hS p q hp hq f hf τ hτ).Additive where
  map_add := by intros; rfl

/-- The direct image of sheaves of modules of Stacks 06WE is additive, being a right adjoint
with an additive left adjoint. -/
instance additive_moduleSheafPushforward :
    (moduleSheafPushforward.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ).Additive :=
  (moduleSheafAdjunction.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ).right_adjoint_additive

/-- The direct image of sheaves of modules of Stacks 06WE preserves finite limits, being a right
adjoint. -/
instance preservesFiniteLimits_moduleSheafPushforward :
    PreservesFiniteLimits
      (moduleSheafPushforward.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ) :=
  have : PreservesLimits
      (moduleSheafPushforward.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ) :=
    (moduleSheafAdjunction.{u, v, w, u, v', w'}
      B S hS p q hp hq f hf τ hτ).rightAdjoint_preservesLimits
  inferInstance

section Injectives

variable [UnivLE.{u, m}] [UnivLE.{v, m}] [UnivLE.{w, m}]
  [HasWeakSheafify (associatedTopology B S hS p τ) AddCommGrpCat.{m}]
  [(associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Sheaves of modules over the structure sheaf of Stacks 06TV have enough injectives in every
module universe into which the site, its homs and the structure rings inject. -/
theorem enoughInjectives_moduleSheaves :
    EnoughInjectives (SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ)) :=
  SheafOfModules.enoughInjectives_of_univLE.{m, w, v, u} _

end Injectives

section HigherDirectImage

variable [HasWeakSheafify (associatedTopology B S hS p τ) AddCommGrpCat.{max u v w v' w'}]
  [(associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{max u v w v' w'}]
  [HasWeakSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{max u v w v' w'}]
  [(associatedTopology B S hS q τ).WEqualsLocallyBijective AddCommGrpCat.{max u v w v' w'}]

/-- The higher direct image `R^i f_*` of sheaves of modules along a 1-morphism of categories
fibred in groupoids: the `i`-th right derived functor of the direct image of Stacks 06WE. -/
noncomputable def moduleSheafHigherDirectImage (i : ℕ) :
    SheafOfModules.{max u v w v' w'} (ringStructureSheafCore B S hS p hp τ hτ) ⥤
      SheafOfModules.{max u v w v' w'} (ringStructureSheafCore B S hS q hq τ hτ) :=
  letI : EnoughInjectives
      (SheafOfModules.{max u v w v' w'} (ringStructureSheafCore B S hS p hp τ hτ)) :=
    enoughInjectives_moduleSheaves.{u, v, w, max u v w v' w'} B S hS p hp τ hτ
  (moduleSheafPushforward.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ).rightDerived i

/-- `R^0 f_* = f_*`: the direct image is left exact, so its zeroth right derived functor is
itself. -/
noncomputable def moduleSheafHigherDirectImageZeroIso :
    moduleSheafHigherDirectImage B S hS p q hp hq f hf τ hτ 0 ≅
      moduleSheafPushforward.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ :=
  letI : EnoughInjectives
      (SheafOfModules.{max u v w v' w'} (ringStructureSheafCore B S hS p hp τ hτ)) :=
    enoughInjectives_moduleSheaves.{u, v, w, max u v w v' w'} B S hS p hp τ hτ
  (moduleSheafPushforward.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ).rightDerivedZeroIsoSelf

end HigherDirectImage

end AlgebraicGeometry.Stack

end
