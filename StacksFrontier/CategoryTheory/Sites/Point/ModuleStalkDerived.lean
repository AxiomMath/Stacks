module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkSheafExact

/-!
# The derived stalk of a complex of sheaves of modules at a point of a site

Let `(C, J)` be a site, `Φ` a point of it and `O` a sheaf of commutative rings on `C`. Taking the
stalk at `Φ` is an exact functor `Mod(O) ⥤ Mod(O_Φ)` (Stacks 04EQ, part (1)), so it induces the
*derived stalk* `Stacks.derivedModuleFiber Φ O : D(O) ⥤ D(O_Φ)` on unbounded derived categories,
sending an object `E` of `D(O)` to `E_Φ`.

## Main definitions

* `Stacks.derivedModuleFiber`: the derived stalk functor `D(O) ⥤ D(O_Φ)`.

## Main results

* `Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing` and
  `Stacks.instAdditiveSheafModuleFiberOfCommRing`: the module-valued stalk functor preserves
  finite colimits and is additive.

## References

* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks

universe w v u d e

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-! The module-valued stalk functor at a point of a site preserves finite limits. -/
attribute [instance] preservesFiniteLimits_sheafModuleFiberOfCommRing

/-- The module-valued stalk functor at a point of a site preserves finite colimits. -/
noncomputable instance instPreservesFiniteColimitsSheafModuleFiberOfCommRing :
    PreservesFiniteColimits (sheafModuleFiberOfCommRing Φ O) :=
  ((exactFunctor_iff _).mp (exactFunctor_sheafModuleFiberOfCommRing Φ O)).2

/-- The module-valued stalk functor at a point of a site is additive. -/
instance instAdditiveSheafModuleFiberOfCommRing :
    (sheafModuleFiberOfCommRing Φ O).Additive :=
  Functor.additive_of_preserves_binary_products _

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (commRingSheafToRingSheaf O))]
  [HasDerivedCategory.{e}
    (ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj))]

/-- The derived stalk at a point of a site: the functor `D(O) ⥤ D(O_Φ)` induced by the exact
module-valued stalk functor, sending an object `E` of `D(O)` to `E_Φ`. -/
noncomputable abbrev derivedModuleFiber :
    DerivedCategory (SheafOfModules.{w} (commRingSheafToRingSheaf O)) ⥤
      DerivedCategory (ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj)) :=
  (sheafModuleFiberOfCommRing Φ O).mapDerivedCategory

end Stacks

end
