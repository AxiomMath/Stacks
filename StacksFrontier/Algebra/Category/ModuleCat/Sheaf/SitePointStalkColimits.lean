module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits

/-!
# The stalk at a point of a site commutes with colimits of sheaves of modules

Let `(C, J)` be a site, `Φ` a point of it and `R` a sheaf of rings on `C`. The stalk functor
`Stacks.sheafModuleFiber Φ R` preserves all colimits indexed by a shape in `Type 0` — in
particular all countable direct sums, which is the form in which "direct sums commute with
taking stalks" is used in the stalk criterion for K-flatness (Stacks 0DEN): the degree-`n`
term of a total tensor complex is a direct sum indexed by the antidiagonal
`{(p, q) : ℤ × ℤ // p + q = n}`, a type in `Type 0`.

## Main results

* `Stacks.preservesColimits_sheafModuleFiber`: the stalk functor on sheaves of modules
  preserves colimits of every shape in `Type 0`.
* `Stacks.preservesColimits_sheafModuleFiberOfCommRing`: the same over the `CommRingCat`-valued
  stalk of a sheaf of commutative rings.

## Implementation notes

Right exactness of the stalk functor on *sheaves* of modules does not come from the presheaf
level by restriction, because `SheafOfModules.forget` is a right adjoint; nor is finite right
exactness enough here, the antidiagonal being infinite. The argument instead reflects along
`forget₂ (ModuleCat _) AddCommGrpCat`, and uses the one equation that makes everything in this
area cheap: `Stacks.sheafModuleFiberCompForget₂`, which says that the stalk of a sheaf of
modules has as its underlying abelian group the stalk of the underlying abelian sheaf, and
which holds by definition. The composite it is identified with is
`SheafOfModules.toSheaf R ⋙ Φ.sheafFiber`, and both factors preserve colimits: the first by
`AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits` (Stacks 03DB), the second because
`Φ.sheafFiber` is a left adjoint, of the skyscraper sheaf functor.

The size of the colimits is cut down to `Type 0` on both sides, because that is where the
antidiagonal lives and because the two inputs come at different sizes: `toSheaf_preservesColimits`
is stated at `PreservesColimitsOfSize.{max u w, w}` and `Φ.sheafFiber`'s adjunction at the site's
own size. `preservesSmallestColimits_of_preservesColimits` is applied with its instance argument
passed explicitly rather than left to search: with two candidate sizes in context, search leaves
the universe variables of its hypothesis undetermined and the declaration is then rejected for
universe metavariables.

## References

* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The stalk of a sheaf of modules at a point of a site commutes with colimits.** The
colimits are those indexed by a shape in `Type 0`, which covers the countable direct sums
occurring as the terms of a total complex. -/
noncomputable instance preservesColimits_sheafModuleFiber (Φ : J.Point.{w}) :
    PreservesColimitsOfSize.{0, 0} (sheafModuleFiber Φ R) := by
  have h0 : PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{w} R) :=
    have hsize : PreservesColimitsOfSize.{max u w, w} (SheafOfModules.toSheaf.{w} R) :=
      inferInstance
    @preservesSmallestColimits_of_preservesColimits _ _ _ _ (SheafOfModules.toSheaf.{w} R) hsize
  have hcomp : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.toSheaf.{w} R ⋙ Φ.sheafFiber (A := AddCommGrpCat.{w})) := inferInstance
  have hforget : PreservesColimitsOfSize.{0, 0} (sheafModuleFiber Φ R ⋙
      forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R.obj))
        AddCommGrpCat.{w}) :=
    preservesColimits_of_natIso (sheafModuleFiberCompForget₂ Φ R).symm
  have hreflects : ReflectsColimitsOfSize.{0, 0}
      (forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R.obj))
        AddCommGrpCat.{w}) := reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R.obj))
      AddCommGrpCat.{w})

/-- The stalk functor over the `CommRingCat`-valued stalk of a sheaf of commutative rings
commutes with colimits: the extra factor is restriction of scalars along the comparison of the
two stalk rings, which preserves colimits. -/
noncomputable instance preservesColimits_sheafModuleFiberOfCommRing (Φ : J.Point.{w})
    (O : Sheaf J CommRingCat.{w}) [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    PreservesColimitsOfSize.{0, 0} (sheafModuleFiberOfCommRing Φ O) := by
  change PreservesColimitsOfSize.{0, 0}
    (sheafModuleFiber Φ (commRingSheafToRingSheaf O) ⋙
      ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom)
  infer_instance

end Stacks

end
