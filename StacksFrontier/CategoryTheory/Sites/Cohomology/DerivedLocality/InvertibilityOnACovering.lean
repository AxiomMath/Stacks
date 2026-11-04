module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact

/-!
# Invertibility in the derived category of modules is local on a covering family

Let `R` be a sheaf of rings on a site `(C, J)` and let `Y : ι → C` be a family of objects
covering the final object. A morphism of `D(R)` is invertible as soon as its restriction to the
slice site over each `Y i` is invertible.

`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over` is the same statement one level
down, for a morphism of sheaves of modules rather than of the derived category. The passage
between the two levels is `CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`, which
rewrites invertibility of `(overFunctor R (Y i)).mapDerivedCategory.map f` as invertibility of
the restrictions of all the homology maps of `f`; restriction to a slice is exact
(`SheafOfModules.overFunctor_preservesFiniteLimits` and
`SheafOfModules.overFunctor_preservesFiniteColimits`), which is what makes that rewrite
available.

## Main results

* `Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor`: invertibility in the
  derived category of modules on a site is local on a covering family.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v₁ u₁ u

namespace Stacks.Cohomology

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (SheafOfModules.{u} R)]

/-- **Invertibility in the derived category of modules is local on a covering family.** If
`Y : ι → C` covers the final object of the site and the restriction of `f : E ⟶ F` to the slice
site over each `Y i` is invertible in the derived category there, then `f` is invertible. -/
theorem isIso_of_isIso_mapDerivedCategory_overFunctor
    {ι : Type*} {Y : ι → C} (hY : J.CoversTop Y)
    [∀ i, HasSheafify (J.over (Y i)) AddCommGrpCat.{u}]
    [∀ i, (J.over (Y i)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ i, HasDerivedCategory.{w} (SheafOfModules.{u} (R.over (Y i)))]
    [∀ i, (SheafOfModules.overFunctor.{u} R (Y i)).Additive]
    {E F : DerivedCategory (SheafOfModules.{u} R)} (f : E ⟶ F)
    (h : ∀ i, IsIso ((SheafOfModules.overFunctor.{u} R (Y i)).mapDerivedCategory.map f)) :
    IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hY _ fun i ↦ ?_
  exact ((SheafOfModules.overFunctor.{u} R (Y i)).isIso_mapDerivedCategory_map_iff f).mp (h i) n

end Stacks.Cohomology

end
