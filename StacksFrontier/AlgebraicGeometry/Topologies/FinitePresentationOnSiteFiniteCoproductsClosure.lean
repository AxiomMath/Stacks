module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePresentationOpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteFiniteCoproducts

/-!
# Finite presentation of sheaves of modules is closed under finite coproducts

A zero sheaf of modules is of finite presentation
(`SheafOfModules.IsFinitePresentationOnSite.of_isZero`), so, with closure under binary
coproducts (`SheafOfModules.isFinitePresentationOnSite_isClosedUnderBinaryCoproducts`), the
property is closed under all finite coproducts.

These live apart from
`StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteFiniteCoproducts`: the import
of `StacksFrontier.AlgebraicGeometry.Spaces.ModulePresentationOpenCover`, which states
`SheafOfModules.IsFinitePresentationOnSite.of_isZero`, brings into scope an
`Abelian (SheafOfModules.{max u v r w} O)` instance at which the universe unifier gets stuck while
elaborating the binary coproduct instance.

## Main results

* `SheafOfModules.isFinitePresentationOnSite_isClosedUnderFiniteCoproducts`
* `SheafOfModules.isFinitePresentationOnSite_coproduct`: a finite direct sum of sheaves of modules
  of finite presentation is of finite presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Finite presentation of sheaves of modules contains a zero object. -/
instance isFinitePresentationOnSite_containsZero [HasZeroObject (SheafOfModules.{m} R)] :
    (isFinitePresentationOnSite.{u, v, w, m} R).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := SheafOfModules.{m} R)
    exact ⟨Z, hZ, IsFinitePresentationOnSite.of_isZero hZ⟩

/-- Finite presentation of sheaves of modules is closed under finite coproducts. -/
instance isFinitePresentationOnSite_isClosedUnderFiniteCoproducts
    [Balanced (SheafOfModules.{w} R)] [HasZeroObject (SheafOfModules.{w} R)]
    [HasFiniteCoproducts (SheafOfModules.{w} R)] :
    (isFinitePresentationOnSite.{u, v, w, w} R).IsClosedUnderFiniteCoproducts :=
  ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- **A finite direct sum of sheaves of modules of finite presentation is of finite
presentation.** -/
theorem isFinitePresentationOnSite_coproduct [Balanced (SheafOfModules.{w} R)]
    [HasZeroObject (SheafOfModules.{w} R)] [HasFiniteCoproducts (SheafOfModules.{w} R)]
    {ι : Type*} [Finite ι] (F : ι → SheafOfModules.{w} R) [HasCoproduct F]
    (h : ∀ i, (F i).IsFinitePresentationOnSite) : (∐ F).IsFinitePresentationOnSite :=
  ObjectProperty.prop_coproduct (isFinitePresentationOnSite.{u, v, w, w} R) h

end SheafOfModules
