module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Derived functors of linear functors are linear

Let `R` be a semiring, let `L : C ⥤ D` be an `R`-linear localization functor for a class of
morphisms `W` and let `F : C ⥤ H` be an `R`-linear functor between `R`-linear categories. A left
derived functor `LF : D ⥤ H` of `F` along `L` is `R`-linear. The right derived case is
`CategoryTheory.Functor.linear_of_isRightDerivedFunctor` of
`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedLinear.lean`, by the dual argument.

## The argument

A functor between `R`-linear categories is `R`-linear as soon as it carries the scalar
endomorphism `r • 𝟙 X` of every object to `r • 𝟙` (`CategoryTheory.Functor.linear_iff`). The
two families `X ↦ LF.map (r • 𝟙 X)` and `X ↦ r • 𝟙 (LF.obj X)` are natural transformations
`LF ⟶ LF`, because scalar endomorphisms commute with every morphism of an `R`-linear category.
A natural transformation into a left derived functor is determined by its composite with the
counit `α : L ⋙ LF ⟶ F` (`CategoryTheory.Functor.leftDerived_ext`), and the two composites agree:
at an object `X` of `C` both are `r • α.app X`, the first by naturality of `α` along
`r • 𝟙 X` together with the linearity of `L` and of `F`. The right derived case, proved in
`RightDerivedLinear.lean`, is dual, with `CategoryTheory.Functor.rightDerived_ext` and the unit.

## Main results

* `CategoryTheory.Functor.linear_of_isLeftDerivedFunctor`: a left derived functor of an
  `R`-linear functor along an `R`-linear localization is `R`-linear.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Category

variable (R : Type*) [Semiring R] {C D H : Type*} [Category* C] [Category* D] [Category* H]
  [Preadditive C] [Preadditive D] [Preadditive H] [CategoryTheory.Linear R C]
  [CategoryTheory.Linear R D] [CategoryTheory.Linear R H]

/-- In an `R`-linear category the scalar endomorphisms `r • 𝟙` form a natural transformation of
any functor into it. -/
@[simps]
def smulNatTrans (G : D ⥤ H) (r : R) : G ⟶ G where
  app X := r • 𝟙 (G.obj X)
  naturality X Y f := by simp

/-- The image under a functor of the scalar endomorphisms `r • 𝟙` of its source is a natural
transformation of that functor. -/
@[simps]
def mapSmulNatTrans (G : D ⥤ H) (r : R) : G ⟶ G where
  app X := G.map (r • 𝟙 X)
  naturality X Y f := by
    rw [← G.map_comp, ← G.map_comp, Linear.smul_comp, Linear.comp_smul, id_comp, comp_id]

variable {L : C ⥤ D} (W : MorphismProperty C) [L.IsLocalization W] [L.Linear R]
  {F : C ⥤ H} [F.Linear R]

/-- **A left derived functor of an `R`-linear functor along an `R`-linear localization is
`R`-linear.** -/
theorem linear_of_isLeftDerivedFunctor (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor α W] : LF.Linear R := by
  rw [linear_iff]
  intro X r
  have h := leftDerived_ext LF α W LF (mapSmulNatTrans R LF r) (smulNatTrans R LF r) (by
    ext Y
    simp only [comp_obj, NatTrans.comp_app, whiskerLeft_app, mapSmulNatTrans_app,
      smulNatTrans_app, Linear.smul_comp, id_comp]
    rw [← L.map_id, ← L.map_smul]
    have := α.naturality (r • 𝟙 Y)
    simp only [comp_obj, comp_map] at this
    rw [this, F.map_smul, F.map_id, Linear.comp_smul, comp_id])
  exact congrArg (fun τ : LF ⟶ LF => τ.app X) h

end CategoryTheory.Functor
