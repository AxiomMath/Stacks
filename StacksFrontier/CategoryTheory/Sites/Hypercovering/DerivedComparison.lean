module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic

/-!
# The complex of a hypercovering and derived sections

Let `K` be a hypercovering of an object `X` of a site. Evaluating a sheaf of abelian groups on the
levels of `K` gives a cosimplicial abelian group and hence a nonnegative cochain complex `s(F(K))`.
This file constructs that complex and the derived sections `RΓ(X, -)`, as functors of the sheaf
with values in the bounded below derived category of abelian groups.

## Main definitions

* `hypercoverCochainFunctor` is the bounded-below complex `s(F(K))`, functorial in `F`.
* `derivedSectionsFunctor` is `RΓ(X, -)` with values in `D⁺(Ab)`.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits DerivedCategory.Plus Opposite

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : Pretopology C) (X : C)

/-- The restriction of an abelian sheaf on `C` to objects over `X`. -/
def sectionsOnOverFunctor :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
      (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⋙
    (Functor.whiskeringLeft _ _ _).obj (Over.forget X).op

/-- Evaluating sheaves on a simplicial formal coproduct and taking alternating cofaces gives the
nonnegative complex `s(F(K))`. -/
def hypercoverCochainNatFunctor
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  sectionsOnOverFunctor J X ⋙
    FormalCoproduct.cochainComplexFunctor (A := AddCommGrpCat.{max u v w}) K

/-- The complex `s(F(K))`, extended by zero to integer degrees. -/
def hypercoverCochainIntFunctor
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℤ :=
  hypercoverCochainNatFunctor J X K ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w}

/-- The bounded-below complex `s(F(K))`, functorial in the abelian sheaf `F`. -/
def hypercoverCochainFunctor
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
      CochainComplex.Plus AddCommGrpCat.{max u v w} :=
  ObjectProperty.lift _ (hypercoverCochainIntFunctor J X K) (fun F ↦ ⟨0, by
    change CochainComplex.IsStrictlyGE
      (((hypercoverCochainNatFunctor J X K).obj F).extend ComplexShape.embeddingUpNat) 0
    infer_instance⟩)

/-- The functor of sections of an abelian sheaf on `X`. -/
def sheafSectionsFunctor :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤ AddCommGrpCat.{max u v w} :=
  sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{max u v w}).obj (op X)

/-- Taking sections of abelian sheaves is additive. -/
instance sheafSectionsFunctor_additive : (sheafSectionsFunctor J X).Additive := by
  dsimp [sheafSectionsFunctor]
  infer_instance

/-- The complex `s(F(K))` regarded as an object of `D⁺(Ab)`, functorially in `F`. -/
def hypercoverDerivedFunctor
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
      DerivedCategory.Plus AddCommGrpCat.{max u v w} :=
  hypercoverCochainFunctor J X K ⋙ DerivedCategory.Plus.Q

/-- The bounded-below derived sections functor `RΓ(X, -)`. -/
def derivedSectionsFunctor
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})] :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
      DerivedCategory.Plus AddCommGrpCat.{max u v w} :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙ (sheafSectionsFunctor J X).rightDerivedFunctorPlus

end Stacks.CategoryTheory.Hypercovering

end
