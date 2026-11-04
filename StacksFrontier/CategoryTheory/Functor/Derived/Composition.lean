module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksFrontier.CategoryTheory.Localization.Saturated.Closure

@[expose] public section

set_option backward.isDefEq.respectTransparency false
-- The triangulated/exact structure on all categories, functors and the
-- multiplicative systems is part of the mathematical setup (Definition 4); some
-- of these section hypotheses are not literally consumed by the bookkeeping
-- factorization lemmas, so we silence the unused-section-variable linter.
set_option linter.unusedSectionVars false

/-
# Problem Description

This is Stacks Project Lemma 13.14.16 (Tag [05T2]), on the comparison map between
the derived functor of a composition and the composition of derived functors, in
the general setting of Section 13.14 ("Derived functors in general").

Throughout, all categories are triangulated and all functors between them are
*exact functors* of triangulated categories (additive functors commuting with the
shift up to natural isomorphism and sending distinguished triangles to
distinguished triangles).  A *multiplicative system* `S` in a triangulated
category that is *compatible with the triangulated structure* and *saturated* is
as in Tags [04VB] and [05Q8]: it satisfies the left/right calculus-of-fractions
axioms MS1--MS3 together with the triangulated compatibility axioms MS5--MS6, and
the saturation condition that any morphism becoming invertible in `S⁻¹D` already
lies in `S`.  We write `Q : D ⥤ S⁻¹D` for the localization functor; it is an
exact functor of triangulated categories sending every element of `S` to an
isomorphism.

## Mathlib framing of the derived functor (Tags 05S8, 05S9, 05SE, 05SV)

In the Stacks Project, the (everywhere-defined) right derived functor `RF` of an
exact functor `F : D ⥤ D'` with respect to a saturated multiplicative system `S`
is built object-by-object as the value of the essentially constant ind-object
`(s : X ⟶ X') ↦ F(X')` over the filtered category `X/S` (Definition 13.14.2,
Tag [05S9]), and then (Proposition 13.14.8, Tag [05SE]) assembled into an exact
functor `RF : S⁻¹D ⥤ D'` characterized on morphisms by Lemma 13.14.3 (Tag
[05SA]).

Mathlib formalizes exactly this everywhere-defined derived functor through its
*universal property*: for a localization functor `L : C ⥤ D` of `W`, a functor
`RF : D ⥤ H` together with a natural transformation `α : F ⟶ L ⋙ RF` is *the*
right derived functor of `F` iff `(RF, α)` is the *left Kan extension* of `F`
along `L` (`CategoryTheory.Functor.IsRightDerivedFunctor`).  This is equivalent to
the Stacks essentially-constant-ind-object description: the colimit
`colim_{s : X ⟶ X'} F(X')` is precisely the value of the pointwise left Kan
extension, and the structure map `F(X) ⟶ RF(X)` is the component `α.app X` of the
unit.  Dually, the everywhere-defined left derived functor `LF` is the *right Kan
extension* of `F` along `L` (`CategoryTheory.Functor.IsLeftDerivedFunctor`), with
counit `α : L ⋙ LF ⟶ F` whose component `α.app X` is the canonical map
`LF(X) ⟶ F(X)`.

We adopt this Mathlib framing.  It is strictly stronger than (and determines) the
Stacks essentially-constant description, since the universal property pins the
derived functor down up to unique isomorphism, and it lets us construct the
comparison map `t` of Lemma 13.14.16 as an actual canonical natural
transformation rather than asserting mere existence.

## The data of the composition lemma (Definition 4)

Let `A, B, C` be triangulated categories.  Let `S` (resp. `S'`) be a saturated
multiplicative system in `A` (resp. `B`) compatible with the triangulated
structure, with localization functors `Q_A : A ⥤ S⁻¹A` and `Q_B : B ⥤ S'⁻¹B`.
Let `F : A ⥤ B` and `G : B ⥤ C` be exact functors.  Set `F' = Q_B ∘ F`.  We
consider three derived-functor situations:

* `F' : A ⥤ S'⁻¹B` with system `S`, giving `RF', LF' : S⁻¹A ⥤ S'⁻¹B`;
* `G ∘ F : A ⥤ C` with system `S`, giving `R(G∘F), L(G∘F) : S⁻¹A ⥤ C`;
* `G : B ⥤ C` with system `S'`, giving `RG, LG : S'⁻¹B ⥤ C`.

## Main statements

* Statement 1 (right derived): if `RF'`, `RG`, `R(G∘F)` are everywhere defined,
  there is a canonical natural transformation `t : R(G∘F) ⟶ RG ∘ RF'`, whose
  component at `Q_A X` is the composite
  `R(G∘F)(Q_A X) = colim G(F X')  ⟶  colim RG(Q_B(F X')) = RG(RF'(X))`
  induced by the canonical map `t' : G ⟶ RG ∘ Q_B`.

* Statement 2 (left derived): dually `t : LG ∘ LF' ⟶ L(G∘F)`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace DerivedFunctorComposition

/-! ## The data of the composition lemma (Stacks Definition 4, Tag 05T2)

We work with three triangulated categories `A`, `B`, `C` (in possibly different
universes), saturated multiplicative systems `S` on `A` and `S'` on `B`
compatible with the triangulated structure, the corresponding triangulated
localizations `Q_A : A ⥤ LocA` and `Q_B : B ⥤ LocB`, and exact (triangulated)
functors `F : A ⥤ B`, `G : B ⥤ C`. -/

variable
  {A : Type u₁} [Category.{v₁} A] [Preadditive A] [HasZeroObject A] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A] [IsTriangulated A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
  {C : Type u₃} [Category.{v₃} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  -- saturated multiplicative systems compatible with the triangulated structure
  (S : MorphismProperty A)
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    [S.IsCompatibleWithTriangulation] (hS : S.IsSaturated)
  (S' : MorphismProperty B)
    [S'.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [S'.IsCompatibleWithTriangulation] (hS' : S'.IsSaturated)
  -- the localized categories, equipped with their triangulated structure
  {LocA : Type u₄} [Category.{v₄} LocA] [Preadditive LocA] [HasZeroObject LocA]
    [HasShift LocA ℤ] [∀ n : ℤ, (shiftFunctor LocA n).Additive]
    [Pretriangulated LocA] [IsTriangulated LocA]
  {LocB : Type u₅} [Category.{v₅} LocB] [Preadditive LocB] [HasZeroObject LocB]
    [HasShift LocB ℤ] [∀ n : ℤ, (shiftFunctor LocB n).Additive]
    [Pretriangulated LocB] [IsTriangulated LocB]
  -- the triangulated localization functors `Q_A`, `Q_B`
  (QA : A ⥤ LocA) [QA.IsLocalization S] [QA.CommShift ℤ] [QA.Additive] [QA.IsTriangulated]
  (QB : B ⥤ LocB) [QB.IsLocalization S'] [QB.CommShift ℤ] [QB.Additive] [QB.IsTriangulated]
  -- the exact functors `F`, `G`
  (F : A ⥤ B) [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
  (G : B ⥤ C) [G.CommShift ℤ] [G.Additive] [G.IsTriangulated]

/-- Stacks Definition 4 (Tag 05T2): the exact functor `F' = Q_B ∘ F : A ⥤ S'⁻¹B`. -/
noncomputable abbrev Fprime : A ⥤ LocB := F ⋙ QB

/-! ## Statement 1: right derived functors (Tag 05T2)

We are given everywhere-defined right derived functors, packaged through their
universal property `IsRightDerivedFunctor` (left Kan extension along the
localization):

* `RFp : LocA ⥤ LocB` of `F' = Q_B ∘ F`, with unit `αFp : F' ⟶ Q_A ⋙ RFp`;
* `RG : LocB ⥤ C` of `G`, with unit `αG : G ⟶ Q_B ⋙ RG`
  (the component `αG.app Y : G(Y) ⟶ RG(Q_B Y)` is the canonical map `t'` of the
  problem statement);
* `RGF : LocA ⥤ C` of `G ∘ F`, with unit `αGF : (F ⋙ G) ⟶ Q_A ⋙ RGF`. -/

variable
  (RFp : LocA ⥤ LocB) (RG : LocB ⥤ C) (RGF : LocA ⥤ C)
  (αFp : Fprime QB F ⟶ QA ⋙ RFp) (αG : G ⟶ QB ⋙ RG)
  (αGF : (F ⋙ G) ⟶ QA ⋙ RGF)

/-- The natural transformation `β : F ⋙ G ⟶ Q_A ⋙ (RFp ⋙ RG)` underlying the
comparison map of Statement 1.  It is the composite
`F ⋙ G  ⟶  F ⋙ (Q_B ⋙ RG) = (F ⋙ Q_B) ⋙ RG = F' ⋙ RG  ⟶  (Q_A ⋙ RFp) ⋙ RG
   = Q_A ⋙ (RFp ⋙ RG)`,
built from `αG` (the canonical map `G ⟶ RG ∘ Q_B`) whiskered by `F`, followed by
`αFp` (the unit of `RF'`) whiskered by `RG`.  This is precisely the "concrete"
construction `colim G(F X') ⟶ colim RG(Q_B(F X')) = RG(RF'(X))` of Tag 05T2. -/
noncomputable def rightComparisonUnit : (F ⋙ G) ⟶ QA ⋙ (RFp ⋙ RG) :=
  whiskerLeft F αG ≫ (Functor.associator F QB RG).inv ≫
    whiskerRight αFp RG ≫ (Functor.associator QA RFp RG).hom

/-- **Stacks Lemma 13.14.16, Statement 1 (Tag 05T2): the canonical comparison
natural transformation `t : R(G∘F) ⟶ RG ∘ RF'`.**

Assuming the right derived functors `RF'`, `RG`, `R(G∘F)` are everywhere defined
(encoded by the `IsRightDerivedFunctor` instances), the comparison `t` is defined
using the universal property of `R(G∘F)` as the left Kan extension of `F ⋙ G`
along `Q_A`: it is the unique descent of the natural transformation
`rightComparisonUnit` through the unit `αGF`. -/
noncomputable def rightComparison
    [RFp.IsRightDerivedFunctor αFp S] [RG.IsRightDerivedFunctor αG S']
    [RGF.IsRightDerivedFunctor αGF S] :
    RGF ⟶ RFp ⋙ RG :=
  haveI : RGF.IsLeftKanExtension αGF := IsRightDerivedFunctor.isLeftKanExtension RGF αGF S
  RGF.descOfIsLeftKanExtension αGF (RFp ⋙ RG)
    (rightComparisonUnit (QA := QA) (QB := QB) (F := F) (G := G) (RFp := RFp) (RG := RG) αFp αG)

/-- **Stacks Lemma 13.14.16, Statement 1 (Tag 05T2).**
Assume the data of Definition 4 and that the right derived functors `RF'`, `RG`
and `R(G∘F)` are everywhere defined.  Then there exists a natural transformation
`t : R(G∘F) ⟶ RG ∘ RF'` of functors `S⁻¹A ⥤ C` which is characterized at each
object `Q_A X` by the concrete composite of Tag 05T2: precomposing the component
`t_{Q_A X}` with the structure map `αGF.app X : (G∘F)(X) ⟶ R(G∘F)(Q_A X)` yields
the canonical map `G(F X) ⟶ RG(Q_B(F X))` followed by `RG` applied to the
structure map `αFp.app X` of `RF'`. -/
@[stacks 05T2 "(1)"]
theorem exists_rightDerived_comparison
    [RFp.IsRightDerivedFunctor αFp S] [RG.IsRightDerivedFunctor αG S']
    [RGF.IsRightDerivedFunctor αGF S] :
    ∃ t : RGF ⟶ RFp ⋙ RG,
      ∀ X : A, αGF.app X ≫ t.app (QA.obj X) = αG.app (F.obj X) ≫ RG.map (αFp.app X) := by
  have : RGF.IsLeftKanExtension αGF := IsRightDerivedFunctor.isLeftKanExtension RGF αGF S
  refine ⟨rightComparison S S' QA QB F G RFp RG RGF αFp αG αGF, fun X => ?_⟩
  simp [rightComparison, rightComparisonUnit]

/-! ## Statement 2: left derived functors (Tag 05T2)

Dually, everywhere-defined left derived functors are packaged through their
universal property `IsLeftDerivedFunctor` (right Kan extension along the
localization):

* `LFp : LocA ⥤ LocB` of `F'`, with counit `βFp : Q_A ⋙ LFp ⟶ F'`;
* `LG : LocB ⥤ C` of `G`, with counit `βG : Q_B ⋙ LG ⟶ G`
  (the component `βG.app Y : LG(Q_B Y) ⟶ G(Y)` is the canonical map of the
  problem statement);
* `LGF : LocA ⥤ C` of `G ∘ F`, with counit `βGF : Q_A ⋙ LGF ⟶ (F ⋙ G)`. -/

variable
  (LFp : LocA ⥤ LocB) (LG : LocB ⥤ C) (LGF : LocA ⥤ C)
  (βFp : QA ⋙ LFp ⟶ Fprime QB F) (βG : QB ⋙ LG ⟶ G)
  (βGF : QA ⋙ LGF ⟶ (F ⋙ G))

/-- The natural transformation `β : Q_A ⋙ (LFp ⋙ LG) ⟶ F ⋙ G` underlying the
comparison map of Statement 2.  It is the composite
`Q_A ⋙ (LFp ⋙ LG) = (Q_A ⋙ LFp) ⋙ LG  ⟶  (F ⋙ Q_B) ⋙ LG = F ⋙ (Q_B ⋙ LG)
   ⟶  F ⋙ G`,
built from `βFp` (the counit of `LF'`) whiskered by `LG`, followed by `βG` (the
canonical map `LG ∘ Q_B ⟶ G`) whiskered by `F`.  This is the dual of
`rightComparisonUnit`. -/
noncomputable def leftComparisonCounit : QA ⋙ (LFp ⋙ LG) ⟶ (F ⋙ G) :=
  (Functor.associator QA LFp LG).inv ≫ whiskerRight βFp LG ≫
    (Functor.associator F QB LG).hom ≫ whiskerLeft F βG

/-- **Stacks Lemma 13.14.16, Statement 2 (Tag 05T2): the canonical comparison
natural transformation `t : LG ∘ LF' ⟶ L(G∘F)`.**

Assuming the left derived functors `LF'`, `LG`, `L(G∘F)` are everywhere defined
(encoded by the `IsLeftDerivedFunctor` instances), the comparison `t` is defined
using the universal property of `L(G∘F)` as the right Kan extension of `F ⋙ G`
along `Q_A`: it is the unique lift of `leftComparisonCounit` through the counit
`βGF`. -/
noncomputable def leftComparison
    [LFp.IsLeftDerivedFunctor βFp S] [LG.IsLeftDerivedFunctor βG S']
    [LGF.IsLeftDerivedFunctor βGF S] :
    LFp ⋙ LG ⟶ LGF :=
  haveI : LGF.IsRightKanExtension βGF := IsLeftDerivedFunctor.isRightKanExtension LGF βGF S
  LGF.liftOfIsRightKanExtension βGF (LFp ⋙ LG)
    (leftComparisonCounit (QA := QA) (QB := QB) (F := F) (G := G) (LFp := LFp) (LG := LG) βFp βG)

/-- **Stacks Lemma 13.14.16, Statement 2 (Tag 05T2).**
Dually to Statement 1: assume the data of Definition 4 and that the left derived
functors `LF'`, `LG` and `L(G∘F)` are everywhere defined.  Then there exists a
natural transformation `t : LG ∘ LF' ⟶ L(G∘F)` of functors `S⁻¹A ⥤ C`,
characterized at each object `Q_A X` by the concrete dual composite of Tag 05T2:
postcomposing the component `t_{Q_A X}` with the structure map
`βGF.app X : L(G∘F)(Q_A X) ⟶ (G∘F)(X)` yields `LG` applied to the structure map
`βFp.app X` of `LF'` followed by the canonical map `LG(Q_B(F X)) ⟶ G(F X)`. -/
@[stacks 05T2 "(2)"]
theorem exists_leftDerived_comparison
    [LFp.IsLeftDerivedFunctor βFp S] [LG.IsLeftDerivedFunctor βG S']
    [LGF.IsLeftDerivedFunctor βGF S] :
    ∃ t : LFp ⋙ LG ⟶ LGF,
      ∀ X : A, t.app (QA.obj X) ≫ βGF.app X = LG.map (βFp.app X) ≫ βG.app (F.obj X) := by
  have : LGF.IsRightKanExtension βGF := IsLeftDerivedFunctor.isRightKanExtension LGF βGF S
  refine ⟨leftComparison S S' QA QB F G LFp LG LGF βFp βG βGF, fun X => ?_⟩
  simp [leftComparison, leftComparisonCounit]

end DerivedFunctorComposition
