module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
import StacksCore.Tactic.StacksAttribute

/-! # Restriction of abelian sheaves along a continuous cocontinuous functor is exact

Let `H : C ⥤ D` be a functor of sites which is both continuous and cocontinuous. The
restriction `H_* : Ab(D) ⥤ Ab(C)` — the inverse image `g^{-1}` of the associated morphism of
topoi — is then exact, and its left adjoint `H^! = g_!` is additive whenever it exists.

Neither half is formal. Left exactness holds for every continuous functor and is
`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous` (Stacks 04J4). Right
exactness is where cocontinuity enters: restriction commutes with sheafification, hence
preserves all colimits indexed in the universe of the sections, which is
`Stacks.SheafOfModules.sheafPushforward_preservesColimits`. This file only puts the two
together, and records the additivity of a left adjoint of an additive functor, which is what
makes `g_!` applicable degreewise to complexes.

The module analogue of the exactness statement is
`Stacks.Cohomology.DerivedLowerShriek.restriction_exact`; this is the abelian-sheaf one, which
the forgetful squares of Stacks 08PC and 07AC need alongside it.

## Main results

* `CategoryTheory.Functor.additive_sheafPullback`: a left adjoint of restriction of sheaves in a
  preadditive category is additive.
* `CategoryTheory.Functor.exactFunctor_sheafPushforwardContinuous_of_isCocontinuous`:
  restriction of sheaves of abelian groups along a continuous cocontinuous functor of sites is
  exact.

## References

* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 0796](https://stacks.math.columbia.edu/tag/0796)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (H : C ⥤ D)
  [H.IsContinuous J K]

/-- A left adjoint of restriction of sheaves valued in a preadditive category is additive.
Restriction is additive by `CategoryTheory.Functor.additive_sheafPushforwardContinuous`, and a
left adjoint of an additive functor is additive. This is what lets the lower-shriek functor be
applied degreewise to complexes. -/
instance additive_sheafPullback (A : Type*) [Category* A] [Preadditive A]
    [(H.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    (H.sheafPullback A J K).Additive :=
  (H.sheafAdjunctionContinuous A J K).left_adjoint_additive

/-- **Restriction of abelian sheaves along a continuous cocontinuous functor of sites is
exact.** Left exactness holds for any continuous functor; right exactness is the preservation
of all colimits of `Stacks.SheafOfModules.sheafPushforward_preservesColimits`, which is where
cocontinuity is used. -/
@[sga "4 IV 11.2.2" "special case", sga "7 VI 3.1(a)" "special case"]
theorem exactFunctor_sheafPushforwardContinuous_of_isCocontinuous
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [H.IsCocontinuous J K] :
    exactFunctor (Sheaf K AddCommGrpCat.{w}) (Sheaf J AddCommGrpCat.{w})
      (H.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := by
  have := Stacks.SheafOfModules.sheafPushforward_preservesColimits J K H
  exact (exactFunctor_iff _).mpr
    ⟨inferInstance, PreservesColimitsOfSize.preservesFiniteColimits _⟩

end CategoryTheory.Functor

end
