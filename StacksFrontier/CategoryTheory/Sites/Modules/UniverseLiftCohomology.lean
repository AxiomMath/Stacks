module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSheaf
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of sheaves of modules along an equivalence of ringed sites

Right derived functors are invariant under an exact equivalence of the source category, and
under postcomposition with an exact faithful functor of the target. This file records the
resulting transport of vanishing of right derived functors along a commutative square, and
applies it to the equivalence of categories of sheaves of modules induced by a ring transport
(`Stacks.UniverseLift.RingTransport.sheafEquivalence`): the module-valued cohomology of a sheaf
of modules over an object vanishes exactly when that of its transport over the corresponding
object does.

## Main results

* `Stacks.UniverseLift.rightDerivedObjIsoOfSquare`: for an additive equivalence `E : A ⥤ A'`,
  additive functors `F : A ⥤ B`, `F' : A' ⥤ B'` and an exact functor `Φ : B ⥤ B'` with
  `E ⋙ F' ≅ F ⋙ Φ`, the isomorphism `Rᵖ F' (E Z) ≅ Φ (Rᵖ F Z)`.
* `Stacks.UniverseLift.isZero_rightDerived_obj_iff_of_square`: vanishing of `Rᵖ F' (E Z)` is
  vanishing of `Rᵖ F Z`, when `Φ` is moreover faithful.
* `Stacks.UniverseLift.RingTransport.isZero_rightDerived_evaluation_iff`: **transport of the
  vanishing of module cohomology** along a ring transport.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe m v₁ v₂ u₁ u₂ r₁ r₂

namespace Stacks.UniverseLift

section Square

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasInjectiveResolutions A] [HasInjectiveResolutions A']
  (E : A ⥤ A') [E.Additive] [E.IsEquivalence]
  (F : A ⥤ B) [F.Additive] (F' : A' ⥤ B') [F'.Additive]
  (Φ : B ⥤ B') [Φ.Additive] [Φ.PreservesHomology]

/-- **Right derived functors along a commutative square with an equivalence.** For an additive
equivalence `E : A ⥤ A'`, additive functors `F : A ⥤ B` and `F' : A' ⥤ B'`, and an exact
functor `Φ : B ⥤ B'` with `E ⋙ F' ≅ F ⋙ Φ`, the `p`-th right derived functor of `F'` at `E Z`
is `Φ` applied to the `p`-th right derived functor of `F` at `Z`. -/
@[sga "4 V 2.5.2" "partial"]
noncomputable def rightDerivedObjIsoOfSquare (sq : E ⋙ F' ≅ F ⋙ Φ) (Z : A) (p : ℕ) :
    (F'.rightDerived p).obj (E.obj Z) ≅ Φ.obj ((F.rightDerived p).obj Z) :=
  letI : PreservesFiniteLimits E := inferInstance
  letI : PreservesFiniteColimits E := inferInstance
  (RightDerivedComp.objIso E (injectiveResolution Z)
      (fun n hn ↦ E.isZero_rightDerived_of_exact Z n hn) F' p).symm ≪≫
    { hom := (NatTrans.rightDerived sq.hom p).app Z
      inv := (NatTrans.rightDerived sq.inv p).app Z
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, sq.hom_inv_id,
          NatTrans.rightDerived_id, NatTrans.id_app]
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, sq.inv_hom_id,
          NatTrans.rightDerived_id, NatTrans.id_app] } ≪≫
    (Classical.choice (Cohomology.rightDerived_comp_iso_of_preservesHomology F Φ p Z)).symm

/-- **Vanishing of right derived functors along a commutative square with an equivalence.**
With `E`, `F`, `F'` and `Φ` as in `rightDerivedObjIsoOfSquare` and `Φ` faithful,
`Rᵖ F' (E Z)` vanishes if and only if `Rᵖ F Z` does. -/
theorem isZero_rightDerived_obj_iff_of_square [Φ.Faithful] (sq : E ⋙ F' ≅ F ⋙ Φ) (Z : A)
    (p : ℕ) :
    IsZero ((F'.rightDerived p).obj (E.obj Z)) ↔ IsZero ((F.rightDerived p).obj Z) := by
  let i := rightDerivedObjIsoOfSquare E F F' Φ sq Z p
  refine ⟨fun h ↦ ?_, fun h ↦ (Φ.map_isZero h).of_iso i⟩
  replace h := h.of_iso i.symm
  rw [IsZero.iff_id_eq_zero]
  exact Φ.map_injective (by rw [Φ.map_id, Φ.map_zero]; exact h.eq_of_src _ _)

end Square

namespace RingTransport

-- The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is stated at a module
-- universe which is a `max` of four universe variables; at the free module universe `m` used
-- here, instance search against it leaves a stuck universe constraint. The instance that
-- applies is Mathlib's `SheafOfModules.instAbelian`, to which it unfolds.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {e : C ≌ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{r₁}} {R' : Sheaf K RingCat.{r₂}} (T : RingTransport e R.obj R'.obj)
  [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasInjectiveResolutions (SheafOfModules.{m} R)]
  [HasInjectiveResolutions (SheafOfModules.{m} R')]

/-- **Transport of the vanishing of module cohomology along a ring transport.** The `p`-th
cohomology over `Y` of the transport of a sheaf of modules `F` vanishes if and only if the
`p`-th cohomology of `F` over `e⁻¹ Y` does. -/
theorem isZero_rightDerived_evaluation_iff (F : SheafOfModules.{m} R) (Y : Dᵒᵖ) (p : ℕ) :
    IsZero (((SheafOfModules.evaluation R' Y).rightDerived p).obj (T.sheafFunctor.obj F)) ↔
      IsZero (((SheafOfModules.evaluation R (e.inverse.op.obj Y)).rightDerived p).obj F) := by
  -- Restriction of scalars along a ring isomorphism is used through the equivalence it is a
  -- functor of, so that its exactness is found from the equivalence rather than from an
  -- adjunction whose universes are not those of `m`.
  let E : ModuleCat.{m} (R.obj.obj (e.inverse.op.obj Y)) ≌ ModuleCat.{m} (R'.obj.obj Y) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (T.iso Y)
  have : E.functor.PreservesHomology := Functor.preservesHomologyOfExact _
  exact isZero_rightDerived_obj_iff_of_square T.sheafFunctor _ _ E.functor
    (T.sheafFunctorCompEvaluation Y) F p

end RingTransport

end Stacks.UniverseLift
