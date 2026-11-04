module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompIso
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.DerivedCategory

/-!
# Pushing forward and forgetting, in degree `n`

`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` carries the
identity "push modules forward and then forget is forget and then push abelian sheaves forward" to
the unbounded derived categories, where it is no longer an identity.  Underived the move is
`modulePushforwardCompToSheafIso`, which is `Iso.refl`.  This file reads the derived comparison in
degree `n`: its degree-`n` cohomology is the underived move, once the three comparisons that take
an exact functor past `Hⁿ` — for the two forgetful functors and for the direct image — have been
inserted.

## Main results

* `Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso_homology`:
  the square.  Going down the derived comparison and then taking `Hⁿ` past the forgetful functor
  on `X` and past the abelian direct image is taking `Hⁿ` past the forgetful functor on `Y` and
  past the direct image of modules, followed by the underived move.

## Implementation notes

The derived comparison is by construction a composite of three factors — two instances of
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` and one of
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` — and the degreewise reading of
each factor is a general lemma of
`StacksFrontier/Algebra/Homology/DerivedCategory/MapDerivedCategoryHomologyCompIso.lean`.  All that
happens here is that the three are chained; the chaining is the `private` lemma `chain_degreewise`,
stated at a variable category and applied with `exact`, because the two spellings `f_* ⋙ Φ_Y` and
`Φ_X ⋙ f_*^{ab}` of one functor meet in the middle of the chain and `rw` and `simp` refuse to
identify them, reporting that the target is not type-correct at their transparency level.  This is
the device of `chain_cancel` in
`StacksFrontier/Topology/Sheaves/Cohomology/ModulePushforwardComparison/DerivedCategory.lean`.

**No `@[stacks ...]` attribute is attached to any declaration here.**
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.ModulePushforwardComparison

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- Chaining the degreewise readings of the three factors of the derived comparison, at an
abstract category: the two outer factors are comparisons of "the descent of a composite" with
"the composite of the descents" and the middle one is the descent of the underived move.  Stated
at a variable category and applied with `exact` for the reason recorded in the implementation
notes. -/
private lemma chain_degreewise {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (W : C₀ ⥤ D₀)
    {b₀ b₁ b₂ b₃ : C₀} {s s' t : D₀}
    (x : b₀ ⟶ b₃) (p : b₀ ⟶ b₁) (q : b₁ ⟶ b₂) (r : b₂ ⟶ b₃) (r' : b₃ ⟶ b₂)
    (u₁ : W.obj b₁ ⟶ s) (u₂ : W.obj b₂ ⟶ t) (v₁ : W.obj b₀ ⟶ s') (v₂ : s' ⟶ s)
    (r₂ : W.obj b₃ ⟶ t) (ε : s ⟶ t)
    (hx : x = p ≫ q ≫ r) (hr : r ≫ r' = 𝟙 b₂)
    (h₁ : W.map p ≫ u₁ = v₁ ≫ v₂) (h₂ : W.map r' ≫ u₂ = r₂)
    (h₃ : W.map q ≫ u₂ = u₁ ≫ ε) :
    W.map x ≫ r₂ = v₁ ≫ v₂ ≫ ε := by
  rw [hx, W.map_comp, W.map_comp, ← h₂, ← Category.assoc v₁ v₂ ε, ← h₁,
    Category.assoc (W.map p) u₁ ε, ← h₃]
  simp only [Category.assoc]
  rw [← Category.assoc (W.map r) (W.map r') u₂, ← W.map_comp, hr, W.map_id, Category.id_comp]

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [PreservesFiniteLimits (modulePushforward f)]
  [PreservesFiniteColimits (modulePushforward f)]
  [PreservesFiniteColimits (abelianPushforward f)]

/-- **The derived pushforward/forget comparison in degree `n`.**  The degree-`n` cohomology of
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso`, followed
by the two comparisons that take `Hⁿ` past the abelian direct image and past the forgetful functor
on `X`, is the two comparisons that take `Hⁿ` past the forgetful functor on `Y` and past the direct
image of modules, followed by the underived move `modulePushforwardCompToSheafIso`. -/
theorem derivedModulePushforwardCompToSheafIso_homology (n : ℤ)
    (A : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) n).map
          ((derivedModulePushforwardCompToSheafIso f).hom.app A) ≫
        ((abelianPushforward f).mapDerivedCategoryHomologyFunctorIso n).hom.app
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing X)).mapDerivedCategory.obj A) ≫
        (abelianPushforward f).map
          (((_root_.SheafOfModules.toSheaf
            (structureSheafRing X)).mapDerivedCategoryHomologyFunctorIso n).hom.app A) =
      ((_root_.SheafOfModules.toSheaf
            (structureSheafRing Y)).mapDerivedCategoryHomologyFunctorIso n).hom.app
          ((modulePushforward f).mapDerivedCategory.obj A) ≫
        (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).map
          (((modulePushforward f).mapDerivedCategoryHomologyFunctorIso n).hom.app A) ≫
        (modulePushforwardCompToSheafIso f).hom.app
          ((DerivedCategory.homologyFunctor
            (_root_.SheafOfModules.{u} (structureSheafRing X)) n).obj A) := by
  have hsplit : (derivedModulePushforwardCompToSheafIso f).hom.app A =
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso (modulePushforward f)
          (_root_.SheafOfModules.toSheaf (structureSheafRing Y))).inv.app A ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
            (modulePushforward f ⋙ _root_.SheafOfModules.toSheaf (structureSheafRing Y))
            (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianPushforward f)
            (modulePushforwardCompToSheafIso f)).hom.app A ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (_root_.SheafOfModules.toSheaf (structureSheafRing X))
          (abelianPushforward f)).hom.app A := rfl
  refine chain_degreewise
    (DerivedCategory.homologyFunctor
      (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) n)
    _ _ _ _ _
    (((modulePushforward f ⋙
        _root_.SheafOfModules.toSheaf
          (structureSheafRing Y)).mapDerivedCategoryHomologyFunctorIso n).hom.app A)
    (((_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        abelianPushforward f).mapDerivedCategoryHomologyFunctorIso n).hom.app A)
    _ _ _ _ hsplit (Iso.hom_inv_id_app _ A) ?_ ?_ ?_
  · exact CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_comp_app
      (modulePushforward f) (_root_.SheafOfModules.toSheaf (structureSheafRing Y)) n A
  · exact CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_comp_app
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)) (abelianPushforward f) n A
  · exact CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_isoOfNatIso_app
      (modulePushforward f ⋙ _root_.SheafOfModules.toSheaf (structureSheafRing Y))
      (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianPushforward f)
      (modulePushforwardCompToSheafIso f) n A

end Stacks.Cohomology.ModulePushforwardComparison

end
