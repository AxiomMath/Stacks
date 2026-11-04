module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonCartesianCohomology
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftUniversalArrow

/-!
# Cartesian presheaves of modules along a ring transport

A presheaf of modules `P` over a presheaf of rings `O` is *cartesian* when each of its
restriction maps `P(V) ⟶ P(U)` is a base change, that is, a universal arrow for restriction of
scalars along `O(V) ⟶ O(U)` (`Stacks.ModulesOnACategory.ChaoticComparison.IsCartesianPresheaf`).
The transport of presheaves of modules along a ring transport `T : RingTransport e O O'` (an
equivalence `e : C ≌ D` together with ring isomorphisms `O'(Y) ≃+* O(e⁻¹ Y)`, possibly between
different universes) preserves and reflects the cartesian condition.

## Main results

* `Stacks.UniverseLift.RingTransport.isUniversalArrow_functor_obj_map`: a restriction map of the
  transport is a base change where the corresponding restriction map of the presheaf is.
* `Stacks.UniverseLift.RingTransport.isCartesianPresheaf_functor_obj`: the transport of a
  cartesian presheaf of modules is cartesian.
* `Stacks.UniverseLift.RingTransport.isCartesianPresheaf_functor_obj_iff`: a presheaf of modules
  is cartesian exactly when its transport is.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.ModulesOnACategory.ChaoticComparison (IsCartesianPresheaf)

universe m v₁ v₂ u₁ u₂ r₁ r₂

namespace Stacks.UniverseLift.RingTransport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {e : C ≌ D}
  {R : Cᵒᵖ ⥤ RingCat.{r₁}} {R' : Dᵒᵖ ⥤ RingCat.{r₂}} (T : RingTransport e R R')

/-- **The restriction maps of a transport are base changes where those of the presheaf are.**
For `a' : V' ⟶ U'` in `Dᵒᵖ`, if the restriction map of `M` along `e⁻¹ a'` is a universal arrow
for restriction of scalars, then so is the restriction map of the transport of `M` along
`a'`. -/
theorem isUniversalArrow_functor_obj_map (M : PresheafOfModules.{m} R) {U' V' : Dᵒᵖ}
    (a' : V' ⟶ U')
    (h : (ModuleCat.restrictScalars.{m} (R.map (e.inverse.op.map a')).hom).IsUniversalArrow
      (M.map (e.inverse.op.map a'))) :
    (ModuleCat.restrictScalars.{m} (R'.map a').hom).IsUniversalArrow
      ((T.functor.obj M).map a') := by
  refine Functor.IsUniversalArrow.of_equivalence (T.restrictScalarsSquare.{m} a')
    (Iso.refl _) (Iso.refl _) ?_ h
  ext x
  rfl

/-- **The transport of a cartesian presheaf of modules along a ring transport is cartesian.** -/
theorem isCartesianPresheaf_functor_obj {M : PresheafOfModules.{m} R}
    (hM : IsCartesianPresheaf M) : IsCartesianPresheaf (T.functor.obj M) :=
  fun _ _ a' => T.isUniversalArrow_functor_obj_map M a' (hM (e.inverse.op.map a'))

/-- **A presheaf of modules is cartesian exactly when its transport along a ring transport
is.** -/
theorem isCartesianPresheaf_functor_obj_iff (M : PresheafOfModules.{m} R) :
    IsCartesianPresheaf (T.functor.obj M) ↔ IsCartesianPresheaf M :=
  ⟨fun h => (T.symm.isCartesianPresheaf_functor_obj h).of_iso (T.unitIso.app M).symm,
    T.isCartesianPresheaf_functor_obj⟩

end Stacks.UniverseLift.RingTransport

namespace Stacks.UniverseLift

variable {C : Type u₁} [Category.{v₁} C]

/-- The functor of the identity equivalence is continuous for any topology. -/
instance refl_functor_isContinuous (J : GrothendieckTopology C) :
    (CategoryTheory.Equivalence.refl : C ≌ C).functor.IsContinuous J J :=
  Functor.isContinuous_id J

/-- The inverse of the identity equivalence is continuous for any topology. -/
instance refl_inverse_isContinuous (J : GrothendieckTopology C) :
    (CategoryTheory.Equivalence.refl : C ≌ C).inverse.IsContinuous J J :=
  Functor.isContinuous_id J

end Stacks.UniverseLift

end
