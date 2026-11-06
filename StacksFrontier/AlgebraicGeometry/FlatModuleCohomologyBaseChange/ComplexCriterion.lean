module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.AcyclicResolution

/-!
# The criterion of `AcyclicResolution.lean` read backwards

`Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_Qh` says that the derived
comparison of [Stacks, Tag 0GN5] is invertible at the image of a bounded below complex `L` as soon
as the derived-functor unit of `Rf_*` and the canonical map out of `Φ(f_*L)` are.  The underlying
identity `derivedComparison_fac` is an equation, so it also runs in the other direction: when the
unit of `Rf_*` is invertible at `L` — for instance when the terms of `L` are right acyclic for
`f_*` — the canonical map out of `Φ(f_*L)` is invertible exactly when the derived comparison is
invertible at `Qh L`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_comparisonOnHomotopy_app_of_isIso`: the
  comparison on bounded below homotopy categories is invertible at `L`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_complexComparison_of_isIso`: **the canonical
  map `Φ(f_*L) ⟶ Rf'_*(ΨL)` is invertible.**

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- **The comparison on bounded below homotopy categories is invertible at `L`** as soon as the
derived-functor unit of `Rf_*` is invertible at `L` and the derived comparison is invertible at
the image of `L` in `D⁺(X)`: the first is a factor of the second composite in
`derivedComparison_fac`. -/
theorem isIso_comparisonOnHomotopy_app_of_isIso (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hL : IsIso ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlusUnith.app L))
    (h : IsIso ((derivedComparison G w hG).app (DerivedCategory.Plus.Qh.obj L))) :
    IsIso ((comparisonOnHomotopy G w hG).app L) := by
  have key := NatTrans.congr_app (derivedComparison_fac G w hG) L
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp] at key
  have := hL
  have := h
  rw [← key]
  infer_instance

/-- **The canonical map `Φ(f_*L) ⟶ Rf'_*(ΨL)` is invertible** as soon as the derived-functor unit
of `Rf_*` is invertible at `L` and the derived comparison is invertible at the image of `L`. -/
theorem isIso_complexComparison_of_isIso (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (L : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hL : IsIso ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlusUnith.app L))
    (h : IsIso ((derivedComparison G H.w hG).app (DerivedCategory.Plus.Qh.obj L))) :
    IsIso (complexComparison H.w G L) :=
  (isIso_comparisonOnHomotopy_app_iff H G hG L).1
    (isIso_comparisonOnHomotopy_app_of_isIso H.w G hG L hL h)

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
