module

public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Module.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionFree
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE

/-!
# Torsion-free coherent modules on an integral regular scheme of dimension at most one

On an integral regular scheme of dimension at most one, a coherent module is torsion free
exactly when it is finite locally free.

## Main results

* `Module.free_of_isTorsionFree_of_ringKrullDim_le_one`: a finite torsion-free module over a
  regular local domain of Krull dimension at most one is free.
* `AlgebraicGeometry.isTorsionFree_iff_isFiniteLocallyFree`: the characterization of
  torsion-free coherent modules on an integral regular scheme of dimension at most one.

## References

* [Stacks Project, Tag 0CC4](https://stacks.math.columbia.edu/tag/0CC4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

/-- A finite torsion-free module over a regular local domain of Krull dimension at most one is
free. -/
@[ega "0 10.2.8" "more general", ega "0 6.3.4" "more general"]
theorem Module.free_of_isTorsionFree_of_ringKrullDim_le_one
    {R M : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsTorsionFree R M]
    (hdim : ringKrullDim R ≤ 1) : Module.Free R M := by
  by_cases hField : IsField R
  · let : Field R := hField.toField
    infer_instance
  · have hone : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
      change (1 : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R)
      rw [Order.one_le_krullDim_iff]
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ⟨IsLocalRing.maximalIdeal R,
        (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩, ?_⟩
      change (⊥ : Ideal R) < IsLocalRing.maximalIdeal R
      exact bot_lt_iff_ne_bot.mpr fun h =>
        hField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    have hRegDim : IsRegularLocalRing R ∧ ringKrullDim R = 1 :=
      ⟨inferInstance, le_antisymm hdim hone⟩
    obtain ⟨_, _⟩ := ((isDiscreteValuationRing_tfae R).out 3 1).mp hRegDim
    exact Module.free_iff_isTorsionFree.mpr inferInstance

namespace AlgebraicGeometry

/-- On an integral regular scheme of dimension at most one a coherent module is torsion free if
and only if it is finite locally free. -/
@[stacks 0CC4]
theorem isTorsionFree_iff_isFiniteLocallyFree {X : Scheme.{u}} [IsIntegral X]
    (hregular : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] :
    (let : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
     IsTorsionFree F) ↔ SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) F := by
  let : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  let : F.IsFiniteType := _root_.IsCoherent.toIsFiniteType F
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    (((isRegular_tfae X).out 1 2 rfl rfl).mp hregular).2
  have hstalkdim (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
    (le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x).trans
      ((topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X).symm.le.trans hdim)
  refine ⟨fun hTorsion => ?_, fun hFree => ?_⟩
  · have hstalkTorsion := (isTorsionFree_iff_forall_stalk F).mp hTorsion
    have hstalkFree : ∀ x : X,
        let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) F.val x
        Module.Free (X.presheaf.stalk x) ↑(F.presheaf.stalk x) := by
      intro x
      let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      let := hreg x
      let : Module.IsTorsionFree (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
        hstalkTorsion x
      let : Module.Finite (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
        Stacks.StalkFiniteType.finite_stalk F x
      exact Module.free_of_isTorsionFree_of_ringKrullDim_le_one (hstalkdim x)
    apply ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae F).out 2 4).mp
    exact ⟨_root_.isFinitePresentation_of_isCoherent F, hstalkFree⟩
  · have hstalkFree :=
      ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae F).out 4 2).mp hFree
    refine (isTorsionFree_iff_forall_stalk F).mpr fun x => ?_
    let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
      F.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
    let : Module.Free (X.presheaf.stalk x) ↑(F.presheaf.stalk x) := hstalkFree.2 x
    exact Module.Free.instIsTorsionFree (R := X.presheaf.stalk x) (M := ↑(F.presheaf.stalk x))

end AlgebraicGeometry

end
