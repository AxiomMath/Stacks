module

public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
import Mathlib.RingTheory.HopkinsLevitzki
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Normalized dualizing complexes over zero-dimensional local rings

Let `A` be a Noetherian local ring of Krull dimension zero and let `E` be an injective hull of
its residue field. A normalized dualizing complex over `A` is `E` placed in degree zero, and an
arbitrary dualizing complex over `A` is a shift of that.

## Main results

* `Dualizing.nonempty_iso_single_injectiveHull_of_ringKrullDim_eq_zero` ([stacks 0A7R]): a
  normalized dualizing complex over a zero-dimensional Noetherian local ring is an injective
  hull of the residue field in degree zero.
* `Dualizing.exists_shift_iso_single_injectiveHull_of_ringKrullDim_eq_zero`: an arbitrary
  dualizing complex over such a ring is an integral shift of the same object.

## Implementation notes

Over a zero-dimensional Noetherian ring the ring itself has finite length, so it is an object of
`Dualizing.FiniteLengthModules`; evaluating the identification of derived Hom with Matlis duality
(`Dualizing.derivedHomFiniteLengthIsoMatlisDual`) at that object turns `RHom_A(A, ω)` into
`Hom_A(A, E)[0]`, and both sides are then simplified to `ω` and `E[0]`. The second result follows
by shifting a dualizing complex to a normalized one
(`Dualizing.exists_isNormalizedDualizingComplex_shift`).

The module universe is independent of the universe of the ring, so the role of the ring as a
module over itself is played by `ULift A`. An injective hull is represented by a chosen essential
monomorphism out of the residue field, and the conclusion applies to any such choice.

## References

* [Stacks Project, Tag 0A7R](https://stacks.math.columbia.edu/tag/0A7R)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- A Noetherian ring of Krull dimension zero has finite length as a module over itself. -/
@[ega "0 16.1.10" "special case"]
private lemma isFiniteLength_self_of_ringKrullDim_eq_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hdim : ringKrullDim A = 0) :
    IsFiniteLength A A :=
  (isArtinianRing_iff_isFiniteLength A).mp
    (isArtinianRing_iff_krullDimLE_zero.mpr (Ring.krullDimLE_iff.mpr hdim.le))

/-- Homomorphisms out of the ring, lifted to an arbitrary module universe, are their values
at `1`. -/
private noncomputable def uliftRingHomIso {A : Type u} [CommRing A]
    (E : ModuleCat.{max v u} A) :
    ModuleCat.of A (ModuleCat.of A (ULift.{v} A) ⟶ E) ≅ E :=
  LinearEquiv.toModuleIso
    ((ModuleCat.homLinearEquiv (S := A) (M := ModuleCat.of A (ULift.{v} A)) (N := E)).trans
      ((LinearEquiv.arrowCongr (ULift.moduleEquiv (R := A) (M := A))
          (LinearEquiv.refl A E)).trans
        (LinearMap.ringLmapEquivSelf A A E)))

/-- **Stacks Project, Tag 0A7R.** A normalized dualizing complex over a zero-dimensional
Noetherian local ring is an injective hull of the residue field placed in degree zero. -/
@[stacks 0A7R]
theorem nonempty_iso_single_injectiveHull_of_ringKrullDim_eq_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) (hdim : ringKrullDim A = 0)
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Nonempty (K ≅ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj E) := by
  let N : FiniteLengthModules.{u, v} A :=
    ⟨ModuleCat.of A (ULift.{v} A),
      (ULift.moduleEquiv (R := A) (M := A)).symm.isFiniteLength
        (isFiniteLength_self_of_ringKrullDim_eq_zero A hdim)⟩
  obtain ⟨α⟩ := derivedHomFiniteLengthIsoMatlisDual.{u, v} A K hK E i hi
  exact ⟨(derivedHomULiftRingIso.{u, v} A K).symm ≪≫ α.app (Opposite.op N) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).mapIso (uliftRingHomIso E)⟩

/-- Over a zero-dimensional Noetherian local ring, a dualizing complex is an integral shift of
an injective hull of the residue field placed in degree zero. -/
theorem exists_shift_iso_single_injectiveHull_of_ringKrullDim_eq_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsDualizingComplex K) (hdim : ringKrullDim A = 0)
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ∃ n : ℤ, Nonempty
      (K ≅ ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj E)⟦n⟧) := by
  obtain ⟨n, hn⟩ := exists_isNormalizedDualizingComplex_shift.{u, v} K hK
  obtain ⟨e⟩ := nonempty_iso_single_injectiveHull_of_ringKrullDim_eq_zero.{u, v}
    (K⟦-n⟧) hn hdim E i hi
  exact ⟨n, ⟨(shiftFunctorCompIsoId
      (DerivedCategory (ModuleCat.{max v u} A)) (-n) n (by omega)).symm.app K ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n).mapIso e⟩⟩

end Dualizing

end
