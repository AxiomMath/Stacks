module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.CoextensionHomothety

/-!
# The homothety of a coextension as a quasi-isomorphism

Declarations built on `StacksFrontier.RingTheory.Dualizing.DerivedHomothety.CoextensionHomothety`.

## Main results

* `exists_quasiIso_homothety_derivedHom_shift`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

/-! ### A bounded-below injective representative -/

end Dualizing

namespace Dualizing

/-! ### The scalar homothety under a shift -/

/-! ### Biduality and an isomorphism of the dualizing object -/

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]

end Dualizing

namespace Dualizing

open StacksDraft.DerivedHom

end Dualizing

namespace Dualizing

section Generalized

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **A shifted derived coextension of scalars has an injective representative whose scalar
homothety is a quasi-isomorphism**, given a bounded-below injective representative of the complex
coextended and the invertibility of the biduality morphism of `B[0]` over `A`. This is the
chain-level statement behind `Dualizing.isIso_derivedHomothety_overRing_derivedHom_shift`, and it
does not refer to any tensor--Hom adjunction. -/
theorem exists_quasiIso_homothety_derivedHom_shift [IsNoetherianRing A]
    (f : A →+* B) {ω : DerivedCategory (ModuleCat.{max v u} A)}
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ) (hGE : I.IsStrictlyGE a)
    (hinj : ∀ i, Injective (I.X i)) (e : ω ≅ DerivedCategory.Q.obj I)
    (hbid : IsIso (dualizingBidualityMor.{u, max v u} A ω (targetSingle.{u, v} f)))
    (n : ℤ) {ω' : DerivedCategory (ModuleCat.{max v u} B)}
    (e' : ω' ≅ (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).obj
      ((derivedHom.{u, v, u} f).obj ω)) :
    ∃ (J : CochainComplex (ModuleCat.{max v u} B) ℤ) (b : ℤ), J.IsStrictlyGE b ∧
      (∀ i : ℤ, Injective (J.X i)) ∧ Nonempty (ω' ≅ DerivedCategory.Q.obj J) ∧
        QuasiIso (homothety J) := by
  have hIge := hGE
  have hIinj := hinj
  have hI : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  set J := (coextendComplex.{u, u, v} f).obj I with hJ
  have hJge : J.IsStrictlyGE a := isStrictlyGE_coextendComplex_obj.{u, v} f I a
  have hJinj : ∀ i : ℤ, Injective (J.X i) := injective_coextendComplex_obj_X.{u, v} f I hinj
  have := hJge
  have := hJinj
  have hJki : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
  -- `J` represents the derived coextension
  set eJ : (derivedHom.{u, v, u} f).obj ω ≅ DerivedCategory.Q.obj J :=
    (derivedHom.{u, v, u} f).mapIso e ≪≫ derivedHomObjIsoCoextend.{u, v} f I hI with heJ
  -- the two Hom computations
  obtain ⟨e₀⟩ := nonempty_endLinearEquiv_derivedHom_of_isIso_bidualityMor.{u, v}
    f I a hGE hinj e hbid
  have hvanish : ∀ m : ℤ, m ≠ 0 →
      IsZero ((CochainComplex.HomComplexR B J J).homology m) := by
    intro m hm
    refine isZero_homology_homComplexR_of_subsingleton.{u, v} J a m ?_
    have := subsingleton_hom_derivedHom_shift_of_isIso_bidualityMor.{u, v}
      f I a hGE hinj e hbid m hm
    exact Equiv.subsingleton (Iso.homCongr eJ.symm
      ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) m).mapIso eJ.symm))
  have hhom : QuasiIso (homothety J) :=
    quasiIso_homothety_of_rankOne J
      ((homologyZeroEndLinearEquiv J).trans ((endLinearEquivOfIso eJ.symm).trans e₀)) hvanish
  -- shift
  have hshift : QuasiIso (homothety (J⟦n⟧)) := quasiIso_homothety_shift J n hhom
  have hSge : (J⟦n⟧).IsStrictlyGE (a - n) := J.isStrictlyGE_shift a n (a - n) (by omega)
  have hSinj : ∀ i : ℤ, Injective ((J⟦n⟧).X i) := fun i =>
    Injective.of_iso (J.shiftFunctorObjXIso n i (n + i) (by abel)).symm (hJinj (n + i))
  exact ⟨J⟦n⟧, a - n, hSge, hSinj,
    ⟨e' ≪≫ (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).mapIso eJ ≪≫
      ((DerivedCategory.Q.commShiftIso n).app J).symm⟩, hshift⟩

end Generalized

end Dualizing

namespace Dualizing

section Perfect07VI

variable {A B : Type u} [CommRing A] [CommRing B]

end Perfect07VI

end Dualizing

end
