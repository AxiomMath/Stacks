module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizing
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.CoextensionHomothetyQuasiIso

/-!
# The homothety of the relative dualizing complex

Let `R` be Noetherian and `f : R →+* A` presented by `p`, with `A` a perfect module over the
polynomial algebra of the presentation. The relative dualizing complex `ω_{A/R} = p^!(R)` is
represented by a bounded below complex `J` of injective `A`-modules whose scalar homothety
`A[0] → Hom•_A(J, J)` is a quasi-isomorphism.

## Main results

* `Dualizing.upperShriekFunctor_unit_exists_quasiIso_homothety`: `ω_{A/R}` has a bounded below
  injective representative whose scalar homothety is a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

namespace PolynomialPresentation

end PolynomialPresentation

/-- **The relative dualizing complex has an injective representative whose scalar homothety is a
quasi-isomorphism**, under the hypotheses of [Stacks, Tag 0BZW] (1)(c): for `R` Noetherian and `A`
perfect over the polynomial algebra of `p`, `p^!(R)` is isomorphic in `D(A)` to a bounded below
complex `J` of injectives with `homothety J` a quasi-isomorphism. -/
theorem upperShriekFunctor_unit_exists_quasiIso_homothety [IsNoetherianRing R]
    (p : PolynomialPresentation f)
    (hperf : letI : Module p.Poly (ULift.{max v u} A) :=
        Module.compHom (ULift.{max v u} A) p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) (ULift.{max v u} A)) :
    ∃ (J : CochainComplex (ModuleCat.{max v u} A) ℤ) (b : ℤ), J.IsStrictlyGE b ∧
      (∀ i : ℤ, Injective (J.X i)) ∧
      Nonempty (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))) ≅ DerivedCategory.Q.obj J) ∧
      QuasiIso (homothety J) := by
  set ωP := p.derivedExtension.{u, v}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
      (ModuleCat.of R (ULift.{v} R)))
  set eU := PolynomialPresentation.derivedExtensionTensorUnitIso.{u, v} p
  have : ωP.IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (eU ≪≫ derivedTensorUnitIsoSingle.{u, v} p.Poly).symm 0
  obtain ⟨I, hIge, hIinj, ⟨eI⟩⟩ := exists_injectiveRepresentative ωP 0
  have hbid : IsIso (dualizingBidualityMor.{u, max v u} p.Poly ωP
      (targetSingle.{u, v} p.toRingHom)) := by
    change IsIso (bidualityMor
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} p.Poly) ωP
      (targetSingle.{u, v} p.toRingHom))
    exact isIso_bidualityMor_of_iso_dualizing _ eU.symm _
      (isIso_dualizingBidualityMor_derivedTensorUnit_of_isPerfect.{u, v}
        (targetSingle.{u, v} p.toRingHom)
        (isPerfect_scalarPreimage_targetSingle.{u, v} p.toRingHom hperf))
  exact exists_quasiIso_homothety_derivedHom_shift.{u, v} p.toRingHom I 0 hIge hIinj eI
    hbid (p.variableCount : ℤ) (Iso.refl _)

end Dualizing

end
