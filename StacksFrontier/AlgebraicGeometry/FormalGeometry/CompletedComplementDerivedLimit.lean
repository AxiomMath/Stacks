module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneRealization
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.TensorModelNormalizedLimit
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.UliftAdicQuotient
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.TensorModel

/-!
# Stacks 0BLX in the shape the proof of Stacks 0EIF consumes

`Stacks.Algebraization.CompletedComplementIsFormalSections` asserts that for an ideal `J` of a
Noetherian ring `A`, a finite `A`-module `M` and a localization triangle datum `D` of `J`, the
derived `I`-adic completion of `RΓ(V, M̃) = D.complement.obj M`, with `V = Spec A ∖ V(J)`, is a
derived limit of the tower `n ↦ RΓ(V, (M/IⁿM)^~)`, with projections normalized against the
completion unit. This file proves it.

## Main results

* `Stacks.Algebraization.completedComplementIsFormalSections` —
  `Stacks.Algebraization.CompletedComplementIsFormalSections`, with no hypotheses.

## Implementation notes

The third term of a localization triangle is a derived tensor product `M ↦ C' ⊗ᴸ M[0]`
(`Stacks.LocalCohomology.exists_complementIso_tensor`), so the normalized derived-limit argument
for such functors (`Dualizing.exists_isDerivedLimitWithProjections_of_tensorIso`) applies. It
produces a cone for the reflection of Stacks 0922; the two reflections onto the derived complete
objects agree compatibly with their units (`CategoryTheory.Adjunction.leftAdjointUniq`), and the
tower `Stacks.LocalCohomology.idealPowerQuotientTower` is the tower
`AlgebraicGeometry.ProEtale.adicQuotientModuleSystem` termwise, with the identity as comparison.

## References

* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

attribute [local instance] Dualizing.AdicQuotientComparison.derivedCategoryHasProductsNat

/-- The two presentations of the tower `n ↦ M/IⁿM` agree, with the identity as comparison. -/
def adicQuotientModuleSystemIsoIdealPowerQuotientTower {A : Type u} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) :
    AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ≅
      idealPowerQuotientTower.{u, u} I M where
  hom := NatTrans.ofOpSequence (fun _ => 𝟙 _) fun n => by
    unfold AlgebraicGeometry.ProEtale.adicQuotientModuleSystem
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl))
  inv := NatTrans.ofOpSequence (fun _ => 𝟙 _) fun n => by
    unfold AlgebraicGeometry.ProEtale.adicQuotientModuleSystem
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl))

/-- **Stacks 0BLX, 0A0K and 0D60 combined, in the shape the proof of Stacks 0EIF consumes**: the
derived `I`-adic completion of `RΓ(Spec A ∖ V(J), M̃)` is a derived limit of the tower
`n ↦ RΓ(Spec A ∖ V(J), (M/IⁿM)^~)`, with projections normalized against the completion unit, for
every Noetherian ring `A`, ideals `I`, `J`, finite module `M` and localization triangle datum of
`J`. -/
theorem completedComplementIsFormalSections : CompletedComplementIsFormalSections.{u} := by
  intro A _ _ I J M _ D
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp J.fg_of_isNoetherianRing
  obtain ⟨C, ⟨ψ⟩⟩ := exists_complementIso_tensor f hf D
  have hI := I.fg_of_isNoetherianRing
  obtain ⟨L, adj, q, hq, hqnorm⟩ :=
    Dualizing.exists_isDerivedLimitWithProjections_of_tensorIso A I D.complement C ψ M
      (Dualizing.fg_comap_uliftRingEquiv A hI)
      (Dualizing.uliftAdicQuotientModuleSystemIso A I M)
      (Dualizing.map_mkQ_comp_uliftAdicQuotientModuleSystemIso A I M)
  let ee := (Dualizing.derivedCompleteProperty A I).ι.mapIso
    ((adj.leftAdjointUniq (adicCompletionAdjunction A I hI)).app (D.complement.obj M))
  have hee : adj.unit.app (D.complement.obj M) ≫ ee.hom =
      (adicCompletionUnit A I hI).app (D.complement.obj M) :=
    adj.unit_leftAdjointUniq_hom_app (adicCompletionAdjunction A I hI) _
  let eT := Functor.isoWhiskerRight (adicQuotientModuleSystemIsoIdealPowerQuotientTower I M)
    D.complement
  refine ⟨inferInstance, fun n => ee.inv ≫ (q n ≫ eT.hom.app ⟨n⟩),
    (hq.ofNatIso eT).ofIso ee, fun n => ?_⟩
  rw [← hee, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hqnorm n]
  refine (D.complement.map_comp _ _).symm.trans (congrArg D.complement.map ?_)
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

end Stacks.Algebraization

end
