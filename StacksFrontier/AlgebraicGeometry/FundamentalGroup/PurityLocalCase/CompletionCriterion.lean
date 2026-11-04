module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.FiniteExtensionFromCompletion

/-!
# Purity and completion

Let `A` be a Noetherian local ring with maximal ideal `𝔪`, let `U = Spec A ∖ {𝔪}` be its
punctured spectrum and let `V ⟶ U` be finite étale. Write `Â` for the `𝔪`-adic completion of
`A` and decorate with a hat the base changes to `Spec Â`. Then `V` extends to a finite étale
scheme over `Spec A` if and only if `V̂` extends to a finite étale scheme over `Spec Â`.

One direction is base change. The other combines the finite extension produced by formal
glueing with faithfully flat descent of étaleness: `Â` is faithfully flat over `A`, so
`Spec Â ⟶ Spec A` is a flat surjective quasi-compact morphism and étaleness of the extension
descends along it.

## Main results

* `AlgebraicGeometry.exists_finiteEtale_extension_iff_completion` — the equivalence above.

## Implementation notes

Both base changes are categorical pullbacks: `Û` is the pullback of `U ⟶ Spec A` along
`Spec Â ⟶ Spec A`, and `V̂` is the pullback of `V ⟶ U` along the resulting projection. That a
scheme over `Spec A` restricts to `V` over `U` is recorded as a `CategoryTheory.IsPullback`
square.

## References

* [Stacks Project, Tag 0BLL](https://stacks.math.columbia.edu/tag/0BLL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0BLL.** A finite étale cover of the punctured spectrum of a
Noetherian local ring extends over the spectrum exactly when its base change to the adic
completion extends over the completed spectrum. -/
@[stacks 0BLL]
lemma exists_finiteEtale_extension_iff_completion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (V : Scheme.{u}) (pi : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    [IsFinite pi] [Etale pi] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    let Xhat := Spec (.of Ahat)
    let completionMap : Xhat ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Uhat := pullback (Stacks.Divisors.puncturedSpectrum A).ι completionMap
    let UhatToU : Uhat ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme :=
      pullback.fst _ _
    let Vhat := pullback pi UhatToU
    let pihat : Vhat ⟶ Uhat := pullback.snd _ _
    (∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)) (g : V ⟶ Y),
      IsFinite f ∧ Etale f ∧
        IsPullback pi g (Stacks.Divisors.puncturedSpectrum A).ι f) ↔
      ∃ (Yhat : Scheme.{u}) (fhat : Yhat ⟶ Xhat) (ghat : Vhat ⟶ Yhat),
        IsFinite fhat ∧ Etale fhat ∧
          IsPullback pihat ghat (pullback.snd (Stacks.Divisors.puncturedSpectrum A).ι completionMap)
            fhat := by
  intro Ahat Xhat completionMap Uhat UhatToU Vhat pihat
  constructor
  · rintro ⟨Y, f, g, _, _, hp⟩
    let ghat : Vhat ⟶ pullback f completionMap :=
      pullback.lift (pullback.fst pi UhatToU ≫ g)
        (pihat ≫ pullback.snd (Stacks.Divisors.puncturedSpectrum A).ι completionMap)
        (by
          calc
            (pullback.fst pi UhatToU ≫ g) ≫ f =
                pullback.fst pi UhatToU ≫ pi ≫ (Stacks.Divisors.puncturedSpectrum A).ι := by
              rw [Category.assoc, hp.w]
            _ = pihat ≫ pullback.snd (Stacks.Divisors.puncturedSpectrum A).ι completionMap ≫
                completionMap := by
              rw [← Category.assoc, pullback.condition, Category.assoc, pullback.condition])
    exact ⟨pullback f completionMap, pullback.snd f completionMap, ghat, inferInstance,
      inferInstance, (IsPullback.paste_twist_right hp.flip
        (IsPullback.of_hasPullback f completionMap) UhatToU
        (pullback.snd _ _) pullback.condition (pullback.fst pi UhatToU) pihat
        (IsPullback.of_hasPullback pi UhatToU)
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).flip⟩
  · rintro ⟨Yhat, fhat, ghat, _, hehat, hp⟩
    obtain ⟨Y, f, g, _, hf, hpV, hpCompletion, _⟩ :=
      exists_finite_extension_of_completion A V pi Yhat fhat ghat hp
    obtain ⟨hflat, hsurj⟩ : Flat completionMap ∧ Surjective completionMap := by
      rw [flat_and_surjective_SpecMap_iff]
      exact RingHom.faithfullyFlat_algebraMap_iff.mpr
        (AdicCompletion.faithfullyFlat_of_le_ringJacobson _
          (ringJacobson_eq_maximalIdeal (R := A)).ge)
    exact ⟨Y, f, g, hf, MorphismProperty.of_isPullback_of_descendsAlong
      (P := @Etale) (Q := @Surjective.{u} ⊓ @Flat ⊓ @QuasiCompact)
      hpCompletion ⟨⟨hsurj, hflat⟩, inferInstance⟩ hehat, hpV⟩

end AlgebraicGeometry

end
