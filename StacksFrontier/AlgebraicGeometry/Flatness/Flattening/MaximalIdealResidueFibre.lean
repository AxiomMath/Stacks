module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MaximalIdealInjectivity

/-!
# The residue-field fibre at the maximal ideal

In the injectivity-modulo-the-maximal-ideal situation of Stacks 0AT0 the standing hypothesis is
injectivity of the reduction of `u` modulo the maximal ideal of the base ring. Read as a
statement about residue-field fibres, it says that `u ⊗ id_{κ(𝔭)}` is injective for `𝔭` the
maximal ideal.

This identifies the content of Claim 2 in the proof of Stacks 05U9 — injectivity of
`u ⊗ id_{κ(𝔭)}` for *every* prime `𝔭` of the base ring, which is the hypothesis of Stacks 0AT9 —
as a statement about the non-maximal primes only: at the maximal ideal it is the standing
hypothesis of Situation 0AT0, and over a Noetherian base it holds at every prime by Stacks 0AT1.

## Main definitions

No new definitions are introduced beyond a comparison of two spellings of the residue field.

## Main results

* `IsLocalRing.residueFieldAlgEquivMaximalIdeal`: for a local ring `A`, the residue field of `A`
  and the residue field of the prime `maximalIdeal A` are the same `A`-algebra.
* `AlgebraicGeometry.rTensor_residueField_maximalIdeal_injective`: in Situation 0AT0 the fibre
  of `u` at the maximal ideal is injective, unconditionally.
* `AlgebraicGeometry.rTensor_residueField_injective_of_isNoetherianRing`: over a Noetherian base
  the fibre of `u` at every prime is injective.

## Implementation notes

`Ideal.ResidueField 𝔭` is the residue field of the localization `A_𝔭`, whereas
`IsLocalRing.ResidueField A` is the quotient `A/𝔪_A`; for `𝔭 = 𝔪_A` the localization map
`A → A_{𝔪_A}` is an isomorphism because `A ∖ 𝔪_A` consists of units, which is what
`IsLocalRing.residueFieldAlgEquivMaximalIdeal` records.

Injectivity of the reduction of `u` modulo an ideal `I` is injectivity of `u ⊗ id_{A/I}`; the
reduction is `Submodule.mapQ` of `u` for the submodules `I • ⊤`, and the comparison is the
`TensorProduct.tensorQuotEquivQuotSMul` square.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT1](https://stacks.math.columbia.edu/tag/0AT1)
* [Stacks Project, Tag 0AT9](https://stacks.math.columbia.edu/tag/0AT9)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄

open TensorProduct

namespace IsLocalRing

/-- For a local ring `A`, the quotient `A/𝔪_A` and the residue field of the prime `𝔪_A` — that
is, the residue field of the localization `A_{𝔪_A}` — are the same `A`-algebra.

The localization map `A → A_{𝔪_A}` is an isomorphism because every element outside `𝔪_A` is a
unit. -/
noncomputable def residueFieldAlgEquivMaximalIdeal (A : Type u₁) [CommRing A] [IsLocalRing A] :
    ResidueField A ≃ₐ[A] (maximalIdeal A).ResidueField := by
  have hunits : (maximalIdeal A).primeCompl ≤ IsUnit.submonoid A :=
    fun _ => notMem_maximalIdeal.mp
  have hcomp : ∀ a : A, algebraMap A (maximalIdeal A).ResidueField a =
      residue (Localization.AtPrime (maximalIdeal A))
        (algebraMap A (Localization.AtPrime (maximalIdeal A)) a) := fun _ => rfl
  have hzero : ∀ a ∈ maximalIdeal A,
      (Algebra.ofId A (maximalIdeal A).ResidueField) a = 0 := by
    intro a ha
    have hmem : algebraMap A (Localization.AtPrime (maximalIdeal A)) a ∈
        maximalIdeal (Localization.AtPrime (maximalIdeal A)) := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (maximalIdeal A)
        (Localization.AtPrime (maximalIdeal A))]
      exact Ideal.mem_map_of_mem _ ha
    exact (residue_eq_zero_iff _).mpr hmem
  have hsurj : Function.Surjective (algebraMap A (maximalIdeal A).ResidueField) := by
    intro y
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective
      (I := maximalIdeal (Localization.AtPrime (maximalIdeal A))) y
    obtain ⟨a, ha⟩ :=
      (IsLocalization.atUnits A (maximalIdeal A).primeCompl hunits).surjective z
    refine ⟨a, ?_⟩
    rw [hcomp a]
    have halg : (IsLocalization.atUnits A (maximalIdeal A).primeCompl hunits) a =
        algebraMap A (Localization.AtPrime (maximalIdeal A)) a := by
      simpa using (IsLocalization.atUnits A (maximalIdeal A).primeCompl hunits).commutes a
    rw [← halg, ha]
    exact hz
  let φ : ResidueField A →ₐ[A] (maximalIdeal A).ResidueField :=
    Ideal.Quotient.liftₐ (maximalIdeal A) (Algebra.ofId A (maximalIdeal A).ResidueField) hzero
  refine AlgEquiv.ofBijective φ ⟨φ.toRingHom.injective, fun y => ?_⟩
  obtain ⟨a, ha⟩ := hsurj y
  exact ⟨algebraMap A (ResidueField A) a, (φ.commutes a).trans ha⟩

end IsLocalRing

namespace AlgebraicGeometry

/-- Injectivity transfers along a commuting square whose horizontal maps are bijective. -/
private theorem injective_iff_of_bijective_comp_eq {α β γ δ : Type*} {f : α → β} {g : γ → δ}
    {e : α → γ} {e' : β → δ} (he : e.Bijective) (he' : e'.Injective) (h : e' ∘ f = g ∘ e) :
    f.Injective ↔ g.Injective := by
  rw [← he'.of_comp_iff f, h, Function.Injective.of_comp_iff' g he]

/-- Injectivity of a base change is invariant under a linear equivalence of test modules. -/
theorem injective_rTensor_iff_of_equiv
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {Q Q' : Type*} [AddCommGroup Q] [Module R Q]
    [AddCommGroup Q'] [Module R Q'] (f : M →ₗ[R] N) (e : Q ≃ₗ[R] Q') :
    Function.Injective (f.rTensor Q) ↔ Function.Injective (f.rTensor Q') := by
  have hcomm : (LinearEquiv.lTensor N e).toLinearMap ∘ₗ f.rTensor Q =
      (f.rTensor Q') ∘ₗ (LinearEquiv.lTensor M e).toLinearMap := by
    rw [LinearEquiv.coe_lTensor, LinearEquiv.coe_lTensor, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]
  exact injective_iff_of_bijective_comp_eq (LinearEquiv.lTensor M e).bijective
    (LinearEquiv.lTensor N e).injective (congrArg DFunLike.coe hcomm)

/-- Injectivity of the reduction of a map modulo an ideal is injectivity of its base change to
the quotient ring. -/
theorem mapQ_injective_iff_rTensor_quotient {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (I : Ideal R) :
    Function.Injective ((I • (⊤ : Submodule R M)).mapQ
      (I • (⊤ : Submodule R N)) f (Submodule.smul_top_le_comap_smul_top I f)) ↔
      Function.Injective (f.rTensor (R ⧸ I)) := by
  have hcomm : (tensorQuotEquivQuotSMul N I).toLinearMap ∘ₗ f.rTensor (R ⧸ I) =
      (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
        (Submodule.smul_top_le_comap_smul_top I f) ∘ₗ
      (tensorQuotEquivQuotSMul M I).toLinearMap := by
    refine TensorProduct.ext' fun x r' => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r'
    simp [tensorQuotEquivQuotSMul_tmul_mk, Submodule.mapQ_apply]
  exact (injective_iff_of_bijective_comp_eq (tensorQuotEquivQuotSMul M I).bijective
    (tensorQuotEquivQuotSMul N I).injective (congrArg DFunLike.coe hcomm)).symm

/-- **The residue-field fibre at the maximal ideal, in Situation 0AT0.** The standing hypothesis
of Stacks 0AT0 is exactly injectivity of `u ⊗ id_{κ(𝔪_A)}`.

This is the fibre hypothesis of Stacks 0AT9 — Claim 2 in the proof of Stacks 05U9 — at the
maximal ideal of the base ring, so the content of that claim lies at the non-maximal primes. -/
theorem rTensor_residueField_maximalIdeal_injective
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) :
    Function.Injective (S.u.rTensor (IsLocalRing.maximalIdeal S.A).ResidueField) :=
  (injective_rTensor_iff_of_equiv S.u
      (IsLocalRing.residueFieldAlgEquivMaximalIdeal S.A).toLinearEquiv).mp
    ((mapQ_injective_iff_rTensor_quotient S.u (IsLocalRing.maximalIdeal S.A)).mp
      S.injective_mod_maximalIdeal)

/-- Over a Noetherian base the residue-field fibre of `u` is injective at every prime, by the
universal-injectivity clause of Stacks 0AT1.

So the fibre hypothesis of Stacks 0AT9 — Claim 2 in the proof of Stacks 05U9 — is not a dead end
in Situation 0AT0: it is reachable, and reproduces at the maximal ideal the standing hypothesis
of the situation. -/
theorem rTensor_residueField_injective_of_isNoetherianRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) [IsNoetherianRing S.A]
    (p : Ideal S.A) [p.IsPrime] :
    Function.Injective (S.u.rTensor p.ResidueField) :=
  universallyInjective_of_isNoetherianRing S p.ResidueField

end AlgebraicGeometry

end
