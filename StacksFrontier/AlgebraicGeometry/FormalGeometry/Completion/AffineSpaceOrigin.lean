module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChangePullback
public import StacksFrontier.RingTheory.AdicCompletion.MaximalIdealLocalization
public import StacksFrontier.RingTheory.MvPowerSeries.MixedCompletion

/-!
# The completed local ring of affine space at the origin

For a field `k`, the local ring of `𝔸ⁿ_k = Spec k[x_0, …, x_{n-1}]` at the origin has completion
`k[[x_0, …, x_{n-1}]]`, compatibly with the maps from the polynomial ring: a polynomial goes to
itself, read as a power series.

The isomorphism is assembled from three comparisons already in the library: the stalk of `Spec`
at a prime is the localization there (`AlgebraicGeometry.Spec.stalkIso`); completing the local
ring at a maximal ideal is completing the ring at that ideal
(`Stacks.MaximalLocalization.exists_adicCompletionAlgEquiv_localizationAtPrime`); and the
completion of a polynomial ring at the ideal of the origin is the power series ring
(`Stacks.MixedCompletion.polynomialAdicCompletionAlgEquiv`), whose coefficients are a priori in
the completion of `k`, which is `k` itself.

## Main definitions

* `Stacks.AffineSpaceOrigin.origin`: the origin of `𝔸ⁿ_k`, a closed point.
* `Stacks.AffineSpaceOrigin.completionFieldEquiv`: a field is its own completion.
* `Stacks.AffineSpaceOrigin.mvPowerSeriesCongr`: power series rings over isomorphic coefficient
  rings are isomorphic.

## Main results

* `Stacks.AffineSpaceOrigin.isClosed_singleton_origin`: the origin is a closed point.
* `Stacks.AffineSpaceOrigin.exists_ringEquiv_adicCompletion_stalk_origin`: the completed local
  ring of `𝔸ⁿ_k` at the origin is `k[[x_0, …, x_{n-1}]]`, compatibly with the polynomials.
-/

@[expose] public noncomputable section

open AlgebraicGeometry IsLocalRing CategoryTheory

universe u

namespace Stacks.AffineSpaceOrigin

/-- The origin of affine `n`-space `𝔸ⁿ_k = Spec k[x_0, …, x_{n-1}]`: the point given by the
ideal `(x_0, …, x_{n-1})`, written as the mixed ideal `𝔪_k · k[x] + (x)` of
`Stacks.MixedCompletion.polyMixed` (which for a field is the ideal of the variables). -/
def origin (k : Type u) [Field k] (n : ℕ) :
    Spec (CommRingCat.of (MvPolynomial (Fin n) k)) :=
  ⟨Stacks.MixedCompletion.polyMixed (maximalIdeal k) n,
    Stacks.MixedCompletion.polyMixed_isPrime _ n⟩

/-- A field is its own completion at its maximal ideal `⊥`. -/
def completionFieldEquiv (k : Type u) [Field k] :
    AdicCompletion (maximalIdeal k) k ≃+* k :=
  (RingEquiv.ofBijective (algebraMap k (AdicCompletion (maximalIdeal k) k)) (by
    rw [show maximalIdeal k = ⊥ from maximalIdeal_eq_bot]
    have hfun : ⇑(algebraMap k (AdicCompletion (⊥ : Ideal k) k)) = AdicCompletion.of ⊥ k :=
      funext fun x => by rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
    rw [hfun]
    exact AdicCompletion.of_bijective_iff.2 inferInstance)).symm

/-- A ring isomorphism of coefficients induces a ring isomorphism of power series rings,
coefficientwise. -/
def mvPowerSeriesCongr {σ R S : Type*} [CommRing R] [CommRing S] (c : R ≃+* S) :
    MvPowerSeries σ R ≃+* MvPowerSeries σ S :=
  RingEquiv.ofRingHom (MvPowerSeries.map (c : R →+* S)) (MvPowerSeries.map (c.symm : S →+* R))
    (by ext f d; simp) (by ext f d; simp)

/-- The isomorphism of power series rings acts coefficientwise. -/
theorem mvPowerSeriesCongr_apply {σ R S : Type*} [CommRing R] [CommRing S] (c : R ≃+* S)
    (f : MvPowerSeries σ R) : mvPowerSeriesCongr c f = MvPowerSeries.map (c : R →+* S) f := rfl

/-- The origin of affine space is a closed point. -/
theorem isClosed_singleton_origin (k : Type u) [Field k] (n : ℕ) :
    IsClosed ({origin k n} : Set (Spec (CommRingCat.of (MvPolynomial (Fin n) k)))) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    (Stacks.MixedCompletion.polyMixed_isMaximal (maximalIdeal k) n)

/-- **The completed local ring of affine space at the origin is the power series ring.** For a
field `k`, the completion of the local ring of `𝔸ⁿ_k` at the origin is isomorphic to
`k[[x_0, …, x_{n-1}]]`, by an isomorphism carrying (the image of) every polynomial to itself,
regarded as a power series. -/
theorem exists_ringEquiv_adicCompletion_stalk_origin (k : Type u) [Field k] (n : ℕ) :
    ∃ E : AdicCompletion
        (maximalIdeal ((Spec (CommRingCat.of (MvPolynomial (Fin n) k))).presheaf.stalk
          (origin k n)))
        ((Spec (CommRingCat.of (MvPolynomial (Fin n) k))).presheaf.stalk (origin k n)) ≃+*
        MvPowerSeries (Fin n) k,
      ∀ q : MvPolynomial (Fin n) k,
        E (algebraMap _ (AdicCompletion _ _)
          ((Spec (CommRingCat.of (MvPolynomial (Fin n) k))).presheaf.germ ⊤ (origin k n)
            trivial ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) k))).inv q))) =
          (q : MvPowerSeries (Fin n) k) := by
  set R := MvPolynomial (Fin n) k
  set q := Stacks.MixedCompletion.polyMixed (maximalIdeal k) n
  have : q.IsMaximal := Stacks.MixedCompletion.polyMixed_isMaximal _ n
  have h1 := StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv
    (Spec.stalkIso (CommRingCat.of R) (origin k n)).commRingCatIsoToRingEquiv
  have hm : Ideal.map (algebraMap R (Localization.AtPrime q)) q =
      maximalIdeal (Localization.AtPrime q) := Localization.AtPrime.map_eq_maximalIdeal
  have h2 := Stacks.MaximalLocalization.exists_adicCompletionAlgEquiv_localizationAtPrime q
  rw [hm] at h2
  obtain ⟨E2, hE2⟩ := h2
  obtain ⟨E1, hE1⟩ := h1
  refine ⟨E1.trans (E2.symm.toRingEquiv.trans
    ((Stacks.MixedCompletion.polynomialAdicCompletionAlgEquiv k n).toRingEquiv.trans
      (mvPowerSeriesCongr (completionFieldEquiv k)))), fun f => ?_⟩
  have key1 : (Spec.stalkIso (CommRingCat.of R) (origin k n)).hom
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (origin k n) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)) =
        algebraMap R (Localization.AtPrime q) f := by
    have := ConcreteCategory.congr_hom
      (Spec.germ_stalkMapIso_hom (R := CommRingCat.of R) (origin k n))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at this
    exact this
  have step1 := hE1 ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (origin k n) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f))
  show (E2.symm.toRingEquiv.trans
      ((Stacks.MixedCompletion.polynomialAdicCompletionAlgEquiv k n).toRingEquiv.trans
        (mvPowerSeriesCongr (completionFieldEquiv k)))) (E1 _) = _
  rw [step1]
  show (E2.symm.toRingEquiv.trans
      ((Stacks.MixedCompletion.polynomialAdicCompletionAlgEquiv k n).toRingEquiv.trans
        (mvPowerSeriesCongr (completionFieldEquiv k))))
      (algebraMap (Localization.AtPrime q) (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) ((Spec.stalkIso (CommRingCat.of R) (origin k n)).hom
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (origin k n) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)))) = _
  rw [key1, ← hE2 f]
  simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_apply]
  ext d
  rw [mvPowerSeriesCongr_apply, MvPowerSeries.coeff_map,
    Stacks.MixedCompletion.polynomialAdicCompletionAlgEquiv_of,
    Stacks.MixedCompletion.coeff_toSeries, MvPolynomial.coeff_coe]
  exact (RingEquiv.ofBijective _ _).symm_apply_apply _

end Stacks.AffineSpaceOrigin

end
