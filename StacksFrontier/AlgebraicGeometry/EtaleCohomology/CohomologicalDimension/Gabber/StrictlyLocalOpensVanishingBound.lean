module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.FractionFieldOfPuncturedSpectrum

/-!
# Exposé XVIII-A, Theorem 1.1, from Corollary 1.2

Travaux de Gabber, Exposé XVIII-A, Theorem 1.1: for a strictly henselian Noetherian local ring
`A` of dimension `d` and `n` invertible in `A`, every open `U` of `X = Spec A` has `cd_n(U) ≤
2d - 1`. This file derives it from Corollary 1.2 there
(`AlgebraicGeometry.Scheme.FractionFieldVanishingBound`, the bound `2e - 1` for the fraction field
of a strictly henselian Noetherian local domain of dimension `e ≥ 1`), in full generality: `A` is
not assumed to be a domain and `U` is arbitrary.

**The argument** avoids the source's induction on `d`
and its reduction to an integral `X`, since Corollary 1.2 is available in every dimension.

* For `𝓕` on `U` killed by `n`, let `L = j_*𝓕` on `X`, so `L|_U = 𝓕` (Stacks 0F70). As `X` is
  strictly local, `H^{≥1}(X, L) = 0` (Stacks 03QO), and the excision sequence gives
  `H^i(U, 𝓕) = 0` as soon as `H^{i+1}_{X∖U}(X, L) = 0`
  (`AlgebraicGeometry.Scheme.subsingleton_sheafH_etaleRestriction_of_subsingleton_of_isZero`).
* Lemma 2.2 with supports
  (`AlgebraicGeometry.Scheme.isZero_rightDerived_opensSupport_of_genericPointSupportKilling`,
  whose local input is Lemma 2.1, here
  `AlgebraicGeometry.Scheme.puncturedSpectrumVanishingBound_of_fractionFieldVanishingBound`)
  bounds `H^*_{X∖U}(X, L)` by `sup_{y ∉ U} (c(y) + 2 ht y)`, with
  `c(y) = max(0, 2 coht y - 1)` a bound for `κ(y) = Frac(A ⧸ 𝔭_y)`
  (`AlgebraicGeometry.Scheme.isTorsionVanishingBound_residueField_spec_of_upTo`). As
  `ht y + coht y ≤ d`, the supremum is at most `2d`, so `H^i(U, 𝓕) = 0` for `i ≥ 2d`.

## Main results

* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_opens_spec_of_fractionFieldVanishingBound`:
  **Theorem 1.1 from Corollary 1.2.**

## References

* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Theorem 1.1, Corollary 1.2, Lemmas 2.1 and 2.2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 0F70](https://stacks.math.columbia.edu/tag/0F70)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

variable {n : ℕ}

/-- **Travaux de Gabber, Exposé XVIII-A, Theorem 1.1, from Corollary 1.2**, for coefficients
killed by `n`. Let `A` be a strictly henselian Noetherian local ring of dimension `d` with `n`
invertible in `A`, and `U` any open of `Spec A`. Then `cd_n(U) ≤ 2d - 1`.

For `𝓕` on `U` killed by `n`, `L = j_*𝓕` restricts to `𝓕` on `U`, has no higher cohomology on
the strictly local `Spec A`, and has `H^{i+1}_{X∖U}(X, L) = 0` for `i ≥ 2d` by Lemma 2.2 with
supports: the bound at `κ(y)` is `max(0, 2 coht y - 1)` and `ht y + coht y ≤ d`. (The statement
also holds for `d = 0`, with `2d - 1` read in `ℕ` as `0`.) -/
theorem isTorsionVanishingBound_opens_spec_of_fractionFieldVanishingBound
    (h : FractionFieldVanishingBound.{u} n) (A : Type u) [CommRing A] [IsNoetherianRing A]
    [StrictlyHenselianLocalRing A] {d : ℕ} (hd : ringKrullDim A = d) (hn : IsUnit (n : A))
    (U : (Spec (.of A)).Opens) :
    IsTorsionVanishingBound U.toScheme n ((2 * d - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn
  intro F hF p hp
  have hp' : 2 * d - 1 < p := by exact_mod_cast hp
  -- the sheaf `L = j_* 𝓕` on `X = Spec A`, whose restriction to `U` is `𝓕`
  let L := (Stacks.EtaleCohomology.etaleDirectImage.{u, 0} U.ι).obj F
  have hL : ∀ (T : (Spec (.of A)).Etale) (x : L.obj.obj (op T)), n • x = 0 :=
    (forall_nsmul_eq_zero_iff_nsmul_id_eq_zero L).2
      (nsmul_id_obj_eq_zero (Stacks.EtaleCohomology.etaleDirectImage.{u, 0} U.ι)
        ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero F).1 hF))
  refine (Stacks.EtaleCohomology.subsingleton_H_iff_of_iso
    ((Stacks.EtaleCohomology.directImageRestrictionIso.{u, 0} U.ι).app F) p).1 ?_
  refine subsingleton_sheafH_etaleRestriction_of_subsingleton_of_isZero U L p
    (Stacks.StrictlyHenselian.subsingleton_etaleCohomology_smallEtaleTopology A L p (by omega)) ?_
  -- Lemma 2.2 with supports on `X = Spec A`
  have hnX : IsUnit (n : Γ(Spec (.of A), ⊤)) := by
    simpa only [map_natCast] using hn.map (Scheme.ΓSpecIso (.of A)).inv.hom
  let c : Spec (.of A) → WithBot ℕ∞ := fun x =>
    ((2 * (Order.coheight (α := PrimeSpectrum A) x).toNat - 1 : ℕ) : WithBot ℕ∞)
  have hc : ∀ x, IsTorsionVanishingBound (Spec (.of ((Spec (.of A)).residueField x))) n (c x) := by
    intro x
    obtain ⟨a, b, -, hb, hab⟩ := exists_height_coheight_eq_of_ringKrullDim_eq hd
      (x : PrimeSpectrum A)
    simp only [c]
    rw [hb, ENat.toNat_natCast]
    exact isTorsionVanishingBound_residueField_spec_of_upTo hn0 (h.upTo d) hn x hb (by omega)
  have hsup : (⨆ (x : Spec (.of A)) (_ : x ∉ U),
      (c x + 2 * ringKrullDim ((Spec (.of A)).presheaf.stalk x))) ≤
        ((2 * d : ℕ) : WithBot ℕ∞) := by
    refine iSup₂_le fun x _ => ?_
    obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq_of_ringKrullDim_eq hd
      (x : PrimeSpectrum A)
    have hstalk : ringKrullDim ((Spec (.of A)).presheaf.stalk x) = ((a : ℕ) : WithBot ℕ∞) := by
      let y : PrimeSpectrum A := x
      have h1 : y.asIdeal.height = a := by
        rw [PrimeSpectrum.height_eq_orderHeight]
        exact ha
      rw [ringKrullDim_stalk_spec (CommRingCat.of A) x]
      exact congrArg (fun t : ℕ∞ => (t : WithBot ℕ∞)) h1
    simp only [c]
    rw [hb, ENat.toNat_natCast, hstalk]
    exact_mod_cast (by omega : 2 * b - 1 + 2 * a ≤ 2 * d)
  exact isZero_rightDerived_opensSupport_of_genericPointSupportKilling
    (genericPointSupportKilling_of_localInputs
      (puncturedStalkVanishing_of_puncturedSpectrumVanishingBound
        (puncturedSpectrumVanishingBound_of_fractionFieldVanishingBound h))
      (localSectionsAtPoint n))
    (Spec (.of A)) hnX c hc L hL U (p + 1)
    (lt_of_le_of_lt hsup (by exact_mod_cast (by omega : 2 * d < p + 1)))

end AlgebraicGeometry.Scheme

end
