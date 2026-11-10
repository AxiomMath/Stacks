module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.DimensionBoundedLocalToGlobal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FractionFieldVanishingBound
public import StacksFrontier.Order.HeightCoheight

/-!
# The punctured bound of Exposé XVIII-A from Corollary 1.2

Travaux de Gabber, Exposé XVIII-A, Lemma 2.1
(`AlgebraicGeometry.Scheme.PuncturedSpectrumVanishingBound`):
the punctured spectrum `U = Spec A ∖ {𝔪}` of a strictly henselian Noetherian local ring `A` of
dimension `d ≥ 1` has `cd_n(U) ≤ 2d - 1`. This file derives it from Corollary 1.2
(`AlgebraicGeometry.Scheme.FractionFieldVanishingBound`, the bound `2e - 1` for the fraction field
of a strictly henselian Noetherian local domain of dimension `e ≥ 1`), by induction on `d`. This is
the route of the remark at the end of section 2 of the source ("by Lemma 2.2 it suffices to show
Corollary 1.2"), and the proof of Theorem 1.1 there, applied to the punctured spectrum.

**The induction step.** Assume the punctured bound in dimensions `< d` and apply Lemma 2.2 to the
Noetherian scheme `U`
(`AlgebraicGeometry.Scheme.isTorsionVanishingBound_of_puncturedSpectrumVanishingBoundUpTo`),
whose local rings `A_𝔭` have dimension `ht 𝔭 ≤ d - 1`, so that only the punctured bound in
dimensions `≤ d - 1` enters. At a point `𝔭 ≠ 𝔪` of `U` the residue field is `κ(𝔭) = Frac(A ⧸ 𝔭)`,
and `A ⧸ 𝔭` is a strictly henselian Noetherian local domain of dimension `e = coht 𝔭 ≥ 1`; by
Corollary 1.2 its cohomology vanishes above `c(𝔭) = 2e - 1`. Since `ht 𝔭 + coht 𝔭 ≤ d`,
`c(𝔭) + 2 dim 𝒪_{U,𝔭} ≤ 2d - 1`.

## Main results

* `AlgebraicGeometry.Scheme.ringKrullDim_stalk_puncturedSpectrum`: `dim 𝒪_{U,𝔭} = ht 𝔭`.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_residueField_puncturedSpectrum`: the bound
  `2 coht 𝔭 - 1` for `κ(𝔭)`, from Corollary 1.2.
* `AlgebraicGeometry.Scheme.puncturedSpectrumVanishingBoundUpTo_of_fractionFieldVanishingBound`:
  the induction.
* `AlgebraicGeometry.Scheme.puncturedSpectrumVanishingBound_of_fractionFieldVanishingBound`:
  Lemma 2.1 from Corollary 1.2.

## References

* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Theorem 1.1, Corollary 1.2, Lemmas 2.1 and 2.2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

section PuncturedSpectrum

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- **The punctured spectrum of a Noetherian local ring is a Noetherian scheme**: an open
subscheme of the Noetherian scheme `Spec A`, quasi-compact since `Spec A` is a Noetherian
space. -/
theorem isNoetherian_puncturedSpectrum [IsNoetherianRing A] :
    IsNoetherian (Stacks.puncturedSpectrum A).toScheme := by
  have : CompactSpace (Stacks.puncturedSpectrum A).toScheme :=
    isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact _)
  exact ⟨⟩

/-- **The local ring of the punctured spectrum at `𝔭` has dimension `ht 𝔭`**: it is the local
ring `A_𝔭` of `Spec A` at `𝔭`. -/
theorem ringKrullDim_stalk_puncturedSpectrum (x : (Stacks.puncturedSpectrum A).toScheme) :
    ringKrullDim ((Stacks.puncturedSpectrum A).toScheme.presheaf.stalk x) =
      (Order.height (α := PrimeSpectrum A) ((Stacks.puncturedSpectrum A).ι x) : WithBot ℕ∞) := by
  let y : PrimeSpectrum A := (Stacks.puncturedSpectrum A).ι x
  -- instance search for this `IsIso` wanders off in the present import closure
  have hiso : IsIso ((Stacks.puncturedSpectrum A).ι.stalkMap x) :=
    @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ (Stacks.puncturedSpectrum A).ι
      (Scheme.Opens.instIsOpenImmersionι _) x
  let e := (asIso ((Stacks.puncturedSpectrum A).ι.stalkMap x)).commRingCatIsoToRingEquiv
  rw [← ringKrullDim_eq_of_ringEquiv e]
  change ringKrullDim ((Spec.structureSheaf A).presheaf.stalk y) =
    ((Order.height y : ℕ∞) : WithBot ℕ∞)
  rw [← PrimeSpectrum.height_eq_orderHeight]
  exact IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal
    ((Spec.structureSheaf A).presheaf.stalk y)

omit [IsLocalRing A] in
/-- The coheight of a prime `𝔭` is the dimension of `A ⧸ 𝔭`. -/
private lemma coheight_eq_ringKrullDim_quotient' (P : PrimeSpectrum A) :
    (Order.coheight P : WithBot ℕ∞) = ringKrullDim (A ⧸ P.asIdeal) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  rfl

/-- **Height and coheight of a non-closed point** of the spectrum of a local ring of dimension
`d`: both are natural numbers `a` and `b` with `a + b ≤ d` and `b ≥ 1`. -/
theorem exists_height_coheight_of_ne_closedPoint {d : ℕ} (hd : ringKrullDim A = d)
    (y : PrimeSpectrum A) (hy : y ≠ closedPoint A) :
    ∃ a b : ℕ, Order.height y = a ∧ Order.coheight y = b ∧ a + b ≤ d ∧ 1 ≤ b := by
  have h := Order.height_add_coheight_le_krullDim y
  change _ ≤ ringKrullDim A at h
  rw [hd, ← WithBot.coe_add] at h
  have h' : Order.height y + Order.coheight y ≤ (d : ℕ∞) := by exact_mod_cast h
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1
    (ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h'))
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1
    (ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_add_self h'))
  refine ⟨a, b, ha.symm, hb.symm, ?_, ?_⟩
  · rw [← ha, ← hb] at h'
    exact_mod_cast h'
  · refine Nat.one_le_iff_ne_zero.2 fun hb0 => ?_
    subst hb0
    have hmax : IsMax y := Order.coheight_eq_zero.1 (by rw [← hb]; rfl)
    exact hmax.not_lt (lt_of_le_of_ne (IsLocalRing.le_maximalIdeal y.isPrime.ne_top) hy)

end PuncturedSpectrum

/-- **The bound at the residue fields of the punctured spectrum, from Corollary 1.2.** At a point
`𝔭` of the punctured spectrum of a strictly henselian Noetherian local ring, with `n > 0`
invertible, `κ(𝔭) = Frac(A ⧸ 𝔭)` for the strictly henselian Noetherian local domain `A ⧸ 𝔭`, of
dimension `coht 𝔭 ≥ 1`, so Corollary 1.2 bounds its cohomology by `2 coht 𝔭 - 1`. -/
theorem isTorsionVanishingBound_residueField_puncturedSpectrum {A : Type u} [CommRing A] {n : ℕ}
    (hn0 : 0 < n)
    (h : FractionFieldVanishingBound.{u} n) [IsNoetherianRing A] [StrictlyHenselianLocalRing A]
    (hn : IsUnit (n : A)) (x : (Stacks.puncturedSpectrum A).toScheme) {b : ℕ}
    (hb : Order.coheight (α := PrimeSpectrum A) ((Stacks.puncturedSpectrum A).ι x) = b)
    (hb1 : 1 ≤ b) :
    IsTorsionVanishingBound
      (Spec (.of ((Stacks.puncturedSpectrum A).toScheme.residueField x))) n
      ((2 * b - 1 : ℕ) : WithBot ℕ∞) := by
  let y : PrimeSpectrum A := (Stacks.puncturedSpectrum A).ι x
  have : StrictlyHenselianLocalRing (A ⧸ y.asIdeal) :=
    StrictlyHenselianLocalRing.quotient y.isPrime.ne_top
  have hdim : ringKrullDim (A ⧸ y.asIdeal) ≤ b := by
    rw [← coheight_eq_ringKrullDim_quotient' A y, show Order.coheight y = b from hb]
    rfl
  have hnB : IsUnit (n : A ⧸ y.asIdeal) := by
    simpa only [map_natCast] using hn.map (Ideal.Quotient.mk y.asIdeal)
  have hfrac := isTorsionVanishingBound_spec_fractionRing hn0 h (A ⧸ y.asIdeal) hb1 hdim hnB
  -- `κ(x) ≅ κ(𝔭) ≅ Frac(A ⧸ 𝔭)`
  let eq : y.asIdeal.ResidueField ≃ₐ[A ⧸ y.asIdeal] FractionRing (A ⧸ y.asIdeal) :=
    IsLocalization.algEquiv (nonZeroDivisors (A ⧸ y.asIdeal)) _ _
  let c : CommRingCat.of (FractionRing (A ⧸ y.asIdeal)) ≅
      (Stacks.puncturedSpectrum A).toScheme.residueField x :=
    eq.toRingEquiv.symm.toCommRingCatIso ≪≫ (Spec.residueFieldIso (.of A) y).symm ≪≫
      asIso ((Stacks.puncturedSpectrum A).ι.residueFieldMap x)
  exact IsTorsionVanishingBound.of_iso (Scheme.Spec.mapIso c.op) hfrac

variable {n : ℕ}

/-- **Exposé XVIII-A, Lemma 2.1, up to every dimension, from Corollary 1.2**, by induction on the
dimension: Lemma 2.2 on the punctured spectrum of a local ring of dimension `d ≤ D + 1` needs the
punctured bound only up to dimension `d - 1 ≤ D`. -/
theorem puncturedSpectrumVanishingBoundUpTo_of_fractionFieldVanishingBound
    (h : FractionFieldVanishingBound.{u} n) (D : ℕ) :
    PuncturedSpectrumVanishingBoundUpTo.{u} n D := by
  induction D with
  | zero => exact fun A _ _ _ d _ hpos hle _ => absurd hle (by omega)
  | succ D ih =>
  intro A _ _ _ d hd hpos hdD hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn
  set U := Stacks.puncturedSpectrum A
  have := isNoetherian_puncturedSpectrum A
  have hy : ∀ x : U.toScheme, (U.ι x : PrimeSpectrum A) ≠ closedPoint A := fun x => by
    have hx := Set.mem_range_self (f := ⇑U.ι) x
    rw [Scheme.Opens.range_ι] at hx
    exact hx
  choose a b ha hb hab hb1 using fun x : U.toScheme =>
    exists_height_coheight_of_ne_closedPoint A hd _ (hy x)
  have hnU : IsUnit (n : Γ(U.toScheme, ⊤)) := by
    simpa only [map_natCast] using hn.map ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop).hom
  have hstalk : ∀ x : U.toScheme,
      ringKrullDim (U.toScheme.presheaf.stalk x) = ((a x : ℕ) : WithBot ℕ∞) := fun x => by
    rw [ringKrullDim_stalk_puncturedSpectrum, ha x]
    rfl
  have hD : ∀ x : U.toScheme, ringKrullDim (U.toScheme.presheaf.stalk x) ≤ D := fun x => by
    rw [hstalk x]
    exact_mod_cast (by have := hab x; have := hb1 x; omega : a x ≤ D)
  refine (isTorsionVanishingBound_of_puncturedSpectrumVanishingBoundUpTo ih U.toScheme hnU hD
    (fun x => ((2 * b x - 1 : ℕ) : WithBot ℕ∞))
    (fun x => isTorsionVanishingBound_residueField_puncturedSpectrum hn0 h hn x (hb x)
      (hb1 x))).mono ?_
  refine iSup_le fun x => ?_
  rw [hstalk x]
  have : 2 * b x - 1 + 2 * a x ≤ 2 * d - 1 := by
    have := hab x
    have := hb1 x
    omega
  exact_mod_cast this

/-- **Travaux de Gabber, Exposé XVIII-A, Lemma 2.1 (the punctured bound of Theorem 1.1), from
Corollary 1.2**, for coefficients killed by `n`: the bound `2e - 1` for the fraction fields of
strictly henselian Noetherian local domains of dimension `e ≥ 1` gives the bound `2d - 1` for the
punctured spectra of strictly henselian Noetherian local rings of dimension `d ≥ 1`. -/
theorem puncturedSpectrumVanishingBound_of_fractionFieldVanishingBound
    (h : FractionFieldVanishingBound.{u} n) : PuncturedSpectrumVanishingBound.{u} n :=
  fun A _ _ _ d hd hpos hn =>
    puncturedSpectrumVanishingBoundUpTo_of_fractionFieldVanishingBound h d A d hd hpos le_rfl hn

end AlgebraicGeometry.Scheme

end
