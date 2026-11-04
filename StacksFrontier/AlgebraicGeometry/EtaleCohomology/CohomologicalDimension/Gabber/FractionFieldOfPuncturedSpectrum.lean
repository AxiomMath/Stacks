module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.OpensSupportBotCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.PuncturedSpectrumOfFractionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.LocalSchemeAffineLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FieldExtensionTorsionBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSmallEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecStalkHeight
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Corollary 1.2 of Exposé XVIII-A from the punctured bound

Travaux de Gabber, Exposé XVIII-A, Corollary 1.2
(`AlgebraicGeometry.Scheme.FractionFieldVanishingBound`):
for a strictly henselian Noetherian local domain `B` of dimension `e ≥ 1` with fraction field `K`,
`cd_n(K) ≤ 2e - 1`. This file derives it from Lemma 2.1 there
(`AlgebraicGeometry.Scheme.PuncturedSpectrumVanishingBound`, the bound `2d - 1` for the punctured
spectra of strictly henselian Noetherian local rings of dimension `d ≥ 1`), by induction on `e`.
Together with
`AlgebraicGeometry.Scheme.puncturedSpectrumVanishingBound_of_fractionFieldVanishingBound`
this makes the two bounds equivalent.

**The argument** is the source's: Remark 1.3(a) and the proof of Theorem 1.1. Let `X = Spec B`.

* `Spec K` is the directed limit of the affine open neighbourhoods of the generic point of `X`
  (`AlgebraicGeometry.Scheme.isLimitLocalAffineCone`), so it suffices to bound `cd_n(U)` for
  every open `U ∋ η` of `X` (Stacks 0F0R,
  `AlgebraicGeometry.Scheme.isTorsionVanishingBound_of_isLimit_of_isDirected`).
* For `𝓕` on `U` killed by `n`, let `L = j_*𝓕` on `X`, so `L|_U = 𝓕` (Stacks 0F70). As `X` is
  strictly local, `H^{≥1}(X, L) = 0` (Stacks 03QO), and the excision sequence gives
  `H^i(U, 𝓕) = 0` as soon as `H^{i+1}_{X∖U}(X, L) = 0`
  (`AlgebraicGeometry.Scheme.subsingleton_sheafH_etaleRestriction_of_subsingleton_of_isZero`).
* Lemma 2.2 with supports
  (`AlgebraicGeometry.Scheme.isZero_rightDerived_opensSupport_of_genericPointSupportKilling`,
  whose local input is Lemma 2.1) bounds `H^*_{X∖U}(X, L)` by
  `sup_{y ∉ U} (c(y) + 2 ht y)`, with `c(y)` a bound for `κ(y) = Frac(B ⧸ 𝔭_y)`. Since
  `η ∈ U`, every `y ∉ U` has `ht y ≥ 1`, so `B ⧸ 𝔭_y` has dimension `coht y ≤ e - 1` and by
  induction `c(y) = 2 coht y - 1` (`0` at the closed point, whose residue field is separably
  closed). As `ht y + coht y ≤ e`, the supremum is at most `2e`, so `H^i(U, 𝓕) = 0` for
  `i ≥ 2e`.

## Main definitions

* `AlgebraicGeometry.Scheme.FractionFieldVanishingBoundUpTo n D`: Corollary 1.2 for domains of
  dimension `1 ≤ e ≤ D`.

## Main results

* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_opens_spec_of_upTo`: Theorem 1.1 for the
  opens of `Spec B` containing the generic point, from Lemma 2.1 and Corollary 1.2 in lower
  dimension.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_fractionRing_of_upTo`: the induction step.
* `AlgebraicGeometry.Scheme.fractionFieldVanishingBound_of_puncturedSpectrumVanishingBound`:
  **Corollary 1.2 from Lemma 2.1.**

## References

* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Theorem 1.1, Corollary 1.2, Remark 1.3(a), Lemmas 2.1 and 2.2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 0F0R](https://stacks.math.columbia.edu/tag/0F0R)
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

/-- **Exposé XVIII-A, Corollary 1.2, up to dimension `D`**: for every strictly henselian
Noetherian local domain `B` of dimension `e` with `1 ≤ e ≤ D` in which `n` is invertible, the
étale cohomology of `Spec (Frac B)` with coefficients killed by `n` vanishes above `2e - 1`. -/
def FractionFieldVanishingBoundUpTo (n D : ℕ) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [StrictlyHenselianLocalRing B]
    (e : ℕ), ringKrullDim B = e → 0 < e → e ≤ D → IsUnit (n : B) →
      IsTorsionVanishingBound (Spec (.of (FractionRing B))) n ((2 * e - 1 : ℕ) : WithBot ℕ∞)

/-- Corollary 1.2 in every dimension gives it up to every dimension. -/
theorem FractionFieldVanishingBound.upTo (h : FractionFieldVanishingBound.{u} n) (D : ℕ) :
    FractionFieldVanishingBoundUpTo.{u} n D :=
  fun B _ _ _ _ e he hpos _ hn => h B e he hpos hn

/-- The bound `⊤` holds for every scheme: there is no degree above it. -/
theorem isTorsionVanishingBound_top (X : Scheme.{u}) (n : ℕ) : IsTorsionVanishingBound X n ⊤ :=
  fun _ _ _ hp => absurd hp (not_lt.2 le_top)

/-- **The fraction field of a strictly henselian Noetherian local domain of dimension `b ≤ D`**,
given Corollary 1.2 up to dimension `D`: its cohomology with coefficients killed by `n > 0`
vanishes above `2b - 1` (truncated, so `0` when `b = 0`). In dimension `0` the domain is a
field equal to its separably closed residue field. -/
theorem isTorsionVanishingBound_spec_fractionRing_of_upTo {D : ℕ} (hn0 : 0 < n)
    (h : FractionFieldVanishingBoundUpTo.{u} n D) (B : Type u) [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [StrictlyHenselianLocalRing B] {b : ℕ} (hdim : ringKrullDim B = b)
    (hbD : b ≤ D) (hnB : IsUnit (n : B)) :
    IsTorsionVanishingBound (Spec (.of (FractionRing B))) n ((2 * b - 1 : ℕ) : WithBot ℕ∞) := by
  rcases Nat.eq_zero_or_pos b with rfl | hpos
  · have : Ring.KrullDimLE 0 B := Ring.krullDimLE_iff.2 (by rw [hdim])
    have hfield : IsField B := Ring.KrullDimLE.isField_of_isDomain
    have hres : Function.Bijective (IsLocalRing.residue B) := by
      refine ⟨?_, IsLocalRing.residue_surjective⟩
      rw [injective_iff_map_eq_zero]
      intro x hx
      have hx' : x ∈ RingHom.ker (IsLocalRing.residue B) := hx
      rwa [IsLocalRing.ker_residue, isField_iff_maximalIdeal_eq.1 hfield, Ideal.mem_bot] at hx'
    let e₁ : B ≃ₐ[B] FractionRing B := IsLocalization.atUnits B (nonZeroDivisors B)
      (fun y hy => (IsUnit.mem_submonoid_iff y).2
        (isUnit_iff_exists_inv.2 (hfield.mul_inv_cancel (nonZeroDivisors.ne_zero hy))))
    have : IsSepClosed (FractionRing B) :=
      IsSepClosed.of_ringEquiv (M := ResidueField B)
        (e₁.symm.toRingEquiv.trans (RingEquiv.ofBijective _ hres))
    exact (isTorsionVanishingBound_spec_of_isSepClosed (FractionRing B) hn0).mono
      (by exact_mod_cast Nat.zero_le _)
  · exact h B b hdim hpos hbD hnB

/-- The coheight of a prime `𝔭` is the dimension of `B ⧸ 𝔭`. -/
private lemma coheight_eq_ringKrullDim_quotient_asIdeal (B : Type u) [CommRing B]
    (P : PrimeSpectrum B) :
    (Order.coheight P : WithBot ℕ∞) = ringKrullDim (B ⧸ P.asIdeal) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  rfl

/-- **Height and coheight of a prime of a local ring of dimension `d`** are natural numbers
`a` and `b` with `a + b ≤ d`. -/
theorem exists_height_coheight_eq_of_ringKrullDim_eq {B : Type u} [CommRing B] {d : ℕ}
    (hd : ringKrullDim B = d) (y : PrimeSpectrum B) :
    ∃ a b : ℕ, Order.height y = a ∧ Order.coheight y = b ∧ a + b ≤ d := by
  have h := Order.height_add_coheight_le_krullDim y
  change _ ≤ ringKrullDim B at h
  rw [hd, ← WithBot.coe_add] at h
  have h' : Order.height y + Order.coheight y ≤ (d : ℕ∞) := by exact_mod_cast h
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1
    (ne_top_of_le_ne_top (ENat.coe_ne_top d) (le_trans le_self_add h'))
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1
    (ne_top_of_le_ne_top (ENat.coe_ne_top d) (le_trans le_add_self h'))
  refine ⟨a, b, ha.symm, hb.symm, ?_⟩
  rw [← ha, ← hb] at h'
  exact_mod_cast h'

/-- **The bound at a residue field of `Spec B`, from Corollary 1.2 up to dimension `D`.** At a
point `x` of `Spec B` of coheight `b ≤ D`, `κ(x) = Frac(B ⧸ 𝔭_x)` for the strictly henselian
Noetherian local domain `B ⧸ 𝔭_x` of dimension `b`, so its cohomology vanishes above
`2b - 1`. -/
theorem isTorsionVanishingBound_residueField_spec_of_upTo {D : ℕ} (hn0 : 0 < n)
    (h : FractionFieldVanishingBoundUpTo.{u} n D) {B : Type u} [CommRing B] [IsNoetherianRing B]
    [StrictlyHenselianLocalRing B] (hn : IsUnit (n : B)) (x : Spec (.of B)) {b : ℕ}
    (hb : Order.coheight (α := PrimeSpectrum B) x = b) (hbD : b ≤ D) :
    IsTorsionVanishingBound (Spec (.of ((Spec (.of B)).residueField x))) n
      ((2 * b - 1 : ℕ) : WithBot ℕ∞) := by
  let y : PrimeSpectrum B := x
  have : y.asIdeal.IsPrime := y.isPrime
  have : StrictlyHenselianLocalRing (B ⧸ y.asIdeal) :=
    StrictlyHenselianLocalRing.quotient y.isPrime.ne_top
  have hb' : Order.coheight y = b := hb
  have hdim : ringKrullDim (B ⧸ y.asIdeal) = b := by
    rw [← coheight_eq_ringKrullDim_quotient_asIdeal B y, hb']
    all_goals rfl
  have hnB : IsUnit (n : B ⧸ y.asIdeal) := by
    simpa only [map_natCast] using hn.map (Ideal.Quotient.mk y.asIdeal)
  have hfrac := isTorsionVanishingBound_spec_fractionRing_of_upTo hn0 h (B ⧸ y.asIdeal) hdim hbD
    hnB
  let eq : y.asIdeal.ResidueField ≃ₐ[B ⧸ y.asIdeal] FractionRing (B ⧸ y.asIdeal) :=
    IsLocalization.algEquiv (nonZeroDivisors (B ⧸ y.asIdeal)) _ _
  let c : CommRingCat.of (FractionRing (B ⧸ y.asIdeal)) ≅ (Spec (.of B)).residueField x :=
    eq.toRingEquiv.symm.toCommRingCatIso ≪≫ (Spec.residueFieldIso (.of B) y).symm
  exact IsTorsionVanishingBound.of_iso (Scheme.Spec.mapIso c.op) hfrac

/-- **The function field of the spectrum of a domain is its fraction field**, as an isomorphism
of commutative rings (`AlgebraicGeometry.functionField_isFractionRing_of_affine`). -/
def specFunctionFieldIsoFractionRing (R : CommRingCat.{u}) [IsDomain R] :
    (Spec R).functionField ≅ CommRingCat.of (FractionRing R) :=
  (IsLocalization.algEquiv (nonZeroDivisors R) (Spec R).functionField
    (FractionRing R)).toRingEquiv.toCommRingCatIso

/-- **Exposé XVIII-A, Theorem 1.1, for the opens of `Spec B` containing the generic point**, from
Lemma 2.1 and Corollary 1.2 in dimension `< e`. Let `B` be a strictly henselian Noetherian local
domain of dimension `e ≥ 1` with `n` invertible, and `U` an open of `Spec B` containing the
generic point. Then `cd_n(U) ≤ 2e - 1`.

For `𝓕` on `U` killed by `n`, `L = j_*𝓕` restricts to `𝓕` on `U`, has no higher cohomology on
the strictly local `Spec B`, and has `H^{i+1}_{X∖U}(X, L) = 0` for `i ≥ 2e` by Lemma 2.2 with
supports: every `y ∉ U` has `ht y ≥ 1`, the bound at `κ(y)` is `2 coht y - 1` with
`coht y ≤ e - 1`, and `ht y + coht y ≤ e`. -/
theorem isTorsionVanishingBound_opens_spec_of_upTo (h : PuncturedSpectrumVanishingBound.{u} n)
    {D : ℕ} (ih : FractionFieldVanishingBoundUpTo.{u} n D) (B : Type u) [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [StrictlyHenselianLocalRing B] {e : ℕ} (hd : ringKrullDim B = e)
    (hpos : 0 < e) (heD : e ≤ D + 1) (hn : IsUnit (n : B)) (U : (Spec (.of B)).Opens)
    (hU : genericPoint (Spec (.of B)) ∈ U) :
    IsTorsionVanishingBound U.toScheme n ((2 * e - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn
  intro F hF p hp
  have hp' : 2 * e ≤ p := by
    have : 2 * e - 1 < p := by exact_mod_cast hp
    omega
  let L := (Stacks.EtaleCohomology.etaleDirectImage.{u, 0} U.ι).obj F
  have hL : ∀ (T : (Spec (.of B)).Etale) (x : L.obj.obj (op T)), n • x = 0 :=
    (forall_nsmul_eq_zero_iff_nsmul_id_eq_zero L).2
      (nsmul_id_obj_eq_zero (Stacks.EtaleCohomology.etaleDirectImage.{u, 0} U.ι)
        ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero F).1 hF))
  refine (Stacks.EtaleCohomology.subsingleton_H_iff_of_iso
    ((Stacks.EtaleCohomology.directImageRestrictionIso.{u, 0} U.ι).app F) p).1 ?_
  refine subsingleton_sheafH_etaleRestriction_of_subsingleton_of_isZero U L p
    (Stacks.StrictlyHenselian.subsingleton_etaleCohomology_smallEtaleTopology B L p (by omega)) ?_
  have hnX : IsUnit (n : Γ(Spec (.of B), ⊤)) := by
    simpa only [map_natCast] using hn.map (Scheme.ΓSpecIso (.of B)).inv.hom
  have hgen : genericPoint (Spec (.of B)) = (⊥ : PrimeSpectrum B) :=
    genericPoint_eq_bot_of_affine (.of B)
  have hcoh : ∀ x : Spec (.of B), x ∉ U → ∃ a b : ℕ,
      Order.height (α := PrimeSpectrum B) x = a ∧ Order.coheight (α := PrimeSpectrum B) x = b ∧
        a + b ≤ e ∧ 1 ≤ a := by
    intro x hx
    obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq_of_ringKrullDim_eq hd
      (x : PrimeSpectrum B)
    refine ⟨a, b, ha, hb, hab, ?_⟩
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · exfalso
      subst ha0
      have hmin : IsMin (α := PrimeSpectrum B) x :=
        (Order.height_eq_zero (α := PrimeSpectrum B)).1 (by simpa using ha)
      have hbot : @Eq (PrimeSpectrum B) x ⊥ := hmin.eq_bot
      apply hx
      rw [show x = genericPoint (Spec (.of B)) from hbot.trans hgen.symm]
      exact hU
    · exact ha0
  let c : Spec (.of B) → WithBot ℕ∞ := fun x => if x ∈ U then ⊤ else
    ((2 * (Order.coheight (α := PrimeSpectrum B) x).toNat - 1 : ℕ) : WithBot ℕ∞)
  have hc : ∀ x, IsTorsionVanishingBound (Spec (.of ((Spec (.of B)).residueField x))) n (c x) := by
    intro x
    by_cases hx : x ∈ U <;> simp only [c, hx, ↓reduceIte]
    · exact isTorsionVanishingBound_top _ n
    · obtain ⟨a, b, ha, hb, hab, ha1⟩ := hcoh x hx
      rw [hb, ENat.toNat_coe]
      exact isTorsionVanishingBound_residueField_spec_of_upTo hn0 ih hn x hb (by omega)
  have hsup : (⨆ (x : Spec (.of B)) (_ : x ∉ U),
      (c x + 2 * ringKrullDim ((Spec (.of B)).presheaf.stalk x))) ≤
        ((2 * e : ℕ) : WithBot ℕ∞) := by
    refine iSup₂_le fun x hx => ?_
    obtain ⟨a, b, ha, hb, hab, ha1⟩ := hcoh x hx
    have hstalk : ringKrullDim ((Spec (.of B)).presheaf.stalk x) = ((a : ℕ) : WithBot ℕ∞) := by
      let y : PrimeSpectrum B := x
      have h1 : y.asIdeal.height = a := by
        rw [PrimeSpectrum.height_eq_orderHeight]
        exact ha
      rw [ringKrullDim_stalk_spec (CommRingCat.of B) x]
      exact congrArg (fun t : ℕ∞ => (t : WithBot ℕ∞)) h1
    simp only [c, hx, ↓reduceIte]
    rw [hb, ENat.toNat_coe, hstalk]
    exact_mod_cast (by omega : 2 * b - 1 + 2 * a ≤ 2 * e)
  exact isZero_rightDerived_opensSupport_of_genericPointSupportKilling
    (genericPointSupportKilling_of_localInputs
      (puncturedStalkVanishing_of_puncturedSpectrumVanishingBound h) (localSectionsAtPoint n))
    (Spec (.of B)) hnX c hc L hL U (p + 1)
    (lt_of_le_of_lt hsup (by exact_mod_cast (by omega : 2 * e < p + 1)))

/-- **The induction step of Corollary 1.2** (Exposé XVIII-A, Remark 1.3(a)). Given Lemma 2.1
and Corollary 1.2 up to dimension `D`, Corollary 1.2 holds for a strictly henselian Noetherian
local domain `B` of dimension `1 ≤ e ≤ D + 1`: `Spec (Frac B)` is the directed limit of the
affine open neighbourhoods of the generic point of `Spec B`, each of which has `cd_n ≤ 2e - 1`
(`AlgebraicGeometry.Scheme.isTorsionVanishingBound_opens_spec_of_upTo`). -/
theorem isTorsionVanishingBound_fractionRing_of_upTo (h : PuncturedSpectrumVanishingBound.{u} n)
    {D : ℕ} (ih : FractionFieldVanishingBoundUpTo.{u} n D) (B : Type u) [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [StrictlyHenselianLocalRing B] {e : ℕ} (hd : ringKrullDim B = e)
    (hpos : 0 < e) (heD : e ≤ D + 1) (hn : IsUnit (n : B)) :
    IsTorsionVanishingBound (Spec (.of (FractionRing B))) n ((2 * e - 1 : ℕ) : WithBot ℕ∞) := by
  let X := Spec (.of B)
  let η := genericPoint X
  obtain ⟨V₀, -⟩ := exists_affineOpenNhds_le X η ⊤
  have hlim : IsTorsionVanishingBound (Spec (X.presheaf.stalk η)) n
      ((2 * e - 1 : ℕ) : WithBot ℕ∞) :=
    isTorsionVanishingBound_of_isLimit_of_isDirected
      (localAffineEtaleDiagram η V₀ ⋙ Scheme.Etale.forget X ⋙ Over.forget X)
      (isLimitLocalAffineCone η V₀) fun i =>
        isTorsionVanishingBound_opens_spec_of_upTo h ih B hd hpos heD hn
          (OrderDual.ofDual i.unop).1 (OrderDual.ofDual i.unop).2.2.1
  have : IsDomain (CommRingCat.of B) := inferInstanceAs (IsDomain B)
  exact IsTorsionVanishingBound.of_iso
    (Scheme.Spec.mapIso (specFunctionFieldIsoFractionRing (CommRingCat.of B)).op) hlim

/-- **Exposé XVIII-A, Corollary 1.2, up to every dimension, from Lemma 2.1**, by induction on
the dimension. -/
theorem fractionFieldVanishingBoundUpTo_of_puncturedSpectrumVanishingBound
    (h : PuncturedSpectrumVanishingBound.{u} n) (D : ℕ) :
    FractionFieldVanishingBoundUpTo.{u} n D := by
  induction D with
  | zero => exact fun B _ _ _ _ e _ hpos hle _ => absurd hle (by omega)
  | succ D ih => exact fun B _ _ _ _ e hd hpos heD hn =>
    isTorsionVanishingBound_fractionRing_of_upTo h ih B hd hpos heD hn

/-- **Travaux de Gabber, Exposé XVIII-A, Corollary 1.2, from Lemma 2.1**, for coefficients killed
by `n`: the bound `2d - 1` for the punctured spectra of strictly henselian Noetherian local rings
of dimension `d ≥ 1` gives the bound `2e - 1` for the fraction fields of strictly henselian
Noetherian local domains of dimension `e ≥ 1`. This is the converse of
`AlgebraicGeometry.Scheme.puncturedSpectrumVanishingBound_of_fractionFieldVanishingBound`. -/
theorem fractionFieldVanishingBound_of_puncturedSpectrumVanishingBound
    (h : PuncturedSpectrumVanishingBound.{u} n) : FractionFieldVanishingBound.{u} n :=
  fun B _ _ _ _ e hd hpos hn =>
    fractionFieldVanishingBoundUpTo_of_puncturedSpectrumVanishingBound h e B e hd hpos le_rfl hn

end AlgebraicGeometry.Scheme

end
