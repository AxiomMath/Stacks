module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Associated points on an affine open

For a quasi-coherent sheaf `F` on a scheme `X` and an affine open `U`, the points of `U`
associated to `F` are compared with the primes of `Γ(X, U)` associated to the module of
sections `Γ(F, U)`.

An associated prime of `Γ(F, U)` always yields an associated point of `F`, and the converse
holds as soon as the corresponding prime ideal is finitely generated, hence on a locally
Noetherian scheme. For *weakly* associated points no finiteness is needed: the two conditions
always agree.

## Main results

* `AlgebraicGeometry.isAssociatedPoint_of_isAssociatedPrime_sections` and
  `AlgebraicGeometry.isAssociatedPrime_sections_of_isAssociatedPoint_of_fg` are the two
  implications, and
  `AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian`
  the resulting equivalence over a locally Noetherian scheme.
* `AlgebraicGeometry.isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint`: a point of an affine
  open is weakly associated to `F` exactly when the corresponding prime is weakly associated to
  `Γ(F, U)`.

## Implementation notes

An affine open `U` is presented by `U : X.Opens` together with `IsAffineOpen U`; the prime of
`Γ(X, U)` corresponding to `x ∈ U` is `IsAffineOpen.primeIdealOf`. Everything rests on the
stalk `F_x` being the localization of `Γ(F, U)` at that prime, which is
`AlgebraicGeometry.affineGerm_isLocalized`.

## References

* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks Project, Tag 056M](https://stacks.math.columbia.edu/tag/056M)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Descent of an exact-annihilator associated prime along a localization of modules at a
finitely generated prime: if the maximal ideal of the localized ring is an associated prime of
the localized module, then the prime itself is an associated prime of the original module. -/
private lemma exactAssociated_of_localize {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Algebra R S] [IsLocalRing S]
    [Module S N] [tower : IsScalarTower R S N] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime S p] (f : M →ₗ[R] N) [loc : IsLocalizedModule p.primeCompl f]
    (hfg : p.FG)
    (h : IsAssociatedPrimeStacks S N (IsLocalRing.maximalIdeal S)) :
    IsAssociatedPrimeStacks R M p := by
  classical
  obtain ⟨-, n, hn⟩ := h
  obtain ⟨T, hT⟩ := hfg
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p.primeCompl f n
  have kill (a : T) : ∃ t : p.primeCompl, t.1 • (a.1 • m) = 0 := by
    have ha : a.1 ∈ p := by
      rw [← hT]
      exact Ideal.subset_span a.2
    have ha' : algebraMap R S a.1 ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff S p a.1).mpr ha
    have hz : algebraMap R S a.1 • IsLocalizedModule.mk' f m s = 0 :=
      Submodule.mem_colon_span_singleton.mp (hn.symm ▸ ha')
    rw [← IsLocalization.mk'_one (M := p.primeCompl) S a.1,
      IsLocalizedModule.mk'_smul_mk' S f a.1 m 1 s, IsLocalizedModule.mk'_eq_zero' f] at hz
    simpa using hz
  choose g hg using kill
  let v : p.primeCompl := ∏ a : T, g a
  have hkill (a : T) : a.1 • (v.1 • m) = 0 := by
    obtain ⟨w, hw⟩ : (g a).1 ∣ v.1 := by
      simpa [v] using (Finset.dvd_prod_of_mem (s := Finset.univ)
        (f := fun a : T => (g a).1) (Finset.mem_univ a))
    calc
      a.1 • (v.1 • m) = w • ((g a).1 • (a.1 • m)) := by
        rw [hw]
        simp only [mul_smul]
        rw [smul_comm a.1 (g a).1, smul_comm a.1 w, smul_comm (g a).1 w]
      _ = 0 := by rw [hg a, smul_zero]
  refine ⟨inferInstance, v.1 • m, ?_⟩
  apply le_antisymm
  · intro r hr
    have hz : (r * v.1) • m = 0 := by
      simpa only [mul_smul, smul_comm r] using
        (show r • (v.1 • m) = 0 by
          simpa only [Submodule.mem_bot] using
            (Submodule.mem_colon_span_singleton.mp hr))
    have hz' : algebraMap R S (r * v.1) • IsLocalizedModule.mk' f m s = 0 := by
      rw [← IsLocalization.mk'_one (M := p.primeCompl) S (r * v.1),
        IsLocalizedModule.mk'_smul_mk' S f (r * v.1) m 1 s, hz]
      exact IsLocalizedModule.mk'_zero f _
    have hmem : algebraMap R S (r * v.1) ∈
        (⊥ : Submodule S N).colon (Submodule.span S {IsLocalizedModule.mk' f m s}) :=
      Submodule.mem_colon_span_singleton.mpr (by simpa using hz')
    have hmem' : algebraMap R S (r * v.1) ∈ IsLocalRing.maximalIdeal S := hn ▸ hmem
    have hrv : r * v.1 ∈ p := (IsLocalization.AtPrime.to_map_mem_maximal_iff S p _).mp hmem'
    exact ((inferInstance : p.IsPrime).mul_mem_iff_mem_or_mem.mp hrv).resolve_right
      (Ideal.mem_primeCompl_iff.mp v.2)
  · have hle : Ideal.span (T : Set R) ≤
        (⊥ : Submodule R M).colon (Submodule.span R {v.1 • m}) := by
      rw [Ideal.span_le]
      intro r hr
      exact Submodule.mem_colon_span_singleton.mpr
        (by simpa only [Submodule.mem_bot] using hkill ⟨r, hr⟩)
    exact hT ▸ hle

/-- **Stacks 02OK, part (1).** An associated prime of the sections of a quasi-coherent sheaf on
an affine open gives an associated point of the sheaf. -/
@[stacks 02OK "part (1)"]
theorem isAssociatedPoint_of_isAssociatedPrime_sections {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (h : IsAssociatedPrimeStacks Γ(X, U) Γ(F, U) (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    Stacks.Divisors.IsAssociatedPoint F x := by
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hx⟩
  let : IsLocalRing (X.presheaf.stalk x) := IsLocalization.AtPrime.isLocalRing _ p
  obtain ⟨hp, m, hm⟩ := h
  change IsAssociatedPrimeStacks (X.presheaf.stalk x) (F.presheaf.stalk x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  refine ⟨(IsLocalRing.maximalIdeal.isMaximal _).isPrime, F.presheaf.germ U x hx m, ?_⟩
  ext z
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
  rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot,
    IsLocalization.AtPrime.mk'_mem_maximal_iff (X.presheaf.stalk x) p r s]
  have hs : IsUnit (IsLocalization.mk' (X.presheaf.stalk x) (1 : Γ(X, U)) s) :=
    (IsLocalization.AtPrime.isUnit_mk'_iff (X.presheaf.stalk x) p 1 s).mpr
      (one_mem p.primeCompl)
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_smul,
    smul_comm (algebraMap Γ(X, U) (X.presheaf.stalk x) r)
    (IsLocalization.mk' (X.presheaf.stalk x) 1 s), hs.smul_eq_zero]
  have hsmul : (algebraMap Γ(X, U) (X.presheaf.stalk x) r) • F.presheaf.germ U x hx m =
      F.presheaf.germ U x hx (r • m) := (F.val.germ_smul x U hx r m).symm
  rw [hsmul, germ_eq_zero_iff_exists_smul_eq_zero_affine F U hU x hx]
  constructor
  · rintro ⟨g, hg, hgr⟩
    have hmem : g * r ∈ p := by
      apply hm ▸ (Submodule.mem_colon_span_singleton.mpr ?_)
      simpa only [Submodule.mem_bot, mul_smul] using hgr
    exact (hp.mul_mem_iff_mem_or_mem.mp hmem).resolve_left hg
  · intro hr
    have hr_ann : r ∈ (⊥ : Submodule Γ(X, U) Γ(F, U)).colon (Submodule.span Γ(X, U) {m}) :=
      hm ▸ hr
    exact ⟨1, p.primeCompl.one_mem, by simpa using Submodule.mem_colon_span_singleton.mp hr_ann⟩

/-- **Stacks 02OK, part (2).** If the prime corresponding to an associated point is finitely
generated, then it is associated to the module of sections on the affine open. -/
@[stacks 02OK "part (2)"]
theorem isAssociatedPrime_sections_of_isAssociatedPoint_of_fg {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (hfg : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.FG) (h : Stacks.Divisors.IsAssociatedPoint F x) :
    IsAssociatedPrimeStacks Γ(X, U) Γ(F, U) (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hx⟩
  let : IsLocalRing (X.presheaf.stalk x) := IsLocalization.AtPrime.isLocalRing _ p
  let : Module Γ(X, U) (F.presheaf.stalk x) := affineStalkModule F U x hx
  change IsAssociatedPrimeStacks Γ(X, U) Γ(F, U) p
  exact exactAssociated_of_localize
    (tower := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)) p (affineGerm F U x hx)
    (loc := affineGerm_isLocalized F U hU x hx) hfg h

/-- **Stacks 02OK, locally Noetherian case.** On a locally Noetherian scheme, the prime
corresponding to a point of an affine open is associated to the module of sections exactly when
the point is associated to the sheaf. -/
@[stacks 02OK "locally Noetherian case", ega "IV 3.1.2" "more general"]
theorem isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    IsAssociatedPrimeStacks Γ(X, U) Γ(F, U) (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔
      Stacks.Divisors.IsAssociatedPoint F x := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact ⟨isAssociatedPoint_of_isAssociatedPrime_sections F U hU hx,
    isAssociatedPrime_sections_of_isAssociatedPoint_of_fg F U hU hx
      (Ideal.FG.of_isNoetherianRing _)⟩

/-- Weak association of the maximal ideal of a localization at a prime is weak association of
that prime for the original module. -/
private theorem isWeaklyAssociatedPrime_iff_of_isLocalization_atPrime {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module S M'] [tower : IsScalarTower R S M'] (p : Ideal R)
    [p.IsPrime] [IsLocalization.AtPrime S p] [IsLocalRing S] (g : M →ₗ[R] M')
    [loc : IsLocalizedModule p.primeCompl g] :
    IsWeaklyAssociatedPrime R M p ↔
      IsWeaklyAssociatedPrime S M' (IsLocalRing.maximalIdeal S) := by
  change WeaklyAssociated p M ↔ WeaklyAssociated (IsLocalRing.maximalIdeal S) M'
  let m : Ideal S := IsLocalRing.maximalIdeal S
  have hmp : m.IsPrime := (IsLocalRing.maximalIdeal.isMaximal S).isPrime
  have hcomap_m : Ideal.comap (algebraMap R S) m = p := by
    simpa [Ideal.under] using IsLocalization.AtPrime.under_maximalIdeal S p
  constructor
  · rintro ⟨x, ⟨-, hxp⟩, hmin⟩
    refine ⟨g x, ⟨hmp, ?_⟩, fun q ⟨hq, hAq⟩ hqm ↦ ?_⟩
    · exact (annOfElem_localized_le_iff p.primeCompl g x m hmp).mpr (hxp.trans hcomap_m.ge)
    · have hq'p : Ideal.comap (algebraMap R S) q ≤ p :=
        (Ideal.comap_mono hqm).trans hcomap_m.le
      refine (congrArg PrimeSpectrum.asIdeal
        (PrimeSpectrum.localization_comap_injective S p.primeCompl
          (a₁ := ⟨q, hq⟩) (a₂ := ⟨m, hmp⟩) (PrimeSpectrum.ext ?_))).ge
      exact (hq'p.antisymm (hmin ⟨Ideal.comap_isPrime (algebraMap R S) q,
        (annOfElem_localized_le_iff p.primeCompl g x q hq).mp hAq⟩ hq'p)).trans hcomap_m.symm
  · rintro ⟨t, ht⟩
    obtain ⟨⟨x, s⟩, hsx⟩ := IsLocalizedModule.surj p.primeCompl g t
    obtain ⟨v, hv⟩ := IsLocalization.map_units S s
    have hann : annihilatorOfElem_semiring (R := S) (g x) = annihilatorOfElem_semiring t := by
      have h1 : g x = (v : S) • t := by
        rw [hv, algebraMap_smul]
        exact hsx.symm
      rw [annihilatorOfElem_semiring, annihilatorOfElem_semiring, h1,
        Submodule.span_singleton_smul_eq v.isUnit]
    rw [← hann] at ht
    obtain ⟨⟨-, hAm⟩, hmin⟩ := ht
    refine ⟨x, ⟨inferInstance, ?_⟩, fun q' ⟨hq', hAq'⟩ hq'p ↦ ?_⟩
    · exact ((annOfElem_localized_le_iff p.primeCompl g x m hmp).mp hAm).trans hcomap_m.le
    · let e := IsLocalization.AtPrime.orderIsoOfPrime S p
      let q : Ideal S := (e.symm ⟨q', hq', hq'p⟩).val
      have hq : q.IsPrime := (e.symm ⟨q', hq', hq'p⟩).property
      have hqcomap : Ideal.comap (algebraMap R S) q = q' :=
        congrArg Subtype.val (e.apply_symm_apply ⟨q', hq', hq'p⟩)
      have hmq : m ≤ q := hmin
        ⟨hq, (annOfElem_localized_le_iff p.primeCompl g x q hq).mpr (hAq'.trans hqcomap.ge)⟩
        (IsLocalRing.le_maximalIdeal hq.ne_top)
      exact hcomap_m.symm.trans_le ((Ideal.comap_mono hmq).trans_eq hqcomap)

/-- **Stacks Project, Tag 056M.** On an affine open, a point is weakly associated to a
quasi-coherent sheaf if and only if its corresponding prime ideal is weakly associated to the
module of sections. -/
@[stacks 056M]
theorem isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    IsWeaklyAssociatedPrime Γ(X, U) Γ(F, U) (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint F x := by
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hx⟩
  let : IsLocalRing (X.presheaf.stalk x) := IsLocalization.AtPrime.isLocalRing _ p
  let : Module Γ(X, U) (F.presheaf.stalk x) := affineStalkModule F U x hx
  change IsWeaklyAssociatedPrime Γ(X, U) Γ(F, U) p ↔
    IsWeaklyAssociatedPrime (X.presheaf.stalk x) (F.presheaf.stalk x) (IsLocalRing.maximalIdeal _)
  exact isWeaklyAssociatedPrime_iff_of_isLocalization_atPrime
    (tower := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)) p (affineGerm F U x hx)
    (loc := affineGerm_isLocalized F U hU x hx)

end AlgebraicGeometry
