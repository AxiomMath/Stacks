module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.RingTheory.Depth.Localization
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCutoff
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Depth.AlgebraMap

/-!
# The local cohomology cutoff does not decrease under localization

Let `A` be a commutative ring, `I ⊆ A` an ideal, `M` an `A`-module and `P` a prime of `A`. The
admissible pairs of primes for the cutoff `s_{A_P, I A_P}(M_P)` are exactly the images of the
admissible pairs `p ⊆ q ⊆ P` for `s_{A, I}(M)`, and each such pair contributes the same value on
both sides: the two depth terms agree because `(A_P)_{p A_P} = A_p` compatibly with the
localizations of `M`, and the two height terms agree because the image of `q` in `A_P / p A_P`
lies over the image of `q` in `A / p`. Taking the infimum over a subfamily can only increase it,
so

`s_{A, I}(M) ≤ s_{A_P, I A_P}(M_P)`.

## Main results

* `Stacks.LocalCohomology.depth_localizedModule_localizationLocalization` — localizing twice at
  compatible primes computes the same depth as localizing once.
* `Stacks.LocalCohomology.height_map_quotientMk_localization` — the relative height of a pair of
  primes is unchanged by localization at a multiplicative set disjoint from the larger one.
* `Stacks.LocalCohomology.localCohomologyCutoff_le_localization` — the cutoff does not decrease
  on passing to a localization at a prime.

## Implementation notes

The depth comparison is phrased for an arbitrary multiplicative set `S` and a prime `q` of
`S⁻¹A`, with `p = q ∩ A`; the isomorphism `A_p ≅ (S⁻¹A)_q` is
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization`, transported to modules through
`IsBaseChange`.

## References

* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
-/

@[expose] public section

universe u v

namespace Stacks.LocalCohomology

/-- Localizing `M` at a prime `p` of `A` and localizing `S⁻¹M` at a prime `q` of `S⁻¹A` lying
over `p` give modules of the same depth over the corresponding local rings. -/
theorem depth_localizedModule_localizationLocalization
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (S : Submonoid A) (q : Ideal (Localization S)) [q.IsPrime] :
    Module.depth (Localization.AtPrime (q.comap (algebraMap A (Localization S))))
        (IsLocalRing.maximalIdeal
          (Localization.AtPrime (q.comap (algebraMap A (Localization S)))))
        (LocalizedModule (q.comap (algebraMap A (Localization S))).primeCompl M) =
      Module.depth (Localization.AtPrime q) (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (LocalizedModule q.primeCompl (LocalizedModule S M)) := by
  classical
  let p := q.comap (algebraMap A (Localization S))
  let L0 := Localization.AtPrime p
  let L1 := Localization.AtPrime q
  let M0 := LocalizedModule p.primeCompl M
  let MS := LocalizedModule S M
  let M1 := LocalizedModule q.primeCompl MS
  let e : L0 ≃ₐ[A] L1 :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := S) q
  let : Algebra L0 L1 := RingHom.toAlgebra e.toRingEquiv.toRingHom
  let : Module L1 M0 := Module.compHom M0 e.toRingEquiv.symm.toRingHom
  let : IsScalarTower L0 L1 M0 := IsScalarTower.of_algebraMap_smul fun x m =>
    congrArg (· • m) (e.toRingEquiv.symm_apply_apply x)
  let : IsScalarTower A L0 L1 := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (e.commutes x).symm)
  let : IsScalarTower A L1 M0 := IsScalarTower.of_algebraMap_smul fun x m => by
    show e.toRingEquiv.symm (algebraMap A L1 x) • m = x • m
    rw [← e.commutes x]
    exact (congrArg (· • m) (e.toRingEquiv.symm_apply_apply _)).trans
      (IsScalarTower.algebraMap_smul L0 x m)
  let f₁ : M →ₗ[A] MS := LocalizedModule.mkLinearMap S M
  let f₂ : MS →ₗ[Localization S] M1 := LocalizedModule.mkLinearMap q.primeCompl MS
  let f : M →ₗ[A] M1 := (f₂.restrictScalars A).comp f₁
  have hstandard : IsBaseChange L1 (LocalizedModule.mkLinearMap p.primeCompl M) :=
    IsLocalizedModule.isBaseChange p.primeCompl L1 _
  have hfirst : IsBaseChange (Localization S) f₁ := LocalizedModule.isBaseChange S M
  have hsecond : IsBaseChange L1 f₂ := IsLocalizedModule.isBaseChange q.primeCompl L1 f₂
  have hcomp : IsBaseChange L1 f := by
    dsimp [f]
    exact hfirst.comp hsecond
  let eM : M0 ≃ₗ[L1] M1 := hstandard.equiv.symm.trans hcomp.equiv
  have hdepthRing : Module.depth L0 (IsLocalRing.maximalIdeal L0) M0 =
      Module.depth L1 (IsLocalRing.maximalIdeal L1) M0 := by
    rw [Module.depth_eq_depth_map_algebraMap e.surjective]
    show Module.depth L1 ((IsLocalRing.maximalIdeal L0).map e.toRingEquiv.toRingHom) M0 = _
    have hmax : (IsLocalRing.maximalIdeal L0).map e.toRingEquiv.toRingHom =
        IsLocalRing.maximalIdeal L1 := IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
    rw [hmax]
  show Module.depth L0 (IsLocalRing.maximalIdeal L0) M0 =
    Module.depth L1 (IsLocalRing.maximalIdeal L1) M1
  exact hdepthRing.trans (Module.depth_eq_depth_of_linearEquiv _ eM)

/-- For primes `p ≤ q` of `A` with `q` disjoint from a multiplicative set `S`, the height of the
image of `q` in `A / p` equals the height of the image of `q S⁻¹A` in `S⁻¹A / p S⁻¹A`: the
quotient map identifies `S⁻¹A / p S⁻¹A` with a localization of `A / p`, and the image of `q`
there lies over the image of `q`. -/
theorem height_map_quotientMk_localization {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (S : Submonoid A) [IsLocalization S B]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    (hS : Disjoint (S : Set A) (q : Set A)) :
    (q.map (Ideal.Quotient.mk p)).height =
      ((q.map (algebraMap A B)).map
        (Ideal.Quotient.mk (p.map (algebraMap A B)))).height := by
  let pB := p.map (algebraMap A B)
  let qB := q.map (algebraMap A B)
  let A₀ := A ⧸ p
  let B₀ := B ⧸ pB
  let q₀ := q.map (Ideal.Quotient.mk p)
  let q₁ := qB.map (Ideal.Quotient.mk pB)
  let S₀ := Algebra.algebraMapSubmonoid A₀ S
  have hle : p ≤ Ideal.comap (algebraMap A B) pB := fun x hx =>
    Ideal.mem_map_of_mem (algebraMap A B) hx
  let fquot := Ideal.quotientMap pB (algebraMap A B) hle
  let : Algebra A₀ B₀ := Ideal.Quotient.algebraQuotientMapQuotient
  let : IsLocalization S₀ B₀ :=
    IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap S B p
  have hq₀ : q₀.IsPrime := by
    dsimp [q₀]
    exact Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have hdisj : Disjoint (S₀ : Set A₀) (q₀ : Set A₀) := by
    rw [Set.disjoint_left] at hS ⊢
    intro x hxS hxq
    obtain ⟨s, hs, rfl⟩ := (Submonoid.mem_map).mp hxS
    apply hS hs
    have hs' : s ∈ Ideal.comap (Ideal.Quotient.mk p) q₀ := hxq
    rwa [Ideal.comap_map_quotientMk, sup_eq_right.mpr hpq] at hs'
  have hcomp : (algebraMap A₀ B₀).comp (Ideal.Quotient.mk p) =
      (Ideal.Quotient.mk pB).comp (algebraMap A B) := by
    ext a
    show fquot (Ideal.Quotient.mk p a) = Ideal.Quotient.mk pB (algebraMap A B a)
    exact Ideal.quotientMap_mk
  have hmap : Ideal.map (algebraMap A₀ B₀) q₀ = q₁ := by
    dsimp [q₀, q₁, qB, pB]
    calc
      Ideal.map (algebraMap A₀ B₀) (Ideal.map (Ideal.Quotient.mk p) q) =
          Ideal.map ((algebraMap A₀ B₀).comp (Ideal.Quotient.mk p)) q := Ideal.map_map _ _
      _ = Ideal.map ((Ideal.Quotient.mk pB).comp (algebraMap A B)) q := by rw [hcomp]
      _ = Ideal.map (Ideal.Quotient.mk pB) (Ideal.map (algebraMap A B) q) :=
        (Ideal.map_map _ _).symm
  have hunder : Ideal.under A₀ q₁ = q₀ := by
    rw [← hmap]
    exact IsLocalization.under_map_of_isPrime_disjoint S₀ B₀ hq₀ hdisj
  exact (congrArg Ideal.height hunder).symm.trans (IsLocalization.height_under S₀ q₁)

/-- **The cutoff does not decrease under localization at a prime.** Each admissible pair of
primes of `A_P` comes from an admissible pair of `A`, contributing the same depth and the same
relative height, so the infimum over the smaller family is at least the infimum over the
larger. -/
theorem localCohomologyCutoff_le_localization
    {A : Type u} [CommRing A] (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (P : Ideal A) [P.IsPrime] :
    localCohomologyCutoff A I M ≤
      localCohomologyCutoff (Localization.AtPrime P)
        (I.map (algebraMap A (Localization.AtPrime P)))
        (LocalizedModule P.primeCompl M) := by
  classical
  let R := Localization.AtPrime P
  rw [le_localCohomologyCutoff_iff]
  intro p' q' hp' hq' hp'q'
  let p := p'.asIdeal.comap (algebraMap A R)
  let q := q'.asIdeal.comap (algebraMap A R)
  have hqP : q ≤ P := (IsLocalization.AtPrime.primeSpectrumOrderIso R P q').property
  have hpq : p ≤ q := Ideal.comap_mono hp'q'
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have hp : ¬ I ≤ p := fun h => hp' ((Ideal.map_le_iff_le_comap).2 h)
  have hq : I ≤ q := (Ideal.map_le_iff_le_comap).1 hq'
  have hdisj : Disjoint (P.primeCompl : Set A) (q : Set A) :=
    Set.disjoint_left.2 fun _ hxS hxq => hxS (hqP hxq)
  have hdepth := depth_localizedModule_localizationLocalization
    (A := A) (M := M) P.primeCompl p'.asIdeal
  have hheight := height_map_quotientMk_localization (A := A) (B := R)
    P.primeCompl p q hpq hdisj
  have hmap (J : Ideal R) [J.IsPrime] : (J.comap (algebraMap A R)).map (algebraMap A R) = J :=
    IsLocalization.map_under P.primeCompl R J
  rw [hmap p'.asIdeal, hmap q'.asIdeal] at hheight
  exact (localCohomologyCutoff_le A I M ⟨p, inferInstance⟩ ⟨q, inferInstance⟩ hp hq hpq).trans_eq
    (by rw [hdepth, hheight])

end Stacks.LocalCohomology
