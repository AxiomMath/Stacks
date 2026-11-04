module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localizing at a prime commutes with passing to a quotient

If `Bq` is the localization of `B` at a prime `𝔫`, and `𝔮` is a prime of `B ⧸ J` contracting to
`𝔫`, then `Bq ⧸ J Bq` is the localization of `B ⧸ J` at `𝔮`.

## Main results

* `isLocalization_atPrime_quotient`: the quotient of the localization at a prime `𝔫` is the
  localization of the quotient at a prime lying over `𝔫`.
-/

@[expose] public section

/-- The quotient of the localization at a prime `𝔫` is the localization of the quotient at a prime
`𝔮` lying over `𝔫`. -/
theorem isLocalization_atPrime_quotient {B : Type*} [CommRing B]
    (𝔫 : Ideal B) [𝔫.IsPrime] (Bq : Type*) [CommRing Bq] [Algebra B Bq]
    [IsLocalization.AtPrime Bq 𝔫] (J : Ideal B)
    (𝔮 : Ideal (B ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = 𝔫) :
    IsLocalization.AtPrime (Bq ⧸ J.map (algebraMap B Bq)) 𝔮 := by
  have hsub : Algebra.algebraMapSubmonoid (B ⧸ J) 𝔫.primeCompl = 𝔮.primeCompl := by
    subst h𝔮
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨fun ⟨z, hz, hzy⟩ hy ↦ hz ?_, fun hy ↦ ⟨y, hy, rfl⟩⟩
    rwa [SetLike.mem_coe, Ideal.mem_comap, ← Ideal.Quotient.algebraMap_eq, hzy]
  have := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
    (M := 𝔫.primeCompl) (S := Bq) J
  rwa [hsub] at this
