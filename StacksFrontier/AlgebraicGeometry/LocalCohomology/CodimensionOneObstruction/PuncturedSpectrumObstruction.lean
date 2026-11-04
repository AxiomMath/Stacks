module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.CompletedLocalPuncturedSpectrum
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.PrimeIdealOfTop
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.SectionsFunctionField
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.StructureSheafObstruction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Non-coherence on the punctured spectrum of a Noetherian local ring

Let `Λ` be a Noetherian local ring with an associated prime `𝔭` satisfying `dim(Λ ⧸ 𝔭) = 1`, and
let `V = Spec Λ ∖ {closed point}` be the punctured spectrum. Then the direct image of the
structure sheaf of `V` along the open immersion `V → Spec Λ` is not coherent.

## Main results

In the namespace `Stacks.AlgebraicGeometry.CodimensionOneObstruction`.

* `not_isCoherent_pushforward_puncturedSpectrum_of_isAssociatedPrime`: the statement above.
* `not_moduleFinite_sections_puncturedSpectrum_of_isAssociatedPrime`: under the same
  hypotheses, the sections of `Spec Λ` over `V` are not a finite module over the global sections.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace
open Stacks.LocalCohomology (puncturedSpectrum)

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

/-- An associated prime in the sense of [Stacks, Tag 00LA] contracts along a ring isomorphism to
an associated prime: if `q` is the annihilator of an element of `T` and `e : R ≃+* T`, then the
contraction of `q` along `e` is the annihilator of the preimage of that element. -/
private theorem isAssociatedPrimeStacks_comap_of_ringEquiv {R T : Type*} [CommRing R]
    [CommRing T] (e : R ≃+* T) {q : Ideal T} (hq : (q.comap (e : R →+* T)).IsPrime)
    (h : IsAssociatedPrimeStacks T T q) :
    IsAssociatedPrimeStacks R R (q.comap (e : R →+* T)) := by
  obtain ⟨-, m, hm⟩ := h
  refine ⟨hq, e.symm m, ?_⟩
  ext r
  rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot, smul_eq_mul, Ideal.mem_comap,
    ← hm, Submodule.mem_colon_span_singleton, Submodule.mem_bot, smul_eq_mul]
  refine ⟨fun hr => ?_, fun hr => e.injective ?_⟩
  · simpa using congrArg e hr
  · simpa using hr

/-- A prime of a local ring whose quotient has Krull dimension one lies in the punctured
spectrum. -/
private theorem mem_puncturedSpectrum_of_ringKrullDim_quotient_eq_one (Λ : CommRingCat.{u})
    [IsLocalRing Λ] {p : PrimeSpectrum Λ} (hdim : ringKrullDim (Λ ⧸ p.asIdeal) = 1) :
    (p : Spec Λ) ∈ puncturedSpectrum Λ := by
  intro hcon
  have hpm : p.asIdeal = maximalIdeal Λ := congrArg PrimeSpectrum.asIdeal hcon
  rw [hpm] at hdim
  let : Field (Λ ⧸ maximalIdeal Λ) := Ideal.Quotient.field _
  rw [ringKrullDim_eq_zero_of_field] at hdim
  exact absurd hdim (by decide)

/-- An associated prime of `Λ` as a module over itself is an associated point of the structure
sheaf of `Spec Λ`. -/
@[ega "IV 3.1.2" "Sufficiency"]
private theorem isAssociatedPoint_unit_of_isAssociatedPrime (Λ : CommRingCat.{u})
    {p : PrimeSpectrum Λ} (hp : IsAssociatedPrimeStacks Λ Λ p.asIdeal) :
    Stacks.Divisors.IsAssociatedPoint
      (SheafOfModules.unit (Spec Λ).ringCatSheaf) (p : Spec Λ) := by
  have : p.asIdeal.IsPrime := p.isPrime
  have : (SheafOfModules.unit (Spec Λ).ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  refine isAssociatedPoint_of_isAssociatedPrime_sections _ ⊤ (isAffineOpen_top (Spec Λ)) trivial ?_
  rw [primeIdealOf_top_spec Λ (p : Spec Λ)]
  exact isAssociatedPrimeStacks_comap_of_ringEquiv (Scheme.ΓSpecIso Λ).commRingCatIsoToRingEquiv
    inferInstance hp

/-- If `dim(Λ ⧸ 𝔭) = 1`, then the image of the prime of the closed point in the quotient of the
sections over the top open of `Spec Λ` by the prime of `𝔭` has height at most one. -/
private theorem height_quotient_primeIdealOf_top_le_one (Λ : CommRingCat.{u}) [IsLocalRing Λ]
    {p : PrimeSpectrum Λ} (hdim : ringKrullDim (Λ ⧸ p.asIdeal) = 1) :
    (((isAffineOpen_top (Spec Λ)).primeIdealOf ⟨closedPoint Λ, trivial⟩).asIdeal.map
        (Ideal.Quotient.mk
          ((isAffineOpen_top (Spec Λ)).primeIdealOf
            ⟨(p : Spec Λ), trivial⟩).asIdeal)).height ≤ 1 := by
  have : p.asIdeal.IsPrime := p.isPrime
  let ε : Γ(Spec Λ, ⊤) ≃+* Λ := (Scheme.ΓSpecIso Λ).commRingCatIsoToRingEquiv
  let f : Γ(Spec Λ, ⊤) →+* Λ := ε
  have hεhom : f = (Scheme.ΓSpecIso Λ).hom.hom := rfl
  have hmapP : (p.asIdeal.comap f).map f = p.asIdeal :=
    Ideal.map_comap_of_surjective _ ε.surjective _
  have hdim' : ringKrullDim (Γ(Spec Λ, ⊤) ⧸ p.asIdeal.comap f) = 1 :=
    (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ p.asIdeal ε hmapP.symm)).trans hdim
  have hprime : (((maximalIdeal Λ).comap f).map (Ideal.Quotient.mk (p.asIdeal.comap f))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact Ideal.comap_mono (le_maximalIdeal_of_isPrime p.asIdeal))
  rw [primeIdealOf_top_spec Λ (p : Spec Λ), primeIdealOf_top_spec Λ (closedPoint Λ), ← hεhom]
  exact_mod_cast hdim' ▸ Ideal.height_le_ringKrullDim_of_ne_top hprime.ne_top'

/-- **The direct image of the structure sheaf of the punctured spectrum of a Noetherian local
ring with a one-dimensional associated quotient is not coherent.** Let `Λ` be a Noetherian local
ring, let `𝔭` be a prime of `Λ` which is the annihilator of a single element of `Λ`, and suppose
`dim(Λ ⧸ 𝔭) = 1`. Then the direct image of the structure sheaf along the inclusion of the
punctured spectrum into `Spec Λ` is not coherent. -/
@[ega "IV 7.8.3" "(ix), partial"]
theorem not_isCoherent_pushforward_puncturedSpectrum_of_isAssociatedPrime
    (Λ : CommRingCat.{u}) [IsNoetherianRing Λ] [IsLocalRing Λ] {p : PrimeSpectrum Λ}
    (hp : IsAssociatedPrimeStacks Λ Λ p.asIdeal)
    (hdim : ringKrullDim (Λ ⧸ p.asIdeal) = 1) :
    ¬ ((Scheme.Modules.pushforward (puncturedSpectrum Λ).ι).obj
        (SheafOfModules.unit _)).IsCoherent :=
  not_isCoherent_pushforward_structureSheaf_of_height_quotient_le_one
    (isAffineOpen_top (Spec Λ)) (x := (p : Spec Λ)) (z := closedPoint Λ) trivial trivial
    (IsLocalRing.specializes_closedPoint p) (height_quotient_primeIdealOf_top_le_one Λ hdim)
    (isAssociatedPoint_unit_of_isAssociatedPrime Λ hp)
    (mem_puncturedSpectrum_of_ringKrullDim_quotient_eq_one Λ hdim)
    (Stacks.LocalCohomology.closedPoint_notMem_puncturedSpectrumOpens (ToType Λ))

/-- **The sections over the punctured spectrum are not a finite module.** Let `Λ` be a Noetherian
local ring with a prime `𝔭` which is the annihilator of a single element of `Λ`, and suppose
`dim(Λ ⧸ 𝔭) = 1`. Then the sections of the structure sheaf of `Spec Λ` over the punctured spectrum
are not a finite module over the global sections. -/
theorem not_moduleFinite_sections_puncturedSpectrum_of_isAssociatedPrime
    (Λ : CommRingCat.{u}) [IsNoetherianRing Λ] [IsLocalRing Λ] {p : PrimeSpectrum Λ}
    (hp : IsAssociatedPrimeStacks Λ Λ p.asIdeal)
    (hdim : ringKrullDim (Λ ⧸ p.asIdeal) = 1) :
    ¬ (letI := resAlgebra (le_top (a := puncturedSpectrum Λ));
        Module.Finite Γ(Spec Λ, ⊤) Γ(Spec Λ, puncturedSpectrum Λ)) := by
  intro hfin
  have : (SheafOfModules.unit (Spec Λ).ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  exact not_moduleFinite_sections_of_isAssociatedPoint (isAffineOpen_top (Spec Λ))
    (SheafOfModules.unit (Spec Λ).ringCatSheaf) (x := (p : Spec Λ)) (z := closedPoint Λ)
    trivial trivial (IsLocalRing.specializes_closedPoint p)
    (height_quotient_primeIdealOf_top_le_one Λ hdim)
    (isAssociatedPoint_unit_of_isAssociatedPrime Λ hp) le_top
    (mem_puncturedSpectrum_of_ringKrullDim_quotient_eq_one Λ hdim)
    (Stacks.LocalCohomology.closedPoint_notMem_puncturedSpectrumOpens (ToType Λ)) hfin

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
