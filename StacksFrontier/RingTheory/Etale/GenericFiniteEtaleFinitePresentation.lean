module

public import StacksFrontier.RingTheory.Etale.GenericFiniteEtale
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Etale.Field

/-!
# Generic finite étaleness over an arbitrary domain

Let `R ⊆ B` be domains with `B` of finite presentation over `R`, and suppose the extension of
fraction fields `L / K` is separable algebraic. Then there is a nonzero `g ∈ R` such that `B_g`
is finite étale over `R_g`. This removes the hypothesis, in
`Stacks.GenericFiniteEtale.exists_finite_etale_localization`, that `R` is a Dedekind domain;
for a noetherian `R` (for instance a polynomial ring over a field) finite presentation is
finite type.

Instead of deducing flatness from torsion-freeness over a Dedekind ring, the proof uses that the
étale locus of `Spec B` over `R` is open (`Algebra.isOpen_etaleLocus`). The generic point lies
in it: the local ring there is `L`, and `R → K → L` is a localization followed by a separable
algebraic extension. So some basic open `D(f)`, `f ≠ 0`, of `Spec B` is étale over `R`, and `f`
divides a nonzero element of `R`. Inverting also the product of denominators of integral
equations of generators of `B` (`Stacks.GenericFiniteEtale.exists_isIntegral_loc`) makes the
localization finite.

## Main results

* `Stacks.GenericFiniteEtale.exists_formallyEtale_away`: the generic point is étale.
* `Stacks.GenericFiniteEtale.exists_finite_etale_localization_of_finitePresentation`.
-/

@[expose] public section

open Algebra

namespace Stacks.GenericFiniteEtale

variable {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B]
  [FaithfulSMul R B]

variable (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L]

omit [IsDomain R] [FaithfulSMul R B] in
include K L in
/-- **The generic point is étale**: some basic open `D(f)`, `f ≠ 0`, of `Spec B` is formally
étale over `R`, when `B` is of finite presentation over `R` and `L / K` is separable. -/
theorem exists_formallyEtale_away [Algebra.FinitePresentation R B] [Algebra.IsSeparable K L] :
    ∃ f : B, f ≠ 0 ∧ Algebra.FormallyEtale R (Localization.Away f) := by
  have h1 : FormallyEtale R K := FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have h2 : FormallyEtale K L := FormallyEtale.of_isSeparable K L
  have h3 : FormallyEtale R L := FormallyEtale.comp R K L
  have : IsFractionRing B (Localization.AtPrime (⊥ : Ideal B)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal B).primeCompl)
  let e : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[R] L :=
    (IsLocalization.algEquiv (nonZeroDivisors B)
      (Localization.AtPrime (⊥ : Ideal B)) L).restrictScalars R
  have : IsEtaleAt R (⊥ : Ideal B) := FormallyEtale.of_equiv e.symm
  obtain ⟨f, hf, H⟩ := exists_etale_of_isEtaleAt (R := R) (⊥ : Ideal B)
  exact ⟨f, fun h => hf (h ▸ Submodule.zero_mem _), H.1⟩

include K L in
/-- **Generic finite étaleness.** Let `R ⊆ B` be domains, `B` of finite presentation over `R`,
with separable algebraic extension of fraction fields `L / K`. Then for some nonzero `g ∈ R`
the localization `B_g` is finite and étale over `R_g`. -/
theorem exists_finite_etale_localization_of_finitePresentation [Algebra.FinitePresentation R B]
    [Algebra.IsSeparable K L] :
    ∃ g : R, g ≠ 0 ∧ Module.Finite (Localization.Away g) (Loc B g) ∧
      Algebra.Etale (Localization.Away g) (Loc B g) := by
  have := isAlgebraic_of_isAlgebraic_fractionRing (R := R) (B := B) K L
  obtain ⟨f, hf0, hfe⟩ := exists_formallyEtale_away (R := R) (B := B) K L
  obtain ⟨r, hr0, hfr⟩ := exists_dvd_algebraMap (R := R) hf0
  obtain ⟨g₁, hg₁0, hint⟩ := exists_isIntegral_loc (R := R) (B := B)
  have hg0 : g₁ * r ≠ 0 := mul_ne_zero hg₁0 hr0
  refine ⟨g₁ * r, hg0, ?_⟩
  set g := g₁ * r with hg
  have := hint g (dvd_mul_right _ _)
  set c := algebraMap R B g
  have hpow : Algebra.algebraMapSubmonoid B (Submonoid.powers g) = Submonoid.powers c :=
    Submonoid.map_powers _ _
  have hloc : IsLocalization (Submonoid.powers c) (Loc B g) := by
    rw [← hpow]; infer_instance
  -- finite presentation and finiteness
  have : Algebra.FinitePresentation B (Loc B g) :=
    IsLocalization.Away.finitePresentation (S := Loc B g) c
  have : Algebra.FinitePresentation R (Loc B g) := Algebra.FinitePresentation.trans R B _
  have : Algebra.FinitePresentation R (Localization.Away g) :=
    IsLocalization.Away.finitePresentation (S := Localization.Away g) g
  have : Algebra.FinitePresentation (Localization.Away g) (Loc B g) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ _
  have hfin : Module.Finite (Localization.Away g) (Loc B g) := Algebra.IsIntegral.finite
  -- étale
  have hEc : FormallyEtale R (Localization.Away c) := by
    rw [← basicOpen_subset_etaleLocus_iff]
    refine subset_trans ?_ (basicOpen_subset_etaleLocus_iff.2 hfe)
    intro p hp hpf
    exact hp (Ideal.mem_of_dvd _ (hfr.trans (map_dvd _ (dvd_mul_left r g₁))) hpf)
  have : FormallyEtale R (Loc B g) := FormallyEtale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers c) (Localization.Away c)
      (Loc B g)).restrictScalars R)
  have : FormallyEtale R (Localization.Away g) :=
    FormallyEtale.of_isLocalization (Submonoid.powers g)
  have : FormallyEtale (Localization.Away g) (Loc B g) :=
    FormallyEtale.of_restrictScalars (R := R)
  exact ⟨hfin, ⟨inferInstance, inferInstance⟩⟩

end Stacks.GenericFiniteEtale
