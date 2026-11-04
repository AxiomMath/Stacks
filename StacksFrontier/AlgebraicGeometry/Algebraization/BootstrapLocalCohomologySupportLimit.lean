module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimit
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimitCone
public import StacksFrontier.RingTheory.AdicCompletion.QuotientRestrictScalars
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantBootstrap

/-!
# Stacks 0EG0: local cohomology as the limit over the adic quotients, in degree `s + 1`

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `M` be a finite `A`-module and let `s` and `d`
be integers. Assume that `A, I, V(𝔞), M` are in the bootstrap situation of [Stacks, Tag 0EFU] for
`s` and `d`, and that `A, I, 𝔞, M` satisfy the conditions of [Stacks, Tag 0EFL] for `s + 1` and
`d`. Stacks 0EG0 asserts that there is an ideal `J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞)` such that for
every `J ⊆ J₀` with `V(J) ∩ V(I) = V(𝔞)` the canonical map

`H^{s+1}_J(M) ⟶ lim H^{s+1}_𝔞(M/IⁿM)`

is an isomorphism.

The proof is the source's. [Stacks, Tag 0EFL] gives `J₀` and identifies `H^{s+1}_J(M)` with
`H^{s+1}(RΓ_𝔞(M)^∧)`; [Stacks, Tag 0EEW] puts the latter in a short exact sequence between
`R¹lim H^s_𝔞(M/IⁿM)` and `lim H^{s+1}_𝔞(M/IⁿM)`; and the `R¹lim` term vanishes because
`{H^s_𝔞(M/IⁿM)}` is Mittag-Leffler, which is [Stacks, Tag 0EIE] in the bootstrap situation
(`Stacks.LocalCohomology.Bootstrap.essentiallyConstant_and_consequences`).

## Main results

* `Stacks.Algebraization.BootstrapSituation.exists_ideal_isIso_localCohomologyToAdicQuotientLimit`
  — **Stacks 0EG0**.

## Implementation notes

Condition (1) of the source is the bootstrap situation `S`, whose locus is the closed set `V(𝔞)`
(`hT`). Condition (2), the conditions of [Stacks, Tag 0EFL] for `s + 1` and `d`, is the
disjunction of the two cases in which the library states that lemma: for `V(𝔞)` nonempty,
`Stacks.Algebraization.AlgebraizationHypotheses`, which like the library's Stacks 0EFL is stated
against a dimension function on `Spec(A)` and its extreme values on `V(𝔞) ∩ V(I)`; for `V(𝔞)`
empty, that is `𝔞 = A`, the `I`-adic completeness of `A`, the source's condition (5) being vacuous
there. The local cohomology of the adic quotients appearing in the limit is
`Dualizing.adicQuotientLocalCohomologySystem`, built from `RΓ_𝔞`; the Mittag-Leffler property of
[Stacks, Tag 0EIE] is proved for `RΓ_{V(𝔞)}`, and the two agree by [Stacks, Tag 0955].

## References

* [Stacks Project, Tag 0EG0](https://stacks.math.columbia.edu/tag/0EG0)
* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.LocalCohomology
open AlgebraicGeometry.ProEtale (adicQuotientModuleSystem)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

section Comparison

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I a : Ideal A) (M : ModuleCat.{u} A)

/-- **The local cohomology of the adic quotients, in the two models.** The system
`n ↦ Hⁱ(RΓ_𝔞(M/IⁿM))` of `Dualizing.adicQuotientLocalCohomologySystem` is the system
`n ↦ Hⁱ_{V(𝔞)}(M/IⁿM)`, by [Stacks, Tag 0955]. -/
private def adicQuotientLocalCohomologySystemIso (i : ℤ) :
    Dualizing.adicQuotientLocalCohomologySystem A I a a.fg_of_isNoetherianRing M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ≅
      idealPowerQuotientTower.{u, u} I M ⋙
        localCohomologyWithSupportInModuleFunctor.{u, u} A
          (PrimeSpectrum.zeroLocus (a : Set A)) i :=
  haveI := isIso_compareSectionsWithSupportLocalCohomology.{u, u} A a a.fg_of_isNoetherianRing
  Functor.isoWhiskerLeft (adicQuotientModuleSystem A I M ⋙
      DerivedCategory.singleFunctor (ModuleCat.{u} A) 0)
      (Functor.isoWhiskerRight (asIso (compareSectionsWithSupportLocalCohomology.{u, u} A a
        a.fg_of_isNoetherianRing)).symm (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)) ≪≫
    Functor.isoWhiskerRight (idealPowerQuotientTowerIso I M).symm
      (localCohomologyWithSupportInModuleFunctor.{u, u} A
        (PrimeSpectrum.zeroLocus (a : Set A)) i)

end Comparison

/-- **Stacks Project, Tag 0EG0.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `M` be a
finite `A`-module and let `s` and `d` be integers. Assume

1. `A, I, V(𝔞), M` satisfy the assumptions of Situation [Stacks, Tag 0EFU] for `s` and `d` — the
   bootstrap situation `S`, with locus `V(𝔞)`;
2. `A, I, 𝔞, M` satisfy the conditions of [Stacks, Tag 0EFL] for `s + 1` and `d` with `J = 𝔞` —
   the hypothesis `H`.

Then there is an ideal `J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞)` such that for every `J ⊆ J₀` with
`V(J) ∩ V(I) = V(𝔞)` the map `H^{s+1}_J(M) ⟶ lim H^{s+1}_𝔞(M/IⁿM)` is an isomorphism.

Stacks 0EFL supplies `J₀` together with the identification `H^{s+1}_J(M) = H^{s+1}(RΓ_𝔞(M)^∧)`;
Stacks 0EEW puts `H^{s+1}(RΓ_𝔞(M)^∧)` in a short exact sequence with `R¹lim H^s_𝔞(M/IⁿM)` on the
left and `lim H^{s+1}_𝔞(M/IⁿM)` on the right; and the left-hand term vanishes because
`{H^s_𝔞(M/IⁿM)}` is Mittag-Leffler by Theorem [Stacks, Tag 0EIE].

Condition (2) is the disjunction of the two cases in which the library states Stacks 0EFL.
`Stacks.Algebraization.AlgebraizationHypotheses` names the extreme values of a dimension function
on `V(𝔞) ∩ V(I) = V(𝔞)`, so it can only hold when `V(𝔞)` is nonempty; when `V(𝔞)` is empty, that
is `𝔞 = A`, the source's condition (5), the only one naming the dimension function, is guarded by
`V(𝔭) ∩ V(𝔞) ∩ V(I) ≠ ∅` and is vacuous, and of the source's conditions only the `I`-adic
completeness of `A` is used, through
`Stacks.Algebraization.isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty`.
Either disjunct follows from the source's condition (2), so the hypothesis asks for nothing beyond
it. -/
@[stacks 0EG0]
public theorem BootstrapSituation.exists_ideal_isIso_localCohomologyToAdicQuotientLimit
    (S : BootstrapSituation.{u, u, u}) (a : Ideal S.A) (hIa : S.I ≤ a)
    (hT : S.T = PrimeSpectrum.zeroLocus (a : Set S.A))
    (omega : DerivedCategory (ModuleCat.{u} S.A)) (δ : PrimeSpectrum S.A → ℤ) (δmax δmin : ℤ)
    (H : AlgebraizationHypotheses (M := S.M) S.I a (S.s + 1) S.d omega δ δmax δmin ∨
      (IsAdicComplete S.I S.A ∧ PrimeSpectrum.zeroLocus (a : Set S.A) = ∅)) :
    ∃ J₀ : Ideal S.A, J₀ ≤ a ∧
      PrimeSpectrum.zeroLocus (J₀ : Set S.A) ∩ PrimeSpectrum.zeroLocus (S.I : Set S.A) =
        PrimeSpectrum.zeroLocus (a : Set S.A) ∧
      ∀ J : Ideal S.A, J ≤ J₀ →
        ∀ hJ : PrimeSpectrum.zeroLocus (J : Set S.A) ∩ PrimeSpectrum.zeroLocus (S.I : Set S.A) =
          PrimeSpectrum.zeroLocus (a : Set S.A),
          IsIso (localCohomologyToAdicQuotientLimit S.A S.I a J (ModuleCat.of S.A S.M)
            (hJ.trans (zeroLocus_inter_eq_self_of_le hIa).symm) (S.s + 1)) := by
  -- Stacks 0EFL, in its two cases
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Ideal S.A, IsAlgebraizationIdeal (M := S.M) S.I a (S.s + 1) J₀ := by
    rcases H with H | ⟨hcomplete, hempty⟩
    · exact exists_isAlgebraizationIdeal S.I a (S.s + 1) S.d omega δ δmax δmin H
    · refine ⟨a, isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty S.I a (S.s + 1) hcomplete ?_⟩
      rw [hempty, Set.empty_inter]
  refine ⟨J₀, hJ₀.le, ?_, fun J hJle hJ ↦ ?_⟩
  · rw [hJ₀.zeroLocus_inter]
    exact zeroLocus_inter_eq_self_of_le hIa
  have hiso := hJ₀.isIso J hJle (hJ.trans (zeroLocus_inter_eq_self_of_le hIa).symm)
    (S.s + 1) le_rfl
  -- the Mittag-Leffler property of `{H^s_𝔞(M/IⁿM)}`, Theorem 0EIE
  have hML : IsMittagLefflerCategorical
      (Dualizing.adicQuotientLocalCohomologySystem S.A S.I a a.fg_of_isNoetherianRing
          (ModuleCat.of S.A S.M) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) (S.s + 1 - 1)) := by
    rw [add_sub_cancel_right]
    have h := (Stacks.LocalCohomology.Bootstrap.essentiallyConstant_and_consequences S S.s
      le_rfl).2.1
    simp only [Stacks.LocalCohomology.Bootstrap.tower, hT] at h
    exact IsMittagLefflerCategorical.of_natIso
      (adicQuotientLocalCohomologySystemIso S.I a (ModuleCat.of S.A S.M) S.s) h
  have hlim := Stacks.LocalCohomology.isIso_completedLocalCohomologyToLimit_of_isMittagLeffler
    S.A S.I a a.fg_of_isNoetherianRing (ModuleCat.of S.A S.M) _
    (Dualizing.isDerivedLimit_completedLocalCohomology S.A S.I a S.I.fg_of_isNoetherianRing
      a.fg_of_isNoetherianRing (ModuleCat.of S.A S.M)) (S.s + 1) hML
  unfold localCohomologyToAdicQuotientLimit
  have := hiso
  have := hlim
  infer_instance

end Stacks.Algebraization

end
