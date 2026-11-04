module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimitGeneral
public import StacksFrontier.AlgebraicGeometry.FormalSectionsAlgebraization.AdicLimitAllDegrees
public import StacksFrontier.AlgebraicGeometry.FormalSectionsAlgebraization.AdicLimitBootstrapInput
public import StacksFrontier.AlgebraicGeometry.FormalSectionsAlgebraization.AdicLimitHypotheses
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.FiniteComplete
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantBootstrap

/-!
# Stacks 0EG4: higher formal sections on a punctured spectrum

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `F` be a coherent module on
`U = Spec(A) ∖ V(𝔞)` and let `s ≥ 0`. Stacks 0EG4 asserts, under

1. `A` is `I`-adically complete and has a dualizing complex,
2. for `x ∈ U ∖ V(I)`, `depth(F_x) > s` or
   `depth(F_x) + dim(𝒪_{closure {x}, z}) > cd(A, I) + s + 1` for all `z ∈ V(𝔞) ∩ closure {x}`,
3. `F|_{U ∖ V(I)}` is `(S_{s+1})`, or `V(𝔞)` has dimension at most `2` in the sense of a dimension
   function,

that `H^i(U, F) → lim H^i(U, F/IⁿF)` is an isomorphism for `i < s` and that
`colim_V H^s(V, F) → lim H^s(U, F/IⁿF)` is an isomorphism, the colimit over the opens `V ⊆ U`
containing `U ∩ V(I)`.

## Main results

* `Stacks.Algebraization.adicLimit_of_essentiallyConstant` — the proposition from the assertion of
  Theorem 0EIE.
* `Stacks.Algebraization.adicLimit_allDegrees` — **Stacks 0EG4**.

## The proof

The source's. Write `F ≅ M̃|_U` with `M` finite (Stacks 0BK0); `M` is `I`-adically complete. Lemma
0EFW gives Situation 0EFU for `A, I, V(𝔞), M, s, cd(A, I)`, and Theorem 0EIE gives that the cones
`H^i_{V(𝔞)}(M) → lim H^i_{V(𝔞)}(M/IⁿM)` are limit cones and the systems are Mittag-Leffler for
`i ≤ s`. Lemma 0EFL for `s + 1` (whose hypotheses come from (1)–(3)) gives `J₀`, and Lemma 0EG0 in
cone form gives the limit cones `H^i_{V(J)}(M) → lim H^i_{V(J)}(M/IⁿM)` for `i ≤ s + 1` and every
`J ⊆ J₀` with `V(J) ∩ V(I) = V(𝔞)`. The comparison of cohomology on `U` and on `U ∖ V(J)` with
local cohomology, natural in the module (Stacks 0DWR), and the four-term sequence in degree `0`
turn these into the two assertions; the opens `U ∖ V(J)` are cofinal among the `V`.

## References

* [Stacks Project, Tag 0EG4](https://stacks.math.columbia.edu/tag/0EG4)
* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0EG0](https://stacks.math.columbia.edu/tag/0EG0)
* [Stacks Project, Tag 0EFW](https://stacks.math.columbia.edu/tag/0EFW)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.LocalCohomology

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- An inverse system of zero objects is Mittag-Leffler. -/
theorem isMittagLefflerCategorical_of_isZero {C : Type*} [Category C] [Abelian C]
    (F : ℕᵒᵖ ⥤ C) (hF : ∀ n, IsZero (F.obj n)) : IsMittagLefflerCategorical F := by
  intro i
  refine ⟨i, le_rfl, fun k hk => ?_⟩
  have := Subobject.subsingleton_of_isZero (hF (op i))
  exact Subsingleton.elim _ _

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I a : Ideal A) (hIa : I ≤ a)

include hIa in
/-- **Stacks 0EG4 from the assertion of Theorem 0EIE.** The two conclusions of
`Stacks.Algebraization.adicLimit_allDegrees`, from its hypotheses and the essential-constancy
assertion of Theorem 0EIE for every bootstrap situation. -/
theorem adicLimit_of_essentiallyConstant
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent] (s : ℕ)
    (hcomplete : IsAdicComplete I A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hdepth : SourceSheafDepthHypothesis A I a F s)
    (h3 : SourceSerreOrDimensionHypothesis A I a F s)
    (hEC : ∀ (S : BootstrapSituation.{u, u, u}) (i : ℤ), i ≤ S.s →
      ∃ (j : ℕᵒᵖ) (σ : (Bootstrap.tower.{u, u} S i).obj j ⟶ (Bootstrap.cone.{u, u} S i).pt),
        EssentiallyConstantPro.IsEssentiallyConstantWith
          (Bootstrap.tower.{u, u} S i) (Bootstrap.cone.{u, u} S i) j σ) :
    (∀ i : ℕ, i < s →
      IsIso (limit.lift (quotientSystemNearVanishing A I a F ⋙ complementOpenCohomology A a ⊤ i)
        ((complementOpenCohomology A a ⊤ i).mapCone
          (adicQuotientCone (idealSheafNearVanishing A I a) F)))) ∧
    IsIso (colimit.desc (nearVanishingCohomology A I a F s) (nearVanishingCocone A I a F s)) := by
  obtain ⟨M, hMfin, ⟨e⟩⟩ := exists_finiteModule_iso_restrict_tilde A a F
  have hM : IsAdicComplete I M := AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing I M
  have hMdepth := sourceDepthHypothesis_of_sourceSheafDepthHypothesis hIa e (s : ℤ) hdepth
  have hα : ∀ i : ℤ, i ≤ s →
      Nonempty (IsLimit (localCohomologyAdicCone.{u, u} A
        (PrimeSpectrum.zeroLocus (a : Set A)) I i M)) ∧
      IsMittagLefflerCategorical (localCohomologyAdicTower.{u, u} A
        (PrimeSpectrum.zeroLocus (a : Set A)) I i M) := fun i hi =>
    localCohomologyAdicCone_zeroLocus_of_essentiallyConstant.{u, u} I a hIa (M := M) s hdual
      hMdepth hEC i hi
  have hML : ∀ k : ℤ, k ≤ s → IsMittagLefflerCategorical (localCohomologyAdicTower.{u, u} A
      (PrimeSpectrum.zeroLocus (a : Set A)) I k M) := by
    intro k hk
    by_cases hk0 : k < 0
    · exact isMittagLefflerCategorical_of_isZero _ fun n =>
        isZero_localCohomologyWithSupportIn_single_of_neg.{u, u} A _ _ k hk0
    · exact (hα k hk).2
  have hJ₀ : ∃ J₀ : Ideal A, IsAlgebraizationIdeal (M := M) I a ((s : ℤ) + 1) J₀ := by
    by_cases hne : (PrimeSpectrum.zeroLocus (a : Set A)).Nonempty
    · obtain ⟨omega, δ, δmax, δmin, H⟩ :=
        algebraizationHypotheses_of_sourceHypotheses hIa e s hcomplete hdual hdepth h3 hne
      exact exists_isAlgebraizationIdeal I a _ _ omega δ δmax δmin H
    · refine ⟨a, isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty I a _ hcomplete ?_⟩
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, Set.empty_inter]
  obtain ⟨J₀, hJ₀⟩ := hJ₀
  have hinter := Set.inter_eq_left.mpr (PrimeSpectrum.zeroLocus_anti_mono_ideal hIa)
  have hML₀ := (hα 0 (by positivity)).2
  have hV₀ : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) := hJ₀.zeroLocus_inter.trans hinter
  refine adicLimit_of_localCohomologyCones I a e hM s (fun i hi => (hα i (by exact_mod_cast hi)).1)
    hML₀ J₀ hV₀ fun J hJle hJ => ⟨fun i hi => ?_, ?_⟩
  · exact Stacks.LocalCohomology.nonempty_isLimit_localCohomologyAdicCone_of_isAlgebraizationIdeal
      hIa M _ J₀ hJ₀ J hJle hJ i (by exact_mod_cast hi) (hML _ (by omega))
  · exact isMittagLefflerCategorical_localCohomologyAdicTower_of_zeroLocus_inter
      (hJ.trans hinter.symm) 0 M hML₀

include hIa in
/-- **Stacks Project, Tag 0EG4.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `F` be a
coherent module on `U = Spec(A) ∖ V(𝔞)` and let `s ≥ 0`. Assume

1. `A` is `I`-adically complete and has a dualizing complex,
2. `Stacks.Algebraization.SourceSheafDepthHypothesis`: for `x ∈ U ∖ V(I)`, `depth(F_x) > s` or
   `depth(F_x) + dim(𝒪_{closure {x}, z}) > cd(A, I) + s + 1` for all `z ∈ V(𝔞) ∩ closure {x}`,
3. `Stacks.Algebraization.SourceSerreOrDimensionHypothesis`: the restriction of `F` to
   `U ∖ V(I)` is `(S_{s+1})`, or the difference of the maximal and minimal values of a dimension
   function on `V(𝔞)` is at most `2`.

Then the maps `H^i(U, F) → lim H^i(U, F/IⁿF)` are isomorphisms for `i < s`, and
`colim_V H^s(V, F) → lim H^s(U, F/IⁿF)` is an isomorphism, the colimit being over the opens
`V ⊆ U` containing `U ∩ V(I)`.

Here `H^i(V, -)` is `Stacks.LocalCohomology.complementOpenCohomology`, the `i`-th right derived
functor of the sections over `V` of `𝒪_U`-modules, read over `A`; the first map is the comparison
induced by the quotient maps `F → F/IⁿF`; the second is the descent of
`Stacks.Algebraization.nearVanishingCocone`, whose component at `V` is reduction modulo `Iⁿ` on
`V` followed by the inverse of the restriction isomorphism `H^s(U, F/IⁿF) ≅ H^s(V, F/IⁿF)`. -/
@[stacks 0EG4]
theorem adicLimit_allDegrees
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent] (s : ℕ)
    (hcomplete : IsAdicComplete I A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hdepth : SourceSheafDepthHypothesis A I a F s)
    (h3 : SourceSerreOrDimensionHypothesis A I a F s) :
    (∀ i : ℕ, i < s →
      IsIso (limit.lift (quotientSystemNearVanishing A I a F ⋙ complementOpenCohomology A a ⊤ i)
        ((complementOpenCohomology A a ⊤ i).mapCone
          (adicQuotientCone (idealSheafNearVanishing A I a) F)))) ∧
    IsIso (colimit.desc (nearVanishingCohomology A I a F s) (nearVanishingCocone A I a F s)) :=
  adicLimit_of_essentiallyConstant I a hIa F s hcomplete hdual hdepth h3 fun S i hi =>
    (Stacks.LocalCohomology.Bootstrap.essentiallyConstant_and_consequences.{u, u} S i hi).1

end Stacks.Algebraization

end
