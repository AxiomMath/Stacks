module

public import Mathlib.Algebra.DirectSum.Finsupp
public import StacksFrontier.RingTheory.AdicCompletion.ShortExact
public import StacksFrontier.RingTheory.Flat.ProjectiveCompletedDirectSum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The completion of a flat module with projective reduction

Let `R` be a Noetherian ring which is `I`-adically complete and let `M` be a flat `R`-module whose
reduction `M/IM` is projective over `R/I`. This file proves Stacks 05DK: the `I`-adic completion
`M^∧` is a flat Mittag-Leffler `R`-module.

The argument is the source's. Choose a surjection `F → M` with `F` free. Flatness of `M` and
projectivity of `M/IM` make the completed sequence `0 → K^∧ → F^∧ → M^∧ → 0` split exact
(Stacks 05D3), so `M^∧` is a direct summand of `F^∧`. Both flatness and the Mittag-Leffler
property pass to direct summands, so the lemma reduces to the case of a free module, which is
Stacks 05DJ.

## Main results

* `AdicCompletion.flat_of_projective_quotient_smul_top`: the completion is flat; completeness of
  `R` is not needed for this half.
* `AdicCompletion.isMittagLeffler_of_projective_quotient_smul_top`: the completion is
  Mittag-Leffler.

## Implementation notes

The free module surjecting onto `M` is `M →₀ R`, the free module on the elements of `M`, with
`AdicCompletion.freeCover` the map sending the basis vector at `m` to `m`. This is the shape in
which Stacks 05DJ supplies the Mittag-Leffler property; its flatness half is stated for
`DirectSum`, and the two are identified by `finsuppLEquivDirectSum`.

The quotient `M/IM` is `M ⧸ I • (⊤ : Submodule R M)` with its canonical `R ⧸ I`-module structure,
and the two conclusions of the source's "flat Mittag-Leffler" are stated separately.

## References

* [Stacks Project, Tag 05DK](https://stacks.math.columbia.edu/tag/05DK)
-/

@[expose] public section

universe u v w uP uQ uN

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- A split injection stays injective after tensoring with any module. -/
private theorem injective_rTensor_of_comp_eq_id {M : Type v} {F : Type w} [AddCommGroup M]
    [Module R M] [AddCommGroup F] [Module R F] {i : M →ₗ[R] F} {p : F →ₗ[R] M}
    (hpi : p ∘ₗ i = LinearMap.id) (N : Type uN) [AddCommGroup N] [Module R N] :
    Function.Injective (i.rTensor N) :=
  LinearMap.injective_of_comp_eq_id _ (p.rTensor N) <| by
    rw [← LinearMap.rTensor_comp, hpi, LinearMap.rTensor_id]

/-- Precomposition with a map that stays injective after tensoring does not change kernels of
tensored maps. -/
private theorem ker_rTensor_comp_left_eq {M : Type v} {F : Type w} {P : Type uP} [AddCommGroup M]
    [Module R M] [AddCommGroup F] [Module R F] [AddCommGroup P] [Module R P] (i : M →ₗ[R] F)
    (f : P →ₗ[R] M) (N : Type uN) [AddCommGroup N] [Module R N]
    (hi : Function.Injective (i.rTensor N)) :
    LinearMap.ker ((i ∘ₗ f).rTensor N) = LinearMap.ker (f.rTensor N) := by
  rw [LinearMap.rTensor_comp]
  exact LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hi)

/-- The Mittag-Leffler property passes to a direct summand. -/
private theorem isMittagLeffler_of_comp_eq_id {M : Type v} {F : Type w} [AddCommGroup M]
    [Module R M] [AddCommGroup F] [Module R F] {i : M →ₗ[R] F} {p : F →ₗ[R] M}
    (hpi : p ∘ₗ i = LinearMap.id) (hF : IsMittagLeffler.{u, uP, w, uQ, uN} R F) :
    IsMittagLeffler.{u, uP, v, uQ, uN} R M := by
  refine (isMittagLeffler_def_iff.{u, uP, v, uQ, uN} R M).2 fun P _ _ _ f => ?_
  obtain ⟨Q, hQa, hQm, hQfp, g, hg⟩ :=
    (isMittagLeffler_def_iff.{u, uP, w, uQ, uN} R F).1 hF P (i ∘ₗ f)
  refine ⟨Q, hQa, hQm, hQfp, g, fun N _ _ => ?_⟩
  change LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)
  exact (ker_rTensor_comp_left_eq i f N (injective_rTensor_of_comp_eq_id hpi N)).symm.trans (hg N)

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The canonical surjection onto `M` from the free `R`-module on the elements of `M`, sending the
basis vector at `m` to `m`. -/
noncomputable def freeCover : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id

/-- The free cover of `M` is surjective: `m` is the image of the basis vector at `m`. -/
theorem freeCover_surjective : Function.Surjective (freeCover (R := R) M) :=
  fun x => ⟨Finsupp.single x 1, by simp [freeCover]⟩

variable (I : Ideal R)

/-- The completion of `M` is a direct summand of the completion of the free module on the elements
of `M`: this is Stacks 05D3 applied to `0 → ker → (M →₀ R) → M → 0`. -/
private theorem exists_adicCompletion_retract [Module.Flat R M]
    (hM : Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) :
    ∃ (i : AdicCompletion I M →ₗ[R] AdicCompletion I (M →₀ R))
      (p : AdicCompletion I (M →₀ R) →ₗ[R] AdicCompletion I M), p ∘ₗ i = LinearMap.id := by
  obtain ⟨s, hs⟩ := (AdicCompletion.map_splitExact_of_projective_quotient_smul_top I
    (f := (LinearMap.ker (freeCover (R := R) M)).subtype) (g := freeCover (R := R) M)
    (LinearMap.ker (freeCover (R := R) M)).subtype_injective
    (LinearMap.exact_subtype_ker_map (freeCover (R := R) M)) (freeCover_surjective M) hM).2.2
  exact ⟨s.restrictScalars R, (AdicCompletion.map I (freeCover (R := R) M)).restrictScalars R,
    LinearMap.ext fun x => LinearMap.congr_fun hs x⟩

/-- **Stacks Project, Tag 05DK.** If `R` is Noetherian, `M` is flat and `M/IM` is projective over
`R/I`, then the `I`-adic completion of `M` is flat over `R`. The source's hypothesis that `R` be
`I`-adically complete is not needed for this half. -/
@[stacks 05DK "flatness; `M/IM` is `M ⧸ I • ⊤`. The source's hypothesis that `R` be `I`-adically
complete is dropped: it is unused, neither Tag 05D3 nor Tag 06LE needing it, so this is strictly
more general than the source's statement.", sga "1 IV 3.1"]
theorem flat_of_projective_quotient_smul_top [IsNoetherianRing R]
    [Module.Flat R M] (hM : Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) :
    Module.Flat R (AdicCompletion I M) := by
  classical
  obtain ⟨i, p, hpi⟩ := exists_adicCompletion_retract M I hM
  have hsum : Module.Flat R (AdicCompletion I (DirectSum M fun _ : M => R)) :=
    AdicCompletion.flat_directSum R I M
  have hfree : Module.Flat R (AdicCompletion I (M →₀ R)) :=
    Module.Flat.of_linearEquiv
      ((AdicCompletion.congr I (finsuppLEquivDirectSum R R M)).restrictScalars R)
  exact Module.Flat.of_retract i p hpi

/-- **Stacks Project, Tag 05DK.** If `R` is Noetherian and `I`-adically complete, `M` is flat and
`M/IM` is projective over `R/I`, then the `I`-adic completion of `M` is a Mittag-Leffler
`R`-module. -/
@[stacks 05DK "the Mittag-Leffler property; `M/IM` is `M ⧸ I • ⊤`, and Mittag-Leffler is
`IsMittagLeffler`, condition (1) of 059E, as in 059N and 05DJ."]
theorem isMittagLeffler_of_projective_quotient_smul_top [IsNoetherianRing R] [IsAdicComplete I R]
    [Module.Flat R M] (hM : Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) :
    IsMittagLeffler.{u, uP, v, max u uP, uN} R (AdicCompletion I M) := by
  obtain ⟨i, p, hpi⟩ := exists_adicCompletion_retract M I hM
  exact isMittagLeffler_of_comp_eq_id hpi (AdicCompletion.isMittagLeffler_finsupp I M)

end AdicCompletion

end
