module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import StacksFrontier.Examples.Completion.NoncompleteQuotient
import StacksCore.Tactic.StacksAttribute

/-!
# Adic completion is neither left nor right exact

Adic completion can fail to preserve exactness of a short exact sequence, even for a principal
ideal of definition and even on finitely presented modules.

Both failures come from the ring of Stacks 05JE: a ring `R` which is `I`-adically complete for a
principal ideal `I` and carries a principal ideal `J` for which `R ⧸ J` is not complete. By
Stacks 031A the failure of completeness produces an element `x ∈ R` lying in every `J + Iⁿ` but
not in `J`. Its image in the completion of `R` is killed by the completion of `R → R ⧸ J`, yet
it cannot come from the completion of `J`: `R` is already complete, so an element of the
completion of `J` coming from `R` would put `x` in `J`. Writing `J = (f)` and presenting `J` as
the image of multiplication by `f` turns the same sequence into the presentation
`R → R → R ⧸ (f) → 0`, whose three terms are finitely presented, so right exactness fails too.

## Main results

* `Stacks.Examples.exists_not_left_exact_adicCompletion`: a short exact sequence whose
  completion is not exact in the middle.
* `Stacks.Examples.exists_not_right_exact_adicCompletion_finitePresentation`: a presentation
  `R → R → R ⧸ (f) → 0` of finitely presented modules whose completion is not exact in the
  middle.

## Implementation notes

The maps after completion are the functorial maps `AdicCompletion.map`. Exactness of a pair of
maps is `Function.Exact`. The ideal of definition is principal, hence in particular finitely
generated, in both witnesses.

## References

* [Stacks Project, Tag 05JG](https://stacks.math.columbia.edu/tag/05JG)
* [Stacks Project, Tag 05JE](https://stacks.math.columbia.edu/tag/05JE)
* [Stacks Project, Tag 031A](https://stacks.math.columbia.edu/tag/031A)
-/

@[expose] public section

universe u

namespace Stacks.Examples

/-- Multiplication by a member `f` of an ideal `J`, viewed as a map into `J`. -/
private def principalIdealMap {R : Type u} [CommRing R] (J : Ideal R) (f : R)
    (hf : f ∈ J) : R →ₗ[R] J :=
  (LinearMap.toSpanSingleton R R f).codRestrict (J : Submodule R R)
    fun r => by simpa [LinearMap.toSpanSingleton, smul_eq_mul] using J.mul_mem_left r hf

private lemma principalIdealMap_coe_apply {R : Type u} [CommRing R] (J : Ideal R) (f : R)
    (hf : f ∈ J) (r : R) : (principalIdealMap J f hf r : R) = r * f := by
  simp [principalIdealMap, LinearMap.toSpanSingleton, smul_eq_mul]

private theorem principalIdealMap_surjective {R : Type u} [CommRing R] (J : Ideal R)
    (f : R) (hf : f ∈ J) (hJ : J = Ideal.span ({f} : Set R)) :
    Function.Surjective (principalIdealMap J f hf) := by
  intro y
  have hy : (y : R) ∈ Ideal.span ({f} : Set R) := hJ ▸ y.property
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨r, Subtype.ext ?_⟩
  rw [principalIdealMap_coe_apply]
  simpa [mul_comm] using hr

/-- Stacks 031A, read as the production of an element witnessing the failure of completeness
of a quotient: it lies in every `J + Iⁿ` but not in `J`. -/
private theorem completion_kernel_element_of_incomplete_quotient
    {R : Type u} [CommRing R] (I J : Ideal R) [IsAdicComplete I R]
    (hnot : ¬ IsAdicComplete (I.map (Ideal.Quotient.mk J)) (R ⧸ (J : Submodule R R))) :
    ∃ x : R, x ∉ J ∧ ∀ n : ℕ, x ∈ J ⊔ (I ^ n • (⊤ : Submodule R R)) := by
  have hnotComplete : ¬ IsAdicComplete I (R ⧸ (J : Submodule R R)) := fun hc =>
    hnot (by simpa [Ideal.Quotient.algebraMap_eq] using
      (IsAdicComplete.map_algebraMap_iff (I := I) (R := R)
        (S := R ⧸ (J : Submodule R R)) (M := R ⧸ (J : Submodule R R))).mpr hc)
  have hnotle : ¬ (⨅ n : ℕ, J ⊔ (I ^ n • (⊤ : Submodule R R))) ≤ J := fun h =>
    hnotComplete ((main_theorem_031a I R J).mp (le_antisymm (le_iInf fun _ => le_sup_left) h))
  obtain ⟨x, hxInf, hxJ⟩ := SetLike.not_le_iff_exists.mp hnotle
  exact ⟨x, hxJ, (Submodule.mem_iInf _).mp hxInf⟩

/-- The image of `x` in `R ⧸ J` vanishes modulo `Iⁿ` exactly when `x ∈ J + Iⁿ`. -/
theorem mkQ_sModEq_zero_iff_mem_sup {R : Type u} [CommRing R] (I J : Ideal R) (x : R)
    (n : ℕ) :
    (Submodule.mkQ (J : Submodule R R) x ≡ 0
      [SMOD (I ^ n • (⊤ : Submodule R (R ⧸ (J : Submodule R R))))]) ↔
      x ∈ J ⊔ (I ^ n • (⊤ : Submodule R R)) := by
  rw [SModEq.zero, show (I ^ n • (⊤ : Submodule R (R ⧸ (J : Submodule R R)))) =
      Submodule.map (Submodule.mkQ (J : Submodule R R)) (I ^ n • (⊤ : Submodule R R)) by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ],
    ← Submodule.mem_comap, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_comm]

/-- **Stacks 05JG.** Adic completion need not preserve the exactness of a short exact sequence
at its middle term, so it is not left exact in general. -/
@[stacks 05JG "failure of left exactness"]
theorem exists_not_left_exact_adicCompletion :
    ∃ (R : Type u) (_ : CommRing R) (I J : Ideal R),
      I.IsPrincipal ∧ J.IsPrincipal ∧
        Function.Exact (Submodule.subtype (J : Submodule R R))
          (Submodule.mkQ (J : Submodule R R)) ∧
        ¬ Function.Exact
          (AdicCompletion.map I (Submodule.subtype (J : Submodule R R)))
          (AdicCompletion.map I (Submodule.mkQ (J : Submodule R R))) := by
  obtain ⟨R, instR, I, J, hI, hJ, hR, hnot⟩ :=
    exists_complete_principal_ideal_not_complete_quotient
  let _ : CommRing R := instR
  let _ : IsAdicComplete I R := hR
  obtain ⟨f, hfspan⟩ := hJ.principal
  have hfJ : f ∈ J := hfspan ▸ Ideal.mem_span_singleton_self f
  obtain ⟨x, hxJ, hxInf⟩ := completion_kernel_element_of_incomplete_quotient I J hnot
  have hker : AdicCompletion.map I (Submodule.mkQ (J : Submodule R R))
      (AdicCompletion.of I R x) = 0 := by
    refine AdicCompletion.ext fun n => ?_
    rw [← AdicCompletion.eval_apply, AdicCompletion.map_of, AdicCompletion.eval_of,
      AdicCompletion.val_zero_apply]
    exact (Submodule.Quotient.mk_eq_zero
      (I ^ n • (⊤ : Submodule R (R ⧸ (J : Submodule R R))))).mpr
      (SModEq.zero.mp ((mkQ_sModEq_zero_iff_mem_sup I J x n).mpr (hxInf n)))
  have hNotExact : ¬ Function.Exact
      (AdicCompletion.map I (Submodule.subtype (J : Submodule R R)))
      (AdicCompletion.map I (Submodule.mkQ (J : Submodule R R))) := by
    intro h
    have hxRange : AdicCompletion.of I R x ∈
        LinearMap.range (AdicCompletion.map I (Submodule.subtype (J : Submodule R R))) := by
      rw [← h.linearMap_ker_eq]
      exact LinearMap.mem_ker.mpr hker
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hxRange
    let g := principalIdealMap J f hfJ
    have hg : Function.Surjective g := principalIdealMap_surjective J f hfJ hfspan
    obtain ⟨y, hy⟩ := AdicCompletion.map_surjective (I := I) hg z
    obtain ⟨r, hr⟩ := AdicCompletion.of_surjective I R y
    have heq : AdicCompletion.of I R ((Submodule.subtype (J : Submodule R R) ∘ₗ g) r) =
        AdicCompletion.of I R x := by
      calc
        _ = AdicCompletion.map I (Submodule.subtype (J : Submodule R R))
            (AdicCompletion.map I g (AdicCompletion.of I R r)) := by
              simp only [LinearMap.comp_apply, AdicCompletion.map_of]
        _ = AdicCompletion.map I (Submodule.subtype (J : Submodule R R))
            (AdicCompletion.map I g y) := by rw [hr]
        _ = AdicCompletion.of I R x := by rw [hy, hz]
    have hxval : (Submodule.subtype (J : Submodule R R) ∘ₗ g) r = x :=
      (AdicCompletion.of_bijective_iff.mpr inferInstance).1 heq
    exact hxJ (hxval ▸ (g r).property)
  exact ⟨R, instR, I, J, hI, hJ, LinearMap.exact_subtype_mkQ (Q := J), hNotExact⟩

/-- **Stacks 05JG.** Completion is not right exact even on finitely presented modules over a
ring, with a principal ideal of definition. -/
@[stacks 05JG "failure of right exactness on finitely presented modules"]
theorem exists_not_right_exact_adicCompletion_finitePresentation :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R) (f : R),
      I.IsPrincipal ∧
        Module.FinitePresentation R (R ⧸ (Ideal.span {f} : Submodule R R)) ∧
        Function.Exact (LinearMap.mulLeft R f)
          (Submodule.mkQ (Ideal.span {f} : Submodule R R)) ∧
        ¬ Function.Exact
          (AdicCompletion.map I (LinearMap.mulLeft R f))
          (AdicCompletion.map I (Submodule.mkQ (Ideal.span {f} : Submodule R R))) := by
  obtain ⟨R, instR, I, J, hI, hJ, _, hNotExact⟩ := exists_not_left_exact_adicCompletion
  let _ : CommRing R := instR
  obtain ⟨f, hfspan⟩ := hJ.principal
  subst J
  have hfJ : f ∈ (Ideal.span {f} : Ideal R) := Ideal.mem_span_singleton_self f
  have hfp : Module.FinitePresentation R (R ⧸ (Ideal.span {f} : Submodule R R)) := by
    apply Module.finitePresentation_of_surjective
      (Submodule.mkQ (Ideal.span {f} : Submodule R R)) (Submodule.mkQ_surjective _)
    rw [Submodule.ker_mkQ]
    exact Submodule.fg_span (Set.finite_singleton f)
  have hg : Function.Surjective (principalIdealMap (Ideal.span {f}) f hfJ) :=
    principalIdealMap_surjective (Ideal.span {f}) f hfJ rfl
  have hcomp0 : Submodule.subtype (Ideal.span {f} : Submodule R R) ∘ₗ
      principalIdealMap (Ideal.span {f}) f hfJ = LinearMap.mulLeft R f := by
    refine LinearMap.ext fun r => ?_
    rw [LinearMap.comp_apply, Submodule.subtype_apply, principalIdealMap_coe_apply,
      LinearMap.mulLeft_apply, mul_comm]
  refine ⟨R, instR, I, f, hI, hfp, ?_, ?_⟩
  · simpa [← hcomp0] using
      hg.comp_exact_iff_exact.mpr (LinearMap.exact_subtype_mkQ (Q := Ideal.span {f}))
  · exact fun hright => hNotExact
      ((AdicCompletion.map_surjective (I := I) hg).comp_exact_iff_exact.mp
        (by simpa only [← hcomp0, AdicCompletion.map_comp, LinearMap.coe_comp] using hright))

end Stacks.Examples

end
