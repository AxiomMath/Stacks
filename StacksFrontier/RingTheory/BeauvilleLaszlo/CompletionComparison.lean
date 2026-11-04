module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.BeauvilleLaszlo.Descent

@[expose] public section

/-!
# Comparison with the original Beauville--Laszlo theorem

When `f` is a nonzerodivisor in a commutative ring `R`, the map from `R` to its `(f)`-adic
completion is a Beauville--Laszlo glueing pair. The resulting glueing theorem applies to every
glueable module, in particular to every module on which `f` is a nonzerodivisor, which is the
hypothesis of the original statement of Beauville--Laszlo. The finite-projective criterion
applies to arbitrary modules, without either restriction.

## Main results

* `beauvilleLaszlo_completion_comparison` (Stacks 0BP8): for a nonzerodivisor `f : R` the
  completion sequence is short exact; every module on which `f` is a nonzerodivisor is
  glueable; the canonical functor identifies all glueable modules with glueing data; and
  finite projectivity descends from the completion and the localization for every module.

## Implementation notes

A glueing pair and a glueable module are represented by short exactness of their canonical
Beauville--Laszlo sequences. The categorical statement is made for the full subcategory of
*all* glueable modules, while the finite-projective equivalence quantifies over every module
and therefore imposes no glueability or torsion-freeness assumption; this is the precise sense
in which the formalized theorem is stronger than the original one.

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0BP8](https://stacks.math.columbia.edu/tag/0BP8)
-/

namespace BeauvilleLaszlo
section

open CategoryTheory
open scoped TensorProduct

universe u w

/-- For a nonzerodivisor `f : R`, passage to the `(f)`-adic completion gives a
Beauville--Laszlo glueing pair. Every module on which `f` is a nonzerodivisor is
glueable, the canonical functor identifies all glueable modules with glueing data, and
finite projectivity can be checked after completion and localization for an arbitrary
module, with no torsion-freeness or glueability assumption on that module. -/
@[stacks 0BP8]
public theorem beauvilleLaszlo_completion_comparison
    (R : Type u) [CommRing R] (f : R) (hf : IsSMulRegular R f) :
    let Rhat := AdicCompletion (Ideal.span {f}) R
    (beauvilleLaszloSequence f (algebraMap R Rhat)).ShortExact ∧
      (∀ (M : Type w) [AddCommGroup M] [Module R M], IsSMulRegular M f →
        (beauvilleLaszloModuleSequence (S := Rhat) M f).ShortExact) ∧
      (let C := FormalGlueing.moduleGlueingConstruction.{u, u, w} Rhat (fun _ : Fin 1 ↦ f);
        let _ := C.category;
        (canonicalOnGlueableModules f C).IsEquivalence) ∧
      (∀ (M : Type w) [AddCommGroup M] [Module R M],
        (Module.Finite R M ∧ Module.Projective R M) ↔
          ((Module.Finite Rhat (Rhat ⊗[R] M) ∧ Module.Projective Rhat (Rhat ⊗[R] M)) ∧
            (Module.Finite (Localization.Away f) (LocalizedModule.Away f M) ∧
              Module.Projective (Localization.Away f) (LocalizedModule.Away f M)))) := by
  let Rhat := AdicCompletion (Ideal.span {f}) R
  have hquot : ∀ n : ℕ, 0 < n → Function.Bijective
      (quotientPowMap f n (algebraMap R Rhat)) :=
    fun n _ => quotientPowMap_adicCompletion_bijective f n
  have hpower : Function.Bijective (powerTorsionMap f (algebraMap R Rhat)) := by
    have := powerTorsion_subsingleton (M := R) (f := f) hf
    have := powerTorsion_subsingleton (M := Rhat)
      (isSMulRegular_algebraMap_adicCompletion rfl hf)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩
  have hglue : (beauvilleLaszloSequence f (algebraMap R Rhat)).ShortExact :=
    (beauvilleLaszloSequence_exactness_iff_powerTorsionMap f
      (algebraMap R Rhat) hquot).2.2.2.1.mpr hpower
  refine ⟨hglue, ?_, ?_, ?_⟩
  · intro M _ _ hM
    rw [(beauvilleLaszloModuleSequence_exactness_iff_powerTorsionMap.{u, u, w}.2
      R M f hglue)]
    have := powerTorsion_subsingleton (M := M) hM
    exact fun _ _ _ => Subsingleton.elim _ _
  · exact (canonicalOnGlueableModules_isEquivalence f hquot hglue).1
  · intro M _ _
    exact finite_projective_iff_baseChange_and_localization R Rhat f hquot hglue M

end

end BeauvilleLaszlo

end
