module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumRefined
public import StacksFrontier.CategoryTheory.PullbackCancelMonoRefined

/-!
# The quotient stages of a completed tensor product, as fibre products of spectra

Let `A` and `B` be algebras over `C`, let `i ⊆ A` and `j ⊆ B` be ideals and let `l ⊆ C` be an
ideal whose image lies in both. Then the square
```
Spec (A ⧸ i ⊗_C B ⧸ j)  ⟶  Spec (B ⧸ j)
          ↓                      ↓
     Spec (A ⧸ i)          ⟶  Spec (C ⧸ l)
```
is cartesian. This is the affine shadow of clause (3) of **Stacks 0AN3**: the quotients of the
completed tensor product by its weak ideals of definition are, cofinally, the rings
`A ⧸ i ⊗_C B ⧸ j`, and the above square is what makes their spectra the stages of a
presentation of the fibre product.

## Main results

* `AlgebraicGeometry.isPullback_specQuotientTensor`: the displayed square is cartesian.

## Implementation notes

Over `Spec C` the statement is `AlgebraicGeometry.pullbackSpecIso`. The passage from `Spec C` to
`Spec (C ⧸ l)` is free, in both directions: the two structure morphisms factor through
`Spec (C ⧸ l)`, which is a closed immersion into `Spec C` and in particular a monomorphism, and
a cartesian square over the target of a monomorphism is cartesian over its source
(`CategoryTheory.isPullback_of_comp_mono`). No identification of `A ⧸ i ⊗_C B ⧸ j` with
`A ⧸ i ⊗_{C ⧸ l} B ⧸ j` is needed.

## References

* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

section

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A] [Algebra C B]
  {i : Ideal A} {j : Ideal B} {l : Ideal C}
  (hi : l ≤ Ideal.comap (algebraMap C A) i) (hj : l ≤ Ideal.comap (algebraMap C B) j)

/-- The structure map of a quotient of `A` as an algebra over the base factors through the
corresponding quotient of the base. -/
theorem quotientMap_comp_mk_eq_algebraMap :
    (Ideal.quotientMap i (algebraMap C A) hi).comp (Ideal.Quotient.mk l) =
      algebraMap C (A ⧸ i) := by
  refine RingHom.ext fun c => ?_
  simp [Ideal.quotientMap_mk]

/-- Spectra of the two factorisations of the structure map of a quotient. -/
theorem spec_map_algebraMap_quotient_eq :
    Spec.map (CommRingCat.ofHom (algebraMap C (A ⧸ i))) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap i (algebraMap C A) hi)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk l)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, quotientMap_comp_mk_eq_algebraMap hi]

/-- **The quotient stage of a tensor product is a fibre product of spectra.** For ideals
`i ⊆ A`, `j ⊆ B` and `l ⊆ C` with `l` mapping into both, `Spec (A ⧸ i ⊗_C B ⧸ j)` is the fibre
product of `Spec (A ⧸ i)` and `Spec (B ⧸ j)` over `Spec (C ⧸ l)`. -/
theorem isPullback_specQuotientTensor :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : (A ⧸ i) →+* (A ⧸ i) ⊗[C] (B ⧸ j))))
      (Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : (B ⧸ j) →ₐ[C] (A ⧸ i) ⊗[C] (B ⧸ j)).toRingHom)))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap i (algebraMap C A) hi)))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap j (algebraMap C B) hj))) := by
  have hmono : Mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk l))) := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk l))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hbase : IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : (A ⧸ i) →+* (A ⧸ i) ⊗[C] (B ⧸ j))))
      (Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : (B ⧸ j) →ₐ[C] (A ⧸ i) ⊗[C] (B ⧸ j)).toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap C (A ⧸ i))))
      (Spec.map (CommRingCat.ofHom (algebraMap C (B ⧸ j)))) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso C (A ⧸ i) (B ⧸ j)).symm ?_ ?_
    · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun c => by
        simp [Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.algebraMap_apply]
    · exact pullbackSpecIso_inv_fst C (A ⧸ i) (B ⧸ j)
    · exact pullbackSpecIso_inv_snd C (A ⧸ i) (B ⧸ j)
  rw [spec_map_algebraMap_quotient_eq hi, spec_map_algebraMap_quotient_eq hj] at hbase
  exact isPullback_of_comp_mono _ hbase

end

end AlgebraicGeometry

end
