module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.SpecTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ResidueDegreeBound

/-!
# A degree bound bounds the number of points in every fibre

If every field-valued base change of a morphism of schemes is finite locally free of degree at
most `n`, then every such base change has at most `n` points.

## Main results

* `AlgebraicGeometry.cardinalMk_pullback_le_of_degree_le` bounds the number of points of every
  field-valued base change by its uniform degree bound.

## Implementation notes

The degree condition is expressed by the existence of a rank `r ≤ n` for the finite locally
free structural morphism of the base change. The number of points is expressed using
`Cardinal.mk`, so the conclusion itself retains its literal cardinality meaning without a
separate finiteness instance.

Each point of such a base change contributes at least one to the sum of the residue degrees,
because its residue field is a nonzero finite extension of the ground field; the bound on that
sum then bounds the number of points. Finiteness of the residue field uses that the base change
is a finite morphism, which is the content of the characterisation of finite locally free
morphisms over the spectrum of a ring.

## References

* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Along a finite morphism to the spectrum of a field, every residue field of the source is a
finite extension of that field. -/
private lemma finite_residueField_of_finite_over_field
    (k : Type u) [Field k] {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k)) [IsFinite p]
    (z : Z) :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Z.Γevaluation z).hom.toAlgebra
    Module.Finite k (Z.residueField z) := by
  let : IsLocallyArtinian Z := IsLocallyArtinian.of_locallyQuasiFinite p
  let : LocallyOfFiniteType (Z.fromSpecResidueField z) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp
      (isClosed_discrete ({z} : Set Z))
    infer_instance
  have hcomp : LocallyOfFiniteType (Z.fromSpecResidueField z ≫ p) := inferInstance
  rw [← p.SpecMap_residueFieldMap_fromSpecResidueField z] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @LocallyOfFiniteType)] at hcomp
  let : Algebra k (Z.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Z.Γevaluation z).hom.toAlgebra
  let : Algebra.FiniteType k (Z.residueField z) := by
    show RingHom.FiniteType (algebraMap k (Z.residueField z))
    convert hcomp using 1
    · rfl
    · simp only [RingHom.algebraMap_toAlgebra]
      rw [← Scheme.Γevaluation_naturality]
      simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  exact finite_of_finite_type_of_isJacobsonRing _ _

/-- **Stacks Project, Tag 03J5.** If all field-valued base changes of a morphism are finite of
degree at most `n`, then each of them has at most `n` points. -/
@[stacks 03J5 "card_fibre_le_bound"]
theorem cardinalMk_pullback_le_of_degree_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (h : ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
      ∃ r ≤ n, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r) :
    ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
      Cardinal.mk (pullback g f : Scheme.{u}) ≤ n := by
  intro k _ g
  obtain ⟨r, -, hr⟩ := h k g
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r := hr
  let hflf : Stacks.Morphisms.IsFiniteLocallyFree (pullback.fst g f) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r
  let : IsFinite (pullback.fst g f) :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_of_specTarget (pullback.fst g f)).mp hflf).1
  apply Cardinal.card_le_of
  intro s
  classical
  let e : Fin s.card ≃ s := s.equivFin.symm
  let x : Fin s.card → (pullback g f : Scheme.{u}) := fun i ↦ (e i : _)
  have hx : Function.Injective x := Subtype.val_injective.comp e.injective
  have hle : s.card ≤ ∑ i : Fin s.card,
      (let := ((Scheme.ΓSpecIso (.of k)).inv ≫ (pullback.fst g f).appTop ≫
        (pullback g f).Γevaluation (x i)).hom.toAlgebra
      Module.finrank k ((pullback g f).residueField (x i))) := by
    calc
      s.card = ∑ _ : Fin s.card, (1 : ℕ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        let : Algebra k ((pullback g f).residueField (x i)) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (pullback.fst g f).appTop ≫
            (pullback g f).Γevaluation (x i)).hom.toAlgebra
        let : Module.Finite k ((pullback g f).residueField (x i)) :=
          finite_residueField_of_finite_over_field k (pullback.fst g f) (x i)
        exact Module.finrank_pos
  exact hle.trans <|
    AlgebraicGeometry.sum_finrank_residueField_le_of_degree_le f n h k g x hx

end AlgebraicGeometry

end
