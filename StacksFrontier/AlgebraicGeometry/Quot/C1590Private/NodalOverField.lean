module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# At-worst-nodal morphisms to the spectrum of a field

A morphism of schemes `f : X ⟶ Spec k`, locally of finite presentation, from a nonempty scheme, is
at-worst-nodal of relative dimension one (Stacks 0C5A) exactly when `X` is equidimensional of
dimension one with at-worst-nodal singularities over `k` (Stacks 0C47). This is the criterion of
Stacks 0C59 over a field: the only fibre of `f` is `X` itself, over the residue field of the
point of `Spec k`, which is `k`.

## Main results

* `AlgebraicGeometry.C1590Private.isAtWorstNodalOfRelativeDimensionOne_iff_of_field`.

## References

* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

/-- **Stacks 0C59 over a field.** A morphism `f : X ⟶ Spec k` from a nonempty scheme, locally of
finite presentation, is at-worst-nodal of relative dimension one exactly when `X` is
equidimensional of dimension one and has at-worst-nodal singularities over `k`. -/
theorem isAtWorstNodalOfRelativeDimensionOne_iff_of_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation f] [Nonempty X] :
    IsAtWorstNodalOfRelativeDimensionOne f ↔
      TopologicalSpace.Equidimensional X ∧ topologicalKrullDim X = 1 ∧
        (letI : X.Over (Spec (.of k)) := ⟨f⟩; Stacks.Curves.HasAtWorstNodalSingularities k X) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have hg1 : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 _ from rfl, Spec.map_id]
  have : IsIso ((Spec (.of k)).descResidueField
      (Scheme.stalkClosedPointTo (𝟙 (Spec (.of k))))) := by
    have := isIso_descResidueField_of_surjective (algebraMap k k) Function.surjective_id
    rwa [hg1] at this
  obtain ⟨s, φ, hφ, E, hE₂⟩ : ∃ (s : Spec (.of k))
      (φ : CommRingCat.of ((Spec (.of k)).residueField s) ⟶ CommRingCat.of k)
      (_ : IsIso φ) (E : f.fiber s ≅ pullback f (𝟙 (Spec (.of k)))),
      E.hom ≫ pullback.snd f (𝟙 _) ≫ Spec.map φ = f.fiberToSpecResidueField s := by
    obtain ⟨E, -, hE₂⟩ := exists_iso_fiber_pullback_of_isIso_descResidueField f (𝟙 _)
    exact ⟨_, _, inferInstance, E, hE₂⟩
  have := hφ
  have : LocallyOfFiniteType f := inferInstance
  let e : f.fiber s ≅ X := E ≪≫ asIso (pullback.fst f (𝟙 _))
  have hsnd : pullback.snd f (𝟙 (Spec (.of k))) = pullback.fst f (𝟙 _) ≫ f := by
    simpa using (pullback.condition (f := f) (g := 𝟙 (Spec (.of k)))).symm
  have he : e.hom ≫ f ≫ Spec.map φ = f.fiberToSpecResidueField s := by
    rw [← hE₂, hsnd]
    simp [e]
  have he' : e.inv ≫ f.fiberToSpecResidueField s ≫ Spec.map (inv φ) = f := by
    rw [← he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, IsIso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  let : (f.fiber s).Over (Spec (.of ((Spec (.of k)).residueField s))) :=
    ⟨f.fiberToSpecResidueField s⟩
  have : LocallyOfFiniteType (f.fiber s ↘ Spec (.of ((Spec (.of k)).residueField s))) :=
    inferInstanceAs (LocallyOfFiniteType (f.fiberToSpecResidueField s))
  have hX : (TopologicalSpace.Equidimensional X ∧ topologicalKrullDim X = 1 ∧
      Stacks.Curves.HasAtWorstNodalSingularities k X) ↔
      (TopologicalSpace.Equidimensional (f.fiber s) ∧
          topologicalKrullDim (f.fiber s) = (1 : WithBot ℕ∞) ∧
            Stacks.Curves.HasAtWorstNodalSingularities ((Spec (.of k)).residueField s)
              (f.fiber s)) := by
    have hdimeq : topologicalKrullDim (f.fiber s) = topologicalKrullDim X :=
      IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph
    exact ⟨fun ⟨heq, hdim, hnod⟩ => ⟨heq.of_homeomorph (Scheme.homeoOfIso e), hdimeq.trans hdim,
        @Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ _ _ _ _ _ f
          (f.fiberToSpecResidueField s) _ hdim e.hom _ φ hφ he hnod⟩,
      fun ⟨heq, hdim, hnod⟩ => ⟨heq.of_homeomorph (Scheme.homeoOfIso e).symm,
        hdimeq.symm.trans hdim,
        @Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ _ _ _ _ _ (f.fiber s ↘ _) f
          _ hdim e.inv _ (inv φ) inferInstance he' hnod⟩⟩
  rw [← Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff, hX]
  have hne : Nonempty (f.fiber s) := ⟨e.inv (Classical.arbitrary X)⟩
  refine ⟨fun ⟨_, _, h⟩ => h s hne, fun h => ⟨inferInstance, inferInstance, fun t _ => ?_⟩⟩
  obtain rfl : t = s := Subsingleton.elim _ _
  exact h

end AlgebraicGeometry.C1590Private

end
