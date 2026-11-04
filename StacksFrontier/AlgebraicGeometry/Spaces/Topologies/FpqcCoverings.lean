module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Scheme refinements of the fpqc coverings of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. Every fpqc covering of an algebraic
space over `S` is refined by an fpqc covering whose members are schemes: each member of the
given family has a surjective étale scheme atlas, which is an étale and hence an fpqc covering
of it, and composing the two coverings gives the refinement.

## Main results

* `AlgebraicGeometry.Space.exists_fpqc_scheme_refinement`: **Stacks 0419**.

## Implementation notes

A scheme over the base is represented by the Yoneda presheaf of an object of the chosen big
fppf site, and the refining family is indexed by the index type of the given family, so the
factorisation through the original members is part of the statement rather than a condition on
an unnamed covering family. Composing the given covering with the one-member atlas coverings
of its sources indexes the composite by `Σ i, Unit`, and
`AlgebraicGeometry.Space.isFpqcCovering_reindex` transports it back to the original index type
along the section `i ↦ ⟨i, ()⟩`.

The refining morphisms are the atlases of the members, so they are relatively étale, and the
statement records this: it is what lets the refinement be used where the base change of the
given covering along it has to be controlled, flatness of the refining morphisms being exactly
what the source's "again because flat base change preserves the property" appeals to.

## References

* [Stacks Project, Tag 0419](https://stacks.math.columbia.edu/tag/0419)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0419.** Every fpqc covering of an algebraic space over `S` by algebraic spaces
has an fpqc refinement by schemes, with each new member factoring through the corresponding
member of the original covering by a relatively étale morphism. -/
@[stacks 0419]
theorem exists_fpqc_scheme_refinement
    {I : Type v} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Xᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXᵢ : ∀ i, IsAlgebraicSpace B S hS (Xᵢ i))
    (f : ∀ i, Xᵢ i ⟶ X) (hf : IsFpqcCovering B S hS f) :
    ∃ (T : I → BigFppfOver B S hS) (e : ∀ i, yoneda.obj (T i) ⟶ Xᵢ i),
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (e i)) ∧
        IsFpqcCovering B S hS (fun i => e i ≫ f i) := by
  classical
  choose T e hsurj hetale using fun i => (hXᵢ i).exists_atlas
  have hEtaleCovering (i : I) :
      IsEtaleCovering B S hS (fun _ : Unit => yoneda.obj (T i)) (fun _ => e i) := by
    refine ⟨hXᵢ i, fun _ => isAlgebraicSpace_yoneda B S hS (T i),
      fun _ => (isEtale_iff_presheaf_of_yoneda B S hS (e i)).2 (hetale i), ?_⟩
    rw [Set.iUnion_const, Set.range_eq_univ]
    exact (surjective_iff_surjective_pointsMap B S hS (Xᵢ i) (hXᵢ i) (T i) (e i)).1 (hsurj i)
  refine ⟨T, e, hetale, ?_⟩
  exact isFpqcCovering_reindex B S hS
    (isFpqcCovering_comp B S hS (X := X) (Xi := Xᵢ)
      (Xij := fun ij : Σ _ : I, Unit => yoneda.obj (T ij.1)) hX hXᵢ
      (fun i _ => isAlgebraicSpace_yoneda B S hS (T i)) f (fun i _ => e i) hf
      (fun i => isFpqcCovering_of_isEtaleCovering B S hS
        (fun _ : Unit => yoneda.obj (T i)) (fun _ => e i) (hEtaleCovering i)))
    (σ := fun i : I => (⟨i, ()⟩ : Σ _ : I, Unit))
    (fun p => ⟨p.1, by cases p.2; rfl⟩)

end AlgebraicGeometry.Space

end
