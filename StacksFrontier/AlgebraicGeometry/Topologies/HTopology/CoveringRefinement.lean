module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhCoveringRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Recognising h coverings by refinement

A family of morphisms of schemes which are locally of finite presentation is an h covering
exactly when some h covering refines it, and exactly when the single morphism from the
disjoint union of its sources is an h covering.

## Main results

* `AlgebraicGeometry.isHCovering_tfae`: the three equivalent descriptions.

## Implementation notes

Refinement is a `CategoryTheory.PreZeroHypercover.Hom`, and the disjoint-union morphism is
`CategoryTheory.Limits.Sigma.desc` regarded as a family indexed by `Unit`.  The index type is
assumed small relative to the universe of the schemes, so that the coproduct exists.

Since an h covering is a ph covering whose members are locally of finite presentation, and
local finite presentation is Zariski-local at the source — so that it passes to the
disjoint-union morphism — each of the three conditions differs from the corresponding
condition for ph coverings by the same standing hypothesis.  The content is therefore the
analogous statement for ph coverings, `AlgebraicGeometry.isPHCovering_tfae`.

## References

* [Stacks Project, Tag 0ETX](https://stacks.math.columbia.edu/tag/0ETX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- **Stacks 0ETX.** A family of morphisms of schemes which are locally of finite
presentation is an h covering if and only if some h covering refines it, if and only if its
disjoint-union morphism is an h covering. -/
@[stacks 0ETX]
public theorem isHCovering_tfae {T : Scheme.{u}} {I : Type v} [Small.{u} I]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hlfp : ∀ i, LocallyOfFinitePresentation (f i)) :
    List.TFAE [
      IsHCovering X f,
      ∃ (K : Type v) (Y : K → Scheme.{u}) (g : ∀ k, Y k ⟶ T),
        IsHCovering Y g ∧
          Nonempty
            (({ I₀ := K, X := Y, f := g } : PreZeroHypercover T).Hom
              ({ I₀ := I, X := X, f := f } : PreZeroHypercover T)),
      IsHCovering (fun _ : Unit ↦ ∐ X) (fun _ ↦ Sigma.desc f)] := by
  have hft : ∀ i, LocallyOfFiniteType (f i) := fun i ↦ have := hlfp i; inferInstance
  have hph := isPHCovering_tfae X f hft
  have hdesc : LocallyOfFinitePresentation (Sigma.desc f) := by
    have : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation) hlfp
  have h₁ : IsHCovering X f ↔ IsPHCovering X f := and_iff_right hlfp
  have h₃ : IsHCovering (fun _ : Unit ↦ ∐ X) (fun _ ↦ Sigma.desc f) ↔
      IsPHCovering (fun _ : Unit ↦ ∐ X) (fun _ ↦ Sigma.desc f) :=
    and_iff_right fun _ ↦ hdesc
  apply List.tfae_of_forall (b := IsHCovering X f)
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  · exact Iff.rfl
  · constructor
    · rintro ⟨K, Y, g, hY, hhom⟩
      have hex : ∃ (K : Type v) (Y : K → Scheme.{u}) (g : ∀ k, Y k ⟶ T),
          IsPHCovering Y g ∧
            Nonempty (({ I₀ := K, X := Y, f := g } : PreZeroHypercover T).Hom
              ({ I₀ := I, X := X, f := f } : PreZeroHypercover T)) :=
        ⟨K, Y, g, hY.2, hhom⟩
      exact h₁.2 ((hph.out 2 1).1 hex)
    · intro h
      exact ⟨I, X, f, h, ⟨PreZeroHypercover.Hom.id _⟩⟩
  · exact h₃.trans ((hph.out 3 1).trans h₁.symm)

end AlgebraicGeometry
