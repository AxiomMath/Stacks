module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.Examples.Flatness.ProjFamilyNotFinitePresentation

/-!
# A proper flat geometrically connected and reduced morphism not of finite presentation

Properness and flatness do not force finite presentation, even for a morphism all of whose
geometric fibres are connected and reduced. Let `R` be a ring with an ideal `I` for which `R ⧸ I`
is finite and flat but not projective, so that `I` is not finitely generated, and let

`X = Proj R[X₀, X₁, X₂] ⧸ (a X₂ : a ∈ I) ⟶ Spec R`

be the projective family of the coefficientwise family `Stacks.Examples.ProjFamily.planeFamily`.
For every field `L` and every ring map `R → L` the ideal `I` extends to `⊥` or to `⊤`, because a
field has no other ideals, and the base change of the family along `Spec L ⟶ Spec R` is accordingly
`ℙ²_L` or `ℙ¹_L`. Projective space over a field is integral, hence connected and reduced, so the
family is geometrically connected and geometrically reduced; it is proper and flat, and it is not
locally of finite presentation because `I` is not finitely generated.

Since the family is proper it is quasi-compact and quasi-separated, so finite presentation of it
asks nothing beyond local finite presentation, and the conclusion can be stated for finite
presentation itself.

## Main results

* `Stacks.Examples.finitePresentation_iff_locallyOfFinitePresentation_of_isProper`: a proper
  morphism is of finite presentation exactly when it is locally of finite presentation.
* `Stacks.Examples.ProjFamily.exists_isPullback_projectiveSpace_planeFamily`: every base change
  of the family to a field is a projective space over that field.
* `Stacks.Examples.ProjFamily.geometricallyConnected_toSpecBase_planeFamily` and
  `Stacks.Examples.ProjFamily.geometricallyReduced_toSpecBase_planeFamily`: the family has
  geometrically connected and geometrically reduced fibres.
* `Stacks.Examples.exists_proper_flat_geometricallyConnected_not_finitePresentation`: there is a
  proper flat morphism with geometrically connected and geometrically reduced fibres which is not
  of finite presentation.

## References

* [Stacks Project, Tag 05LC](https://stacks.math.columbia.edu/tag/05LC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Stacks.CoefficientProj

namespace Stacks.Examples

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A proper morphism is of finite presentation exactly when it is locally of finite
presentation. -/
theorem finitePresentation_iff_locallyOfFinitePresentation_of_isProper {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] :
    FinitePresentation f ↔ LocallyOfFinitePresentation f :=
  ⟨fun h => h.1, fun h => ⟨h, inferInstance, inferInstance⟩⟩

namespace ProjFamily

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Every base change of the family `Proj R[X₀, X₁, X₂] ⧸ (a X₂ : a ∈ I)` to a field `L` is a
projective space `ℙ²_L` or `ℙ¹_L` over that field. -/
theorem exists_isPullback_projectiveSpace_planeFamily (L : Type u) [Field L] [Algebra R L] :
    ∃ (n : ℕ) (g : projectiveSpaceOverRing n (CommRingCat.of L) ⟶
        AlgebraicGeometry.Proj (projGrading (planeFamily R I))),
      IsPullback g (projectiveSpaceOverRing n (CommRingCat.of L) ↘ Spec (CommRingCat.of L))
        (toSpecBase (planeFamily R I)) (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
  rcases (I.map (algebraMap R L)).eq_bot_or_top with h | h
  · obtain ⟨g, hg⟩ := exists_isPullback_projectiveSpace (planeFamily R I) L
      (coefficientIdeal_baseChange_planeFamily_of_bot R I L h)
    exact ⟨2, g, hg⟩
  · obtain ⟨g, hg⟩ := exists_isPullback_projectiveSpace_of_span_X_last (S := L) (n := 1)
      (planeFamily R I) (coefficientIdeal_baseChange_planeFamily_of_top R I L h)
    exact ⟨1, g, hg⟩

/-- The family `Proj R[X₀, X₁, X₂] ⧸ (a X₂ : a ∈ I)` is geometrically connected over `Spec R`. -/
theorem geometricallyConnected_toSpecBase_planeFamily :
    GeometricallyConnected (toSpecBase (planeFamily R I)) := by
  refine ⟨?_⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro L _ _
  obtain ⟨n, g, hg⟩ := exists_isPullback_projectiveSpace_planeFamily I L
  exact ObjectProperty.prop_of_iso (C := Scheme.{u}) (ConnectedSpace ·) hg.isoPullback
    inferInstance

/-- The family `Proj R[X₀, X₁, X₂] ⧸ (a X₂ : a ∈ I)` is geometrically reduced over `Spec R`. -/
theorem geometricallyReduced_toSpecBase_planeFamily :
    GeometricallyReduced (toSpecBase (planeFamily R I)) := by
  refine ⟨?_⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro L _ _
  obtain ⟨n, g, hg⟩ := exists_isPullback_projectiveSpace_planeFamily I L
  exact ObjectProperty.prop_of_iso (C := Scheme.{u}) (IsReduced ·) hg.isoPullback inferInstance

end ProjFamily

open ProjFamily

/-- There is a proper flat morphism of schemes which is geometrically connected and geometrically
reduced and which is not of finite presentation, nor even locally of finite presentation. -/
theorem exists_proper_flat_geometricallyConnected_not_finitePresentation :
    ∃ (R : Type u) (_ : CommRing R) (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
      IsProper f ∧ AlgebraicGeometry.Flat f ∧ GeometricallyConnected f ∧
        GeometricallyReduced f ∧ ¬ FinitePresentation f ∧ ¬ LocallyOfFinitePresentation f := by
  classical
  obtain ⟨D⟩ := nonempty_finiteFlatNonprojectiveQuotient.{u}
  have := D.flat
  have hproper : IsProper (toSpecBase (planeFamily D.R D.I)) :=
    isProper_toSpecBase _ (monotone_planeFamily D.R D.I) (planeFamily_zero D.R D.I)
  have hnot : ¬ LocallyOfFinitePresentation (toSpecBase (planeFamily D.R D.I)) :=
    not_locallyOfFinitePresentation _ (Fin.last 2) D.I (planeFamily_single_le D.R D.I)
      (le_planeFamily_single D.R D.I) D.not_fg
  exact ⟨D.R, inferInstance, AlgebraicGeometry.Proj (projGrading (planeFamily D.R D.I)),
    toSpecBase (planeFamily D.R D.I), hproper,
    flat_toSpecBase _ (monotone_planeFamily D.R D.I) (planeFamily_zero D.R D.I)
      (flat_quotient_planeFamily D.R D.I),
    geometricallyConnected_toSpecBase_planeFamily D.I,
    geometricallyReduced_toSpecBase_planeFamily D.I,
    fun h => hnot ((finitePresentation_iff_locallyOfFinitePresentation_of_isProper _).1 h), hnot⟩

end Stacks.Examples

end
