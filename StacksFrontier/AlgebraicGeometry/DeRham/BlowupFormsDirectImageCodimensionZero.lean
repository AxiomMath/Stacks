module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.StandardChart
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve

/-!
# Clauses (1) and (2) of Stacks 0FUU fail for a centre of codimension zero

[Stacks, Tag 0FUU] is stated for an arbitrary closed immersion `i : Z ⟶ X` of schemes smooth
over `S`.  Its clauses (1) and (2) are false when `Z` contains a non-empty open subset of `X`.
The smallest instance is `S = X = Z = Spec k` with `i = 𝟙`.  The ideal of the centre is then
zero, the Rees algebra is `𝒪_X ⊕ 0 ⊕ 0 ⊕ ⋯`, and its `Proj` is empty.  So the blowup `X'` and
the exceptional divisor `E` are empty, and the comparisons `𝒪_X ⟶ b_*𝒪_{X'} = 0` and
`𝒪_Z ⟶ p_*𝒪_E = 0` are not isomorphisms.  Clause (3) holds there for the trivial reason that
both sides vanish.

The source's own proof does not reach this case.  The local model of Section 50.16 (Tag 0FUB)
assumes `1 ≤ n`, but the étale-local structure theorem of Tag 0FUE also allows `n = 0`, where the
centre is open in `X`.

## Main results

* `Stacks.DeRham.isEmpty_blowUp_bot`: the blowup of a scheme in the zero ideal is empty.
* `Stacks.DeRham.not_isIso_blowupFormsDirectImage_of_isIso` and
  `Stacks.DeRham.not_isIso_exceptionalFormsDirectImage_of_isIso`: when `i` is an isomorphism and
  `Z` is non-empty, the degree-zero comparisons of clauses (1) and (2) are not isomorphisms.
* `Stacks.DeRham.not_isIso_blowupFormsDirectImage_id` and
  `Stacks.DeRham.not_isIso_exceptionalFormsDirectImage_id`: the case `i = f = 𝟙 X`.
* `Stacks.DeRham.exists_smooth_not_isIso_formsDirectImage`: the counterexample at the
  hypotheses of the tag, with `S = X = Z = Spec ℚ`.

The corrected clauses (1) and (2) assume that the image of `i` has empty interior in `X`.  That
is exactly the hypothesis which forces `n ≥ 1` on every chart of Tag 0FUE.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0FUB](https://stacks.math.columbia.edu/tag/0FUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.DeRham

/-- **The blowup in the zero ideal is empty**, for the relative `Proj` of the Rees algebra sheaf.
Each standard affine chart `Γ(X, U)[I(U)/a]` of
the blowup is attached to a section `a` of `I(U) = 0`, so `a = 0` and the chart is empty. -/
theorem isEmpty_blowUp_bot' (X : Scheme.{u}) :
    IsEmpty (AlgebraicGeometry.blowUp (⊥ : X.IdealSheafData)) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, a, z, -⟩ := exists_mem_range_blowUpAffineChart (⊥ : X.IdealSheafData) x
  have ha : (a : X.presheaf.obj (.op U.1)) = 0 := (Submodule.mem_bot _).1 a.2
  exact (isEmpty_spec_blowUpAffineChartRing_of_eq_zero _ U a ha).elim z

/-- **The blowup in the zero ideal is empty**, for the glued construction `Stacks.Blowup.blowUp`;
it is isomorphic to `AlgebraicGeometry.blowUp`, which is empty by `isEmpty_blowUp_bot'`. -/
theorem isEmpty_blowUp_bot (X : Scheme.{u}) :
    IsEmpty (Stacks.Blowup.blowUp (⊥ : X.IdealSheafData)) :=
  ⟨fun x => (isEmpty_blowUp_bot' X).elim ((blowUpIso (⊥ : X.IdealSheafData)).inv x)⟩

/-- On an empty scheme every module has subsingleton sections, since the rings of sections are
zero. -/
theorem subsingleton_sections_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (M : Y.Modules)
    (U : Y.Opens) : Subsingleton Γ(M, U) :=
  Module.subsingleton Γ(Y, U) _

/-- A map from the degree-zero forms on a non-empty scheme to a direct image from an empty
scheme is never an isomorphism.  Its source has global sections `Γ(X, 𝒪_X) ≠ 0` and its target
has none. -/
theorem not_isIso_of_isEmpty {S X Y : Scheme.{u}} [Nonempty X] (f : X ⟶ S) (g : Y ⟶ X)
    [IsEmpty Y] (M : Y.Modules)
    (φ : Scheme.Hom.relativeDifferentialForms f 0 ⟶ (Scheme.Modules.pushforward g).obj M) :
    ¬ IsIso φ := by
  intro hφ
  let e := (Scheme.Hom.relativeDifferentialFormsZeroIso f).symm ≪≫ asIso φ
  have : IsIso (e.hom.app ⊤) := Scheme.Modules.Hom.isIso_iff_isIso_app.1 (Iso.isIso_hom e) ⊤
  have : Subsingleton Γ((Scheme.Modules.pushforward g).obj M, ⊤) :=
    subsingleton_sections_of_isEmpty M (g ⁻¹ᵁ ⊤)
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  exact not_subsingleton Γ(X, ⊤)
    (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).1.subsingleton

/-- The glued blowup in the kernel ideal of an isomorphism is empty. -/
private theorem isEmpty_blowUp_ker_of_isIso {X Z : Scheme.{u}} (i : Z ⟶ X) [IsIso i] :
    IsEmpty (Stacks.Blowup.blowUp i.ker) := by
  rw [Scheme.Hom.ker_eq_bot_of_isIso]
  exact isEmpty_blowUp_bot X

/-- The relative-`Proj` blowup in the kernel ideal of an isomorphism is empty. -/
private theorem isEmpty_blowUp_ker_of_isIso' {X Z : Scheme.{u}} (i : Z ⟶ X) [IsIso i] :
    IsEmpty (AlgebraicGeometry.blowUp i.ker) := by
  rw [Scheme.Hom.ker_eq_bot_of_isIso]
  exact isEmpty_blowUp_bot' X

/-- **Clause (1) of [Stacks, Tag 0FUU] fails for a centre equal to the whole scheme.**  If the
closed immersion `i` is an isomorphism and `Z` is non-empty, then the blowup is empty, and
`Ω^0_{X/S} ⟶ b_*Ω^0_{X'/S}` is not an isomorphism. -/
theorem not_isIso_blowupFormsDirectImage_of_isIso {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsIso i] [Nonempty Z] : ¬ IsIso (blowupFormsDirectImage i f 0) := by
  have : Nonempty X := ⟨i (Classical.arbitrary Z)⟩
  have := isEmpty_blowUp_ker_of_isIso i
  exact not_isIso_of_isEmpty f _ _ _

/-- **Clause (2) of [Stacks, Tag 0FUU] fails for a centre equal to the whole scheme.**  If the
closed immersion `i` is an isomorphism and `Z` is non-empty, then the exceptional divisor is
empty, and `Ω^0_{Z/S} ⟶ p_*Ω^0_{E/S}` is not an isomorphism. -/
theorem not_isIso_exceptionalFormsDirectImage_of_isIso {S X Z : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) [IsIso i] [Nonempty Z] : ¬ IsIso (exceptionalFormsDirectImage i f 0) := by
  have := isEmpty_blowUp_ker_of_isIso i
  have : IsEmpty (Stacks.Blowup.exceptionalDivisor i.ker) :=
    ⟨fun x => isEmptyElim ((Stacks.Blowup.exceptionalIdeal i.ker).subschemeι x)⟩
  exact not_isIso_of_isEmpty (i ≫ f) _ _ _

/-- Clause (1) of [Stacks, Tag 0FUU] fails for `f = i = 𝟙 X` on any non-empty scheme `X`. -/
theorem not_isIso_blowupFormsDirectImage_id (X : Scheme.{u}) [Nonempty X] :
    ¬ IsIso (blowupFormsDirectImage (𝟙 X) (𝟙 X) 0) :=
  not_isIso_blowupFormsDirectImage_of_isIso (𝟙 X) (𝟙 X)

/-- Clause (2) of [Stacks, Tag 0FUU] fails for `f = i = 𝟙 X` on any non-empty scheme `X`. -/
theorem not_isIso_exceptionalFormsDirectImage_id (X : Scheme.{u}) [Nonempty X] :
    ¬ IsIso (exceptionalFormsDirectImage (𝟙 X) (𝟙 X) 0) :=
  not_isIso_exceptionalFormsDirectImage_of_isIso (𝟙 X) (𝟙 X)

/-- **Clauses (1) and (2) of [Stacks, Tag 0FUU] are false as stated.**  The hypotheses of the
tag hold for `S = X = Z = Spec ℚ` with `f = i = 𝟙`: `f` and `i ≫ f` are smooth and `i` is a
closed immersion.  Yet neither comparison is an isomorphism in degree `0`. -/
theorem exists_smooth_not_isIso_formsDirectImage :
    ∃ (S X Z : Scheme.{u}) (f : X ⟶ S) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : Smooth f)
      (_ : Smooth (i ≫ f)),
      ¬ IsIso (blowupFormsDirectImage i f 0) ∧ ¬ IsIso (exceptionalFormsDirectImage i f 0) := by
  let X : Scheme.{u} := Spec (.of (ULift.{u} ℚ))
  exact ⟨X, X, X, 𝟙 X, 𝟙 X, inferInstance, inferInstance, inferInstance,
    not_isIso_blowupFormsDirectImage_id X, not_isIso_exceptionalFormsDirectImage_id X⟩

/-- **Clause (1) of [Stacks, Tag 0FUU] fails for a centre equal to the whole scheme**, for the
relative-`Proj` blowup `AlgebraicGeometry.blowUpToBase` and the comparison map
`AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison`. -/
theorem not_isIso_formsDirectImageComparison_blowUpToBase_of_isIso {S X Z : Scheme.{u}}
    (f : X ⟶ S) (i : Z ⟶ X) [IsIso i] [Nonempty Z] :
    ¬ IsIso (Scheme.Hom.formsDirectImageComparison (blowUpToBase i.ker) f 0) := by
  have : Nonempty X := ⟨i (Classical.arbitrary Z)⟩
  have := isEmpty_blowUp_ker_of_isIso' i
  exact not_isIso_of_isEmpty f _ _ _

/-- **Clause (2) of [Stacks, Tag 0FUU] fails for a centre equal to the whole scheme**, for the
exceptional divisor of `AlgebraicGeometry.blowUp` and its structure morphism
`AlgebraicGeometry.exceptionalDivisorToCentre`. -/
theorem not_isIso_formsDirectImageComparison_exceptionalDivisorToCentre_of_isIso
    {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsIso i] [Nonempty Z] :
    ¬ IsIso (Scheme.Hom.formsDirectImageComparison (exceptionalDivisorToCentre i) (i ≫ f) 0) := by
  have := isEmpty_blowUp_ker_of_isIso' i
  have : IsEmpty (AlgebraicGeometry.exceptionalDivisor i.ker) :=
    ⟨fun x => isEmptyElim ((AlgebraicGeometry.exceptionalIdeal i.ker).subschemeι x)⟩
  exact not_isIso_of_isEmpty (i ≫ f) _ _ _

/-- **Clauses (1) and (2) of [Stacks, Tag 0FUU] are false as stated**, in the spelling of the
relative-`Proj` blowup: for `S = X = Z = Spec ℚ` with `f = i = 𝟙` the hypotheses of the tag
hold and neither comparison is an isomorphism in degree `0`. -/
theorem exists_smooth_not_isIso_formsDirectImageComparison_blowUpToBase :
    ∃ (S X Z : Scheme.{u}) (f : X ⟶ S) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : Smooth f)
      (_ : Smooth (i ≫ f)),
      ¬ IsIso (Scheme.Hom.formsDirectImageComparison (blowUpToBase i.ker) f 0) ∧
        ¬ IsIso
          (Scheme.Hom.formsDirectImageComparison (exceptionalDivisorToCentre i) (i ≫ f) 0) := by
  let X : Scheme.{u} := Spec (.of (ULift.{u} ℚ))
  exact ⟨X, X, X, 𝟙 X, 𝟙 X, inferInstance, inferInstance, inferInstance,
    not_isIso_formsDirectImageComparison_blowUpToBase_of_isIso (𝟙 X) (𝟙 X),
    not_isIso_formsDirectImageComparison_exceptionalDivisorToCentre_of_isIso (𝟙 X) (𝟙 X)⟩

end Stacks.DeRham
