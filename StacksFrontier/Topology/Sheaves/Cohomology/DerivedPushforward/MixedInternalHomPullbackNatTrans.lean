module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDevissage

/-!
# The mixed comparison `Λ P 𝓗om(A, B) ⟶ 𝓗om(P A, P B)` is natural in its first argument

`Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparison` is the canonical map
of Stacks 08I3/08JF in the mixed form Stacks 08JP needs, where the internal hom of the target
lands one category further on and the source of the map is carried there by `Λ`. This file proves
it is **natural in its first argument** and assembles it into a natural transformation

`comparisonSourceFunctor ⟶ comparisonTargetFunctor`

of functors on `D₁ᵒᵖ`, from the two clauses of Stacks 08J8 for each of the two tensor–internal-hom
bijections and nothing else.

The equal-universe form of this is
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparisonNatTrans`, and the proofs
below are that one's, with `P` replaced by `P ⋙ Λ` wherever the source of the comparison appears.
As there, the construction uses no shift, no triangulated structure, and no hypothesis on the
three categories.

## Implementation notes

The dévissage
`Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.isIso_homComparison_of_generatedByOp`
takes the natural transformation whose components are the comparison as a hypothesis `η`,
together with the equation `hη` identifying its components. Here `homComparisonNatTrans` is that
transformation and `homComparisonNatTrans_app` is that equation, by `rfl`. So
`MixedTranspose.isIso_homComparison_of_generatedByOp_natTrans` states the dévissage with no `η`
and no `hη`, exactly as `Transpose.isIso_homComparison_of_generatedByOp_natTrans` does in the
equal-universe case.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.MixedTensorHomEquivDinatural`: the
  dinaturality of the mixed tensor–internal-hom bijection in its internal-hom variable, the
  second clause of Stacks 08J8 in the mixed shape.
* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparisonNatTrans`: **the
  mixed comparison as a natural transformation of its first argument.**
* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.commShift_comparisonSourceFunctor`,
  `commShift_comparisonTargetFunctor`, `isTriangulated_comparisonSourceFunctor`,
  `isTriangulated_comparisonTargetFunctor`: the two sides of the dévissage commute with the shift
  and are triangulated, **as a composition**: the two comparison functors are built from the
  contravariant internal hom of their own side and from `P` and `Λ`, so each property of theirs
  is the conjunction of that property for the factors. For `P` the opposite functor `P.op` is
  covered by Mathlib's `CategoryTheory.Pretriangulated.Opposite.commShiftFunctorOpInt` and
  `functor_isTriangulated_op`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparisonDatum_dinatural`: the
  transpose datum of the mixed comparison is dinatural in the first argument.
* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparison_naturality_source`:
  **the mixed comparison is natural in its first argument.**
* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.isIso_homComparison_of_retract`:
  invertibility of the mixed comparison passes to a retract of its first argument, from
  naturality alone.
* `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.ShiftCompatible`: the shift
  compatibility of the comparison, as a property of the data.
* `MixedTranspose.isIso_homComparison_of_generatedByOp_natTrans`: the dévissage of Stacks 08JP
  with the natural transformation supplied and the shift data of the two sides reduced to that of
  their factors.

## References

* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose

/-! ### The second clause of Stacks 08J8 for the mixed bijection -/

/-- **Dinaturality of the mixed tensor–internal-hom bijection in its internal-hom variable:** the
transpose of a morphism postcomposed with the map induced by `φ : B' ⟶ B` is the transpose
precomposed with `1 ⊗ φ`.

This is `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.TensorHomEquivDinatural` in the
mixed shape, where the bijection's right-hand side is a hom into `Λ C`. It is the companion of
`Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.MixedTensorHomEquivNatural`, the
clause in the source variable, and like it it is a property of the data alone: it asserts nothing
about any instance of the comparison being invertible. -/
def MixedTensorHomEquivDinatural {D₂ D₂' : Type*} [Category D₂] [Category D₂'] (Λ : D₂ ⥤ D₂')
    (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂') (T₂ : D₂' × D₂ ⥤ D₂')
    (e₂ : ∀ (A : D₂') (B C : D₂), (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ Λ.obj C)) :
    Prop :=
  ∀ (A : D₂') (B B' C : D₂) (φ : B' ⟶ B) (ψ : A ⟶ (H₂.obj (op B)).obj C),
    e₂ A B' C (ψ ≫ (H₂.map φ.op).app C) = T₂.map (𝟙 A ×ₘ φ) ≫ e₂ A B C ψ

/-- The source clause of Stacks 08J8 in the shape
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.TensorHomEquivNaturalLeft` states it is
the shape `Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.TensorHomEquivNatural`
states it in, with the four objects in a different order. The first shape is the one the
ringed-space clause
`Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivNaturalLeft_ringedSpace` is stated
at; the second is the one the dévissage of `MixedInternalHomPullbackIso` consumes. -/
theorem tensorHomEquivNatural_of_naturalLeft {D₁ : Type*} [Category D₁] {H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁}
    {T₁ : D₁ × D₁ ⥤ D₁}
    {e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C)}
    (h : Transpose.TensorHomEquivNaturalLeft H₁ T₁ e₁) : TensorHomEquivNatural H₁ T₁ e₁ :=
  fun B C Z Z' f g => h Z Z' B C f g

/-! ### The mixed comparison is natural in its first argument -/

section Naturality

variable {D₁ D₂ D₂' : Type*} [Category D₁] [Category D₂] [Category D₂']
  (P : D₁ ⥤ D₂) (Λ : D₂ ⥤ D₂')
  (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂')
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂' × D₂ ⥤ D₂')
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ (A : D₂') (B C : D₂), (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ Λ.obj C))
  (m : T₁ ⋙ P ⋙ Λ ≅ (P ⋙ Λ).prod P ⋙ T₂)

/-- **The mixed transpose datum of the comparison is dinatural in the first argument.** The datum
is the mixed monoidality comparison followed by `Λ P` of the evaluation, so this is
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.evaluation_dinatural` conjugated by two
naturality squares of `m.inv`, one in each slot of the pair. -/
theorem homComparisonDatum_dinatural
    (hnat₁ : Transpose.TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hdin₁ : Transpose.TensorHomEquivDinatural H₁ T₁ e₁)
    {A B : D₁} (φ : A ⟶ B) (F : D₁) :
    T₂.map (Λ.map (P.map ((H₁.map φ.op).app F)) ×ₘ 𝟙 (P.obj A)) ≫
        homComparisonDatum P Λ H₁ T₁ T₂ e₁ m A F =
      T₂.map (𝟙 (Λ.obj (P.obj ((H₁.obj (op B)).obj F))) ×ₘ P.map φ) ≫
        homComparisonDatum P Λ H₁ T₁ T₂ e₁ m B F := by
  have key : ∀ (a b Z : D₁) (f₁ : a ⟶ (H₁.obj (op Z)).obj F) (f₂ : b ⟶ Z),
      T₂.map (Λ.map (P.map f₁) ×ₘ P.map f₂) ≫ homComparisonDatum P Λ H₁ T₁ T₂ e₁ m Z F =
        m.inv.app (a, b) ≫
          Λ.map (P.map (T₁.map (f₁ ×ₘ f₂) ≫ Transpose.evaluation H₁ T₁ e₁ Z F)) := by
    intro a b Z f₁ f₂
    have := m.inv.naturality (X := (a, b)) (Y := ((H₁.obj (op Z)).obj F, Z)) (f₁ ×ₘ f₂)
    simp only [homComparisonDatum, Functor.map_comp, ← Category.assoc]
    simpa using congrArg (· ≫ Λ.map (P.map (Transpose.evaluation H₁ T₁ e₁ Z F))) this
  have h₁ := key _ _ _ ((H₁.map φ.op).app F) (𝟙 A)
  have h₂ := key _ _ _ (𝟙 ((H₁.obj (op B)).obj F)) φ
  simp only [P.map_id, Λ.map_id] at h₁ h₂
  rw [h₁, h₂, Transpose.evaluation_dinatural H₁ T₁ e₁ hnat₁ hdin₁ φ F]

/-- **The mixed comparison is natural in its first argument.**

The square is checked after transposing under the mixed bijection `e₂`, which pins the comparison
down by `MixedTranspose.homComparison_adjoint`; the left-hand leg is moved across by the
naturality of `e₂` in its source variable and the right-hand one by its dinaturality in its
internal-hom variable, and what is left is `MixedTranspose.homComparisonDatum_dinatural`. -/
theorem homComparison_naturality_source
    (hnat₁ : Transpose.TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hdin₁ : Transpose.TensorHomEquivDinatural H₁ T₁ e₁)
    (hnat₂ : MixedTensorHomEquivNatural Λ H₂ T₂ e₂)
    (hdin₂ : MixedTensorHomEquivDinatural Λ H₂ T₂ e₂)
    {A B : D₁} (φ : A ⟶ B) (F : D₁) :
    Λ.map (P.map ((H₁.map φ.op).app F)) ≫ homComparison P Λ H₁ H₂ T₁ T₂ e₁ e₂ m A F =
      homComparison P Λ H₁ H₂ T₁ T₂ e₁ e₂ m B F ≫ (H₂.map (P.map φ).op).app (P.obj F) := by
  refine (e₂ (Λ.obj (P.obj ((H₁.obj (op B)).obj F))) (P.obj A) (P.obj F)).injective ?_
  rw [hnat₂ (P.obj A) (P.obj F) (Λ.obj (P.obj ((H₁.obj (op B)).obj F)))
      (Λ.obj (P.obj ((H₁.obj (op A)).obj F))) (Λ.map (P.map ((H₁.map φ.op).app F)))
      (homComparison P Λ H₁ H₂ T₁ T₂ e₁ e₂ m A F),
    hdin₂ (Λ.obj (P.obj ((H₁.obj (op B)).obj F))) (P.obj B) (P.obj A) (P.obj F) (P.map φ)
      (homComparison P Λ H₁ H₂ T₁ T₂ e₁ e₂ m B F),
    homComparison_adjoint, homComparison_adjoint]
  exact homComparisonDatum_dinatural P Λ H₁ T₁ T₂ e₁ m hnat₁ hdin₁ φ F

/-- **The mixed comparison as a natural transformation of its first argument**, from
`E ↦ Λ P 𝓗om₁(E, F)` to `E ↦ 𝓗om₂(P E, P F)` on `D₁ᵒᵖ`. Its components are the comparison, by
`MixedTranspose.homComparisonNatTrans_app`, and it is built with no hypothesis beyond the two
clauses of Stacks 08J8 for each of the two bijections.

This is the transformation the dévissage
`MixedTranspose.isIso_homComparison_of_generatedByOp` carries as the hypothesis `η`. -/
def homComparisonNatTrans
    (hnat₁ : Transpose.TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hdin₁ : Transpose.TensorHomEquivDinatural H₁ T₁ e₁)
    (hnat₂ : MixedTensorHomEquivNatural Λ H₂ T₂ e₂)
    (hdin₂ : MixedTensorHomEquivDinatural Λ H₂ T₂ e₂)
    (F : D₁) :
    comparisonSourceFunctor P Λ H₁ F ⟶ comparisonTargetFunctor P H₂ F where
  app E := homComparison P Λ H₁ H₂ T₁ T₂ e₁ e₂ m E.unop F
  naturality _ _ f :=
    homComparison_naturality_source P Λ H₁ H₂ T₁ T₂ e₁ e₂ m hnat₁ hdin₁ hnat₂ hdin₂ f.unop F

/-- **The components of `MixedTranspose.homComparisonNatTrans` are the mixed comparison**, which
is the equation the dévissage carries as the hypothesis `hη`. -/
@[simp]
theorem homComparisonNatTrans_app
    (hnat₁ : Transpose.TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hdin₁ : Transpose.TensorHomEquivDinatural H₁ T₁ e₁)
    (hnat₂ : MixedTensorHomEquivNatural Λ H₂ T₂ e₂)
    (hdin₂ : MixedTensorHomEquivDinatural Λ H₂ T₂ e₂)
    (F : D₁) (Z : D₁) :
    (homComparisonNatTrans P Λ H₁ H₂ T₁ T₂ e₁ e₂ m hnat₁ hdin₁ hnat₂ hdin₂ F).app (op Z) =
      homComparison P Λ H₁ H₂ T₁ T₂ e₁ e₂ m Z F :=
  rfl

/-- **Invertibility of the mixed comparison passes to a retract of its first argument.** If `A` is
a retract of `B` in `D₁` — so `A ⟶ B ⟶ A` is the identity — and the comparison at `B` is
invertible, then so is the comparison at `A`.

This is `Stacks.DerivedCategoryComparisons.isIso_app_of_retract` for
`MixedTranspose.homComparisonNatTrans`, and it uses *only* the naturality of that transformation:
no shift, no triangulated structure, and no hypothesis on the three categories. -/
theorem isIso_homComparison_of_retract
    (hnat₁ : Transpose.TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hdin₁ : Transpose.TensorHomEquivDinatural H₁ T₁ e₁)
    (hnat₂ : MixedTensorHomEquivNatural Λ H₂ T₂ e₂)
    (hdin₂ : MixedTensorHomEquivDinatural Λ H₂ T₂ e₂)
    (F : D₁) {A B : D₁} (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (hB : IsIso (homComparison P Λ H₁ H₂ T₁ T₂ e₁ e₂ m B F)) :
    IsIso (homComparison P Λ H₁ H₂ T₁ T₂ e₁ e₂ m A F) :=
  Stacks.DerivedCategoryComparisons.isIso_app_of_retract
    (homComparisonNatTrans P Λ H₁ H₂ T₁ T₂ e₁ e₂ m hnat₁ hdin₁ hnat₂ hdin₂ F)
    (X := op A) (Y := op B) ⟨r.op, i.op, by rw [← op_comp, hir, op_id]⟩ hB

end Naturality

/-! ### The two sides of the dévissage commute with the shift and are triangulated -/

section Shift

open scoped CategoryTheory.Pretriangulated.Opposite

variable {D₁ D₂ D₂' : Type*} [Category D₁] [Category D₂] [Category D₂']
  [HasShift D₁ ℤ] [HasShift D₂ ℤ] [HasShift D₂' ℤ]
  (P : D₁ ⥤ D₂) [P.CommShift ℤ] (Λ : D₂ ⥤ D₂') [Λ.CommShift ℤ]
  (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂')

/-- **The source side of the dévissage commutes with the shift.** It is
`H₁.flip.obj F ⋙ P ⋙ Λ`, so the commutation of the contravariant internal hom into `F` and the
commutations of `P` and of `Λ` compose. -/
instance commShift_comparisonSourceFunctor (F : D₁) [(H₁.flip.obj F).CommShift ℤ] :
    (comparisonSourceFunctor P Λ H₁ F).CommShift ℤ :=
  inferInstanceAs ((H₁.flip.obj F ⋙ P ⋙ Λ).CommShift ℤ)

/-- **The target side of the dévissage commutes with the shift.** It is
`P.op ⋙ H₂.flip.obj (P.obj F)`, and `P.op` commutes with the shift for the opposite shift of
`CategoryTheory.Pretriangulated.Opposite` whenever `P` does, so again the two compose. -/
instance commShift_comparisonTargetFunctor (F : D₁) [(H₂.flip.obj (P.obj F)).CommShift ℤ] :
    (comparisonTargetFunctor P H₂ F).CommShift ℤ :=
  inferInstanceAs ((P.op ⋙ H₂.flip.obj (P.obj F)).CommShift ℤ)

variable [HasZeroObject D₁] [HasZeroObject D₂] [HasZeroObject D₂']
  [Preadditive D₁] [Preadditive D₂] [Preadditive D₂']
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [∀ n : ℤ, (shiftFunctor D₂ n).Additive]
  [∀ n : ℤ, (shiftFunctor D₂' n).Additive]
  [CategoryTheory.Pretriangulated D₁] [CategoryTheory.Pretriangulated D₂]
  [CategoryTheory.Pretriangulated D₂']

/-- **The source side of the dévissage is triangulated**, being the composition of the
contravariant internal hom into `F` with `P` and with `Λ`. -/
instance isTriangulated_comparisonSourceFunctor (F : D₁) [(H₁.flip.obj F).CommShift ℤ]
    [(H₁.flip.obj F).IsTriangulated] [P.IsTriangulated] [Λ.IsTriangulated] :
    (comparisonSourceFunctor P Λ H₁ F).IsTriangulated :=
  inferInstanceAs ((H₁.flip.obj F ⋙ P ⋙ Λ).IsTriangulated)

/-- **The target side of the dévissage is triangulated**, being the composition of `P.op` — which
is triangulated for the opposite triangulation whenever `P` is, by Mathlib's
`CategoryTheory.Pretriangulated.Opposite.functor_isTriangulated_op` — with the contravariant
internal hom of the target into `P F`. -/
instance isTriangulated_comparisonTargetFunctor (F : D₁)
    [(H₂.flip.obj (P.obj F)).CommShift ℤ] [(H₂.flip.obj (P.obj F)).IsTriangulated]
    [P.IsTriangulated] :
    (comparisonTargetFunctor P H₂ F).IsTriangulated :=
  inferInstanceAs ((P.op ⋙ H₂.flip.obj (P.obj F)).IsTriangulated)

end Shift

/-! ### The shift compatibility of the comparison, as a property of the data -/

section ShiftCompatible

open scoped CategoryTheory.Pretriangulated.Opposite

variable {D₁ D₂ D₂' : Type*} [Category D₁] [Category D₂] [Category D₂']
  [HasShift D₁ ℤ] [HasShift D₂ ℤ] [HasShift D₂' ℤ]
  (P : D₁ ⥤ D₂) (Λ : D₂ ⥤ D₂')
  (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂')
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂' × D₂ ⥤ D₂')
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ (A : D₂') (B C : D₂), (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ Λ.obj C))
  (m : T₁ ⋙ P ⋙ Λ ≅ (P ⋙ Λ).prod P ⋙ T₂)

/-- **The mixed comparison is compatible with the shift**: the natural transformation
`MixedTranspose.homComparisonNatTrans` carries a `CategoryTheory.NatTrans.CommShift`, for the
shift commutations of its two sides that `MixedTranspose.commShift_comparisonSourceFunctor` and
`commShift_comparisonTargetFunctor` build out of the four commutations `hP`, `hΛ`, `hH₁`, `hH₂`.

It is a *property of the data* `e₁`, `e₂`, `m` and those four commutations, on a par with the
naturality clauses `MixedTensorHomEquivNatural` and `MixedTensorHomEquivDinatural`: it asserts
nothing about any instance of the comparison being invertible.

The four commutations are explicit arguments rather than instance binders, and that is not
cosmetic. The class `CategoryTheory.NatTrans.CommShift` needs the commutations of its two
functors, which are the *composites*; synthesising those composites from the factors is free over
abstract categories and is not at the derived categories of module sheaves of two ringed sites,
where `CategoryTheory.Functor.CommShift.comp` has to identify two spellings of the shift on the
middle category across a semireducible definition and fails. Taking the factors explicitly
performs that synthesis here, once, in the abstract. -/
def ShiftCompatible (hP : P.CommShift ℤ) (hΛ : Λ.CommShift ℤ)
    (hnat₁ : Transpose.TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hdin₁ : Transpose.TensorHomEquivDinatural H₁ T₁ e₁)
    (hnat₂ : MixedTensorHomEquivNatural Λ H₂ T₂ e₂)
    (hdin₂ : MixedTensorHomEquivDinatural Λ H₂ T₂ e₂)
    (F : D₁) (hH₁ : (H₁.flip.obj F).CommShift ℤ)
    (hH₂ : (H₂.flip.obj (P.obj F)).CommShift ℤ) : Prop :=
  letI := hP
  letI := hΛ
  letI := hH₁
  letI := hH₂
  NatTrans.CommShift
    (homComparisonNatTrans P Λ H₁ H₂ T₁ T₂ e₁ e₂ m hnat₁ hdin₁ hnat₂ hdin₂ F) ℤ

end ShiftCompatible

/-! ### The dévissage with the natural transformation supplied -/

section Generated

open scoped CategoryTheory.Pretriangulated.Opposite

variable {D₁ D₂ D₂' : Type*} [Category D₁] [Category D₂] [Category D₂']
  [HasZeroObject D₁] [HasZeroObject D₂] [HasZeroObject D₂']
  [Preadditive D₁] [Preadditive D₂] [Preadditive D₂']
  [HasShift D₁ ℤ] [HasShift D₂ ℤ] [HasShift D₂' ℤ]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [∀ n : ℤ, (shiftFunctor D₂ n).Additive]
  [∀ n : ℤ, (shiftFunctor D₂' n).Additive]
  [CategoryTheory.Pretriangulated D₁] [CategoryTheory.Pretriangulated D₂]
  [CategoryTheory.Pretriangulated D₂']
  (P : D₁ ⥤ D₂) (Λ : D₂ ⥤ D₂')
  (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂')
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂' × D₂ ⥤ D₂')
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ (A : D₂') (B C : D₂), (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ Λ.obj C))
  (m : T₁ ⋙ P ⋙ Λ ≅ (P ⋙ Λ).prod P ⋙ T₂)
  (U : D₁) (r₁ : ∀ Z : D₁, T₁.obj (Z, U) ≅ Z) (r₂ : ∀ Z : D₂', T₂.obj (Z, P.obj U) ≅ Z)

/-- **The dévissage of Stacks 08JP, case (2), with the natural transformation supplied**, by
`MixedTranspose.homComparisonNatTrans`, and with the shift data of the two sides reduced to the
shift data of their factors.

Compared with `MixedTranspose.isIso_homComparison_of_generatedByOp`:

* the hypotheses `η` and `hη` are gone. The transformation is *constructed*, from the two clauses
  of Stacks 08J8 for each of the two bijections, and the identification of its components with
  the comparison is `rfl`;
* the four shift data of the two comparison functors are gone. They are discharged by
  `MixedTranspose.commShift_comparisonSourceFunctor` and its three companions from the
  corresponding data for `P`, for `Λ` and for the two *contravariant internal homs*, which is
  what is asked for instead.

So what the statement still carries about the shift is: the commutation and triangulatedness of
`P`, of `Λ`, of `H₁(-, F)` and of `H₂(-, P F)`, and the shift compatibility `ShiftCompatible` of
the comparison. None of these asserts that any instance of the comparison is invertible; the only
invertibility fed into the dévissage is the unit case, and that is proved. -/
theorem isIso_homComparison_of_generatedByOp_natTrans
    (hP : P.CommShift ℤ) (hΛ : Λ.CommShift ℤ)
    (hPt : letI := hP; P.IsTriangulated) (hΛt : letI := hΛ; Λ.IsTriangulated)
    (hnat₁ : Transpose.TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hdin₁ : Transpose.TensorHomEquivDinatural H₁ T₁ e₁)
    (hr₁ : RightUnitorNatural T₁ U r₁)
    (hnat₂ : MixedTensorHomEquivNatural Λ H₂ T₂ e₂)
    (hdin₂ : MixedTensorHomEquivDinatural Λ H₂ T₂ e₂)
    (hr₂ : MixedRightUnitorNatural P T₂ U r₂)
    (hm : MonoidalityUnital P Λ T₁ T₂ m U r₁ r₂)
    (F : D₁)
    (hH₁ : (H₁.flip.obj F).CommShift ℤ)
    (hH₁t : letI := hH₁; (H₁.flip.obj F).IsTriangulated)
    (hH₂ : (H₂.flip.obj (P.obj F)).CommShift ℤ)
    (hH₂t : letI := hH₂; (H₂.flip.obj (P.obj F)).IsTriangulated)
    (hsh : ShiftCompatible P Λ H₁ H₂ T₁ T₂ e₁ e₂ m hP hΛ hnat₁ hdin₁ hnat₂ hdin₂ F hH₁ hH₂)
    (E : D₁) (hE : GeneratedByOp U E) :
    IsIso (homComparison P Λ H₁ H₂ T₁ T₂ e₁ e₂ m E F) := by
  let := hP
  let := hΛ
  let := hH₁
  let := hH₂
  let := hPt
  let := hΛt
  let := hH₁t
  let := hH₂t
  let : NatTrans.CommShift
      (homComparisonNatTrans P Λ H₁ H₂ T₁ T₂ e₁ e₂ m hnat₁ hdin₁ hnat₂ hdin₂ F) ℤ := hsh
  exact isIso_homComparison_of_generatedByOp P Λ H₁ H₂ T₁ T₂ e₁ e₂ m U r₁ r₂
    (tensorHomEquivNatural_of_naturalLeft hnat₁) hr₁ hnat₂ hr₂ hm F
    (homComparisonNatTrans P Λ H₁ H₂ T₁ T₂ e₁ e₂ m hnat₁ hdin₁ hnat₂ hdin₂ F)
    (homComparisonNatTrans_app P Λ H₁ H₂ T₁ T₂ e₁ e₂ m hnat₁ hdin₁ hnat₂ hdin₂ F) E hE

end Generated

end Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose

end
