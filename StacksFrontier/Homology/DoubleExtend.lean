module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# A complex concentrated in two adjacent degrees, read in two complex shapes

A two-term complex `f : X₀ ⟶ X₁` can be presented as `HomologicalComplex.double f hi₀₁` for any
complex shape `c` and any pair of indices with `c.Rel i₀ i₁`; for instance the chain presentation
`HomologicalComplex.double f (show (ComplexShape.down ℕ).Rel 1 0 from rfl)` and the cochain
presentation `HomologicalComplex.double f (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)`.

The two presentations are not equal and not even objects of the same category, so a
quasi-isomorphism proved for one says nothing about the other until they are related.  This file
relates them, for an arbitrary `ComplexShape.Embedding`: `doubleExtendIso` identifies the
`c'`-presentation with Mathlib's `HomologicalComplex.extend` of the `c`-presentation, and
`quasiIso_double_of_quasiIso_double` transports a quasi-isomorphism of `c`-presentations to the
`c'`-presentations, given only that the two morphisms have the same two components.

## Main definitions

* `HomologicalComplex.doubleExtendIso`: `double f (e.rel hi₀₁) ≅ (double f hi₀₁).extend e`.

## Main results

* `HomologicalComplex.quasiIso_double_of_quasiIso_double`: a morphism of two-term complexes in the
  shape `c'` is a quasi-isomorphism as soon as the morphism with the same components in the shape
  `c` is one.

## Implementation notes

`doubleExtendIso` is built as a morphism out of the `c'`-presentation by Mathlib's
`mkHomFromDouble` and then shown to be an isomorphism degreewise.  Only two degrees carry
content: at `e.f i₀` and `e.f i₁` the component is a composite of the canonical identifications
`doubleXIso₀`, `doubleXIso₁` and `extendXIso`, and in every other degree both the source and the
target are zero, so the component is an isomorphism for want of anything else to be.  The
degreewise case distinction is the one forced by `extend`: an index of `c'` either is `e.f i` for
a (then unique, by `ComplexShape.Embedding.injective_f`) index `i` of `c`, in which case the
`extend` is `double f hi₀₁` at `i`, or it is outside the image, in which case the `extend` is zero
by `isZero_extend_X`.

`quasiIso_double_of_quasiIso_double` needs no homology argument of its own: with
`doubleExtendIso` in hand, the morphism of `c'`-presentations is conjugate to
`HomologicalComplex.extendMap` of the morphism of `c`-presentations — which is checked on the two
degrees alone, by `from_double_hom_ext` — and Mathlib's `quasiIso_extendMap_iff` already says
that `extendMap` neither creates nor destroys quasi-isomorphisms.  The hypotheses are stated as
equations between the components read through `doubleXIso₀` and `doubleXIso₁` rather than as a
`double`-valued morphism built from a commuting square, so that the lemma applies to a morphism
however it was constructed.
-/

@[expose] public section

open CategoryTheory Category Limits

/-- The degrees `1` and `0` are adjacent in the homological complex shape
`ComplexShape.down ℕ`. -/
public theorem ComplexShape.downNatRelOneZero : (ComplexShape.down ℕ).Rel 1 0 := rfl

/-- The degrees `-1` and `0` are adjacent in the cohomological complex shape
`ComplexShape.up ℤ`. -/
public theorem ComplexShape.upIntRelNegOneZero : (ComplexShape.up ℤ).Rel (-1) 0 := rfl

namespace HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {X₀ X₁ Y₀ Y₁ : C} (f : X₀ ⟶ X₁) {g : Y₀ ⟶ Y₁}
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)

/-- The indices `e.f i₀` and `e.f i₁` of the ambient shape are distinct, because an embedding of
complex shapes is injective on indices. -/
public theorem _root_.ComplexShape.Embedding.ne_f (hne : i₀ ≠ i₁) : e.f i₀ ≠ e.f i₁ :=
  fun he ↦ hne (e.injective_f he)

/-- The comparison morphism from the two-term complex in the shape `c'` to the extension along
`e` of the two-term complex in the shape `c`. It is the identity on both nonzero terms, read
through the canonical identifications. -/
public noncomputable def doubleExtendHom :
    double f (e.rel hi₀₁) ⟶ (double f hi₀₁).extend e :=
  mkHomFromDouble (e.rel hi₀₁) (e.ne_f hne)
    ((doubleXIso₀ f hi₀₁).inv ≫ ((double f hi₀₁).extendXIso e (i := i₀) rfl).inv)
    ((doubleXIso₁ f hi₀₁ hne).inv ≫ ((double f hi₀₁).extendXIso e (i := i₁) rfl).inv)
    (by
      rw [extend_d_eq (double f hi₀₁) e (i := i₀) (j := i₁) rfl rfl,
        double_d f hi₀₁ hne]
      simp)
    (fun k hk ↦ by
      by_cases hex : ∃ i, e.f i = k
      · obtain ⟨i, rfl⟩ := hex
        rw [extend_d_eq (double f hi₀₁) e (i := i₁) (j := i) rfl rfl,
          double_d_eq_zero₀ f hi₀₁ i₁ i hne.symm]
        simp
      · exact ((double f hi₀₁).isZero_extend_X e k
          (fun i hi ↦ hex ⟨i, hi⟩)).eq_of_tgt _ _)

/-- The component of `doubleExtendHom` in degree `e.f i₀` is the composite of the canonical
identifications of `X₀` with the terms in that degree. -/
@[simp]
public theorem doubleExtendHom_f₀ :
    (doubleExtendHom f e hi₀₁ hne).f (e.f i₀) =
      (doubleXIso₀ f (e.rel hi₀₁)).hom ≫ (doubleXIso₀ f hi₀₁).inv ≫
        ((double f hi₀₁).extendXIso e (i := i₀) rfl).inv :=
  mkHomFromDouble_f₀ _ _ _ _ _ _

/-- The component of `doubleExtendHom` in degree `e.f i₁` is the composite of the canonical
identifications of `X₁` with the terms in that degree. -/
@[simp]
public theorem doubleExtendHom_f₁ :
    (doubleExtendHom f e hi₀₁ hne).f (e.f i₁) =
      (doubleXIso₁ f (e.rel hi₀₁) (e.ne_f hne)).hom ≫ (doubleXIso₁ f hi₀₁ hne).inv ≫
        ((double f hi₀₁).extendXIso e (i := i₁) rfl).inv :=
  mkHomFromDouble_f₁ _ _ _ _ _ _

/-- Every component of `doubleExtendHom` is an isomorphism: in the two degrees `e.f i₀` and
`e.f i₁` it is a composite of canonical identifications, and in every other degree both its
source and its target are zero. -/
public theorem isIso_doubleExtendHom_f (j : ι') :
    IsIso ((doubleExtendHom f e hi₀₁ hne).f j) := by
  by_cases h₀ : j = e.f i₀
  · subst h₀; rw [doubleExtendHom_f₀]; infer_instance
  by_cases h₁ : j = e.f i₁
  · subst h₁; rw [doubleExtendHom_f₁]; infer_instance
  have hsrc : IsZero ((double f (e.rel hi₀₁)).X j) := isZero_double_X _ _ j h₀ h₁
  have htgt : IsZero (((double f hi₀₁).extend e).X j) := by
    by_cases hex : ∃ i, e.f i = j
    · obtain ⟨i, rfl⟩ := hex
      exact (isZero_double_X f hi₀₁ i (fun hi ↦ h₀ (congrArg e.f hi))
        (fun hi ↦ h₁ (congrArg e.f hi))).of_iso ((double f hi₀₁).extendXIso e rfl)
    · exact (double f hi₀₁).isZero_extend_X e j (fun i hi ↦ hex ⟨i, hi⟩)
  rw [hsrc.eq_of_src ((doubleExtendHom f e hi₀₁ hne).f j) (hsrc.iso htgt).hom]
  infer_instance

/-- **The two-term complex in the shape `c'` is the extension along `e` of the two-term complex
in the shape `c`.** The same map `f : X₀ ⟶ X₁` presented in degrees `e.f i₀`, `e.f i₁` of the
ambient shape, and presented in degrees `i₀`, `i₁` of `c` and then extended, agree. -/
public noncomputable def doubleExtendIso :
    double f (e.rel hi₀₁) ≅ (double f hi₀₁).extend e :=
  haveI : ∀ j, IsIso ((doubleExtendHom f e hi₀₁ hne).f j) := isIso_doubleExtendHom_f f e hi₀₁ hne
  haveI := Hom.isIso_of_components (doubleExtendHom f e hi₀₁ hne)
  asIso (doubleExtendHom f e hi₀₁ hne)

section Self

variable (D : HomologicalComplex C c)
  (hout : ∀ j, c.Rel i₁ j → D.d i₁ j = 0)
  (hsupport : ∀ j, j ≠ i₀ → j ≠ i₁ → IsZero (D.X j))

/-- The comparison from the two-term complex of a complex's own differential to the complex
itself. It is the identity on both nonzero terms. -/
public noncomputable def doubleSelfHom : double (D.d i₀ i₁) hi₀₁ ⟶ D :=
  mkHomFromDouble hi₀₁ hne (𝟙 _) (𝟙 _) (by simp) (fun k hk ↦ by simp [hout k hk])

/-- The component of `doubleSelfHom` in degree `i₀` is the canonical identification
`doubleXIso₀`. -/
@[simp]
public theorem doubleSelfHom_f₀ :
    (doubleSelfHom hi₀₁ hne D hout).f i₀ = (doubleXIso₀ (D.d i₀ i₁) hi₀₁).hom := by
  rw [doubleSelfHom, mkHomFromDouble_f₀, Category.comp_id]

/-- The component of `doubleSelfHom` in degree `i₁` is the canonical identification
`doubleXIso₁`. -/
@[simp]
public theorem doubleSelfHom_f₁ :
    (doubleSelfHom hi₀₁ hne D hout).f i₁ = (doubleXIso₁ (D.d i₀ i₁) hi₀₁ hne).hom := by
  rw [doubleSelfHom, mkHomFromDouble_f₁, Category.comp_id]

/-- **A complex concentrated in two adjacent degrees is the two-term complex of its own
differential.** -/
public noncomputable def doubleSelfIso : double (D.d i₀ i₁) hi₀₁ ≅ D :=
  haveI : ∀ j, IsIso ((doubleSelfHom hi₀₁ hne D hout).f j) := by
    intro j
    by_cases h₀ : j = i₀
    · subst h₀; rw [doubleSelfHom_f₀]; infer_instance
    by_cases h₁ : j = i₁
    · subst h₁; rw [doubleSelfHom_f₁]; infer_instance
    have hsrc : IsZero ((double (D.d i₀ i₁) hi₀₁).X j) := isZero_double_X _ _ j h₀ h₁
    rw [hsrc.eq_of_src ((doubleSelfHom hi₀₁ hne D hout).f j) (hsrc.iso (hsupport j h₀ h₁)).hom]
    infer_instance
  haveI := Hom.isIso_of_components (doubleSelfHom hi₀₁ hne D hout)
  asIso (doubleSelfHom hi₀₁ hne D hout)

/-- The forward morphism of `doubleSelfIso` is `doubleSelfHom`. -/
@[simp]
public theorem doubleSelfIso_hom :
    (doubleSelfIso hi₀₁ hne D hout hsupport).hom = doubleSelfHom hi₀₁ hne D hout := rfl

end Self

/-- **A quasi-isomorphism of two-term complexes is one in every complex shape.** Let `φ` compare
the two-term complexes of `f` and `g` placed in degrees `i₀`, `i₁` of `c`, and let `ψ` compare
the same two-term complexes placed in degrees `e.f i₀`, `e.f i₁` of the ambient shape `c'`. If
the two morphisms have the same pair of components, read through the canonical identifications of
the nonzero terms, then `ψ` is a quasi-isomorphism as soon as `φ` is. -/
public theorem quasiIso_double_of_quasiIso_double [CategoryWithHomology C]
    (φ : double f hi₀₁ ⟶ double g hi₀₁)
    (ψ : double f (e.rel hi₀₁) ⟶ double g (e.rel hi₀₁))
    (h₀ : (doubleXIso₀ f (e.rel hi₀₁)).inv ≫ ψ.f (e.f i₀) ≫ (doubleXIso₀ g (e.rel hi₀₁)).hom =
      (doubleXIso₀ f hi₀₁).inv ≫ φ.f i₀ ≫ (doubleXIso₀ g hi₀₁).hom)
    (h₁ : (doubleXIso₁ f (e.rel hi₀₁) (e.ne_f hne)).inv ≫ ψ.f (e.f i₁) ≫
        (doubleXIso₁ g (e.rel hi₀₁) (e.ne_f hne)).hom =
      (doubleXIso₁ f hi₀₁ hne).inv ≫ φ.f i₁ ≫ (doubleXIso₁ g hi₀₁ hne).hom)
    [QuasiIso φ] : QuasiIso ψ := by
  have hsq : ψ ≫ (doubleExtendIso g e hi₀₁ hne).hom =
      (doubleExtendIso f e hi₀₁ hne).hom ≫ extendMap φ e := by
    apply from_double_hom_ext (f := f) (hi₀₁ := e.rel hi₀₁)
    · rw [comp_f, comp_f, extendMap_f φ e (i := i₀) rfl]
      change ψ.f (e.f i₀) ≫ (doubleExtendHom g e hi₀₁ hne).f (e.f i₀) =
        (doubleExtendHom f e hi₀₁ hne).f (e.f i₀) ≫ _
      rw [doubleExtendHom_f₀, doubleExtendHom_f₀]
      rw [← cancel_epi (doubleXIso₀ f (e.rel hi₀₁)).inv]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      slice_lhs 1 3 => rw [h₀]
      simp
    · rw [comp_f, comp_f, extendMap_f φ e (i := i₁) rfl]
      change ψ.f (e.f i₁) ≫ (doubleExtendHom g e hi₀₁ hne).f (e.f i₁) =
        (doubleExtendHom f e hi₀₁ hne).f (e.f i₁) ≫ _
      rw [doubleExtendHom_f₁, doubleExtendHom_f₁]
      rw [← cancel_epi (doubleXIso₁ f (e.rel hi₀₁) (e.ne_f hne)).inv]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      slice_lhs 1 3 => rw [h₁]
      simp
  have hψ : ψ = (doubleExtendIso f e hi₀₁ hne).hom ≫ extendMap φ e ≫
      (doubleExtendIso g e hi₀₁ hne).inv := by
    rw [← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : QuasiIso (extendMap φ e) := (quasiIso_extendMap_iff φ e).mpr inferInstance
  rw [hψ]
  infer_instance

end HomologicalComplex

end
