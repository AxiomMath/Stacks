module

public import StacksFrontier.CategoryTheory.KanExtension.FilteredColimit
public import StacksCore.Tactic.StacksAttribute

/-! # Extending a functor from a subcategory of categorically compact objects

Stacks 0FWY: let `C` and `D` be big categories having filtered colimits and let `C' ⊆ C` be a
small full subcategory of categorically compact objects of `C` such that every object of `C`
is a filtered colimit of objects of `C'`. Then every functor `F' : C' ⥤ D` has a unique
extension `F : C ⥤ D` commuting with filtered colimits.

`C'` is presented as an object property `P : ObjectProperty C` whose full subcategory is
essentially `w`-small; "categorically compact" is Stacks 0FWX, i.e. Mathlib's
`IsFinitelyPresentable`; and "every object is a filtered colimit of objects of `C'`" is
Mathlib's `ObjectProperty.ind`.

Uniqueness is read as uniqueness up to a *unique* natural isomorphism compatible with the
identifications of the restrictions with `F'`: the source only pins the values of `F` down as
`colim F'(Xᵢ)` for a chosen presentation `X = colim Xᵢ`, and shows that two presentations give
canonically isomorphic values, so no stronger reading is available. This is exactly the
universal property of the left Kan extension along the inclusion, which
`existsUnique_natTrans_of_preservesFilteredColimits` records.
-/

@[expose] public section

open CategoryTheory Category Limits ObjectProperty

universe w v v' u u'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (P : ObjectProperty C)

/-- Two functors out of `C` that commute with `w`-filtered colimits admit exactly one natural
transformation between them inducing a prescribed natural transformation on the subcategory of
`P`-objects. -/
theorem existsUnique_natTrans_of_preservesFilteredColimits
    [LocallySmall.{w} P.FullSubcategory]
    (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)
    (F₁ F₂ : C ⥤ D) [PreservesFilteredColimitsOfSize.{w, w} F₁]
    (β : P.ι ⋙ F₁ ⟶ P.ι ⋙ F₂) :
    ∃! φ : F₁ ⟶ F₂, Functor.whiskerLeft P.ι φ = β := by
  have h₁ : Functor.IsLeftKanExtension F₁ (𝟙 (P.ι ⋙ F₁)) :=
    isLeftKanExtension_of_preservesFilteredColimits P hP hgen F₁
  have hfac : Functor.whiskerLeft P.ι (F₁.descOfIsLeftKanExtension (𝟙 (P.ι ⋙ F₁)) F₂ β) = β := by
    simpa using F₁.descOfIsLeftKanExtension_fac (𝟙 (P.ι ⋙ F₁)) F₂ β
  refine ⟨_, hfac, fun ψ hψ ↦ ?_⟩
  refine F₁.hom_ext_of_isLeftKanExtension (𝟙 (P.ι ⋙ F₁)) _ _ ?_
  rw [id_comp, id_comp, hψ, hfac]

/-- **Stacks 0FWY** (existence).
Let `C` and `D` have `w`-filtered colimits, let `P` be a property of objects of `C` cutting out
an essentially `w`-small full subcategory of categorically compact objects (Stacks 0FWX), and
assume every object of `C` is a `w`-filtered colimit of objects satisfying `P`. Then every
functor `F'` out of that subcategory extends to a functor `C ⥤ D` commuting with filtered
colimits. -/
@[stacks 0FWY, sga "4 I 8.7.2" "existence of f̄", sga "4 I 8.7.3" "ess. surj. of (8.7.3.1)"]
theorem exists_extension_of_preservesFilteredColimits
    [HasFilteredColimitsOfSize.{w, w} C] [HasFilteredColimitsOfSize.{w, w} D]
    [EssentiallySmall.{w} P.FullSubcategory]
    (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)
    (F' : P.FullSubcategory ⥤ D) :
    ∃ F : C ⥤ D, PreservesFilteredColimitsOfSize.{w, w} F ∧ Nonempty (P.ι ⋙ F ≅ F') := by
  have hpt : P.ι.HasPointwiseLeftKanExtension F' :=
    hasPointwiseLeftKanExtension_ι P hP hgen F'
  have hEx := Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension P.ι F'
  refine ⟨P.ι.pointwiseLeftKanExtension F', ?_, ?_⟩
  · exact preservesFilteredColimitsOfSize_right P hP
      (Functor.LeftExtension.mk _ (Functor.pointwiseLeftKanExtensionUnit P.ι F')) hEx
  · have : IsIso (Functor.pointwiseLeftKanExtensionUnit P.ι F') := hEx.isIso_hom
    exact ⟨(asIso (Functor.pointwiseLeftKanExtensionUnit P.ι F')).symm⟩

/-- **Stacks 0FWY** (uniqueness).
Under the hypotheses of `exists_extension_of_preservesFilteredColimits`, an extension of `F'`
commuting with filtered colimits is unique up to a unique natural isomorphism compatible with
the identifications of the restrictions with `F'`. -/
@[stacks 0FWY, sga "4 I 8.7.2" "uniqueness of f̄", sga "4 I 8.7.3" "uniqueness of extension"]
theorem existsUnique_iso_of_preservesFilteredColimits
    [HasFilteredColimitsOfSize.{w, w} C] [EssentiallySmall.{w} P.FullSubcategory]
    (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)
    {F' : P.FullSubcategory ⥤ D} (F₁ F₂ : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} F₁] [PreservesFilteredColimitsOfSize.{w, w} F₂]
    (e₁ : P.ι ⋙ F₁ ≅ F') (e₂ : P.ι ⋙ F₂ ≅ F') :
    ∃! φ : F₁ ≅ F₂, Functor.whiskerLeft P.ι φ.hom = (e₁ ≪≫ e₂.symm).hom := by
  obtain ⟨u, hu, hu'⟩ :=
    existsUnique_natTrans_of_preservesFilteredColimits P hP hgen F₁ F₂ (e₁ ≪≫ e₂.symm).hom
  obtain ⟨v, hv, -⟩ :=
    existsUnique_natTrans_of_preservesFilteredColimits P hP hgen F₂ F₁ (e₂ ≪≫ e₁.symm).hom
  have huv : u ≫ v = 𝟙 F₁ :=
    (existsUnique_natTrans_of_preservesFilteredColimits P hP hgen F₁ F₁ (𝟙 _)).unique
      (by rw [Functor.whiskerLeft_comp, hu, hv]; ext; simp) rfl
  have hvu : v ≫ u = 𝟙 F₂ :=
    (existsUnique_natTrans_of_preservesFilteredColimits P hP hgen F₂ F₂ (𝟙 _)).unique
      (by rw [Functor.whiskerLeft_comp, hv, hu]; ext; simp) rfl
  exact ⟨⟨u, v, huv, hvu⟩, hu, fun ψ hψ ↦ Iso.ext (hu' ψ.hom hψ)⟩

/-- In a finitely accessible category every object is a filtered colimit of finitely
presentable, i.e. categorically compact, objects. -/
theorem ind_isFinitelyPresentable [IsFinitelyAccessibleCategory.{w} C] (X : C) :
    (isFinitelyPresentable.{w} C).ind.{w} X := by
  rw [ObjectProperty.ind_iff_exists le_rfl]
  intro Z g hZ
  exact ⟨Z, 𝟙 Z, g, by simp, hZ⟩

/-- Stacks 0FWY for the categorically compact objects of a finitely accessible category with
filtered colimits: the hypotheses of `exists_extension_of_preservesFilteredColimits` are all
met by `P = isFinitelyPresentable C`, so every functor out of the full subcategory of
categorically compact objects extends to one commuting with filtered colimits. -/
theorem exists_extension_isFinitelyPresentable [IsFinitelyAccessibleCategory.{w} C]
    [HasFilteredColimitsOfSize.{w, w} C] [HasFilteredColimitsOfSize.{w, w} D]
    (F' : (isFinitelyPresentable.{w} C).FullSubcategory ⥤ D) :
    ∃ F : C ⥤ D, PreservesFilteredColimitsOfSize.{w, w} F ∧
      Nonempty ((isFinitelyPresentable.{w} C).ι ⋙ F ≅ F') :=
  exists_extension_of_preservesFilteredColimits _ le_rfl ind_isFinitelyPresentable F'

end CategoryTheory.ObjectProperty
