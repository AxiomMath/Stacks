module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import StacksFrontier.CategoryTheory.Functor.Derived.OrthogonalResolutions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived functors obtained from resolutions are absolute

Let `L : C ⥤ D` be a localization functor for a class of morphisms `W`, and suppose that `W`
admits *resolutions by objects at which `L` is fully faithful*: every `X : C` receives a morphism
`s : P ⟶ X` of `W` such that `L` is bijective on the morphisms out of `P`. In the triangulated
situation this is `CategoryTheory.ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated`
applied to a resolving left orthogonal, as in
`StacksFrontier/CategoryTheory/Functor/Derived/OrthogonalResolutions.lean`.

Under that hypothesis the left derived functor of *every* functor out of `C` exists, and this
file proves the stronger statement that such a derived functor is **absolute**: if `LF` is the
left derived functor of `F` with comparison `α`, then for every further functor `G` the composite
`LF ⋙ G` is the left derived functor of `F ⋙ G`, with the whiskered comparison. The dual
statement holds for right derived functors out of resolutions on the other side.

Absoluteness is exactly the extra hypothesis of Mathlib's `CategoryTheory.Adjunction.derived`,
which produces an adjunction between derived functors from an adjunction between the functors
being derived. So the two main results below are what turn an adjunction on `C` into an
adjunction between the derived functors, which is Stacks Tag 0FND.

## Main results

* `CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_resolutions` and
  `CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_of_resolutions`: the resolution
  hypothesis produces the pointwise left, resp. right, derived functor of an arbitrary functor.
* `CategoryTheory.Functor.RightExtension.isIso_hom_app_of_bijective` and
  `CategoryTheory.Functor.LeftExtension.isIso_hom_app_of_bijective`: the comparison map of a
  derived functor is invertible at an object at which the localization functor is fully faithful.
* `CategoryTheory.Functor.isIso_of_isIso_app_of_resolutions` and its dual
  `CategoryTheory.Functor.isIso_of_isIso_app_of_coresolutions`: a natural transformation between
  functors on `D` is invertible as soon as it is invertible at the resolving objects.
* `CategoryTheory.Functor.isLeftDerivedFunctor_comp_of_resolutions`: a left derived functor
  obtained from resolutions is absolute.
* `CategoryTheory.Functor.isRightDerivedFunctor_comp_of_coresolutions`: the dual.

## Implementation notes

*Why the hypothesis is bijectivity of `L` on morphisms rather than an orthogonality.* Nothing in
the argument uses a triangulated structure: what a resolving object `P` contributes is that the
index category `StructuredArrow (L.obj P) L` computing the pointwise Kan extension at `L.obj P`
has `𝟙 (L.obj P)` as an initial object, and that is precisely bijectivity of `L` on the morphisms
out of `P`. Stating it that way keeps the file free of any hypothesis on `C` and lets the
triangulated input be supplied by the caller.

*Why absoluteness does not follow from existence alone.* The resolution hypothesis gives that
`F ⋙ G` *has* a left derived functor, but `CategoryTheory.Adjunction.derived` needs the
particular candidate `LF ⋙ G`, with the particular whiskered comparison, to *be* one. The two
are compared by `CategoryTheory.Functor.leftDerivedLift`, and that comparison is checked to be
invertible objectwise: at `L.obj P` for a resolving `P` both comparison maps are invertible by
`CategoryTheory.Functor.RightExtension.isIso_hom_app_of_bijective`, and every object of `D` is
isomorphic to such an `L.obj P` because `L` is essentially surjective and inverts the resolving
morphisms.

## References

* [Stacks Project, Tag 0FND](https://stacks.math.columbia.edu/tag/0FND), the derived adjunction;
  the criterion producing the derived functors is
  [Tag 06XN](https://stacks.math.columbia.edu/tag/06XN).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H] {H' : Type u₄} [Category.{v₄} H']

/-! ### The comparison map of a derived functor at a resolving object -/

/-- The comparison map of a right extension along `L` is invertible at `P` as soon as the
extension is a pointwise right Kan extension at `L.obj P` and `L` is bijective on the morphisms
out of `P`.

This is `CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt.isIso_hom_app`
with full faithfulness of `L` weakened to full faithfulness at the single object `P`, which is
what a resolving object supplies. -/
@[sga "4 I 5.7" "more general"]
theorem RightExtension.isIso_hom_app_of_bijective {L : C ⥤ D} {F : C ⥤ H}
    (E : L.RightExtension F) {P : C}
    (h : E.IsPointwiseRightKanExtensionAt (L.obj P))
    (hb : ∀ Y : C, Function.Bijective (L.map : (P ⟶ Y) → (L.obj P ⟶ L.obj Y))) :
    IsIso (E.hom.app P) := by
  have h' := h.isIso_π_app_of_isInitial _ (structuredArrowMkIdIsInitial L P hb)
  simpa using h'

/-- Dually to `CategoryTheory.Functor.RightExtension.isIso_hom_app_of_bijective`: the comparison
map of a left extension along `L` is invertible at `I` as soon as the extension is a pointwise
left Kan extension at `L.obj I` and `L` is bijective on the morphisms into `I`. -/
theorem LeftExtension.isIso_hom_app_of_bijective {L : C ⥤ D} {F : C ⥤ H}
    (E : L.LeftExtension F) {I : C}
    (h : E.IsPointwiseLeftKanExtensionAt (L.obj I))
    (hb : ∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I))) :
    IsIso (E.hom.app I) := by
  have h' := h.isIso_ι_app_of_isTerminal _ (costructuredArrowMkIdIsTerminal L I hb)
  simpa using h'

/-! ### Recognising an isomorphism on the resolving objects -/

section

variable {L : C ⥤ D} (W : MorphismProperty C) [L.IsLocalization W]

/-- A natural transformation between two functors on the localization `D` is invertible as soon
as it is invertible at `L.obj P` for every object `P` that resolves some object of `C`: every
object of `D` is isomorphic to such an `L.obj P`, because `L` is essentially surjective and
inverts the resolving morphism. -/
theorem isIso_of_isIso_app_of_resolutions {E₁ E₂ : D ⥤ H'} (γ : E₁ ⟶ E₂)
    (hres : ∀ X : C, ∃ (P : C) (s : P ⟶ X), W s ∧
      ∀ Y : C, Function.Bijective (L.map : (P ⟶ Y) → (L.obj P ⟶ L.obj Y)))
    (h : ∀ P : C, (∀ Y : C, Function.Bijective (L.map : (P ⟶ Y) → (L.obj P ⟶ L.obj Y))) →
      IsIso (γ.app (L.obj P))) :
    IsIso γ := by
  have := Localization.essSurj L W
  have happ : ∀ Y : D, IsIso (γ.app Y) := by
    intro Y
    obtain ⟨P, s, hs, hb⟩ := hres (L.objPreimage Y)
    have : IsIso (L.map s) := Localization.inverts L W s hs
    have := h P hb
    let e : L.obj P ≅ Y := asIso (L.map s) ≪≫ L.objObjPreimageIso Y
    have : IsIso (E₁.map e.hom ≫ γ.app Y) := by
      rw [γ.naturality e.hom]; infer_instance
    exact IsIso.of_isIso_comp_left (E₁.map e.hom) (γ.app Y)
  exact NatIso.isIso_of_isIso_app γ

/-- Dually to `CategoryTheory.Functor.isIso_of_isIso_app_of_resolutions`, with the resolving
morphisms going the other way. -/
theorem isIso_of_isIso_app_of_coresolutions {E₁ E₂ : D ⥤ H'} (γ : E₁ ⟶ E₂)
    (hres : ∀ X : C, ∃ (I : C) (s : X ⟶ I), W s ∧
      ∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I)))
    (h : ∀ I : C, (∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I))) →
      IsIso (γ.app (L.obj I))) :
    IsIso γ := by
  have := Localization.essSurj L W
  have happ : ∀ Y : D, IsIso (γ.app Y) := by
    intro Y
    obtain ⟨I, s, hs, hb⟩ := hres (L.objPreimage Y)
    have : IsIso (L.map s) := Localization.inverts L W s hs
    have := h I hb
    let e : Y ≅ L.obj I := (L.objObjPreimageIso Y).symm ≪≫ asIso (L.map s)
    have : IsIso (γ.app Y ≫ E₂.map e.hom) := by
      rw [← γ.naturality e.hom]; infer_instance
    exact IsIso.of_isIso_comp_right (γ.app Y) (E₂.map e.hom)
  exact NatIso.isIso_of_isIso_app γ

end

/-! ### Derived functors from resolutions, and their absoluteness -/

section Left

variable {L : C ⥤ D} (W : MorphismProperty C) [L.IsLocalization W]

/-- If every object of `C` receives a morphism of `W` from an object at which `L` is fully
faithful, then every functor out of `C` has a pointwise left derived functor with respect
to `W`. -/
theorem hasPointwiseLeftDerivedFunctor_of_resolutions (F : C ⥤ H)
    (hres : ∀ X : C, ∃ (P : C) (s : P ⟶ X), W s ∧
      ∀ Y : C, Function.Bijective (L.map : (P ⟶ Y) → (L.obj P ⟶ L.obj Y))) :
    F.HasPointwiseLeftDerivedFunctor W := by
  intro X
  obtain ⟨P, s, hs, hb⟩ := hres X
  rw [← F.hasPointwiseLeftDerivedFunctorAt_iff_of_mem W s hs,
    F.hasPointwiseLeftDerivedFunctorAt_iff L W P]
  exact hasPointwiseRightKanExtensionAt_of_bijective L F P hb

/-- The comparison map of a left derived functor is invertible at a resolving object. -/
private theorem isIso_app_of_isLeftDerivedFunctor {F : C ⥤ H} {LF : D ⥤ H} (α : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor α W] [F.HasPointwiseLeftDerivedFunctor W] {P : C}
    (hb : ∀ Y : C, Function.Bijective (L.map : (P ⟶ Y) → (L.obj P ⟶ L.obj Y))) :
    IsIso (α.app P) :=
  (RightExtension.mk LF α).isIso_hom_app_of_bijective
    (isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LF α W (L.obj P)) hb

/-- **Absoluteness of a left derived functor obtained from resolutions.** If every object of `C`
receives a morphism of `W` from an object at which `L` is fully faithful, and `LF` is the left
derived functor of `F` with comparison `α`, then for every functor `G` the composite `LF ⋙ G` is
the left derived functor of `F ⋙ G`, with the whiskered comparison.

This is the hypothesis `CategoryTheory.Adjunction.derived` asks of the left adjoint's derived
functor. -/
theorem isLeftDerivedFunctor_comp_of_resolutions {F : C ⥤ H} {LF : D ⥤ H}
    (α : L ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α W] (G : H ⥤ H')
    (hres : ∀ X : C, ∃ (P : C) (s : P ⟶ X), W s ∧
      ∀ Y : C, Function.Bijective (L.map : (P ⟶ Y) → (L.obj P ⟶ L.obj Y))) :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G) W := by
  have := hasPointwiseLeftDerivedFunctor_of_resolutions W F hres
  have := hasPointwiseLeftDerivedFunctor_of_resolutions W (F ⋙ G) hres
  have := (F ⋙ G).hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor W
  rw [((F ⋙ G).totalLeftDerived L W).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
    ((F ⋙ G).totalLeftDerivedCounit L W) W (LF ⋙ G)
    ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G)]
  refine isIso_of_isIso_app_of_resolutions W _ hres fun P hb => ?_
  have := isIso_app_of_isLeftDerivedFunctor W α hb
  have := isIso_app_of_isLeftDerivedFunctor W ((F ⋙ G).totalLeftDerivedCounit L W) hb
  have : IsIso ((((F ⋙ G).totalLeftDerived L W).leftDerivedLift
      ((F ⋙ G).totalLeftDerivedCounit L W) W (LF ⋙ G)
      ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G)).app (L.obj P) ≫
      ((F ⋙ G).totalLeftDerivedCounit L W).app P) := by
    rw [((F ⋙ G).totalLeftDerived L W).leftDerived_fac_app
      ((F ⋙ G).totalLeftDerivedCounit L W) W (LF ⋙ G)
      ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G) P]
    have h : ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G).app P
        = G.map (α.app P) := by simp
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (((F ⋙ G).totalLeftDerivedCounit L W).app P)

end Left

section Right

variable {L : C ⥤ D} (W : MorphismProperty C) [L.IsLocalization W]

/-- If every object of `C` admits a morphism of `W` into an object at which `L` is fully
faithful, then every functor out of `C` has a pointwise right derived functor with respect
to `W`. -/
theorem hasPointwiseRightDerivedFunctor_of_coresolutions (F : C ⥤ H)
    (hres : ∀ X : C, ∃ (I : C) (s : X ⟶ I), W s ∧
      ∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I))) :
    F.HasPointwiseRightDerivedFunctor W := by
  intro X
  obtain ⟨I, s, hs, hb⟩ := hres X
  rw [F.hasPointwiseRightDerivedFunctorAt_iff_of_mem W s hs,
    F.hasPointwiseRightDerivedFunctorAt_iff L W I]
  exact hasPointwiseLeftKanExtensionAt_of_bijective L F I hb

/-- The comparison map of a right derived functor is invertible at a resolving object. -/
private theorem isIso_app_of_isRightDerivedFunctor {F : C ⥤ H} {RF : D ⥤ H} (β : F ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor β W] [F.HasPointwiseRightDerivedFunctor W] {I : C}
    (hb : ∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I))) :
    IsIso (β.app I) :=
  (LeftExtension.mk RF β).isIso_hom_app_of_bijective
    (isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor RF β W (L.obj I)) hb

/-- **Absoluteness of a right derived functor obtained from resolutions.** If every object of `C`
admits a morphism of `W` into an object at which `L` is fully faithful, and `RF` is the right
derived functor of `F` with comparison `β`, then for every functor `G` the composite `RF ⋙ G` is
the right derived functor of `F ⋙ G`, with the whiskered comparison.

This is the hypothesis `CategoryTheory.Adjunction.derived` asks of the right adjoint's derived
functor. -/
theorem isRightDerivedFunctor_comp_of_coresolutions {F : C ⥤ H} {RF : D ⥤ H}
    (β : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor β W] (G : H ⥤ H')
    (hres : ∀ X : C, ∃ (I : C) (s : X ⟶ I), W s ∧
      ∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I))) :
    (RF ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight β G ≫ (Functor.associator L RF G).hom) W := by
  have := hasPointwiseRightDerivedFunctor_of_coresolutions W F hres
  have := hasPointwiseRightDerivedFunctor_of_coresolutions W (F ⋙ G) hres
  have := (F ⋙ G).hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor W
  rw [((F ⋙ G).totalRightDerived L W).isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    ((F ⋙ G).totalRightDerivedUnit L W) W (RF ⋙ G)
    (Functor.whiskerRight β G ≫ (Functor.associator L RF G).hom)]
  refine isIso_of_isIso_app_of_coresolutions W _ hres fun I hb => ?_
  have := isIso_app_of_isRightDerivedFunctor W β hb
  have := isIso_app_of_isRightDerivedFunctor W ((F ⋙ G).totalRightDerivedUnit L W) hb
  have : IsIso (((F ⋙ G).totalRightDerivedUnit L W).app I ≫
      (((F ⋙ G).totalRightDerived L W).rightDerivedDesc
        ((F ⋙ G).totalRightDerivedUnit L W) W (RF ⋙ G)
        (Functor.whiskerRight β G ≫ (Functor.associator L RF G).hom)).app (L.obj I)) := by
    rw [((F ⋙ G).totalRightDerived L W).rightDerived_fac_app
      ((F ⋙ G).totalRightDerivedUnit L W) W (RF ⋙ G)
      (Functor.whiskerRight β G ≫ (Functor.associator L RF G).hom) I]
    have h : (Functor.whiskerRight β G ≫ (Functor.associator L RF G).hom).app I
        = G.map (β.app I) := by simp
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (((F ⋙ G).totalRightDerivedUnit L W).app I) _

end Right

end Functor

end CategoryTheory

end
