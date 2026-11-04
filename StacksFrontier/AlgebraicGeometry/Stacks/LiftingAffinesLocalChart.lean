module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms

/-!
# Local thickened charts for Stacks 0CJV

The restriction of a smooth chart `b : U' ⟶ 𝒳'` to an open `U'_w ⊆ U'` is smooth; its base
change along a thickening `𝒳 ⟶ 𝒳'` is an algebraic space `U_w` with a monomorphism to `U'_w`
whose range is a thickening, and a relatively smooth projection to `𝒳`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The 1-morphism of the stack of an étale morphism of representable spaces is smooth.** -/
theorem isSmooth_map_yoneda_of_etale {U V : BigFppfOver B S hS} (φ : U ⟶ V)
    (hφ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map φ)) :
    AlgebraicStacks.IsSmooth B S hS ((algebraicSpaceStackFunctor.{u, w} B S hS).map
      (schemeSpaceMap φ :
        (schemeSpace U : AlgebraicSpaces B S hS) ⟶
          schemeSpace V)) := by
  refine isSmooth_of_isSmooth_representingMap B S hS (schemeSpace U).obj (schemeSpace V).obj
    (schemeSpace U).property (schemeSpace V).property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) _ ?_
  show Space.IsSmooth B S hS (representingMap B S hS
    (fibredCategory B S hS (schemeSpace U).obj) (fibredCategory B S hS (schemeSpace V).obj)
    (schemeSpace U).obj (schemeSpace V).obj
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (associatedMap B S hS (schemeSpaceMap φ).hom).1)
  rw [representingMap_associatedMap]
  exact Space.isSmooth_of_isEtale B S hS (isAlgebraicSpace_yoneda B S hS V)
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((Space.presheaf_yoneda_map_etale_iff B S hS φ).2 hφ))

/-- **The base change of a smooth 1-morphism out of an algebraic space along a thickening.** -/
theorem exists_thickeningChart_square {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (ι : 𝒳 ⟶ 𝒳')
    (hι : IsThickening ι) {U' : AlgebraicSpaces B S hS}
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U' ⟶ 𝒳')
    (hb : AlgebraicStacks.IsSmooth B S hS b) :
    ∃ (U : AlgebraicSpaces B S hS) (iU : U ⟶ U')
      (a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳)
      (γ : (algebraicSpaceStackFunctor.{u, w} B S hS).map iU ≫ b ≅ a ≫ ι),
      Nonempty (Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq b ι)) ∧
      IsRelativelySmooth.{u, u, u + 1} B S hS a.hom ∧ Mono iU.hom ∧
      Space.IsThickening B S hS U' (Subfunctor.range iU.hom) := by
  have hrep : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom ι.hom).pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS _ _ _ ι.hom b.hom _
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        b.hom ι.hom) hι.1.1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U'.obj U'.property)
  obtain ⟨U, c, a, γ, ⟨hγ⟩⟩ := exists_isTwoFibreProduct_algebraicSpaceStackFunctor_obj b ι hrep
  obtain ⟨iU, rfl⟩ : ∃ iU : U ⟶ U', (algebraicSpaceStackFunctor.{u, w} B S hS).map iU = c :=
    ⟨_, algebraicSpaceStackFunctor_map_homMk_representingMap c⟩
  have hsw' := isTwoFibreProduct_underlying_algebraicStacks B S hS _
    (Bicategory.isTwoFibreProduct_swap hγ)
  let Q := (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq b ι).underlying
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_underlying_algebraicStacks B S hS _ hγ
  have hth := mono_and_isThickening_range_representingMap_fst B S hS ι.hom b.hom
    (isRelativeThickening_of_isThickening B S hS hι) Q hQ U.obj U'.obj U.property U'.property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  have he : representingMap B S hS Q.pt ((algebraicSpaceStackFunctor.{u, w} B S hS).obj U').val
      U.obj U'.obj (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst = iU.hom :=
    representingMap_associatedMap B S hS U.obj U'.obj iU.hom
  rw [he] at hth
  exact ⟨U, iU, a, γ, ⟨hγ⟩,
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS _ _ _ b.hom ι.hom _ hsw'
      (isRelativelySmooth_of_isSmooth_space_source b hb), hth.1, hth.2⟩

/-- **A thickening subspace of a representable algebraic space is a closed subscheme.** If a
monomorphism `U ⟶ X` of algebraic spaces into a representable `X` has a thickening as its range,
then `U` is represented by an object `Y` of the site with a surjective closed immersion
`Y ⟶ X`. -/
theorem exists_closedSubscheme_of_isThickening {X : BigFppfOver B S hS}
    {U : AlgebraicSpaces B S hS}
    (iU : U ⟶ (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS))
    [Mono iU.hom]
    (h : Space.IsThickening B S hS ⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩
      (Subfunctor.range iU.hom)) :
    ∃ (Y : BigFppfOver B S hS) (c : Y ⟶ X) (e : yoneda.obj Y ≅ U.obj),
      e.hom ≫ iU.hom = yoneda.map c ∧
        AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map c) ∧
      Function.Surjective ((BigFppfOver.toScheme B S hS).map c) := by
  obtain ⟨⟨-, hcl⟩, hsurj⟩ := h
  have hrep := hcl.rep
  let g : yoneda.obj X ⟶ yoneda.obj X := 𝟙 _
  have hpb := hrep.isPullback g
  have : IsIso (hrep.fst g) := hpb.isIso_fst_of_isIso
  let e : yoneda.obj (hrep.pullback g) ≅ U.obj :=
    asIso (hrep.fst g) ≪≫ (asIso (Subfunctor.toRange iU.hom)).symm
  have he : e.hom ≫ iU.hom = yoneda.map (hrep.snd g) := by
    have hw := hpb.w
    simp only [g, Category.comp_id] at hw
    rw [← hw]
    simp only [e, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
    congr 1
    rw [IsIso.inv_comp_eq]
    rfl
  refine ⟨hrep.pullback g, hrep.snd g, e, he, hcl.property_snd g, ?_⟩
  have hisoS : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : F ≅ G),
      Function.Surjective (Space.pointsMap B S hS F φ.hom) := by
    intro F G φ q
    refine ⟨Space.pointsMap B S hS _ φ.inv q, ?_⟩
    rw [← Function.comp_apply (f := Space.pointsMap B S hS _ φ.hom), ← Space.pointsMap_comp,
      φ.inv_hom_id, Space.pointsMap_id]
    rfl
  rw [← Space.surjective_pointsMap_yoneda_iff B S hS, ← he, Space.pointsMap_comp]
  refine Function.Surjective.comp ?_ (hisoS e)
  have hfac : iU.hom = Subfunctor.toRange iU.hom ≫ (Subfunctor.range iU.hom).ι := rfl
  rw [hfac, Space.pointsMap_comp]
  exact hsurj.comp (hisoS (asIso (Subfunctor.toRange iU.hom)))

end AlgebraicGeometry.Stack

end
