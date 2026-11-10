module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleColimits
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.BaseChange

/-!
# Galois structures extend along fully faithful base change

Let `q : T ⟶ S` be a morphism along which base change of finite étale covers is fully faithful,
`Y` a finite étale cover of `S` with connected total space and `Z` a finite étale Galois cover of
`T` with group `G`, together with an isomorphism `Y ×_S T ≅ Z`. Then the action of `G` on `Z`
comes from a unique action on `Y`, and this makes `Y` a Galois cover: the comparison map
`G × Y ⟶ Y ×_S Y` is a morphism of finite étale covers of `S` whose base change to `T` is the
comparison map of `Z`, and a fully faithful functor reflects isomorphisms.

## Main results

* `AlgebraicGeometry.exists_finiteEtaleGaloisCover_of_fullyFaithful`.

## References

* [Stacks Project, Section 03SF](https://stacks.math.columbia.edu/tag/03SF)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- **Galois structures extend along fully faithful base change.** -/
theorem exists_finiteEtaleGaloisCover_of_fullyFaithful {S T : Scheme.{u}} (q : T ⟶ S)
    (hff : (finiteEtaleBaseChange q).FullyFaithful)
    (G : Type v) [Group G] [Finite G] (Y : FiniteEtaleOver S) (hY : ConnectedSpace Y.left)
    (Z : FiniteEtaleGaloisCover T G) (e : (finiteEtaleBaseChange q).obj Y ≅ Z.obj) :
    ∃ (Y' : FiniteEtaleGaloisCover S G) (e : (finiteEtaleBaseChange q).obj Y'.obj ≅ Z.obj),
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange q).map (Y'.action g).asIso.hom ≫ e.hom =
        e.hom ≫ (Z.action g).asIso.hom := by
  let F := finiteEtaleBaseChange q
  let act : Gᵐᵒᵖ →* Aut Y := ((hff.autMulEquivOfFullyFaithful Y).symm.toMonoidHom).comp
    ((e.symm.conjAut.toMonoidHom).comp Z.action)
  have hequiv : ∀ g, F.map (act g).asIso.hom ≫ e.hom = e.hom ≫ (Z.action g).asIso.hom := by
    intro g
    change F.map (hff.preimage (e.symm.conjAut (Z.action g)).asIso.hom) ≫ e.hom = _
    rw [hff.map_preimage, Iso.conjAut_hom, Iso.conj_apply_asHom]
    simp
  let aY : Gᵐᵒᵖ →* Aut (Over.mk Y.hom) := ((MorphismProperty.Over.forget _ ⊤ S).mapAut Y).comp act
  let aZ : Gᵐᵒᵖ →* Aut (Over.mk Z.obj.hom) :=
    ((MorphismProperty.Over.forget _ ⊤ T).mapAut Z.obj).comp Z.action
  let p : Z.obj.left ⟶ Y.left := e.inv.left ≫ pullback.fst Y.hom q
  have H : IsPullback p Z.obj.hom Y.hom q := by
    let eL : ((finiteEtaleBaseChange q).obj Y).left ≅ Z.obj.left :=
      ((MorphismProperty.Over.forget _ ⊤ T) ⋙ Over.forget T).mapIso e
    refine (IsPullback.of_hasPullback Y.hom q).of_iso eL (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id]
      exact (eL.hom_inv_id_assoc (pullback.fst Y.hom q)).symm
    · simp only [Iso.refl_hom, Category.comp_id, eL]
      exact (MorphismProperty.Over.w e.hom).symm
    · simp
    · simp
  have hab : ∀ g, (aZ g).asIso.hom.left ≫ p = p ≫ (aY g).asIso.hom.left := by
    intro g
    have h1 : e.inv ≫ F.map (act g).asIso.hom = (Z.action g).asIso.hom ≫ e.inv := by
      rw [Iso.eq_comp_inv, Category.assoc, hequiv, Iso.inv_hom_id_assoc]
    have h2 : e.inv.left ≫ (F.map (act g).asIso.hom).left =
        (Z.action g).asIso.hom.left ≫ e.inv.left :=
      congrArg (fun φ ↦ φ.left) h1
    change (Z.action g).asIso.hom.left ≫ e.inv.left ≫ pullback.fst Y.hom q =
      (e.inv.left ≫ pullback.fst Y.hom q) ≫ (act g).asIso.hom.left
    have h3 := finiteEtaleBaseChange_map_left_fst q (act g).asIso.hom
    calc (Z.action g).asIso.hom.left ≫ e.inv.left ≫ pullback.fst Y.hom q
        = ((Z.action g).asIso.hom.left ≫ e.inv.left) ≫ pullback.fst Y.hom q :=
          (Category.assoc _ _ _).symm
      _ = (e.inv.left ≫ (F.map (act g).asIso.hom).left) ≫ pullback.fst Y.hom q := by rw [h2]
      _ = e.inv.left ≫ ((F.map (act g).asIso.hom).left ≫ pullback.fst Y.hom q) :=
          Category.assoc _ _ _
      _ = e.inv.left ≫ (pullback.fst Y.hom q ≫ (act g).asIso.hom.left) :=
          congrArg (e.inv.left ≫ ·) h3
      _ = (e.inv.left ≫ pullback.fst Y.hom q) ≫ (act g).asIso.hom.left :=
          (Category.assoc _ _ _).symm
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  let A : FiniteEtaleOver S := MorphismProperty.Over.mk ⊤ (Limits.Sigma.desc fun _ : G ↦ Y.hom)
    (Stacks.FundamentalGroup.finiteEtale_sigmaDesc fun _ ↦ Y.prop)
  let B : FiniteEtaleOver S := MorphismProperty.Over.mk ⊤ (pullback.fst Y.hom Y.hom ≫ Y.hom)
    ⟨inferInstance, inferInstance⟩
  let cY := Stacks.Descent.galoisCoverComparison Y.hom aY
  let C : A ⟶ B :=
    MorphismProperty.Over.homMk cY (galoisCoverComparison_fst_comp Y.hom aY)
  have : IsIso (F.map C).left :=
    (GaloisCoverLimits.isIso_galoisCoverComparison_iff_isIso_pullback_map H aY aZ hab).mp
      Z.comparisonIsIso
  have : IsIso (F.map C) := by
    have : F.map C = (MorphismProperty.Over.isoMk (asIso (F.map C).left)
        (MorphismProperty.Over.w (F.map C))).hom := by
      ext
      rfl
    rw [this]
    infer_instance
  have : IsIso C := hff.isIso_of_isIso_map C
  have : IsIso cY := ((MorphismProperty.Over.forget _ ⊤ S) ⋙ Over.forget S).map_isIso C
  exact ⟨{ obj := Y, connected := hY, action := act, comparisonIsIso := this }, e, hequiv⟩

end AlgebraicGeometry
