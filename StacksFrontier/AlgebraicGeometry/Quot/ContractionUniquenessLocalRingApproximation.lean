module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessLocalRing
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertLimitStageProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationColimitRealised
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.RingTheory.SpreadingOut.ColimitSystem

/-!
# Approximating families of curves over a local ring by Noetherian local stages

Let `W = lim W_λ` be a cofiltered limit of affine objects of a big fppf site, with affine
transition morphisms, realised in the site. This file collects the approximation statements of the
proof of [Stacks, Tag 0E89] in the form of cartesian squares: an algebraic space of finite
presentation over `W` is the base change of one over a stage ([Stacks, Tag 07SK]), a morphism
between two such base changes is the base change of a morphism at a later stage, and properness and
flatness of the base change are already properness and flatness at a later stage
([Stacks, Tags 08K1, 08K0]).

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_of_isFinitePresentationColimit`: a model at a stage.
* `AlgebraicGeometry.Space.exists_isPullback_hom_of_isFinitePresentationColimit`: a model at a
  later stage of a morphism.
* `AlgebraicGeometry.Space.exists_stage_of_isLimit_of_isPullback`: a base-change-stable property
  of morphisms which descends along the limit (properness, flatness) holds at a later stage.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.Space

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝒯S" => BigFppfOver.toScheme B S hS

/-- **The base change of a cartesian square along a factorisation of its bottom edge.** If `Z` is
the base change of `Zᵢ` along `P : T ⟶ Tᵢ` and `P` factors as `P' ≫ Q`, then `Z` is the base
change along `P'` of the base change of `Zᵢ` along `Q`. -/
theorem isPullback_lift_of_isPullback_of_fac {Z Zi T T' Ti : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {q : Z ⟶ Zi} {f : Z ⟶ T} {fi : Zi ⟶ Ti} {P : T ⟶ Ti} (sq : IsPullback q f fi P)
    (P' : T ⟶ T') (Q : T' ⟶ Ti) (hPQ : P' ≫ Q = P) :
    IsPullback (pullback.lift q (f ≫ P') (by rw [Category.assoc, hPQ, sq.w]) :
        Z ⟶ pullback fi Q) f (pullback.snd fi Q) P' := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback fi Q)
  rw [pullback.lift_fst, hPQ]
  exact sq

/-- An object of the big fppf site, as a scheme over the terminal algebraic space. -/
def schemesOverTerminal :
    BigFppfOver B S hS ⥤ SchemesOverPresheaf B S hS (schemeSpace (Over.mk (𝟙 (B.obj hS)))) where
  obj T := CostructuredArrow.mk (yoneda.map (Over.mkIdTerminal.from T))
  map f := CostructuredArrow.homMk f
    ((Functor.map_comp yoneda _ _).symm.trans (congrArg yoneda.map (Over.mkIdTerminal.hom_ext _ _)))

variable {B S hS}

/-- **A model at a stage** ([Stacks, Tag 07SK], essential surjectivity). If base change exhibits
the algebraic spaces of finite presentation over `M` as the filtered colimit of those over the
stages `W i`, every algebraic space of finite presentation over `M` is the base change of one over
a stage, through a cartesian square. -/
theorem exists_isPullback_of_isFinitePresentationColimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] {W : I ⥤ BigFppfOver B S hS} {M : BigFppfOver B S hS}
    {p : (i : I) → (M ⟶ W.obj i)} {hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i}
    (P : FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS W M p hp)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z) (f : Z ⟶ yoneda.obj M)
    (hfp : IsFinitePresentation B S hS f) :
    ∃ (i : I) (Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (fi : Zi ⟶ yoneda.obj (W.obj i))
      (q : Z ⟶ Zi), IsAlgebraicSpace B S hS Zi ∧ IsFinitePresentation B S hS fi ∧
        IsPullback q f fi (yoneda.map (p i)) := by
  obtain ⟨i, Yi, ⟨θ⟩⟩ := P.essSurj ⟨Over.mk f, hZ, hfp⟩
  let θ' := (ObjectProperty.ι _).mapIso θ
  let a : pullback Yi.obj.hom (yoneda.map (p i)) ⟶ Z := θ'.hom.left
  let b : Z ⟶ pullback Yi.obj.hom (yoneda.map (p i)) := θ'.inv.left
  have hab : a ≫ b = 𝟙 _ := congrArg (fun k => k.left) θ'.hom_inv_id
  have hba : b ≫ a = 𝟙 _ := congrArg (fun k => k.left) θ'.inv_hom_id
  have ha : a ≫ f = pullback.snd Yi.obj.hom (yoneda.map (p i)) := Over.w θ'.hom
  refine ⟨i, Yi.obj.left, Yi.obj.hom, b ≫ pullback.fst _ _, Yi.property.1, Yi.property.2, ?_⟩
  refine IsPullback.of_iso (IsPullback.of_hasPullback Yi.obj.hom (yoneda.map (p i)))
    ⟨a, b, hab, hba⟩ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change pullback.fst _ _ ≫ 𝟙 _ = a ≫ b ≫ pullback.fst _ _
    rw [← Category.assoc, hab, Category.id_comp, Category.comp_id]
  · change pullback.snd _ _ ≫ 𝟙 _ = a ≫ f
    rw [ha, Category.comp_id]

/-- The morphism of fibre products induced by a morphism `c` over the base of two cartesian
squares lies over the base. -/
theorem isoPullback_inv_comp_comp_snd {Y Z Yi Zi T Ti : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {gY : Y ⟶ T} {gZ : Z ⟶ T} {gYi : Yi ⟶ Ti} {gZi : Zi ⟶ Ti} {P : T ⟶ Ti} {qY : Y ⟶ Yi}
    {qZ : Z ⟶ Zi} (sqY : IsPullback qY gY gYi P) (sqZ : IsPullback qZ gZ gZi P) (c : Y ⟶ Z)
    (hc : c ≫ gZ = gY) :
    (sqY.isoPullback.inv ≫ c ≫ sqZ.isoPullback.hom) ≫ pullback.snd gZi P = pullback.snd gYi P := by
  rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd, hc,
    IsPullback.isoPullback_inv_snd]

/-- **The square form of a morphism given by fullness.** If `h'` is a morphism over the stage `j`
between the base changes of `Yᵢ`, `Zᵢ` whose base change to the vertex is, through the comparisons
of the factorisation `p j ≫ W.map e = p i`, the morphism induced by `c : Y ⟶ Z`, then `h'` models
`c` through the lifts of the cartesian squares. -/
theorem comp_lift_eq_lift_comp_of_baseChangeFactorIso {I : Type u} [Category.{u} I]
    {W : I ⥤ BigFppfOver B S hS} {M : BigFppfOver B S hS}
    {p : (i : I) → (M ⟶ W.obj i)} (hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i) {i j : I}
    (e : j ⟶ i) {Y Z Yi Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hYi : IsAlgebraicSpace B S hS Yi)
    (hZi : IsAlgebraicSpace B S hS Zi) {gY : Y ⟶ yoneda.obj M} {gZ : Z ⟶ yoneda.obj M}
    {gYi : Yi ⟶ yoneda.obj (W.obj i)} {gZi : Zi ⟶ yoneda.obj (W.obj i)}
    (hYifp : IsFinitePresentation B S hS gYi) (hZifp : IsFinitePresentation B S hS gZi)
    {qY : Y ⟶ Yi} {qZ : Z ⟶ Zi} (sqY : IsPullback qY gY gYi (yoneda.map (p i)))
    (sqZ : IsPullback qZ gZ gZi (yoneda.map (p i))) (c : Y ⟶ Z) (hc : c ≫ gZ = gY)
    (h' : (FinitePresentationSpacesOver.baseChange B S hS (W.map e)).obj
        (⟨Over.mk gYi, hYi, hYifp⟩ : FinitePresentationSpacesOver B S hS (W.obj i)) ⟶
      (FinitePresentationSpacesOver.baseChange B S hS (W.map e)).obj
        (⟨Over.mk gZi, hZi, hZifp⟩ : FinitePresentationSpacesOver B S hS (W.obj i)))
    (hh' : (FinitePresentationSpacesOver.baseChangeFactorIso B S hS (hp e)).hom.app
        (⟨Over.mk gYi, hYi, hYifp⟩ : FinitePresentationSpacesOver B S hS (W.obj i)) ≫
        (FinitePresentationSpacesOver.baseChange B S hS (p j)).map h' =
      (ObjectProperty.homMk (Over.homMk (sqY.isoPullback.inv ≫ c ≫ sqZ.isoPullback.hom)
          (isoPullback_inv_comp_comp_snd sqY sqZ c hc)) :
        (FinitePresentationSpacesOver.baseChange B S hS (p i)).obj
            (⟨Over.mk gYi, hYi, hYifp⟩ : FinitePresentationSpacesOver B S hS (W.obj i)) ⟶
          (FinitePresentationSpacesOver.baseChange B S hS (p i)).obj
            (⟨Over.mk gZi, hZi, hZifp⟩ : FinitePresentationSpacesOver B S hS (W.obj i))) ≫
        (FinitePresentationSpacesOver.baseChangeFactorIso B S hS (hp e)).hom.app
          (⟨Over.mk gZi, hZi, hZifp⟩ : FinitePresentationSpacesOver B S hS (W.obj i))) :
    ∀ cj : pullback gYi (yoneda.map (W.map e)) ⟶ pullback gZi (yoneda.map (W.map e)),
      cj = h'.hom.left →
      c ≫ pullback.lift qZ (gZ ≫ yoneda.map (p j))
          (by rw [Category.assoc, ← Functor.map_comp, hp e, sqZ.w]) =
        pullback.lift qY (gY ≫ yoneda.map (p j))
          (by rw [Category.assoc, ← Functor.map_comp, hp e, sqY.w]) ≫ cj := by
  intro cj₀ hcj₀
  -- the comparisons of the factorisation, read on the presheaves
  have hfac : yoneda.map (p j) ≫ yoneda.map (W.map e) = yoneda.map (p i) := by
    rw [← Functor.map_comp, hp e]
  have hδ : ∀ {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A : Over (yoneda.obj (W.obj i))}
      {gV : V ⟶ yoneda.obj M} {qV : V ⟶ A.left}
      (sqV : IsPullback qV gV A.hom (yoneda.map (p i))),
      sqV.isoPullback.hom ≫ (Over.pullbackFactorObjIso hfac A).hom.left ≫ pullback.fst _ _ =
        pullback.lift qV (gV ≫ yoneda.map (p j)) (by rw [Category.assoc, hfac]; exact sqV.w) := by
    intro V A gV qV sqV
    have sq' := Over.isPullback_pullback_snd_pullback_of_comp hfac A
    have e : sqV.isoPullback.hom ≫ (Over.pullbackFactorObjIso hfac A).hom.left =
        sq'.lift qV gV sqV.w := by
      apply sq'.hom_ext
      · rw [sq'.lift_fst, Category.assoc, Over.pullbackFactorObjIso_hom_left_fst]
        exact sqV.isoPullback_hom_fst
      · rw [sq'.lift_snd, Category.assoc, Over.pullbackFactorObjIso_hom_left_snd]
        exact sqV.isoPullback_hom_snd
    rw [← Category.assoc, e]
    apply pullback.hom_ext
    · exact (sq'.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
    · simp only [Over.pullback_obj_hom, Category.assoc]
      rw [pullback.condition, ← Category.assoc, sq'.lift_snd, pullback.lift_snd]
  have key := congrArg (fun k => (ObjectProperty.ι _).map k) hh'
  simp only [Functor.map_comp, FinitePresentationSpacesOver.baseChangeFactorIso_hom_app_left,
    FinitePresentationSpacesOver.ι_map_baseChange_map, Over.pullbackFactorIso_hom_app] at key
  have key' : (Over.pullbackFactorObjIso hfac (Over.mk gYi)).hom.left ≫
      ((Over.pullback (yoneda.map (p j))).map ((ObjectProperty.ι _).map h')).left =
        (sqY.isoPullback.inv ≫ c ≫ sqZ.isoPullback.hom) ≫
          (Over.pullbackFactorObjIso hfac (Over.mk gZi)).hom.left :=
    congrArg Over.Hom.left key
  obtain ⟨cj, hcj⟩ : ∃ cj : ((Over.pullback (yoneda.map (W.map e))).obj (Over.mk gYi)).left ⟶
      ((Over.pullback (yoneda.map (W.map e))).obj (Over.mk gZi)).left, cj = h'.hom.left :=
    ⟨_, rfl⟩
  obtain ⟨Mj, hMj⟩ : ∃ Mj : ((Over.pullback (yoneda.map (W.map e)) ⋙
      Over.pullback (yoneda.map (p j))).obj (Over.mk gYi)).left ⟶
        ((Over.pullback (yoneda.map (W.map e)) ⋙ Over.pullback (yoneda.map (p j))).obj
          (Over.mk gZi)).left,
      Mj = ((Over.pullback (yoneda.map (p j))).map ((ObjectProperty.ι _).map h')).left :=
    ⟨_, rfl⟩
  have hmap : Mj ≫ pullback.fst ((Over.pullback (yoneda.map (W.map e))).obj (Over.mk gZi)).hom
          (yoneda.map (p j)) =
      pullback.fst ((Over.pullback (yoneda.map (W.map e))).obj (Over.mk gYi)).hom
          (yoneda.map (p j)) ≫ cj := by
    rw [hcj, hMj]
    exact pullback.lift_fst _ _ _
  have key'' : (Over.pullbackFactorObjIso hfac (Over.mk gYi)).hom.left ≫ Mj =
      (sqY.isoPullback.inv ≫ c ≫ sqZ.isoPullback.hom) ≫
        (Over.pullbackFactorObjIso hfac (Over.mk gZi)).hom.left := by
    rwa [hMj]
  have E : (sqY.isoPullback.hom ≫ (Over.pullbackFactorObjIso hfac (Over.mk gYi)).hom.left ≫
        pullback.fst ((Over.pullback (yoneda.map (W.map e))).obj (Over.mk gYi)).hom
          (yoneda.map (p j))) ≫ cj =
      c ≫ sqZ.isoPullback.hom ≫ (Over.pullbackFactorObjIso hfac (Over.mk gZi)).hom.left ≫
        pullback.fst ((Over.pullback (yoneda.map (W.map e))).obj (Over.mk gZi)).hom
          (yoneda.map (p j)) := by
    rw [Category.assoc, Category.assoc, ← hmap,
      ← Category.assoc (Over.pullbackFactorObjIso hfac (Over.mk gYi)).hom.left Mj, key'']
    simp
  erw [← hδ (A := Over.mk gYi) sqY, ← hδ (A := Over.mk gZi) sqZ]
  rw [hcj₀, ← hcj]
  exact E.symm

/-- **A model at a later stage of a morphism** ([Stacks, Tag 07SK], fullness). If `Y`, `Z` are,
through cartesian squares, base changes of `Yᵢ`, `Zᵢ` over a stage, a morphism `c : Y ⟶ Z` over
`M` is the base change of a morphism `cⱼ` over a later stage between the base changes of `Yᵢ` and
`Zᵢ`. -/
theorem exists_isPullback_hom_of_isFinitePresentationColimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] {W : I ⥤ BigFppfOver B S hS} {M : BigFppfOver B S hS}
    {p : (i : I) → (M ⟶ W.obj i)} {hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i}
    (P : FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS W M p hp) (i : I)
    {Y Z Yi Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hYi : IsAlgebraicSpace B S hS Yi)
    (hZi : IsAlgebraicSpace B S hS Zi) {gY : Y ⟶ yoneda.obj M} {gZ : Z ⟶ yoneda.obj M}
    {gYi : Yi ⟶ yoneda.obj (W.obj i)} {gZi : Zi ⟶ yoneda.obj (W.obj i)}
    (hYifp : IsFinitePresentation B S hS gYi) (hZifp : IsFinitePresentation B S hS gZi)
    {qY : Y ⟶ Yi} {qZ : Z ⟶ Zi} (sqY : IsPullback qY gY gYi (yoneda.map (p i)))
    (sqZ : IsPullback qZ gZ gZi (yoneda.map (p i))) (c : Y ⟶ Z) (hc : c ≫ gZ = gY) :
    ∃ (j : I) (e : j ⟶ i)
      (cj : pullback gYi (yoneda.map (W.map e)) ⟶ pullback gZi (yoneda.map (W.map e))),
      cj ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      c ≫ pullback.lift qZ (gZ ≫ yoneda.map (p j))
          (by rw [Category.assoc, ← Functor.map_comp, hp e, sqZ.w]) =
        pullback.lift qY (gY ≫ yoneda.map (p j))
          (by rw [Category.assoc, ← Functor.map_comp, hp e, sqY.w]) ≫ cj := by
  let Yi' : FinitePresentationSpacesOver B S hS (W.obj i) := ⟨Over.mk gYi, hYi, hYifp⟩
  let Zi' : FinitePresentationSpacesOver B S hS (W.obj i) := ⟨Over.mk gZi, hZi, hZifp⟩
  let h : (FinitePresentationSpacesOver.baseChange B S hS (p i)).obj Yi' ⟶
      (FinitePresentationSpacesOver.baseChange B S hS (p i)).obj Zi' :=
    ObjectProperty.homMk (Over.homMk (sqY.isoPullback.inv ≫ c ≫ sqZ.isoPullback.hom)
        (isoPullback_inv_comp_comp_snd sqY sqZ c hc))
  obtain ⟨j, e, h', hh'⟩ := P.full i Yi' Zi' h
  exact ⟨j, e, h'.hom.left, Over.w h'.hom,
    comp_lift_eq_lift_comp_of_baseChangeFactorIso hp e hYi hZi hYifp hZifp sqY sqZ c hc h' hh' _
      rfl⟩

/-- **A model at a later stage of an isomorphism** ([Stacks, Tag 07SK], the isomorphism form of
fullness). If `Y`, `Z` are, through cartesian squares, base changes of `Yᵢ`, `Zᵢ` over a stage, an
isomorphism `ψ : Y ≅ Z` over `M` is the base change of an isomorphism over a later stage between
the base changes of `Yᵢ` and `Zᵢ`. -/
theorem exists_isPullback_iso_of_isFinitePresentationColimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] {W : I ⥤ BigFppfOver B S hS} {M : BigFppfOver B S hS}
    {p : (i : I) → (M ⟶ W.obj i)} {hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i}
    (P : FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS W M p hp) (i : I)
    {Y Z Yi Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hYi : IsAlgebraicSpace B S hS Yi)
    (hZi : IsAlgebraicSpace B S hS Zi) {gY : Y ⟶ yoneda.obj M} {gZ : Z ⟶ yoneda.obj M}
    {gYi : Yi ⟶ yoneda.obj (W.obj i)} {gZi : Zi ⟶ yoneda.obj (W.obj i)}
    (hYifp : IsFinitePresentation B S hS gYi) (hZifp : IsFinitePresentation B S hS gZi)
    {qY : Y ⟶ Yi} {qZ : Z ⟶ Zi} (sqY : IsPullback qY gY gYi (yoneda.map (p i)))
    (sqZ : IsPullback qZ gZ gZi (yoneda.map (p i))) (ψ : Y ≅ Z) (hψ : ψ.hom ≫ gZ = gY) :
    ∃ (j : I) (e : j ⟶ i)
      (ψj : pullback gYi (yoneda.map (W.map e)) ≅ pullback gZi (yoneda.map (W.map e))),
      ψj.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      ψ.hom ≫ pullback.lift qZ (gZ ≫ yoneda.map (p j))
          (by rw [Category.assoc, ← Functor.map_comp, hp e, sqZ.w]) =
        pullback.lift qY (gY ≫ yoneda.map (p j))
          (by rw [Category.assoc, ← Functor.map_comp, hp e, sqY.w]) ≫ ψj.hom := by
  let Yi' : FinitePresentationSpacesOver B S hS (W.obj i) := ⟨Over.mk gYi, hYi, hYifp⟩
  let Zi' : FinitePresentationSpacesOver B S hS (W.obj i) := ⟨Over.mk gZi, hZi, hZifp⟩
  let Θ : (FinitePresentationSpacesOver.baseChange B S hS (p i)).obj Yi' ≅
      (FinitePresentationSpacesOver.baseChange B S hS (p i)).obj Zi' :=
    (ObjectProperty.fullyFaithfulι _).preimageIso
      (Over.isoMk (sqY.isoPullback.symm ≪≫ ψ ≪≫ sqZ.isoPullback)
        (isoPullback_inv_comp_comp_snd sqY sqZ ψ.hom hψ))
  obtain ⟨j, e, Θ', hΘ'⟩ := P.essIso i Yi' Zi' Θ
  exact ⟨j, e, (Over.forget _).mapIso ((ObjectProperty.ι _).mapIso Θ'), Over.w Θ'.hom.hom,
    comp_lift_eq_lift_comp_of_baseChangeFactorIso hp e hYi hZi hYifp hZifp sqY sqZ ψ.hom hψ
      Θ'.hom hΘ' _ rfl⟩


/-- The base change of `f₀ : X₀ ⟶ Y₀` along `g` is cartesian over `f₀`, as soon as the comparison
`m` is the identity on the base coordinate and `f₀` on the other one. -/
private theorem isPullback_snd_of_comp_eq {B₁ B₀ X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g : B₁ ⟶ B₀} {s : X₀ ⟶ B₀} {t : Y₀ ⟶ B₀} {f₀ : X₀ ⟶ Y₀}
    (hf : f₀ ≫ t = s) (m : pullback g s ⟶ pullback g t)
    (hm₁ : m ≫ pullback.fst g t = pullback.fst g s)
    (hm₂ : m ≫ pullback.snd g t = pullback.snd g s ≫ f₀) :
    IsPullback (pullback.snd g s) m f₀ (pullback.snd g t) := by
  refine IsPullback.of_bot ?_ hm₂.symm (IsPullback.of_hasPullback g t).flip
  rw [hm₁, hf]
  exact (IsPullback.of_hasPullback g s).flip

/-- **A base-change-stable property which descends along a limit holds at a stage.** Let
`W = lim Wᵢ` be a directed limit of affine objects of the site, realised in the site, and let
`Q` be a property of morphisms of algebraic spaces, stable under base change, which descends to
a stage in every situation of Stacks 084W under the convention of Stacks 07SD (as properness,
Stacks 08K1, and flatness, Stacks 08K0, do). If `f : Z ⟶ W` is the base change of
`f₀ : Z₀ ⟶ W_l`, of finite presentation, and `f` has `Q`, then the base change of `f₀` to a later
stage has `Q`. -/
theorem exists_stage_of_isLimit_of_isPullback
    (Q : ∀ ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄, (F ⟶ G) → Prop)
    [MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => Q k.hom)]
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (hdesc : ∀ Dsit : MorphismDescentSituation B S hS (BigFppfSite.contains_terminal B) Λ,
      SiteContainsBaseChangeLimits B S hS Dsit.base →
      IsLocallyOfFinitePresentation B S hS Dsit.map₀ → Q Dsit.mapLimit →
        ∃ (i : Λ) (hi : Dsit.initial ≤ i), Q (Dsit.mapAt i hi))
    (D : Λᵒᵖ ⥤ BigFppfOver B S hS) (hD : ∀ j, IsAffine ((𝒯S).obj (D.obj j))) (c : Cone D)
    (hc : IsLimit ((𝒯S).mapCone c)) (l : Λ) {Z₀ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ₀ : IsAlgebraicSpace B S hS Z₀) (hZ : IsAlgebraicSpace B S hS Z)
    (f₀ : Z₀ ⟶ yoneda.obj (D.obj (op l))) (hfp : IsFinitePresentation B S hS f₀)
    (f : Z ⟶ yoneda.obj c.pt) (q : Z ⟶ Z₀) (sq : IsPullback q f f₀ (yoneda.map (c.π.app (op l))))
    (h : Q f) :
    ∃ (i : Λ) (hi : l ≤ i), Q (pullback.snd f₀ (yoneda.map (D.map (homOfLE hi).op))) := by
  classical
  have hZt := BigFppfSite.contains_terminal B
  have : IsCofiltered Λᵒᵖ := inferInstance
  have : IsConnected Λᵒᵖ := IsCofiltered.isConnected _
  have hsite : IsLimit c := isLimitOfReflects (𝒯S) hc
  have hyl : IsLimit (yoneda.mapCone c) := isLimitOfPreserves yoneda hsite
  let base : Λᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := D ⋙ yoneda
  let toT : limit base ⟶ yoneda.obj c.pt := hyl.lift (limit.cone base)
  have htoT : ∀ j, toT ≫ yoneda.map (c.π.app j) = limit.π base j := fun j =>
    hyl.fac (limit.cone base) j
  have hlimIso : limit base ≅ yoneda.obj c.pt :=
    (limit.isLimit base).conePointUniqueUpToIso hyl
  have hyaff : ∀ (V : BigFppfOver B S hS), IsAffine ((𝒯S).obj V) →
      IsQuasiCompactSpace B S hS (yoneda.obj V) ∧
        IsAbsolutelyQuasiSeparated B S hS hZt (yoneda.obj V) := fun V hV =>
    ⟨isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV,
      have := hV
      isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj V) hZt
        ⟨V, inferInstance, ⟨Functor.RepresentableBy.yoneda V⟩⟩⟩
  have hTl := hyaff _ (hD (op l))
  have hYl := isAlgebraicSpace_yoneda B S hS (D.obj (op l))
  have hZqc : IsQuasiCompactSpace B S hS Z₀ :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS _ hYl hTl.1 hfp
  have hZqs : IsAbsolutelyQuasiSeparated B S hS hZt Z₀ :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZt hZ₀ hTl.2 hfp.2.2
  let Dsit : MorphismDescentSituation B S hS hZt Λ :=
    { base := base
      base_isAlgebraicSpace := fun i => isAlgebraicSpace_yoneda B S hS _
      transition_affine := fun {i j} a => by
        have : IsAffine ((𝒯S).obj (D.obj i)) := hD i
        have : IsAffine ((𝒯S).obj (D.obj j)) := hD j
        exact isAffineHom_of_presheaf
          ((presheaf_yoneda_map_iff B S hS
              (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance _).mpr
            (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))
      limit_isAlgebraicSpace :=
        (isAlgebraicSpace_yoneda B S hS _).of_iso hlimIso.symm
      initial := l
      source₀ := Z₀
      target₀ := yoneda.obj (D.obj (op l))
      sourceToBase := f₀
      targetToBase := 𝟙 _
      map₀ := f₀
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hZ₀
      target₀_isAlgebraicSpace := hYl
      base₀_quasiCompact := hTl.1
      base₀_quasiSeparated := hTl.2
      source₀_quasiCompact := hZqc
      source₀_quasiSeparated := hZqs
      target₀_quasiCompact := hTl.1
      target₀_quasiSeparated := hTl.2 }
  have hconv : SiteContainsBaseChangeLimits B S hS Dsit.base :=
    siteContainsBaseChangeLimits_yoneda (D ⋙ schemesOverTerminal B S hS)
      ((schemesOverTerminal B S hS).mapCone c) hc
  -- the base change to the limit has `Q`
  have hQ' : Q Dsit.mapLimit := by
    exact prop_of_isPullback_of_factor
      (fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => Q k.hom)
      (isAlgebraicSpace_yoneda B S hS _) Dsit.targetLimit_isAlgebraicSpace hZ
      Dsit.sourceLimit_isAlgebraicSpace sq
      (isPullback_snd_of_comp_eq Dsit.map₀_over _ Dsit.mapLimit_fst Dsit.mapLimit_snd)
      (pullback.fst (limit.π base (op l)) Dsit.targetToBase ≫ toT)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => pullback.fst _ _ ≫ t) (htoT (op l))).trans
          (pullback.condition.trans (Category.comp_id _)))) h
  obtain ⟨i, hi, hQi⟩ := hdesc Dsit hconv hfp.1 hQ'
  refine ⟨i, hi, ?_⟩
  exact prop_of_isPullback_of_factor
    (fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => Q k.hom)
    (Dsit.targetAt_isAlgebraicSpace i hi) (isAlgebraicSpace_yoneda B S hS _)
    (Dsit.sourceAt_isAlgebraicSpace i hi)
    (isAlgebraicSpace_pullback B S hS f₀ _ hZ₀ (isAlgebraicSpace_yoneda B S hS _) hYl)
    (isPullback_snd_of_comp_eq Dsit.map₀_over _ (Dsit.mapAt_fst i hi) (Dsit.mapAt_snd i hi))
    (IsPullback.of_hasPullback f₀ (yoneda.map (D.map (homOfLE hi).op)))
    (pullback.lift (𝟙 _) (yoneda.map (D.map (homOfLE hi).op))
      (by rw [Category.id_comp, Category.comp_id]; rfl))
    (pullback.lift_snd _ _ _) hQi

/-- **Transfer of a base-change-stable property between two base changes along a factorisation**:
if the base change of `f₀` along `g₁` has the property and `g₂ = ε ≫ g₁`, so has the base change
of `f₀` along `g₂`. -/
theorem prop_pullback_snd_of_factor
    (Q : ∀ ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄, (F ⟶ G) → Prop)
    [MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => Q k.hom)]
    {Z₀ T₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T₁ T₂ : BigFppfOver B S hS}
    (hZ₀ : IsAlgebraicSpace B S hS Z₀) (hT₀ : IsAlgebraicSpace B S hS T₀) (f₀ : Z₀ ⟶ T₀)
    (g₁ : yoneda.obj T₁ ⟶ T₀) (g₂ : yoneda.obj T₂ ⟶ T₀) (ε : T₂ ⟶ T₁)
    (hε : yoneda.map ε ≫ g₁ = g₂) (h : Q (pullback.snd f₀ g₁)) : Q (pullback.snd f₀ g₂) :=
  prop_of_isPullback_of_factor (fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => Q k.hom)
    (isAlgebraicSpace_yoneda B S hS T₁) (isAlgebraicSpace_yoneda B S hS T₂)
    (isAlgebraicSpace_pullback B S hS f₀ g₁ hZ₀ (isAlgebraicSpace_yoneda B S hS T₁) hT₀)
    (isAlgebraicSpace_pullback B S hS f₀ g₂ hZ₀ (isAlgebraicSpace_yoneda B S hS T₂) hT₀)
    (IsPullback.of_hasPullback f₀ g₁) (IsPullback.of_hasPullback f₀ g₂) (yoneda.map ε) hε h

/-- The morphisms between the objects of a cofiltered system of affine objects of the site are
affine, and the represented presheaves of affine objects are quasi-compact and quasi-separated:
the hypotheses of Stacks 07SK in
`AlgebraicGeometry.FinitePresentationSpacesOver.isFinitePresentationColimit_of_isLimitMapCone`. -/
theorem isFinitePresentationColimit_of_isLimit_of_isAffine {Λ : Type u} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] [Nonempty Λ] {D : Λᵒᵖ ⥤ BigFppfOver B S hS}
    (hD : ∀ j, IsAffine ((𝒯S).obj (D.obj j))) {c : Cone D} (hc : IsLimit ((𝒯S).mapCone c)) :
    FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS D c.pt
      (fun i => c.π.app i) (fun {_ _} e => c.w e) := by
  have hZt := BigFppfSite.contains_terminal B
  refine FinitePresentationSpacesOver.isFinitePresentationColimit_of_isLimitMapCone B S hS
    (fun {i j} f => ?_) hc (fun j => isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (hD j))
    (fun j => ?_)
  · have : IsAffine ((𝒯S).obj (D.obj i)) := hD i
    have : IsAffine ((𝒯S).obj (D.obj j)) := hD j
    exact _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
  · have := hD j
    exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj (D.obj j)) hZt
      ⟨D.obj j, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩

/-- The transition morphisms of a system, read on the represented presheaves, compose. -/
private theorem yoneda_map_transition_comp {Λ : Type u} [Preorder Λ]
    (D : Λᵒᵖ ⥤ BigFppfOver B S hS) {l i N : Λ} (hli : l ≤ i) (hiN : i ≤ N) :
    yoneda.map (D.map (homOfLE hiN).op) ≫ yoneda.map (D.map (homOfLE hli).op) =
      yoneda.map (D.map (homOfLE (hli.trans hiN)).op) := by
  rw [← Functor.map_comp, ← D.map_comp]
  rfl

/-- **Properness and flatness at a stage.** -/
theorem exists_stage_isFlat_isProper {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [Nonempty Λ] (D : Λᵒᵖ ⥤ BigFppfOver B S hS) (hD : ∀ j, IsAffine ((𝒯S).obj (D.obj j)))
    (c : Cone D) (hc : IsLimit ((𝒯S).mapCone c)) (l : Λ)
    {Z₀ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ₀ : IsAlgebraicSpace B S hS Z₀)
    (hZ : IsAlgebraicSpace B S hS Z) (f₀ : Z₀ ⟶ yoneda.obj (D.obj (op l)))
    (hfp : IsFinitePresentation B S hS f₀) (f : Z ⟶ yoneda.obj c.pt) (q : Z ⟶ Z₀)
    (sq : IsPullback q f f₀ (yoneda.map (c.π.app (op l)))) (hfl : IsFlat B S hS f)
    (hpr : IsProper B S hS f) :
    ∃ (N : Λ) (hN : l ≤ N), IsFlat B S hS (pullback.snd f₀ (yoneda.map (D.map (homOfLE hN).op))) ∧
      IsProper B S hS (pullback.snd f₀ (yoneda.map (D.map (homOfLE hN).op))) := by
  have := isFlat_isStableUnderBaseChange B S hS
  obtain ⟨i₁, hi₁, h₁⟩ := exists_stage_of_isLimit_of_isPullback
    (fun ⦃_ _⦄ k => IsProper B S hS k)
    (fun Dsit hconv hfp' h => Dsit.exists_isProper_mapAt_of_siteContainsBaseChangeLimits hconv h
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp'))
    D hD c hc l hZ₀ hZ f₀ hfp f q sq hpr
  obtain ⟨i₂, hi₂, h₂⟩ := exists_stage_of_isLimit_of_isPullback
    (fun ⦃_ _⦄ k => IsFlat B S hS k)
    (fun Dsit hconv hfp' h => Dsit.exists_isFlat_mapAt_of_siteContainsBaseChangeLimits hconv h hfp')
    D hD c hc l hZ₀ hZ f₀ hfp f q sq hfl
  obtain ⟨N, hN₁, hN₂⟩ := directed_of (· ≤ ·) i₁ i₂
  have hY := isAlgebraicSpace_yoneda B S hS (D.obj (op l))
  exact ⟨N, hi₁.trans hN₁,
    prop_pullback_snd_of_factor (fun ⦃_ _⦄ k => IsFlat B S hS k) hZ₀ hY f₀ _ _ _
      ((yoneda_map_transition_comp D hi₂ hN₂).trans (by rfl)) h₂,
    prop_pullback_snd_of_factor (fun ⦃_ _⦄ k => IsProper B S hS k) hZ₀ hY f₀ _ _ _
      ((yoneda_map_transition_comp D hi₁ hN₁).trans (by rfl)) h₁⟩

/-- **Moving a model to a later stage**: a cartesian square over the stage `i` gives one over any
later stage `j`, with the base change of the model along the transition morphism. -/
theorem isPullback_lift_cone {Λ : Type u} [Preorder Λ] {D : Λᵒᵖ ⥤ BigFppfOver B S hS}
    (c : Cone D) {i j : Λᵒᵖ} (e : j ⟶ i) {Z Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : Z ⟶ yoneda.obj c.pt} {fi : Zi ⟶ yoneda.obj (D.obj i)} {q : Z ⟶ Zi}
    (sq : IsPullback q f fi (yoneda.map (c.π.app i))) :
    IsPullback (pullback.lift q (f ≫ yoneda.map (c.π.app j))
        (by rw [Category.assoc, ← Functor.map_comp, c.w, sq.w]) :
          Z ⟶ pullback fi (yoneda.map (D.map e)))
      f (pullback.snd fi (yoneda.map (D.map e))) (yoneda.map (c.π.app j)) :=
  isPullback_lift_of_isPullback_of_fac B S hS sq _ _ (by rw [← Functor.map_comp, c.w])

/-- **Models of three spaces at a common stage.** -/
theorem exists_isPullback_common_stage {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [Nonempty Λ] {D : Λᵒᵖ ⥤ BigFppfOver B S hS} {c : Cone D}
    (P : FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS D c.pt
      (fun i => c.π.app i) (fun {_ _} e => c.w e))
    {X Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY₁ : IsAlgebraicSpace B S hS Y₁) (hY₂ : IsAlgebraicSpace B S hS Y₂)
    (fX : X ⟶ yoneda.obj c.pt) (g₁ : Y₁ ⟶ yoneda.obj c.pt) (g₂ : Y₂ ⟶ yoneda.obj c.pt)
    (hfpX : IsFinitePresentation B S hS fX) (hfp₁ : IsFinitePresentation B S hS g₁)
    (hfp₂ : IsFinitePresentation B S hS g₂) :
    ∃ (l : Λ) (X' Y₁' Y₂' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (fX' : X' ⟶ yoneda.obj (D.obj (op l))) (g₁' : Y₁' ⟶ yoneda.obj (D.obj (op l)))
      (g₂' : Y₂' ⟶ yoneda.obj (D.obj (op l))) (qX : X ⟶ X') (q₁ : Y₁ ⟶ Y₁') (q₂ : Y₂ ⟶ Y₂'),
      IsAlgebraicSpace B S hS X' ∧ IsAlgebraicSpace B S hS Y₁' ∧ IsAlgebraicSpace B S hS Y₂' ∧
      IsFinitePresentation B S hS fX' ∧ IsFinitePresentation B S hS g₁' ∧
      IsFinitePresentation B S hS g₂' ∧ IsPullback qX fX fX' (yoneda.map (c.π.app (op l))) ∧
      IsPullback q₁ g₁ g₁' (yoneda.map (c.π.app (op l))) ∧
      IsPullback q₂ g₂ g₂' (yoneda.map (c.π.app (op l))) := by
  obtain ⟨iX, X₁, fX₁, qX₁, hX₁, hfX₁, sqX₁⟩ :=
    exists_isPullback_of_isFinitePresentationColimit P hX fX hfpX
  obtain ⟨i₁, Y₁₁, g₁₁, q₁₁, hY₁₁, hg₁₁, sq₁₁⟩ :=
    exists_isPullback_of_isFinitePresentationColimit P hY₁ g₁ hfp₁
  obtain ⟨i₂, Y₂₁, g₂₁, q₂₁, hY₂₁, hg₂₁, sq₂₁⟩ :=
    exists_isPullback_of_isFinitePresentationColimit P hY₂ g₂ hfp₂
  obtain ⟨m, h₁, h₂⟩ := directed_of (· ≤ ·) iX.unop i₁.unop
  obtain ⟨l, h₃, h₄⟩ := directed_of (· ≤ ·) m i₂.unop
  have move : ∀ {Z Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i : Λᵒᵖ} (_ : IsAlgebraicSpace B S hS Zi)
      {f : Z ⟶ yoneda.obj c.pt} {fi : Zi ⟶ yoneda.obj (D.obj i)} {q : Z ⟶ Zi}
      (_ : IsFinitePresentation B S hS fi) (_ : IsPullback q f fi (yoneda.map (c.π.app i)))
      (h : i.unop ≤ l),
      ∃ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : Z' ⟶ yoneda.obj (D.obj (op l)))
        (q' : Z ⟶ Z'), IsAlgebraicSpace B S hS Z' ∧ IsFinitePresentation B S hS f' ∧
          IsPullback q' f f' (yoneda.map (c.π.app (op l))) := by
    intro Z Zi i hZi f fi q hfi sq h
    have hT := isAlgebraicSpace_yoneda B S hS (D.obj i)
    have hT' := isAlgebraicSpace_yoneda B S hS (D.obj (op l))
    exact ⟨_, _, _, isAlgebraicSpace_pullback B S hS fi _ hZi hT' hT,
      isFinitePresentation_of_isPullback B S hS
        (isAlgebraicSpace_pullback B S hS fi _ hZi hT' hT) hZi hT' hT
        (IsPullback.of_hasPullback fi (yoneda.map (D.map (homOfLE h).op))) hfi,
      isPullback_lift_cone c (homOfLE h).op sq⟩
  obtain ⟨X', fX', qX, hX', hfX', sqX⟩ := move hX₁ hfX₁ sqX₁ (h₁.trans h₃)
  obtain ⟨Y₁', g₁', q₁, hY₁', hg₁', sq₁⟩ := move hY₁₁ hg₁₁ sq₁₁ (h₂.trans h₃)
  obtain ⟨Y₂', g₂', q₂, hY₂', hg₂', sq₂⟩ := move hY₂₁ hg₂₁ sq₂₁ h₄
  exact ⟨l, X', Y₁', Y₂', fX', g₁', g₂', qX, q₁, q₂, hX', hY₁', hY₂', hfX', hg₁', hg₂', sqX, sq₁,
    sq₂⟩

/-- **The base change of a morphism along a further base change of the base.** If `d` models `c`
through the projections `qX`, `qY`, its base change along `m` models `c` through the lifts. -/
theorem comp_lift_eq_lift_comp_map {X Y X₁ Y₁ T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fX₁ : X₁ ⟶ T₁) (g₁ : Y₁ ⟶ T₁) (m : T₂ ⟶ T₁) (d : X₁ ⟶ Y₁) (hd : d ≫ g₁ = fX₁)
    (c : X ⟶ Y) (qX : X ⟶ X₁) (qY : Y ⟶ Y₁) (hq : c ≫ qY = qX ≫ d) (fX : X ⟶ T₂)
    (gY : Y ⟶ T₂) (hc : c ≫ gY = fX) (wX : qX ≫ fX₁ = fX ≫ m) (wY : qY ≫ g₁ = gY ≫ m) :
    c ≫ pullback.lift qY gY wY = pullback.lift qX fX wX ≫
      pullback.lift (pullback.fst fX₁ m ≫ d) (pullback.snd fX₁ m)
        (by rw [Category.assoc, hd, pullback.condition]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, hq,
      ← Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd,
      hc]

/-- **Models of two morphisms at a later stage.** If three spaces over the vertex are base
changes of flat, proper spaces of finite presentation over a stage `N`, two morphisms `c₁, c₂`
over the vertex are base changes of morphisms over a later stage `M`, between the base changes of
the models, which are flat, proper and of finite presentation over `M`. -/
theorem exists_stage_homs_of_isFinitePresentationColimit {Λ : Type u} [Preorder Λ]
    {D : Λᵒᵖ ⥤ BigFppfOver B S hS} {c : Cone D} [IsCofiltered Λᵒᵖ]
    (P : FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS D c.pt
      (fun i => c.π.app i) (fun {_ _} e => c.w e)) (N : Λᵒᵖ)
    {X Y₁ Y₂ X' Y₁' Y₂' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hY₁' : IsAlgebraicSpace B S hS Y₁') (hY₂' : IsAlgebraicSpace B S hS Y₂')
    {fX : X ⟶ yoneda.obj c.pt} {g₁ : Y₁ ⟶ yoneda.obj c.pt} {g₂ : Y₂ ⟶ yoneda.obj c.pt}
    {fX' : X' ⟶ yoneda.obj (D.obj N)} {g₁' : Y₁' ⟶ yoneda.obj (D.obj N)}
    {g₂' : Y₂' ⟶ yoneda.obj (D.obj N)}
    (hflX' : IsFlat B S hS fX') (hprX' : IsProper B S hS fX')
    (hfpX' : IsFinitePresentation B S hS fX')
    (hfl₁' : IsFlat B S hS g₁') (hpr₁' : IsProper B S hS g₁')
    (hfp₁' : IsFinitePresentation B S hS g₁')
    (hfl₂' : IsFlat B S hS g₂') (hpr₂' : IsProper B S hS g₂')
    (hfp₂' : IsFinitePresentation B S hS g₂')
    {qX : X ⟶ X'} {q₁ : Y₁ ⟶ Y₁'} {q₂ : Y₂ ⟶ Y₂'}
    (sqX : IsPullback qX fX fX' (yoneda.map (c.π.app N)))
    (sq₁ : IsPullback q₁ g₁ g₁' (yoneda.map (c.π.app N)))
    (sq₂ : IsPullback q₂ g₂ g₂' (yoneda.map (c.π.app N)))
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = fX) (hc₂ : c₂ ≫ g₂ = fX) :
    ∃ (M : Λᵒᵖ) (X₀ Y₁₀ Y₂₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (f₀ : X₀ ⟶ yoneda.obj (D.obj M)) (g₁₀ : Y₁₀ ⟶ yoneda.obj (D.obj M))
      (g₂₀ : Y₂₀ ⟶ yoneda.obj (D.obj M)) (c₁₀ : X₀ ⟶ Y₁₀) (c₂₀ : X₀ ⟶ Y₂₀) (qX₀ : X ⟶ X₀)
      (q₁₀ : Y₁ ⟶ Y₁₀) (q₂₀ : Y₂ ⟶ Y₂₀),
      IsAlgebraicSpace B S hS X₀ ∧ IsAlgebraicSpace B S hS Y₁₀ ∧ IsAlgebraicSpace B S hS Y₂₀ ∧
      IsFlat B S hS f₀ ∧ IsProper B S hS f₀ ∧ IsFinitePresentation B S hS f₀ ∧
      IsFlat B S hS g₁₀ ∧ IsProper B S hS g₁₀ ∧ IsFinitePresentation B S hS g₁₀ ∧
      IsFlat B S hS g₂₀ ∧ IsProper B S hS g₂₀ ∧ IsFinitePresentation B S hS g₂₀ ∧
      c₁₀ ≫ g₁₀ = f₀ ∧ c₂₀ ≫ g₂₀ = f₀ ∧ IsPullback qX₀ fX f₀ (yoneda.map (c.π.app M)) ∧
      IsPullback q₁₀ g₁ g₁₀ (yoneda.map (c.π.app M)) ∧
      IsPullback q₂₀ g₂ g₂₀ (yoneda.map (c.π.app M)) ∧
      c₁ ≫ q₁₀ = qX₀ ≫ c₁₀ ∧ c₂ ≫ q₂₀ = qX₀ ≫ c₂₀ := by
  obtain ⟨j₁, e₁, d₁, hd₁s, hd₁c⟩ :=
    exists_isPullback_hom_of_isFinitePresentationColimit P N hX' hY₁' hfpX' hfp₁' sqX sq₁ c₁ hc₁
  have hT := isAlgebraicSpace_yoneda B S hS (D.obj N)
  have hT₁ := isAlgebraicSpace_yoneda B S hS (D.obj j₁)
  have hX₁ := isAlgebraicSpace_pullback B S hS fX' (yoneda.map (D.map e₁)) hX' hT₁ hT
  have hY₁₁ := isAlgebraicSpace_pullback B S hS g₁' (yoneda.map (D.map e₁)) hY₁' hT₁ hT
  have hY₂₁ := isAlgebraicSpace_pullback B S hS g₂' (yoneda.map (D.map e₁)) hY₂' hT₁ hT
  obtain ⟨hflX₁, hprX₁, hfpX₁⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B S hS
    (IsPullback.of_hasPullback fX' (yoneda.map (D.map e₁))) hX' hX₁ hflX' hprX' hfpX'
  obtain ⟨hfl₁₁, hpr₁₁, hfp₁₁⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B S hS
    (IsPullback.of_hasPullback g₁' (yoneda.map (D.map e₁))) hY₁' hY₁₁ hfl₁' hpr₁' hfp₁'
  obtain ⟨hfl₂₁, hpr₂₁, hfp₂₁⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B S hS
    (IsPullback.of_hasPullback g₂' (yoneda.map (D.map e₁))) hY₂' hY₂₁ hfl₂' hpr₂' hfp₂'
  have sqX₁ := isPullback_lift_cone c e₁ sqX
  have sq₁₁ := isPullback_lift_cone c e₁ sq₁
  have sq₂₁ := isPullback_lift_cone c e₁ sq₂
  obtain ⟨j₂, e₂, d₂, hd₂s, hd₂c⟩ :=
    exists_isPullback_hom_of_isFinitePresentationColimit P j₁ hX₁ hY₂₁ hfpX₁ hfp₂₁ sqX₁ sq₂₁ c₂
      hc₂
  have hT₂ := isAlgebraicSpace_yoneda B S hS (D.obj j₂)
  have hX₂ := isAlgebraicSpace_pullback B S hS (pullback.snd fX' (yoneda.map (D.map e₁)))
    (yoneda.map (D.map e₂)) hX₁ hT₂ hT₁
  have hY₁₂ := isAlgebraicSpace_pullback B S hS (pullback.snd g₁' (yoneda.map (D.map e₁)))
    (yoneda.map (D.map e₂)) hY₁₁ hT₂ hT₁
  have hY₂₂ := isAlgebraicSpace_pullback B S hS (pullback.snd g₂' (yoneda.map (D.map e₁)))
    (yoneda.map (D.map e₂)) hY₂₁ hT₂ hT₁
  obtain ⟨hflX₂, hprX₂, hfpX₂⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B S hS
    (IsPullback.of_hasPullback (pullback.snd fX' (yoneda.map (D.map e₁)))
      (yoneda.map (D.map e₂))) hX₁ hX₂ hflX₁ hprX₁ hfpX₁
  obtain ⟨hfl₁₂, hpr₁₂, hfp₁₂⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B S hS
    (IsPullback.of_hasPullback (pullback.snd g₁' (yoneda.map (D.map e₁)))
      (yoneda.map (D.map e₂))) hY₁₁ hY₁₂ hfl₁₁ hpr₁₁ hfp₁₁
  obtain ⟨hfl₂₂, hpr₂₂, hfp₂₂⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B S hS
    (IsPullback.of_hasPullback (pullback.snd g₂' (yoneda.map (D.map e₁)))
      (yoneda.map (D.map e₂))) hY₂₁ hY₂₂ hfl₂₁ hpr₂₁ hfp₂₁
  have sqX₂ := isPullback_lift_cone c e₂ sqX₁
  have sq₁₂ := isPullback_lift_cone c e₂ sq₁₁
  have sq₂₂ := isPullback_lift_cone c e₂ sq₂₁
  refine ⟨j₂, _, _, _, _, _, _,
    pullback.lift (pullback.fst (pullback.snd fX' (yoneda.map (D.map e₁)))
        (yoneda.map (D.map e₂)) ≫ d₁)
      (pullback.snd (pullback.snd fX' (yoneda.map (D.map e₁))) (yoneda.map (D.map e₂)))
      (by rw [Category.assoc, hd₁s, pullback.condition]), d₂, _, _, _, hX₂, hY₁₂, hY₂₂,
    hflX₂, hprX₂, hfpX₂, hfl₁₂, hpr₁₂, hfp₁₂, hfl₂₂, hpr₂₂, hfp₂₂, pullback.lift_snd _ _ _, hd₂s,
    sqX₂, sq₁₂,
    sq₂₂, ?_, hd₂c⟩
  exact comp_lift_eq_lift_comp_map _ _ _ d₁ hd₁s c₁ _ _ hd₁c _ _ (by rw [← Category.assoc, hc₁]) _ _

/-- **Models over a stage of three flat proper spaces of finite presentation and two morphisms.**
Over the vertex of a limit cone of a directed system of affine objects of the site, realised in the
site, three flat and proper algebraic spaces of finite presentation `X`, `Y₁`, `Y₂` and two
morphisms `cᵢ : X ⟶ Yᵢ` are, through cartesian squares, base changes of flat and proper algebraic
spaces of finite presentation and of morphisms over a stage ([Stacks, Tags 07SK, 08K0, 08K1]). -/
theorem exists_isPullback_stage_model {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [Nonempty Λ] (D : Λᵒᵖ ⥤ BigFppfOver B S hS) (hD : ∀ j, IsAffine ((𝒯S).obj (D.obj j)))
    (c : Cone D) (hc : IsLimit ((𝒯S).mapCone c))
    {X Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY₁ : IsAlgebraicSpace B S hS Y₁) (hY₂ : IsAlgebraicSpace B S hS Y₂)
    (fX : X ⟶ yoneda.obj c.pt) (g₁ : Y₁ ⟶ yoneda.obj c.pt) (g₂ : Y₂ ⟶ yoneda.obj c.pt)
    (hflX : IsFlat B S hS fX) (hprX : IsProper B S hS fX) (hfpX : IsFinitePresentation B S hS fX)
    (hfl₁ : IsFlat B S hS g₁) (hpr₁ : IsProper B S hS g₁) (hfp₁ : IsFinitePresentation B S hS g₁)
    (hfl₂ : IsFlat B S hS g₂) (hpr₂ : IsProper B S hS g₂) (hfp₂ : IsFinitePresentation B S hS g₂)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = fX) (hc₂ : c₂ ≫ g₂ = fX) :
    ∃ (M : Λᵒᵖ) (X₀ Y₁₀ Y₂₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (f₀ : X₀ ⟶ yoneda.obj (D.obj M)) (g₁₀ : Y₁₀ ⟶ yoneda.obj (D.obj M))
      (g₂₀ : Y₂₀ ⟶ yoneda.obj (D.obj M)) (c₁₀ : X₀ ⟶ Y₁₀) (c₂₀ : X₀ ⟶ Y₂₀) (qX₀ : X ⟶ X₀)
      (q₁₀ : Y₁ ⟶ Y₁₀) (q₂₀ : Y₂ ⟶ Y₂₀),
      IsAlgebraicSpace B S hS X₀ ∧ IsAlgebraicSpace B S hS Y₁₀ ∧ IsAlgebraicSpace B S hS Y₂₀ ∧
      IsFlat B S hS f₀ ∧ IsProper B S hS f₀ ∧ IsFinitePresentation B S hS f₀ ∧
      IsFlat B S hS g₁₀ ∧ IsProper B S hS g₁₀ ∧ IsFinitePresentation B S hS g₁₀ ∧
      IsFlat B S hS g₂₀ ∧ IsProper B S hS g₂₀ ∧ IsFinitePresentation B S hS g₂₀ ∧
      c₁₀ ≫ g₁₀ = f₀ ∧ c₂₀ ≫ g₂₀ = f₀ ∧ IsPullback qX₀ fX f₀ (yoneda.map (c.π.app M)) ∧
      IsPullback q₁₀ g₁ g₁₀ (yoneda.map (c.π.app M)) ∧
      IsPullback q₂₀ g₂ g₂₀ (yoneda.map (c.π.app M)) ∧
      c₁ ≫ q₁₀ = qX₀ ≫ c₁₀ ∧ c₂ ≫ q₂₀ = qX₀ ≫ c₂₀ := by
  have P := isFinitePresentationColimit_of_isLimit_of_isAffine hD hc
  obtain ⟨l, X', Y₁', Y₂', fX', g₁', g₂', qX, q₁, q₂, hX', hY₁', hY₂', hfX', hg₁', hg₂', sqX, sq₁,
    sq₂⟩ := exists_isPullback_common_stage P hX hY₁ hY₂ fX g₁ g₂ hfpX hfp₁ hfp₂
  obtain ⟨NX, hNX, hflNX, hprNX⟩ :=
    exists_stage_isFlat_isProper D hD c hc l hX' hX fX' hfX' fX qX sqX hflX hprX
  obtain ⟨N₁, hN₁, hflN₁, hprN₁⟩ :=
    exists_stage_isFlat_isProper D hD c hc l hY₁' hY₁ g₁' hg₁' g₁ q₁ sq₁ hfl₁ hpr₁
  obtain ⟨N₂, hN₂, hflN₂, hprN₂⟩ :=
    exists_stage_isFlat_isProper D hD c hc l hY₂' hY₂ g₂' hg₂' g₂ q₂ sq₂ hfl₂ hpr₂
  obtain ⟨N', hN'X, hN'₁⟩ := directed_of (· ≤ ·) NX N₁
  obtain ⟨N, hNN', hNN₂⟩ := directed_of (· ≤ ·) N' N₂
  have hYl := isAlgebraicSpace_yoneda B S hS (D.obj (op l))
  have hYN := isAlgebraicSpace_yoneda B S hS (D.obj (op N))
  have move : ∀ {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS Z')
      {f : Z ⟶ yoneda.obj c.pt} {f' : Z' ⟶ yoneda.obj (D.obj (op l))} {q : Z ⟶ Z'}
      (_ : IsFinitePresentation B S hS f') (_ : IsPullback q f f' (yoneda.map (c.π.app (op l))))
      {K : Λ} (hK : l ≤ K) (_ : K ≤ N)
      (_ : IsFlat B S hS (pullback.snd f' (yoneda.map (D.map (homOfLE hK).op))))
      (_ : IsProper B S hS (pullback.snd f' (yoneda.map (D.map (homOfLE hK).op)))),
      ∃ (Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f₀ : Z₀ ⟶ yoneda.obj (D.obj (op N)))
        (q₀ : Z ⟶ Z₀), IsAlgebraicSpace B S hS Z₀ ∧ IsFlat B S hS f₀ ∧ IsProper B S hS f₀ ∧
          IsFinitePresentation B S hS f₀ ∧ IsPullback q₀ f f₀ (yoneda.map (c.π.app (op N))) := by
    intro Z Z' hZ' f f' q hf' sq K hK hKN hfl hpr
    have hlN : l ≤ N := hK.trans hKN
    have hε := yoneda_map_transition_comp D hK hKN
    have := isFlat_isStableUnderBaseChange B S hS
    refine ⟨_, _, _, isAlgebraicSpace_pullback B S hS f' _ hZ' hYN hYl,
      prop_pullback_snd_of_factor (fun ⦃_ _⦄ k => IsFlat B S hS k) hZ' hYl f' _ _ _ hε hfl,
      prop_pullback_snd_of_factor (fun ⦃_ _⦄ k => IsProper B S hS k) hZ' hYl f' _ _ _ hε hpr,
      isFinitePresentation_of_isPullback B S hS
        (isAlgebraicSpace_pullback B S hS f' _ hZ' hYN hYl) hZ' hYN hYl
        (IsPullback.of_hasPullback f' (yoneda.map (D.map (homOfLE hlN).op))) hf',
      isPullback_lift_cone c (homOfLE hlN).op sq⟩
  obtain ⟨X₁, fX₁, qX₁, hX₁, hflX₁, hprX₁, hfpX₁, sqX₁⟩ :=
    move hX' hfX' sqX hNX (hN'X.trans hNN') hflNX hprNX
  obtain ⟨Y₁₁, g₁₁, q₁₁, hY₁₁, hfl₁₁, hpr₁₁, hfp₁₁, sq₁₁⟩ :=
    move hY₁' hg₁' sq₁ hN₁ (hN'₁.trans hNN') hflN₁ hprN₁
  obtain ⟨Y₂₁, g₂₁, q₂₁, hY₂₁, hfl₂₁, hpr₂₁, hfp₂₁, sq₂₁⟩ :=
    move hY₂' hg₂' sq₂ hN₂ hNN₂ hflN₂ hprN₂
  exact exists_stage_homs_of_isFinitePresentationColimit P (op N) hX₁ hY₁₁ hY₂₁ hflX₁ hprX₁ hfpX₁
    hfl₁₁ hpr₁₁ hfp₁₁ hfl₂₁ hpr₂₁ hfp₂₁ sqX₁ sq₁₁ sq₂₁ c₁ c₂ hc₁ hc₂

/-- **Two morphisms over a stage agreeing over the vertex agree at a later stage**
([Stacks, Tag 07SK], faithfulness), in the form of cartesian squares. -/
theorem exists_eq_of_isFinitePresentationColimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] {W : I ⥤ BigFppfOver B S hS} {M : BigFppfOver B S hS}
    {p : (i : I) → (M ⟶ W.obj i)} {hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i}
    (P : FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS W M p hp) (i : I)
    {Y Yi Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hYi : IsAlgebraicSpace B S hS Yi)
    (hZi : IsAlgebraicSpace B S hS Zi) {gY : Y ⟶ yoneda.obj M}
    {gYi : Yi ⟶ yoneda.obj (W.obj i)} {gZi : Zi ⟶ yoneda.obj (W.obj i)}
    (hYifp : IsFinitePresentation B S hS gYi) (hZifp : IsFinitePresentation B S hS gZi)
    {qY : Y ⟶ Yi} (sqY : IsPullback qY gY gYi (yoneda.map (p i))) (u v : Yi ⟶ Zi)
    (hu : u ≫ gZi = gYi) (hv : v ≫ gZi = gYi) (h : qY ≫ u = qY ≫ v) :
    ∃ (j : I) (e : j ⟶ i),
      (pullback.lift (pullback.fst gYi (yoneda.map (W.map e)) ≫ u)
          (pullback.snd gYi (yoneda.map (W.map e)))
          (by rw [Category.assoc, hu, pullback.condition]) :
        pullback gYi (yoneda.map (W.map e)) ⟶ pullback gZi (yoneda.map (W.map e))) =
      pullback.lift (pullback.fst gYi (yoneda.map (W.map e)) ≫ v)
        (pullback.snd gYi (yoneda.map (W.map e)))
        (by rw [Category.assoc, hv, pullback.condition]) := by
  let Yi' : FinitePresentationSpacesOver B S hS (W.obj i) := ⟨Over.mk gYi, hYi, hYifp⟩
  let Zi' : FinitePresentationSpacesOver B S hS (W.obj i) := ⟨Over.mk gZi, hZi, hZifp⟩
  let f : Yi' ⟶ Zi' := ObjectProperty.homMk (Over.homMk u hu)
  let g : Yi' ⟶ Zi' := ObjectProperty.homMk (Over.homMk v hv)
  have hl : (pullback.lift (pullback.fst gYi (yoneda.map (p i)) ≫ u)
      (pullback.snd gYi (yoneda.map (p i))) (by rw [Category.assoc, hu, pullback.condition]) :
        pullback gYi (yoneda.map (p i)) ⟶ pullback gZi (yoneda.map (p i))) =
      pullback.lift (pullback.fst gYi (yoneda.map (p i)) ≫ v)
        (pullback.snd gYi (yoneda.map (p i))) (by rw [Category.assoc, hv, pullback.condition]) := by
    congr 1
    rw [← sqY.isoPullback_inv_fst, Category.assoc, Category.assoc, h]
  have hfg : (FinitePresentationSpacesOver.baseChange B S hS (p i)).map f =
      (FinitePresentationSpacesOver.baseChange B S hS (p i)).map g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hl
  obtain ⟨j, e, he⟩ := P.faithful i Yi' Zi' f g hfg
  exact ⟨j, e, congrArg (fun k => k.hom.left) he⟩

/-- **The base change of an isomorphism compatible with two morphisms.** -/
theorem exists_iso_pullback_comp_eq {A B₁ B₂ T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fA : A ⟶ T} {g₁ : B₁ ⟶ T} {g₂ : B₂ ⟶ T} (m : T' ⟶ T) (b₁ : A ⟶ B₁) (b₂ : A ⟶ B₂)
    (hb₁ : b₁ ≫ g₁ = fA) (hb₂ : b₂ ≫ g₂ = fA) (Θ : B₁ ≅ B₂) (hΘ : Θ.hom ≫ g₂ = g₁)
    (heq : pullback.fst fA m ≫ b₁ ≫ Θ.hom = pullback.fst fA m ≫ b₂) :
    ∃ ψ : pullback g₁ m ≅ pullback g₂ m, ψ.hom ≫ pullback.snd g₂ m = pullback.snd g₁ m ∧
      ψ.hom ≫ pullback.fst g₂ m = pullback.fst g₁ m ≫ Θ.hom ∧
      pullback.lift (pullback.fst fA m ≫ b₁) (pullback.snd fA m)
          (by rw [Category.assoc, hb₁, pullback.condition]) ≫ ψ.hom =
        pullback.lift (pullback.fst fA m ≫ b₂) (pullback.snd fA m)
          (by rw [Category.assoc, hb₂, pullback.condition]) := by
  obtain ⟨ψ, hψs, hψf⟩ := exists_iso_of_isPullback_of_iso B S hS m
    (IsPullback.of_hasPullback g₁ m) (IsPullback.of_hasPullback g₂ m) Θ hΘ
  refine ⟨ψ, hψs, hψf, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, hψf, pullback.lift_fst_assoc, Category.assoc, heq, pullback.lift_fst]
  · rw [Category.assoc, hψs, pullback.lift_snd, pullback.lift_snd]

/-- **Lifts through the base change of an isomorphism.** -/
theorem comp_lift_eq_lift_comp_of_iso {Y₁ Y₂ B₁ B₂ T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g₁ : B₁ ⟶ T} {g₂ : B₂ ⟶ T} {m : T' ⟶ T} (Θ : B₁ ≅ B₂) (ψj : pullback g₁ m ≅ pullback g₂ m)
    (hψs : ψj.hom ≫ pullback.snd g₂ m = pullback.snd g₁ m)
    (hψf : ψj.hom ≫ pullback.fst g₂ m = pullback.fst g₁ m ≫ Θ.hom) (ψ : Y₁ ≅ Y₂)
    (q₁ : Y₁ ⟶ B₁) (q₂ : Y₂ ⟶ B₂) (G₁ : Y₁ ⟶ T') (G₂ : Y₂ ⟶ T') (hψG : ψ.hom ≫ G₂ = G₁)
    (hΘ : ψ.hom ≫ q₂ = q₁ ≫ Θ.hom) (w₁ : q₁ ≫ g₁ = G₁ ≫ m) (w₂ : q₂ ≫ g₂ = G₂ ≫ m) :
    ψ.hom ≫ pullback.lift q₂ G₂ w₂ = pullback.lift q₁ G₁ w₁ ≫ ψj.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, hψf, pullback.lift_fst_assoc, hΘ]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, hψs, pullback.lift_snd, hψG]

/-- The first two steps of `AlgebraicGeometry.Space.exists_iso_stage_of_iso`: a model `Θ` of `ψ`
at a stage `j₁`, and a later stage `j` at which the base changes of the `cₖ` agree through `Θ`. -/
theorem exists_iso_stage_of_iso_aux {I : Type u} [Category.{u} I] [IsCofiltered I]
    {W : I ⥤ BigFppfOver B S hS} {M : BigFppfOver B S hS}
    {p : (i : I) → (M ⟶ W.obj i)} {hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i}
    (P : FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS W M p hp) (i : I)
    {X Y₁ Y₂ Xi Y₁i Y₂i : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXi : IsAlgebraicSpace B S hS Xi)
    (hY₁i : IsAlgebraicSpace B S hS Y₁i) (hY₂i : IsAlgebraicSpace B S hS Y₂i)
    {fX : X ⟶ yoneda.obj M} {g₁ : Y₁ ⟶ yoneda.obj M} {g₂ : Y₂ ⟶ yoneda.obj M}
    {fXi : Xi ⟶ yoneda.obj (W.obj i)} {g₁i : Y₁i ⟶ yoneda.obj (W.obj i)}
    {g₂i : Y₂i ⟶ yoneda.obj (W.obj i)} (hfpXi : IsFinitePresentation B S hS fXi)
    (hfp₁i : IsFinitePresentation B S hS g₁i) (hfp₂i : IsFinitePresentation B S hS g₂i)
    {qX : X ⟶ Xi} {q₁ : Y₁ ⟶ Y₁i} {q₂ : Y₂ ⟶ Y₂i}
    (sqX : IsPullback qX fX fXi (yoneda.map (p i))) (sq₁ : IsPullback q₁ g₁ g₁i (yoneda.map (p i)))
    (sq₂ : IsPullback q₂ g₂ g₂i (yoneda.map (p i))) (c₁i : Xi ⟶ Y₁i) (c₂i : Xi ⟶ Y₂i)
    (hc₁i : c₁i ≫ g₁i = fXi) (hc₂i : c₂i ≫ g₂i = fXi) (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂)
    (hc₁ : c₁ ≫ g₁ = fX) (hc₂ : c₂ ≫ g₂ = fX) (hcq₁ : c₁ ≫ q₁ = qX ≫ c₁i)
    (hcq₂ : c₂ ≫ q₂ = qX ≫ c₂i) (ψ : Y₁ ≅ Y₂) (hψg : ψ.hom ≫ g₂ = g₁) (hψc : c₁ ≫ ψ.hom = c₂) :
    ∃ (j₁ : I) (e₁ : j₁ ⟶ i)
      (Θ : pullback g₁i (yoneda.map (W.map e₁)) ≅ pullback g₂i (yoneda.map (W.map e₁))),
      Θ.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      ψ.hom ≫ pullback.lift q₂ (g₂ ≫ yoneda.map (p j₁))
          (by rw [Category.assoc, ← Functor.map_comp, hp e₁, sq₂.w]) =
        pullback.lift q₁ (g₁ ≫ yoneda.map (p j₁))
          (by rw [Category.assoc, ← Functor.map_comp, hp e₁, sq₁.w]) ≫ Θ.hom ∧
      ∃ (j : I) (e₂ : j ⟶ j₁),
        pullback.fst (pullback.snd fXi (yoneda.map (W.map e₁))) (yoneda.map (W.map e₂)) ≫
          (pullback.lift (pullback.fst fXi (yoneda.map (W.map e₁)) ≫ c₁i)
          (pullback.snd fXi (yoneda.map (W.map e₁)))
            (by rw [Category.assoc, hc₁i, pullback.condition])) ≫ Θ.hom =
        pullback.fst (pullback.snd fXi (yoneda.map (W.map e₁))) (yoneda.map (W.map e₂)) ≫
          pullback.lift (pullback.fst fXi (yoneda.map (W.map e₁)) ≫ c₂i)
          (pullback.snd fXi (yoneda.map (W.map e₁)))
            (by rw [Category.assoc, hc₂i, pullback.condition]) := by
  obtain ⟨j₁, e₁, Θ, hΘs, hΘc⟩ :=
    exists_isPullback_iso_of_isFinitePresentationColimit P i hY₁i hY₂i hfp₁i hfp₂i sq₁ sq₂ ψ hψg
  have hT := isAlgebraicSpace_yoneda B S hS (W.obj i)
  have hT₁ := isAlgebraicSpace_yoneda B S hS (W.obj j₁)
  have hfac₁ : yoneda.map (p j₁) ≫ yoneda.map (W.map e₁) = yoneda.map (p i) := by
    rw [← Functor.map_comp, hp e₁]
  have sqX₁ := isPullback_lift_of_isPullback_of_fac B S hS sqX _ _ hfac₁
  have hX₁ := isAlgebraicSpace_pullback B S hS fXi (yoneda.map (W.map e₁)) hXi hT₁ hT
  have hY₂₁ := isAlgebraicSpace_pullback B S hS g₂i (yoneda.map (W.map e₁)) hY₂i hT₁ hT
  have hfpX₁ := isFinitePresentation_of_isPullback B S hS hX₁ hXi hT₁ hT
    (IsPullback.of_hasPullback fXi (yoneda.map (W.map e₁))) hfpXi
  have hfp₂₁ := isFinitePresentation_of_isPullback B S hS hY₂₁ hY₂i hT₁ hT
    (IsPullback.of_hasPullback g₂i (yoneda.map (W.map e₁))) hfp₂i
  -- the two morphisms to be compared at `j₁`
  let b₁ : pullback fXi (yoneda.map (W.map e₁)) ⟶ pullback g₁i (yoneda.map (W.map e₁)) :=
    pullback.lift (pullback.fst _ _ ≫ c₁i) (pullback.snd _ _)
      (by rw [Category.assoc, hc₁i, pullback.condition])
  let b₂ : pullback fXi (yoneda.map (W.map e₁)) ⟶ pullback g₂i (yoneda.map (W.map e₁)) :=
    pullback.lift (pullback.fst _ _ ≫ c₂i) (pullback.snd _ _)
      (by rw [Category.assoc, hc₂i, pullback.condition])
  have hb₁ := comp_lift_eq_lift_comp_map fXi g₁i (yoneda.map (W.map e₁)) c₁i hc₁i c₁ qX q₁ hcq₁
    (fX ≫ yoneda.map (p j₁)) (g₁ ≫ yoneda.map (p j₁)) (by rw [← Category.assoc, hc₁])
    (by rw [Category.assoc, hfac₁, sqX.w]) (by rw [Category.assoc, hfac₁, sq₁.w])
  have hb₂ := comp_lift_eq_lift_comp_map fXi g₂i (yoneda.map (W.map e₁)) c₂i hc₂i c₂ qX q₂ hcq₂
    (fX ≫ yoneda.map (p j₁)) (g₂ ≫ yoneda.map (p j₁)) (by rw [← Category.assoc, hc₂])
    (by rw [Category.assoc, hfac₁, sqX.w]) (by rw [Category.assoc, hfac₁, sq₂.w])
  have hbs₁ : b₁ ≫ pullback.snd g₁i (yoneda.map (W.map e₁)) = pullback.snd _ _ :=
    pullback.lift_snd _ _ _
  have hbs₂ : b₂ ≫ pullback.snd g₂i (yoneda.map (W.map e₁)) = pullback.snd _ _ :=
    pullback.lift_snd _ _ _
  have hu : (b₁ ≫ Θ.hom) ≫ pullback.snd g₂i (yoneda.map (W.map e₁)) = pullback.snd _ _ := by
    rw [Category.assoc, hΘs, hbs₁]
  have heqX : pullback.lift qX (fX ≫ yoneda.map (p j₁)) (by rw [Category.assoc, hfac₁, sqX.w]) ≫
      (b₁ ≫ Θ.hom) =
      pullback.lift qX (fX ≫ yoneda.map (p j₁)) (by rw [Category.assoc, hfac₁, sqX.w]) ≫ b₂ := by
    rw [← Category.assoc, ← hb₁, Category.assoc, ← hΘc, ← Category.assoc, hψc, hb₂]
  obtain ⟨j, e₂, heq⟩ := exists_eq_of_isFinitePresentationColimit P j₁ hX₁ hY₂₁ hfpX₁ hfp₂₁ sqX₁
    (b₁ ≫ Θ.hom) b₂ hu hbs₂ heqX
  refine ⟨j₁, e₁, Θ, hΘs, hΘc, j, e₂, ?_⟩
  have := congrArg (· ≫ pullback.fst _ _) heq
  simpa only [pullback.lift_fst] using this

/-- The last step of `AlgebraicGeometry.Space.exists_iso_stage_of_iso`: the base change of `Θ`
to the stage `j`. -/
theorem exists_iso_stage_of_iso_of_aux {I : Type u} [Category.{u} I] [IsCofiltered I]
    {W : I ⥤ BigFppfOver B S hS} {M : BigFppfOver B S hS}
    {p : (i : I) → (M ⟶ W.obj i)} {hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i}
    (i : I) {Y₁ Y₂ Xi Y₁i Y₂i : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g₁ : Y₁ ⟶ yoneda.obj M} {g₂ : Y₂ ⟶ yoneda.obj M}
    {fXi : Xi ⟶ yoneda.obj (W.obj i)} {g₁i : Y₁i ⟶ yoneda.obj (W.obj i)}
    {g₂i : Y₂i ⟶ yoneda.obj (W.obj i)} {q₁ : Y₁ ⟶ Y₁i} {q₂ : Y₂ ⟶ Y₂i}
    (sq₁ : IsPullback q₁ g₁ g₁i (yoneda.map (p i)))
    (sq₂ : IsPullback q₂ g₂ g₂i (yoneda.map (p i))) (c₁i : Xi ⟶ Y₁i) (c₂i : Xi ⟶ Y₂i)
    (hc₁i : c₁i ≫ g₁i = fXi) (hc₂i : c₂i ≫ g₂i = fXi) (ψ : Y₁ ≅ Y₂) (hψg : ψ.hom ≫ g₂ = g₁)
    {j₁ : I} (e₁ : j₁ ⟶ i)
    (Θ : pullback g₁i (yoneda.map (W.map e₁)) ≅ pullback g₂i (yoneda.map (W.map e₁)))
    (hΘs : Θ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hΘc : ψ.hom ≫ pullback.lift q₂ (g₂ ≫ yoneda.map (p j₁))
          (by rw [Category.assoc, ← Functor.map_comp, hp e₁, sq₂.w]) =
        pullback.lift q₁ (g₁ ≫ yoneda.map (p j₁))
          (by rw [Category.assoc, ← Functor.map_comp, hp e₁, sq₁.w]) ≫ Θ.hom)
    {j : I} (e₂ : j ⟶ j₁)
    (heq' : pullback.fst (pullback.snd fXi (yoneda.map (W.map e₁))) (yoneda.map (W.map e₂)) ≫
          (pullback.lift (pullback.fst fXi (yoneda.map (W.map e₁)) ≫ c₁i)
          (pullback.snd fXi (yoneda.map (W.map e₁)))
            (by rw [Category.assoc, hc₁i, pullback.condition])) ≫ Θ.hom =
        pullback.fst (pullback.snd fXi (yoneda.map (W.map e₁))) (yoneda.map (W.map e₂)) ≫
          pullback.lift (pullback.fst fXi (yoneda.map (W.map e₁)) ≫ c₂i)
          (pullback.snd fXi (yoneda.map (W.map e₁)))
            (by rw [Category.assoc, hc₂i, pullback.condition])) :
    ∃ (e : j ⟶ i) (Xj Y₁j Y₂j : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (fXj : Xj ⟶ yoneda.obj (W.obj j)) (g₁j : Y₁j ⟶ yoneda.obj (W.obj j))
      (g₂j : Y₂j ⟶ yoneda.obj (W.obj j)) (rX : Xj ⟶ Xi) (r₁ : Y₁j ⟶ Y₁i) (r₂ : Y₂j ⟶ Y₂i)
      (c₁j : Xj ⟶ Y₁j) (c₂j : Xj ⟶ Y₂j) (q₁j : Y₁ ⟶ Y₁j) (q₂j : Y₂ ⟶ Y₂j)
      (ψj : Y₁j ≅ Y₂j),
      IsPullback rX fXj fXi (yoneda.map (W.map e)) ∧ IsPullback r₁ g₁j g₁i (yoneda.map (W.map e)) ∧
      IsPullback r₂ g₂j g₂i (yoneda.map (W.map e)) ∧ c₁j ≫ g₁j = fXj ∧ c₂j ≫ g₂j = fXj ∧
      c₁j ≫ r₁ = rX ≫ c₁i ∧ c₂j ≫ r₂ = rX ≫ c₂i ∧ ψj.hom ≫ g₂j = g₁j ∧ c₁j ≫ ψj.hom = c₂j ∧
      q₁j ≫ r₁ = q₁ ∧ q₂j ≫ r₂ = q₂ ∧ q₁j ≫ g₁j = g₁ ≫ yoneda.map (p j) ∧
      q₂j ≫ g₂j = g₂ ≫ yoneda.map (p j) ∧ ψ.hom ≫ q₂j = q₁j ≫ ψj.hom := by
  have hfac₁ : yoneda.map (p j₁) ≫ yoneda.map (W.map e₁) = yoneda.map (p i) := by
    rw [← Functor.map_comp, hp e₁]
  have hfac₂ : yoneda.map (p j) ≫ yoneda.map (W.map e₂) = yoneda.map (p j₁) := by
    rw [← Functor.map_comp, hp e₂]
  have hfac : yoneda.map (W.map e₂) ≫ yoneda.map (W.map e₁) = yoneda.map (W.map (e₂ ≫ e₁)) := by
    rw [W.map_comp, Functor.map_comp]
  have paste : ∀ {Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : Zi ⟶ yoneda.obj (W.obj i)),
      IsPullback (pullback.fst (pullback.snd h (yoneda.map (W.map e₁))) (yoneda.map (W.map e₂)) ≫
          pullback.fst h (yoneda.map (W.map e₁)))
        (pullback.snd (pullback.snd h (yoneda.map (W.map e₁))) (yoneda.map (W.map e₂))) h
        (yoneda.map (W.map (e₂ ≫ e₁))) := by
    intro Zi h
    rw [← hfac]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  obtain ⟨ψj, hψjs, hψjf, hψjc⟩ := exists_iso_pullback_comp_eq (yoneda.map (W.map e₂)) _ _
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) Θ hΘs heq'
  refine ⟨e₂ ≫ e₁, _, _, _,
    pullback.snd (pullback.snd fXi (yoneda.map (W.map e₁))) (yoneda.map (W.map e₂)),
    pullback.snd (pullback.snd g₁i (yoneda.map (W.map e₁))) (yoneda.map (W.map e₂)),
    pullback.snd (pullback.snd g₂i (yoneda.map (W.map e₁))) (yoneda.map (W.map e₂)), _, _, _, _, _,
    pullback.lift (pullback.lift q₁ (g₁ ≫ yoneda.map (p j₁))
        (by rw [Category.assoc, hfac₁, sq₁.w])) (g₁ ≫ yoneda.map (p j))
        (by rw [pullback.lift_snd, Category.assoc, hfac₂]),
    pullback.lift (pullback.lift q₂ (g₂ ≫ yoneda.map (p j₁))
        (by rw [Category.assoc, hfac₁, sq₂.w])) (g₂ ≫ yoneda.map (p j))
        (by rw [pullback.lift_snd, Category.assoc, hfac₂]),
    ψj, paste fXi, paste g₁i, paste g₂i, pullback.lift_snd _ _ _, pullback.lift_snd _ _ _, ?_, ?_,
    hψjs, hψjc, ?_, ?_, pullback.lift_snd _ _ _, pullback.lift_snd _ _ _,
    comp_lift_eq_lift_comp_of_iso Θ ψj hψjs hψjf ψ _ _ _ _
      (by rw [← Category.assoc, hψg]) hΘc _ _⟩
  · rw [pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst, Category.assoc]
  · rw [pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst, Category.assoc]
  · rw [pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [pullback.lift_fst_assoc, pullback.lift_fst]

/-- **Spreading out an isomorphism compatible with two morphisms.** Over the vertex `M` of a
cofiltered system, let `X`, `Y₁`, `Y₂` be base changes, through cartesian squares, of algebraic
spaces of finite presentation `Xᵢ`, `Y₁ᵢ`, `Y₂ᵢ` over a stage, and `cₖ : X ⟶ Yₖ` base changes of
morphisms `cₖᵢ` over the stage. An isomorphism `ψ : Y₁ ≅ Y₂` over `M` with `c₁ ≫ ψ = c₂` is the
base change of an isomorphism over a later stage `j`, between base changes of the `Yₖᵢ` along
`W j ⟶ W i`, compatible with the base changes of the `cₖᵢ` ([Stacks, Tag 07SK]). -/
theorem exists_iso_stage_of_iso {I : Type u} [Category.{u} I] [IsCofiltered I]
    {W : I ⥤ BigFppfOver B S hS} {M : BigFppfOver B S hS}
    {p : (i : I) → (M ⟶ W.obj i)} {hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i}
    (P : FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS W M p hp) (i : I)
    {X Y₁ Y₂ Xi Y₁i Y₂i : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXi : IsAlgebraicSpace B S hS Xi)
    (hY₁i : IsAlgebraicSpace B S hS Y₁i) (hY₂i : IsAlgebraicSpace B S hS Y₂i)
    {fX : X ⟶ yoneda.obj M} {g₁ : Y₁ ⟶ yoneda.obj M} {g₂ : Y₂ ⟶ yoneda.obj M}
    {fXi : Xi ⟶ yoneda.obj (W.obj i)} {g₁i : Y₁i ⟶ yoneda.obj (W.obj i)}
    {g₂i : Y₂i ⟶ yoneda.obj (W.obj i)} (hfpXi : IsFinitePresentation B S hS fXi)
    (hfp₁i : IsFinitePresentation B S hS g₁i) (hfp₂i : IsFinitePresentation B S hS g₂i)
    {qX : X ⟶ Xi} {q₁ : Y₁ ⟶ Y₁i} {q₂ : Y₂ ⟶ Y₂i}
    (sqX : IsPullback qX fX fXi (yoneda.map (p i))) (sq₁ : IsPullback q₁ g₁ g₁i (yoneda.map (p i)))
    (sq₂ : IsPullback q₂ g₂ g₂i (yoneda.map (p i))) (c₁i : Xi ⟶ Y₁i) (c₂i : Xi ⟶ Y₂i)
    (hc₁i : c₁i ≫ g₁i = fXi) (hc₂i : c₂i ≫ g₂i = fXi) (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂)
    (hc₁ : c₁ ≫ g₁ = fX) (hc₂ : c₂ ≫ g₂ = fX) (hcq₁ : c₁ ≫ q₁ = qX ≫ c₁i)
    (hcq₂ : c₂ ≫ q₂ = qX ≫ c₂i) (ψ : Y₁ ≅ Y₂) (hψg : ψ.hom ≫ g₂ = g₁) (hψc : c₁ ≫ ψ.hom = c₂) :
    ∃ (j : I) (e : j ⟶ i) (Xj Y₁j Y₂j : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (fXj : Xj ⟶ yoneda.obj (W.obj j)) (g₁j : Y₁j ⟶ yoneda.obj (W.obj j))
      (g₂j : Y₂j ⟶ yoneda.obj (W.obj j)) (rX : Xj ⟶ Xi) (r₁ : Y₁j ⟶ Y₁i) (r₂ : Y₂j ⟶ Y₂i)
      (c₁j : Xj ⟶ Y₁j) (c₂j : Xj ⟶ Y₂j) (q₁j : Y₁ ⟶ Y₁j) (q₂j : Y₂ ⟶ Y₂j)
      (ψj : Y₁j ≅ Y₂j),
      IsPullback rX fXj fXi (yoneda.map (W.map e)) ∧ IsPullback r₁ g₁j g₁i (yoneda.map (W.map e)) ∧
      IsPullback r₂ g₂j g₂i (yoneda.map (W.map e)) ∧ c₁j ≫ g₁j = fXj ∧ c₂j ≫ g₂j = fXj ∧
      c₁j ≫ r₁ = rX ≫ c₁i ∧ c₂j ≫ r₂ = rX ≫ c₂i ∧ ψj.hom ≫ g₂j = g₁j ∧ c₁j ≫ ψj.hom = c₂j ∧
      q₁j ≫ r₁ = q₁ ∧ q₂j ≫ r₂ = q₂ ∧ q₁j ≫ g₁j = g₁ ≫ yoneda.map (p j) ∧
      q₂j ≫ g₂j = g₂ ≫ yoneda.map (p j) ∧ ψ.hom ≫ q₂j = q₁j ≫ ψj.hom := by
  obtain ⟨j₁, e₁, Θ, hΘs, hΘc, j, e₂, heq'⟩ := exists_iso_stage_of_iso_aux P i hXi hY₁i hY₂i
    hfpXi hfp₁i hfp₂i sqX sq₁ sq₂ c₁i c₂i hc₁i hc₂i c₁ c₂ hc₁ hc₂ hcq₁ hcq₂ ψ hψg hψc
  exact ⟨j, exists_iso_stage_of_iso_of_aux (hp := hp) i sq₁ sq₂ c₁i c₂i hc₁i hc₂i ψ hψg e₁ Θ
    hΘs hΘc e₂ heq'⟩

end General

section Integers

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

variable (B) in
/-- The spectrum of a ring essentially of finite type over the integers is in every big fppf
site: such a ring is countable. -/
theorem contains_spec_of_essFiniteType (R : Type u) [CommRing R] [Algebra.EssFiniteType ℤ R] :
    B.Contains (Spec (.of R)) := by
  have hl := IsLocalization.cardinalMk_le (Algebra.EssFiniteType.submonoid ℤ R) (L := R)
  have ha := Algebra.lift_cardinalMk_adjoin_le ℤ ((Algebra.EssFiniteType.finset ℤ R : Set R))
  have hs : Cardinal.mk (Algebra.EssFiniteType.subalgebra ℤ R) ≤ Cardinal.aleph0 := by
    have h' : Cardinal.lift.{0} (Cardinal.mk (Algebra.EssFiniteType.subalgebra ℤ R)) ≤
        Cardinal.aleph0 := by
      refine ha.trans (max_le (max_le ?_ ?_) le_rfl)
      · simp
      · exact Cardinal.lift_le_aleph0.2 (Cardinal.mk_le_aleph0_iff.2 inferInstance)
    exact Cardinal.lift_le_aleph0.1 h'
  change (Spec (.of R)).size < B.cutoff
  rw [Scheme.size_Spec]
  exact lt_of_le_of_lt (max_le le_rfl (hl.trans hs)) B.aleph0_lt_cutoff

variable (B) in
/-- The spectrum of the residue field of a local ring whose spectrum is in the site is in the
site. -/
theorem contains_spec_residueField_of_contains (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : B.Contains (Spec (.of R))) : B.Contains (Spec (.of (ResidueField R))) := by
  change (Spec (.of (ResidueField R))).size < B.cutoff
  rw [Scheme.size_Spec]
  refine lt_of_le_of_lt (max_le_max le_rfl
    (Cardinal.mk_le_of_surjective (IsLocalRing.residue_surjective (R := R)))) ?_
  have : (Spec (.of R)).size < B.cutoff := hR
  rwa [Scheme.size_Spec] at this

/-- The identity of a ring is essentially of finite presentation. -/
theorem essentiallyOfFinitePresentation_algebraMap_self (A : Type u) [CommRing A] :
    (algebraMap A A).EssentiallyOfFinitePresentation := by
  unfold RingHom.EssentiallyOfFinitePresentation
  exact ⟨A, inferInstance, Algebra.id A, Algebra.id A, IsScalarTower.of_algebraMap_eq fun _ => rfl,
    Algebra.FinitePresentation.self A, ⊥, IsLocalization.self bot_le⟩

/-- The spectra of the stages of a directed system of rings, as a diagram of the big fppf site of
the integers. -/
def specStageDiagram {Λ : Type u} [Preorder Λ] (R : Λ ⥤ CommRingCat.{u})
    (hR : ∀ i, B.Contains (Spec (R.obj i))) : Λᵒᵖ ⥤ BigFppfOver B integerBase hZ where
  obj i := integerSiteObject B hZ (hR i.unop)
  map {i j} e := integerSiteMap B hZ (hR i.unop) (hR j.unop) (Spec.map (R.map e.unop))
  map_id i := by
    rw [unop_id, R.map_id, Spec.map_id]
    exact integerSiteMap_id
  map_comp {i j k} e e' := by
    rw [unop_comp, R.map_comp, Spec.map_comp]
    exact (integerSiteMap_comp _ _).symm

/-- The cone of a cocone of rings, with vertex an object of the site identified with the spectrum
of the vertex of the cocone. -/
def specStageCone {Λ : Type u} [Preorder Λ] (R : Λ ⥤ CommRingCat.{u})
    (hR : ∀ i, B.Contains (Spec (R.obj i))) {A : CommRingCat.{u}}
    (ρ : R ⟶ (Functor.const Λ).obj A) {W : BigFppfOver B integerBase hZ}
    (ε : (𝒯).obj W ≅ Spec A) : Cone (specStageDiagram (hZ := hZ) R hR) where
  pt := W
  π :=
    { app i := Over.homMk (ObjectProperty.homMk (ε.hom ≫ Spec.map (ρ.app i.unop)))
        (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
      naturality {i j} e := by
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        change 𝟙 _ ≫ ε.hom ≫ Spec.map (ρ.app j.unop) =
          (ε.hom ≫ Spec.map (ρ.app i.unop)) ≫ Spec.map (R.map e.unop)
        rw [Category.id_comp, Category.assoc, ← Spec.map_comp, ρ.naturality]
        simp }

/-- The image in schemes of the leg of `specStageCone` at `i` is `ε.hom` followed by the
spectrum of the cocone map at `i`. -/
theorem toScheme_map_specStageCone_π {Λ : Type u} [Preorder Λ] (R : Λ ⥤ CommRingCat.{u})
    (hR : ∀ i, B.Contains (Spec (R.obj i))) {A : CommRingCat.{u}}
    (ρ : R ⟶ (Functor.const Λ).obj A) {W : BigFppfOver B integerBase hZ}
    (ε : (𝒯).obj W ≅ Spec A) (i : Λᵒᵖ) :
    (𝒯).map ((specStageCone R hR ρ ε).π.app i) = ε.hom ≫ Spec.map (ρ.app i.unop) :=
  rfl

/-- **The spectrum of a filtered colimit of rings is the limit of the spectra, in the site.** -/
def isLimitSpecStageCone {Λ : Type u} [Preorder Λ] (R : Λ ⥤ CommRingCat.{u})
    (hR : ∀ i, B.Contains (Spec (R.obj i))) {A : CommRingCat.{u}}
    (ρ : R ⟶ (Functor.const Λ).obj A) (hρ : IsColimit (Cocone.mk A ρ))
    {W : BigFppfOver B integerBase hZ} (ε : (𝒯).obj W ≅ Spec A) :
    IsLimit ((𝒯).mapCone (specStageCone R hR ρ ε)) :=
  let hl : IsLimit (Scheme.Spec.mapCone (Cocone.mk A ρ).op) :=
    isLimitOfPreserves Scheme.Spec hρ.op
  let α : R.op ⋙ Scheme.Spec ≅ specStageDiagram (hZ := hZ) R hR ⋙ 𝒯 :=
    NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} e => by
      simp only [Iso.refl_hom]
      rfl)
  ((IsLimit.postcomposeHomEquiv α _).symm hl).ofIsoLimit (Cone.ext ε.symm fun i => by
    change Spec.map (ρ.app i.unop) ≫ 𝟙 _ = ε.inv ≫ ε.hom ≫ Spec.map (ρ.app i.unop)
    simp)

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **[Stacks, Tag 0E89] over a local ring.** Let `W` be an object of the big fppf site of the
integers whose underlying scheme is, through `ε`, the spectrum of a local ring `A`, let `X`,
`Y₁`, `Y₂` be families of curves over `W` (flat, proper, of finite presentation and, for `X` and
`Y₁`, of relative dimension at most one) and `cᵢ : X ⟶ Yᵢ` morphisms over `W`. Let `k : K ⟶ W`
be, through `ι` and `ε`, the closed point. Suppose the fibres of `X` and `Y₁` over `k` are
presented by schemes `F_X`, `F₁` on which the fibre `a₁` of `c₁` satisfies `𝒪 ≅ a₁,* 𝒪` and
`R¹a₁,* 𝒪 = 0`, and that `φ` identifies the fibres of `Y₁` and `Y₂` over `k` compatibly with the
`cᵢ`. Then there is an isomorphism `Y₁ ≅ Y₂` over `W`, compatible with the `cᵢ` and with `φ`.

The proof is the source's: `A` is the filtered colimit of local rings `A_λ` essentially of finite
type over `ℤ`, hence Noetherian, with local transition maps
(`Stacks.SpreadingOut.LocalModuleSystem.exists_ringSystem_of_essentiallyOfFinitePresentation`);
the data descend to a stage (`AlgebraicGeometry.Space.exists_isPullback_stage_model`, from
[Stacks, Tags 07SK, 08K0, 08K1]), where the Noetherian local case applies
(`AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isPullback_noetherianStage`). -/
theorem exists_iso_of_closedFibre_of_isLocalRing_of_siteObject (A : Type u) [CommRing A]
    [IsLocalRing A] {W : BigFppfOver B integerBase hZ} (ε : (𝒯).obj W ≅ Spec (.of A))
    {X Y₁ Y₂ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B integerBase hZ X) (hY₁ : IsAlgebraicSpace B integerBase hZ Y₁)
    (hY₂ : IsAlgebraicSpace B integerBase hZ Y₂)
    (fX : X ⟶ yoneda.obj W) (g₁ : Y₁ ⟶ yoneda.obj W) (g₂ : Y₂ ⟶ yoneda.obj W)
    (hflX : IsFlat B integerBase hZ fX) (hprX : IsProper B integerBase hZ fX)
    (hfpX : IsFinitePresentation B integerBase hZ fX)
    (hdX : HasRelativeDimensionLE 1 B integerBase hZ fX)
    (hfl₁ : IsFlat B integerBase hZ g₁) (hpr₁ : IsProper B integerBase hZ g₁)
    (hfp₁ : IsFinitePresentation B integerBase hZ g₁)
    (hd₁ : HasRelativeDimensionLE 1 B integerBase hZ g₁)
    (hfl₂ : IsFlat B integerBase hZ g₂) (hpr₂ : IsProper B integerBase hZ g₂)
    (hfp₂ : IsFinitePresentation B integerBase hZ g₂)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = fX) (hc₂ : c₂ ≫ g₂ = fX)
    {K : BigFppfOver B integerBase hZ} (k : K ⟶ W) (ι : Spec (.of (ResidueField A)) ≅ (𝒯).obj K)
    (hι : ι.hom ≫ (𝒯).map k ≫ ε.hom = ContractionUniquenessComplete.closedPoint A)
    {FX F₁ : BigFppfOver B integerBase hZ} (eX : yoneda.obj FX ≅ pullback fX (yoneda.map k))
    (e₁ : yoneda.obj F₁ ≅ pullback g₁ (yoneda.map k)) (tX : FX ⟶ K) (t₁ : F₁ ⟶ K)
    (heX : eX.hom ≫ pullback.snd fX (yoneda.map k) = yoneda.map tX)
    (he₁ : e₁.hom ≫ pullback.snd g₁ (yoneda.map k) = yoneda.map t₁) (a₁ : FX ⟶ F₁)
    (ha₁ : yoneda.map a₁ ≫ e₁.hom =
      eX.hom ≫ pullback.map fX (yoneda.map k) g₁ (yoneda.map k) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁])
        (by simp))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁)))
    (φ : pullback g₁ (yoneda.map k) ≅ pullback g₂ (yoneda.map k))
    (hφ : φ.hom ≫ pullback.snd g₂ (yoneda.map k) = pullback.snd g₁ (yoneda.map k))
    (hφc : pullback.map fX (yoneda.map k) g₁ (yoneda.map k) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁])
        (by simp) ≫ φ.hom =
      pullback.map fX (yoneda.map k) g₂ (yoneda.map k) c₂ (𝟙 _) (𝟙 _) (by simp [hc₂])
        (by simp)) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ g₂ = g₁ ∧ c₁ ≫ ψ.hom = c₂ ∧
      pullback.fst g₁ (yoneda.map k) ≫ ψ.hom = φ.hom ≫ pullback.fst g₂ (yoneda.map k) := by
  classical
  obtain ⟨Λ, instP, instNe, instDir, R, -, -, ρ, -, hcolim, -, -, hRloc, -, -, hρloc, -, hess,
      -, -⟩ :=
    Stacks.SpreadingOut.LocalModuleSystem.exists_ringSystem_of_essentiallyOfFinitePresentation
      (R := A) (S := A) (essentiallyOfFinitePresentation_algebraMap_self A)
  let := instP
  have := instNe
  have := instDir
  have hcont : ∀ i, B.Contains (Spec (R.obj i)) := fun i => by
    have := hess i
    exact contains_spec_of_essFiniteType B (R.obj i)
  have hc := isLimitSpecStageCone (hZ := hZ) R hcont ρ hcolim ε
  have hD : ∀ j, IsAffine ((𝒯).obj ((specStageDiagram (hZ := hZ) R hcont).obj j)) := fun j => by
    change IsAffine (Spec _)
    infer_instance
  obtain ⟨M, X₀, Y₁₀, Y₂₀, f₀, g₁₀, g₂₀, c₁₀, c₂₀, qX, q₁, q₂, hX₀, hY₁₀, hY₂₀, hfl₀, hpr₀, hfp₀,
      hfl₁₀, hpr₁₀, hfp₁₀, hfl₂₀, hpr₂₀, -, hc₁₀, hc₂₀, sqX, sq₁, sq₂, hcq₁, hcq₂⟩ :=
    exists_isPullback_stage_model _ hD _ hc hX hY₁ hY₂ fX g₁ g₂ hflX hprX hfpX hfl₁ hpr₁ hfp₁
      hfl₂ hpr₂ hfp₂ c₁ c₂ hc₁ hc₂
  -- the Noetherian local stage
  have : IsLocalRing (R.obj M.unop) := hRloc M.unop
  have : Algebra.EssFiniteType ℤ (R.obj M.unop) := hess M.unop
  have : IsNoetherianRing (R.obj M.unop) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have : IsLocalHom (ρ.app M.unop).hom := hρloc M.unop
  have hκ := contains_spec_residueField_of_contains B (R.obj M.unop) (hcont M.unop)
  -- the closed point of the stage, under the closed point of `W`
  let φκ : ResidueField (R.obj M.unop) →+* ResidueField A := ResidueField.map (ρ.app M.unop).hom
  let mmap : (𝒯).obj K ⟶ Spec (.of (ResidueField (R.obj M.unop))) :=
    ι.inv ≫ Spec.map (CommRingCat.ofHom φκ)
  let m : K ⟶ integerSiteObject B hZ hκ :=
    Over.homMk (ObjectProperty.homMk mmap)
      (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  have hkm : k ≫ (specStageCone (hZ := hZ) R hcont ρ ε).π.app M =
      m ≫ closedPointSiteMap (R.obj M.unop) (hcont M.unop) hκ := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change (𝒯).map k ≫ ε.hom ≫ Spec.map (ρ.app M.unop) =
      mmap ≫ Spec.map (CommRingCat.ofHom (residue (R.obj M.unop)))
    have hk : (𝒯).map k ≫ ε.hom = ι.inv ≫ ContractionUniquenessComplete.closedPoint A := by
      rw [← hι]
      simp
    rw [← Category.assoc, hk, Category.assoc]
    simp only [mmap, Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have haff : IsAffine ((𝒯).obj K) := .of_isIso ι.inv
  have haff₀ : IsAffine ((𝒯).obj (integerSiteObject B hZ hκ)) := by
    change IsAffine (Spec _)
    infer_instance
  let := φκ.toAlgebra
  have hmfl : Flat ((𝒯).map m) := by
    change Flat (ι.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _)))
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField (R.obj M.unop))
        (ResidueField A)))) :=
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
    infer_instance
  have hmsu : Surjective ((𝒯).map m) := by
    change Surjective (ι.inv ≫ Spec.map (CommRingCat.ofHom φκ))
    have : Surjective (Spec.map (CommRingCat.ofHom φκ)) :=
      (AlgebraicGeometry.surjective_iff _).2 (Function.surjective_to_subsingleton _)
    infer_instance
  have hm : IsFpqcCovering B integerBase hZ (fun _ : Unit => yoneda.map m) :=
    isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective B integerBase hZ
      (X := schemeSpace K) (Y := schemeSpace (integerSiteObject B hZ hκ))
      (ObjectProperty.homMk (yoneda.map m))
      (isQuasiCompact_yoneda_map_of_isAffineHom B integerBase hZ m
        (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))
      (isFlat_yoneda_map B integerBase hZ m hmfl)
      (isSurjective_yoneda_map B integerBase hZ m hmsu)
  exact exists_iso_of_closedFibre_of_isPullback_noetherianStage (R.obj M.unop) (hcont M.unop) hκ
    hX₀ hY₁₀ hY₂₀ f₀ g₁₀ g₂₀ hfl₀ hpr₀ hfp₀ hfl₁₀ hpr₁₀ hfp₁₀ hfl₂₀ hpr₂₀ c₁₀ c₂₀ hc₁₀ hc₂₀
    ((specStageCone (hZ := hZ) R hcont ρ ε).π.app M) hX hY₁ hY₂ fX g₁ g₂ qX q₁ q₂ sqX sq₁ sq₂
    hdX hd₁ c₁ c₂ hc₁ hc₂ hcq₁ hcq₂ k m hkm hm eX e₁ tX t₁ heX he₁ a₁ ha₁ h0 hR φ hφ hφc

end Integers

end AlgebraicGeometry.Space

end
