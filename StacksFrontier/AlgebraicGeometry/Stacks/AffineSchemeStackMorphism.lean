module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalSchemePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# Affine 1-morphisms and stacks representable by affine schemes

A 1-morphism `c : (Sch/A)_fppf ⟶ (Sch/A')_fppf` between the algebraic stacks of two affine
schemes of the site is affine in the sense of **Stacks 0CHQ**: it is representable by algebraic
spaces (both its source and target are, **Stacks 02ZZ**), and its morphism of representing
presheaves is `h_g : h_A ⟶ h_{A'}` for the morphism of the site `g` underlying `c`, a morphism of
affine schemes, hence affine; the relative condition of Stacks 04XB follows by base change
(**Stacks 03WI**).

## Main results

* `AlgebraicGeometry.Space.affineMorphismProperty_isStableUnderBaseChange`: **Stacks 03WI** as a
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` instance on algebraic spaces.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_of_isAffineRepresentable`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineRepresentable_of_isAffineHom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03WI**: affineness of morphisms of algebraic spaces over `S` is stable under base
change. -/
instance affineMorphismProperty_isStableUnderBaseChange :
    (affineMorphismProperty B S hS).IsStableUnderBaseChange where
  of_isPullback sq hf := IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq) hf

/-- **Affineness of a morphism of presheaves may be read off its base changes along morphisms from
representable presheaves**: if every base change of `k` along a morphism `yoneda.obj V ⟶ Y` is
affine, then `k` is affine. A base change of `k` to an affine scheme is the base change, along the
identity, of the base change of `k` along that scheme. -/
theorem isAffineHom_of_forall_yoneda {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (h : ∀ (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y), IsAffineHom B S hS (pullback.fst v k)) :
    IsAffineHom B S hS k := by
  intro Z g
  obtain ⟨W, p, q, hpq⟩ := h _ g Z (𝟙 _)
  refine ⟨W, p ≫ pullback.snd g k, q, ?_⟩
  simpa using IsPullback.paste_horiz hpq (IsPullback.of_hasPullback g k).flip

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism between algebraic stacks representable by affine schemes is affine**
(**Stacks 0CHQ**). Both stacks are represented by the algebraic spaces `h_A`, `h_{A'}`, so the
1-morphism is representable by algebraic spaces (**Stacks 02ZZ**); its morphism of representing
presheaves `h_A ⟶ h_{A'}` is `h_g` for a morphism `g` of affine schemes, which is affine, and the
condition of Stacks 04XB follows by base change (**Stacks 03WI**). -/
theorem isAffineHom_of_isAffineRepresentable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (h𝒳 : IsAffineRepresentable B S hS 𝒳) (h𝒴 : IsAffineRepresentable B S hS 𝒴) (c : 𝒳 ⟶ 𝒴) :
    IsAffineHom B S hS c := by
  obtain ⟨A, hA, ⟨E⟩⟩ := h𝒳
  obtain ⟨A', hA', ⟨E'⟩⟩ := h𝒴
  let eA := E.trans (PresheafOfCategories.sliceElementsEquivalenceOver A)
  let eA' := E'.trans (PresheafOfCategories.sliceElementsEquivalenceOver A')
  refine ⟨isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS c.hom
    ⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A, ⟨eA⟩⟩
    ⟨yoneda.obj A', isAlgebraicSpace_yoneda B S hS A', ⟨eA'⟩⟩, ?_⟩
  intro U y hy T hT he
  refine relativeProperty_of_prop_representingMap B S hS (Space.affineMorphismProperty B S hS)
    c.hom (yoneda.obj A) (yoneda.obj A') (isAlgebraicSpace_yoneda B S hS A)
    (isAlgebraicSpace_yoneda B S hS A') eA eA' ?_ U y hy T hT he
  rw [← yoneda.map_preimage
    (representingMap B S hS 𝒳.val 𝒴.val (yoneda.obj A) (yoneda.obj A') eA eA' c.hom)]
  refine Space.isAffineHom_of_presheaf ?_
  refine (Space.presheaf_yoneda_map_iff B S hS
    (P := @AlgebraicGeometry.IsAffineHom.{u}) inferInstance _).2 ?_
  infer_instance

/-- **The source of an affine 1-morphism into a stack representable by an affine scheme is
representable by an affine scheme.** The source is represented by an algebraic space `Z`
(**Stacks 0300**), the induced morphism `Z ⟶ h_A` is affine (the forward half of
**Stacks 04XC**), and its base change along the identity of the affine `A` is represented by an
affine scheme, by **Stacks 03WF**. -/
theorem isAffineRepresentable_of_isAffineHom {𝒵 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (h𝒴 : IsAffineRepresentable B S hS 𝒴) (k : 𝒵 ⟶ 𝒴) (hk : IsAffineHom B S hS k) :
    IsAffineRepresentable B S hS 𝒵 := by
  obtain ⟨A, hA, ⟨E⟩⟩ := h𝒴
  let eG := E.trans (PresheafOfCategories.sliceElementsEquivalenceOver A)
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := isRepresentableByAlgebraicSpace_of_representable B S hS 𝒵.val
    𝒴.val k.hom hk.1 ⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A, ⟨eG⟩⟩
  obtain ⟨W, p, q, hpq⟩ := prop_representingMap_of_relativeProperty B S hS
    (Space.affineMorphismProperty B S hS) k.hom Z (yoneda.obj A) hZ
    (isAlgebraicSpace_yoneda B S hS A) eZ eG
    (fun _ _ _ _ m hm => Space.isAffineHom_of_forall_yoneda B S hS m hm) hk.1 hk.2 ⟨A, hA⟩ (𝟙 _)
  have : IsIso p := hpq.isIso_fst_of_isIso
  exact ⟨(BigAffineFppf.inclusion B S hS).obj W, W.property,
    ⟨eZ.trans ((PresheafOfCategories.equivalenceOverOfIso (asIso p).symm).trans
      (PresheafOfCategories.sliceElementsEquivalenceOver _).symm)⟩⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
