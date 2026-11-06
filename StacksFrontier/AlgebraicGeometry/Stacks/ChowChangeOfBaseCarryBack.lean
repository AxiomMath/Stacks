module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowChangeOfBaseTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocusChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.ChangeOfBaseUniversallyClosed

/-!
# Carrying a Chow cover back along a change of base

Let `g : S ⟶ S'` be a morphism of a big fppf site and `Λ` the lower-shriek extension of
Stacks 03I5 (2) along `g`. By Stacks 04SG an algebraic space over `S'` with a morphism to the
representable presheaf of `S` is the extension of an algebraic space over `S`, and morphisms over
that presheaf come from morphisms over `S`. This file proves those two facts in the form the
reduction of Chow's lemma for algebraic stacks (Stacks 0CQ8) to the base `Spec ℤ` needs.

## Main results

* `AlgebraicGeometry.Space.exists_relocalize_iso_of_structureMap`: an algebraic space over `S'`
  over the representable presheaf of `S` is `Λ F` for an algebraic space `F` over `S`.
* `AlgebraicGeometry.Space.exists_relocalize_map_eq`: a morphism `Λ F ⟶ Λ G` compatible with the
  structural morphisms is `Λ v` for a morphism `v : F ⟶ G`.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- The structural morphism of the image of `F` under the presheaf equivalence of Stacks 04SG is
the structural morphism of the lower-shriek extension, read through
`AlgebraicGeometry.smallerBasePresheafForgetIso`. -/
theorem smallerBasePresheafEquivalence_functor_obj_hom (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    ((smallerBasePresheafEquivalence B S S' hS hS' g).functor.obj F).hom =
      ((smallerBasePresheafForgetIso B S S' hS hS' g).hom.app F) ≫
        OverShriek.viewStructureMap g F := by
  ext W s
  apply Over.OverMorphism.ext
  rfl

/-- The forgetful isomorphism of Stacks 04SG is natural, read on the underlying morphisms of the
presheaf equivalence. -/
private theorem smallerBasePresheafEquivalence_map_left_comp {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : F ⟶ G) :
    ((smallerBasePresheafEquivalence B S S' hS hS' g).functor.map v).left ≫
        (smallerBasePresheafForgetIso B S S' hS hS' g).hom.app G =
      (smallerBasePresheafForgetIso B S S' hS hS' g).hom.app F ≫
        (OverShriek.relocalizePresheafFunctor g).map v :=
  (smallerBasePresheafForgetIso B S S' hS hS' g).hom.naturality v

/-- **The converse of Stacks 03I5 part (2).** If the lower-shriek extension of `F` along `g` is
an algebraic space over `S'`, then `F` is an algebraic space over `S`: `F` is the fibre product of
the restriction of the extension with the representable presheaf of the identity of `S`
(`CategoryTheory.OverShriek.isPullback_relocalizeUnit`), all algebraic spaces by
Stacks 03I5 (1). -/
theorem isAlgebraicSpace_of_isAlgebraicSpace_relocalizePresheaf
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hΛ : IsAlgebraicSpace B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F)) :
    IsAlgebraicSpace B S hS F := by
  have hH : IsAlgebraicSpace B S hS
      ((OverShriek.relocalizeRestrict g).obj (yoneda.obj (Over.mk g))) :=
    isAlgebraicSpace_relocalizeRestrict B S S' hS hS' g (yoneda.obj (Over.mk g))
      (isAlgebraicSpace_yoneda B S' hS' (Over.mk g))
  exact isAlgebraicSpace_of_isPullback
    (isAlgebraicSpace_relocalizeRestrict B S S' hS hS' g _ hΛ)
    (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS))))
    hH.isSheaf hH.diagonal_representable (OverShriek.isPullback_relocalizeUnit g F)

/-- **Stacks 04SG, essential surjectivity with algebraicity.** An algebraic space `Q` over `S'`
with a morphism `π` to the representable presheaf of `g` is the lower-shriek extension of an
algebraic space over `S`, compatibly with the two morphisms to that representable presheaf: the
presheaf is produced by `AlgebraicGeometry.smallerBasePresheafEquivalence`. -/
theorem exists_relocalize_iso_of_structureMap
    {Q : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S' hS' Q)
    (π : Q ⟶ yoneda.obj (Over.mk g)) :
    ∃ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS F)
      (e : (OverShriek.relocalizePresheafFunctor g).obj F ≅ Q),
      e.hom ≫ π = OverShriek.viewStructureMap g F := by
  let E := smallerBasePresheafEquivalence B S S' hS hS' g
  let Qπ : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) := Over.mk π
  let F := E.inverse.obj Qπ
  let c := E.counitIso.app Qπ
  let e : (OverShriek.relocalizePresheafFunctor g).obj F ≅ Q :=
    ((smallerBasePresheafForgetIso B S S' hS hS' g).app F).symm ≪≫
      (Over.forget (yoneda.obj (Over.mk g))).mapIso c
  have he : e.hom ≫ π = OverShriek.viewStructureMap g F := by
    have hc : c.hom.left ≫ π = (E.functor.obj F).hom := Over.w c.hom
    show ((smallerBasePresheafForgetIso B S S' hS hS' g).inv.app F ≫ c.hom.left) ≫ π = _
    rw [Category.assoc, hc, smallerBasePresheafEquivalence_functor_obj_hom,
      Iso.inv_hom_id_app_assoc]
  exact ⟨F, isAlgebraicSpace_of_isAlgebraicSpace_relocalizePresheaf B S S' hS hS' g F
    (isAlgebraicSpace_of_iso B S' hS' e.symm hQ), e, he⟩

/-- **Stacks 04SG, fullness.** A morphism `u : Λ F ⟶ Λ G` of lower-shriek extensions which is
compatible with their structural morphisms to the representable presheaf of `g` is the extension
of a morphism `v : F ⟶ G`: it is a morphism of the images of `F` and `G` under the presheaf
equivalence `AlgebraicGeometry.smallerBasePresheafEquivalence`, which is fully faithful. -/
theorem exists_relocalize_map_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (u : (OverShriek.relocalizePresheafFunctor g).obj F ⟶
      (OverShriek.relocalizePresheafFunctor g).obj G)
    (hu : u ≫ OverShriek.viewStructureMap g G = OverShriek.viewStructureMap g F) :
    ∃ v : F ⟶ G, (OverShriek.relocalizePresheafFunctor g).map v = u := by
  let E := smallerBasePresheafEquivalence B S S' hS hS' g
  let φ := smallerBasePresheafForgetIso B S S' hS hS' g
  let m : E.functor.obj F ⟶ E.functor.obj G :=
    Over.homMk (φ.hom.app F ≫ u ≫ φ.inv.app G) (by
      rw [smallerBasePresheafEquivalence_functor_obj_hom, Category.assoc, Category.assoc,
        Iso.inv_hom_id_app_assoc, hu, ← smallerBasePresheafEquivalence_functor_obj_hom])
  refine ⟨E.functor.preimage m, ?_⟩
  have hnat := smallerBasePresheafEquivalence_map_left_comp B S S' hS hS' g (E.functor.preimage m)
  rw [Functor.map_preimage] at hnat
  calc (OverShriek.relocalizePresheafFunctor g).map (E.functor.preimage m)
      = φ.inv.app F ≫ φ.hom.app F ≫
          (OverShriek.relocalizePresheafFunctor g).map (E.functor.preimage m) := by simp
    _ = φ.inv.app F ≫ m.left ≫ φ.hom.app G := by rw [hnat]
    _ = u := by simp [m]

end AlgebraicGeometry.Space


namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **The structure 1-morphism of Construction A of the stack of `F` is represented by the
structural morphism of `Λ F`.** Read through the identification of the view of the category of
elements of `F` with that of `Λ F` and of the stack represented by `S/S'` with the category of
elements of its representable presheaf, both functors to the latter send a pair `(T, x)` to the
factorization `T ⟶ S`. -/
theorem representingMap_changeBaseStructureHom (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    representingMap B S' hS'
        (changeBaseAlgebraicStack B S S' hS hS' g (algebraicSpaceStack.{u, w} B S hS F hF)).val
        (schemeFibredCategory B S' hS' (Over.mk g))
        ((OverShriek.relocalizePresheafFunctor g).obj F) (yoneda.obj (Over.mk g))
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g F)
        (PresheafOfCategories.sliceElementsEquivalenceOver (Over.mk g))
        (changeBaseStructureHom B S S' hS hS' g (algebraicSpaceStack.{u, w} B S hS F hF)) =
      OverShriek.viewStructureMap g F :=
  morphismSpaceEquiv_eq_of_comp_eq B S' hS' _ _ _ _ _ _ _ _ rfl

/-- The underlying morphism of a morphism of a slice conjugated by `eqToHom`s. -/
theorem over_left_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {U : C}
    {A A' B B' : Over U} (f : A ⟶ B) (h₁ : A' = A) (h₂ : B = B') :
    (eqToHom h₁ ≫ f ≫ eqToHom h₂).left =
      eqToHom (congrArg Over.left h₁) ≫ f.left ≫ eqToHom (congrArg Over.left h₂) := by
  subst h₁ h₂
  simp

/-- **Two 1-morphisms to a slice of the site related by a 2-isomorphism are equal**: the fibres
of a slice are discrete, so a component lying over an identity is an identity, and the two
underlying functors agree on objects and, both lying over the same functor to the site, on
morphisms. -/
theorem eq_of_iso_schemeFibredCategory {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S' hS')} {U : BigFppfOver B S' hS'}
    {a b : 𝒜 ⟶ schemeFibredCategory B S' hS' U} (η : a ≅ b) : a = b := by
  have ha := a.hom.w
  have hb := b.hom.w
  have hobj : ∀ x, a.hom.toFunctor.obj x = b.hom.toFunctor.obj x := fun x => by
    have := η.hom.hom.isHomLift' x
    have hl : (a.hom.toFunctor.obj x).left = (b.hom.toFunctor.obj x).left :=
      (Functor.congr_obj ha x).trans (Functor.congr_obj hb x).symm
    refine CostructuredArrow.obj_ext _ _ hl ?_
    have hw := Over.w (η.hom.hom.toNatTrans.app x)
    have hfac := IsHomLift.fac (schemeFibredCategory B S' hS' U).val.p (𝟙 (𝒜.val.p.obj x))
      (η.hom.hom.toNatTrans.app x)
    change 𝟙 _ = eqToHom _ ≫ (η.hom.hom.toNatTrans.app x).left ≫ eqToHom _ at hfac
    have hleft : (η.hom.hom.toNatTrans.app x).left = eqToHom hl := by
      have h1 := (eqToHom_comp_iff _ _ _).1 hfac.symm
      have h2 := (comp_eqToHom_iff _ _ _).1 h1
      rw [h2]
      simp
    rw [hleft] at hw
    simpa using hw
  refine Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext'
    (CategoryTheory.Functor.ext hobj fun x y φ => ?_))
  apply Over.OverMorphism.ext
  have h' : a.hom.toFunctor ⋙ Over.forget U = b.hom.toFunctor ⋙ Over.forget U := ha.trans hb.symm
  have := Functor.congr_hom h' φ
  change Over.Hom.left (a.hom.toFunctor.map φ) =
    eqToHom _ ≫ Over.Hom.left (b.hom.toFunctor.map φ) ≫ eqToHom _ at this
  exact this.trans (over_left_eqToHom_comp_comp_eqToHom _ _ _).symm

/-- The comparison `Φ` of the view of the stack of `F` with the stack of `Λ F` is represented by
the identity of `Λ F`. -/
theorem representingMap_viewAlgebraicSpaceStackToRelocalized
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    representingMap B S' hS'
        (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
          (algebraicSpaceStack.{u, w} B S hS F hF)).val
        (algebraicSpaceStack.{u, w} B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F)
          (isAlgebraicSpace_viewOver B S S' hS hS' g F hF)).val
        ((OverShriek.relocalizePresheafFunctor g).obj F)
        ((OverShriek.relocalizePresheafFunctor g).obj F)
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g F)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (viewAlgebraicSpaceStackToRelocalized.{u, w} B S S' hS hS' g F hF).hom = 𝟙 _ :=
  morphismSpaceEquiv_eq_of_comp_eq B S' hS' _ _ _ _ _ _ _ _ rfl

/-- **Universal closedness descends along Construction A**, the converse of
`AlgebraicGeometry.Stack.universallyClosed_constructionAHom`. For `k : 𝒵 ⟶ 𝒴` over `S`, the
projection `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` is, on points, conjugate by homeomorphisms to the projection of the
2-fibre product over `S'` of the 1-morphisms of Construction A, which is closed by hypothesis:
Construction A of the 2-fibre product is the 2-fibre product of Construction A
(`AlgebraicGeometry.Stack.changeBaseTwoFibreProductHom`) and Construction A does not change the
points (`AlgebraicGeometry.Stack.isHomeomorph_changeBasePointsEquiv`). -/
theorem universallyClosed_of_universallyClosed_constructionAHom
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.UniversallyClosed B S' hS' (constructionAHom B S S' hS hS' g f)) :
    AlgebraicStacks.UniversallyClosed B S hS f := by
  intro 𝒵 k
  have h := hf _ (constructionAHom B S S' hS hS' g k)
  set PS := twoFibreProductSquareAlgebraicStacks B S hS k f
  set PT := twoFibreProductSquareAlgebraicStacks B S' hS'
    (constructionAHom B S S' hS hS' g k) (constructionAHom B S S' hS hS' g f)
  let Hom := changeBaseTwoFibreProductHom B S S' hS hS' g 𝒴.val 𝒵.val 𝒳.val k.hom.hom f.hom.hom
  let := pointTopology B S hS PS.pt.val
  let := pointTopology B S hS 𝒵.val
  let := pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g PS.pt.val)
  let := pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒵.val)
  let := pointTopology B S' hS' PT.pt.val
  have hH : IsHomeomorph (Stack.pointsMap B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g PS.pt.val).val
      (changeBaseFiberedInGroupoids B S S' hS hS' g PS.pt.val).property
      PT.pt.val.property Hom) :=
    isHomeomorph_pointsMap_of_isEquivalence B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g PS.pt.val) PT.pt.val Hom
      (isEquivalence_changeBaseTwoFibreProductHom B S S' hS hS' g _ _ _ _ _)
  let H := hH.homeomorph
  let EP := (isHomeomorph_changeBasePointsEquiv.{u, w} B S S' hS hS' g PS.pt.val
    PS.pt.property).homeomorph
  let EZ := (isHomeomorph_changeBasePointsEquiv.{u, w} B S S' hS hS' g 𝒵.val
    𝒵.property).homeomorph
  show IsClosedMap (Stack.pointsMap B S hS PS.pt.val.val PS.pt.val.property 𝒵.val.property
    PS.fst.hom.hom)
  have hPS' : Stack.pointsMap B S hS PS.pt.val.val PS.pt.val.property 𝒵.val.property
      PS.fst.hom.hom = EZ.symm ∘ Stack.pointsMap B S' hS' PT.pt.val.val PT.pt.val.property
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒵.val).property PT.fst.hom.hom ∘ H ∘ EP := by
    funext z
    have hz : Stack.pointsMap B S' hS' PT.pt.val.val PT.pt.val.property
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒵.val).property PT.fst.hom.hom (H (EP z)) =
        EZ (Stack.pointsMap B S hS PS.pt.val.val PS.pt.val.property 𝒵.val.property
          PS.fst.hom.hom z) := by
      show Stack.pointsMap B S' hS' PT.pt.val.val PT.pt.val.property _ PT.fst.hom.hom
          (Stack.pointsMap B S' hS' _ _ PT.pt.val.property Hom
            (changeBasePointsEquiv B S S' hS hS' g PS.pt.val.val PS.pt.val.property z)) =
        changeBasePointsEquiv B S S' hS hS' g 𝒵.val.val 𝒵.val.property
          (Stack.pointsMap B S hS PS.pt.val.val PS.pt.val.property 𝒵.val.property PS.fst.hom.hom z)
      exact (Stack.pointsMap_comp B S' hS' _ _ _ _ Hom PT.fst.hom.hom _).trans
        (changeBasePointsEquiv_pointsMap B S S' hS hS' g PS.pt.val.property 𝒵.val.property
          PS.fst.hom.hom z).symm
    simp only [Function.comp_apply, hz, Homeomorph.symm_apply_apply]
  let := pointTopology B S' hS' (changeBaseAlgebraicStack B S S' hS hS' g 𝒵).val
  rw [hPS']
  exact EZ.symm.isClosedMap.comp (h.comp (H.isClosedMap.comp EP.isClosedMap))

/-- Construction A of `f : 𝒳 ⟶ 𝒴` followed by the structure 1-morphism of Construction A of `𝒴`
is the structure 1-morphism of Construction A of `𝒳`, `f` being a 1-morphism over `S`. -/
theorem changeBaseHom_comp_changeBaseStructureHom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) :
    (changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f).hom ≫
        changeBaseStructureHom B S S' hS hS' g 𝒴 =
      changeBaseStructureHom B S S' hS hS' g 𝒳 :=
  Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext'
    (show f.hom.hom.toFunctor ⋙ 𝒴.val.val.p ⋙ Over.iteratedSliceBackward (Over.mk g) =
        𝒳.val.val.p ⋙ Over.iteratedSliceBackward (Over.mk g) by
      rw [← Functor.assoc, f.hom.hom.w]))

/-- **A 1-morphism of views compatible with the structural morphisms on representing maps is a
1-morphism of pairs.** Let `c` be a 1-morphism from Construction A of the stack of an algebraic
space `F` to Construction A of `𝒳`, and `f : 𝒳 ⟶ Y` a 1-morphism to the stack of an algebraic
space. If the morphism `Λ F ⟶ Λ Y` representing the view of `c` followed by `f`, followed by the
structural morphism of `Λ Y`, is the structural morphism of `Λ F`, then `c` commutes on the nose
with the structure 1-morphisms to the stack represented by `S/S'`: the two composites have the
same representing map, so they are 2-isomorphic (Stacks 04SW), hence equal, the target being a
slice of the site. -/
theorem comp_changeBaseStructureHom_eq_of_representingMap
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {F Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hY : IsAlgebraicSpace B S hS Y)
    (c : changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
        (algebraicSpaceStack.{u, w} B S hS F hF) ⟶
          changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g 𝒳)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (h : representingMap B S' hS'
        (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
          (algebraicSpaceStack.{u, w} B S hS F hF)).val
        (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
          (algebraicSpaceStack.{u, w} B S hS Y hY)).val
        ((OverShriek.relocalizePresheafFunctor g).obj F)
        ((OverShriek.relocalizePresheafFunctor g).obj Y)
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g F)
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
        (c ≫ changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f).hom ≫
          OverShriek.viewStructureMap g Y = OverShriek.viewStructureMap g F) :
    c.hom ≫ changeBaseStructureHom B S S' hS hS' g 𝒳 =
      changeBaseStructureHom B S S' hS hS' g (algebraicSpaceStack.{u, w} B S hS F hF) := by
  have hc : c.hom ≫ changeBaseStructureHom B S S' hS hS' g 𝒳 =
      (c ≫ changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f).hom ≫
        changeBaseStructureHom B S S' hS hS' g (algebraicSpaceStack.{u, w} B S hS Y hY) := by
    rw [← changeBaseHom_comp_changeBaseStructureHom B S S' hS hS' g f]
    rfl
  have hrep := representingMap_comp B S' hS' _ _ _
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F)
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)
    (PresheafOfCategories.sliceElementsEquivalenceOver (Over.mk g))
    (c ≫ changeBaseHomAlgebraicStacks.{u, w, w} B S S' hS hS' g f).hom
    (changeBaseStructureHom B S S' hS hS' g (algebraicSpaceStack.{u, w} B S hS Y hY))
  have hstr : ∀ (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hG : IsAlgebraicSpace B S hS G),
      representingMap B S' hS'
        (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
          (algebraicSpaceStack.{u, w} B S hS G hG)).val
        (schemeFibredCategory B S' hS' (Over.mk g))
        ((OverShriek.relocalizePresheafFunctor g).obj G) (yoneda.obj (Over.mk g))
        (PresheafOfCategories.relocalizeElementsEquivalenceOver g G)
        (PresheafOfCategories.sliceElementsEquivalenceOver (Over.mk g))
        (changeBaseStructureHom B S S' hS hS' g (algebraicSpaceStack.{u, w} B S hS G hG)) =
      OverShriek.viewStructureMap g G := fun G hG =>
    representingMap_changeBaseStructureHom.{u, w} B S S' hS hS' g G hG
  rw [hstr Y hY, h, ← hc, ← hstr F hF] at hrep
  obtain ⟨e⟩ := nonempty_unique_twoIso_of_representingMap_eq B S' hS'
    (changeBaseAlgebraicStacks.{u, w, w} B S S' hS hS' g
      (algebraicSpaceStack.{u, w} B S hS F hF)).val
    (schemeFibredCategory B S' hS' (Over.mk g))
    ((OverShriek.relocalizePresheafFunctor g).obj F) (yoneda.obj (Over.mk g))
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F)
    (PresheafOfCategories.sliceElementsEquivalenceOver (Over.mk g))
    (f := c.hom ≫ changeBaseStructureHom B S S' hS hS' g 𝒳)
    (g := changeBaseStructureHom B S S' hS hS' g (algebraicSpaceStack.{u, w} B S hS F hF)) hrep
  exact eq_of_iso_schemeFibredCategory B S' hS' e.default

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **The lower-shriek extension is faithful**: it is the presheaf equivalence of Stacks 04SG
followed by the forgetful functor of a slice. -/
theorem relocalize_map_injective {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {v v' : F ⟶ G}
    (h : (OverShriek.relocalizePresheafFunctor g).map v =
      (OverShriek.relocalizePresheafFunctor g).map v') : v = v' := by
  let E := smallerBasePresheafEquivalence B S S' hS hS' g
  let φ := smallerBasePresheafForgetIso B S S' hS hS' g
  apply E.functor.map_injective
  apply Over.OverMorphism.ext
  have h1 := smallerBasePresheafEquivalence_map_left_comp B S S' hS hS' g v
  have h2 := smallerBasePresheafEquivalence_map_left_comp B S S' hS hS' g v'
  rw [← Iso.cancel_iso_hom_right _ _ (φ.app G), Iso.app_hom, h1, h2, h]

end AlgebraicGeometry.Space

end
