module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Situation

/-!
# The mate of a square of direct images along cocontinuous functors

Consider a square of functors of sites
```
  A ---v---> A'
  |          |
  i          i'
  v          v
  B ---T---> B'
```
with `i ⋙ T = v ⋙ i'`, where `v` and `T` are cocontinuous and the vertical functors `i`, `i'` are
both continuous and cocontinuous. The direct images of sheaves of sets along the four functors
form a commutative square `v_* ⋙ i'_* ≅ i_* ⋙ T_*` ([Stacks, Tag 03L5]), and its mate along the
adjunctions `i^{-1} ⊣ i_*` and `i'^{-1} ⊣ i'_*` is a comparison

`T_* ⋙ i'^{-1} ⟶ i^{-1} ⋙ v_*`.

On underlying presheaves this mate is the base change of right Kan extensions of the square of
opposite functors, `CategoryTheory.TwoSquare.ranBaseChange`. In particular the mate is an
isomorphism when the square is Guitart exact: this is the Beck–Chevalley property of the square
of topoi.

## Main definitions

* `CategoryTheory.sheafPushforwardCocontinuousSquareIso`: the square of direct images.
* `CategoryTheory.sheafPushforwardCocontinuousSquareMate`: its mate along the two restrictions.

## Main results

* `CategoryTheory.sheafPushforwardCocontinuousSquareMate_app_hom`: on underlying presheaves the
  mate is the base change of right Kan extensions.
* `CategoryTheory.isIso_sheafPushforwardCocontinuousSquareMate`: the mate is invertible when the
  square of site functors is Guitart exact.
* `CategoryTheory.mateEquiv_symm_natTrans_app_leftAdjointUniq`: changing the left adjoints of a
  mate along `CategoryTheory.Adjunction.leftAdjointUniq` conjugates it by the two comparisons of
  left adjoints.

## References

* [Stacks Project, Tag 03L5](https://stacks.math.columbia.edu/tag/03L5)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

section Comp

variable {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)

/-- The comparison `(u ⋙ w)_* ≅ u_* ⋙ w_*` of [Stacks, Tag 03L5], followed by the composite of the
two right Kan extension counits, is the counit of the right Kan extension along `u ⋙ w`. -/
theorem sheafPushforwardCocontinuousCompIso_hom_app_counit (u : C ⥤ D) (w : D ⥤ E)
    [u.IsCocontinuous J K]
    [w.IsCocontinuous K L] (F : Sheaf J (Type u)) :
    haveI : (u ⋙ w).IsCocontinuous J L := CategoryTheory.isCocontinuous_comp u w J K
    Functor.whiskerLeft (u ⋙ w).op
        ((sheafPushforwardCocontinuousCompIso J K L u w).hom.app F).hom ≫
      Functor.whiskerLeft u.op ((w.op.ranAdjunction (Type u)).counit.app (u.op.ran.obj F.obj)) ≫
        (u.op.ranAdjunction (Type u)).counit.app F.obj =
      ((u ⋙ w).op.ranAdjunction (Type u)).counit.app F.obj := by
  have : (u ⋙ w).IsCocontinuous J L := CategoryTheory.isCocontinuous_comp u w J K
  have h := Adjunction.rightAdjointUniq_hom_app_counit ((u.op ⋙ w.op).ranAdjunction (Type u))
    ((w.op.ranAdjunction (Type u)).comp (u.op.ranAdjunction (Type u))) F.obj
  rw [Adjunction.comp_counit_app] at h
  have e : ((sheafPushforwardCocontinuousCompIso J K L u w).hom.app F).hom =
      (ranOpCompIso u w).hom.app F.obj := by
    have e₀ := Functor.fullyFaithfulCancelRight_hom_app (H := sheafToPresheaf L (Type u))
      (F := (u ⋙ w).sheafPushforwardCocontinuous (Type u) J L)
      (G := u.sheafPushforwardCocontinuous (Type u) J K ⋙
        w.sheafPushforwardCocontinuous (Type u) K L)
      ((sheafToPresheaf J (Type u)).isoWhiskerLeft (ranOpCompIso u w)) F
    show (sheafToPresheaf L (Type u)).map ((Functor.fullyFaithfulCancelRight
      (sheafToPresheaf L (Type u)) (F := (u ⋙ w).sheafPushforwardCocontinuous (Type u) J L)
      (G := u.sheafPushforwardCocontinuous (Type u) J K ⋙
        w.sheafPushforwardCocontinuous (Type u) K L)
      ((sheafToPresheaf J (Type u)).isoWhiskerLeft (ranOpCompIso u w))).hom.app F) = _
    rw [e₀, Functor.map_preimage]
    rfl
  rw [e, ranOpCompIso_def]
  exact h

/-- The inverse of the comparison `(u ⋙ w)_* ≅ u_* ⋙ w_*` of [Stacks, Tag 03L5], followed by the
counit of the right Kan extension along `u ⋙ w`, is the composite of the two counits. -/
theorem sheafPushforwardCocontinuousCompIso_inv_app_counit (u : C ⥤ D) (w : D ⥤ E)
    [u.IsCocontinuous J K]
    [w.IsCocontinuous K L] (F : Sheaf J (Type u)) :
    haveI : (u ⋙ w).IsCocontinuous J L := CategoryTheory.isCocontinuous_comp u w J K
    Functor.whiskerLeft (u ⋙ w).op
        ((sheafPushforwardCocontinuousCompIso J K L u w).inv.app F).hom ≫
      ((u ⋙ w).op.ranAdjunction (Type u)).counit.app F.obj =
      Functor.whiskerLeft u.op ((w.op.ranAdjunction (Type u)).counit.app (u.op.ran.obj F.obj)) ≫
        (u.op.ranAdjunction (Type u)).counit.app F.obj := by
  have : (u ⋙ w).IsCocontinuous J L := CategoryTheory.isCocontinuous_comp u w J K
  rw [← sheafPushforwardCocontinuousCompIso_hom_app_counit J K L u w F, ← Category.assoc,
    ← Functor.whiskerLeft_comp,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app,
    ObjectProperty.FullSubcategory.id_hom, Functor.whiskerLeft_id', Category.id_comp]
  rfl

end Comp

section Eq

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- The inverse of the isomorphism of direct images attached to an equality `W = W'` of site
functors, followed by the counit of the right Kan extension along `W`, is the transport along the
equality followed by the counit along `W'`. -/
theorem cocontinuousPushforwardIsoOfEq_inv_app_counit {W W' : C ⥤ D} [W.IsCocontinuous J K]
    [W'.IsCocontinuous J K]
    (h : W = W') (F : Sheaf J (Type u)) :
    Functor.whiskerLeft W.op
        ((SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J K h).inv.app
          F).hom ≫ (W.op.ranAdjunction (Type u)).counit.app F.obj =
      eqToHom (by subst h; rfl) ≫ (W'.op.ranAdjunction (Type u)).counit.app F.obj := by
  subst h
  simp only [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq]
  rfl

end Eq

section Mate

/-- If `L₁ ⊣ R₁` and `L₁' ⊣ R₁`, `L₂ ⊣ R₂` and `L₂' ⊣ R₂`, the mates of a 2-cell
`R₁ ⋙ G ⟶ H ⋙ R₂` along the two pairs of adjunctions differ, at each object, by the comparisons
`CategoryTheory.Adjunction.leftAdjointUniq` of the left adjoints. -/
theorem mateEquiv_symm_natTrans_app_leftAdjointUniq {C₁ C₂ C₃ C₄ : Type*} [Category C₁]
    [Category C₂] [Category C₃] [Category C₄] {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {L₁ L₁' : C₁ ⥤ C₂}
    {R₁ : C₂ ⥤ C₁}
    {L₂ L₂' : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃} (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₂' : L₂' ⊣ R₂) (β : TwoSquare R₁ H G R₂) (X : C₁) :
    ((mateEquiv adj₁ adj₂).symm β).natTrans.app X =
      (Adjunction.leftAdjointUniq adj₂ adj₂').hom.app (G.obj X) ≫
        ((mateEquiv adj₁' adj₂').symm β).natTrans.app X ≫
          H.map ((Adjunction.leftAdjointUniq adj₁ adj₁').inv.app X) := by
  rw [Stacks.CategoryTheory.mateEquiv_symm_congr_left adj₁ adj₁' adj₂ β,
    Stacks.CategoryTheory.mateEquiv_symm_congr_right adj₁' adj₂' adj₂ β]
  simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, Adjunction.leftAdjointUniq_inv_app]

end Mate

section Square

variable {A A' B B' : Type u} [SmallCategory A] [SmallCategory A'] [SmallCategory B]
  [SmallCategory B']
  (JA : GrothendieckTopology A) (JA' : GrothendieckTopology A') (JB : GrothendieckTopology B)
  (JB' : GrothendieckTopology B')
  (i : A ⥤ B) (i' : A' ⥤ B') (v : A ⥤ A') (T : B ⥤ B')
  [i.IsContinuous JA JB] [i.IsCocontinuous JA JB] [i'.IsContinuous JA' JB']
  [i'.IsCocontinuous JA' JB'] [v.IsCocontinuous JA JA'] [T.IsCocontinuous JB JB']

/-- The square of direct images of sheaves of sets attached to a commutative square of site
functors `i ⋙ T = v ⋙ i'`. -/
def sheafPushforwardCocontinuousSquareIso (hq : i ⋙ T = v ⋙ i') :
    v.sheafPushforwardCocontinuous (Type u) JA JA' ⋙
        i'.sheafPushforwardCocontinuous (Type u) JA' JB' ≅
      i.sheafPushforwardCocontinuous (Type u) JA JB ⋙
        T.sheafPushforwardCocontinuous (Type u) JB JB' :=
  haveI : (v ⋙ i').IsCocontinuous JA JB' := isCocontinuous_comp v i' JA JA'
  haveI : (i ⋙ T).IsCocontinuous JA JB' := isCocontinuous_comp i T JA JB
  (sheafPushforwardCocontinuousCompIso JA JA' JB' v i').symm ≪≫
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} JA JB' hq.symm ≪≫
    sheafPushforwardCocontinuousCompIso JA JB JB' i T

/-- The mate of `sheafPushforwardCocontinuousSquareIso` along the adjunctions
`i^{-1} ⊣ i_*` and `i'^{-1} ⊣ i'_*`: the comparison `T_* ⋙ i'^{-1} ⟶ i^{-1} ⋙ v_*`. -/
def sheafPushforwardCocontinuousSquareMate (hq : i ⋙ T = v ⋙ i') :
    TwoSquare (T.sheafPushforwardCocontinuous (Type u) JB JB')
      (i.sheafPushforwardContinuous (Type u) JA JB)
      (i'.sheafPushforwardContinuous (Type u) JA' JB')
      (v.sheafPushforwardCocontinuous (Type u) JA JA') :=
  (mateEquiv (i.sheafAdjunctionCocontinuous (Type u) JA JB)
      (i'.sheafAdjunctionCocontinuous (Type u) JA' JB')).symm
    (TwoSquare.mk _ _ _ _ (sheafPushforwardCocontinuousSquareIso JA JA' JB JB' i i' v T hq).inv)

/-- The underlying presheaf map of the mate, written with presheaf objects. -/
def sheafPushforwardCocontinuousSquareMateHom (hq : i ⋙ T = v ⋙ i') (F : Sheaf JB (Type u)) :
    i'.op ⋙ T.op.ran.obj F.obj ⟶ v.op.ran.obj (i.op ⋙ F.obj) :=
  Functor.whiskerLeft i'.op
      (T.op.ran.map ((i.sheafAdjunctionCocontinuous (Type u) JA JB).unit.app F).hom) ≫
    Functor.whiskerLeft i'.op
      ((sheafPushforwardCocontinuousSquareIso JA JA' JB JB' i i' v T hq).inv.app
        ((i.sheafPushforwardContinuous (Type u) JA JB).obj F)).hom ≫
    ((i'.sheafAdjunctionCocontinuous (Type u) JA' JB').counit.app
      ((v.sheafPushforwardCocontinuous (Type u) JA JA').obj
        ((i.sheafPushforwardContinuous (Type u) JA JB).obj F))).hom

private theorem squareMate_app_hom_eq (hq : i ⋙ T = v ⋙ i') (F : Sheaf JB (Type u)) :
    ((sheafPushforwardCocontinuousSquareMate JA JA' JB JB' i i' v T hq).natTrans.app F).hom =
      sheafPushforwardCocontinuousSquareMateHom JA JA' JB JB' i i' v T hq F := by
  simp only [sheafPushforwardCocontinuousSquareMate, mateEquiv, Equiv.coe_fn_symm_mk,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_map, Category.id_comp, Functor.map_id,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom]
  rfl

/-- Whiskering on the left commutes with a transport along an equality of the whiskering
functors. -/
private theorem whiskerLeft_comp_eqToHom {C D E : Type*} [Category C] [Category D] [Category E]
    {P P' : C ⥤ D} (h : P = P') {G G' : D ⥤ E} (f : G ⟶ G') :
    Functor.whiskerLeft P f ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫ Functor.whiskerLeft P' f := by
  subst h
  simp

omit [i.IsContinuous JA JB] [i'.IsContinuous JA' JB'] in
/-- The inverse of the square of direct images, followed by the composite counit along
`v ⋙ i'`, is the composite counit along `i ⋙ T`. -/
private theorem squareIso_inv_counit (hq : i ⋙ T = v ⋙ i') (G : Sheaf JA (Type u)) :
    Functor.whiskerLeft v.op (Functor.whiskerLeft i'.op
        ((sheafPushforwardCocontinuousSquareIso JA JA' JB JB' i i' v T hq).inv.app G).hom) ≫
      Functor.whiskerLeft v.op ((i'.op.ranAdjunction (Type u)).counit.app (v.op.ran.obj G.obj)) ≫
        (v.op.ranAdjunction (Type u)).counit.app G.obj =
      eqToHom (show (v ⋙ i').op ⋙ T.op.ran.obj (i.op.ran.obj G.obj) =
          (i ⋙ T).op ⋙ T.op.ran.obj (i.op.ran.obj G.obj) by rw [hq]) ≫
        Functor.whiskerLeft i.op ((T.op.ranAdjunction (Type u)).counit.app (i.op.ran.obj G.obj)) ≫
          (i.op.ranAdjunction (Type u)).counit.app G.obj := by
  have : (v ⋙ i').IsCocontinuous JA JB' := isCocontinuous_comp v i' JA JA'
  have : (i ⋙ T).IsCocontinuous JA JB' := isCocontinuous_comp i T JA JB
  have h1 := sheafPushforwardCocontinuousCompIso_hom_app_counit JA JA' JB' v i' G
  have h2 := cocontinuousPushforwardIsoOfEq_inv_app_counit JA JB' hq.symm G
  have h3 := sheafPushforwardCocontinuousCompIso_inv_app_counit JA JB JB' i T G
  have h4 := whiskerLeft_comp_eqToHom (congrArg Functor.op hq.symm)
    ((sheafPushforwardCocontinuousCompIso JA JB JB' i T).inv.app G).hom
  have e : ((sheafPushforwardCocontinuousSquareIso JA JA' JB JB' i i' v T hq).inv.app G).hom =
      ((sheafPushforwardCocontinuousCompIso JA JB JB' i T).inv.app G).hom ≫
        ((SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} JA JB'
          hq.symm).inv.app G).hom ≫
        ((sheafPushforwardCocontinuousCompIso JA JA' JB' v i').hom.app G).hom := by
    simp only [sheafPushforwardCocontinuousSquareIso, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  rw [e]
  show (v ⋙ i').op.whiskerLeft
        ((sheafPushforwardCocontinuousCompIso JA JB JB' i T).inv.app G).hom ≫
      (v ⋙ i').op.whiskerLeft
        ((SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u}
        JA JB' hq.symm).inv.app G).hom ≫
      (v ⋙ i').op.whiskerLeft
        ((sheafPushforwardCocontinuousCompIso JA JA' JB' v i').hom.app G).hom ≫
      Functor.whiskerLeft v.op ((i'.op.ranAdjunction (Type u)).counit.app (v.op.ran.obj G.obj)) ≫
        (v.op.ranAdjunction (Type u)).counit.app G.obj = _
  rw [h1, h2, ← h3]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ ((i ⋙ T).op.ranAdjunction (Type u)).counit.app G.obj) h4).trans
      (Category.assoc _ _ _))

private theorem mateHom_eq (hq : i ⋙ T = v ⋙ i') (F : Sheaf JB (Type u)) :
    sheafPushforwardCocontinuousSquareMateHom JA JA' JB JB' i i' v T hq F =
      (TwoSquare.mk _ _ _ _ (eqToHom hq) : TwoSquare i v T i').op.ranBaseChange.app F.obj := by
  apply Functor.hom_ext_of_isRightKanExtension (v.op.ran.obj (i.op ⋙ F.obj))
    (v.op.ranCounit.app (i.op ⋙ F.obj))
  rw [TwoSquare.ranBaseChange_app]
  have hR : ∀ {X : A'ᵒᵖ ⥤ Type u} {Y : Aᵒᵖ ⥤ Type u} (y : v.op ⋙ X ⟶ Y),
      Functor.whiskerLeft v.op ((v.op.ranAdjunction (Type u)).homEquiv X Y y) ≫
        v.op.ranCounit.app Y = y := by
    intro X Y y
    have h := (v.op.ranAdjunction (Type u)).homEquiv_counit
      (g := (v.op.ranAdjunction (Type u)).homEquiv X Y y)
    rw [Equiv.symm_apply_apply, Functor.ranAdjunction_counit] at h
    exact h.symm
  refine Eq.trans ?_ (hR _).symm
  rw [← Functor.ranAdjunction_counit]
  have hε : ((i'.sheafAdjunctionCocontinuous (Type u) JA' JB').counit.app
      ((v.sheafPushforwardCocontinuous (Type u) JA JA').obj
        ((i.sheafPushforwardContinuous (Type u) JA JB).obj F))).hom =
        (i'.op.ranAdjunction (Type u)).counit.app (v.op.ran.obj (i.op ⋙ F.obj)) :=
    Functor.sheafAdjunctionCocontinuous_counit_app_hom _ _ _ _ _
  have hη : ((i.sheafAdjunctionCocontinuous (Type u) JA JB).unit.app F).hom =
      (i.op.ranAdjunction (Type u)).unit.app F.obj :=
    Functor.sheafAdjunctionCocontinuous_unit_app_hom _ _ _ _ F
  rw [sheafPushforwardCocontinuousSquareMateHom, hε, hη]
  have hK : Functor.whiskerLeft v.op (Functor.whiskerLeft i'.op
        ((sheafPushforwardCocontinuousSquareIso JA JA' JB JB' i i' v T hq).inv.app
          ((i.sheafPushforwardContinuous (Type u) JA JB).obj F)).hom) ≫
      Functor.whiskerLeft v.op ((i'.op.ranAdjunction (Type u)).counit.app
        (v.op.ran.obj (i.op ⋙ F.obj))) ≫
        (v.op.ranAdjunction (Type u)).counit.app (i.op ⋙ F.obj) =
      eqToHom (show (v ⋙ i').op ⋙ T.op.ran.obj (i.op.ran.obj (i.op ⋙ F.obj)) =
          (i ⋙ T).op ⋙ T.op.ran.obj (i.op.ran.obj (i.op ⋙ F.obj)) by rw [hq]) ≫
        Functor.whiskerLeft i.op ((T.op.ranAdjunction (Type u)).counit.app
          (i.op.ran.obj (i.op ⋙ F.obj))) ≫
          (i.op.ranAdjunction (Type u)).counit.app (i.op ⋙ F.obj) :=
    squareIso_inv_counit JA JA' JB JB' i i' v T hq _
  have hW := whiskerLeft_comp_eqToHom (congrArg Functor.op hq.symm)
    (G := T.op.ran.obj F.obj) (G' := T.op.ran.obj (i.op.ran.obj (i.op ⋙ F.obj)))
    (T.op.ran.map ((i.op.ranAdjunction (Type u)).unit.app F.obj))
  have hN : Functor.whiskerLeft T.op (T.op.ran.map ((i.op.ranAdjunction (Type u)).unit.app F.obj)) ≫
      (T.op.ranAdjunction (Type u)).counit.app (i.op.ran.obj (i.op ⋙ F.obj)) =
      (T.op.ranAdjunction (Type u)).counit.app F.obj ≫
        (i.op.ranAdjunction (Type u)).unit.app F.obj :=
    (T.op.ranAdjunction (Type u)).counit.naturality ((i.op.ranAdjunction (Type u)).unit.app F.obj)
  have hT : Functor.whiskerLeft i.op ((i.op.ranAdjunction (Type u)).unit.app F.obj) ≫
      (i.op.ranAdjunction (Type u)).counit.app (i.op ⋙ F.obj) = 𝟙 _ :=
    (i.op.ranAdjunction (Type u)).left_triangle_components F.obj
  show (v ⋙ i').op.whiskerLeft (T.op.ran.map ((i.op.ranAdjunction (Type u)).unit.app F.obj)) ≫
      (Functor.whiskerLeft v.op (Functor.whiskerLeft i'.op
        ((sheafPushforwardCocontinuousSquareIso JA JA' JB JB' i i' v T hq).inv.app
          ((i.sheafPushforwardContinuous (Type u) JA JB).obj F)).hom) ≫
      Functor.whiskerLeft v.op ((i'.op.ranAdjunction (Type u)).counit.app
        (v.op.ran.obj (i.op ⋙ F.obj))) ≫
        (v.op.ranAdjunction (Type u)).counit.app (i.op ⋙ F.obj)) = _
  refine (congrArg (fun t => (v ⋙ i').op.whiskerLeft
    (T.op.ran.map ((i.op.ranAdjunction (Type u)).unit.app F.obj)) ≫ t) hK).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ Functor.whiskerLeft i.op ((T.op.ranAdjunction (Type u)).counit.app
          (i.op.ran.obj (i.op ⋙ F.obj))) ≫
          (i.op.ranAdjunction (Type u)).counit.app (i.op ⋙ F.obj)) hW).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  show eqToHom _ ≫ Functor.whiskerLeft i.op
      (Functor.whiskerLeft T.op (T.op.ran.map ((i.op.ranAdjunction (Type u)).unit.app F.obj)) ≫
        (T.op.ranAdjunction (Type u)).counit.app (i.op.ran.obj (i.op ⋙ F.obj))) ≫
      (i.op.ranAdjunction (Type u)).counit.app (i.op ⋙ F.obj) = _
  rw [hN, Functor.whiskerLeft_comp, Category.assoc, hT, Category.comp_id,
    Functor.ranAdjunction_counit]
  ext X
  simp [eqToHom_map]


/-- On underlying presheaves, the mate of the square of direct images is the base change of right
Kan extensions of the square of opposite site functors. -/
theorem sheafPushforwardCocontinuousSquareMate_app_hom (hq : i ⋙ T = v ⋙ i')
    (F : Sheaf JB (Type u)) :
    ((sheafPushforwardCocontinuousSquareMate JA JA' JB JB' i i' v T hq).natTrans.app F).hom =
      (TwoSquare.mk _ _ _ _ (eqToHom hq) : TwoSquare i v T i').op.ranBaseChange.app F.obj :=
  (squareMate_app_hom_eq JA JA' JB JB' i i' v T hq F).trans (mateHom_eq JA JA' JB JB' i i' v T hq F)

/-- Beck–Chevalley for a Guitart exact square of site functors: if the square `i ⋙ T = v ⋙ i'` is
Guitart exact, the mate `T_* ⋙ i'^{-1} ⟶ i^{-1} ⋙ v_*` of the square of direct images is an
isomorphism. -/
theorem isIso_sheafPushforwardCocontinuousSquareMate (hq : i ⋙ T = v ⋙ i')
    [(TwoSquare.mk _ _ _ _ (eqToHom hq) : TwoSquare i v T i').GuitartExact] :
    IsIso (sheafPushforwardCocontinuousSquareMate JA JA' JB JB' i i' v T hq).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← ObjectProperty.isIso_hom_iff, sheafPushforwardCocontinuousSquareMate_app_hom]
  exact TwoSquare.isIso_ranBaseChange_app _ _

end Square

end CategoryTheory

end
