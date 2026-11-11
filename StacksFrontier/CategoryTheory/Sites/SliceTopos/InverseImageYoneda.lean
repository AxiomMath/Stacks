module

public import StacksFrontier.CategoryTheory.Sites.SliceTopos.InverseImage

/-!
# Clause (c) of Stacks 03CF with Lemma 04D3's identification

Let `u : C ⥤ D` be a morphism of sites, `V : C` and `U = u.obj V`, and let `f' : D/U → C/V` be the
localized morphism of sites given by `u' = Over.post u` (Stacks writes `u : D → C`; the roles of
`C` and `D` are swapped here).  Clause (c) of Stacks 03CF says that, through the identifications
`Sh(C/V) = Sh(C)/h_V^#` and `Sh(D/U) = Sh(D)/h_U^#` of Stacks 00Y1,
```
  (f')⁻¹ (H ⟶ h_V^#) = (f⁻¹H ⟶ f⁻¹h_V^# = h_U^#) ,
```
where `f⁻¹h_V^# = h_U^#` is Lemma 04D3 (`sheafPullbackSheafifyYonedaIso`).
`Sites/SliceTopos/InverseImage.lean` proves this with the identification `yonedaIso` which the
triangle at the terminal sheaf forces; this file proves that `yonedaIso` *is* 04D3's isomorphism
and so obtains clause (c) in Stacks' formulation.

The proof is a transposition argument.  Write `τ_V(Y) : j_{V!}Y ⟶ h_V^#` for the structure map of
00Y1.  Its transpose across `j_{V!} ⊣ j_V⁻¹` sends every section over `W ⟶ V` to the image of
`W ⟶ V` in `h_V^#(W)` (`homEquiv_structureMap_app`, computed through Stacks 03CD); the transpose of
04D3's isomorphism across `f⁻¹ ⊣ f_*` sends the image of `g` to the image of `u(g)`
(`homEquiv_sheafPullbackSheafifyYonedaIso_hom_app`).  Transposing across
`(f')⁻¹ ⋙ j_{U!} ⊣ j_U⁻¹ ⋙ f'_*`, whose right adjoint is literally `f_* ⋙ j_V⁻¹` (clause (d)),
both sides of `τ_U((f')⁻¹Y) = (comparison) ≫ f⁻¹τ_V(Y) ≫ 04D3` become the same family of sections
(`structureMap_sheafPullback_overPost`), and at the terminal sheaf this is the equation
`yonedaIso = sheafPullbackSheafifyYonedaIso`.

## Main results

* `CategoryTheory.SliceTopos.structureMap_sheafPullback_overPost`: `(f')⁻¹` carries 00Y1's
  structure maps to one another through 04D3, for every sheaf on `C/V`.
* `CategoryTheory.SliceTopos.yonedaIso_eq_sheafPullbackSheafifyYonedaIso`.
* `CategoryTheory.SliceTopos.sheafFunctorToOverCompOverPostSheafifyYonedaIso`: Stacks 03CF (c).
-/

@[expose] public section

namespace CategoryTheory.SliceTopos

open Limits Opposite OverShriek

universe u

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

noncomputable section

section Shriek

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C)

/-- Stacks 03CD's comparison `j_{U!}(G^#) ≅ (∐ G)^#`, transposed across sheafification and
`j_{U!} ⊣ j_U^{-1}`, is the universal property `toRestricted` of the coproduct presheaf. -/
theorem homEquiv_sheafifyNatIso_hom_app_comp (P : (Over U)ᵒᵖ ⥤ Type u) (H : Sheaf J (Type u))
    (s : (presheafToSheaf J (Type u)).obj (presheaf P) ⟶ H) :
    (sheafificationAdjunction (J.over U) (Type u)).homEquiv _ _
        (((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J).homEquiv _ _
          ((sheafifyNatIso (U := U) J).hom.app P ≫ s)) =
      toRestricted P (toSheafify J (presheaf P) ≫ s.hom) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
    ((sheafificationAdjunction (J.over U) (Type u)).comp
      ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J))
    (presheafAdjunction.comp (sheafificationAdjunction J (Type u))) s
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply] at h
  refine h.trans ?_
  change presheafAdjunction.homEquiv P ((sheafToPresheaf J (Type u)).obj H)
    ((sheafificationAdjunction J (Type u)).homEquiv _ _ s) = _
  exact (presheafAdjunction_homEquiv_apply P _).trans
    (congrArg (toRestricted P) ((sheafificationAdjunction J (Type u)).homEquiv_unit _ _ s))

/-- The transpose across `j_{U!} ⊣ j_U^{-1}` of the structure map `j_{U!}X ⟶ h_U^#` of
Stacks 00Y1 sends every section of `X` over `W ⟶ U` to the image of `W ⟶ U` in `h_U^#(W)`. -/
theorem homEquiv_structureMap_app (X : Sheaf (J.over U) (Type u)) (W : (Over U)ᵒᵖ)
    (x : X.obj.obj W) :
    (((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J).homEquiv _ _
        ((sheafFunctorToOverForgetIso (U := U) J).inv.app X ≫
          ((sheafFunctorToOver (U := U) J).obj X).hom)).hom.app W x =
      (toSheafify J (yoneda.obj U)).app (op W.unop.left) W.unop.hom := by
  let ε := (sheafificationAdjunction (J.over U) (Type u)).counit
  let a := (asIso ε).inv.app X
  have h3 : toSheafify (J.over U) X.obj ≫ (ε.app X).hom = 𝟙 _ :=
    (sheafificationAdjunction (J.over U) (Type u)).right_triangle_components X
  have h4 : ε.app X ≫ a = 𝟙 _ := (asIso ε).hom_inv_id_app X
  have hinv : a.hom = toSheafify (J.over U) X.obj :=
    calc a.hom = (toSheafify (J.over U) X.obj ≫ (ε.app X).hom) ≫ a.hom := by
          rw [h3, Category.id_comp]
      _ = toSheafify (J.over U) X.obj ≫ (ε.app X ≫ a).hom := by
          rw [Category.assoc]; rfl
      _ = toSheafify (J.over U) X.obj := by rw [h4]; rfl
  let N := (sheafifyNatIso (U := U) J).hom.app X.obj
  let s := ((sheafFunctorToOver (U := U) J).obj X).hom
  let adjF := (Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J
  have e : (sheafFunctorToOverForgetIso (U := U) J).inv.app X ≫ s =
      ((Over.forget U).sheafPullback (Type u) (J.over U) J).map a ≫ N ≫ s := rfl
  have h := homEquiv_sheafifyNatIso_hom_app_comp J U X.obj _ s
  rw [Adjunction.homEquiv_unit] at h
  have h' := congrArg (fun t => t.app W x) h
  rw [e, Adjunction.homEquiv_naturality_left]
  change (adjF.homEquiv _ _ (N ≫ s)).hom.app W (a.hom.app W x) = _
  rw [hinv]
  change (toSheafify (J.over U) X.obj ≫ (adjF.homEquiv _ _ (N ≫ s)).hom).app W x = _
  refine h'.trans ?_
  change (toSheafify J (presheaf X.obj) ≫ sheafifyMap J (presheafToYoneda X.obj)).app
    (op W.unop.left) ⟨W.unop.hom, x⟩ = _
  rw [← toSheafify_naturality]
  rfl

end Shriek

section Pullback

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) (V : C)
  [u.IsContinuous J K]

/-- The transpose across `f⁻¹ ⊣ f_*` of Stacks 04D3's isomorphism `f⁻¹h_V^# ≅ h_{u(V)}^#` sends
the image of `g : Z ⟶ V` in `h_V^#(Z)` to the image of `u(g)` in `h_{u(V)}^#(u(Z))`. -/
theorem homEquiv_sheafPullbackSheafifyYonedaIso_hom_app {Z : C} (g : Z ⟶ V) :
    ((u.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _
        (sheafPullbackSheafifyYonedaIso u J K V).hom).hom.app (op Z)
        ((toSheafify J (yoneda.obj V)).app (op Z) g) =
      (toSheafify K (yoneda.obj (u.obj V))).app (op (u.obj Z)) (u.map g) := by
  let ψ := (u.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _
    (sheafPullbackSheafifyYonedaIso u J K V).hom
  have h0 := sheafPullbackSheafifyYonedaIso_hom_comp u J K V _ (𝟙 _)
  rw [Category.comp_id] at h0
  have e1 : lhsEquiv u J K V _ (sheafPullbackSheafifyYonedaIso u J K V).hom =
      yonedaEquiv (toSheafify J (yoneda.obj V) ≫ ψ.hom) := by
    change yonedaEquiv ((sheafificationAdjunction J (Type u)).homEquiv _ _ ψ) = _
    rw [Adjunction.homEquiv_unit]
    rfl
  have e2 : rhsEquiv u K V _ (𝟙 _) = yonedaEquiv (toSheafify K (yoneda.obj (u.obj V))) := by
    change yonedaEquiv ((sheafificationAdjunction K (Type u)).homEquiv _ _ (𝟙 _)) = _
    rw [Adjunction.homEquiv_unit, Functor.map_id]
    exact congrArg yonedaEquiv (Category.comp_id _)
  have hV : ψ.hom.app (op V) ((toSheafify J (yoneda.obj V)).app (op V) (𝟙 V)) =
      (toSheafify K (yoneda.obj (u.obj V))).app (op (u.obj V)) (𝟙 (u.obj V)) := by
    have h := e1.symm.trans (h0.trans e2)
    rw [yonedaEquiv_apply, yonedaEquiv_apply] at h
    exact h
  have hZ : (toSheafify J (yoneda.obj V)).app (op Z) g =
      (sheafify J (yoneda.obj V)).map g.op ((toSheafify J (yoneda.obj V)).app (op V) (𝟙 V)) := by
    rw [← NatTrans.naturality_apply]
    simp
  have hZ' : (toSheafify K (yoneda.obj (u.obj V))).app (op (u.obj Z)) (u.map g) =
      (sheafify K (yoneda.obj (u.obj V))).map (u.map g).op
        ((toSheafify K (yoneda.obj (u.obj V))).app (op (u.obj V)) (𝟙 (u.obj V))) := by
    rw [← NatTrans.naturality_apply]
    simp
  rw [hZ, hZ', NatTrans.naturality_apply ψ.hom g.op]
  exact congrArg _ hV

end Pullback

section Clause

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) (V : C)
  [u.IsContinuous J K]

/-- **The structure maps of Stacks 00Y1 are carried to one another by `(f')⁻¹`, through 04D3.**
For a sheaf `Y` on `C/V`, the structure map `j_{U!}(f')⁻¹Y ⟶ h_U^#` is the composite of the
comparison `j_{U!}(f')⁻¹ ≅ f⁻¹j_{V!}` of the proof of 03CF, of `f⁻¹` of the structure map
`j_{V!}Y ⟶ h_V^#`, and of Stacks 04D3's identification `f⁻¹h_V^# ≅ h_U^#`. -/
theorem structureMap_sheafPullback_overPost (Y : Sheaf (J.over V) (Type u)) :
    (sheafFunctorToOverForgetIso (U := u.obj V) K).inv.app
        (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))).obj Y) ≫
      ((sheafFunctorToOver (U := u.obj V) K).obj
        (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))).obj Y)).hom =
    (sheafPullbackOverPostIso J K u V (Type u)).hom.app Y ≫
      (u.sheafPullback (Type u) J K).map
        ((sheafFunctorToOverForgetIso (U := V) J).inv.app Y ≫
          ((sheafFunctorToOver (U := V) J).obj Y).hom) ≫
      (sheafPullbackSheafifyYonedaIso u J K V).hom := by
  let adjPost := (Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
    (K.over (u.obj V))
  let adjForgetU := (Over.forget (u.obj V)).sheafAdjunctionContinuous (Type u)
    (K.over (u.obj V)) K
  let adjForgetV := (Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J
  let adjU := u.sheafAdjunctionContinuous (Type u) J K
  let τU := (sheafFunctorToOverForgetIso (U := u.obj V) K).inv.app
      (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))).obj Y) ≫
    ((sheafFunctorToOver (U := u.obj V) K).obj
      (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))).obj Y)).hom
  let τV := (sheafFunctorToOverForgetIso (U := V) J).inv.app Y ≫
    ((sheafFunctorToOver (U := V) J).obj Y).hom
  let Φ := sheafPullbackSheafifyYonedaIso u J K V
  let ψ := adjU.homEquiv _ _ Φ.hom
  apply ((adjPost.comp adjForgetU).homEquiv _ _).injective
  have h1 : (adjPost.comp adjForgetU).homEquiv _ _
      ((sheafPullbackOverPostIso J K u V (Type u)).hom.app Y ≫
        (u.sheafPullback (Type u) J K).map τV ≫ Φ.hom) =
      (adjForgetV.comp adjU).homEquiv _ _ ((u.sheafPullback (Type u) J K).map τV ≫ Φ.hom) :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app_comp _ _ _
  have hR : (adjForgetV.comp adjU).homEquiv _ _ ((u.sheafPullback (Type u) J K).map τV ≫ Φ.hom) =
      adjForgetV.homEquiv _ _ τV ≫
        ((Over.forget V).sheafPushforwardContinuous (Type u) (J.over V) J).map ψ := by
    simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have hL : (adjPost.comp adjForgetU).homEquiv _ _ τU =
      adjPost.unit.app Y ≫
        ((Over.post (X := V) u).sheafPushforwardContinuous (Type u) (J.over V)
          (K.over (u.obj V))).map (adjForgetU.homEquiv _ _ τU) := by
    simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
    rw [Adjunction.homEquiv_unit]
  refine Eq.trans hL (Eq.trans ?_ (hR.symm.trans h1.symm))
  ext W x
  exact (homEquiv_structureMap_app K (u.obj V) _ (op ((Over.post (X := V) u).obj W.unop)) _).trans
    ((homEquiv_sheafPullbackSheafifyYonedaIso_hom_app J K u V W.unop.hom).symm.trans
      (congrArg (ψ.hom.app (op W.unop.left)) (homEquiv_structureMap_app J V Y W x).symm))

/-- **The identification `yonedaIso` of clause (c) is Stacks 04D3's.**  The isomorphism
`f⁻¹h_V^# ≅ h_U^#` which the triangle of clause (c) at the terminal sheaf forces is
`sheafPullbackSheafifyYonedaIso`, the identification of Stacks 04D3 by which Stacks reads
`f⁻¹h_V^#` as `h_U^#`. -/
theorem yonedaIso_eq_sheafPullbackSheafifyYonedaIso (hu : u.IsMorphismOfSites J K) :
    yonedaIso J K u V hu = sheafPullbackSheafifyYonedaIso u J K V := by
  have := isIso_hom_sheafFunctorToOver_terminal J V
  have := isIso_hom_sheafFunctorToOver_sheafPullback_terminal J K u V hu
  have ht : ((sheafFunctorToOver (U := u.obj V) K).obj
      (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))).obj
        (⊤_ (Sheaf (J.over V) (Type u))))).hom =
      (underlyingIso J K u V).hom.app (⊤_ (Sheaf (J.over V) (Type u))) ≫
        (u.sheafPullback (Type u) J K).map
          ((sheafFunctorToOver (U := V) J).obj (⊤_ (Sheaf (J.over V) (Type u)))).hom ≫
        (sheafPullbackSheafifyYonedaIso u J K V).hom := by
    rw [← cancel_epi ((sheafFunctorToOverForgetIso (U := u.obj V) K).inv.app
      (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))).obj
        (⊤_ (Sheaf (J.over V) (Type u)))))]
    rw [structureMap_sheafPullback_overPost J K u V]
    simp [underlyingIso, Functor.map_comp]
  ext1
  simp only [yonedaIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Iso.app_inv]
  rw [ht]
  simp

/-- **Stacks 03CF, clause (c), with Stacks 04D3's identification.**  Under the identifications
`Sh(C/V) = Sh(C)/h_V^#` and `Sh(D/U) = Sh(D)/h_U^#` of Stacks 00Y1, the inverse image `(f')⁻¹`
of the localized morphism of sites is the rule
```
  (f')⁻¹ (H ⟶ h_V^#) = (f⁻¹H ⟶ f⁻¹h_V^# ≅ h_U^#) ,
```
where `f⁻¹h_V^# ≅ h_U^#` is Lemma 04D3's `sheafPullbackSheafifyYonedaIso`, exactly as in Stacks.
(Stacks writes `u : D → C` for the continuous functor; here `u : C ⥤ D`, `V : C`, `U = u(V)`.) -/
@[stacks 03CF "Clause (c): under 00Y1's identifications `Sh(C/V) = Sh(C)/h_V^#` and
  `Sh(D/U) = Sh(D)/h_U^#`, `(f')⁻¹` sends `(H ⟶ h_V^#)` to `(f⁻¹H ⟶ h_U^#)`, with the
  identification `f⁻¹h_V^# ≅ h_U^#` of 04D3 (`sheafPullbackSheafifyYonedaIso`), for `u` any morphism
  of sites. Clause (a) is `Functor.isMorphismOfSites_overPost_of_isMorphismOfSites`, clause (b)
  `overPullbackCompSheafPullbackOverPostIso`, clause (d) `sheafPushforwardContinuous_overPost_eq`."]
def sheafFunctorToOverCompOverPostSheafifyYonedaIso (hu : u.IsMorphismOfSites J K) :
    (Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ⋙
        sheafFunctorToOver (U := u.obj V) K ≅
      sheafFunctorToOver (U := V) J ⋙ Over.post (u.sheafPullback (Type u) J K) ⋙
        Over.map (sheafPullbackSheafifyYonedaIso u J K V).hom :=
  sheafFunctorToOverCompOverPostIso_of_eq J K u V hu
    (yonedaIso_eq_sheafPullbackSheafifyYonedaIso J K u V hu)

end Clause

end

end CategoryTheory.SliceTopos
