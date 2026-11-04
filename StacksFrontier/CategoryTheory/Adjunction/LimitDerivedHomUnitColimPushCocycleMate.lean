module

public import StacksFrontier.CategoryTheory.Adjunction.MateAlongEquivalencesComposition

/-!
# The cocycle hypothesis of a composition of mates, as an equation of isomorphisms

`CategoryTheory.Adjunction.leftAdjointCompIso_hom_app_comp_mateOfRightIso_app` reduces the
compatibility with composition of the mates of comparisons `e : R ⋙ G ≅ H ⋙ R'` of right
adjoints to the compatibility of the comparisons themselves, which it takes as a hypothesis in
*pointwise* form: an equation between composites of components of natural transformations.
Here that hypothesis is stated as a single equation of **isomorphisms of functors**, from which
the pointwise form follows.

## Main results

* `CategoryTheory.Adjunction.mateOfRightIso_cocycle_app_of_iso`: the pointwise cocycle condition
  for three comparisons of right adjoints, from the equation of isomorphisms.
* `CategoryTheory.Adjunction.cocycle_iso_conj`: the equation of isomorphisms is stable under
  conjugating the vertical functors by isomorphisms.
* `CategoryTheory.Adjunction.leftAdjointCompIso_hom_app_comp_mateOfRightIso_app_of_iso`:
  `CategoryTheory.Adjunction.leftAdjointCompIso_hom_app_comp_mateOfRightIso_app` with its
  hypothesis in that form.
* `CategoryTheory.Adjunction.leftAdjointCompIso_whiskerLeft_comp_mateOfRightIso_of_iso`: the same,
  as an equation of natural transformations.
-/

@[expose] public section

open CategoryTheory.Functor

namespace CategoryTheory.Adjunction

section CocycleOfIso

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  [Category* D₀] [Category* D₁] [Category* D₂]
  {R₁ : C₁ ⥤ C₀} {R₂ : C₂ ⥤ C₁} {R₁₂ : C₂ ⥤ C₀}
  {R₁' : D₁ ⥤ D₀} {R₂' : D₂ ⥤ D₁} {R₁₂' : D₂ ⥤ D₀}
  {G₀ : C₀ ⥤ D₀} {G₁ : C₁ ⥤ D₁} {G₂ : C₂ ⥤ D₂}

/-- **The cocycle condition for three comparisons of right adjoints, at an object, from the
equation of isomorphisms.**

The hypothesis equates the composition comparison `c` of the right adjoints, transported by `G₀`
and followed by the comparison `e₁₂` for the composite, with the comparison `e₁` whiskered by
`R₂`, then `e₂` whiskered by `R₁'`, then the composition comparison `c'`. The conclusion is that
equation read at an object `M`. -/
theorem mateOfRightIso_cocycle_app_of_iso (e₁ : R₁ ⋙ G₀ ≅ G₁ ⋙ R₁')
    (e₂ : R₂ ⋙ G₁ ≅ G₂ ⋙ R₂') (e₁₂ : R₁₂ ⋙ G₀ ≅ G₂ ⋙ R₁₂')
    (c : R₂ ⋙ R₁ ≅ R₁₂) (c' : R₂' ⋙ R₁' ≅ R₁₂')
    (hc : isoWhiskerRight c G₀ ≪≫ e₁₂ =
      isoWhiskerLeft R₂ e₁ ≪≫ isoWhiskerRight e₂ R₁' ≪≫ isoWhiskerLeft G₂ c')
    (M : C₂) :
    G₀.map (c.hom.app M) ≫ e₁₂.hom.app M =
      e₁.hom.app (R₂.obj M) ≫ R₁'.map (e₂.hom.app M) ≫ c'.hom.app (G₂.obj M) := by
  simpa only [Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, Functor.comp_obj] using congr_app (congrArg Iso.hom hc) M

variable {G₀' : C₀ ⥤ D₀} {G₁' : C₁ ⥤ D₁} {G₂' : C₂ ⥤ D₂}

/-- **The cocycle condition is stable under conjugating the vertical functors by
isomorphisms.** If three comparisons `e₁`, `e₂`, `e₁₂` of right adjoints along `G₀`, `G₁`, `G₂`
satisfy the cocycle condition for `c` and `c'`, then so do the comparisons along `G₀'`, `G₁'`,
`G₂'` obtained from them by conjugating with isomorphisms `θ₀ : G₀ ≅ G₀'`, `θ₁ : G₁ ≅ G₁'`,
`θ₂ : G₂ ≅ G₂'`. -/
theorem cocycle_iso_conj (e₁ : R₁ ⋙ G₀ ≅ G₁ ⋙ R₁') (e₂ : R₂ ⋙ G₁ ≅ G₂ ⋙ R₂')
    (e₁₂ : R₁₂ ⋙ G₀ ≅ G₂ ⋙ R₁₂') (c : R₂ ⋙ R₁ ≅ R₁₂) (c' : R₂' ⋙ R₁' ≅ R₁₂')
    (θ₀ : G₀ ≅ G₀') (θ₁ : G₁ ≅ G₁') (θ₂ : G₂ ≅ G₂')
    (hc : isoWhiskerRight c G₀ ≪≫ e₁₂ =
      isoWhiskerLeft R₂ e₁ ≪≫ isoWhiskerRight e₂ R₁' ≪≫ isoWhiskerLeft G₂ c') :
    isoWhiskerRight c G₀' ≪≫
        (isoWhiskerLeft R₁₂ θ₀.symm ≪≫ e₁₂ ≪≫ isoWhiskerRight θ₂ R₁₂') =
      isoWhiskerLeft R₂ (isoWhiskerLeft R₁ θ₀.symm ≪≫ e₁ ≪≫ isoWhiskerRight θ₁ R₁') ≪≫
        isoWhiskerRight (isoWhiskerLeft R₂ θ₁.symm ≪≫ e₂ ≪≫ isoWhiskerRight θ₂ R₂') R₁' ≪≫
        isoWhiskerLeft G₂' c' := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  have h := mateOfRightIso_cocycle_app_of_iso e₁ e₂ e₁₂ c c' hc M
  have hθ := θ₀.inv.naturality (c.hom.app M)
  have hc' := c'.hom.naturality (θ₂.hom.app M)
  simp only [comp_obj, Functor.comp_map] at hθ hc'
  simp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, comp_obj, Category.assoc,
    Functor.map_comp]
  rw [reassoc_of% hθ, reassoc_of% h]
  slice_rhs 3 4 => rw [← R₁'.map_comp, Iso.hom_inv_id_app, R₁'.map_id]
  rw [Category.id_comp, ← hc']
  simp only [Category.assoc]

end CocycleOfIso

section Composition

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  [Category* D₀] [Category* D₁] [Category* D₂]
  {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {L₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁} {L₁₂ : C₀ ⥤ C₂} {R₁₂ : C₂ ⥤ C₀}
  {L₁' : D₀ ⥤ D₁} {R₁' : D₁ ⥤ D₀} {L₂' : D₁ ⥤ D₂} {R₂' : D₂ ⥤ D₁} {L₁₂' : D₀ ⥤ D₂}
  {R₁₂' : D₂ ⥤ D₀}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₁₂ : L₁₂ ⊣ R₁₂)
  (b₁ : L₁' ⊣ R₁') (b₂ : L₂' ⊣ R₂') (b₁₂ : L₁₂' ⊣ R₁₂')
  {G₀ : C₀ ⥤ D₀} {G₁ : C₁ ⥤ D₁} {G₂ : C₂ ⥤ D₂}

/-- **Mates of right adjoint comparisons are compatible with composition**, with the cocycle
condition for the right adjoint comparisons given as an equation of isomorphisms:
`CategoryTheory.Adjunction.leftAdjointCompIso_hom_app_comp_mateOfRightIso_app` with its
hypothesis supplied through
`CategoryTheory.Adjunction.mateOfRightIso_cocycle_app_of_iso`. -/
theorem leftAdjointCompIso_hom_app_comp_mateOfRightIso_app_of_iso
    (e₁ : R₁ ⋙ G₀ ≅ G₁ ⋙ R₁') (e₂ : R₂ ⋙ G₁ ≅ G₂ ⋙ R₂') (e₁₂ : R₁₂ ⋙ G₀ ≅ G₂ ⋙ R₁₂')
    (c : R₂ ⋙ R₁ ≅ R₁₂) (c' : R₂' ⋙ R₁' ≅ R₁₂')
    (hc : isoWhiskerRight c G₀ ≪≫ e₁₂ =
      isoWhiskerLeft R₂ e₁ ≪≫ isoWhiskerRight e₂ R₁' ≪≫ isoWhiskerLeft G₂ c')
    (ι : L₁ ⋙ L₂ ≅ L₁₂) (hι : ι = leftAdjointCompIso a₁ a₂ a₁₂ c) (N : C₀) :
    (leftAdjointCompIso b₁ b₂ b₁₂ c').hom.app (G₀.obj N) ≫ (mateOfRightIso a₁₂ b₁₂ e₁₂).app N =
      L₂'.map ((mateOfRightIso a₁ b₁ e₁).app N) ≫ (mateOfRightIso a₂ b₂ e₂).app (L₁.obj N) ≫
        G₂.map (ι.hom.app N) :=
  leftAdjointCompIso_hom_app_comp_mateOfRightIso_app a₁ a₂ a₁₂ b₁ b₂ b₁₂ e₁ e₂ e₁₂ c c'
    (fun M ↦ mateOfRightIso_cocycle_app_of_iso e₁ e₂ e₁₂ c c' hc M) ι hι N

/-- **Mates of right adjoint comparisons are compatible with composition, as an equation of
natural transformations.**
`CategoryTheory.Adjunction.leftAdjointCompIso_hom_app_comp_mateOfRightIso_app_of_iso` with both
its hypothesis and its conclusion free of `CategoryTheory.NatTrans.app`. -/
theorem leftAdjointCompIso_whiskerLeft_comp_mateOfRightIso_of_iso
    (e₁ : R₁ ⋙ G₀ ≅ G₁ ⋙ R₁') (e₂ : R₂ ⋙ G₁ ≅ G₂ ⋙ R₂') (e₁₂ : R₁₂ ⋙ G₀ ≅ G₂ ⋙ R₁₂')
    (c : R₂ ⋙ R₁ ≅ R₁₂) (c' : R₂' ⋙ R₁' ≅ R₁₂')
    (hc : isoWhiskerRight c G₀ ≪≫ e₁₂ =
      isoWhiskerLeft R₂ e₁ ≪≫ isoWhiskerRight e₂ R₁' ≪≫ isoWhiskerLeft G₂ c')
    (ι : L₁ ⋙ L₂ ≅ L₁₂) (hι : ι = leftAdjointCompIso a₁ a₂ a₁₂ c) :
    whiskerLeft G₀ (leftAdjointCompIso b₁ b₂ b₁₂ c').hom ≫ mateOfRightIso a₁₂ b₁₂ e₁₂ =
      whiskerRight (mateOfRightIso a₁ b₁ e₁) L₂' ≫
        whiskerLeft L₁ (mateOfRightIso a₂ b₂ e₂) ≫ whiskerRight ι.hom G₂ := by
  refine NatTrans.ext (funext fun N ↦ ?_)
  simpa using
    leftAdjointCompIso_hom_app_comp_mateOfRightIso_app_of_iso a₁ a₂ a₁₂ b₁ b₂ b₁₂
      e₁ e₂ e₁₂ c c' hc ι hι N

end Composition

end CategoryTheory.Adjunction

end
