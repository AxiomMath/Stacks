module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# Bounded below derived functors at two models of the derived category

`HasDerivedCategory C` is a *choice* of a localization of the cochain complexes of `C` at the
quasi-isomorphisms. Two choices `h₁, h₂` give equivalent derived categories, and this file
transports, across that equivalence, the bounded below derived functors
`Functor.rightDerivedFunctorPlus` and the natural transformations between them that the
chapter on crystalline cohomology builds.

## Main definitions

All in the namespace `StacksDraft.DerivedModel.PlusTransport`.

* `fullFunctor h₁ h₂` — the comparison `D(C)` at `h₁` ⥤ `D(C)` at `h₂`, from the uniqueness of
  localizations, with `fullQhIso` identifying the two localization functors.
* `plusFunctor h₁ h₂` — its restriction to the bounded below derived categories, an equivalence,
  with `plusQhIso` identifying the two localization functors out of `K⁺(C)`.
* `rightDerivedIso` — `RF` at the first models, followed by the comparison, is the comparison
  followed by `RF` at the second models.
* `mapDerivedCategoryIso` and `mapDerivedCategoryPlusIso` — the same for an exact functor.

## Main results

* `derivedIso_compat` — the general principle: a transformation out of a right derived functor
  is compatible with the comparisons as soon as its composite with the unit is.
* `rightDerivedFunctorPlusNatTrans_compat`, `rightDerivedPlusCompTrans_compat`,
  `rightDerivedFunctorPlusComp_compat`, `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_compat`
  — the four constructions of the library are compatible with the comparisons.
* `bijective_comp_map_iff_of_iso` — a universal arrow into a functor is carried to a universal
  arrow by an equivalence compatible with that functor.
* `isIso_homEquiv_symm_iff` — the transpose of `g : X ⟶ R Y` across an adjunction is
  invertible exactly when `g` is a universal arrow into `R`.

## Implementation notes

No `@[stacks]` attribute is placed here: the statements are about two Lean choices of the same
mathematical object.  All `HasDerivedCategory` arguments are passed explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.DerivedModel.PlusTransport

/-! ### The abstract principle -/

section Abstract

variable {K : Type*} [Category* K] {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {E₁ : Type*} [Category* E₁] {E₂ : Type*} [Category* E₂]
  (W : MorphismProperty K) {L₁ : K ⥤ D₁} {L₂ : K ⥤ D₂} [L₁.IsLocalization W]
  [L₂.IsLocalization W] {G : D₁ ⥤ D₂} [G.IsEquivalence] {J : E₁ ⥤ E₂} [J.IsEquivalence]
  (hG : L₁ ⋙ G ≅ L₂)

/-- The unit exhibiting `G ⋙ RF₂` as a right derived functor along `L₁` of what `RF₂` is a right
derived functor of along `L₂`. -/
def transportUnit {F₂ : K ⥤ E₂} {RF₂ : D₂ ⥤ E₂} (α₂ : F₂ ⟶ L₂ ⋙ RF₂) :
    F₂ ⟶ L₁ ⋙ (G ⋙ RF₂) :=
  α₂ ≫ Functor.whiskerRight hG.inv RF₂ ≫ (Functor.associator L₁ G RF₂).hom

/-- A right derived functor along `L₂`, precomposed with an equivalence `G` carrying `L₁` to
`L₂`, is a right derived functor along `L₁`. -/
theorem isRightDerivedFunctor_transportUnit {F₂ : K ⥤ E₂} {RF₂ : D₂ ⥤ E₂}
    (α₂ : F₂ ⟶ L₂ ⋙ RF₂) [RF₂.IsRightDerivedFunctor α₂ W] :
    (G ⋙ RF₂).IsRightDerivedFunctor (transportUnit hG α₂) W := by
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  have h₂ : RF₂.IsLeftKanExtension α₂ := by
    rwa [← Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ W]
  rw [← Functor.isLeftKanExtension_iff_precomp_equivalence (G := 𝟭 K) (G' := G)
    (transportUnit hG α₂) α₂ (Functor.leftUnitor L₂ ≪≫ hG.symm)
    (Functor.leftUnitor F₂).symm (Iso.refl (G ⋙ RF₂)) ?_]
  · exact h₂
  · ext X
    simp [transportUnit]

variable {F₁ : K ⥤ E₁} {RF₁ : D₁ ⥤ E₁} (α₁ : F₁ ⟶ L₁ ⋙ RF₁) [RF₁.IsRightDerivedFunctor α₁ W]
  {F₂ : K ⥤ E₂} {RF₂ : D₂ ⥤ E₂} (α₂ : F₂ ⟶ L₂ ⋙ RF₂) [RF₂.IsRightDerivedFunctor α₂ W]
  (hF : F₁ ⋙ J ≅ F₂)

/-- **A right derived functor read at two models**: `RF₁ ⋙ J ≅ G ⋙ RF₂`, both sides being right
derived functors of `F₂` along `L₁`. -/
def derivedIso : RF₁ ⋙ J ≅ G ⋙ RF₂ :=
  letI := isRightDerivedFunctor_transportUnit W hG α₂
  Functor.rightDerivedNatIso (RF₁ ⋙ J) (G ⋙ RF₂)
    (Functor.whiskerRight α₁ J ≫ (Functor.associator L₁ RF₁ J).hom)
    (transportUnit hG α₂) W hF

/-- The defining property of `derivedIso`: it is compatible with the two units. -/
theorem derivedIso_fac (X : K) :
    J.map (α₁.app X) ≫ (derivedIso W hG α₁ α₂ hF).hom.app (L₁.obj X) =
      hF.hom.app X ≫ α₂.app X ≫ RF₂.map (hG.inv.app X) := by
  let := isRightDerivedFunctor_transportUnit W hG α₂
  have h := Functor.rightDerivedNatTrans_app (RF₁ ⋙ J) (G ⋙ RF₂)
    (Functor.whiskerRight α₁ J ≫ (Functor.associator L₁ RF₁ J).hom)
    (transportUnit hG α₂) W hF.hom X
  have ht : (transportUnit hG α₂).app X = α₂.app X ≫ RF₂.map (hG.inv.app X) := by
    simp [transportUnit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id, ht] at h
  exact h

/-- `derivedIso_fac` with the comparison of the localizations moved to the left. -/
theorem derivedIso_fac' (X : K) :
    J.map (α₁.app X) ≫ (derivedIso W hG α₁ α₂ hF).hom.app (L₁.obj X) ≫
        RF₂.map (hG.hom.app X) = hF.hom.app X ≫ α₂.app X := by
  rw [reassoc_of% (derivedIso_fac W hG α₁ α₂ hF X), ← RF₂.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The transport principle.**  Let `θ₁ : RF₁ ⟶ H₁` and `θ₂ : RF₂ ⟶ H₂` be transformations out of
the two right derived functors, and `χ : H₁ ⋙ J ≅ G ⋙ H₂` a comparison of their targets.  If the
composites of `θ₁` and `θ₂` with the units are compatible with `χ`, then `θ₁` and `θ₂` are
compatible with `derivedIso` and `χ`. -/
theorem derivedIso_compat {H₁ : D₁ ⥤ E₁} {H₂ : D₂ ⥤ E₂} (χ : H₁ ⋙ J ≅ G ⋙ H₂)
    (θ₁ : RF₁ ⟶ H₁) (θ₂ : RF₂ ⟶ H₂)
    (h : ∀ X : K, J.map (α₁.app X ≫ θ₁.app (L₁.obj X)) ≫ χ.hom.app (L₁.obj X) ≫
      H₂.map (hG.hom.app X) = hF.hom.app X ≫ α₂.app X ≫ θ₂.app (L₂.obj X)) :
    Functor.whiskerRight θ₁ J ≫ χ.hom =
      (derivedIso W hG α₁ α₂ hF).hom ≫ Functor.whiskerLeft G θ₂ := by
  apply Functor.rightDerived_ext (RF₁ ⋙ J)
    (Functor.whiskerRight α₁ J ≫ (Functor.associator L₁ RF₁ J).hom) W
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.comp_id, Functor.comp_obj]
  rw [reassoc_of% (derivedIso_fac W hG α₁ α₂ hF X)]
  have hθ := θ₂.naturality (hG.inv.app X)
  simp only [Functor.comp_obj] at hθ
  rw [hθ, ← cancel_mono (H₂.map (hG.hom.app X))]
  simp only [Category.assoc, ← H₂.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [← h X, J.map_comp, Category.assoc]

end Abstract

/-! ### Composing comparisons -/

section Compose

variable {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {E₁ : Type*} [Category* E₁] {E₂ : Type*} [Category* E₂]
  {F₁ : Type*} [Category* F₁] {F₂ : Type*} [Category* F₂]
  {G : D₁ ⥤ D₂} {J : E₁ ⥤ E₂} {M : F₁ ⥤ F₂}

/-- Two comparisons pasted: from `H₁ ⋙ J ≅ G ⋙ H₂` and `H₁' ⋙ M ≅ J ⋙ H₂'`, the comparison
`(H₁ ⋙ H₁') ⋙ M ≅ G ⋙ (H₂ ⋙ H₂')`. -/
def transportComp {H₁ : D₁ ⥤ E₁} {H₂ : D₂ ⥤ E₂} {H₁' : E₁ ⥤ F₁} {H₂' : E₂ ⥤ F₂}
    (χ : H₁ ⋙ J ≅ G ⋙ H₂) (χ' : H₁' ⋙ M ≅ J ⋙ H₂') : (H₁ ⋙ H₁') ⋙ M ≅ G ⋙ (H₂ ⋙ H₂') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H₁ χ' ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight χ H₂' ≪≫ Functor.associator _ _ _

/-- The components of `transportComp`. -/
@[simp]
theorem transportComp_hom_app {H₁ : D₁ ⥤ E₁} {H₂ : D₂ ⥤ E₂} {H₁' : E₁ ⥤ F₁} {H₂' : E₂ ⥤ F₂}
    (χ : H₁ ⋙ J ≅ G ⋙ H₂) (χ' : H₁' ⋙ M ≅ J ⋙ H₂') (Y : D₁) :
    (transportComp χ χ').hom.app Y = χ'.hom.app (H₁.obj Y) ≫ H₂'.map (χ.hom.app Y) := by
  simp [transportComp]

/-- Compatible squares compose. -/
theorem compat_comp {H₁ H₁' H₁'' : D₁ ⥤ E₁} {H₂ H₂' H₂'' : D₂ ⥤ E₂}
    {χ : H₁ ⋙ J ≅ G ⋙ H₂} {χ' : H₁' ⋙ J ≅ G ⋙ H₂'} {χ'' : H₁'' ⋙ J ≅ G ⋙ H₂''}
    {θ₁ : H₁ ⟶ H₁'} {θ₂ : H₂ ⟶ H₂'} {φ₁ : H₁' ⟶ H₁''} {φ₂ : H₂' ⟶ H₂''}
    (h : Functor.whiskerRight θ₁ J ≫ χ'.hom = χ.hom ≫ Functor.whiskerLeft G θ₂)
    (h' : Functor.whiskerRight φ₁ J ≫ χ''.hom = χ'.hom ≫ Functor.whiskerLeft G φ₂) :
    Functor.whiskerRight (θ₁ ≫ φ₁) J ≫ χ''.hom =
      χ.hom ≫ Functor.whiskerLeft G (θ₂ ≫ φ₂) := by
  rw [Functor.whiskerRight_comp, Category.assoc, h', ← Category.assoc, h, Category.assoc,
    Functor.whiskerLeft_comp]

/-- A compatible square whiskered on the left by a compared pair. -/
theorem compat_whiskerLeft {H₁ : D₁ ⥤ E₁} {H₂ : D₂ ⥤ E₂} (χ : H₁ ⋙ J ≅ G ⋙ H₂)
    {K₁ K₁' : E₁ ⥤ F₁} {K₂ K₂' : E₂ ⥤ F₂} {ψ : K₁ ⋙ M ≅ J ⋙ K₂} {ψ' : K₁' ⋙ M ≅ J ⋙ K₂'}
    {θ₁ : K₁ ⟶ K₁'} {θ₂ : K₂ ⟶ K₂'}
    (h : Functor.whiskerRight θ₁ M ≫ ψ'.hom = ψ.hom ≫ Functor.whiskerLeft J θ₂) :
    Functor.whiskerRight (Functor.whiskerLeft H₁ θ₁) M ≫ (transportComp χ ψ').hom =
      (transportComp χ ψ).hom ≫ Functor.whiskerLeft G (Functor.whiskerLeft H₂ θ₂) := by
  ext Y
  have h₁ := NatTrans.congr_app h (H₁.obj Y)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at h₁
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    transportComp_hom_app, Functor.comp_obj, Category.assoc]
  rw [reassoc_of% h₁, θ₂.naturality]

end Compose

/-! ### The comparison of two models -/

section Models

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  (h₁ : HasDerivedCategory.{w₁} C) (h₂ : HasDerivedCategory.{w₂} C)

/-- **The comparison of two models of `D(C)`**, from the uniqueness of the localization of the
homotopy category at the acyclic complexes. -/
def fullFunctor : @DerivedCategory C _ _ h₁ ⥤ @DerivedCategory C _ _ h₂ :=
  (Localization.uniq (@DerivedCategory.Qh C _ _ h₁) (@DerivedCategory.Qh C _ _ h₂)
    (HomotopyCategory.subcategoryAcyclic C).trW).functor

/-- The comparison of two models of `D(C)` is an equivalence. -/
instance : (fullFunctor h₁ h₂).IsEquivalence := by
  dsimp only [fullFunctor]
  infer_instance

/-- The comparison identifies the two localization functors out of the homotopy category. -/
def fullQhIso :
    @DerivedCategory.Qh C _ _ h₁ ⋙ fullFunctor h₁ h₂ ≅ @DerivedCategory.Qh C _ _ h₂ :=
  Localization.compUniqFunctor _ _ _

/-- **The comparison of two models of `D⁺(C)`**: the restriction of `fullFunctor`, which carries
bounded below objects to bounded below objects since every bounded below object is the image of
a bounded below complex. -/
def plusFunctor : @DerivedCategory.Plus C _ _ h₁ ⥤ @DerivedCategory.Plus C _ _ h₂ :=
  (@DerivedCategory.TStructure.t C _ _ h₂).plus.lift
    (@DerivedCategory.Plus.ι C _ _ h₁ ⋙ fullFunctor h₁ h₂) (by
      intro X
      let K := (@DerivedCategory.Plus.Qh C _ _ h₁).objPreimage X
      let e := (@DerivedCategory.Plus.Qh C _ _ h₁).objObjPreimageIso X
      exact (@DerivedCategory.TStructure.t C _ _ h₂).plus.prop_of_iso
        ((fullQhIso h₁ h₂).symm.app ((HomotopyCategory.Plus.ι C).obj K) ≪≫
          (fullFunctor h₁ h₂).mapIso ((@DerivedCategory.Plus.ι C _ _ h₁).mapIso e))
        ((@DerivedCategory.Plus.Qh C _ _ h₂).obj K).property)

/-- The comparison of the bounded below derived categories is the restriction of the comparison
of the derived categories, on the nose. -/
theorem ι_obj_plusFunctor_obj (X : @DerivedCategory.Plus C _ _ h₁) :
    (@DerivedCategory.Plus.ι C _ _ h₂).obj ((plusFunctor h₁ h₂).obj X) =
      (fullFunctor h₁ h₂).obj ((@DerivedCategory.Plus.ι C _ _ h₁).obj X) := rfl

/-- The comparison of the bounded below derived categories identifies the two localization
functors out of `K⁺(C)`. -/
def plusQhIso :
    @DerivedCategory.Plus.Qh C _ _ h₁ ⋙ plusFunctor h₁ h₂ ≅ @DerivedCategory.Plus.Qh C _ _ h₂ :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((fullQhIso h₁ h₂).app ((HomotopyCategory.Plus.ι C).obj K)))
    (by
      intro K L f
      ext
      exact (fullQhIso h₁ h₂).hom.naturality ((HomotopyCategory.Plus.ι C).map f))

/-- The comparison of two models of `D⁺(C)` is faithful. -/
instance : (plusFunctor h₁ h₂).Faithful := by
  unfold plusFunctor
  infer_instance

/-- The comparison of two models of `D⁺(C)` is full. -/
instance : (plusFunctor h₁ h₂).Full := by
  unfold plusFunctor
  infer_instance

/-- The comparison of two models of `D⁺(C)` is an equivalence: it is essentially surjective since
every object is the image of a bounded below complex. -/
instance : (plusFunctor h₁ h₂).IsEquivalence where
  essSurj := ⟨fun Y => ⟨(@DerivedCategory.Plus.Qh C _ _ h₁).obj
      ((@DerivedCategory.Plus.Qh C _ _ h₂).objPreimage Y),
    ⟨(plusQhIso h₁ h₂).app _ ≪≫ (@DerivedCategory.Plus.Qh C _ _ h₂).objObjPreimageIso Y⟩⟩⟩

/-- The comparison of the bounded below derived categories carries `X[n]` to `X[n]`. -/
def plusSingleObjIso (n : ℤ) (X : C) :
    (plusFunctor h₁ h₂).obj ((@DerivedCategory.Plus.singleFunctor C _ _ h₁ n).obj X) ≅
      (@DerivedCategory.Plus.singleFunctor C _ _ h₂ n).obj X :=
  (plusFunctor h₁ h₂).mapIso ((@Functor.singleFunctorPlusIsoCompQh C _ _ h₁ n).app X) ≪≫
    (plusQhIso h₁ h₂).app _ ≪≫
    ((@Functor.singleFunctorPlusIsoCompQh C _ _ h₂ n).app X).symm

end Models

/-! ### Right derived functors at two models -/

section Derived

universe wC₁ wC₂ wD₁ wD₂ wE₁ wE₂ vC uC vD uD vE uE

variable {C : Type uC} [Category.{vC} C] [Abelian C] {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  (hC₁ : HasDerivedCategory.{wC₁} C) (hC₂ : HasDerivedCategory.{wC₂} C)
  (hD₁ : HasDerivedCategory.{wD₁} D) (hD₂ : HasDerivedCategory.{wD₂} D)
  (hE₁ : HasDerivedCategory.{wE₁} E) (hE₂ : HasDerivedCategory.{wE₂} E)

/-- **`RF` read at two models**: the right derived functor on bounded below derived categories at
the models `hC₁, hD₁`, followed by the comparison, is the comparison followed by the right derived
functor at the models `hC₂, hD₂`. -/
def rightDerivedIso (F : C ⥤ D) [F.Additive] [EnoughInjectives C] :
    @Functor.rightDerivedFunctorPlus C D _ _ _ _ hC₁ hD₁ F _ _ ⋙ plusFunctor hD₁ hD₂ ≅
      plusFunctor hC₁ hC₂ ⋙ @Functor.rightDerivedFunctorPlus C D _ _ _ _ hC₂ hD₂ F _ _ :=
  derivedIso (HomotopyCategory.Plus.quasiIso C) (plusQhIso hC₁ hC₂)
    (@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₁ hD₁ F _ _)
    (@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₂ hD₂ F _ _)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F.mapHomotopyCategoryPlus (plusQhIso hD₁ hD₂))

/-- The defining property of `rightDerivedIso`: it is compatible with the two units. -/
theorem rightDerivedIso_fac (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    (X : HomotopyCategory.Plus C) :
    (plusFunctor hD₁ hD₂).map
        ((@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₁ hD₁ F _ _).app X) ≫
      (rightDerivedIso hC₁ hC₂ hD₁ hD₂ F).hom.app ((@DerivedCategory.Plus.Qh C _ _ hC₁).obj X) ≫
        (@Functor.rightDerivedFunctorPlus C D _ _ _ _ hC₂ hD₂ F _ _).map
          ((plusQhIso hC₁ hC₂).hom.app X) =
      (plusQhIso hD₁ hD₂).hom.app (F.mapHomotopyCategoryPlus.obj X) ≫
        (@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₂ hD₂ F _ _).app X := by
  have h := derivedIso_fac' (HomotopyCategory.Plus.quasiIso C) (plusQhIso hC₁ hC₂)
    (@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₁ hD₁ F _ _)
    (@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₂ hD₂ F _ _)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F.mapHomotopyCategoryPlus (plusQhIso hD₁ hD₂)) X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp] at h
  exact h

/-- **The transport principle for `RF`**: a transformation out of `RF`, given at both models,
is compatible with `rightDerivedIso` as soon as its composite with the units is. -/
theorem rightDerivedIso_compat (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    {H₁ : @DerivedCategory.Plus C _ _ hC₁ ⥤ @DerivedCategory.Plus D _ _ hD₁}
    {H₂ : @DerivedCategory.Plus C _ _ hC₂ ⥤ @DerivedCategory.Plus D _ _ hD₂}
    (χ : H₁ ⋙ plusFunctor hD₁ hD₂ ≅ plusFunctor hC₁ hC₂ ⋙ H₂)
    (θ₁ : @Functor.rightDerivedFunctorPlus C D _ _ _ _ hC₁ hD₁ F _ _ ⟶ H₁)
    (θ₂ : @Functor.rightDerivedFunctorPlus C D _ _ _ _ hC₂ hD₂ F _ _ ⟶ H₂)
    (h : ∀ X : HomotopyCategory.Plus C,
      (plusFunctor hD₁ hD₂).map
          ((@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₁ hD₁ F _ _).app X ≫
            θ₁.app ((@DerivedCategory.Plus.Qh C _ _ hC₁).obj X)) ≫
        χ.hom.app ((@DerivedCategory.Plus.Qh C _ _ hC₁).obj X) ≫
          H₂.map ((plusQhIso hC₁ hC₂).hom.app X) =
      (plusQhIso hD₁ hD₂).hom.app (F.mapHomotopyCategoryPlus.obj X) ≫
        (@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₂ hD₂ F _ _).app X ≫
          θ₂.app ((@DerivedCategory.Plus.Qh C _ _ hC₂).obj X)) :
    Functor.whiskerRight θ₁ (plusFunctor hD₁ hD₂) ≫ χ.hom =
      (rightDerivedIso hC₁ hC₂ hD₁ hD₂ F).hom ≫ Functor.whiskerLeft (plusFunctor hC₁ hC₂) θ₂ :=
  derivedIso_compat (HomotopyCategory.Plus.quasiIso C) (plusQhIso hC₁ hC₂)
    (@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₁ hD₁ F _ _)
    (@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₂ hD₂ F _ _)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F.mapHomotopyCategoryPlus (plusQhIso hD₁ hD₂)) χ θ₁ θ₂
    (fun X => by simpa using h X)

/-- **`Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans` at two models**: the morphism of
right derived functors induced by `τ : F ⟶ F'` is compatible with the comparisons. -/
theorem rightDerivedFunctorPlusNatTrans_compat {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    [EnoughInjectives C] (τ : F ⟶ F') :
    Functor.whiskerRight
        (@Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans C D _ _ _ _ _ hC₁ hD₁ F F' _ _ τ)
        (plusFunctor hD₁ hD₂) ≫ (rightDerivedIso hC₁ hC₂ hD₁ hD₂ F').hom =
      (rightDerivedIso hC₁ hC₂ hD₁ hD₂ F).hom ≫ Functor.whiskerLeft (plusFunctor hC₁ hC₂)
        (@Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans C D _ _ _ _ _ hC₂ hD₂ F F' _ _
          τ) := by
  refine rightDerivedIso_compat hC₁ hC₂ hD₁ hD₂ F _ _ _ (fun X => ?_)
  rw [@Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans_app C D _ _ _ _ _ hC₁ hD₁ F F' _ _
      τ X,
    @Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans_app C D _ _ _ _ _ hC₂ hD₂ F F' _ _
      τ X, Functor.map_comp,
    Category.assoc, rightDerivedIso_fac]
  have hn := (plusQhIso hD₁ hD₂).hom.naturality
    ((Functor.mapHomotopyCategoryPlusNatTrans τ).app X)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

/-- **The comparison transformation `G(F(K)) ⟶ RG(RF(K))` at two models** is compatible with the
comparisons. -/
theorem rightComparisonUnit_compat (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive]
    [EnoughInjectives C] [EnoughInjectives D] (X : HomotopyCategory.Plus C) :
    (plusFunctor hE₁ hE₂).map
        ((@Functor.rightComparisonUnit C D E _ _ _ _ _ _ hC₁ hD₁ hE₁ P Q _ _ _ _).app X) ≫
      (transportComp (rightDerivedIso hC₁ hC₂ hD₁ hD₂ P)
          (rightDerivedIso hD₁ hD₂ hE₁ hE₂ Q)).hom.app
        ((@DerivedCategory.Plus.Qh C _ _ hC₁).obj X) ≫
        (@Functor.rightDerivedFunctorPlus D E _ _ _ _ hD₂ hE₂ Q _ _).map
          ((@Functor.rightDerivedFunctorPlus C D _ _ _ _ hC₂ hD₂ P _ _).map
            ((plusQhIso hC₁ hC₂).hom.app X)) =
      (plusQhIso hE₁ hE₂).hom.app ((P ⋙ Q).mapHomotopyCategoryPlus.obj X) ≫
        (@Functor.rightComparisonUnit C D E _ _ _ _ _ _ hC₂ hD₂ hE₂ P Q _ _ _ _).app X := by
  rw [@Functor.rightComparisonUnit_app C D E _ _ _ _ _ _ hC₁ hD₁ hE₁ P Q _ _ _ _ X,
    @Functor.rightComparisonUnit_app C D E _ _ _ _ _ _ hC₂ hD₂ hE₂ P Q _ _ _ _ X,
    transportComp_hom_app]
  have a := (rightDerivedIso hD₁ hD₂ hE₁ hE₂ Q).hom.naturality
    ((@Functor.rightDerivedFunctorPlusUnith C D _ _ _ _ hC₁ hD₁ P _ _).app X)
  have b := congrArg (@Functor.rightDerivedFunctorPlus D E _ _ _ _ hD₂ hE₂ Q _ _).map
    (rightDerivedIso_fac hC₁ hC₂ hD₁ hD₂ P X)
  have c := rightDerivedIso_fac hD₁ hD₂ hE₁ hE₂ Q (P.mapHomotopyCategoryPlus.obj X)
  have d := (plusQhIso hE₁ hE₂).hom.naturality
    ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ Q))).inv.app X)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp] at a b c d
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% a, b, reassoc_of% c, reassoc_of% d]

/-- **`Stacks.DerivedIndexing.rightDerivedPlusCompTrans` at two models**: the canonical map
`R(Q ∘ P) ⟶ RQ ∘ RP` of [Stacks, Tag 05T2] is compatible with the comparisons. -/
theorem rightDerivedPlusCompTrans_compat (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive]
    [EnoughInjectives C] [EnoughInjectives D] :
    Functor.whiskerRight
        (@Stacks.DerivedIndexing.rightDerivedPlusCompTrans C D E _ _ _ _ _ _ hC₁ hD₁ hE₁ _ _ P Q
          _ _) (plusFunctor hE₁ hE₂) ≫
      (transportComp (rightDerivedIso hC₁ hC₂ hD₁ hD₂ P)
        (rightDerivedIso hD₁ hD₂ hE₁ hE₂ Q)).hom =
      (rightDerivedIso hC₁ hC₂ hE₁ hE₂ (P ⋙ Q)).hom ≫
        Functor.whiskerLeft (plusFunctor hC₁ hC₂)
          (@Stacks.DerivedIndexing.rightDerivedPlusCompTrans C D E _ _ _ _ _ _ hC₂ hD₂ hE₂ _ _ P Q
            _ _) := by
  refine rightDerivedIso_compat hC₁ hC₂ hE₁ hE₂ (P ⋙ Q) _ _ _ (fun X => ?_)
  rw [@Stacks.DerivedIndexing.rightDerivedPlusCompTrans_fac_app C D E _ _ _ _ _ _ hC₁ hD₁ hE₁ _ _
      P Q _ _ X,
    @Stacks.DerivedIndexing.rightDerivedPlusCompTrans_fac_app C D E _ _ _ _ _ _ hC₂ hD₂ hE₂ _ _
      P Q _ _ X]
  exact rightComparisonUnit_compat hC₁ hC₂ hD₁ hD₂ hE₁ hE₂ P Q X

/-- **`CategoryTheory.Functor.rightDerivedFunctorPlusComp` at two models**: the canonical map
`R(G ∘ F) ⟶ RG ∘ RF` is compatible with the comparisons. -/
theorem rightDerivedFunctorPlusComp_compat (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive]
    [EnoughInjectives C] [EnoughInjectives D] :
    Functor.whiskerRight
        (@Functor.rightDerivedFunctorPlusComp C D E _ _ _ _ _ _ hC₁ hD₁ hE₁ P Q _ _ _ _)
        (plusFunctor hE₁ hE₂) ≫
      (transportComp (rightDerivedIso hC₁ hC₂ hD₁ hD₂ P)
        (rightDerivedIso hD₁ hD₂ hE₁ hE₂ Q)).hom =
      (rightDerivedIso hC₁ hC₂ hE₁ hE₂ (P ⋙ Q)).hom ≫
        Functor.whiskerLeft (plusFunctor hC₁ hC₂)
          (@Functor.rightDerivedFunctorPlusComp C D E _ _ _ _ _ _ hC₂ hD₂ hE₂ P Q _ _ _ _) := by
  refine rightDerivedIso_compat hC₁ hC₂ hE₁ hE₂ (P ⋙ Q) _ _ _ (fun X => ?_)
  have h₁ := NatTrans.congr_app
    (@Functor.rightDerivedFunctorPlusComp_fac C D E _ _ _ _ _ _ hC₁ hD₁ hE₁ P Q _ _ _ _) X
  have h₂ := NatTrans.congr_app
    (@Functor.rightDerivedFunctorPlusComp_fac C D E _ _ _ _ _ _ hC₂ hD₂ hE₂ P Q _ _ _ _) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁ h₂
  rw [h₁, h₂]
  exact rightComparisonUnit_compat hC₁ hC₂ hD₁ hD₂ hE₁ hE₂ P Q X

end Derived

/-! ### Exact functors at two models -/

section Exact

universe wA₁ wA₂ wB₁ wB₂ vA uA vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] {B : Type uB} [Category.{vB} B] [Abelian B]
  (hA₁ : HasDerivedCategory.{wA₁} A) (hA₂ : HasDerivedCategory.{wA₂} A)
  (hB₁ : HasDerivedCategory.{wB₁} B) (hB₂ : HasDerivedCategory.{wB₂} B)
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **An exact functor read at two models**: `F.mapDerivedCategory` at the first models, followed
by the comparison, is the comparison followed by `F.mapDerivedCategory` at the second models. Both
lift `F` applied degreewise followed by the second localization functor. -/
def mapDerivedCategoryIso :
    @Functor.mapDerivedCategory A _ _ hA₁ B _ _ hB₁ F _ _ _ ⋙ fullFunctor hB₁ hB₂ ≅
      fullFunctor hA₁ hA₂ ⋙ @Functor.mapDerivedCategory A _ _ hA₂ B _ _ hB₂ F _ _ _ :=
  letI : Localization.Lifting (@DerivedCategory.Qh A _ _ hA₁)
      (HomotopyCategory.subcategoryAcyclic A).trW
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ @DerivedCategory.Qh B _ _ hB₂)
      (@Functor.mapDerivedCategory A _ _ hA₁ B _ _ hB₁ F _ _ _ ⋙ fullFunctor hB₁ hB₂) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (@Functor.mapDerivedCategoryFactorsh A _ _ hA₁ B _ _ hB₁ F _ _ _)
        (fullFunctor hB₁ hB₂) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (fullQhIso hB₁ hB₂)⟩
  letI : Localization.Lifting (@DerivedCategory.Qh A _ _ hA₁)
      (HomotopyCategory.subcategoryAcyclic A).trW
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ @DerivedCategory.Qh B _ _ hB₂)
      (fullFunctor hA₁ hA₂ ⋙ @Functor.mapDerivedCategory A _ _ hA₂ B _ _ hB₂ F _ _ _) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (fullQhIso hA₁ hA₂)
        (@Functor.mapDerivedCategory A _ _ hA₂ B _ _ hB₂ F _ _ _) ≪≫
      @Functor.mapDerivedCategoryFactorsh A _ _ hA₂ B _ _ hB₂ F _ _ _⟩
  Localization.liftNatIso (@DerivedCategory.Qh A _ _ hA₁)
    (HomotopyCategory.subcategoryAcyclic A).trW
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ @DerivedCategory.Qh B _ _ hB₂)
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ @DerivedCategory.Qh B _ _ hB₂)
    (@Functor.mapDerivedCategory A _ _ hA₁ B _ _ hB₁ F _ _ _ ⋙ fullFunctor hB₁ hB₂)
    (fullFunctor hA₁ hA₂ ⋙ @Functor.mapDerivedCategory A _ _ hA₂ B _ _ hB₂ F _ _ _) (Iso.refl _)

/-- `mapDerivedCategoryIso` on the image of a complex. -/
theorem mapDerivedCategoryIso_hom_app (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapDerivedCategoryIso hA₁ hA₂ hB₁ hB₂ F).hom.app
        ((@DerivedCategory.Qh A _ _ hA₁).obj X) =
      (fullFunctor hB₁ hB₂).map
          ((@Functor.mapDerivedCategoryFactorsh A _ _ hA₁ B _ _ hB₁ F _ _ _).hom.app X) ≫
        (fullQhIso hB₁ hB₂).hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
          (@Functor.mapDerivedCategoryFactorsh A _ _ hA₂ B _ _ hB₂ F _ _ _).inv.app X ≫
            (@Functor.mapDerivedCategory A _ _ hA₂ B _ _ hB₂ F _ _ _).map
              ((fullQhIso hA₁ hA₂).inv.app X) := by
  dsimp only [mapDerivedCategoryIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

/-- **The bounded below version of `mapDerivedCategoryIso`**: its restriction to the bounded
below derived categories. -/
def mapDerivedCategoryPlusIso :
    @Functor.mapDerivedCategoryPlus A _ _ hA₁ B _ _ hB₁ F _ _ _ ⋙ plusFunctor hB₁ hB₂ ≅
      plusFunctor hA₁ hA₂ ⋙ @Functor.mapDerivedCategoryPlus A _ _ hA₂ B _ _ hB₂ F _ _ _ :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _
      ((mapDerivedCategoryIso hA₁ hA₂ hB₁ hB₂ F).app ((@DerivedCategory.Plus.ι A _ _ hA₁).obj X)))
    (by
      intro X Y f
      ext
      exact (mapDerivedCategoryIso hA₁ hA₂ hB₁ hB₂ F).hom.naturality
        ((@DerivedCategory.Plus.ι A _ _ hA₁).map f))

/-- `mapDerivedCategoryPlusIso` is `mapDerivedCategoryIso` on the underlying objects. -/
theorem ι_map_mapDerivedCategoryPlusIso_hom_app (X : @DerivedCategory.Plus A _ _ hA₁) :
    (@DerivedCategory.Plus.ι B _ _ hB₂).map
        ((mapDerivedCategoryPlusIso hA₁ hA₂ hB₁ hB₂ F).hom.app X) =
      (mapDerivedCategoryIso hA₁ hA₂ hB₁ hB₂ F).hom.app
        ((@DerivedCategory.Plus.ι A _ _ hA₁).obj X) := rfl

/-- The defining property of `mapDerivedCategoryPlusIso`, on the image of a bounded below
complex. -/
theorem mapDerivedCategoryPlusIso_fac (X : HomotopyCategory.Plus A) :
    (plusFunctor hB₁ hB₂).map
        ((@Functor.mapDerivedCategoryPlusFactorsh A _ _ hA₁ B _ _ hB₁ F _ _ _).inv.app X) ≫
      (mapDerivedCategoryPlusIso hA₁ hA₂ hB₁ hB₂ F).hom.app
        ((@DerivedCategory.Plus.Qh A _ _ hA₁).obj X) ≫
        (@Functor.mapDerivedCategoryPlus A _ _ hA₂ B _ _ hB₂ F _ _ _).map
          ((plusQhIso hA₁ hA₂).hom.app X) =
      (plusQhIso hB₁ hB₂).hom.app (F.mapHomotopyCategoryPlus.obj X) ≫
        (@Functor.mapDerivedCategoryPlusFactorsh A _ _ hA₂ B _ _ hB₂ F _ _ _).inv.app X := by
  ext
  have h := mapDerivedCategoryIso_hom_app hA₁ hA₂ hB₁ hB₂ F X.obj
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  change (fullFunctor hB₁ hB₂).map
      ((@Functor.mapDerivedCategoryFactorsh A _ _ hA₁ B _ _ hB₁ F _ _ _).inv.app X.obj) ≫
      (mapDerivedCategoryIso hA₁ hA₂ hB₁ hB₂ F).hom.app
        ((@DerivedCategory.Qh A _ _ hA₁).obj X.obj) ≫
        (@Functor.mapDerivedCategory A _ _ hA₂ B _ _ hB₂ F _ _ _).map
          ((fullQhIso hA₁ hA₂).hom.app X.obj) =
    (fullQhIso hB₁ hB₂).hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X.obj) ≫
      (@Functor.mapDerivedCategoryFactorsh A _ _ hA₂ B _ _ hB₂ F _ _ _).inv.app X.obj
  rw [h]
  simp only [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The unit of `RF`, followed by the identification of `RF` with `F.mapDerivedCategoryPlus` for
an exact `F`, is the identification of `F.mapDerivedCategoryPlus` as a lift. -/
theorem rightDerivedFunctorPlusUnit_comp_isoMapDerivedCategoryPlus_hom
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : HomotopyCategory.Plus A) :
    F.rightDerivedFunctorPlusUnith.app X ≫
        (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus).hom.app
          (DerivedCategory.Plus.Qh.obj X) =
      F.mapDerivedCategoryPlusFactorsh.inv.app X := by
  dsimp only [Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

/-- **`CategoryTheory.Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus` at two models**:
the identification `RF ≅ F.mapDerivedCategoryPlus` for an exact `F` is compatible with the
comparisons. -/
theorem rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_compat [EnoughInjectives A] :
    Functor.whiskerRight
        (@Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus A _ _ hA₁ B _ _ hB₁ _ F _ _
          _).hom (plusFunctor hB₁ hB₂) ≫ (mapDerivedCategoryPlusIso hA₁ hA₂ hB₁ hB₂ F).hom =
      (rightDerivedIso hA₁ hA₂ hB₁ hB₂ F).hom ≫ Functor.whiskerLeft (plusFunctor hA₁ hA₂)
        (@Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus A _ _ hA₂ B _ _ hB₂ _ F _ _
          _).hom := by
  refine rightDerivedIso_compat hA₁ hA₂ hB₁ hB₂ F _ _ _ (fun X => ?_)
  rw [@rightDerivedFunctorPlusUnit_comp_isoMapDerivedCategoryPlus_hom A _ _ B _ _ F _ hA₁ hB₁ _
      _ _ X,
    @rightDerivedFunctorPlusUnit_comp_isoMapDerivedCategoryPlus_hom A _ _ B _ _ F _ hA₂ hB₂ _
      _ _ X]
  exact mapDerivedCategoryPlusIso_fac hA₁ hA₂ hB₁ hB₂ F X

end Exact

/-! ### Universal arrows -/

section Universal

variable {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂]
  {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]

/-- **The transpose of a map across an adjunction is invertible exactly when the map is a
universal arrow**: for `adj : L ⊣ R` and `g : X ⟶ R Y`, the transpose `L X ⟶ Y` is an
isomorphism if and only if every map `X ⟶ R Z` factors uniquely as `g` followed by `R` of a map
`Y ⟶ Z`. -/
theorem isIso_homEquiv_symm_iff {L : C₁ ⥤ D₁} {R : D₁ ⥤ C₁} (adj : L ⊣ R) {X : C₁} {Y : D₁}
    (g : X ⟶ R.obj Y) :
    IsIso ((adj.homEquiv X Y).symm g) ↔
      ∀ Z : D₁, Function.Bijective (fun f : Y ⟶ Z => g ≫ R.map f) := by
  rw [isIso_iff_coyoneda_map_bijective]
  refine forall_congr' fun Z => ?_
  have : (fun f : Y ⟶ Z => g ≫ R.map f) =
      adj.homEquiv X Z ∘ (fun f : Y ⟶ Z => (adj.homEquiv X Y).symm g ≫ f) := by
    funext f
    simp [Adjunction.homEquiv_naturality_right]
  rw [this, Equiv.comp_bijective]

/-- Being a universal arrow is invariant under precomposition with an isomorphism. -/
theorem bijective_comp_map_iff_of_iso_left {R : D₁ ⥤ C₁} {X X' : C₁} {Y : D₁} (a : X' ≅ X)
    (g : X ⟶ R.obj Y) :
    (∀ Z : D₁, Function.Bijective (fun f : Y ⟶ Z => (a.hom ≫ g) ≫ R.map f)) ↔
      ∀ Z : D₁, Function.Bijective (fun f : Y ⟶ Z => g ≫ R.map f) := by
  refine forall_congr' fun Z => ?_
  have : (fun f : Y ⟶ Z => (a.hom ≫ g) ≫ R.map f) =
      ⇑((Iso.homCongr a (Iso.refl _)).symm : (X ⟶ R.obj Z) ≃ (X' ⟶ R.obj Z)) ∘
        (fun f : Y ⟶ Z => g ≫ R.map f) := by
    funext f
    simp [Iso.homCongr]
  rw [this, Equiv.comp_bijective]

/-- Being a universal arrow is invariant under postcomposition with `R` of an isomorphism. -/
theorem bijective_comp_map_iff_of_iso_right {R : D₁ ⥤ C₁} {X : C₁} {Y Y' : D₁} (b : Y ≅ Y')
    (g : X ⟶ R.obj Y) :
    (∀ Z : D₁, Function.Bijective (fun f : Y' ⟶ Z => (g ≫ R.map b.hom) ≫ R.map f)) ↔
      ∀ Z : D₁, Function.Bijective (fun f : Y ⟶ Z => g ≫ R.map f) := by
  refine forall_congr' fun Z => ?_
  have : (fun f : Y' ⟶ Z => (g ≫ R.map b.hom) ≫ R.map f) =
      (fun f : Y ⟶ Z => g ≫ R.map f) ∘
        ⇑((Iso.homCongr b (Iso.refl _)).symm : (Y' ⟶ Z) ≃ (Y ⟶ Z)) := by
    funext f
    simp [Iso.homCongr]
  rw [this, Equiv.bijective_comp]

/-- **A universal arrow is carried to a universal arrow by an equivalence compatible with the
functor.**  Let `e : D₁ ⥤ D₂` be an equivalence, `e' : C₁ ⥤ C₂` fully faithful, and
`τ : R₁ ⋙ e' ≅ e ⋙ R₂`.  If `g₂ : X₂ ⟶ R₂ Y₂` is `e' g₁` up to isomorphisms `a` of the sources and
`b` of the targets, then `g₁` is a universal arrow into `R₁` exactly when `g₂` is one into
`R₂`. -/
theorem bijective_comp_map_iff_of_iso (e : D₁ ⥤ D₂) [e.IsEquivalence] (e' : C₁ ⥤ C₂)
    [e'.Full] [e'.Faithful] {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} (τ : R₁ ⋙ e' ≅ e ⋙ R₂)
    {X₁ : C₁} {Y₁ : D₁} {X₂ : C₂} {Y₂ : D₂} (g₁ : X₁ ⟶ R₁.obj Y₁) (g₂ : X₂ ⟶ R₂.obj Y₂)
    (a : e'.obj X₁ ≅ X₂) (b : e.obj Y₁ ≅ Y₂)
    (h : e'.map g₁ ≫ τ.hom.app Y₁ ≫ R₂.map b.hom = a.hom ≫ g₂) :
    (∀ Z : D₁, Function.Bijective (fun f : Y₁ ⟶ Z => g₁ ≫ R₁.map f)) ↔
      ∀ Z : D₂, Function.Bijective (fun f : Y₂ ⟶ Z => g₂ ≫ R₂.map f) := by
  have key : ∀ Z : D₁, Function.Bijective (fun f : Y₁ ⟶ Z => g₁ ≫ R₁.map f) ↔
      Function.Bijective (fun f : Y₂ ⟶ e.obj Z => g₂ ≫ R₂.map f) := by
    intro Z
    let eY : (Y₁ ⟶ Z) ≃ (Y₂ ⟶ e.obj Z) :=
      (Functor.FullyFaithful.ofFullyFaithful e).homEquiv.trans (Iso.homCongr b (Iso.refl _))
    let eX : (X₁ ⟶ R₁.obj Z) ≃ (X₂ ⟶ R₂.obj (e.obj Z)) :=
      (Functor.FullyFaithful.ofFullyFaithful e').homEquiv.trans (Iso.homCongr a (τ.app Z))
    have hc : (fun f : Y₂ ⟶ e.obj Z => g₂ ≫ R₂.map f) ∘ eY =
        eX ∘ (fun f : Y₁ ⟶ Z => g₁ ≫ R₁.map f) := by
      funext f
      have hτ := τ.hom.naturality f
      simp only [Functor.comp_map] at hτ
      have h' : g₂ = a.inv ≫ e'.map g₁ ≫ τ.hom.app Y₁ ≫ R₂.map b.hom := by
        rw [h, Iso.inv_hom_id_assoc]
      simp [eY, eX, Iso.homCongr, h', hτ]
    rw [← Equiv.bijective_comp eY, hc, Equiv.comp_bijective]
  constructor
  · intro h₁ Z
    have := (key (e.objPreimage Z)).1 (h₁ _)
    let c := e.objObjPreimageIso Z
    have hc : (fun f : Y₂ ⟶ Z => g₂ ≫ R₂.map f) =
        ⇑((Iso.homCongr (Iso.refl _) (R₂.mapIso c)) : _ ≃ _) ∘
          (fun f : Y₂ ⟶ e.obj (e.objPreimage Z) => g₂ ≫ R₂.map f) ∘
            ⇑((Iso.homCongr (Iso.refl _) c).symm : (Y₂ ⟶ Z) ≃ _) := by
      funext f
      simp [Iso.homCongr]
    rw [hc, Equiv.comp_bijective, Equiv.bijective_comp]
    exact this
  · intro h₂ Z
    exact (key Z).2 (h₂ _)

end Universal

end StacksDraft.DerivedModel.PlusTransport

end
