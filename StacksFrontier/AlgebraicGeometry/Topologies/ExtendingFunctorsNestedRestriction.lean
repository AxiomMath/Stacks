module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsRestrictionFullness

/-!
# Restricting morphisms between two nested full subcategories of schemes over a base

Let `S` be a scheme and let `𝒞₂ ⊆ 𝒞₁` be two full subcategories of `Sch/S`, both satisfying the
conditions (1) and (2) of Stacks 0EUW. For two functors `F` and `G` on `𝒞₁` satisfying conditions
(a) and (b) of Stacks 0EUW, restriction along the inclusion `𝒞₂ ⊆ 𝒞₁` is a bijection between the
morphisms `F ⟶ G` and the morphisms between their restrictions to `𝒞₂`.

For `𝒞₁` the whole of `Sch/S` this is the full faithfulness of the restriction functor of
Stacks 0GE3 (`AlgebraicGeometry.ExtendingFunctors.faithful_limitPreservingRestriction` and
`AlgebraicGeometry.ExtendingFunctors.full_limitPreservingRestriction`).

## Main results

* `AlgebraicGeometry.ExtendingFunctors.isZariskiSheafOnSubcategory_ιOfLE` and
  `AlgebraicGeometry.ExtendingFunctors.preservesAffineLimitsOnSubcategory_ιOfLE`: conditions (a)
  and (b) of Stacks 0EUW pass to a smaller full subcategory.
* `AlgebraicGeometry.ExtendingFunctors.existsUnique_hom_whiskerLeft_ιOfLE_eq`: the restriction
  of morphisms from `𝒞₁` to `𝒞₂` is bijective.

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 0GE3](https://stacks.math.columbia.edu/tag/0GE3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable {S : Scheme.{u}} {P₁ P₂ : ObjectProperty (Over S)}

/-! ### The conditions of Stacks 0EUW pass to a smaller full subcategory -/

/-- **Condition (a) of Stacks 0EUW passes to a smaller full subcategory.** If a functor `F` on
`𝒞₁` satisfies condition (a) of Stacks 0EUW, then so does its restriction to `𝒞₂ ⊆ 𝒞₁`. -/
theorem isZariskiSheafOnSubcategory_ιOfLE (h : P₂ ≤ P₁)
    {F : P₁.FullSubcategoryᵒᵖ ⥤ Type w} (hF : IsZariskiSheafOnSubcategory P₁ F) :
    IsZariskiSheafOnSubcategory P₂ ((ObjectProperty.ιOfLE h).op ⋙ F) := by
  intro X ι Y f hfopen hfcov K U a b haopen hab hcov s hs
  exact hF ((ObjectProperty.ιOfLE h).obj X) ι (fun i => (ObjectProperty.ιOfLE h).obj (Y i))
    (fun i => (ObjectProperty.ιOfLE h).map (f i)) hfopen hfcov K
    (fun i j k => (ObjectProperty.ιOfLE h).obj (U i j k))
    (fun i j k => (ObjectProperty.ιOfLE h).map (a i j k))
    (fun i j k => (ObjectProperty.ιOfLE h).map (b i j k)) haopen
    (fun i j k => by rw [← Functor.map_comp, ← Functor.map_comp, hab]) hcov s hs

/-- **Condition (b) of Stacks 0EUW passes to a smaller full subcategory.** If a functor `F` on
`𝒞₁` satisfies condition (b) of Stacks 0EUW, then so does its restriction to `𝒞₂ ⊆ 𝒞₁`. -/
theorem preservesAffineLimitsOnSubcategory_ιOfLE (h : P₂ ≤ P₁)
    {F : P₁.FullSubcategoryᵒᵖ ⥤ Type w} (hF : PreservesAffineLimitsOnSubcategory P₁ F) :
    PreservesAffineLimitsOnSubcategory P₂ ((ObjectProperty.ιOfLE h).op ⋙ F) := by
  intro Λ _ _ _ D haff c hc
  exact hF Λ (D ⋙ ObjectProperty.ιOfLE h) haff ((ObjectProperty.ιOfLE h).mapCone c) hc

/-! ### Restriction of morphisms -/

/-- **Restriction of morphisms between nested full subcategories is bijective.** Let
`𝒞₂ ⊆ 𝒞₁` be full subcategories of `Sch/S` both satisfying conditions (1) and (2) of
Stacks 0EUW, and let `F` and `G` be functors on `𝒞₁` satisfying conditions (a) and (b) of
Stacks 0EUW. Every morphism between the restrictions of `F` and `G` to `𝒞₂` is the restriction
of exactly one morphism `F ⟶ G`. -/
theorem existsUnique_hom_whiskerLeft_ιOfLE_eq (h : P₂ ≤ P₁)
    (hP1₁ : HasAffineOpens P₁) (hP2₁ : HasFinitePresentationAffines P₁)
    (hP1₂ : HasAffineOpens P₂) (hP2₂ : HasFinitePresentationAffines P₂)
    {F G : P₁.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))}
    (haF : IsZariskiSheafOnSubcategory P₁ F) (hbF : PreservesAffineLimitsOnSubcategory P₁ F)
    (haG : IsZariskiSheafOnSubcategory P₁ G) (hbG : PreservesAffineLimitsOnSubcategory P₁ G)
    (σ : (ObjectProperty.ιOfLE h).op ⋙ F ⟶ (ObjectProperty.ιOfLE h).op ⋙ G) :
    ∃! θ : F ⟶ G, Functor.whiskerLeft (ObjectProperty.ιOfLE h).op θ = σ := by
  let ι₂ := ObjectProperty.ιOfLE h
  have haF₂ := isZariskiSheafOnSubcategory_ιOfLE h haF
  have hbF₂ := preservesAffineLimitsOnSubcategory_ιOfLE h hbF
  have haG₂ := isZariskiSheafOnSubcategory_ιOfLE h haG
  have hbG₂ := preservesAffineLimitsOnSubcategory_ιOfLE h hbG
  have hiF := isIso_restrictionHom F hP1₁ hP2₁ haF hbF
  have hiG := isIso_restrictionHom G hP1₁ hP2₁ haG hbG
  let αF : P₁.ι.op ⋙ extension P₁ F ≅ F := asIso (restrictionHom F hP1₁ haF)
  let αG : P₁.ι.op ⋙ extension P₁ G ≅ G := asIso (restrictionHom G hP1₁ haG)
  have hzF := isZariskiSheaf_extension P₁ F hP1₁ hP2₁ haF
  have hlF := preservesAffineLimits_extension F hP1₁ hP2₁ haF
  have hzG := isZariskiSheaf_extension P₁ G hP1₁ hP2₁ haG
  have hlG := preservesAffineLimits_extension G hP1₁ hP2₁ haG
  have hex : ∃ θ' : extension P₁ F ⟶ extension P₁ G, Functor.whiskerLeft P₂.ι.op θ' =
      Functor.whiskerLeft ι₂.op αF.hom ≫ σ ≫ Functor.whiskerLeft ι₂.op αG.inv := by
    obtain ⟨_, -, -, -, huF⟩ := exists_unique_extension hP1₂ hP2₂ haF₂ hbF₂
    obtain ⟨_, -, -, -, huG⟩ := exists_unique_extension hP1₂ hP2₂ haG₂ hbG₂
    obtain ⟨e₁⟩ := huF (extension P₂ (ι₂.op ⋙ F))
      (isZariskiSheaf_extension P₂ _ hP1₂ hP2₂ haF₂)
      (preservesAffineLimits_extension _ hP1₂ hP2₂ haF₂)
      (nonempty_restrictionIso _ hP1₂ hP2₂ haF₂ hbF₂).some
    obtain ⟨e₂⟩ := huF (extension P₁ F) hzF hlF (Functor.isoWhiskerLeft ι₂.op αF)
    obtain ⟨e₃⟩ := huG (extension P₂ (ι₂.op ⋙ G))
      (isZariskiSheaf_extension P₂ _ hP1₂ hP2₂ haG₂)
      (preservesAffineLimits_extension _ hP1₂ hP2₂ haG₂)
      (nonempty_restrictionIso _ hP1₂ hP2₂ haG₂ hbG₂).some
    obtain ⟨e₄⟩ := huG (extension P₁ G) hzG hlG (Functor.isoWhiskerLeft ι₂.op αG)
    exact exists_map_eq_of_iso ((Functor.whiskeringLeft _ _ _).obj P₂.ι.op)
      (e₁.symm.trans e₂) (e₃.symm.trans e₄)
      (fun σ' => exists_whiskerLeft_eq_of_extension hP1₂ hP2₂ haF₂ hbF₂ haG₂ hbG₂ σ') _
  have huniq : ∀ θ θ' : F ⟶ G, Functor.whiskerLeft ι₂.op θ = Functor.whiskerLeft ι₂.op θ' →
      θ = θ' := by
    intro θ θ' hθθ'
    have hw := whiskerLeft_extensionMap_comp_restrictionHom hP1₁ haF haG θ
    have hw' := whiskerLeft_extensionMap_comp_restrictionHom hP1₁ haF haG θ'
    have hext : extensionMap θ = extensionMap θ' := by
      refine hom_ext_of_app_eq_on_subcategory hP2₂ hlF hzG _ _ fun Y hY => ?_
      let Z : P₁.FullSubcategoryᵒᵖ := op ⟨Y, h _ hY⟩
      have h₁ := congrArg (fun γ => γ.app Z) hw
      have h₂ := congrArg (fun γ => γ.app Z) hw'
      have h₃ : θ.app Z = θ'.app Z :=
        congrArg (fun γ => γ.app (op (⟨Y, hY⟩ : P₂.FullSubcategory))) hθθ'
      simp only [Functor.whiskerLeft_app, NatTrans.comp_app] at h₁ h₂
      have hm : (extensionMap θ).app (op Y) ≫ (restrictionHom G hP1₁ haG).app Z =
          (extensionMap θ').app (op Y) ≫ (restrictionHom G hP1₁ haG).app Z := by
        change (extensionMap θ).app (P₁.ι.op.obj Z) ≫ (restrictionHom G hP1₁ haG).app Z =
          (extensionMap θ').app (P₁.ι.op.obj Z) ≫ (restrictionHom G hP1₁ haG).app Z
        rw [h₁, h₂, h₃]
      exact (cancel_mono _).1 hm
    have h₄ : restrictionHom F hP1₁ haF ≫ θ = restrictionHom F hP1₁ haF ≫ θ' := by
      rw [← hw, ← hw', hext]
    exact (cancel_epi _).1 h₄
  obtain ⟨θ', hθ'⟩ := hex
  have hres : Functor.whiskerLeft ι₂.op
      (αF.inv ≫ Functor.whiskerLeft P₁.ι.op θ' ≫ αG.hom) = σ := by
    refine NatTrans.ext (funext fun Z => ?_)
    have hZ := congrArg (fun γ => γ.app Z) hθ'
    simp only [Functor.whiskerLeft_app, NatTrans.comp_app] at hZ ⊢
    change αF.inv.app (ι₂.op.obj Z) ≫ θ'.app (P₂.ι.op.obj Z) ≫ αG.hom.app (ι₂.op.obj Z) =
      σ.app Z
    rw [hZ]
    simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.assoc]
    exact Category.comp_id _
  exact ⟨_, hres, fun θ hθ => huniq _ _ (hθ.trans hres.symm)⟩

end AlgebraicGeometry.ExtendingFunctors

end
