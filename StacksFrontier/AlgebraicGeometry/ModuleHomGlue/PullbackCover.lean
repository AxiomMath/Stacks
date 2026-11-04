module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Pullback

/-!
# Glueing morphisms of inverse images along an open cover

Let `M` and `N` be sheaves of modules on a scheme `T` and let `V i` be a family of opens covering
`T`. A family of morphisms `φ i : (V i)^* M ⟶ (V i)^* N` of the inverse images along the
inclusions, whose restrictions to every open `W` contained in two members agree, comes from
exactly one morphism `M ⟶ N`; if every `φ i` is an isomorphism, so is the glued morphism.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictLocal`: the restriction of a morphism of
  inverse images along the inclusion of an open `V'` to a smaller open `W`.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong`: the inverse image of a morphism
  of inverse images along `g` along a further morphism `k`, read along `k ≫ g`.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.glueOfCover`: the glued morphism.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.glueIsoOfCover`: the glued isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictLocal_pullback_map`: restricting the
  inverse image of a global morphism gives its inverse image along the smaller open.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_pullback_cover`: morphisms of
  inverse images along the inclusions of an open cover, agreeing on the opens contained in two
  members, glue uniquely.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.isIso_glueOfCover`: the glued morphism of a family of
  isomorphisms is an isomorphism.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_openImmersion_cover`: the same
  glueing for a cover by arbitrary open immersions.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

variable {T : Scheme.{u}} {M N : T.Modules}

/-- **The restriction of a morphism of inverse images to a smaller open.** For `W ≤ V'` and
`ψ : V'^* M ⟶ V'^* N`, the morphism `W^* M ⟶ W^* N` obtained by pulling `ψ` back along the
inclusion `W ⟶ V'` and identifying the composite inclusion with that of `W`. -/
def pullbackRestrictLocal (W : T.Opens) {V' : T.Opens} (hW : W ≤ V')
    (ψ : (Scheme.Modules.pullback V'.ι).obj M ⟶ (Scheme.Modules.pullback V'.ι).obj N) :
    (Scheme.Modules.pullback W.ι).obj M ⟶ (Scheme.Modules.pullback W.ι).obj N :=
  (Scheme.Modules.pullbackCongr (T.homOfLE_ι hW)).inv.app M ≫
    (Scheme.Modules.pullbackComp (T.homOfLE hW) V'.ι).inv.app M ≫
    (Scheme.Modules.pullback (T.homOfLE hW)).map ψ ≫
    (Scheme.Modules.pullbackComp (T.homOfLE hW) V'.ι).hom.app N ≫
    (Scheme.Modules.pullbackCongr (T.homOfLE_ι hW)).hom.app N

/-- Conjugating the inverse image of `Φ` along `g` by the comparison isomorphisms for `k ≫ g = g'`
gives the inverse image of `Φ` along `g'`. -/
private theorem pullbackCongr_comp_pullback_map (Φ : M ⟶ N) {Z Z' : Scheme.{u}} {g : Z ⟶ T}
    {g' : Z' ⟶ T} (k : Z' ⟶ Z) (hk : k ≫ g = g') :
    (Scheme.Modules.pullbackCongr hk).inv.app M ≫ (Scheme.Modules.pullbackComp k g).inv.app M ≫
      (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback g).map Φ) ≫
      (Scheme.Modules.pullbackComp k g).hom.app N ≫ (Scheme.Modules.pullbackCongr hk).hom.app N =
      (Scheme.Modules.pullback g').map Φ := by
  rw [← Functor.comp_map, (Scheme.Modules.pullbackComp k g).hom.naturality_assoc,
    Iso.inv_hom_id_app_assoc, (Scheme.Modules.pullbackCongr hk).hom.naturality,
    Iso.inv_hom_id_app_assoc]

/-- **Restricting the inverse image of a global morphism** to a smaller open gives its inverse
image along the smaller open. -/
theorem pullbackRestrictLocal_pullback_map (Φ : M ⟶ N) {W V' : T.Opens} (hW : W ≤ V') :
    pullbackRestrictLocal W hW ((Scheme.Modules.pullback V'.ι).map Φ) =
      (Scheme.Modules.pullback W.ι).map Φ :=
  pullbackCongr_comp_pullback_map Φ (T.homOfLE hW) (T.homOfLE_ι hW)

/-- The restriction to a smaller open of a composite is the composite of the restrictions. -/
theorem pullbackRestrictLocal_comp {P : T.Modules} {W V' : T.Opens} (hW : W ≤ V')
    (ψ : (Scheme.Modules.pullback V'.ι).obj M ⟶ (Scheme.Modules.pullback V'.ι).obj N)
    (χ : (Scheme.Modules.pullback V'.ι).obj N ⟶ (Scheme.Modules.pullback V'.ι).obj P) :
    pullbackRestrictLocal W hW (ψ ≫ χ) =
      pullbackRestrictLocal W hW ψ ≫ pullbackRestrictLocal W hW χ := by
  simp only [pullbackRestrictLocal, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- The restriction to a smaller open of an identity is the identity. -/
theorem pullbackRestrictLocal_id {W V' : T.Opens} (hW : W ≤ V') :
    pullbackRestrictLocal (M := M) W hW (𝟙 _) = 𝟙 _ := by
  simpa only [CategoryTheory.Functor.map_id] using pullbackRestrictLocal_pullback_map (𝟙 M) hW

/-- If the restrictions of `φ₁` and `φ₂` agree on every open contained in `V₁` and `V₂`, then
`ofPullback V₁.ι φ₁` and `ofPullback V₂.ι φ₂` have the same local component over every open `W`
of `T` that is the image of an open of `V₁` and of an open of `V₂`. -/
theorem localApp_ofPullback_eq_of_pullbackRestrictLocal_eq {V₁ V₂ : T.Opens}
    (φ₁ : (Scheme.Modules.pullback V₁.ι).obj M ⟶ (Scheme.Modules.pullback V₁.ι).obj N)
    (φ₂ : (Scheme.Modules.pullback V₂.ι).obj M ⟶ (Scheme.Modules.pullback V₂.ι).obj N)
    (hφ : ∀ (W : T.Opens) (h₁ : W ≤ V₁) (h₂ : W ≤ V₂),
      pullbackRestrictLocal W h₁ φ₁ = pullbackRestrictLocal W h₂ φ₂)
    (W₁ : V₁.toScheme.Opens) (W₂ : V₂.toScheme.Opens) (W : T.Opens)
    (h₁ : V₁.ι ''ᵁ W₁ = W) (h₂ : V₂.ι ''ᵁ W₂ = W) :
    localApp V₁.ι (ofPullback V₁.ι φ₁) h₁ = localApp V₂.ι (ofPullback V₂.ι φ₂) h₂ := by
  have hW₁ : W ≤ V₁ := h₁ ▸ Scheme.Opens.ι_image_le V₁ W₁
  have hW₂ : W ≤ V₂ := h₂ ▸ Scheme.Opens.ι_image_le V₂ W₂
  exact localApp_ofPullback_eq_of_refinement V₁.ι V₂.ι (T.homOfLE hW₁) (T.homOfLE_ι hW₁)
    (T.homOfLE hW₂) (T.homOfLE_ι hW₂) φ₁ φ₂ (pullbackRestrictLocal W hW₁ φ₁) rfl
    (hφ W hW₁ hW₂).symm h₁ h₂ (W.ι_image_top)

/-- Open immersions whose images cover `T` and morphisms of inverse images whose local components
agree on overlaps glue uniquely. -/
private theorem existsUnique_hom_of_localApp_ofPullback_eq {ι : Type u} {Z : ι → Scheme.{u}}
    (g : ∀ i, Z i ⟶ T) [∀ i, IsOpenImmersion (g i)]
    (hg : ⨆ i, g i ''ᵁ (⊤ : (Z i).Opens) = ⊤)
    (φ : ∀ i, (Scheme.Modules.pullback (g i)).obj M ⟶ (Scheme.Modules.pullback (g i)).obj N)
    (h : ∀ i j (W₁ : (Z i).Opens) (W₂ : (Z j).Opens) (W : T.Opens)
      (h₁ : g i ''ᵁ W₁ = W) (h₂ : g j ''ᵁ W₂ = W),
      localApp (g i) (ofPullback (g i) (φ i)) h₁ = localApp (g j) (ofPullback (g j) (φ j)) h₂) :
    ∃! Φ : M ⟶ N, ∀ i, (Scheme.Modules.pullback (g i)).map Φ = φ i := by
  obtain ⟨Φ, hΦ, huniq⟩ :=
    existsUnique_hom_of_restrict_cover g hg (fun i ↦ ofPullback (g i) (φ i)) h
  refine ⟨Φ, fun i ↦ pullback_map_eq_of_restrictFunctor_map_eq _ Φ (φ i) (hΦ i),
    fun Φ' hΦ' ↦ huniq Φ' fun i ↦ ?_⟩
  rw [← hΦ' i, ofPullback_pullback_map]

section Cover

variable {ι : Type u} (V : ι → T.Opens)

/-- If the opens `V i` cover `T`, the images of their top opens under the inclusions have
supremum `⊤`. -/
theorem iSup_ι_image_top_eq_top (hV : ∀ t : T, ∃ i, t ∈ V i) :
    ⨆ i, (V i).ι ''ᵁ (⊤ : (V i).toScheme.Opens) = ⊤ := by
  refine eq_top_iff.mpr fun t _ ↦ ?_
  obtain ⟨i, hi⟩ := hV t
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, by rwa [Scheme.Opens.ι_image_top]⟩

/-- **Morphisms of inverse images along the inclusions of an open cover glue uniquely.** A family
`φ i : (V i)^* M ⟶ (V i)^* N` whose restrictions to every open `W` contained in two members `V i`,
`V j` agree is the family of inverse images of exactly one morphism `M ⟶ N`. -/
theorem existsUnique_hom_of_pullback_cover (hV : ∀ t : T, ∃ i, t ∈ V i)
    (φ : ∀ i, (Scheme.Modules.pullback (V i).ι).obj M ⟶ (Scheme.Modules.pullback (V i).ι).obj N)
    (hφ : ∀ i j (W : T.Opens) (hi : W ≤ V i) (hj : W ≤ V j),
      pullbackRestrictLocal W hi (φ i) = pullbackRestrictLocal W hj (φ j)) :
    ∃! Φ : M ⟶ N, ∀ i, (Scheme.Modules.pullback (V i).ι).map Φ = φ i := by
  exact existsUnique_hom_of_localApp_ofPullback_eq (fun i ↦ (V i).ι) (iSup_ι_image_top_eq_top V hV)
    φ fun i j W₁ W₂ W h₁ h₂ ↦
      localApp_ofPullback_eq_of_pullbackRestrictLocal_eq (φ i) (φ j) (hφ i j) W₁ W₂ W h₁ h₂

/-- Two morphisms `M ⟶ N` with the same inverse images along the inclusions of an open cover are
equal. -/
theorem hom_ext_of_pullbackCover (hV : ∀ t : T, ∃ i, t ∈ V i) {Φ Φ' : M ⟶ N}
    (h : ∀ i, (Scheme.Modules.pullback (V i).ι).map Φ =
      (Scheme.Modules.pullback (V i).ι).map Φ') : Φ = Φ' :=
  (existsUnique_hom_of_pullback_cover V hV (fun i ↦ (Scheme.Modules.pullback (V i).ι).map Φ)
    (fun i j W hi hj ↦ by
      rw [pullbackRestrictLocal_pullback_map, pullbackRestrictLocal_pullback_map])).unique
    (fun _ ↦ rfl) (fun i ↦ (h i).symm)

/-- **The glued morphism** of a family of morphisms of inverse images along the inclusions of an
open cover, agreeing on the opens contained in two members. -/
def glueOfCover (hV : ∀ t : T, ∃ i, t ∈ V i)
    (φ : ∀ i, (Scheme.Modules.pullback (V i).ι).obj M ⟶ (Scheme.Modules.pullback (V i).ι).obj N)
    (hφ : ∀ i j (W : T.Opens) (hi : W ≤ V i) (hj : W ≤ V j),
      pullbackRestrictLocal W hi (φ i) = pullbackRestrictLocal W hj (φ j)) : M ⟶ N :=
  (existsUnique_hom_of_pullback_cover V hV φ hφ).exists.choose

variable (hV : ∀ t : T, ∃ i, t ∈ V i)
  (φ : ∀ i, (Scheme.Modules.pullback (V i).ι).obj M ⟶ (Scheme.Modules.pullback (V i).ι).obj N)
  (hφ : ∀ i j (W : T.Opens) (hi : W ≤ V i) (hj : W ≤ V j),
    pullbackRestrictLocal W hi (φ i) = pullbackRestrictLocal W hj (φ j))

/-- The inverse image of the glued morphism along a member of the cover is the given morphism. -/
theorem pullback_map_glueOfCover (i : ι) :
    (Scheme.Modules.pullback (V i).ι).map (glueOfCover V hV φ hφ) = φ i :=
  (existsUnique_hom_of_pullback_cover V hV φ hφ).exists.choose_spec i

/-- The glued morphism is the only morphism with the given inverse images. -/
theorem eq_glueOfCover {Φ : M ⟶ N} (h : ∀ i, (Scheme.Modules.pullback (V i).ι).map Φ = φ i) :
    Φ = glueOfCover V hV φ hφ :=
  (existsUnique_hom_of_pullback_cover V hV φ hφ).unique h (pullback_map_glueOfCover V hV φ hφ)

/-- The inverse image of the glued morphism along any open contained in a member of the cover is
the restriction of that member's morphism. -/
theorem pullback_map_glueOfCover_of_le (i : ι) {W : T.Opens} (hW : W ≤ V i) :
    (Scheme.Modules.pullback W.ι).map (glueOfCover V hV φ hφ) =
      pullbackRestrictLocal W hW (φ i) := by
  rw [← pullback_map_glueOfCover V hV φ hφ i, pullbackRestrictLocal_pullback_map]

omit hV hφ in
/-- The restriction to a smaller open of an isomorphism is an isomorphism. -/
instance isIso_pullbackRestrictLocal {W V' : T.Opens} (hW : W ≤ V')
    (ψ : (Scheme.Modules.pullback V'.ι).obj M ⟶ (Scheme.Modules.pullback V'.ι).obj N) [IsIso ψ] :
    IsIso (pullbackRestrictLocal W hW ψ) := by
  dsimp only [pullbackRestrictLocal]
  infer_instance

omit hV hφ in
/-- The restriction to a smaller open of an inverse is the inverse of the restriction. -/
theorem pullbackRestrictLocal_inv {W V' : T.Opens} (hW : W ≤ V')
    (ψ : (Scheme.Modules.pullback V'.ι).obj M ⟶ (Scheme.Modules.pullback V'.ι).obj N) [IsIso ψ] :
    pullbackRestrictLocal W hW (inv ψ) = inv (pullbackRestrictLocal W hW ψ) := by
  refine IsIso.eq_inv_of_hom_inv_id (f := pullbackRestrictLocal W hW ψ) ?_
  rw [← pullbackRestrictLocal_comp, IsIso.hom_inv_id, pullbackRestrictLocal_id]

omit hV in
include hφ in
/-- The inverses of a compatible family of isomorphisms are compatible. -/
theorem inv_compatible [∀ i, IsIso (φ i)] (i j : ι) (W : T.Opens) (hi : W ≤ V i)
    (hj : W ≤ V j) :
    pullbackRestrictLocal W hi (inv (φ i)) = pullbackRestrictLocal W hj (inv (φ j)) := by
  rw [pullbackRestrictLocal_inv, pullbackRestrictLocal_inv]
  congr 1
  exact hφ i j W hi hj

/-- **The glued isomorphism** of a family of isomorphisms of inverse images along the inclusions
of an open cover, agreeing on the opens contained in two members. -/
def glueIsoOfCover [∀ i, IsIso (φ i)] : M ≅ N where
  hom := glueOfCover V hV φ hφ
  inv := glueOfCover V hV (fun i ↦ inv (φ i)) (inv_compatible V φ hφ)
  hom_inv_id := hom_ext_of_pullbackCover V hV fun i ↦ by
    rw [Functor.map_comp, pullback_map_glueOfCover, pullback_map_glueOfCover, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  inv_hom_id := hom_ext_of_pullbackCover V hV fun i ↦ by
    rw [Functor.map_comp, pullback_map_glueOfCover, pullback_map_glueOfCover, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id]

/-- The underlying morphism of the glued isomorphism is the glued morphism. -/
theorem glueIsoOfCover_hom [∀ i, IsIso (φ i)] :
    (glueIsoOfCover V hV φ hφ).hom = glueOfCover V hV φ hφ := rfl

/-- **The glued morphism of a family of isomorphisms is an isomorphism.** -/
theorem isIso_glueOfCover [∀ i, IsIso (φ i)] : IsIso (glueOfCover V hV φ hφ) :=
  (glueIsoOfCover V hV φ hφ).isIso_hom

end Cover

section OpenImmersionCover

/-- The inverse image of a morphism of inverse images along `g` along a further morphism `k`,
read as a morphism of inverse images along `g' = k ≫ g`. -/
def pullbackRestrictAlong {Z Z' : Scheme.{u}} {g : Z ⟶ T} {g' : Z' ⟶ T} (k : Z' ⟶ Z)
    (hk : k ≫ g = g')
    (ψ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    (Scheme.Modules.pullback g').obj M ⟶ (Scheme.Modules.pullback g').obj N :=
  (Scheme.Modules.pullbackCongr hk).inv.app M ≫
    (Scheme.Modules.pullbackComp k g).inv.app M ≫
    (Scheme.Modules.pullback k).map ψ ≫
    (Scheme.Modules.pullbackComp k g).hom.app N ≫
    (Scheme.Modules.pullbackCongr hk).hom.app N

/-- The restriction to a smaller open `W ≤ V'` is the inverse image along the inclusion
`W ⟶ V'`. -/
theorem pullbackRestrictLocal_eq_pullbackRestrictAlong (W : T.Opens) {V' : T.Opens}
    (hW : W ≤ V')
    (ψ : (Scheme.Modules.pullback V'.ι).obj M ⟶ (Scheme.Modules.pullback V'.ι).obj N) :
    pullbackRestrictLocal W hW ψ = pullbackRestrictAlong (T.homOfLE hW) (T.homOfLE_ι hW) ψ :=
  rfl

/-- Restricting the inverse image of a global morphism along a further morphism gives its inverse
image along the composite. -/
theorem pullbackRestrictAlong_pullback_map (Φ : M ⟶ N) {Z Z' : Scheme.{u}} {g : Z ⟶ T}
    {g' : Z' ⟶ T} (k : Z' ⟶ Z) (hk : k ≫ g = g') :
    pullbackRestrictAlong k hk ((Scheme.Modules.pullback g).map Φ) =
      (Scheme.Modules.pullback g').map Φ :=
  pullbackCongr_comp_pullback_map Φ k hk

/-- **Morphisms of inverse images along a cover by open immersions glue uniquely.** Let
`g i : Z i ⟶ T` be open immersions whose images cover `T`. A family
`φ i : (g i)^* M ⟶ (g i)^* N` which agrees, after restriction, over every open `W` of `T` through
which two members factor is the family of inverse images of exactly one morphism `M ⟶ N`. -/
theorem existsUnique_hom_of_openImmersion_cover {ι : Type u} {Z : ι → Scheme.{u}}
    (g : ∀ i, Z i ⟶ T) [∀ i, IsOpenImmersion (g i)]
    (hg : ⨆ i, g i ''ᵁ (⊤ : (Z i).Opens) = ⊤)
    (φ : ∀ i, (Scheme.Modules.pullback (g i)).obj M ⟶ (Scheme.Modules.pullback (g i)).obj N)
    (hφ : ∀ i j (W : T.Opens) (k₁ : W.toScheme ⟶ Z i) (k₂ : W.toScheme ⟶ Z j)
      (h₁ : k₁ ≫ g i = W.ι) (h₂ : k₂ ≫ g j = W.ι),
      pullbackRestrictAlong k₁ h₁ (φ i) = pullbackRestrictAlong k₂ h₂ (φ j)) :
    ∃! Φ : M ⟶ N, ∀ i, (Scheme.Modules.pullback (g i)).map Φ = φ i := by
  have hlift : ∀ i (W₁ : (Z i).Opens) (W : T.Opens), g i ''ᵁ W₁ = W →
      ∃ k : W.toScheme ⟶ Z i, ∃ _ : IsOpenImmersion k, k ≫ g i = W.ι := by
    intro i W₁ W hW
    have hr : Set.range W.ι.base ⊆ Set.range (g i).base := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, -, hy⟩ : x.1 ∈ g i ''ᵁ W₁ := hW ▸ x.2
      exact ⟨y, hy.trans (Scheme.Opens.ι_apply W x).symm⟩
    have hfac := IsOpenImmersion.lift_fac (g i) W.ι hr
    have : IsOpenImmersion (IsOpenImmersion.lift (g i) W.ι hr ≫ g i) := by
      rw [hfac]; infer_instance
    exact ⟨_, IsOpenImmersion.of_comp _ (g i), hfac⟩
  refine existsUnique_hom_of_localApp_ofPullback_eq g hg φ fun i j W₁ W₂ W h₁ h₂ ↦ ?_
  obtain ⟨k₁, _, hk₁⟩ := hlift i W₁ W h₁
  obtain ⟨k₂, _, hk₂⟩ := hlift j W₂ W h₂
  exact localApp_ofPullback_eq_of_refinement (g i) (g j) k₁ hk₁ k₂ hk₂ (φ i) (φ j)
    (pullbackRestrictAlong k₁ hk₁ (φ i)) rfl (hφ i j W k₁ k₂ hk₁ hk₂).symm h₁ h₂ W.ι_image_top

end OpenImmersionCover

end Stacks.AlgebraicGeometry.ModuleHomGlue

end
