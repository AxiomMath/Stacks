module

public import StacksFrontier.AlgebraicGeometry.Quot.TrivializationTorsor
public import StacksFrontier.AlgebraicGeometry.Quot.PicardSectionTransportCoherence

/-!
# Trivialisations along a family of objects of `Picardstack_{X/B}`

For a family `y` of objects `(T, h, L)` of `Picardstack_{X/B}` indexed by a category `𝒯`, the
trivialisations `𝒪_T ≅ σ_T^*L` form a presheaf on `𝒯`
(`AlgebraicGeometry.Space.trivializationsAlong`), restriction being transport of trivialisations.
When `𝒯` has a terminal object `⊤`, this presheaf is the presheaf of trivialisations of the single
invertible module `σ_⊤^*L_⊤`, read along the family of test schemes over the one of `y(⊤)`
(`AlgebraicGeometry.Space.trivializationsAlongIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Iso

/-- A conjugation identity for isomorphisms: transporting along `G` and then undoing a cocycle
`Θ₁ = τ_n ≪≫ G Θ₂ ≪≫ Θ` is transporting the composite with `Θ₂⁻¹` and undoing `τ`. -/
theorem trans_mapIso_trans_trans_symm {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {G : C ⥤ D} {K : E ⥤ C} {J : E ⥤ D} (τ : J ≅ K ⋙ G) {a : D} {x y : C} {z : D} {n : E}
    (s : a ≅ G.obj x) (β : x ≅ y) (Θ : G.obj y ≅ z) (Θ₂ : K.obj n ≅ y) (Θ₁ : J.obj n ≅ z)
    (h : Θ₁ = τ.app n ≪≫ G.mapIso Θ₂ ≪≫ Θ) :
    (s ≪≫ G.mapIso β ≪≫ Θ) ≪≫ Θ₁.symm = s ≪≫ G.mapIso (β ≪≫ Θ₂.symm) ≪≫ (τ.app n).symm := by
  subst h
  ext
  simp

/-- Composing with `e⁻¹` and then with `e` is no composition at all. -/
theorem trans_symm_trans_cancel {C : Type*} [Category* C] {X Y Z : C} (β : X ≅ Y) (e : Z ≅ Y) :
    (β ≪≫ e.symm) ≪≫ e = β := by
  rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- Composing with `e` and then with `e⁻¹` is no composition at all. -/
theorem trans_trans_symm_cancel {C : Type*} [Category* C] {X Y Z : C} (β : X ≅ Y) (e : Y ≅ Z) :
    (β ≪≫ e) ≪≫ e.symm = β := by
  rw [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

end CategoryTheory.Iso

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)
  (hc : ModulePushforwardCoherence B S hS)

section Along

variable {𝒯 : Type*} [Category* 𝒯] (yobj : 𝒯 → PicardObject s)
    (ymap : ∀ {V W : 𝒯}, (V ⟶ W) → PicardHom (yobj V) (yobj W))
    (ymap_id : ∀ V : 𝒯, ymap (𝟙 V) = PicardHom.id hc (yobj V))
    (ymap_comp : ∀ {V W Z : 𝒯} (f : V ⟶ W) (g : W ⟶ Z),
      ymap (f ≫ g) = PicardHom.comp (ymap f) (ymap g))

/-- **The trivialisations along a family of objects of `Picardstack_{X/B}`.**  Over an object `V`
of the index category, the trivialisations `𝒪_T ≅ σ_T^*L` of the object `y(V) = (T, h, L)`;
restriction is transport of trivialisations along the morphisms `y(g)`. -/
def trivializationsAlong : 𝒯ᵒᵖ ⥤ Type (u + 1) where
  obj V := structureModule (s.baseSpaceAt (yobj V.unop).T) ≅
    (PicardSituation.sectionPullback σ hσ (yobj V.unop).T).obj (yobj V.unop).lineBundle
  map {V₁ V₂} g := TypeCat.ofHom fun β ↦
    PicardSituation.transportTrivializationIso (σ := σ) (hσ := hσ) (ymap g.unop) β
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro β
    refine (TypeCat.ofHom_apply _ β).trans ?_
    rw [types_id_apply, unop_id, ymap_id]
    apply Iso.ext
    rw [PicardSituation.transportTrivializationIso_hom]
    exact PicardSituation.sectionTransportCoherence_transport_id σ hσ hc _ β.hom
  map_comp {V₁ V₂ V₃} f g := by
    apply ConcreteCategory.hom_ext
    intro β
    refine (TypeCat.ofHom_apply _ β).trans ?_
    rw [types_comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply, unop_comp, ymap_comp]
    apply Iso.ext
    rw [PicardSituation.transportTrivializationIso_hom,
      PicardSituation.transportTrivializationIso_hom,
      PicardSituation.transportTrivializationIso_hom]
    exact PicardSituation.sectionTransportCoherence_transport_comp σ hσ hc _ _ β.hom

/-- Restriction of trivialisations along the family is transport along its morphisms. -/
theorem trivializationsAlong_map_apply {V₁ V₂ : 𝒯ᵒᵖ} (g : V₁ ⟶ V₂)
    (β : (trivializationsAlong σ hσ hc yobj ymap ymap_id ymap_comp).obj V₁) :
    (trivializationsAlong σ hσ hc yobj ymap ymap_id ymap_comp).map g β =
      PicardSituation.transportTrivializationIso (σ := σ) (hσ := hσ) (ymap g.unop) β := by
  dsimp only [trivializationsAlong]
  exact TypeCat.ofHom_apply _ β

end Along

include hc in
/-- The transport isomorphism of a morphism equal to a composite. -/
theorem sectionTransportIso_eq_of_eq_comp {A C D : PicardObject s} (m : PicardHom A C)
    (n : PicardHom C D) (p : PicardHom A D) (hp : p = PicardHom.comp m n)
    (h : (schemeSpaceFunctor B S hS).map m.base.left ≫ (schemeSpaceFunctor B S hS).map n.base.left =
      (schemeSpaceFunctor B S hS).map p.base.left) :
    PicardSituation.sectionTransportIso σ hσ p =
      (modulePullbackTriangle B S hS h).app ((PicardSituation.sectionPullback σ hσ D.T).obj
          D.lineBundle) ≪≫
        (modulePullback B S hS ((schemeSpaceFunctor B S hS).map m.base.left)).mapIso
          (PicardSituation.sectionTransportIso σ hσ n) ≪≫
        PicardSituation.sectionTransportIso σ hσ m := by
  subst hp
  exact PicardSituation.sectionTransportIso_comp σ hσ hc m n

section Comparison

variable {𝒯 : Type*} [Category* 𝒯] (yobj : 𝒯 → PicardObject s)
    (ymap : ∀ {V W : 𝒯}, (V ⟶ W) → PicardHom (yobj V) (yobj W))
    (ymap_id : ∀ V : 𝒯, ymap (𝟙 V) = PicardHom.id hc (yobj V))
    (ymap_comp : ∀ {V W Z : 𝒯} (f : V ⟶ W) (g : W ⟶ Z),
      ymap (f ≫ g) = PicardHom.comp (ymap f) (ymap g))
    {top : 𝒯} (htop : IsTerminal top)

include ymap_comp in
/-- The morphisms of the family to its value at the terminal object are compatible with
the morphisms of the family. -/
theorem ymap_from_base_comp {V W : 𝒯} (g : V ⟶ W) :
    (ymap g).base.left ≫ (ymap (htop.from W)).base.left = (ymap (htop.from V)).base.left := by
  rw [show htop.from V = g ≫ htop.from W from htop.hom_ext _ _, ymap_comp]
  rfl

/-- The family `y`, read as a family of schemes over the scheme of `y(⊤)`. -/
def alongSlice : 𝒯 ⥤ Over (yobj top).T.left where
  obj V := Over.mk (ymap (htop.from V)).base.left
  map {V W} g := Over.homMk (ymap g).base.left (ymap_from_base_comp yobj ymap ymap_comp htop g)
  map_id V := by
    apply Over.OverMorphism.ext
    change (ymap (𝟙 V)).base.left = 𝟙 _
    rw [ymap_id]
    rfl
  map_comp {V W Z} f g := by
    apply Over.OverMorphism.ext
    change (ymap (f ≫ g)).base.left = (ymap f).base.left ≫ (ymap g).base.left
    rw [ymap_comp]
    rfl

/-- **The trivialisations along `y` are the trivialisations of `σ^*L` of `y(⊤)`**: over `V`, a
trivialisation `𝒪 ≅ σ_V^*L_V` corresponds to `𝒪 ≅ σ_V^*L_V ≅ (V ⟶ ⊤)^*σ_⊤^*L_⊤`, through the
transport isomorphism of `y(V ⟶ ⊤)`. -/
def trivializationsAlongIso :
    trivializationsAlong σ hσ hc yobj ymap ymap_id ymap_comp ≅
      (alongSlice hc yobj ymap ymap_id ymap_comp htop).op ⋙
        trivializationsPresheaf (yobj top).T.left
          ((PicardSituation.sectionPullback σ hσ (yobj top).T).obj (yobj top).lineBundle) :=
  NatIso.ofComponents
    (fun V ↦ Equiv.toIso
      { toFun := fun β ↦ β ≪≫ (PicardSituation.sectionTransportIso σ hσ
          (ymap (htop.from V.unop))).symm
        invFun := fun α ↦ α ≪≫ PicardSituation.sectionTransportIso σ hσ (ymap (htop.from V.unop))
        left_inv := fun β ↦ Iso.trans_symm_trans_cancel _ _
        right_inv := fun α ↦ Iso.trans_trans_symm_cancel _ _ })
    (fun {V₁ V₂} g ↦ by
      apply ConcreteCategory.hom_ext
      intro β
      simp only [types_comp_apply, Equiv.toIso_hom_hom_apply]
      rw [trivializationsAlong_map_apply, Functor.comp_map, trivializationsPresheaf_map_apply]
      have hp : ymap (htop.from V₂.unop) =
          PicardHom.comp (ymap g.unop) (ymap (htop.from V₁.unop)) := by
        rw [← ymap_comp, htop.hom_ext (g.unop ≫ htop.from V₁.unop) (htop.from V₂.unop)]
      exact Iso.trans_mapIso_trans_trans_symm _ _ β _ _ _
        (sectionTransportIso_eq_of_eq_comp σ hσ hc _ _ _ hp _))

end Comparison

end AlgebraicGeometry.Space
