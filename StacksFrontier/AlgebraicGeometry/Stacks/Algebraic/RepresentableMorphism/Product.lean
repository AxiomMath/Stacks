module

public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableMorphism.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableMorphism.Composition
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
import StacksCore.Tactic.StacksAttribute

/-!
# Products of representable 1-morphisms of fibred categories

The product `𝒳₁ × 𝒳₂ ⥤ 𝒴₁ × 𝒴₂` of two representable 1-morphisms of categories fibred in
groupoids over a common base category is representable.

## Main definitions

* `Stacks.RepresentableMorphism.productMorphism`: the componentwise product of two 1-morphisms of
  categories over a common base.

## Main results

* `Stacks.RepresentableMorphism.isRepresentableMorphism_product`: the product of two representable
  1-morphisms is representable.

## Implementation notes

Products are realized as 2-fibre products over the base category along its identity functor.

## References

* [Stacks Project, Tag 02ZU](https://stacks.math.columbia.edu/tag/02ZU)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.RepresentableMorphism

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
  {𝒳₁ : Type u₂} [Category.{v₂} 𝒳₁]
  {𝒳₂ : Type u₃} [Category.{v₃} 𝒳₂]
  {𝒴₁ : Type u₄} [Category.{v₄} 𝒴₁]
  {𝒴₂ : Type u₅} [Category.{v₅} 𝒴₂]

/-- The product of two 1-morphisms of categories over a common base. -/
public def productMorphism
    (p₁ : 𝒳₁ ⥤ 𝒞) (p₂ : 𝒳₂ ⥤ 𝒞)
    (q₁ : 𝒴₁ ⥤ 𝒞) (q₂ : 𝒴₂ ⥤ 𝒞)
    (F₁ : 𝒳₁ ⥤ 𝒴₁) (F₂ : 𝒳₂ ⥤ 𝒴₂)
    (hF₁ : F₁ ⋙ q₁ = p₁) (hF₂ : F₂ ⋙ q₂ = p₂) :
    TwoFibreProductOver p₁ p₂ (𝟭 𝒞) p₁ p₂ ⥤
      TwoFibreProductOver q₁ q₂ (𝟭 𝒞) q₁ q₂ := by
  subst p₁ p₂
  let p := TwoFibreProductOver.structureFunctor (F₁ ⋙ q₁) (F₂ ⋙ q₂)
    (𝟭 𝒞) (F₁ ⋙ q₁) (F₂ ⋙ q₂)
  let π₁ := TwoFibreProductOver.fst (F₁ ⋙ q₁) (F₂ ⋙ q₂)
    (𝟭 𝒞) (F₁ ⋙ q₁) (F₂ ⋙ q₂)
  let π₂ := TwoFibreProductOver.snd (F₁ ⋙ q₁) (F₂ ⋙ q₂)
    (𝟭 𝒞) (F₁ ⋙ q₁) (F₂ ⋙ q₂)
  exact TwoFibreProductOver.lift q₁ q₂ (𝟭 𝒞) q₁ q₂ p
    (π₁ ⋙ F₁) (π₂ ⋙ F₂)
    (by rw [Functor.assoc]; exact TwoFibreProductOver.fst_comp_eq)
    (by rw [Functor.assoc]; exact TwoFibreProductOver.snd_comp_eq)
    (TwoFibreProductOver.psiIso (F₁ ⋙ q₁) (F₂ ⋙ q₂)
      (𝟭 𝒞) (F₁ ⋙ q₁) (F₂ ⋙ q₂))
    (fun P ↦ P.vertical)

private theorem identity_comparison_eqToIso {A B U : 𝒞} (hA : A = U) (hB : B = U)
    (e : A ≅ B) (he : (𝟭 𝒞).IsHomLift (𝟙 U) e.hom) :
    e = eqToIso (hA.trans hB.symm) := by
  apply Iso.ext
  simpa using IsHomLift.fac' (𝟭 𝒞) (𝟙 U) e.hom

private theorem fibredEquivalence_of_equivalence
    {𝒟 : Type*} [Category 𝒟] {A B : Type*} [Category A] [Category B]
    (p : A ⥤ 𝒟) (q : B ⥤ 𝒟) (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (F : A ⥤ B) (hF : F ⋙ q = p)
    [Functor.IsEquivalence F] : IsFibredEquivalence p q F := by
  obtain ⟨G, hG, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over p q hp hq F hF
      (inferInstance : F.IsEquivalence)
  have hFObj (x : A) : q.obj (F.obj x) = p.obj x := Functor.congr_obj hF x
  have hGObj (y : B) : p.obj (G.obj y) = q.obj y := Functor.congr_obj hG y
  refine ⟨⟨hF, ?_⟩, ?_⟩
  · intro R S x y f φ hφ hφcart
    have hmap : q.IsHomLift f (F.map φ) := Functor.isHomLift_map_of_comp_eq hF f φ
    have hstrong : q.IsStronglyCartesian f (F.map φ) := hq.isStronglyCartesian_homLift f (F.map φ)
    infer_instance
  · refine ⟨G, ⟨hG, ?_⟩, ⟨ε, ?_⟩, ⟨η, ?_⟩⟩
    · intro R S x y f φ hφ hφcart
      have hmap : p.IsHomLift f (G.map φ) := Functor.isHomLift_map_of_comp_eq hG f φ
      have hstrong : p.IsStronglyCartesian f (G.map φ) :=
      hp.isStronglyCartesian_homLift f (G.map φ)
      infer_instance
    · intro x
      refine ⟨(hFObj (G.obj x)).trans (hGObj x), ?_⟩
      have : q.IsHomLift (𝟙 (q.obj x)) (ε.hom.app x) := hε x
      simpa using IsHomLift.fac' q (𝟙 (q.obj x)) (ε.hom.app x)
    · intro x
      refine ⟨(hGObj (F.obj x)).trans (hFObj x), ?_⟩
      have : p.IsHomLift (𝟙 (p.obj x)) (η.hom.app x) := hη x
      simpa using IsHomLift.fac' p (𝟙 (p.obj x)) (η.hom.app x)

private theorem representableCFG_of_equivalence
    {𝒟 : Type*} [Category 𝒟] {A B : Type*} [Category A] [Category B]
    (p : A ⥤ 𝒟) (q : B ⥤ 𝒟) (hq : q.IsFiberedInGroupoids) (F : B ⥤ A) (hF : F ⋙ p = q)
    [Functor.IsEquivalence F] (hrepr : Stacks.RepresentableMorphism.IsRepresentableCFG p) :
    Stacks.RepresentableMorphism.IsRepresentableCFG q := by
  obtain ⟨X, E, hE⟩ := hrepr
  have hEeq : E.IsEquivalence :=
    Stacks.RepresentableMorphism.SliceEquivalence.isEquivalence_of_isEquivalenceOver p X E hE
  let FE := F ⋙ E
  have hFE : FE ⋙ Over.forget X = q := by
    dsimp [FE]; rw [Functor.assoc, hE.isCartesianFunctor.comm, hF]
  have : Functor.IsEquivalence FE := Functor.isEquivalence_trans F E
  exact ⟨X, FE, fibredEquivalence_of_equivalence q (Over.forget X) hq
    (Functor.IsFiberedInGroupoids.over_forget X) FE hFE⟩

private def pullbackIdentityGraph
    {A B : Type*} [Category A] [Category B]
    (p : A ⥤ 𝒞) (q : B ⥤ 𝒞) (F : A ⥤ B) (hF : F ⋙ q = p) :
    A ⥤ TwoFibreProductOver q p q (𝟭 B) F :=
  TwoFibreProductOver.lift q p q (𝟭 B) F p F (𝟭 A) hF (by rfl)
    (Iso.refl _) (fun a ↦ IsHomLift.id (Functor.congr_obj hF a))

attribute [local implicit_reducible] pullbackIdentityGraph
  TwoFibreProductOver.lift TwoFibreProductOver.fst TwoFibreProductOver.snd
  TwoFibreProductOver.structureFunctor

private theorem pullbackIdentityGraph_isEquivalence
    {A B : Type*} [Category A] [Category B]
    (p : A ⥤ 𝒞) (q : B ⥤ 𝒞) (F : A ⥤ B) (hF : F ⋙ q = p) :
    (pullbackIdentityGraph p q F hF).IsEquivalence := by
  let J := pullbackIdentityGraph p q F hF
  have : J.Faithful := ⟨fun h ↦ congrArg TwoFibreProductOver.Hom.b h⟩
  have : J.Full := ⟨fun f ↦ ⟨f.b, by
    refine TwoFibreProductOver.Hom.ext' ?_ rfl
    simpa [J, pullbackIdentityGraph, TwoFibreProductOver.lift] using f.w.symm⟩⟩
  have : J.EssSurj := ⟨fun P ↦ by
    have := P.vertical
    have : q.IsHomLift (𝟙 P.base) P.iso.inv := inferInstance
    let m : J.obj P.y ⟶ P := TwoFibreProductOver.Hom.mk' P.iso.inv (𝟙 P.y) (by
      rw [IsHomLift.fac' q (𝟙 P.base) P.iso.inv]
      simp [J, pullbackIdentityGraph, TwoFibreProductOver.lift]) (by
      simp [J, pullbackIdentityGraph, TwoFibreProductOver.lift])
    have : IsIso m := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ m
      (by change IsIso P.iso.inv; infer_instance) (by change IsIso (𝟙 P.y); infer_instance)
    exact ⟨P.y, ⟨asIso m⟩⟩⟩
  exact {}

private theorem isRepresentableCFG_of_morphism_to_slice
    {A : Type*} [Category A] (p : A ⥤ 𝒞) (U : 𝒞) (F : A ⥤ Over U)
    (hF : F ⋙ Over.forget U = p) (hp : p.IsFiberedInGroupoids)
    (hrep : Stacks.RepresentableMorphism.IsRepresentableMorphism p (Over.forget U) F) :
    Stacks.RepresentableMorphism.IsRepresentableCFG F := by
  have hFfib := Functor.IsFiberedInGroupoids.of_comp_over U p F hF hp
  have := pullbackIdentityGraph_isEquivalence p (Over.forget U) F hF
  exact representableCFG_of_equivalence _ F hFfib
    (pullbackIdentityGraph p (Over.forget U) F hF) rfl (hrep U (𝟭 _) (by rfl))

private def productHom
    {p₁ : 𝒳₁ ⥤ 𝒞} {p₂ : 𝒳₂ ⥤ 𝒞}
    {P Q : TwoFibreProductOver p₁ p₂ (𝟭 𝒞) p₁ p₂}
    (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (h : eqToHom P.hy.symm ≫ p₂.map b ≫ eqToHom Q.hy =
      eqToHom P.hx.symm ≫ p₁.map a ≫ eqToHom Q.hx) : P ⟶ Q :=
  TwoFibreProductOver.Hom.mk' a b h (by
    rw [identity_comparison_eqToIso P.hx P.hy P.iso P.vertical,
      identity_comparison_eqToIso Q.hx Q.hy Q.iso Q.vertical]
    have h' := congrArg (fun f ↦ eqToHom P.hx ≫ f ≫ eqToHom Q.hy.symm) h
    simpa [Category.assoc] using h'.symm)

private noncomputable def productIso
    {p₁ : 𝒳₁ ⥤ 𝒞} {p₂ : 𝒳₂ ⥤ 𝒞}
    {P Q : TwoFibreProductOver p₁ p₂ (𝟭 𝒞) p₁ p₂}
    (a : P.x ≅ Q.x) (b : P.y ≅ Q.y)
    (h : eqToHom P.hy.symm ≫ p₂.map b.hom ≫ eqToHom Q.hy =
      eqToHom P.hx.symm ≫ p₁.map a.hom ≫ eqToHom Q.hx) : P ≅ Q := by
  let m := productHom a.hom b.hom h
  have : IsIso m := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ m
    (by dsimp [m, productHom]; infer_instance) (by dsimp [m, productHom]; infer_instance)
  exact asIso m

section Comparison

variable (q₁ : 𝒴₁ ⥤ 𝒞) (q₂ : 𝒴₂ ⥤ 𝒞)
  (F₁ : 𝒳₁ ⥤ 𝒴₁) (F₂ : 𝒳₂ ⥤ 𝒴₂)
  {Z : Type*} [Category Z] (r : Z ⥤ 𝒞)
  (G : Z ⥤ TwoFibreProductOver q₁ q₂ (𝟭 𝒞) q₁ q₂)

private abbrev firstPullback :=
  TwoFibreProductOver r (F₁ ⋙ q₁) q₁
    (G ⋙ TwoFibreProductOver.fst q₁ q₂ (𝟭 𝒞) q₁ q₂) F₁

private abbrev firstProjection : firstPullback q₁ q₂ F₁ r G ⥤ Z :=
  TwoFibreProductOver.fst _ _ _ _ _

private abbrev firstStructure : firstPullback q₁ q₂ F₁ r G ⥤ 𝒞 :=
  TwoFibreProductOver.structureFunctor _ _ _ _ _

private abbrev iteratedPullback :=
  TwoFibreProductOver (firstStructure q₁ q₂ F₁ r G) (F₂ ⋙ q₂) q₂
    (firstProjection q₁ q₂ F₁ r G ⋙ G ⋙ TwoFibreProductOver.snd q₁ q₂ (𝟭 𝒞) q₁ q₂) F₂

private abbrev productPullback :=
  TwoFibreProductOver r
    (TwoFibreProductOver.structureFunctor (F₁ ⋙ q₁) (F₂ ⋙ q₂) (𝟭 𝒞)
      (F₁ ⋙ q₁) (F₂ ⋙ q₂))
    (TwoFibreProductOver.structureFunctor q₁ q₂ (𝟭 𝒞) q₁ q₂) G
    (productMorphism (F₁ ⋙ q₁) (F₂ ⋙ q₂) q₁ q₂ F₁ F₂ rfl rfl)

attribute [local implicit_reducible] productMorphism productHom productIso

private def productPullbackToIterated :
    productPullback q₁ q₂ F₁ F₂ r G ⥤ iteratedPullback q₁ q₂ F₁ F₂ r G where
  obj P :=
    { base := P.base
      x :=
        { base := P.base
          x := P.x
          y := P.y.x
          hx := P.hx
          hy := P.y.hx.trans P.hy
          iso := (TwoFibreProductOver.fst q₁ q₂ (𝟭 𝒞) q₁ q₂).mapIso P.iso
          vertical := by
            have := P.vertical
            exact Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.fst_comp_eq _ _ }
      y := P.y.y
      hx := rfl
      hy := P.y.hy.trans P.hy
      iso := (TwoFibreProductOver.snd q₁ q₂ (𝟭 𝒞) q₁ q₂).mapIso P.iso
      vertical := by
        have := P.vertical
        exact Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.snd_comp_eq _ _ }
  map f :=
    { hbase := f.hbase
      a :=
        { hbase := f.hbase
          a := f.a
          b := f.b.a
          ha := f.ha
          hb := by
            have := f.hb
            exact Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.fst_comp_eq _ _
          w := congrArg TwoFibreProductOver.Hom.a f.w }
      b := f.b.b
      ha := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
      hb := by
        have := f.hb
        exact Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.snd_comp_eq _ _
      w := congrArg TwoFibreProductOver.Hom.b f.w }
  map_id _ := TwoFibreProductOver.Hom.ext' (TwoFibreProductOver.Hom.ext' rfl rfl) rfl
  map_comp _ _ := TwoFibreProductOver.Hom.ext' (TwoFibreProductOver.Hom.ext' rfl rfl) rfl

attribute [local implicit_reducible] productPullbackToIterated

private theorem productPullbackToIterated_faithful :
    (productPullbackToIterated q₁ q₂ F₁ F₂ r G).Faithful where
  map_injective h := TwoFibreProductOver.Hom.ext'
    (congrArg (fun f ↦ f.a.a) h)
    (TwoFibreProductOver.Hom.ext' (congrArg (fun f ↦ f.a.b) h) (congrArg (fun f ↦ f.b) h))

private theorem productPullbackToIterated_full :
    (productPullbackToIterated q₁ q₂ F₁ F₂ r G).Full where
  map_surjective {P Q} f := by
    have := f.ha
    have hf₁ : (F₁ ⋙ q₁).IsHomLift f.hbase f.a.b :=
      Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.snd_comp_eq _ _
    have := f.hb
    let b : P.y ⟶ Q.y := productHom f.a.b f.b (by
      rw [IsHomLift.fac' (F₁ ⋙ q₁) f.hbase f.a.b,
        IsHomLift.fac' (F₂ ⋙ q₂) f.hbase f.b]
      simp [Category.assoc])
    have hb : (TwoFibreProductOver.structureFunctor (F₁ ⋙ q₁) (F₂ ⋙ q₂) (𝟭 𝒞)
        (F₁ ⋙ q₁) (F₂ ⋙ q₂)).IsHomLift f.hbase b := by
      simpa only [TwoFibreProductOver.fst_comp_eq] using
        (Functor.isHomLift_comp_iff
          (TwoFibreProductOver.fst (F₁ ⋙ q₁) (F₂ ⋙ q₂) (𝟭 𝒞) (F₁ ⋙ q₁) (F₂ ⋙ q₂))
          (F₁ ⋙ q₁) f.hbase b).2 hf₁
    let m : P ⟶ Q :=
      { hbase := f.hbase
        a := f.a.a
        b := b
        ha := Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.fst_comp_eq _ _
        hb := hb
        w := TwoFibreProductOver.Hom.ext' f.a.w f.w }
    exact ⟨m, TwoFibreProductOver.Hom.ext' (TwoFibreProductOver.Hom.ext' rfl rfl) rfl⟩

private theorem productPullbackToIterated_essSurj :
    (productPullbackToIterated q₁ q₂ F₁ F₂ r G).EssSurj where
  mem_essImage P := by
    let hx : (F₁ ⋙ q₁).obj P.x.y = P.base := P.x.hy.trans P.hx
    let hy : (F₂ ⋙ q₂).obj P.y = P.base := P.hy
    let y : TwoFibreProductOver (F₁ ⋙ q₁) (F₂ ⋙ q₂) (𝟭 𝒞) (F₁ ⋙ q₁) (F₂ ⋙ q₂) :=
      { base := P.base
        x := P.x.y
        y := P.y
        hx := hx
        hy := hy
        iso := eqToIso (hx.trans hy.symm)
        vertical := IsHomLift.of_fac' _ _ _ hx hy (by simp) }
    have hv₁ : q₁.IsHomLift (𝟙 P.base) P.x.iso.hom := P.hx ▸ P.x.vertical
    have hv₂ := P.vertical
    let e : G.obj P.x.x ≅
        (productMorphism (F₁ ⋙ q₁) (F₂ ⋙ q₂) q₁ q₂ F₁ F₂ rfl rfl).obj y :=
      productIso P.x.iso P.iso (by
        rw [IsHomLift.fac' q₁ (𝟙 P.base) P.x.iso.hom,
          IsHomLift.fac' q₂ (𝟙 P.base) P.iso.hom]
        simp)
    have he : (TwoFibreProductOver.structureFunctor q₁ q₂ (𝟭 𝒞) q₁ q₂).IsHomLift
        (𝟙 P.base) e.hom := by
      simpa only [TwoFibreProductOver.fst_comp_eq] using
        (Functor.isHomLift_comp_iff
          (TwoFibreProductOver.fst q₁ q₂ (𝟭 𝒞) q₁ q₂) q₁ (𝟙 P.base) e.hom).2 hv₁
    let A : productPullback q₁ q₂ F₁ F₂ r G :=
      { base := P.base
        x := P.x.x
        y := y
        hx := P.x.hx.trans P.hx
        hy := rfl
        iso := e
        vertical := he }
    let m₁ : ((productPullbackToIterated q₁ q₂ F₁ F₂ r G).obj A).x ⟶ P.x :=
      TwoFibreProductOver.Hom.mk' (𝟙 P.x.x) (𝟙 P.x.y)
        (by simp [productPullbackToIterated, A, y])
        (by
          show (G.map (𝟙 P.x.x)).a ≫ P.x.iso.hom =
            P.x.iso.hom ≫ F₁.map (𝟙 P.x.y)
          simp)
    have hm₁ : IsIso m₁ := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ m₁
      (by change IsIso (𝟙 P.x.x); infer_instance)
      (by change IsIso (𝟙 P.x.y); infer_instance)
    let m : (productPullbackToIterated q₁ q₂ F₁ F₂ r G).obj A ⟶ P :=
      TwoFibreProductOver.Hom.mk' m₁ (𝟙 P.y)
        (by simp [productPullbackToIterated, m₁, A, y,
          TwoFibreProductOver.Hom.mk'])
        (by
          show (G.map (𝟙 P.x.x)).b ≫ P.iso.hom =
            P.iso.hom ≫ F₂.map (𝟙 P.y)
          simp)
    have hm : IsIso m := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ m
      hm₁ (by change IsIso (𝟙 P.y); infer_instance)
    exact ⟨A, ⟨asIso m⟩⟩

private theorem productPullbackToIterated_isEquivalence :
    (productPullbackToIterated q₁ q₂ F₁ F₂ r G).IsEquivalence :=
  { faithful := productPullbackToIterated_faithful q₁ q₂ F₁ F₂ r G
    full := productPullbackToIterated_full q₁ q₂ F₁ F₂ r G
    essSurj := productPullbackToIterated_essSurj q₁ q₂ F₁ F₂ r G }

end Comparison

/-- The product of two representable 1-morphisms of categories fibred in groupoids over a base
category is representable. -/
@[stacks 02ZU]
public theorem isRepresentableMorphism_product
    (p₁ : 𝒳₁ ⥤ 𝒞) (p₂ : 𝒳₂ ⥤ 𝒞)
    (q₁ : 𝒴₁ ⥤ 𝒞) (q₂ : 𝒴₂ ⥤ 𝒞)
    (hp₁ : p₁.IsFiberedInGroupoids) (hp₂ : p₂.IsFiberedInGroupoids)
    (hq₁ : q₁.IsFiberedInGroupoids) (hq₂ : q₂.IsFiberedInGroupoids)
    (F₁ : 𝒳₁ ⥤ 𝒴₁) (F₂ : 𝒳₂ ⥤ 𝒴₂)
    (hF₁ : F₁ ⋙ q₁ = p₁) (hF₂ : F₂ ⋙ q₂ = p₂)
    (hrep₁ : Stacks.RepresentableMorphism.IsRepresentableMorphism p₁ q₁ F₁)
    (hrep₂ : Stacks.RepresentableMorphism.IsRepresentableMorphism p₂ q₂ F₂) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism
      (TwoFibreProductOver.structureFunctor p₁ p₂ (𝟭 𝒞) p₁ p₂)
      (TwoFibreProductOver.structureFunctor q₁ q₂ (𝟭 𝒞) q₁ q₂)
      (productMorphism p₁ p₂ q₁ q₂ F₁ F₂ hF₁ hF₂) := by
  subst p₁ p₂
  let sX := TwoFibreProductOver.structureFunctor (F₁ ⋙ q₁) (F₂ ⋙ q₂) (𝟭 𝒞)
    (F₁ ⋙ q₁) (F₂ ⋙ q₂)
  let sY := TwoFibreProductOver.structureFunctor q₁ q₂ (𝟭 𝒞) q₁ q₂
  let F := productMorphism (F₁ ⋙ q₁) (F₂ ⋙ q₂) q₁ q₂ F₁ F₂ rfl rfl
  have hsX : sX.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hp₁ hp₂
      Functor.isFiberedInGroupoids_id (by rfl) (by rfl)
  have hsY : sY.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hq₁ hq₂
      Functor.isFiberedInGroupoids_id (by rfl) (by rfl)
  have hF : F ⋙ sY = sX := rfl
  intro U G hG
  let r := Over.forget U
  let G₁ := G ⋙ TwoFibreProductOver.fst q₁ q₂ (𝟭 𝒞) q₁ q₂
  let G₂ := G ⋙ TwoFibreProductOver.snd q₁ q₂ (𝟭 𝒞) q₁ q₂
  have hG₁ : G₁ ⋙ q₁ = r := by
    dsimp [G₁]; rw [Functor.assoc, TwoFibreProductOver.fst_comp_eq, hG]
  have hG₂ : G₂ ⋙ q₂ = r := by
    dsimp [G₂]; rw [Functor.assoc, TwoFibreProductOver.snd_comp_eq, hG]
  let r₁ := firstStructure q₁ q₂ F₁ r G
  let π₁ := firstProjection q₁ q₂ F₁ r G
  let K := π₁ ⋙ G₂
  have hπ₁ : π₁ ⋙ r = r₁ := TwoFibreProductOver.fst_comp_eq
  have hK : K ⋙ q₂ = r₁ := by
    dsimp [K]; rw [Functor.assoc, hG₂, hπ₁]
  have hr := Functor.IsFiberedInGroupoids.over_forget U
  have hr₁ : r₁.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids r (F₁ ⋙ q₁) q₁ G₁ F₁ hr hp₁ hq₁ hG₁ rfl
  have hrepπ₁ : Stacks.RepresentableMorphism.IsRepresentableMorphism r₁ r π₁ :=
    isRepresentableMorphism_fst_twoFibreProductOver
      (F₁ ⋙ q₁) q₁ r F₁ G₁ rfl hG₁ hrep₁
  let r₂ := TwoFibreProductOver.structureFunctor r₁ (F₂ ⋙ q₂) q₂ K F₂
  let π₂ := TwoFibreProductOver.fst r₁ (F₂ ⋙ q₂) q₂ K F₂
  have hπ₂ : π₂ ⋙ r₁ = r₂ := TwoFibreProductOver.fst_comp_eq
  have hr₂ : r₂.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hr₁ hp₂ hq₂ hK rfl
  have hrepπ₂ : Stacks.RepresentableMorphism.IsRepresentableMorphism r₂ r₁ π₂ :=
    isRepresentableMorphism_fst_twoFibreProductOver
      (F₂ ⋙ q₂) q₂ r₁ F₂ K rfl hK hrep₂
  have hrepr := isRepresentableCFG_of_morphism_to_slice r₂ U (π₂ ⋙ π₁)
    (by rw [Functor.assoc, hπ₁, hπ₂]) hr₂
    (isRepresentableMorphism_comp r₂ r₁ r hr₂ hr₁ hr π₂ π₁ hπ₂ hπ₁ hrepπ₂ hrepπ₁)
  have hprod := TwoFibreProductOver.fst_isFiberedInGroupoids U sX sY F G hsX hsY hF hG
  have := productPullbackToIterated_isEquivalence q₁ q₂ F₁ F₂ r G
  exact representableCFG_of_equivalence (π₂ ⋙ π₁) _ hprod
    (productPullbackToIterated q₁ q₂ F₁ F₂ r G) rfl hrepr

end Stacks.RepresentableMorphism
