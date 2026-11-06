module
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.Homology.KFlat.BifunctorOneSided
public import StacksFrontier.Homology.KFlat.BifunctorTransport

public import StacksFrontier.Homology.KFlat.BifunctorTransportRepresentatives
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit

/-!
# The projection-formula map of a derived adjunction, on representatives

Let `G ⊣ F` be an adjunction between abelian categories with `G : B ⥤ A` exact, let `RF` be a
right derived functor of `F` computed by K-injective resolutions, and let
`Stacks.DerivedFunctor.derivedAdjunction` be the induced adjunction
`G.mapDerivedCategory ⊣ RF`. Let `FB` and `FA` be bifunctors on `B` and on `A` (tensor products)
with derived bifunctors `FB^𝐋`, `FA^𝐋`, and let `ε : G(b ⊗ b') ≅ G b ⊗ G b'` be compatible with
them, so that `derivedTransportProdIso` compares `FB^𝐋` and `FA^𝐋` along `G`. The projection
formula map is then `CategoryTheory.adjunctionTensorMap`:

  `RF(E) ⊗^𝐋 K ⟶ RF(E ⊗^𝐋 G K)`.

This file computes it at `(Qh I, Qh P)` for an arbitrary complex `I` of `A` and a K-flat complex
`P` of `B`: precomposed with the derived-functor comparison `β` at `I` in the first factor, it is
`Qh` of the **projection-formula map on complexes**
`complexProjectionMap : Tot(F I ⊗ P) ⟶ F(Tot(I ⊗ G P))` — the adjoint of the transport of `ε`
followed by the counit `G F I ⟶ I` — followed by `β` at `Tot(I ⊗ G P)`, between the one-sided
comparisons `comparisonRightQhIso` of the derived bifunctors on these representatives.

## Main definitions

* `CochainComplex.KFlatBifunctor.complexProjectionMap`: the projection-formula map on complexes.

## Main results

* `CochainComplex.KFlatBifunctor.adjunctionTensorMap_derivedAdjunction_Qh`: the computation.
* `CochainComplex.KFlatBifunctor.isIso_adjunctionTensorMap_derivedAdjunction_Qh`: for `I`
  K-injective and `P` K-flat, the derived projection-formula map at `(Qh I, Qh P)` is invertible
  as soon as `complexProjectionMap` is a quasi-isomorphism and `β` is invertible at
  `Tot(I ⊗ G P)`.

## Implementation notes

The identity is checked after transposition along the derived adjunction, where the counit is
`Stacks.DerivedFunctor.derivedAdjunction_counit_app` and the comparison is
`derivedTransportIso_hom_app_app_Qh`; what remains reduces to the homotopy category and then to
the defining property of `complexProjectionMap`. The arrow algebra is done in bare categories
(`derived_projection_chain`, `homotopy_projection_chain`), applied by `exact`, because the objects
involved carry several definitionally equal spellings that a rewrite cannot cross.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace CochainComplex.KFlatBifunctor

universe w v₁ v₂ u₁ u₂

/-! ### Arrow algebra in bare categories -/

section Bare

/-- Cancelling a comparison against its inverse in the first factor of a bifunctor. -/
theorem bifunctor_inv_comp_map_comp {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] (P : C₁ ⥤ C₂ ⥤ C₃) {x x' x'' : C₁} {y y' : C₂} (u : x' ≅ x) (q : x ⟶ x'')
    (v : y ⟶ y') :
    (P.map u.inv).app y ≫ (P.obj x').map v ≫ (P.map (u.hom ≫ q)).app y' =
      (P.map q).app y ≫ (P.obj x'').map v := by
  have h₁ := (P.map u.hom).naturality v
  have h₂ := (P.map q).naturality v
  rw [Functor.map_comp, NatTrans.comp_app, reassoc_of% h₁, ← NatTrans.comp_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, h₂]

/-- An equation of two composites, transported by a functor. -/
theorem map_comp₂_eq_map_comp₄ {C C' : Type*} [Category C] [Category C'] (H : C' ⥤ C)
    {X₀ X₁ X₂ Y₁ Y₂ Y₃ : C'} (x : X₀ ⟶ X₁) (y : X₁ ⟶ X₂) (g₁ : X₀ ⟶ Y₁) (g₂ : Y₁ ⟶ Y₂)
    (g₃ : Y₂ ⟶ Y₃) (g₄ : Y₃ ⟶ X₂) (h : x ≫ y = g₁ ≫ g₂ ≫ g₃ ≫ g₄) :
    H.map x ≫ H.map y = H.map g₁ ≫ H.map g₂ ≫ H.map g₃ ≫ H.map g₄ := by
  simp only [← H.map_comp, h]

/-- An equation of two composites of two morphisms, transported by a functor. -/
theorem map_comp₂_eq_map_comp₂ {C C' : Type*} [Category C] [Category C'] (H : C' ⥤ C)
    {X₀ X₁ X₂ Y₁ : C'} (x : X₀ ⟶ X₁) (y : X₁ ⟶ X₂) (g₁ : X₀ ⟶ Y₁) (g₂ : Y₁ ⟶ X₂)
    (h : x ≫ y = g₁ ≫ g₂) :
    H.map x ≫ H.map y = H.map g₁ ≫ H.map g₂ := by
  simp only [← H.map_comp, h]

/-- The transpose of a morphism, followed by the counit after applying the left adjoint, is
the morphism itself. -/
theorem map_homEquiv_comp_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    f = L.map (adj.homEquiv X Y f) ≫ adj.counit.app Y := by
  simp [Adjunction.homEquiv_unit]

/-- Two naturality squares, chained. -/
theorem comp_chain₂ {C : Type*} [Category C] {X₀ X₁ X₂ Y₀' Y₁ Y₂ : C}
    (a : X₀ ⟶ X₁) (e : X₁ ⟶ X₂) (f : X₂ ⟶ Y₂) (b : X₁ ⟶ Y₁) (c : X₀ ⟶ Y₀') (d : Y₀' ⟶ Y₁)
    (g : Y₁ ⟶ Y₂) (h₁ : a ≫ b = c ≫ d) (h₂ : e ≫ f = b ≫ g) :
    a ≫ e ≫ f = c ≫ d ≫ g := by
  rw [h₂, reassoc_of% h₁]

/-- The homotopy-level arrow algebra behind `adjunctionTensorMap_derivedAdjunction_Qh`. -/
theorem homotopy_projection_chain {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ Y₂ : C}
    (x : X₀ ⟶ X₃) (y : X₃ ⟶ X₅) (p : X₀ ⟶ X₁) (t : X₁ ⟶ X₂) (i : X₂ ⟶ X₃) (q : X₂ ⟶ X₄)
    (i' : X₄ ⟶ X₅) (u : X₁ ⟶ Y₂) (v : Y₂ ⟶ X₄)
    (hx : x = p ≫ t ≫ i) (hi : q ≫ i' = i ≫ y) (htq : t ≫ q = u ≫ v) :
    x ≫ y = p ≫ u ≫ v ≫ i' := by
  rw [hx, Category.assoc, Category.assoc, ← hi, reassoc_of% htq]

/-- The derived-level arrow algebra behind `adjunctionTensorMap_derivedAdjunction_Qh`. -/
theorem derived_projection_chain {Cc Dd : Type*} [Category Cc] [Category Dd] (L : Cc ⥤ Dd)
    {Rr : Dd ⥤ Cc} (εc : Rr ⋙ L ⟶ 𝟭 Dd)
    {Y Z₁ Z₂ Z₃ Z₄ Z₅ Z₆ W₁ W₂ W₃ W₄ V₁ V₂ : Dd} {T₀ T₁ T₂ T₃ : Cc}
    (lx : L.obj T₀ ⟶ Z₁) (a : Z₁ ⟶ Z₂) (bcou : Z₂ ⟶ Y) (τ : L.obj T₀ ⟶ Z₃) (m : Z₃ ⟶ Z₂)
    (z : Z₃ ⟶ Y)
    (hxa : lx ≫ a = τ ≫ m) (hm : m ≫ bcou = z)
    (c₁ : T₀ ⟶ T₁) (r₂ : L.obj T₁ ⟶ W₁) (r₃ : W₁ ⟶ W₂) (r₄ : W₂ ⟶ W₃) (r₅ : W₃ ⟶ W₄)
    (r₆ : W₄ ⟶ Z₃) (hτ : τ = L.map c₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ r₅ ≫ r₆)
    (k₁ : W₃ ⟶ V₁) (k₂ : V₁ ⟶ Y) (hz : r₅ ≫ r₆ ≫ z = k₁ ≫ k₂)
    (s₁ : W₂ ⟶ V₂) (s₂ : V₂ ⟶ V₁) (hn₄ : r₄ ≫ k₁ = s₁ ≫ s₂)
    (g₁ : W₁ ⟶ Z₄) (g₂ : Z₄ ⟶ Z₅) (g₃ : Z₅ ⟶ Z₆) (g₄ : Z₆ ⟶ V₂)
    (hhom : r₃ ≫ s₁ = g₁ ≫ g₂ ≫ g₃ ≫ g₄)
    (c₂ : T₁ ⟶ T₂) (e : T₂ ⟶ T₃) (fT : L.obj T₃ ⟶ Z₅)
    (hfac : L.map c₂ ≫ L.map e ≫ fT = r₂ ≫ g₁ ≫ g₂)
    (βT : T₃ ⟶ Rr.obj Z₆) (hβ : L.map βT ≫ εc.app Z₆ = fT ≫ g₃)
    (d₁ : Z₆ ⟶ V₁) (d₂ : V₁ ⟶ Y) (hd₁ : d₁ = g₄ ≫ s₂) (hd₂ : d₂ = k₂)
    (c : T₀ ⟶ T₂) (hc : c = c₁ ≫ c₂) :
    lx ≫ a ≫ bcou = L.map (c ≫ e ≫ βT ≫ Rr.map d₁ ≫ Rr.map d₂) ≫ εc.app Y := by
  have hn₁ := εc.naturality d₁
  have hn₂ := εc.naturality d₂
  simp only [Functor.comp_map, Functor.id_map] at hn₁ hn₂
  rw [reassoc_of% hxa, hm, hτ, hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn₂, reassoc_of% hn₁, reassoc_of% hβ, reassoc_of% hfac, hz, reassoc_of% hn₄,
    reassoc_of% hhom, hd₁, hd₂]
  simp only [Category.assoc]

end Bare

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w} B]
  (FA : A ⥤ A ⥤ A) [FA.Additive] [∀ X, (FA.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ FA (ComplexShape.up ℤ)]
  (FB : B ⥤ B ⥤ B) [FB.Additive] [∀ X, (FB.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ FB (ComplexShape.up ℤ)]
  {F : A ⥤ B} [F.Additive] {G : B ⥤ A} [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : G ⊣ F)
  (ε : ∀ (a b : B), G.obj ((FB.obj a).obj b) ≅ (FA.obj (G.obj a)).obj (G.obj b))
  (hε₁ : ∀ {a a' : B} (f : a ⟶ a') (b : B),
    G.map ((FB.map f).app b) ≫ (ε a' b).hom = (ε a b).hom ≫ (FA.map (G.map f)).app (G.obj b))
  (hε₂ : ∀ (a : B) {b b' : B} (g : b ⟶ b'),
    G.map ((FB.obj a).map g) ≫ (ε a b').hom = (ε a b).hom ≫ (FA.obj (G.obj a)).map (G.map g))
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) G]
  [∀ (K L : CochainComplex B ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex G
      (((FB.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ)]

/-- **The projection-formula map on cochain complexes**: for complexes `I` of `A` and `P` of
`B`, the map `Tot(F I ⊗ P) ⟶ F(Tot(I ⊗ G P))` adjoint to the transport
`G(Tot(F I ⊗ P)) ≅ Tot(G F I ⊗ G P)` followed by the counit `G F I ⟶ I` in the first factor.
Here `⊗` stands for the bifunctors `FB` and `FA`. -/
def complexProjectionMap (I : CochainComplex A ℤ) (P : CochainComplex B ℤ) :
    totalComplex FB ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) P ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (totalComplex FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).homEquiv _ _)
    ((transportComplexIso FB FA G G G ε hε₁ hε₂ _ P).hom ≫
      HomologicalComplex.mapBifunctorMap
        ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).counit.app I)
        (𝟙 _) FA (ComplexShape.up ℤ))

variable [(kFlatQLeft FA).IsLocalization (kFlatQuasiIsoLeft FA)]
  [(kFlatQ FA).IsLocalization (kFlatQuasiIso FA)]
  [(kFlatQLeft FB).IsLocalization (kFlatQuasiIsoLeft FB)]
  [(kFlatQ FB).IsLocalization (kFlatQuasiIso FB)]
  (hKFlatLeft : ∀ K : CochainComplex B ℤ, KFlatLeft FB K →
    KFlatLeft FA ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hKFlat : ∀ L : CochainComplex B ℤ, KFlat FB L →
    KFlat FA ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : K ⟶ I),
    I.IsKInjective ∧ QuasiIso q)

/-- **The projection-formula map of a derived adjunction, on representatives.** -/
theorem adjunctionTensorMap_derivedAdjunction_Qh (I : CochainComplex A ℤ)
    (P : CochainComplex B ℤ) (hP : KFlat FB P) :
    ((derivedBifunctor FB).map
        (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P)) ≫
      adjunctionTensorMap (Stacks.DerivedFunctor.derivedAdjunction adj RF β hA)
        (Functor.uncurry.obj (derivedBifunctor FB)) (Functor.uncurry.obj (derivedBifunctor FA))
        (derivedTransportProdIso FB FA G ε hε₁ hε₂ hKFlatLeft hKFlat).hom
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P)) =
    (comparisonRightQhIso FB ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) P hP).hom ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        (complexProjectionMap FA FB adj ε hε₁ hε₂ I P)) ≫
      β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (totalComplex FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      RF.map ((comparisonRightQhIso FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (hKFlat P hP)).inv ≫
        ((derivedBifunctor FA).obj (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))).map
          (G.mapDerivedCategoryFactorsh.inv.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P))) := by
  have hpc : (transportComplexIso FB FA G G G ε hε₁ hε₂
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) P).hom ≫
      HomologicalComplex.mapBifunctorMap
        ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).counit.app I)
        (𝟙 _) FA (ComplexShape.up ℤ) =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (complexProjectionMap FA FB adj ε hε₁ hε₂ I P) ≫
        (Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).counit.app
          (totalComplex FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    map_homEquiv_comp_counit _ _
  have hH := homotopy_projection_chain
    (((homotopyTransportIso FB FA G G G ε hε₁ hε₂).hom.app
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))).app
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P))
    (((homotopyBifunctor FA).map
      ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).counit.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))).app
      ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P)))
    _ _ _ _ _
    ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        (complexProjectionMap FA FB adj ε hε₁ hε₂ I P)))
    ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).counit.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (totalComplex FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))))
    (homotopyTransportIso_hom_app_app_quotient' FB FA G G G ε hε₁ hε₂
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) P)
    (NatTrans.congr_app ((homotopyBifunctorLiftingIso FA).inv.naturality
      ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).counit.app I))
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (map_comp₂_eq_map_comp₂ (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _ _ _ _ hpc)
  have hhom := map_comp₂_eq_map_comp₄ DerivedCategory.Qh _ _ _ _ _ _ hH
  have hxa := NatTrans.congr_app
    ((derivedTransportIso FB FA G G G ε hε₁ hε₂ hKFlatLeft hKFlat).hom.naturality
      (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P))
  simp only [NatTrans.comp_app] at hxa
  have hm : ((derivedBifunctor FA).map (G.mapDerivedCategory.map
        (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))).app
        (G.mapDerivedCategory.obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P))) ≫
      (Functor.uncurry.obj (derivedBifunctor FA)).map
        ((Stacks.DerivedFunctor.derivedAdjunction adj RF β hA).counit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) ×ₘ
          𝟙 (G.mapDerivedCategory.obj
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P)))) =
      ((derivedBifunctor FA).map
        (G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) ≫
          DerivedCategory.Qh.map
            ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).counit.app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))).app
        (G.mapDerivedCategory.obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P))) := by
    rw [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id,
      ← NatTrans.comp_app, ← Functor.map_comp, Stacks.DerivedFunctor.derivedAdjunction_counit_app]
  have hτ := (derivedTransportIso_hom_app_app_Qh FB FA G G G ε hε₁ hε₂ hKFlatLeft hKFlat
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))
      ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P, hP⟩).trans
    (homotopyTransportAtIso_hom_app FB FA G G G ε hε₁ hε₂ hKFlat
      ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P, hP⟩
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
  have hz := bifunctor_inv_comp_map_comp (derivedBifunctor FA)
    (G.mapDerivedCategoryFactorsh.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (DerivedCategory.Qh.map
      ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).counit.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (G.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P))
  have hn₄ := NatTrans.congr_app ((homotopyComparisonRightIso FA).inv.naturality
    ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).counit.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    ((kFlatMapRight FB FA G hKFlat).obj
      ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P, hP⟩)
  simp only [NatTrans.comp_app] at hn₄
  have hfac := comp_chain₂ _ _ _ _ _ _ _
    (G.mapDerivedCategoryFactorsh.hom.naturality
      (((homotopyBifunctorIso FB).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).app P))
    (G.mapDerivedCategoryFactorsh.hom.naturality
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        (complexProjectionMap FA FB adj ε hε₁ hε₂ I P)))
  have hβ := Stacks.DerivedFunctor.derivedAdjunction_counit_app adj RF β hA
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
      (totalComplex FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
  apply ((Stacks.DerivedFunctor.derivedAdjunction adj RF β hA).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    map_adjunctionTensorMap_comp_counit]
  refine (derived_projection_chain G.mapDerivedCategory
    (Stacks.DerivedFunctor.derivedAdjunction adj RF β hA).counit _ _ _ _ _ _ hxa hm
    _ _ _ _ _ _ hτ _ _ hz _ _ hn₄.symm _ _ _ _ hhom _ _ _ hfac _ hβ _ _ rfl rfl _ rfl).trans ?_
  simp only [comparisonRightQhIso, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc, Functor.id_obj]
  rfl

/-- **The projection-formula map of a derived adjunction is invertible at `(Qh I, Qh P)`** for
a K-injective complex `I` and a K-flat complex `P`, as soon as the projection-formula map
`Tot(F I ⊗ P) ⟶ F(Tot(I ⊗ G P))` on complexes is a quasi-isomorphism and the derived-functor
comparison `β` of `F` is invertible at `Tot(I ⊗ G P)` (for instance because that complex is
K-injective, or `F`-acyclic). -/
theorem isIso_adjunctionTensorMap_derivedAdjunction_Qh (I : CochainComplex A ℤ)
    (hI : I.IsKInjective) (P : CochainComplex B ℤ) (hP : KFlat FB P)
    (hpf : QuasiIso (complexProjectionMap FA FB adj ε hε₁ hε₂ I P))
    (hT : IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
      (totalComplex FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))))) :
    IsIso (adjunctionTensorMap (Stacks.DerivedFunctor.derivedAdjunction adj RF β hA)
        (Functor.uncurry.obj (derivedBifunctor FB)) (Functor.uncurry.obj (derivedBifunctor FA))
        (derivedTransportProdIso FB FA G ε hε₁ hε₂ hKFlatLeft hKFlat).hom
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P))) := by
  have hβI : IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hA).2
        DerivedCategory.Qh RF β I hI
  have hq : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
      (complexProjectionMap FA FB adj ε hε₁ hε₂ I P))) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hpf)
  have h := adjunctionTensorMap_derivedAdjunction_Qh FA FB adj ε hε₁ hε₂ hKFlatLeft hKFlat RF β hA
    I P hP
  have hX : IsIso (((derivedBifunctor FB).map
      (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P))) :=
    inferInstance
  have hR : IsIso ((comparisonRightQhIso FB ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        P hP).hom ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        (complexProjectionMap FA FB adj ε hε₁ hε₂ I P)) ≫
      β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (totalComplex FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      RF.map ((comparisonRightQhIso FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (hKFlat P hP)).inv ≫
        ((derivedBifunctor FA).obj (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))).map
          (G.mapDerivedCategoryFactorsh.inv.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P)))) :=
    Iso.isIso_hom ((comparisonRightQhIso FB ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        P hP) ≪≫
      asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          (complexProjectionMap FA FB adj ε hε₁ hε₂ I P))) ≪≫
      @asIso _ _ _ _ (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (totalComplex FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) hT ≪≫
      RF.mapIso ((comparisonRightQhIso FA I ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (hKFlat P hP)).symm ≪≫
        ((derivedBifunctor FA).obj (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))).mapIso
          (G.mapDerivedCategoryFactorsh.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P)).symm))
  rw [← h] at hR
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hX hR

end CochainComplex.KFlatBifunctor

end
