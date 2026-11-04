module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedIsoMapDerivedCategoryOfIsoComp
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# Squares of exact functors on derived categories, and their composition

An isomorphism `β : e ⋙ ι' ≅ ι ⋙ p` of exact functors between abelian categories induces an
isomorphism `D(e) ⋙ D(ι') ≅ D(ι) ⋙ D(p)` of the functors they induce on derived categories
(`Stacks.DerivedCategoryComparisons.mapDerivedCategorySquareIso`). This file shows that pasting
squares horizontally is compatible with this construction: if three squares `β_f`, `β_g`, `β_h`
are related by `e_f ⋙ e_g ≅ e_h` and `p_f ⋙ p_g ≅ p_h` on the level of the abelian categories,
the induced squares are related by the induced composition isomorphisms on derived categories.

## Main definitions

* `Stacks.DerivedCategoryComparisons.mapDerivedCategorySquareIso`: the isomorphism
  `D(e) ⋙ D(ι') ≅ D(ι) ⋙ D(p)` induced by an isomorphism `e ⋙ ι' ≅ ι ⋙ p` of exact functors.

## Main results

* `Stacks.DerivedCategoryComparisons.mapDerivedCategorySquareIso_hom_app_Q`: its value at the
  image of a cochain complex.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategorySquareIso_comp_hom`: **compatibility
  with composition of squares.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedCategoryComparisons

universe w₁ w₂ w₃ w₄ w₅ w₆

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

section Square

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {D₁ : Type*} [Category D₁] [Abelian D₁] [HasDerivedCategory.{w₃} D₁]
  {D₂ : Type*} [Category D₂] [Abelian D₂] [HasDerivedCategory.{w₄} D₂]
  (e : C₁ ⥤ C₂) (ι : C₁ ⥤ D₁) (ι' : C₂ ⥤ D₂) (p : D₁ ⥤ D₂)
  [e.Additive] [PreservesFiniteLimits e] [PreservesFiniteColimits e]
  [ι.Additive] [PreservesFiniteLimits ι] [PreservesFiniteColimits ι]
  [ι'.Additive] [PreservesFiniteLimits ι'] [PreservesFiniteColimits ι']
  [p.Additive] [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  (β : e ⋙ ι' ≅ ι ⋙ p)

/-- The isomorphism `D(e) ⋙ D(ι') ≅ D(ι) ⋙ D(p)` of functors on derived categories induced by
an isomorphism `e ⋙ ι' ≅ ι ⋙ p` of exact functors. -/
def mapDerivedCategorySquareIso :
    e.mapDerivedCategory ⋙ ι'.mapDerivedCategory ≅ ι.mapDerivedCategory ⋙ p.mapDerivedCategory :=
  (mapDerivedCategoryCompIso e ι').symm ≪≫ mapDerivedCategoryIsoOfNatIso _ _ β ≪≫
    mapDerivedCategoryCompIso ι p

/-- The square isomorphism at the image of a cochain complex: the canonical factorizations
around `Q` of the degreewise isomorphism. -/
lemma mapDerivedCategorySquareIso_hom_app_Q (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategorySquareIso e ι ι' p β).hom.app (DerivedCategory.Q.obj P) =
      ι'.mapDerivedCategory.map (e.mapDerivedCategoryFactors.hom.app P) ≫
        ι'.mapDerivedCategoryFactors.hom.app ((e.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex β (ComplexShape.up ℤ)).hom.app P) ≫
        p.mapDerivedCategoryFactors.inv.app ((ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        p.mapDerivedCategory.map (ι.mapDerivedCategoryFactors.inv.app P) := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    mapDerivedCategoryCompIso_inv_app_Q, mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    mapDerivedCategoryCompIso_hom_app_Q, Category.assoc, Iso.inv_hom_id_app_assoc]

end Square

section Comp

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {D₁ : Type*} [Category D₁] [Abelian D₁] [HasDerivedCategory.{w₄} D₁]
  {D₂ : Type*} [Category D₂] [Abelian D₂] [HasDerivedCategory.{w₅} D₂]
  {D₃ : Type*} [Category D₃] [Abelian D₃] [HasDerivedCategory.{w₆} D₃]
  (e₁ : C₁ ⥤ C₂) (e₂ : C₂ ⥤ C₃) (e₃ : C₁ ⥤ C₃) (ι₁ : C₁ ⥤ D₁) (ι₂ : C₂ ⥤ D₂) (ι₃ : C₃ ⥤ D₃)
  (p₁ : D₁ ⥤ D₂) (p₂ : D₂ ⥤ D₃) (p₃ : D₁ ⥤ D₃)
  [e₁.Additive] [PreservesFiniteLimits e₁] [PreservesFiniteColimits e₁]
  [e₂.Additive] [PreservesFiniteLimits e₂] [PreservesFiniteColimits e₂]
  [e₃.Additive] [PreservesFiniteLimits e₃] [PreservesFiniteColimits e₃]
  [ι₁.Additive] [PreservesFiniteLimits ι₁] [PreservesFiniteColimits ι₁]
  [ι₂.Additive] [PreservesFiniteLimits ι₂] [PreservesFiniteColimits ι₂]
  [ι₃.Additive] [PreservesFiniteLimits ι₃] [PreservesFiniteColimits ι₃]
  [p₁.Additive] [PreservesFiniteLimits p₁] [PreservesFiniteColimits p₁]
  [p₂.Additive] [PreservesFiniteLimits p₂] [PreservesFiniteColimits p₂]
  [p₃.Additive] [PreservesFiniteLimits p₃] [PreservesFiniteColimits p₃]
  (β₁ : e₁ ⋙ ι₂ ≅ ι₁ ⋙ p₁) (β₂ : e₂ ⋙ ι₃ ≅ ι₂ ⋙ p₂) (β₃ : e₃ ⋙ ι₃ ≅ ι₁ ⋙ p₃)
  (u : e₁ ⋙ e₂ ≅ e₃) (v : p₁ ⋙ p₂ ≅ p₃)

/-- A component of a natural transformation, conjugated along an isomorphism of objects. -/
private lemma app_eq_conj {A B : Type*} [Category A] [Category B] {F G : A ⥤ B} (τ : F ⟶ G)
    {a b : A} (φ : a ≅ b) : τ.app a = F.map φ.hom ≫ τ.app b ≫ G.map φ.inv := by
  rw [← Category.assoc, τ.naturality, Category.assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id,
    Category.comp_id]

/-- Cancellation of a component of an isomorphism under one functor. -/
private lemma map_inv_hom_app_assoc {A B C : Type*} [Category A] [Category B] [Category C]
    (H : B ⥤ C) {F G : A ⥤ B} (e : F ≅ G) (X : A) {c : C} (k : H.obj (G.obj X) ⟶ c) :
    H.map (e.inv.app X) ≫ H.map (e.hom.app X) ≫ k = k := by
  rw [← H.map_comp_assoc, Iso.inv_hom_id_app, H.map_id, Category.id_comp]

/-- Cancellation of a component of an isomorphism under two functors. -/
private lemma map_map_inv_hom_app_assoc {A B C E : Type*} [Category A] [Category B]
    [Category C] [Category E] (K : C ⥤ E) (H : B ⥤ C) {F G : A ⥤ B} (e : F ≅ G) (X : A)
    {c : E} (k : K.obj (H.obj (G.obj X)) ⟶ c) :
    K.map (H.map (e.inv.app X)) ≫ K.map (H.map (e.hom.app X)) ≫ k = k := by
  exact map_inv_hom_app_assoc K (Functor.isoWhiskerRight e H) X k

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₁] [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  [PreservesFiniteLimits e₁] [PreservesFiniteColimits e₁]
  [PreservesFiniteLimits e₂] [PreservesFiniteColimits e₂]
  [PreservesFiniteLimits e₃] [PreservesFiniteColimits e₃]
  [PreservesFiniteLimits ι₁] [PreservesFiniteColimits ι₁]
  [PreservesFiniteLimits ι₂] [PreservesFiniteColimits ι₂]
  [PreservesFiniteLimits ι₃] [PreservesFiniteColimits ι₃]
  [PreservesFiniteLimits p₁] [PreservesFiniteColimits p₁]
  [PreservesFiniteLimits p₂] [PreservesFiniteColimits p₂]
  [PreservesFiniteLimits p₃] [PreservesFiniteColimits p₃] in
/-- The degreewise form of the pasting condition. -/
private lemma pasting_degreewise
    (h : ∀ M, ι₃.map (u.hom.app M) ≫ β₃.hom.app M =
      β₂.hom.app (e₁.obj M) ≫ p₂.map (β₁.hom.app M) ≫ v.hom.app (ι₁.obj M))
    (P : CochainComplex C₁ ℤ) :
    (ι₃.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso u (ComplexShape.up ℤ)).hom.app P) ≫
      (NatIso.mapHomologicalComplex β₃ (ComplexShape.up ℤ)).hom.app P =
    (NatIso.mapHomologicalComplex β₂ (ComplexShape.up ℤ)).hom.app
        ((e₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      (p₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex β₁ (ComplexShape.up ℤ)).hom.app P) ≫
      (Functor.mapHomologicalComplexCompIso v (ComplexShape.up ℤ)).hom.app
        ((ι₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  ext n
  simpa using h (P.X n)

/-- **Pasting squares is compatible with passing to derived categories.** If the squares
`β₁ : e₁ ⋙ ι₂ ≅ ι₁ ⋙ p₁`, `β₂ : e₂ ⋙ ι₃ ≅ ι₂ ⋙ p₂` paste, through `u : e₁ ⋙ e₂ ≅ e₃` and
`v : p₁ ⋙ p₂ ≅ p₃`, to `β₃ : e₃ ⋙ ι₃ ≅ ι₁ ⋙ p₃`, then the induced squares on derived categories
paste, through the induced composition isomorphisms, to the square induced by `β₃`. -/
theorem mapDerivedCategorySquareIso_comp_hom
    (h : ∀ M, ι₃.map (u.hom.app M) ≫ β₃.hom.app M =
      β₂.hom.app (e₁.obj M) ≫ p₂.map (β₁.hom.app M) ≫ v.hom.app (ι₁.obj M)) :
    Functor.whiskerRight (Stacks.Homology.mapDerivedCategoryCompIso e₁ e₂ e₃ u).hom
        ι₃.mapDerivedCategory ≫ (mapDerivedCategorySquareIso e₃ ι₁ ι₃ p₃ β₃).hom =
      Functor.whiskerLeft e₁.mapDerivedCategory (mapDerivedCategorySquareIso e₂ ι₂ ι₃ p₂ β₂).hom ≫
        Functor.whiskerRight (mapDerivedCategorySquareIso e₁ ι₁ ι₂ p₁ β₁).hom
          p₂.mapDerivedCategory ≫
        Functor.whiskerLeft ι₁.mapDerivedCategory
          (Stacks.Homology.mapDerivedCategoryCompIso p₁ p₂ p₃ v).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_
  have hu := (Iso.eq_comp_inv (e₃.mapDerivedCategoryFactors.app P)).2
    (Stacks.Homology.mapDerivedCategoryCompIso_hom_app_Q e₁ e₂ e₃ u P)
  have hv := (Iso.eq_comp_inv (p₃.mapDerivedCategoryFactors.app
    ((ι₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))).2
    (Stacks.Homology.mapDerivedCategoryCompIso_hom_app_Q p₁ p₂ p₃ v
      ((ι₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
  have hd := congrArg DerivedCategory.Q.map (pasting_degreewise e₁ e₂ e₃ ι₁ ι₂ ι₃ p₁ p₂ p₃
    β₁ β₂ β₃ u v h P)
  have n₃ := ι₃.mapDerivedCategoryFactors.hom.naturality
    ((Functor.mapHomologicalComplexCompIso u (ComplexShape.up ℤ)).hom.app P)
  have n₂ : p₂.mapDerivedCategory.map (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex β₁ (ComplexShape.up ℤ)).hom.app P)) ≫
      p₂.mapDerivedCategoryFactors.hom.app ((p₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ι₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
      p₂.mapDerivedCategoryFactors.hom.app ((ι₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((e₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((p₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex β₁ (ComplexShape.up ℤ)).hom.app P)) :=
    p₂.mapDerivedCategoryFactors.hom.naturality
      ((NatIso.mapHomologicalComplex β₁ (ComplexShape.up ℤ)).hom.app P)
  simp only [Functor.comp_map] at n₃
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj]
  rw [app_eq_conj (mapDerivedCategorySquareIso e₂ ι₂ ι₃ p₂ β₂).hom
      (a := e₁.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
      (b := DerivedCategory.Q.obj ((e₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
      (e₁.mapDerivedCategoryFactors.app P),
    app_eq_conj (Stacks.Homology.mapDerivedCategoryCompIso p₁ p₂ p₃ v).hom
      (a := ι₁.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
      (b := DerivedCategory.Q.obj ((ι₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
      (ι₁.mapDerivedCategoryFactors.app P)]
  simp only [hu, hv, mapDerivedCategorySquareIso_hom_app_Q]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc, Iso.app_hom, Iso.app_inv,
    map_inv_hom_app_assoc, map_map_inv_hom_app_assoc] at hd ⊢
  rw [reassoc_of% n₃, reassoc_of% n₂, Iso.inv_hom_id_app_assoc, reassoc_of% hd]

end Comp

end Stacks.DerivedCategoryComparisons

end
