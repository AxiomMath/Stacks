module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedIsoMapDerivedCategoryOfIsoComp
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryTransport

/-!
# Transport of morphisms along composites, read through derived functors

Let `F : C₁ ⥤ C₂` and `T : C₂ ⥤ C₃` be exact, with `v : F ⋙ T ≅ G` and `γ : F ⋙ T ≅ G'`
differing by an equality `G = G'`. Let `L_F`, `L_T`, `L_G`, `L_{G'}` be functors on derived
categories identified with `D(F)`, `D(T)`, `D(G)`, `D(G')`, with a composition isomorphism
`L_F ⋙ L_T ≅ L_G` compatible with `v`, and a transport `L_G ≅ L_{G'}` compatible with the
equality. Then the transport `Stacks.DerivedCategoryComparisons.transportQMap γ` of a morphism
read through `L_F` is `L_T` applied to it, read through `L_F ⋙ L_T ≅ L_{G'}`.

## Main results

* `Stacks.DerivedCategoryComparisons.transportQMap_eq_comp_derived`: the transport statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₃ w₂ w₁

namespace Stacks.DerivedCategoryComparisons

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- The identification `L(Q P) ≅ Q(F P)` given by an isomorphism `L ≅ D(F)` followed by the
canonical factorization of `D(F)`. -/
def derivedQIso (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {L : DerivedCategory C₁ ⥤ DerivedCategory C₂} (i : L ≅ F.mapDerivedCategory)
    (P : CochainComplex C₁ ℤ) :
    L.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  i.app (DerivedCategory.Q.obj P) ≪≫ F.mapDerivedCategoryFactors.app P

/-- Equal exact functors have equal images on each object of the derived category. -/
lemma mapDerivedCategory_obj_eq_of_eq {G G' : C₁ ⥤ C₂} [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [G'.Additive] [PreservesFiniteLimits G']
    [PreservesFiniteColimits G'] (h : G = G') (K : DerivedCategory C₁) :
    G.mapDerivedCategory.obj K = G'.mapDerivedCategory.obj K := by
  subst h
  rfl

/-- A morphism read through `L ≅ D(F)` at `Q P`, `Q I`: restriction along `F` is `L` read
through `Stacks.DerivedCategoryComparisons.derivedQIso`. -/
lemma restrictQMap_eq_derivedQIso (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {L : DerivedCategory C₁ ⥤ DerivedCategory C₂}
    (i : L ≅ F.mapDerivedCategory) {P I : CochainComplex C₁ ℤ}
    (d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :
    restrictQMap F d = (derivedQIso F i P).inv ≫ L.map d ≫ (derivedQIso F i I).hom := by
  simp only [restrictQMap, derivedQIso, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    Category.assoc]
  rw [← NatIso.naturality_2 i d]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- Conjugating by `ρ : F ⋙ G ≅ H` commutes with pre- and postcomposition by images of
morphisms under `F` and `H`. -/
lemma inv_app_comp_map_comp_hom_app {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
    {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ ℰ} {H : 𝒞 ⥤ ℰ} (ρ : F ⋙ G ≅ H) {X X' Y Y' : 𝒞} (f : X ⟶ X')
    (x : F.obj X' ⟶ F.obj Y') (g : Y' ⟶ Y) :
    ρ.inv.app X ≫ G.map (F.map f ≫ x ≫ F.map g) ≫ ρ.hom.app Y =
      H.map f ≫ (ρ.inv.app X' ≫ G.map x ≫ ρ.hom.app Y') ≫ H.map g := by
  have h₁ := ρ.inv.naturality f
  have h₂ := ρ.hom.naturality g
  simp only [Functor.comp_map] at h₁ h₂
  simp only [Functor.map_comp, Category.assoc]
  rw [← h₂, reassoc_of% h₁]

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] in
/-- Two isomorphisms `F ⋙ T ≅ G'` that differ by an equality `G = G'` induce, on complexes,
isomorphisms that differ by the transport along `G = G'`. -/
lemma Q_map_mapHomologicalComplexCompIso_hom_app_of_hom_eq {F : C₁ ⥤ C₂} {T : C₂ ⥤ C₃}
    {G G' : C₁ ⥤ C₃} [F.Additive] [T.Additive] [G.Additive] [G'.Additive]
    (v : F ⋙ T ≅ G) (h : G = G') (γ : F ⋙ T ≅ G') (hγ : γ.hom = v.hom ≫ eqToHom h)
    (P : CochainComplex C₁ ℤ) :
    DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).hom.app P) =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso v (ComplexShape.up ℤ)).hom.app P) ≫
        eqToHom (by subst h; rfl) := by
  subst h
  obtain rfl : γ = v := Iso.ext (by simpa using hγ)
  simp

section Comp

variable {F : C₁ ⥤ C₂} {T : C₂ ⥤ C₃} {G G' : C₁ ⥤ C₃}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [hGadd : G.Additive] [hGpfl : PreservesFiniteLimits G] [hGpfc : PreservesFiniteColimits G]
  [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (v : F ⋙ T ≅ G) (h : G = G') (γ : F ⋙ T ≅ G') (hγ : γ.hom = v.hom ≫ eqToHom h)
  {LF : DerivedCategory C₁ ⥤ DerivedCategory C₂} {LT : DerivedCategory C₂ ⥤ DerivedCategory C₃}
  {LG LG' : DerivedCategory C₁ ⥤ DerivedCategory C₃}
  (iF : LF ≅ F.mapDerivedCategory) (iT : LT ≅ T.mapDerivedCategory)
  (iG : LG ≅ G.mapDerivedCategory) (iG' : LG' ≅ G'.mapDerivedCategory)
  (comp : LF ⋙ LT ≅ LG) (cong : LG ≅ LG')
  (hcong : ∀ K, cong.hom.app K ≫ iG'.hom.app K =
    iG.hom.app K ≫ eqToHom (mapDerivedCategory_obj_eq_of_eq h K))
  (hcoh : comp.hom ≫ iG.hom = Functor.whiskerRight iF.hom LT ≫
    Functor.whiskerLeft F.mapDerivedCategory iT.hom ≫
      (Stacks.Homology.mapDerivedCategoryCompIso F T G v).hom)

include hγ hcong hcoh in
/-- The composition isomorphism `L_F ⋙ L_T ≅ L_{G'}`, read through the identifications with the
induced functors at `Q(P)`, is `L_T` of the identification for `F`, followed by the identification
for `T` and the comparison `γ` on complexes. -/
lemma comp_trans_hom_app_comp_derivedQIso_hom (P : CochainComplex C₁ ℤ) :
    (comp ≪≫ cong).hom.app (DerivedCategory.Q.obj P) ≫ (derivedQIso G' iG' P).hom =
      LT.map (derivedQIso F iF P).hom ≫ iT.hom.app _ ≫
        T.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).hom.app P) := by
  have h1 := congrArg (fun t => t.app (DerivedCategory.Q.obj P) ≫
    G.mapDerivedCategoryFactors.hom.app P) hcoh
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] at h1
  rw [Stacks.Homology.mapDerivedCategoryCompIso_hom_app_Q] at h1
  rw [Q_map_mapHomologicalComplexCompIso_hom_app_of_hom_eq v h γ hγ P]
  simp only [derivedQIso, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% (hcong (DerivedCategory.Q.obj P)),
    eqToHom_comp_mapDerivedCategoryFactors_hom_app h P, reassoc_of% h1, Functor.map_comp,
    Category.assoc, ← NatTrans.naturality_assoc]

include hγ hcong hcoh in
/-- **Transport along a composite, through derived functors.** The transport along `γ` of a
morphism `L_F(Q P) ⟶ L_F(Q I)`, read through `L_F ≅ D(F)`, is its image under `L_T`, read
through the composition isomorphism `ρ = comp ≪≫ cong : L_F ⋙ L_T ≅ L_{G'}` and
`L_{G'} ≅ D(G')`. -/
lemma transportQMap_eq_comp_derived (ρ : LF ⋙ LT ≅ LG') (hρ : comp ≪≫ cong = ρ)
    {P I : CochainComplex C₁ ℤ}
    (β : LF.obj (DerivedCategory.Q.obj P) ⟶ LF.obj (DerivedCategory.Q.obj I)) :
    transportQMap γ ((derivedQIso F iF P).inv ≫ β ≫ (derivedQIso F iF I).hom) =
      (derivedQIso G' iG' P).inv ≫ (ρ.inv.app _ ≫ LT.map β ≫ ρ.hom.app _) ≫
        (derivedQIso G' iG' I).hom := by
  subst hρ
  have key := comp_trans_hom_app_comp_derivedQIso_hom (hGadd := hGadd) (hGpfl := hGpfl)
    (hGpfc := hGpfc) v h γ hγ iF iT iG iG' comp cong hcong hcoh
  have := transportQMap_eq_of_iso γ LT iT (derivedQIso F iF P) (derivedQIso F iF I)
    (derivedQIso G' iG' P) (derivedQIso G' iG' I) ((comp ≪≫ cong).app _) ((comp ≪≫ cong).app _)
    (key P) (key I) β
  simpa only [Iso.app_inv, Iso.app_hom] using this

end Comp

end Stacks.DerivedCategoryComparisons

end
