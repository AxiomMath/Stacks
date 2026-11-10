module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow

/-!
# Base change maps between bounded below right derived functors

Consider a square of additive functors between abelian categories
```
A --G'--> A'
|F        |F'
v         v
B --G---> B'
```
with `G` and `G'` exact, `A` and `A'` with enough injectives, and a transformation
`α : F ⋙ G ⟶ G' ⋙ F'`. This file constructs the induced *base change map*
$$
G \circ RF \longrightarrow RF' \circ G'
$$
of functors `D⁺(A) ⥤ D⁺(B')`. The exact functors act on bounded below derived categories
degreewise (`CategoryTheory.Functor.mapDerivedCategoryPlus`), `RF ⋙ G` is a right derived functor
of degreewise `F ⋙ G` (`CategoryTheory.Functor.isRightDerivedFunctor_postcomp`), and the
degreewise transformation `α`, followed by the derived-functor unit of `RF'`, descends along the
universal property.

This is the shape of the base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` of [Stacks, Tag 0DDE]
for sheaves of modules, where `F = f_*`, `F' = f'_*`, `G = g^{-1}`, `G' = (g')^{-1}` and `α` is
the underived base change comparison.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus`: the base change map
  `RF ⋙ G ⟶ G' ⋙ RF'`.

## Main results

* `Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus_fac`: precomposed with `G` of
  the derived-functor unit of `RF`, the base change map is the localized degreewise `α` followed
  by the derived-functor unit of `RF'`.
* `Stacks.Cohomology.DerivedBaseChangePlus.isIso_derivedBaseChangePlus_app_of_quasiIso`: at a
  bounded below complex of injectives `I`, the base change map is an isomorphism as soon as the
  morphism of complexes `α_I ≫ F'(i) : G(F(I)) ⟶ F'(L)` is a quasi-isomorphism (an isomorphism
  of the derived category) for one quasi-isomorphism `i : G'(I) ⟶ L` onto a bounded below complex
  of injectives.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedBaseChangePlus

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [EnoughInjectives A] [EnoughInjectives A']
  (F : A ⥤ B) (F' : A' ⥤ B') (G : B ⥤ B') (G' : A ⥤ A')
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (α : F ⋙ G ⟶ G' ⋙ F')

/-- The derived-functor unit exhibiting `RF ⋙ G` as a right derived functor of degreewise
`F ⋙ G`: the unit of `RF` whiskered with `G`. -/
abbrev derivedBaseChangePlusUnit :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ G.mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus) :=
  Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.mapDerivedCategoryPlus

/-- The degreewise `α : F ⋙ G ⟶ G' ⋙ F'` on bounded below complexes, localized, followed by the
derived-functor unit of `RF'`; read on the source of the derived-functor unit of `RF ⋙ G`. -/
def derivedBaseChangePlusAux :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ G.mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙ (G'.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft F.mapHomotopyCategoryPlus G.mapDerivedCategoryPlusFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatTrans α) DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft G'.mapHomotopyCategoryPlus F'.rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight G'.mapDerivedCategoryPlusFactorsh.inv F'.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- **The base change map `RF ⋙ G ⟶ G' ⋙ RF'`** on bounded below derived categories, induced by
`α : F ⋙ G ⟶ G' ⋙ F'` for exact `G` and `G'`. -/
def derivedBaseChangePlus :
    F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus ⟶
      G'.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus :=
  (F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus).rightDerivedDesc
    (derivedBaseChangePlusUnit F G) (HomotopyCategory.Plus.quasiIso A)
    (G'.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus) (derivedBaseChangePlusAux F F' G G' α)

/-- **The characterization of the base change map on bounded below complexes**: precomposed with
`G` of the derived-functor unit of `RF` at `K`, it is `derivedBaseChangePlusAux` at `K`. -/
theorem derivedBaseChangePlus_fac (K : HomotopyCategory.Plus A) :
    G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
      (derivedBaseChangePlus F F' G G' α).app (DerivedCategory.Plus.Qh.obj K) =
    (derivedBaseChangePlusAux F F' G G' α).app K :=
  (F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus).rightDerived_fac_app
    (derivedBaseChangePlusUnit F G) (HomotopyCategory.Plus.quasiIso A)
    (G'.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus)
    (derivedBaseChangePlusAux F F' G G' α) K

omit [EnoughInjectives A] in
/-- The components of `derivedBaseChangePlusAux`. -/
theorem derivedBaseChangePlusAux_app (K : HomotopyCategory.Plus A) :
    (derivedBaseChangePlusAux F F' G G' α).app K =
      G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans α).app K) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv.app K) ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K) ≫
        F'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  simp [derivedBaseChangePlusAux]

/-- The components of `Functor.mapHomologicalComplexCompIso` of an identity isomorphism are
identities. -/
private theorem mapHomologicalComplexCompIso_refl_hom_app_eq_id {A B B' : Type*} [Category* A]
    [Category* B] [Category* B'] [Preadditive A] [Preadditive B] [Preadditive B']
    (F : A ⥤ B) (G : B ⥤ B') [F.Additive] [G.Additive] (K : CochainComplex A ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app K =
      𝟙 _ := by
  ext n
  simp [Functor.mapHomologicalComplexCompIso]

/-- The components of the inverse of `Functor.mapHomologicalComplexCompIso` of an identity
isomorphism are identities. -/
private theorem mapHomologicalComplexCompIso_refl_inv_app_eq_id {A B B' : Type*} [Category* A]
    [Category* B] [Category* B'] [Preadditive A] [Preadditive B] [Preadditive B']
    (F : A ⥤ B) (G : B ⥤ B') [F.Additive] [G.Additive] (K : CochainComplex A ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app K =
      𝟙 _ := by
  ext n
  simp [Functor.mapHomologicalComplexCompIso]

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G] [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] in
/-- **The degreewise comparison followed by the derived-functor unit, through a resolution.**
If `i : G'(I) ⟶ L` is a quasi-isomorphism onto a bounded below complex of injectives and the
morphism of complexes `α_I ≫ F'(i)` is a quasi-isomorphism, then the localized degreewise
`α_I` followed by the unit `F'(G'(I)) ⟶ RF'(G'(I))` is an isomorphism. -/
theorem isIso_Qh_map_comp_rightDerivedFunctorPlusUnit_app (I : CochainComplex.Plus A)
    (L : CochainComplex.Plus A') [∀ n, Injective (L.obj.X n)]
    (i : G'.mapCochainComplexPlus.obj I ⟶ L) (hi : QuasiIso i.hom)
    (hx : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I.obj ≫
        (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom))) :
    IsIso (DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatTrans α).app
          ((HomotopyCategory.Plus.quotient A).obj I)) ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (G' ⋙ F'))).inv.app ((HomotopyCategory.Plus.quotient A).obj I)) ≫
      F'.rightDerivedFunctorPlusUnith.app
        (G'.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient A).obj I))) := by
  let K := (HomotopyCategory.Plus.quotient A).obj I
  let φ : G'.mapHomotopyCategoryPlus.obj K ⟶ (HomotopyCategory.Plus.quotient A').obj L :=
    (HomotopyCategory.Plus.quotient A').map i
  have hφ : IsIso (F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map φ)) := by
    have : IsIso (DerivedCategory.Plus.Qh.map φ) :=
      Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _) φ
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hi)
    infer_instance
  have hnat := F'.rightDerivedFunctorPlusUnith.naturality φ
  simp only [Functor.comp_map] at hnat
  let ψ := (Functor.mapHomotopyCategoryPlusNatTrans α).app K ≫
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv.app K ≫
      F'.mapHomotopyCategoryPlus.map φ
  have hψq : HomotopyCategory.Plus.quasiIso _ ψ := by
    change HomotopyCategory.quasiIso _ _ ψ.hom
    have e : ψ.hom = (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I.obj ≫
          (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom) := by
      change (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I.obj) ≫
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (G' ⋙ F'))
            (ComplexShape.up ℤ)).inv.app I.obj) ≫
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom) = _
      rw [mapHomologicalComplexCompIso_refl_inv_app_eq_id, CategoryTheory.Functor.map_id,
        Category.id_comp, ← Functor.map_comp]
    rw [e]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hx)
  have hψ : IsIso (DerivedCategory.Plus.Qh.map ψ) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _) ψ hψq
  have e : (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans α).app K) ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (G' ⋙ F'))).inv.app K) ≫
      F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K)) ≫
        F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map φ) =
      DerivedCategory.Plus.Qh.map ψ ≫
        F'.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A').obj L) := by
    simp only [ψ, Functor.map_comp, Category.assoc]
    exact congrArg (fun t => DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusNatTrans α).app K) ≫ DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv.app K) ≫ t) hnat.symm
  have h' : IsIso (DerivedCategory.Plus.Qh.map ψ ≫
      F'.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A').obj L)) :=
    inferInstance
  rw [← e] at h'
  exact IsIso.of_isIso_comp_right _ (F'.rightDerivedFunctorPlus.map
    (DerivedCategory.Plus.Qh.map φ))

/-- **The base change map at a bounded below complex of injectives, through a resolution of its
image.** Let `I` be a bounded below complex of injectives of `A`, and `i : G'(I) ⟶ L` a
quasi-isomorphism onto a bounded below complex of injectives of `A'`. If the morphism of
complexes `α_I ≫ F'(i) : G(F(I)) ⟶ F'(L)` is a quasi-isomorphism, then the base change map
`G(RF(I)) ⟶ RF'(G'(I))` is an isomorphism. -/
theorem isIso_derivedBaseChangePlus_app_of_quasiIso (I : CochainComplex.Plus A)
    [∀ n, Injective (I.obj.X n)] (L : CochainComplex.Plus A') [∀ n, Injective (L.obj.X n)]
    (i : G'.mapCochainComplexPlus.obj I ⟶ L) (hi : QuasiIso i.hom)
    (hx : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I.obj ≫
        (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom))) :
    IsIso ((derivedBaseChangePlus F F' G G' α).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj I))) := by
  have hfac := derivedBaseChangePlus_fac F F' G G' α ((HomotopyCategory.Plus.quotient A).obj I)
  rw [derivedBaseChangePlusAux_app] at hfac
  have hgen := isIso_Qh_map_comp_rightDerivedFunctorPlusUnit_app F F' G G' α I L i hi hx
  have hR : IsIso (G.mapDerivedCategoryPlus.map
      (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj I)) ≫
        (derivedBaseChangePlus F F' G G' α).app
          (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj I))) := by
    rw [hfac]
    refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance ?_)
    simpa only [Category.assoc] using IsIso.comp_isIso' hgen inferInstance
  exact IsIso.of_isIso_comp_left (G.mapDerivedCategoryPlus.map
    (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj I))) _

section Comparison

/-- The components of `CategoryTheory.Functor.mapHomotopyCategoryCompIso` of an identity
isomorphism at the image of a complex are identities. -/
theorem mapHomotopyCategoryCompIso_refl_hom_app_quotient_obj {A B B' : Type*} [Category* A]
    [Category* B] [Category* B'] [Preadditive A] [Preadditive B] [Preadditive B']
    (F : A ⥤ B) (G : B ⥤ B') [F.Additive] [G.Additive] (K : CochainComplex A ℤ) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) = 𝟙 _ := by
  change (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app K) = _
  rw [mapHomologicalComplexCompIso_refl_hom_app_eq_id, CategoryTheory.Functor.map_id]
  rfl

/-- The components of the inverse of `CategoryTheory.Functor.mapHomotopyCategoryCompIso` of an
identity isomorphism at the image of a complex are identities. -/
theorem mapHomotopyCategoryCompIso_refl_inv_app_quotient_obj {A B B' : Type*} [Category* A]
    [Category* B] [Category* B'] [Preadditive A] [Preadditive B] [Preadditive B']
    (F : A ⥤ B) (G : B ⥤ B') [F.Additive] [G.Additive] (K : CochainComplex A ℤ) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) = 𝟙 _ := by
  change (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app K) = _
  rw [mapHomologicalComplexCompIso_refl_inv_app_eq_id, CategoryTheory.Functor.map_id]
  rfl

/-- A morphism of complexes whose image in the homotopy category becomes an isomorphism of the
derived category is an isomorphism of the derived category. -/
theorem isIso_Q_map_of_isIso_Qh_map_eq {C : Type*} {_ : Category C} {_ : Abelian C}
    {_ : HasDerivedCategory C} {K L : CochainComplex C ℤ} (z : K ⟶ L)
    (m : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)
    (hm : m = (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map z)
    (h : IsIso (DerivedCategory.Qh.map m)) : IsIso (DerivedCategory.Q.map z) := by
  subst hm
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) z).1 h

/-- At the image of a complex `K`, the degreewise comparison
`CategoryTheory.NatTrans.mapHomotopyCategory α`, conjugated by the identity comparisons
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` and followed by the image of the class of `q`
under `F'`, is the class of `α_K ≫ F'(q)`. -/
theorem quotient_map_natTrans_comp_eq {A A' B B' : Type*} {_ : Category A} {_ : Category A'}
    {_ : Category B} {_ : Category B'} {_ : Preadditive A} {_ : Preadditive A'}
    {_ : Preadditive B} {_ : Preadditive B'} (F : A ⥤ B) (G : B ⥤ B') (G' : A ⥤ A')
    (F' : A' ⥤ B') {_ : F.Additive} {_ : G.Additive} {_ : G'.Additive} {_ : F'.Additive}
    {_ : (F ⋙ G).Additive} {_ : (G' ⋙ F').Additive}
    (α : F ⋙ G ⟶ G' ⋙ F') (K : CochainComplex A ℤ) (K' : CochainComplex A' ℤ)
    (q : (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ K') :
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (G' ⋙ F')) (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
      (F'.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map q) =
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K ≫
          (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
  change ((HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).hom.app K) ≫
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) ≫
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (G' ⋙ F'))
          (ComplexShape.up ℤ)).inv.app K)) ≫
    (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
      ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).map q) = _
  rw [mapHomologicalComplexCompIso_refl_hom_app_eq_id,
    mapHomologicalComplexCompIso_refl_inv_app_eq_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, ← Functor.map_comp]

/-- The component at the image of a complex of the degreewise comparison
`CategoryTheory.NatTrans.mapHomotopyCategory α` conjugated by the identity comparisons
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` is the class of the degreewise
comparison. -/
theorem mapHomotopyCategoryCompIso_hom_comp_comp_inv_app_quotient_obj {A A' B B' : Type*}
    {_ : Category A} {_ : Category A'} {_ : Category B} {_ : Category B'} {_ : Preadditive A}
    {_ : Preadditive A'} {_ : Preadditive B} {_ : Preadditive B'} (F : A ⥤ B) (G : B ⥤ B')
    (G' : A ⥤ A') (F' : A' ⥤ B') {_ : F.Additive} {_ : G.Additive} {_ : G'.Additive}
    {_ : F'.Additive} {_ : (F ⋙ G).Additive} {_ : (G' ⋙ F').Additive}
    (α : F ⋙ G ⟶ G' ⋙ F') (K : CochainComplex A ℤ) :
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (G' ⋙ F')) (ComplexShape.up ℤ)).inv).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) := by
  change (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).hom.app K) ≫
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) ≫
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (G' ⋙ F'))
          (ComplexShape.up ℤ)).inv.app K) = _
  rw [mapHomologicalComplexCompIso_refl_hom_app_eq_id,
    mapHomologicalComplexCompIso_refl_inv_app_eq_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]

/-- A morphism of complexes `y ≫ F(q)` is an isomorphism of the derived category as soon as the
composite of the classes of `y` and of `F(q)` in the homotopy category localizes to one. -/
theorem isIso_Q_map_comp_of_isIso_Qh_map {C D : Type*} {_ : Category C} {_ : Category D}
    {_ : Preadditive C} {_ : Abelian D} {_ : HasDerivedCategory D} (F : C ⥤ D)
    {_ : F.Additive} {K : CochainComplex D ℤ} {L M : CochainComplex C ℤ}
    (y : K ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) (q : L ⟶ M)
    (h : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map y ≫
      (F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map q)))) :
    IsIso (DerivedCategory.Q.map (y ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) := by
  change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map y ≫
    (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q))) at h
  rw [← Functor.map_comp] at h
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso D) _).1 h

/-- The image under `F.mapHomotopyCategory` of the class of a morphism of complexes `q` is the class
of `F(q)`. -/
theorem mapHomotopyCategory_map_quotient_map {C D : Type*} {_ : Category C} {_ : Category D}
    {_ : Preadditive C} {_ : Preadditive D} (F : C ⥤ D) {_ : F.Additive}
    {L M : CochainComplex C ℤ} (q : L ⟶ M) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map q) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) :=
  rfl

end Comparison

section Forget

/-- **Detecting a quasi-isomorphism through an exact conservative functor.** If `U` is exact and
reflects isomorphisms, and `U(x)` agrees with `y` up to isomorphisms of source and target, then
`x` is an isomorphism of the derived category as soon as `y` is. -/
theorem isIso_Q_map_of_isIso_Q_map_of_comp_eq {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (U : C ⥤ D)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U] [U.ReflectsIsomorphisms]
    {K₁ K₂ : CochainComplex C ℤ} (x : K₁ ⟶ K₂) {M₁ M₂ : CochainComplex D ℤ} (y : M₁ ⟶ M₂)
    (e₁ : M₁ ≅ (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₁)
    (e₂ : M₂ ≅ (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₂)
    (hxy : y ≫ e₂.hom = e₁.hom ≫ (U.mapHomologicalComplex (ComplexShape.up ℤ)).map x)
    (hy : IsIso (DerivedCategory.Q.map y)) : IsIso (DerivedCategory.Q.map x) := by
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at hy ⊢
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ U]
  have h' : QuasiIso (y ≫ e₂.hom) := inferInstance
  rw [hxy] at h'
  exact (quasiIso_iff_comp_left _ _).1 h'

end Forget

end Stacks.Cohomology.DerivedBaseChangePlus
