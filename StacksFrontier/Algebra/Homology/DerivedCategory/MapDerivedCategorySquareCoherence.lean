module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import
  StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory

/-!
# Derived squares of exact functors and composition

For exact functors of abelian categories, an isomorphism `Ψ : p ⋙ e_X ≅ e_Y ⋙ d` induces an
isomorphism of the functors they induce on derived categories, through the composition comparisons
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`. This file shows that this
construction preserves compatibility with composition of the horizontal functors.

## Main results

* `Stacks.DerivedCategoryComparisons.mapDerivedCategorySquare_hom_app_Q`: the derived square at
  the image of a cochain complex.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_comp_isoOfNatIso_hom`: the
  derived comparison induced by `e : F ⋙ G ≅ H` is
  `CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso e`.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategorySquare_comp_coherence`: compatibility with
  composition passes to derived squares.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedCategoryComparisons

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {AX AY AZ EX EY EZ : Type*} [Category* AX] [Category* AY] [Category* AZ]
  [Category* EX] [Category* EY] [Category* EZ] [Abelian AX] [Abelian AY] [Abelian AZ]
  [Abelian EX] [Abelian EY] [Abelian EZ] [HasDerivedCategory AX] [HasDerivedCategory AY]
  [HasDerivedCategory AZ] [HasDerivedCategory EX] [HasDerivedCategory EY] [HasDerivedCategory EZ]

/-- The derived square `D(p) ⋙ D(e_X) ≅ D(e_Y) ⋙ D(d)` induced by an isomorphism
`Ψ : p ⋙ e_X ≅ e_Y ⋙ d` of exact functors, at the image of a cochain complex: the canonical
factorizations around the localization of the degreewise action of `Ψ`. -/
theorem mapDerivedCategorySquare_hom_app_Q (p : AY ⥤ AX) (eX : AX ⥤ EX) (eY : AY ⥤ EY) (d : EY ⥤ EX)
    [p.Additive] [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    [eX.Additive] [PreservesFiniteLimits eX] [PreservesFiniteColimits eX]
    [eY.Additive] [PreservesFiniteLimits eY] [PreservesFiniteColimits eY]
    [d.Additive] [PreservesFiniteLimits d] [PreservesFiniteColimits d]
    (Ψ : p ⋙ eX ≅ eY ⋙ d) (P : CochainComplex AY ℤ) :
    ((mapDerivedCategoryCompIso p eX).symm ≪≫ mapDerivedCategoryIsoOfNatIso _ _ Ψ ≪≫
        mapDerivedCategoryCompIso eY d).hom.app (DerivedCategory.Q.obj P) =
      eX.mapDerivedCategory.map (p.mapDerivedCategoryFactors.hom.app P) ≫
        eX.mapDerivedCategoryFactors.hom.app ((p.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex Ψ (ComplexShape.up ℤ)).hom.app P) ≫
        d.mapDerivedCategoryFactors.inv.app ((eY.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        d.mapDerivedCategory.map (eY.mapDerivedCategoryFactors.inv.app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, mapDerivedCategoryCompIso_inv_app_Q,
    mapDerivedCategoryIsoOfNatIso_hom_app_Q, mapDerivedCategoryCompIso_hom_app_Q, Category.assoc,
    Iso.inv_hom_id_app_assoc]


/-- The derived comparison `D(F) ⋙ D(G) ≅ D(H)` induced by `e : F ⋙ G ≅ H`, at the image of a
cochain complex: the canonical factorizations around the localization of the degreewise action of
`e`. -/
theorem mapDerivedCategoryCompIso_inv_comp_isoOfNatIso_hom_app_Q (F : AY ⥤ AX) (G : AX ⥤ EX)
    (H : AY ⥤ EX)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (P : CochainComplex AY ℤ) :
    ((mapDerivedCategoryCompIso F G).inv ≫ (mapDerivedCategoryIsoOfNatIso _ _ e).hom).app
        (DerivedCategory.Q.obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) ≫
        H.mapDerivedCategoryFactors.inv.app P := by
  simp only [NatTrans.comp_app, mapDerivedCategoryCompIso_inv_app_Q,
    mapDerivedCategoryIsoOfNatIso_hom_app_Q, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The derived comparison induced by `e : F ⋙ G ≅ H` through
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` is
`CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso e`. -/
theorem mapDerivedCategoryCompIso_inv_comp_isoOfNatIso_hom (F : AY ⥤ AX) (G : AX ⥤ EX)
    (H : AY ⥤ EX) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H) :
    (mapDerivedCategoryCompIso F G).inv ≫ (mapDerivedCategoryIsoOfNatIso _ _ e).hom =
      (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom :=
  Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso AY (ComplexShape.up ℤ)) fun _ => rfl

variable {pF : AY ⥤ AX} {pG : AZ ⥤ AY} {pFG : AZ ⥤ AX} {eX : AX ⥤ EX} {eY : AY ⥤ EY}
  {eZ : AZ ⥤ EZ} {dF : EY ⥤ EX} {dG : EZ ⥤ EY} {dFG : EZ ⥤ EX}
  [pF.Additive] [PreservesFiniteLimits pF] [PreservesFiniteColimits pF]
  [pG.Additive] [PreservesFiniteLimits pG] [PreservesFiniteColimits pG]
  [pFG.Additive] [PreservesFiniteLimits pFG] [PreservesFiniteColimits pFG]
  [eX.Additive] [PreservesFiniteLimits eX] [PreservesFiniteColimits eX]
  [eY.Additive] [PreservesFiniteLimits eY] [PreservesFiniteColimits eY]
  [eZ.Additive] [PreservesFiniteLimits eZ] [PreservesFiniteColimits eZ]
  [dF.Additive] [PreservesFiniteLimits dF] [PreservesFiniteColimits dF]
  [dG.Additive] [PreservesFiniteLimits dG] [PreservesFiniteColimits dG]
  [dFG.Additive] [PreservesFiniteLimits dFG] [PreservesFiniteColimits dFG]

/-- **Compatibility with composition passes to derived categories.** If isomorphisms
`Ψ_j : p_j ⋙ e_X ≅ e_Y ⋙ d_j` of exact functors, for `j = f, g, f ≫ g`, are compatible with
comparisons `PC : p_g ⋙ p_f ≅ p_{fg}` and `c_D : d_g ⋙ d_f ≅ d_{fg}`, then so are the induced
squares of functors on derived categories, with the induced comparisons. -/
theorem mapDerivedCategorySquare_comp_coherence (PC : pG ⋙ pF ≅ pFG) (cD : dG ⋙ dF ≅ dFG)
    (ΨF : pF ⋙ eX ≅ eY ⋙ dF) (ΨG : pG ⋙ eY ≅ eZ ⋙ dG) (ΨFG : pFG ⋙ eX ≅ eZ ⋙ dFG)
    (hΨ : ∀ M, eX.map (PC.hom.app M) ≫ ΨFG.hom.app M =
      ΨF.hom.app (pG.obj M) ≫ dF.map (ΨG.hom.app M) ≫ cD.hom.app (eZ.obj M))
    (K : DerivedCategory AZ) :
    eX.mapDerivedCategory.map (((mapDerivedCategoryCompIso pG pF).inv ≫
        (mapDerivedCategoryIsoOfNatIso _ _ PC).hom).app K) ≫
      ((mapDerivedCategoryCompIso pFG eX).symm ≪≫ mapDerivedCategoryIsoOfNatIso _ _ ΨFG ≪≫
        mapDerivedCategoryCompIso eZ dFG).hom.app K =
    ((mapDerivedCategoryCompIso pF eX).symm ≪≫ mapDerivedCategoryIsoOfNatIso _ _ ΨF ≪≫
        mapDerivedCategoryCompIso eY dF).hom.app (pG.mapDerivedCategory.obj K) ≫
      dF.mapDerivedCategory.map (((mapDerivedCategoryCompIso pG eY).symm ≪≫
        mapDerivedCategoryIsoOfNatIso _ _ ΨG ≪≫ mapDerivedCategoryCompIso eZ dG).hom.app K) ≫
      ((mapDerivedCategoryCompIso dG dF).inv ≫ (mapDerivedCategoryIsoOfNatIso _ _ cD).hom).app
        (eZ.mapDerivedCategory.obj K) := by
  set TF := (mapDerivedCategoryCompIso pF eX).symm ≪≫ mapDerivedCategoryIsoOfNatIso _ _ ΨF ≪≫
    mapDerivedCategoryCompIso eY dF with hTF
  set TG := (mapDerivedCategoryCompIso pG eY).symm ≪≫ mapDerivedCategoryIsoOfNatIso _ _ ΨG ≪≫
    mapDerivedCategoryCompIso eZ dG with hTG
  set TFG := (mapDerivedCategoryCompIso pFG eX).symm ≪≫ mapDerivedCategoryIsoOfNatIso _ _ ΨFG ≪≫
    mapDerivedCategoryCompIso eZ dFG with hTFG
  set cP := (mapDerivedCategoryCompIso pG pF).inv ≫ (mapDerivedCategoryIsoOfNatIso _ _ PC).hom
    with hcP
  set cE := (mapDerivedCategoryCompIso dG dF).inv ≫ (mapDerivedCategoryIsoOfNatIso _ _ cD).hom
    with hcE
  have key : Functor.whiskerRight cP eX.mapDerivedCategory ≫ TFG.hom =
      Functor.whiskerLeft pG.mapDerivedCategory TF.hom ≫
        Functor.whiskerRight TG.hom dF.mapDerivedCategory ≫
        Functor.whiskerLeft eZ.mapDerivedCategory cE := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso AZ (ComplexShape.up ℤ)) fun P => ?_
    have hC : (eX.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex PC (ComplexShape.up ℤ)).hom.app P) ≫
        (NatIso.mapHomologicalComplex ΨFG (ComplexShape.up ℤ)).hom.app P =
        (NatIso.mapHomologicalComplex ΨF (ComplexShape.up ℤ)).hom.app
            ((pG.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (dF.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatIso.mapHomologicalComplex ΨG (ComplexShape.up ℤ)).hom.app P) ≫
          (NatIso.mapHomologicalComplex cD (ComplexShape.up ℤ)).hom.app
            ((eZ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
      ext n
      simpa using hΨ (P.X n)
    have nF := TF.hom.naturality (pG.mapDerivedCategoryFactors.inv.app P)
    have nE := cE.naturality (eZ.mapDerivedCategoryFactors.inv.app P)
    have nX : eX.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex PC (ComplexShape.up ℤ)).hom.app P)) ≫
        eX.mapDerivedCategoryFactors.hom.app
          ((pFG.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        eX.mapDerivedCategoryFactors.hom.app ((pF.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((pG.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((eX.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex PC (ComplexShape.up ℤ)).hom.app P)) :=
      eX.mapDerivedCategoryFactors.hom.naturality _
    have nD : DerivedCategory.Q.map ((dF.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex ΨG (ComplexShape.up ℤ)).hom.app P)) ≫
        dF.mapDerivedCategoryFactors.inv.app ((dG.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((eZ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
        dF.mapDerivedCategoryFactors.inv.app ((eY.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((pG.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        dF.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ΨG (ComplexShape.up ℤ)).hom.app P)) :=
      dF.mapDerivedCategoryFactors.inv.naturality _
    have c3 : eX.mapDerivedCategory.map (pFG.mapDerivedCategoryFactors.inv.app P) ≫
        eX.mapDerivedCategory.map (pFG.mapDerivedCategoryFactors.hom.app P) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    have c4 : dF.mapDerivedCategory.map (eY.mapDerivedCategoryFactors.inv.app
          ((pG.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        dF.mapDerivedCategory.map (eY.mapDerivedCategoryFactors.hom.app
          ((pG.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    have c5 : dF.mapDerivedCategory.map (dG.mapDerivedCategoryFactors.inv.app
          ((eZ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        dF.mapDerivedCategory.map (dG.mapDerivedCategoryFactors.hom.app
          ((eZ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    simp only [Functor.comp_map, Functor.comp_obj] at nF nE
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    have nF' : TF.hom.app (pG.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) =
        eX.mapDerivedCategory.map (pF.mapDerivedCategory.map
          (pG.mapDerivedCategoryFactors.hom.app P)) ≫
        TF.hom.app (DerivedCategory.Q.obj ((pG.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        dF.mapDerivedCategory.map (eY.mapDerivedCategory.map
          (pG.mapDerivedCategoryFactors.inv.app P)) := by
      rw [← nF, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id_app,
        CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
    have nE' : cE.app (eZ.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) =
        dF.mapDerivedCategory.map (dG.mapDerivedCategory.map
          (eZ.mapDerivedCategoryFactors.hom.app P)) ≫
        cE.app (DerivedCategory.Q.obj ((eZ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        dFG.mapDerivedCategory.map (eZ.mapDerivedCategoryFactors.inv.app P) := by
      rw [← nE, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id_app,
        CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
    have c1 : dF.mapDerivedCategory.map (eY.mapDerivedCategory.map
          (pG.mapDerivedCategoryFactors.inv.app P)) ≫
        dF.mapDerivedCategory.map (eY.mapDerivedCategory.map
          (pG.mapDerivedCategoryFactors.hom.app P)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id]
    have c2 : dF.mapDerivedCategory.map (dG.mapDerivedCategory.map
          (eZ.mapDerivedCategoryFactors.inv.app P)) ≫
        dF.mapDerivedCategory.map (dG.mapDerivedCategory.map
          (eZ.mapDerivedCategoryFactors.hom.app P)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id]
    rw [nF', nE', hcP, mapDerivedCategoryCompIso_inv_comp_isoOfNatIso_hom_app_Q, hTFG,
      mapDerivedCategorySquare_hom_app_Q, hTF, mapDerivedCategorySquare_hom_app_Q, hTG,
      mapDerivedCategorySquare_hom_app_Q, hcE,
      mapDerivedCategoryCompIso_inv_comp_isoOfNatIso_hom_app_Q]
    simp only [Functor.map_comp, Category.assoc, reassoc_of% c1, reassoc_of% c2]
    rw [reassoc_of% c3, reassoc_of% c4, reassoc_of% c5, reassoc_of% nX, ← reassoc_of% nD,
      Iso.inv_hom_id_app_assoc, ← DerivedCategory.Q.map_comp_assoc, hC]
    simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun t => t.app K) key

end Stacks.DerivedCategoryComparisons
