module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalenceNatural

/-!
# The derived internal Hom transport along an equivalence of ringed sites, on K-injective models

Let `e : C ≌ D` be an equivalence of ringed sites as in
`AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso`. That comparison
`φ_* RSheafHom(K, L) ≅ RSheafHom(φ_* K, φ_* L)` is computed at a representative `N` of `K` and a
K-injective representative `I` of `L`. This file records it at an arbitrary such pair of
representatives and proves that it is natural in the second variable.

## Main definitions

* `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomModelIsoOfIso`: the comparison computed at
  a representative of `K` and a K-injective representative of `L`.

## Main results

* `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso_eq_modelIso`: the comparison of
  `siteEquivDerivedSheafHomIso` is the model comparison at its chosen representatives.
* `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso_natural_right` and
  `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIsoOfIso_natural_right`: the comparison
  is natural in the second variable.

## References

* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {X Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- The transport of an object of `D(O_X)` represented by a complex `A` is represented by the
transport of `A`. -/
def pushModelIso
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ K) :
    DerivedCategory.Q.obj ((pushComplex eqv φ).obj A) ≅
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K :=
  ((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app A).symm ≪≫
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso eA

/-- The comparison of `siteEquivDerivedSheafHomIso`, computed at a representative `N` of `K`
and a K-injective representative `I` of `L`. -/
def siteEquivDerivedSheafHomModelIsoOfIso
    {K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {N I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] (eN : DerivedCategory.Q.obj N ≅ K) (eI : DerivedCategory.Q.obj I ≅ L) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj
        (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).obj
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) :=
  haveI := pushComplex_isKInjective eqv φ ψ H₁ H₂ I
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso
      (derivedSheafHomObjectsModelIso X eN eI ≪≫ derivedSheafHomComparison X N I) ≪≫
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app
      (sheafHomComplex X N I).obj ≪≫
    DerivedCategory.Q.mapIso (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ N I) ≪≫
    (derivedSheafHomComparison Y ((pushComplex eqv φ).obj N)
      ((pushComplex eqv φ).obj I)).symm ≪≫
    (derivedSheafHomObjectsModelIso Y (pushModelIso eqv φ eN) (pushModelIso eqv φ eI)).symm

omit [eqv.inverse.IsContinuous X.J Y.J] in
/-- Through the comparisons `derivedSheafHomComparison` and `derivedSheafHomObjectsModelIso` on
`Y`, the internal Hom map induced by the transport of `b : I ⟶ I'` is the action of the transport
of `a : L ⟶ L'` on the derived internal Hom out of the transport of `K`. -/
theorem siteEquivDerivedSheafHomModelIso_natural_right_aux
    {K L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {N I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective] (eN : DerivedCategory.Q.obj N ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ L)
    (eI' : DerivedCategory.Q.obj I' ≅ L') (a : L ⟶ L') (b : I ⟶ I')
    (hb : DerivedCategory.Q.map b = eI.hom ≫ a ≫ eI'.inv)
    [((pushComplex eqv φ).obj I).IsKInjective] [((pushComplex eqv φ).obj I').IsKInjective] :
    DerivedCategory.Q.map (homMap Y (𝟙 _) ((pushComplex eqv φ).map b)) ≫
      (derivedSheafHomComparison Y ((pushComplex eqv φ).obj N)
        ((pushComplex eqv φ).obj I')).inv ≫
      (derivedSheafHomObjectsModelIso Y (pushModelIso eqv φ eN)
        (pushModelIso eqv φ eI')).inv =
      (derivedSheafHomComparison Y ((pushComplex eqv φ).obj N)
        ((pushComplex eqv φ).obj I)).inv ≫
      (derivedSheafHomObjectsModelIso Y (pushModelIso eqv φ eN) (pushModelIso eqv φ eI)).inv ≫
        ((derivedSheafHomBifunctor Y).obj
          (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).map
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map a) := by
  have hC : DerivedCategory.Q.map (homMap Y (𝟙 _) ((pushComplex eqv φ).map b)) ≫
      (derivedSheafHomComparison Y ((pushComplex eqv φ).obj N)
        ((pushComplex eqv φ).obj I')).inv =
      (derivedSheafHomComparison Y ((pushComplex eqv φ).obj N)
        ((pushComplex eqv φ).obj I)).inv ≫
      ((derivedSheafHomBifunctor Y).obj
        (op (DerivedCategory.Q.obj ((pushComplex eqv φ).obj N)))).map
          (DerivedCategory.Q.map ((pushComplex eqv φ).map b)) := by
    rw [Iso.comp_inv_eq, Category.assoc, derivedSheafHomComparison_naturality_id_source,
      Iso.inv_hom_id_assoc]
  have hpb : DerivedCategory.Q.map ((pushComplex eqv φ).map b) ≫ (pushModelIso eqv φ eI').hom =
      (pushModelIso eqv φ eI).hom ≫
        (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map a := by
    have h5 := (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors_hom_naturality b
    have h5' : DerivedCategory.Q.map ((pushComplex eqv φ).map b) =
        ((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app I).inv ≫
          (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map (DerivedCategory.Q.map b) ≫
            ((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app I').hom :=
      (Iso.eq_inv_comp _).2 h5.symm
    dsimp only [pushModelIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [h5']
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, hb]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hC]
  congr 1
  dsimp only [derivedSheafHomObjectsModelIso, Iso.trans_inv, Iso.app_inv,
    Functor.mapIso_inv, Iso.symm_inv]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hpb, Functor.map_comp_assoc]
  exact whisker_eq _ (((derivedSheafHomBifunctor Y).map (pushModelIso eqv φ eN).op.inv).naturality
    ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map a))

/-- **The model comparison is natural in the second variable**, along a morphism of K-injective
representatives. -/
theorem siteEquivDerivedSheafHomModelIso_natural_right
    {K L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {N I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective] (eN : DerivedCategory.Q.obj N ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ L)
    (eI' : DerivedCategory.Q.obj I' ≅ L') (a : L ⟶ L') (b : I ⟶ I')
    (hb : DerivedCategory.Q.map b = eI.hom ≫ a ≫ eI'.inv) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).obj (op K)).map a) ≫
        (siteEquivDerivedSheafHomModelIsoOfIso eqv φ ψ H₁ H₂ eN eI').hom =
      (siteEquivDerivedSheafHomModelIsoOfIso eqv φ ψ H₁ H₂ eN eI).hom ≫
        ((derivedSheafHomBifunctor Y).obj
          (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).map
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map a) := by
  have := pushComplex_isKInjective eqv φ ψ H₁ H₂ I
  have := pushComplex_isKInjective eqv φ ψ H₁ H₂ I'
  have hb' : eI.inv ≫ DerivedCategory.Q.map b = a ≫ eI'.inv := by
    rw [hb, Iso.inv_hom_id_assoc]
  have hA : ((derivedSheafHomBifunctor X).obj (op K)).map a ≫
      (derivedSheafHomObjectsModelIso X eN eI').hom ≫ (derivedSheafHomComparison X N I').hom =
      (derivedSheafHomObjectsModelIso X eN eI).hom ≫ (derivedSheafHomComparison X N I).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 N) b) := by
    have h1 := ((derivedSheafHomBifunctor X).map eN.op.hom).naturality a
    dsimp only [derivedSheafHomObjectsModelIso, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Iso.symm_hom]
    simp only [Category.assoc]
    rw [reassoc_of% h1, ← Functor.map_comp_assoc, ← hb', Functor.map_comp_assoc,
      derivedSheafHomComparison_naturality_id_source]
  have hB : (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (DerivedCategory.Q.map (homMap X (𝟙 N) b)) ≫
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.hom.app
        (sheafHomComplex X N I').obj ≫
      DerivedCategory.Q.map (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ N I').hom =
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.hom.app
        (sheafHomComplex X N I).obj ≫
      DerivedCategory.Q.map (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ N I).hom ≫
      DerivedCategory.Q.map (homMap Y (𝟙 _) ((pushComplex eqv φ).map b)) := by
    have h3 := siteEquivSheafHomComplexIso_natural eqv φ ψ H₁ H₂ (𝟙 N) b
    rw [CategoryTheory.Functor.map_id] at h3
    rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc, ← Functor.map_comp, h3,
      Functor.map_comp]
  have hC := siteEquivDerivedSheafHomModelIso_natural_right_aux eqv φ eN eI eI' a b hb
  dsimp only [siteEquivDerivedSheafHomModelIsoOfIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hA]
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom]
  rw [reassoc_of% hB]
  exact whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ hC)))

/-- The comparison of `siteEquivDerivedSheafHomIso` is the model comparison at the chosen
representative of `K` and the chosen K-injective representative of `L`. -/
theorem siteEquivDerivedSheafHomIso_eq_modelIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    siteEquivDerivedSheafHomIso eqv φ ψ H₁ H₂ K L =
      siteEquivDerivedSheafHomModelIsoOfIso eqv φ ψ H₁ H₂ (DerivedCategory.Q.objObjPreimageIso K)
        (kInjectiveModelIso X L) :=
  rfl

/-- **The derived internal Hom transport is natural in the second variable.** -/
theorem siteEquivDerivedSheafHomIso_natural_right
    {K L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : L ⟶ L') :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).obj (op K)).map a) ≫
        (siteEquivDerivedSheafHomIso eqv φ ψ H₁ H₂ K L').hom =
      (siteEquivDerivedSheafHomIso eqv φ ψ H₁ H₂ K L).hom ≫
        ((derivedSheafHomBifunctor Y).obj
          (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).map
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map a) := by
  obtain ⟨b, hb⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X L).hom ≫ a ≫ (kInjectiveModelIso X L').inv)
  rw [siteEquivDerivedSheafHomIso_eq_modelIso, siteEquivDerivedSheafHomIso_eq_modelIso]
  exact siteEquivDerivedSheafHomModelIso_natural_right eqv φ ψ H₁ H₂ _ _ _ a b hb

end Derived

section OfIso

attribute [local instance] HasDerivedCategory.standard

variable [hφ : IsIso φ]

variable [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- `siteEquivDerivedSheafHomIsoOfIso` is natural in the second variable. -/
theorem siteEquivDerivedSheafHomIsoOfIso_natural_right
    {K L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : L ⟶ L') :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).obj (op K)).map a) ≫
        (siteEquivDerivedSheafHomIsoOfIso eqv φ K L').hom =
      (siteEquivDerivedSheafHomIsoOfIso eqv φ K L).hom ≫
        ((derivedSheafHomBifunctor Y).obj
          (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).map
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map a) :=
  siteEquivDerivedSheafHomIso_natural_right eqv φ _ _ _ a

end OfIso

end AlgebraicGeometry.RingedSite

end
