module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusCompositionCompatibility

/-!
# The degreewise action on derived categories is functorial in the exact functor

An exact additive functor `T : 𝒜 ⥤ ℬ` of abelian categories with derived categories acts
degreewise on the unbounded derived category by `CategoryTheory.Functor.mapDerivedCategory`, and
on the bounded below one by `CategoryTheory.Functor.mapDerivedCategoryPlus`. This file makes
both actions functorial in `T`: a transformation `τ : T ⟶ S` of exact functors induces
transformations of the two actions, computed on the image of the localization by applying `τ`
degreewise, and the comparison of the degreewise action with homology is natural in `T`.

## Main definitions

* `Stacks.DerivedFunctor.mapDerivedNatTrans`: the transformation `T.mapDerivedCategory ⟶
  S.mapDerivedCategory` induced by `τ : T ⟶ S`.
* `Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans`: its restriction to bounded below
  derived categories.

## Main results

* `Stacks.DerivedFunctor.mapDerivedNatTrans_factors_app`,
  `Stacks.DerivedFunctor.mapDerivedNatTrans_homotopy_fac_app` and
  `Stacks.DerivedFunctor.mapDerivedNatTrans_homotopy_fac`: the induced transformation is `τ`
  applied degreewise, read through the factorizations of the two actions through the category of
  complexes, respectively through the homotopy category.
* `Stacks.DerivedFunctor.derivedHomologyIso_naturality` and
  `Stacks.DerivedFunctor.derivedHomologyIso_hom_app_Qh_naturality`: **the comparison of the
  degreewise action with homology is natural in the exact functor**, as a transformation and
  then written out on the image of the localization of the homotopy category.
* `Stacks.DerivedFunctor.ι_map_mapDerivedCategoryPlusNatTrans_app`: the inclusion of the
  bounded below subcategory carries the bounded below transformation to the unbounded one.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.DerivedFunctor

section Complexes

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] {T S : A ⥤ B} [T.Additive] [S.Additive]
  [T.PreservesHomology] [S.PreservesHomology]

/-- **The homology comparison on complexes is natural in the functor.** -/
theorem complexHomologyIso_naturality (τ : T ⟶ S) {ι : Type*} (c : ComplexShape ι) (i : ι)
    (K : HomologicalComplex A c) :
    (HomologicalComplex.homologyFunctor B c i).map ((τ.mapHomologicalComplex c).app K) ≫
        (complexHomologyIso S c i).hom.app K =
      (complexHomologyIso T c i).hom.app K ≫
        τ.app ((HomologicalComplex.homologyFunctor A c i).obj K) := by
  rw [complexHomologyIso_hom_app, complexHomologyIso_hom_app]
  change ShortComplex.homologyMap ((K.sc i).mapNatTrans τ) ≫
    ((K.sc i).mapHomologyIso S).hom = ((K.sc i).mapHomologyIso T).hom ≫ _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end Complexes

section HomotopyCategory

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Preadditive A] [Preadditive B] {T S : A ⥤ B} [T.Additive] [S.Additive]

/-- A transformation of additive functors is compatible with the identifications of the functors
it induces on homotopy categories with the functors it induces on complexes. -/
theorem mapHomotopyCategoryFactors_inv_app_naturality (τ : T ⟶ S) {ι : Type*}
    (c : ComplexShape ι) (K : HomologicalComplex A c) :
    (HomotopyCategory.quotient B c).map ((τ.mapHomologicalComplex c).app K) ≫
        (S.mapHomotopyCategoryFactors c).inv.app K =
      (T.mapHomotopyCategoryFactors c).inv.app K ≫
        (τ.mapHomotopyCategory c).app ((HomotopyCategory.quotient A c).obj K) :=
  (Category.comp_id _).trans (Category.id_comp _).symm

end HomotopyCategory

section Unbounded

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  {T S : A ⥤ B} [T.Additive] [S.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- **The transformation of the degreewise actions on unbounded derived categories induced by a
transformation of exact functors**, obtained from the universal property of the localization. -/
def mapDerivedNatTrans (τ : T ⟶ S) : T.mapDerivedCategory ⟶ S.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (S.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    T.mapDerivedCategory S.mapDerivedCategory
    (Functor.whiskerRight (τ.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- `mapDerivedNatTrans` is `τ` applied degreewise, read through the factorizations of the two
actions through the category of complexes. -/
theorem mapDerivedNatTrans_factors_app (τ : T ⟶ S) (K : CochainComplex A ℤ) :
    (mapDerivedNatTrans τ).app (DerivedCategory.Q.obj K) ≫
        S.mapDerivedCategoryFactors.hom.app K =
      T.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app K) := by
  simp only [mapDerivedNatTrans, Localization.liftNatTrans_app, Functor.whiskerRight_app]
  dsimp only [Localization.Lifting.iso]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- `mapDerivedNatTrans` is `τ` applied degreewise, read through the factorizations of the two
actions through the homotopy category. -/
theorem mapDerivedNatTrans_homotopy_fac_app (τ : T ⟶ S) (K : CochainComplex A ℤ) :
    (mapDerivedNatTrans τ).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        S.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      T.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((τ.mapHomotopyCategory (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
  rw [S.mapDerivedCategoryFactorsh_hom_app,
    reassoc_of% T.mapDerivedCategoryFactorsh_hom_app,
    ← reassoc_of% (mapDerivedNatTrans τ).naturality
      ((DerivedCategory.quotientCompQhIso A).hom.app K),
    reassoc_of% mapDerivedNatTrans_factors_app τ K,
    DerivedCategory.quotientCompQhIso_inv_naturality_assoc,
    ← Functor.map_comp, ← Functor.map_comp,
    mapHomotopyCategoryFactors_inv_app_naturality τ (ComplexShape.up ℤ) K]

/-- **`mapDerivedNatTrans` descends the transformation induced on homotopy categories.** -/
theorem mapDerivedNatTrans_homotopy_fac (τ : T ⟶ S) :
    Functor.whiskerLeft DerivedCategory.Qh (mapDerivedNatTrans τ) ≫
        S.mapDerivedCategoryFactorsh.hom =
      T.mapDerivedCategoryFactorsh.hom ≫
        Functor.whiskerRight (τ.mapHomotopyCategory (ComplexShape.up ℤ))
          DerivedCategory.Qh := by
  ext X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  exact mapDerivedNatTrans_homotopy_fac_app τ K

/-- `mapDerivedNatTrans_homotopy_fac_app` on an arbitrary object of the homotopy category. -/
theorem mapDerivedNatTrans_factorsh_app (τ : T ⟶ S)
    (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapDerivedNatTrans τ).app (DerivedCategory.Qh.obj M) ≫
        S.mapDerivedCategoryFactorsh.hom.app M =
      T.mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map ((τ.mapHomotopyCategory (ComplexShape.up ℤ)).app M) := by
  exact congr_app (mapDerivedNatTrans_homotopy_fac τ) M

/-- `mapDerivedNatTrans_factorsh_app` solved for the inverse factorizations. -/
theorem Qh_map_comp_mapDerivedCategoryFactorsh_inv_app (τ : T ⟶ S)
    (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map ((τ.mapHomotopyCategory (ComplexShape.up ℤ)).app M) ≫
        S.mapDerivedCategoryFactorsh.inv.app M =
      T.mapDerivedCategoryFactorsh.inv.app M ≫
        (mapDerivedNatTrans τ).app (DerivedCategory.Qh.obj M) := by
  rw [← cancel_mono (S.mapDerivedCategoryFactorsh.hom.app M), Category.assoc, Category.assoc,
    mapDerivedNatTrans_factorsh_app]
  simp

/-- **The comparison of the degreewise action with homology is natural in the exact functor.** -/
theorem derivedHomologyIso_naturality (τ : T ⟶ S) (i : ℤ) :
    Functor.whiskerRight (mapDerivedNatTrans τ) (DerivedCategory.homologyFunctor B i) ≫
        (derivedHomologyIso S i).hom =
      (derivedHomologyIso T i).hom ≫
        Functor.whiskerLeft (DerivedCategory.homologyFunctor A i) τ := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    mapDerivedNatTrans, derivedHomologyIso, Localization.liftNatTrans_app,
    Localization.liftNatIso_hom]
  dsimp only [Localization.Lifting.iso, Iso.trans, Iso.symm, Iso.app,
    Functor.isoWhiskerRight, Functor.isoWhiskerLeft, Functor.associator, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.mapIso,
    Functor.whiskeringLeft, Functor.whiskeringRight]
  simp only [Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Category.comp_id, Functor.map_comp, Category.assoc]
  have hn := (DerivedCategory.homologyFunctorFactors B i).hom.naturality
    ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app K)
  change (DerivedCategory.homologyFunctor B i).map
      (DerivedCategory.Q.map ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app K)) ≫ _ =
    _ ≫ (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) i).map
      ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app K) at hn
  rw [reassoc_of% hn,
    reassoc_of% complexHomologyIso_naturality τ (ComplexShape.up ℤ) i K]
  congr 3
  exact (τ.naturality ((DerivedCategory.homologyFunctorFactors A i).inv.app K)).symm

/-- **The naturality of the homology comparison in the exact functor, on the image of the
localization of the homotopy category**, with the induced transformation written out
degreewise. -/
theorem derivedHomologyIso_hom_app_Qh_naturality (τ : T ⟶ S) (i : ℤ)
    (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    (DerivedCategory.homologyFunctor B i).map
          (T.mapDerivedCategoryFactorsh.hom.app M ≫
            DerivedCategory.Qh.map ((τ.mapHomotopyCategory (ComplexShape.up ℤ)).app M) ≫
              S.mapDerivedCategoryFactorsh.inv.app M) ≫
        (derivedHomologyIso S i).hom.app (DerivedCategory.Qh.obj M) =
      (derivedHomologyIso T i).hom.app (DerivedCategory.Qh.obj M) ≫
        τ.app ((DerivedCategory.homologyFunctor A i).obj (DerivedCategory.Qh.obj M)) := by
  rw [Qh_map_comp_mapDerivedCategoryFactorsh_inv_app, Iso.hom_inv_id_app_assoc]
  exact congr_app (derivedHomologyIso_naturality τ i) _

end Unbounded

section Plus

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  {T S : A ⥤ B} [T.Additive] [S.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- **The transformation of the degreewise actions on bounded below derived categories induced
by a transformation of exact functors**: the unbounded one, which preserves boundedness
below. -/
def mapDerivedCategoryPlusNatTrans (τ : T ⟶ S) :
    T.mapDerivedCategoryPlus ⟶ S.mapDerivedCategoryPlus where
  app K := ObjectProperty.homMk ((mapDerivedNatTrans τ).app K.obj)
  naturality _ _ f := by
    ext
    exact (mapDerivedNatTrans τ).naturality f.hom

/-- The inclusion of the bounded below subcategory carries the bounded below transformation to
the unbounded one. -/
theorem ι_map_mapDerivedCategoryPlusNatTrans_app (τ : T ⟶ S) (K : DerivedCategory.Plus A) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusNatTrans τ).app K) =
      (mapDerivedNatTrans τ).app (DerivedCategory.Plus.ι.obj K) := rfl

end Plus

end Stacks.DerivedFunctor

end
