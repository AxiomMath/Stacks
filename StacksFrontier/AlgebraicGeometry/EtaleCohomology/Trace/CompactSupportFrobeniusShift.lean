module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonCoherence
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-!
# The geometric Frobenius on `RΓ_c(X_k̄, -)` commutes with the shift

Let `k` be a finite field, `X` a scheme over `k` with a compactification `j : X ⟶ X̄` and `k̄` an
extension of `k`. The functor `K ↦ RΓ_c(X_k̄, K)` on bounded below complexes
(`Stacks.EtaleCohomology.compactSupportFrobeniusFunctor`) is a composite of functors commuting with
the shift: extension by zero and restriction to `X̄_k̄` applied degreewise, the localization, and
the derived direct image and global sections. The canonical geometric Frobenius `π_X^*`
(`Stacks.EtaleCohomology.canonicalCompactSupportFrobeniusNatTrans`) is a composite of
transformations commuting with the shift: the degreewise base change twist, the derived-functor
unit and the composition comparison of derived direct images. Hence `π_X^*` commutes with the
shift (`Stacks.EtaleCohomology.natTransCommShift_canonicalCompactSupportFrobeniusNatTrans`).

On cohomology this gives, for a sheaf `M` placed in degree `q`,
`Hⁱ(RΓ_c(X_k̄, M[-q])) ≅ H^{i-q}_c(X_k̄, M)`, natural in `M` and compatible with `π_X^*`
(`Stacks.EtaleCohomology.compactSupportSingleHomologyIso`).

## Main definitions

* `Stacks.EtaleCohomology.compactSupportSingleHomologyIso`: the natural isomorphism
  `Hⁱ(RΓ_c(X_k̄, M[-d])) ≅ H^{i'}_c(X_k̄, M)` for `-d + i = i'`.

## Main results

* `Stacks.EtaleCohomology.natTransCommShift_canonicalCompactSupportFrobeniusNatTrans`: the
  geometric Frobenius `π_X^*` on `RΓ_c(X_k̄, -)` commutes with the shift.
* `Stacks.EtaleCohomology.compactSupportSingleHomologyIso_hom_frobenius`: the isomorphism
  `compactSupportSingleHomologyIso` commutes with `π_X^*`.

## Implementation notes

`compactSupportFrobeniusFunctor` lives in the standard model `HasDerivedCategory.standard` of the
derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- The natural transformation of functors on bounded below complexes induced degreewise by a
natural transformation of additive functors. -/
def mapCochainComplexPlusNatTrans {F G : A ⥤ B} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    F.mapCochainComplexPlus ⟶ G.mapCochainComplexPlus where
  app K := ObjectProperty.homMk ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K.obj)
  naturality _ _ φ := ObjectProperty.hom_ext _
    ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).naturality φ.hom)

/-- The transformation induced degreewise on bounded below complexes commutes with the shift. -/
instance commShift_mapCochainComplexPlusNatTrans {F G : A ⥤ B} [F.Additive] [G.Additive]
    (τ : F ⟶ G) : NatTrans.CommShift (mapCochainComplexPlusNatTrans τ) ℤ := by
  refine NatTrans.commShift_of_whiskerRight _ (CochainComplex.Plus.ι B) ?_
  let eF : F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ≅
      CochainComplex.Plus.ι A ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  let eG : G.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ≅
      CochainComplex.Plus.ι A ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  have : NatTrans.CommShift eF.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eG.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  refine NatTrans.commShift_of_eq_conj eF eG
    (Functor.whiskerLeft (CochainComplex.Plus.ι A)
      (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))) ?_
  ext K
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- A composite of `x` with identities and the image of an identity is `x`. -/
private theorem comp_map_id_chain {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D) {a : D}
    {b : C} (x : a ⟶ H.obj b) :
    ((((x ≫ 𝟙 _) ≫ H.map (𝟙 b)) ≫ 𝟙 _) ≫ 𝟙 _) ≫ 𝟙 _ = x := by
  simp

/-- The natural transformation `F⁺ ⟶ G⁺ ⋙ H⁺` of functors on bounded below complexes induced
degreewise by a natural transformation `F ⟶ G ⋙ H` of additive functors. -/
def mapCochainComplexPlusNatTransComp {E : Type*} [Category* E] [Abelian E] {F : A ⥤ E}
    {G : A ⥤ B} {H : B ⥤ E} [F.Additive] [G.Additive] [H.Additive] (τ : F ⟶ G ⋙ H) :
    F.mapCochainComplexPlus ⟶ G.mapCochainComplexPlus ⋙ H.mapCochainComplexPlus where
  app K := ObjectProperty.homMk ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K.obj)
  naturality _ _ φ := ObjectProperty.hom_ext _
    ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).naturality φ.hom)

/-- **The transformation `F⁺ ⟶ G⁺ ⋙ H⁺` induced degreewise commutes with the shift.** -/
instance commShift_mapCochainComplexPlusNatTransComp {E : Type*} [Category* E] [Abelian E]
    {F : A ⥤ E} {G : A ⥤ B} {H : B ⥤ E} [F.Additive] [G.Additive] [H.Additive]
    (τ : F ⟶ G ⋙ H) : NatTrans.CommShift (mapCochainComplexPlusNatTransComp τ) ℤ := by
  refine NatTrans.commShift_of_whiskerRight _ (CochainComplex.Plus.ι E) ?_
  let eF : F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι E ≅
      CochainComplex.Plus.ι A ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  let eG : G.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ≅
      CochainComplex.Plus.ι A ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  let eH : H.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι E ≅
      CochainComplex.Plus.ι B ⋙ H.mapHomologicalComplex (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  have : NatTrans.CommShift eF.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eG.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eH.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  let eGH : (G.mapCochainComplexPlus ⋙ H.mapCochainComplexPlus) ⋙ CochainComplex.Plus.ι E ≅
      CochainComplex.Plus.ι A ⋙ (G ⋙ H).mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G.mapCochainComplexPlus eH ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eG (H.mapHomologicalComplex (ComplexShape.up ℤ)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (CochainComplex.Plus.ι A)
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (ComplexShape.up ℤ))
  have : NatTrans.CommShift eGH.hom ℤ := by
    dsimp only [eGH, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  refine NatTrans.commShift_of_eq_conj eF eGH
    (Functor.whiskerLeft (CochainComplex.Plus.ι A)
      (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))) ?_
  refine NatTrans.ext (funext fun K => ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app]
  have h₁ : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (ComplexShape.up ℤ)).inv.app
      K.obj = 𝟙 _ := by
    ext n
    simp
  have h₂ : eF.hom.app K = 𝟙 _ := rfl
  have h₃ : eGH.inv.app K =
      (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (ComplexShape.up ℤ)).inv.app
        K.obj := by
    simp only [eGH, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    have hx : eG.inv.app K = 𝟙 _ := rfl
    have hy : eH.inv.app (G.mapCochainComplexPlus.obj K) = 𝟙 _ := rfl
    rw [hx, hy]
    exact comp_map_id_chain (H.mapHomologicalComplex (ComplexShape.up ℤ)) _
  rw [h₂, h₃, h₁]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit

section CommShift

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]

/-- The transport `R(G ∘ F) ≅ RH` along an isomorphism `F ⋙ G ≅ H` commutes with the shift. -/
instance natTransCommShift_rightDerivedFunctorPlusIsoOfCompIso (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (rightDerivedFunctorPlusIsoOfCompIso F G H e).hom ℤ := by
  have h₁ : NatTrans.CommShift (mapHomotopyCategoryPlusIsoOfCompIso F G H e).hom ℤ := by
    dsimp only [mapHomotopyCategoryPlusIsoOfCompIso, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have h₂ : NatTrans.CommShift (Functor.isoWhiskerRight
      (mapHomotopyCategoryPlusIsoOfCompIso F G H e) DerivedCategory.Plus.Qh).hom ℤ :=
    NatTrans.CommShift.whiskerRight _ _ ℤ
  have h₃ : NatTrans.CommShift ((Functor.isoWhiskerRight
      (mapHomotopyCategoryPlusIsoOfCompIso F G H e) DerivedCategory.Plus.Qh).hom ≫
        H.rightDerivedFunctorPlusUnith) ℤ := NatTrans.CommShift.comp _ _ ℤ
  exact Stacks.Triangulated.natTransCommShift_rightDerivedDesc _ _
    (HomotopyCategory.Plus.quasiIso C) ℤ _ _

/-- The comparison `RH ≅ RF ⋙ RG` attached to `F ⋙ G ≅ H` commutes with the shift. -/
instance natTransCommShift_rightDerivedFunctorPlusCompIsoOfIso [F.PreservesInjectiveObjects]
    (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (rightDerivedFunctorPlusCompIsoOfIso F G H e).hom ℤ := by
  have := CategoryTheory.Functor.natTransCommShift_rightDerivedFunctorPlusComp F G
  dsimp only [rightDerivedFunctorPlusCompIsoOfIso, Iso.trans_hom, Iso.symm_hom,
    Functor.rightDerivedFunctorPlusCompIso_hom]
  infer_instance

end CommShift

section HomologyShift

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- `Hᵃ(Y[n]) ≅ H^{a'}(Y)` for `n + a = a'`, on the bounded below derived category. -/
def plusHomologyShiftIso (Y : DerivedCategory.Plus C) (n a a' : ℤ) (h : n + a = a') :
    (DerivedCategory.Plus.homologyFunctor C a).obj (Y⟦n⟧) ≅
      (DerivedCategory.Plus.homologyFunctor C a').obj Y :=
  ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso n a a' h).app Y

/-- The isomorphism `Hᵃ(Y[n]) ≅ H^{a'}(Y)` is natural in `Y`. -/
@[reassoc]
theorem plusHomologyShiftIso_hom_naturality {Y Y' : DerivedCategory.Plus C} (φ : Y ⟶ Y')
    (n a a' : ℤ) (h : n + a = a') :
    (DerivedCategory.Plus.homologyFunctor C a).map (φ⟦n⟧') ≫
        (plusHomologyShiftIso Y' n a a' h).hom =
      (plusHomologyShiftIso Y n a a' h).hom ≫ (DerivedCategory.Plus.homologyFunctor C a').map φ :=
  (DerivedCategory.Plus.homologyFunctor C 0).shiftIso_hom_naturality n a a' h φ

/-- If `u = v ≫ w⟦n⟧`, then `Hᵃ(u)` followed by `Hᵃ(Y'[n]) ≅ H^{a'}(Y')` equals `Hᵃ(v)` followed
by `Hᵃ(Y[n]) ≅ H^{a'}(Y)` and `H^{a'}(w)`. -/
theorem plusHomologyShiftIso_square {n : ℤ} {A₀ Y Y' : DerivedCategory.Plus C} (u : A₀ ⟶ Y'⟦n⟧)
    (v : A₀ ⟶ Y⟦n⟧) (w : Y ⟶ Y') (a a' : ℤ) (h : n + a = a') (key : u = v ≫ w⟦n⟧') :
    (DerivedCategory.Plus.homologyFunctor C a).map u ≫ (plusHomologyShiftIso Y' n a a' h).hom =
      (DerivedCategory.Plus.homologyFunctor C a).map v ≫ (plusHomologyShiftIso Y n a a' h).hom ≫
        (DerivedCategory.Plus.homologyFunctor C a').map w := by
  rw [key, Functor.map_comp, Category.assoc, plusHomologyShiftIso_hom_naturality]

end HomologyShift

section CompactSupport

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- `RΓ_c(X_k̄, -)` commutes with the shift. -/
instance commShift_compactSupportFrobeniusFunctor :
    (compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).CommShift ℤ := by
  dsimp only [compactSupportFrobeniusFunctor, fieldBaseChangeRestrictionFunctor]
  infer_instance

/-- For an additive functor `T`, the canonical transformation `Q ∘ T⁺ ⟶ RT ∘ Q` on bounded below
complexes commutes with the shift. -/
instance natTransCommShift_mapCochainComplexPlusDerivedUnit_local {A B : Type*} [Category* A]
    [Category* B] [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [EnoughInjectives A] (T : A ⥤ B) [T.Additive] :
    NatTrans.CommShift (Functor.mapCochainComplexPlusDerivedUnit T) ℤ :=
  Stacks.DerivedIndexing.natTransCommShift_mapCochainComplexPlusDerivedUnit T

/-- The canonical morphism `C|_{Y_k̄} ⟶ Rπ̄_*(C|_{Y_k̄})`, as a natural transformation. -/
def frobeniusRestrictionDerivedNatTrans (Y : Over (Spec (.of k))) :
    fieldBaseChangeRestrictionFunctor.{u, r} Λ Y kbar ⟶
      fieldBaseChangeRestrictionFunctor.{u, r} Λ Y kbar ⋙
        etaleModuleDerivedDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard) :=
  Functor.whiskerRight
      (Functor.mapCochainComplexPlusNatTransComp
        (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard))
      DerivedCategory.Plus.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus
      (Functor.mapCochainComplexPlusDerivedUnit
        (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))) ≫
    (Functor.associator _ _ _).inv

/-- The component of `frobeniusRestrictionDerivedNatTrans` at `C` is
`frobeniusRestrictionDerivedMap` at `C`. -/
theorem frobeniusRestrictionDerivedNatTrans_app (Y : Over (Spec (.of k)))
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (frobeniusRestrictionDerivedNatTrans.{u, r} Λ kbar p q hcard Y).app C =
      frobeniusRestrictionDerivedMap.{u, r} Λ Y kbar p q hcard C := by
  simp [frobeniusRestrictionDerivedNatTrans, frobeniusRestrictionDerivedMap,
    Functor.mapCochainComplexPlusNatTransComp]

/-- The canonical morphism `C|_{Y_k̄} ⟶ Rπ̄_*(C|_{Y_k̄})` commutes with the shift. -/
instance natTransCommShift_frobeniusRestrictionDerivedNatTrans (Y : Over (Spec (.of k))) :
    NatTrans.CommShift (frobeniusRestrictionDerivedNatTrans.{u, r} Λ kbar p q hcard Y) ℤ := by
  dsimp only [frobeniusRestrictionDerivedNatTrans]
  infer_instance

/-- The geometric Frobenius `π_X^*`, written as a composite of natural transformations each
commuting with the shift. -/
def canonicalCompactSupportFrobeniusNatTrans' :
    (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus ⋙
        fieldBaseChangeRestrictionFunctor.{u, r} Λ (Over.mk j.toBase) kbar ⋙
        etaleModuleDerivedDirectImage.{u, r} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) ⋙
        etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar)) ⟶
      (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus ⋙
        fieldBaseChangeRestrictionFunctor.{u, r} Λ (Over.mk j.toBase) kbar ⋙
        etaleModuleDerivedDirectImage.{u, r} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) ⋙
        etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar)) :=
  Functor.whiskerLeft (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (Functor.whiskerRight (frobeniusRestrictionDerivedNatTrans.{u, r} Λ kbar p q hcard
            (Over.mk j.toBase))
            (etaleModuleDerivedDirectImage.{u, r} Λ
              (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (fieldBaseChangeRestrictionFunctor.{u, r} Λ (Over.mk j.toBase) kbar)
            (etaleModuleDerivedDirectImageEndomorphismComp.{u, r} Λ
              (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
              (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
              (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard)).inv)
        (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))) ≫
      (Functor.associator _ _ _).hom)

/-- `canonicalCompactSupportFrobeniusNatTrans` equals the composite
`canonicalCompactSupportFrobeniusNatTrans'`. -/
theorem canonicalCompactSupportFrobeniusNatTrans_eq :
    canonicalCompactSupportFrobeniusNatTrans.{u, r} Λ f j kbar p q hcard =
      canonicalCompactSupportFrobeniusNatTrans'.{u, r} Λ f j kbar p q hcard := by
  ext K
  simp only [canonicalCompactSupportFrobeniusNatTrans_app,
    canonicalCompactSupportFrobeniusNatTrans', canonicalCompactSupportFrobenius,
    frobeniusRestrictionCohomologyEndo, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.map_comp,
    frobeniusRestrictionDerivedNatTrans_app]
  rfl

/-- **The geometric Frobenius `π_X^*` on `RΓ_c(X_k̄, -)` commutes with the shift.** -/
instance natTransCommShift_canonicalCompactSupportFrobeniusNatTrans :
    NatTrans.CommShift
      (canonicalCompactSupportFrobeniusNatTrans.{u, r} Λ f j kbar p q hcard) ℤ := by
  have : NatTrans.CommShift (etaleModuleDerivedDirectImageEndomorphismComp.{u, r} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard)).hom ℤ := by
    dsimp only [etaleModuleDerivedDirectImageEndomorphismComp, etaleModuleDerivedDirectImageComp]
    exact natTransCommShift_rightDerivedFunctorPlusCompIsoOfIso _ _ _ _
  have h : NatTrans.CommShift
      (canonicalCompactSupportFrobeniusNatTrans'.{u, r} Λ f j kbar p q hcard) ℤ := by
    unfold canonicalCompactSupportFrobeniusNatTrans'
    infer_instance
  rwa [canonicalCompactSupportFrobeniusNatTrans_eq]

/-! ### Sheaves placed in degree `d` -/

/-- **`Hⁱ(RΓ_c(X_k̄, M[-d])) ≅ H^{i'}_c(X_k̄, M)` for `-d + i = i'`**, natural in the sheaf `M`. -/
def compactSupportSingleHomologyIso (d i i' : ℤ) (h : -d + i = i') :
    (Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, r} Λ X)).functor d ⋙
        compactSupportFrobeniusFunctor.{u, r} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i ≅
      (Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, r} Λ X)).functor 0 ⋙
        compactSupportFrobeniusFunctor.{u, r} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i' :=
  NatIso.ofComponents
    (fun M => (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).mapIso
        ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).mapIso
          (((Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, r} Λ X)).shiftIso (-d) d 0
            (neg_add_cancel d)).app M).symm ≪≫
          ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).commShiftIso (-d)).app
            (((Stacks.DerivedIndexing.cplusSingleFunctors
              (EtaleModules.{u, r} Λ X)).functor 0).obj M)) ≪≫
      plusHomologyShiftIso ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).obj
          (((Stacks.DerivedIndexing.cplusSingleFunctors
            (EtaleModules.{u, r} Λ X)).functor 0).obj M))
        (-d) i i' h)
    (fun {M M'} φ => by
      let S := Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, r} Λ X)
      let Φ := compactSupportFrobeniusFunctor.{u, r} Λ f j kbar
      have h₁ : (S.functor d).map φ ≫ (S.shiftIso (-d) d 0 (neg_add_cancel d)).inv.app M' =
          (S.shiftIso (-d) d 0 (neg_add_cancel d)).inv.app M ≫ ((S.functor 0).map φ)⟦-d⟧' :=
        (S.shiftIso (-d) d 0 (neg_add_cancel d)).inv.naturality φ
      have h₂ : Φ.map (((S.functor 0).map φ)⟦-d⟧') ≫
            (Φ.commShiftIso (-d)).hom.app ((S.functor 0).obj M') =
          (Φ.commShiftIso (-d)).hom.app ((S.functor 0).obj M) ≫
            (Φ.map ((S.functor 0).map φ))⟦-d⟧' :=
        (Φ.commShiftIso (-d)).hom.naturality ((S.functor 0).map φ)
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Iso.symm_hom, Iso.app_inv, Category.assoc]
      rw [← Functor.map_comp_assoc]
      refine plusHomologyShiftIso_square _ _ _ _ _ h ?_
      rw [← Φ.map_comp_assoc, h₁, Φ.map_comp, Category.assoc, h₂, Category.assoc])

/-- **The isomorphism `Hⁱ(RΓ_c(X_k̄, M[-d])) ≅ H^{i'}_c(X_k̄, M)` commutes with the geometric
Frobenius `π_X^*`.** -/
theorem compactSupportSingleHomologyIso_hom_frobenius (d i i' : ℤ) (h : -d + i = i') :
    Functor.whiskerLeft
        ((Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, r} Λ X)).functor d)
        (Functor.whiskerRight (canonicalCompactSupportFrobeniusNatTrans.{u, r} Λ f j kbar p q hcard)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i)) ≫
      (compactSupportSingleHomologyIso.{u, r} Λ f j kbar d i i' h).hom =
    (compactSupportSingleHomologyIso.{u, r} Λ f j kbar d i i' h).hom ≫
      Functor.whiskerLeft
        ((Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, r} Λ X)).functor 0)
        (Functor.whiskerRight (canonicalCompactSupportFrobeniusNatTrans.{u, r} Λ f j kbar p q hcard)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i')) := by
  refine NatTrans.ext (funext fun M => ?_)
  let S := Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, r} Λ X)
  let Φ := compactSupportFrobeniusFunctor.{u, r} Λ f j kbar
  let Fr := canonicalCompactSupportFrobeniusNatTrans.{u, r} Λ f j kbar p q hcard
  have h₁ : Φ.map ((S.shiftIso (-d) d 0 (neg_add_cancel d)).inv.app M) ≫
      Fr.app (((S.functor 0).obj M)⟦-d⟧) =
      Fr.app ((S.functor d).obj M) ≫ Φ.map ((S.shiftIso (-d) d 0 (neg_add_cancel d)).inv.app M) :=
    Fr.naturality ((S.shiftIso (-d) d 0 (neg_add_cancel d)).inv.app M)
  have h₂ : Fr.app (((S.functor 0).obj M)⟦-d⟧) ≫
      (Φ.commShiftIso (-d)).hom.app ((S.functor 0).obj M) =
      (Φ.commShiftIso (-d)).hom.app ((S.functor 0).obj M) ≫ (Fr.app ((S.functor 0).obj M))⟦-d⟧' :=
    (NatTrans.shift_app_comm Fr (-d) ((S.functor 0).obj M)).symm
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    compactSupportSingleHomologyIso, NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [← Functor.map_comp_assoc]
  refine plusHomologyShiftIso_square _ _ _ _ _ h ?_
  rw [← Category.assoc, ← h₁, Category.assoc, h₂, Category.assoc]

end CompactSupport

end Stacks.EtaleCohomology
