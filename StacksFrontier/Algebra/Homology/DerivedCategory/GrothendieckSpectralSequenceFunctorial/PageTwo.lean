module

public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.SpectralSequenceFunctor
import all StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.SpectralSequenceFunctor

/-!
# The second page of the functorial Grothendieck spectral sequence

The second page of the Grothendieck spectral sequence of `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞`
is identified, as an isomorphism of functors, with `R^qF ⋙ R^pG` for a single object of `𝒜`
(`natPageTwoIso`) and with `RF ⋙ H^q ⋙ R^pG` on `D⁺(𝒜)` (`plusPageTwoIso`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.Grothendieck

open Stacks.Cohomology.HigherDirectImagePresheaf (derivedPlusToStandard)

attribute [local instance] HasDerivedCategory.standard

section Construction

open CategoryTheory.ComposableArrows

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

private noncomputable def derivedTruncationSpectralSequenceNatFunctorPageTwoIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] (p q : ℕ) :
    derivedTruncationSpectralSequenceNatFunctor F G ⋙
      SpectralSequence.pageFunctor _ _ 2 2 ⋙ HomologicalComplex.eval _ _ (p, q) ≅
    (spectralObjectInFunctorCategory (DerivedCategory.Plus.singleFunctor A 0 ⋙
      derivedTruncationSpectralObjectFunctor F G)).H ((p : ℤ) + q) |>.obj
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) by simp))) := by
  let S := DerivedCategory.Plus.singleFunctor A 0 ⋙ derivedTruncationSpectralObjectFunctor F G
  have := spectralObjectInFunctorCategory_isFirstQuadrant S
    (fun X => derivedTruncationSpectralObject_isFirstQuadrant F G _)
  exact (spectralObjectInFunctorCategory S).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂CohomologicalNat (p, q) (q : ℤ) ((q : ℤ) + 1)
      rfl rfl ((p : ℤ) + q) rfl


/-- An object of the derived category concentrated in a single degree is canonically the
single complex on its cohomology in that degree. -/
private noncomputable def derivedObjectIsoSingleHomology
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (X : DerivedCategory A) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (DerivedCategory.singleFunctor A n).obj
      ((DerivedCategory.homologyFunctor A n).obj X) := by
  classical
  let h := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose h
  let e := Classical.choice (Classical.choose_spec h)
  exact e ≪≫ (DerivedCategory.singleFunctor A n).mapIso
    (((DerivedCategory.homologyFunctor A n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A n).app Y).symm)

/-- The identification above induces the identity on the cohomology in that degree. -/
private theorem derivedObjectIsoSingleHomology_homology
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (X : DerivedCategory A) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    (DerivedCategory.homologyFunctor A n).map
        (derivedObjectIsoSingleHomology X n).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A n).hom.app
        ((DerivedCategory.homologyFunctor A n).obj X) = 𝟙 _ := by
  classical
  let H := DerivedCategory.homologyFunctor A n
  let S := DerivedCategory.singleFunctor A n
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso A n
  let h := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose h
  let e := Classical.choice (Classical.choose_spec h)
  let u := H.mapIso e ≪≫ ε.app Y
  dsimp only [derivedObjectIsoSingleHomology]
  show H.map (e.hom ≫ S.map u.inv) ≫ ε.hom.app (H.obj X) = 𝟙 _
  have hn : H.map (S.map u.inv) ≫ ε.hom.app (H.obj X) =
      ε.hom.app Y ≫ u.inv := by
    simpa [H, S] using ε.hom.naturality u.inv
  rw [Functor.map_comp, Category.assoc, hn]
  simp [u, H, ε]

/-- A functor into the derived category with values concentrated in degree `n` is the single
complex on its `n`-th cohomology, naturally. -/
private noncomputable def derivedFunctorIsoSingleHomology
    {D A : Type*} [Category D] [Category A] [Abelian A] [HasDerivedCategory A]
    (F : D ⥤ DerivedCategory A) (n : ℤ)
    (hGE : ∀ X, (F.obj X).IsGE n) (hLE : ∀ X, (F.obj X).IsLE n) :
    F ≅ F ⋙ DerivedCategory.homologyFunctor A n ⋙ DerivedCategory.singleFunctor A n := by
  refine NatIso.ofComponents (fun X => by
    letI : (F.obj X).IsGE n := hGE X
    letI : (F.obj X).IsLE n := hLE X
    exact derivedObjectIsoSingleHomology (F.obj X) n) ?_
  intro X Y f
  let : (F.obj X).IsGE n := hGE X
  let : (F.obj X).IsLE n := hLE X
  let : (F.obj Y).IsGE n := hGE Y
  let : (F.obj Y).IsLE n := hLE Y
  let H := DerivedCategory.homologyFunctor A n
  let S := DerivedCategory.singleFunctor A n
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso A n
  let eX := derivedObjectIsoSingleHomology (F.obj X) n
  let eY := derivedObjectIsoSingleHomology (F.obj Y) n
  have key (Z : DerivedCategory A) [Z.IsGE n] [Z.IsLE n] :
      H.mapIso (derivedObjectIsoSingleHomology Z n) = (ε.app (H.obj Z)).symm := by
    apply Iso.ext
    apply (cancel_mono (ε.hom.app (H.obj Z))).1
    simpa using derivedObjectIsoSingleHomology_homology Z n
  have hx' : H.map eX.inv = ε.hom.app (H.obj (F.obj X)) := by
    simpa using congrArg Iso.inv (key (F.obj X))
  have hy' : H.map eY.hom = ε.inv.app (H.obj (F.obj Y)) :=
    congrArg Iso.hom (key (F.obj Y))
  apply (cancel_epi eX.inv).1
  simp only [Functor.comp_obj, Functor.comp_map, cancelIso]
  let u := eX.inv ≫ F.map f ≫ eY.hom
  obtain ⟨a, ha⟩ := S.map_surjective u
  have hu : H.map u = ε.hom.app (H.obj (F.obj X)) ≫
      H.map (F.map f) ≫ ε.inv.app (H.obj (F.obj Y)) := by
    dsimp [u]
    rw [Functor.map_comp, Functor.map_comp, hx', hy']
  have hnat : H.map (S.map a) ≫ ε.hom.app (H.obj (F.obj Y)) =
      ε.hom.app (H.obj (F.obj X)) ≫ a := by
    simpa [H, S] using ε.hom.naturality a
  have hA : ε.hom.app (H.obj (F.obj X)) ≫ a =
      ε.hom.app (H.obj (F.obj X)) ≫ H.map (F.map f) := by
    rw [← hnat, ha, hu]
    simp [Category.assoc]
  have ha' : a = H.map (F.map f) :=
    (cancel_epi (ε.hom.app (H.obj (F.obj X)))).mp hA
  change u = S.map (H.map (F.map f))
  exact ha.symm.trans (congrArg S.map ha')

/-- The degree-`q` slice of the derived direct image: the `q`-th truncation layer of `RF`. -/
private noncomputable def truncationSliceFunctor
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (q : ℤ) :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus B :=
  F.rightDerivedFunctorPlus ⋙
    (DerivedCategory.Plus.TStructure.t (C := B)).eTruncLT.obj ((q + 1 : ℤ) : EInt) ⋙
    (DerivedCategory.Plus.TStructure.t (C := B)).eTruncGE.obj (q : EInt)

private theorem truncationSliceFunctor_isGE
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (q : ℤ) (K : DerivedCategory.Plus A) :
    ((truncationSliceFunctor F q).obj K).IsGE q := by
  let T : CategoryTheory.Triangulated.TStructure (DerivedCategory.Plus B) :=
    DerivedCategory.Plus.TStructure.t
  exact T.isGE_eTruncGE_obj_obj q (q : EInt) (by simp)
    ((T.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj (F.rightDerivedFunctorPlus.obj K))

private theorem truncationSliceFunctor_isLE
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (q : ℤ) (K : DerivedCategory.Plus A) :
    ((truncationSliceFunctor F q).obj K).IsLE q := by
  let T : CategoryTheory.Triangulated.TStructure (DerivedCategory.Plus B) :=
    DerivedCategory.Plus.TStructure.t
  let Klt := (T.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj (F.rightDerivedFunctorPlus.obj K)
  have hLE : T.IsLE Klt q :=
    T.isLE_eTruncLT_obj_obj q ((q + 1 : ℤ) : EInt) (by simp)
      (F.rightDerivedFunctorPlus.obj K)
  let : T.IsLE Klt q := hLE
  dsimp [truncationSliceFunctor]
  show T.IsLE ((T.eTruncGE.obj (q : EInt)).obj Klt) q
  infer_instance

/-- The slice is the single complex on its own `q`-th cohomology. -/
private noncomputable def truncationSliceIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (q : ℤ) :
    truncationSliceFunctor F q ≅
      truncationSliceFunctor F q ⋙
        DerivedCategory.Plus.homologyFunctor B q ⋙
          DerivedCategory.Plus.singleFunctor B q := by
  let Sl := truncationSliceFunctor F q
  let ι : DerivedCategory.Plus B ⥤ DerivedCategory B := DerivedCategory.Plus.ι
  let H := DerivedCategory.Plus.homologyFunctor B q
  let Sg := DerivedCategory.Plus.singleFunctor B q
  let e := derivedFunctorIsoSingleHomology (Sl ⋙ ι) q
    (fun K => by
      change (ι.obj (Sl.obj K)).IsGE q
      rw [DerivedCategory.Plus.isGE_ι_obj_iff]
      exact truncationSliceFunctor_isGE F q K)
    (fun K => by
      change (ι.obj (Sl.obj K)).IsLE q
      rw [DerivedCategory.Plus.isLE_ι_obj_iff]
      exact truncationSliceFunctor_isLE F q K)
  let eTarget : Sl ⋙ H ⋙ Sg ⋙ ι ≅
      Sl ⋙ ι ⋙ DerivedCategory.homologyFunctor B q ⋙
        DerivedCategory.singleFunctor B q := by
    refine NatIso.ofComponents (fun K =>
      (DerivedCategory.Plus.singleFunctorιIso B q).app (H.obj (Sl.obj K))) ?_
    intro K L φ
    dsimp [Sl, H, Sg]
    exact (DerivedCategory.Plus.singleFunctorιIso B q).hom.naturality
      ((DerivedCategory.Plus.homologyFunctor B q).map ((truncationSliceFunctor F q).map φ))
  exact Functor.fullyFaithfulCancelRight ι (e.trans eTarget.symm)

/-- The `q`-th cohomology of the slice is the `q`-th cohomology of the derived image. -/
private noncomputable def truncationSliceHomologyIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (q : ℤ) :
    truncationSliceFunctor F q ⋙ DerivedCategory.Plus.homologyFunctor B q ≅
      F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B q := by
  let T : CategoryTheory.Triangulated.TStructure (DerivedCategory.Plus B) :=
    DerivedCategory.Plus.TStructure.t
  let RF := F.rightDerivedFunctorPlus
  let LT := T.eTruncLT.obj ((q + 1 : ℤ) : EInt)
  let GE := T.eTruncGE.obj (q : EInt)
  let H₀ := DerivedCategory.Plus.homologyFunctor B 0
  letI : H₀.ShiftSequence ℤ := inferInstance
  let H := H₀.shift q
  let ηLT : RF ⋙ LT ⋙ H ⟶ RF ⋙ H :=
    Functor.whiskerLeft RF (Functor.whiskerRight
      (T.eTruncLTι ((q + 1 : ℤ) : EInt)) H)
  let θGE : LT ⋙ H ⟶ (LT ⋙ GE) ⋙ H :=
    Functor.whiskerLeft LT (Functor.whiskerRight (T.eTruncGEπ (q : EInt)) H)
  let ηGE := Functor.whiskerLeft RF θGE
  have hηLT (K : DerivedCategory.Plus A) : IsIso (ηLT.app K) := by
    let K' := RF.obj K
    let Tq := (T.triangleLTGE (q + 1)).obj K'
    have hTq := T.triangleLTGE_distinguished (q + 1) K'
    have hGE : T.IsGE Tq.obj₃ (q + 1) := by
      change T.IsGE ((T.truncGE (q + 1)).obj K') (q + 1)
      exact T.isGE_truncGE_obj K' (q + 1) (q + 1) le_rfl
    let : T.IsGE Tq.obj₃ (q + 1) := hGE
    have hz : IsZero ((H₀.shift q).obj Tq.obj₃) :=
      DerivedCategory.Plus.isZero_homology_of_isGE Tq.obj₃ (q + 1) q (by omega)
    have h_epi : Epi ((H₀.shift q).map Tq.mor₁) :=
      (H₀.homologySequence_epi_shift_map_mor₁_iff Tq hTq q).2 (hz.eq_of_tgt _ _)
    have hz' : IsZero ((H₀.shift (q - 1)).obj Tq.obj₃) :=
      DerivedCategory.Plus.isZero_homology_of_isGE Tq.obj₃ (q + 1) (q - 1) (by omega)
    have h_mono : Mono ((H₀.shift q).map Tq.mor₁) :=
      (H₀.homologySequence_mono_shift_map_mor₁_iff Tq hTq (q - 1) q (by omega)).2
        (hz'.eq_of_src _ _)
    have h_iso : IsIso ((H₀.shift q).map Tq.mor₁) := isIso_of_mono_of_epi _
    change IsIso (H.map ((T.eTruncLTι ((q + 1 : ℤ) : EInt)).app (RF.obj K)))
    exact h_iso
  have hηGE (K : DerivedCategory.Plus A) : IsIso (ηGE.app K) := by
    let K' := LT.obj (RF.obj K)
    let Tq := (T.triangleLTGE q).obj K'
    have hTq := T.triangleLTGE_distinguished q K'
    have hLE : T.IsLE Tq.obj₁ (q - 1) := by
      change T.IsLE ((T.truncLT q).obj K') (q - 1)
      exact T.isLE_eTruncLT_obj_obj (q - 1) (q : EInt) (by simp) K'
    let : T.IsLE Tq.obj₁ (q - 1) := hLE
    have hz : IsZero ((H₀.shift q).obj Tq.obj₁) :=
      DerivedCategory.Plus.isZero_homology_of_isLE Tq.obj₁ (q - 1) q (by omega)
    have h_mono : Mono ((H₀.shift q).map Tq.mor₂) :=
      (H₀.homologySequence_mono_shift_map_mor₂_iff Tq hTq q).2 (hz.eq_of_src _ _)
    have hz' : IsZero ((H₀.shift (q + 1)).obj Tq.obj₁) :=
      DerivedCategory.Plus.isZero_homology_of_isLE Tq.obj₁ (q - 1) (q + 1) (by omega)
    have h_epi : Epi ((H₀.shift q).map Tq.mor₂) :=
      (H₀.homologySequence_epi_shift_map_mor₂_iff Tq hTq q (q + 1) (by omega)).2
        (hz'.eq_of_tgt _ _)
    have h_iso : IsIso ((H₀.shift q).map Tq.mor₂) := isIso_of_mono_of_epi _
    change IsIso (H.map ((T.eTruncGEπ (q : EInt)).app K'))
    exact h_iso
  haveI : IsIso ηLT := (NatTrans.isIso_iff_isIso_app ηLT).2 hηLT
  haveI : IsIso ηGE := (NatTrans.isIso_iff_isIso_app ηGE).2 hηGE
  let eLT := asIso ηLT
  let eGE := asIso ηGE
  exact eGE.symm ≪≫ eLT

/-- Shifting the single complex: `H^{p+q}(RG(X[−q]))` is the `p`-th derived functor. -/
private noncomputable def shiftedRightDerivedIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    DerivedCategory.Plus.singleFunctor A q ⋙ F.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor B (p + q) ≅
      F.rightDerivedPlus p := by
  let RF := F.rightDerivedFunctorPlus
  let α := F.rightDerivedFunctorPlusUnith
  let W := HomotopyCategory.Plus.quasiIso A
  letI : RF.IsRightDerivedFunctor α W := inferInstance
  letI : RF.CommShift ℤ := Functor.IsRightDerivedFunctor.commShift RF α W ℤ
  letI : NatTrans.CommShift α ℤ :=
    Functor.IsRightDerivedFunctor.natTrans_commShift RF α W ℤ
  let S₀ := DerivedCategory.Plus.singleFunctor A 0
  let H := DerivedCategory.Plus.homologyFunctor B (p + q)
  let ι : DerivedCategory.Plus B ⥤ DerivedCategory B := DerivedCategory.Plus.ι
  let Hord := DerivedCategory.homologyFunctor B (p + q)
  let Hord₀ := DerivedCategory.homologyFunctor B 0
  let shA := shiftFunctor (DerivedCategory.Plus A) (-q)
  let shB := shiftFunctor (DerivedCategory.Plus B) (-q)
  let shD := shiftFunctor (DerivedCategory B) (-q)
  let eS : DerivedCategory.Plus.singleFunctor A q ≅ S₀ ⋙ shA :=
    ((DerivedCategory.Plus.singleFunctors A).shiftIso (-q) q 0 (by omega)).symm
  have eHOrd : shD ⋙ Hord ≅ DerivedCategory.homologyFunctor B p := by
    dsimp [Hord]
    rw [← DerivedCategory.shift_homologyFunctor B (p + q),
      ← DerivedCategory.shift_homologyFunctor B p]
    exact (DerivedCategory.homologyFunctor B 0).shiftIso (-q) (p + q) p (by omega)
  have eH : shB ⋙ H ≅ DerivedCategory.Plus.homologyFunctor B p := by
    change shB ⋙ ι ⋙ Hord ≅ ι ⋙ DerivedCategory.homologyFunctor B p
    exact (Functor.associator shB ι Hord).symm ≪≫
      Functor.isoWhiskerRight (ι.commShiftIso (-q)) Hord ≪≫
      Functor.associator ι shD Hord ≪≫
      Functor.isoWhiskerLeft ι eHOrd
  change DerivedCategory.Plus.singleFunctor A q ⋙ RF ⋙ H ≅ _
  dsimp [Functor.rightDerivedPlus, RF, H, S₀]
  exact
    Functor.isoWhiskerRight eS (RF ⋙ H) ≪≫
      Functor.isoWhiskerRight (Functor.associator S₀ shA RF) H ≪≫
      Functor.associator S₀ (shA ⋙ RF) H ≪≫
      Functor.isoWhiskerLeft S₀ (Functor.isoWhiskerRight (RF.commShiftIso (-q)) H) ≪≫
      Functor.isoWhiskerLeft S₀ (Functor.associator RF shB H) ≪≫
      Functor.isoWhiskerLeft (S₀ ⋙ RF) eH

/-- The second-page term of the Grothendieck spectral object is the cohomology of the
derived image of the slice. -/
private noncomputable def pageTwoSliceFunctorIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] (p q : ℤ) :
    ((spectralObjectInFunctorCategory
          (derivedTruncationSpectralObjectFunctor F G)).H (p + q)).obj
        (mk₁ (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp))) ≅
      truncationSliceFunctor F q ⋙ G.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor C (p + q) :=
  Iso.refl _

/-- The second page of the Grothendieck spectral sequence of `F` and `G`, identified with
`R^pG ∘ H^q ∘ RF`. -/
private noncomputable def pageTwoChainIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] (p : ℕ) (q : ℤ) :
    ((spectralObjectInFunctorCategory
          (derivedTruncationSpectralObjectFunctor F G)).H ((p : ℤ) + q)).obj
        (mk₁ (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp))) ≅
      F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B q ⋙
        G.rightDerived p := by
  let RF := F.rightDerivedFunctorPlus
  let RG := G.rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor C ((p : ℤ) + q)
  let Hq := DerivedCategory.Plus.homologyFunctor B q
  let Sg := DerivedCategory.Plus.singleFunctor B q
  let Sl := truncationSliceFunctor F q
  let W := RG ⋙ H
  exact pageTwoSliceFunctorIso F G (p : ℤ) q ≪≫
    Functor.isoWhiskerRight (truncationSliceIso F q) W ≪≫
    Functor.associator Sl (Hq ⋙ Sg) W ≪≫
    Functor.isoWhiskerLeft Sl (Functor.associator Hq Sg W) ≪≫
    (Functor.associator Sl Hq (Sg ⋙ W)).symm ≪≫
    Functor.isoWhiskerLeft (Sl ⋙ Hq) (shiftedRightDerivedIso G (p : ℤ) q) ≪≫
    Functor.isoWhiskerRight (truncationSliceHomologyIso F q) (G.rightDerivedPlus (p : ℤ)) ≪≫
    Functor.associator RF Hq (G.rightDerivedPlus (p : ℤ)) ≪≫
    Functor.isoWhiskerLeft (RF ⋙ Hq) (derivedPlusToStandard G p)

/-- The second page of the Grothendieck spectral sequence for bounded below complexes. -/
@[no_expose] noncomputable def plusPageTwoIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] (p : ℕ) (q : ℤ) :
    derivedTruncationSpectralSequenceFunctor F G ⋙
        SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ ((p : ℤ), q) ≅
      F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B q ⋙
        G.rightDerived p :=
  spectralObjectSequenceFunctorPageTwoIso
      (derivedTruncationSpectralObjectFunctor F G) (p : ℤ) q ≪≫
    pageTwoChainIso F G p q

/-- The second page of the Grothendieck spectral sequence for a single object. -/
@[no_expose] noncomputable def natPageTwoIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] (p q : ℕ) :
    derivedTruncationSpectralSequenceNatFunctor F G ⋙
        SpectralSequence.pageFunctor _ _ 2 2 ⋙ HomologicalComplex.eval _ _ (p, q) ≅
      F.rightDerived q ⋙ G.rightDerived p := by
  have e₄a : DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor B (q : ℤ) ≅ F.rightDerivedPlus (q : ℤ) := by
    simpa only [add_zero] using shiftedRightDerivedIso F (q : ℤ) 0
  have e₀ : ((spectralObjectInFunctorCategory (DerivedCategory.Plus.singleFunctor A 0 ⋙
        derivedTruncationSpectralObjectFunctor F G)).H ((p : ℤ) + (q : ℤ))).obj
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) by simp))) ≅
      DerivedCategory.Plus.singleFunctor A 0 ⋙
        ((spectralObjectInFunctorCategory
          (derivedTruncationSpectralObjectFunctor F G)).H ((p : ℤ) + (q : ℤ))).obj
          (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) by simp))) :=
    Iso.refl _
  exact derivedTruncationSpectralSequenceNatFunctorPageTwoIso F G p q ≪≫ e₀ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
      (pageTwoChainIso F G p (q : ℤ)) ≪≫
    Functor.isoWhiskerRight (e₄a ≪≫ derivedPlusToStandard F q) (G.rightDerived p)

end Construction

end Stacks.Cohomology.Grothendieck

end
