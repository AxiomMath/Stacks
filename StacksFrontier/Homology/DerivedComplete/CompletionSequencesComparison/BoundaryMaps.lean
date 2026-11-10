module

public import StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.ShiftCompatibility
import all StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.ShortExactSequences
import all StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.ShiftCompatibility

/-!
# Comparison of completions at a principal ideal: boundary and connecting maps

Auxiliary part of Stacks 0H32. This part describes the boundary maps of the completion cone
sequences and of the derived completion, the projections of the cones, and the connecting map
of the Milnor triangle, and proves their naturality and their compatibility with shifts, with
single complexes and with truncations.
-/

section


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory PrincipalTorsionTower

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace PrincipalCompletionDiagram

attribute [local instance] DerivedCategory.homologyFunctor_linear

universe u₁ v₁

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem completionConeBoundary_eq
    {A : Type u} [CommRing A] (f : A)
    {F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A)}
    {η : 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F}
    (c : CompletionSequences.CompletionComparison A f F η)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (p q : ℤ) (hpq : p + 1 = q) (n : ℕ) :
    completionConeBoundary f c C p q hpq n =
      (homologyFunctor (ModuleCat.{v} A) p).map (c.iso C).hom ≫
      (homologyFunctorFactors (ModuleCat.{v} A) p).hom.app
        (CochainComplex.mappingCocone
          (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
            C))) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) 0).shiftMap
        (principalCompletionBoundary f C n) p q (by omega) ≫
      (homologyFunctorFactors (ModuleCat.{v} A) q).inv.app C := by
  erw [← shiftMap_homologyFunctor_map_Q (principalCompletionBoundary f C n) p q (by omega)]
  dsimp only [completionConeBoundary, principalCompletionBoundary,
    Functor.homologySequenceδ, Functor.shiftMap, ShiftedHom.map]
  simp only [Functor.map_comp, Category.assoc]
  rw [show (Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C))).mor₃ =
      Q.map (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C)).mor₃ ≫
      (Q.commShiftIso (1 : ℤ)).hom.app C from rfl]
  simp only [Functor.map_comp, Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem homologyShiftIso_hom_app_Q_obj_inv
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (m a a' : ℤ) (h : m + a = a') :
    (homologyFunctor C a).map ((Q.commShiftIso m).inv.app K) ≫
      (homologyFunctorFactors C a).hom.app (K⟦m⟧) ≫
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso m a a' h).hom.app K =
    ((homologyFunctor C 0).shiftIso m a a' h).hom.app (Q.obj K) ≫
      (homologyFunctorFactors C a').hom.app K := by
  apply (cancel_epi ((homologyFunctor C a).map ((Q.commShiftIso m).hom.app K))).1
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [reassoc_of% homologyShiftIso_hom_app_Q_obj K m a a' h]
  simp only [Iso.inv_hom_id_app]
  exact (congrArg ((homologyFunctorFactors C a).hom.app (K⟦m⟧) ≫ ·)
    (Category.comp_id _)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem completionConeBoundary_shift
    {A : Type u} [CommRing A] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (s : CompletionSequences.CompletionShift A (completion ⋙ P.ι) adj.unit)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m p q p' q' : ℤ)
    (hpq : p + 1 = q) (hp : m + p = p') (hq : m + q = q') (n : ℕ) :
    completionConeBoundary f c (C⟦m⟧) p q hpq n ≫
      (homologyFunctor (ModuleCat.{v} A) q).map ((Q.commShiftIso m).hom.app C) ≫
      ((homologyFunctor (ModuleCat.{v} A) 0).shiftIso m q q' hq).hom.app (Q.obj C) =
    m.negOnePow •
      ((homologyFunctor (ModuleCat.{v} A) p).map
        ((completion ⋙ P.ι).map ((Q.commShiftIso m).hom.app C) ≫ (s.iso (Q.obj C) m).hom) ≫
      ((homologyFunctor (ModuleCat.{v} A) 0).shiftIso m p p' hp).hom.app
        ((completion ⋙ P.ι).obj (Q.obj C)) ≫
      completionConeBoundary f c C p' q' (by omega) n) := by
  let H := homologyFunctor (ModuleCat.{v} A)
  let HC := HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ)
  have hC : (homologyFunctorFactors (ModuleCat.{v} A) q).inv.app (C⟦m⟧) ≫
      (H q).map ((Q.commShiftIso m).hom.app C) ≫
      ((H 0).shiftIso m q q' hq).hom.app (Q.obj C) =
      ((HC 0).shiftIso m q q' hq).hom.app C ≫
      (homologyFunctorFactors (ModuleCat.{v} A) q').inv.app C := by
    rw [homologyShiftIso_hom_app_Q_obj]
    simp only [Iso.inv_hom_id_app_assoc]
    rfl
  rw [completionConeBoundary_eq, completionConeBoundary_eq,
    ← completionComparison_shift f adj c s C m]
  simp only [Functor.map_comp, Category.assoc]
  rw [hC]
  erw [(homologyFunctorFactors (ModuleCat.{v} A) p).hom.naturality_assoc]
  erw [← (HC 0).shiftMap_comp'_assoc]
  rw [principalCompletionShiftMap_boundary]
  have hsmul {X Y : CochainComplex (ModuleCat.{v} A) ℤ}
      (k : X ⟶ Y⟦(1 : ℤ)⟧) :
      (HC 0).shiftMap (m.negOnePow • k) p q (by omega) =
        m.negOnePow • (HC 0).shiftMap k p q (by omega) := by
    dsimp only [Functor.shiftMap]
    erw [show (HC p).map (m.negOnePow • k) = m.negOnePow • (HC p).map k from
      map_zsmul_unit (HC p).mapAddHom _ _, Linear.units_smul_comp]
    rfl
  rw [hsmul]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp]
  congr 1
  erw [reassoc_of% shiftMap_shift (HC 0) (principalCompletionBoundary f C n)
    m p q p' q' hpq hp hq]
  rw [reassoc_of% homologyShiftIso_hom_app_Q_obj_inv _ m p p' hp]
  erw [((H 0).shiftIso m p p' hp).hom.naturality_assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem completionConeBoundary_single
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (s : CompletionSequences.CompletionShift A (completion ⋙ P.ι) adj.unit)
    (M : ModuleCat.{v} A) (seq : CompletionSequences.ModuleCompletionSequence A f
      (completion ⋙ P.ι) adj.unit c M) (p : ℤ) (n : ℕ) :
    completionConeBoundary f c ((CochainComplex.singleFunctor (ModuleCat.{v} A) (p + 1)).obj M)
      p (p + 1) rfl n ≫ (CompletionSequences.singleHomology A (p + 1) M).hom =
    (p + 1).negOnePow •
      ((s.singleIso M (p + 1) p (-1) (by omega)).hom ≫ seq.tateIso.hom ≫
        limit.π (PrincipalTorsionTower.powerTorsionSystem A M f) ⟨n⟩ ≫
        kernel.ι (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1)))) := by
  let H := homologyFunctor (ModuleCat.{v} A)
  let F := completion ⋙ P.ι
  let C := CompletionSequences.moduleComplex A M
  let D := (CochainComplex.singleFunctor (ModuleCat.{v} A) (p + 1)).obj M
  let m := -(p + 1)
  let e : Q.obj (C⟦m⟧) ≅ Q.obj D :=
    (Q.commShiftIso m).app C ≪≫
      ((singleFunctors (ModuleCat.{v} A)).shiftIso m (p + 1) 0 (by dsimp [m]; omega)).app M
  let d := ((singleFunctors (ModuleCat.{v} A)).shiftIso m (p + 1) 0 (by dsimp [m]; omega)).app M
  have hd : (H (p + 1)).map d.hom ≫ (CompletionSequences.singleHomology A (p + 1) M).hom =
      ((H 0).shiftIso m (p + 1) 0 (by dsimp [m]; omega)).hom.app (Q.obj C) ≫
      (CompletionSequences.singleHomology A 0 M).hom := by
    apply (cancel_epi ((H (p + 1)).map d.inv)).1
    rw [← Functor.map_comp_assoc, d.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    exact (singleHomology_shift M m (p + 1) 0 (by dsimp [m]; omega)).symm
  have he : (H (p + 1)).map e.hom ≫ (CompletionSequences.singleHomology A (p + 1) M).hom =
      (H (p + 1)).map ((Q.commShiftIso m).hom.app C) ≫
      ((H 0).shiftIso m (p + 1) 0 (by dsimp [m]; omega)).hom.app (Q.obj C) ≫
      (CompletionSequences.singleHomology A 0 M).hom := by
    change (H (p + 1)).map ((Q.commShiftIso m).hom.app C ≫ d.hom) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, hd]
  have hz : F.map e.hom ≫ (F.map d.inv ≫ (s.iso (Q.obj C) m).hom) =
      F.map ((Q.commShiftIso m).hom.app C) ≫ (s.iso (Q.obj C) m).hom := by
    change F.map ((Q.commShiftIso m).hom.app C ≫ d.hom) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, ← F.map_comp_assoc d.hom d.inv, d.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hc : (H p).map (F.map e.hom) ≫ (s.singleIso M (p + 1) p (-1) (by omega)).hom =
      (H p).map (F.map ((Q.commShiftIso m).hom.app C) ≫ (s.iso (Q.obj C) m).hom) ≫
      ((H 0).shiftIso m p (-1) (by dsimp [m]; omega)).hom.app (F.obj (Q.obj C)) := by
    change (H p).map (F.map e.hom) ≫
      (H p).map (F.map d.inv ≫ (s.iso (Q.obj C) m).hom) ≫ _ = _
    rw [← Functor.map_comp_assoc, hz]
    rfl
  have hbase : completionConeBoundary f c C (-1) 0 (by omega) n ≫
      (CompletionSequences.singleHomology A 0 M).hom =
      seq.tateIso.hom ≫ limit.π (PrincipalTorsionTower.powerTorsionSystem A M f) ⟨n⟩ ≫
        kernel.ι (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1))) := by
    rw [reassoc_of% seq.tateIso_π n, Category.assoc, seq.torsionIso_ι]
  apply (cancel_epi ((H p).map (F.map e.hom))).1
  rw [← Category.assoc, completionConeBoundary_naturality f adj c (C⟦m⟧) D e.hom,
    Category.assoc, he]
  dsimp only [H]
  have hshift := completionConeBoundary_shift f adj c s C m p (p + 1) (-1) 0 rfl
    (by dsimp [m]; omega) (by dsimp [m]; omega) n
  have hh := congrArg (fun k => k ≫ (CompletionSequences.singleHomology A 0 M).hom) hshift
  simp only [Category.assoc] at hh
  refine hh.trans ?_
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
    m, Int.negOnePow_neg]
  rw [← reassoc_of% hc]
  simp only [completionConeBoundary, Category.assoc] at hbase
  rw [hbase]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private abbrev derivedCompletionBoundary
    {A : Type u} [CommRing A] (f : A)
    {F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A)}
    {η : 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F}
    (c : CompletionSequences.CompletionComparison A f F η)
    (K : DerivedCategory (ModuleCat.{v} A)) (p q : ℤ) (hpq : p + 1 = q) (n : ℕ) :=
  (homologyFunctor (ModuleCat.{v} A) p).map (F.map (Q.objObjPreimageIso K).inv) ≫
    completionConeBoundary f c (Q.objPreimage K) p q hpq n ≫
    (homologyFunctor (ModuleCat.{v} A) q).map (Q.objObjPreimageIso K).hom

/-- Naturality of the completion cone boundary, conjugated by isomorphisms with `Q`-images. -/
private theorem completionConeBoundary_conj_naturality
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} {K L : DerivedCategory (ModuleCat.{v} A)}
    (a : Q.obj C ≅ K) (b : Q.obj D ≅ L) (g : K ⟶ L) (p q : ℤ) (hpq : p + 1 = q) (n : ℕ) :
    (homologyFunctor (ModuleCat.{v} A) p).map ((completion ⋙ P.ι).map g) ≫
      (homologyFunctor (ModuleCat.{v} A) p).map ((completion ⋙ P.ι).map b.inv) ≫
        completionConeBoundary f c D p q hpq n ≫ (homologyFunctor (ModuleCat.{v} A) q).map b.hom =
    (homologyFunctor (ModuleCat.{v} A) p).map ((completion ⋙ P.ι).map a.inv) ≫
      completionConeBoundary f c C p q hpq n ≫ (homologyFunctor (ModuleCat.{v} A) q).map a.hom ≫
        (homologyFunctor (ModuleCat.{v} A) q).map g := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  (have h := completionConeBoundary_naturality f adj c C D (a.hom ≫ g ≫ b.inv) p q hpq n
   have hh := congrArg (fun k => (homologyFunctor (ModuleCat.{v} A) p).map
     ((completion ⋙ P.ι).map a.inv) ≫ k ≫ (homologyFunctor (ModuleCat.{v} A) q).map b.hom) h
   simp only [Functor.map_comp, Category.assoc] at hh
   simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
     CategoryTheory.Functor.map_id, Category.comp_id] at hh
   simpa only [completionConeBoundary, Functor.map_comp, Category.assoc] using hh)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem derivedCompletionBoundary_eq
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (K : DerivedCategory (ModuleCat.{v} A))
    (e : Q.obj C ≅ K) (p q : ℤ) (hpq : p + 1 = q) (n : ℕ) :
    derivedCompletionBoundary f c K p q hpq n =
      (homologyFunctor (ModuleCat.{v} A) p).map ((completion ⋙ P.ι).map e.inv) ≫
      completionConeBoundary f c C p q hpq n ≫
      (homologyFunctor (ModuleCat.{v} A) q).map e.hom := by
  have h := completionConeBoundary_conj_naturality f adj c (Q.objObjPreimageIso K) e (𝟙 K) p q hpq n
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  exact h.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem derivedCompletionBoundary_naturality
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    {K L : DerivedCategory (ModuleCat.{v} A)} (g : K ⟶ L)
    (p q : ℤ) (hpq : p + 1 = q) (n : ℕ) :
    (homologyFunctor (ModuleCat.{v} A) p).map ((completion ⋙ P.ι).map g) ≫
      derivedCompletionBoundary f c L p q hpq n =
    derivedCompletionBoundary f c K p q hpq n ≫
      (homologyFunctor (ModuleCat.{v} A) q).map g := by
  exact completionConeBoundary_conj_naturality f adj c (Q.objObjPreimageIso K)
    (Q.objObjPreimageIso L) g p q hpq n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem homologyMap_truncGEπ_mono
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (n p : ℤ) (hnp : n ≤ p) :
    Mono ((homologyFunctor C p).map ((TStructure.t.truncGEπ n).app K)) := by
  let T := (TStructure.t.triangleLTGE n).obj K
  have hz : IsZero ((homologyFunctor C p).obj T.obj₁) :=
    DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) p (by omega)
  exact ((homologyFunctor C 0).homologySequence_exact₂ T
    (TStructure.t.triangleLTGE_distinguished n K) p).mono_g (hz.eq_of_src _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem derivedCompletionBoundary_projection
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (s : CompletionSequences.CompletionShift A (completion ⋙ P.ι) adj.unit)
    (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ)
    (t : CompletionSequences.TruncationIdentifications A (completion ⋙ P.ι) K p)
    (seq : CompletionSequences.ModuleCompletionSequence A f (completion ⋙ P.ι) adj.unit c
      ((homologyFunctor (ModuleCat.{v} A) (p + 1)).obj K)) (n : ℕ) :
    derivedCompletionBoundary f c K p (p + 1) rfl n =
      t.projection f s seq.tateIso ≫
        limit.π (PrincipalTorsionTower.powerTorsionSystem A ((homologyFunctor (ModuleCat.{v} A) (p +
          1)).obj K) f) ⟨n⟩ ≫
        kernel.ι (PrincipalTorsionTower.powerMultiplication A
          ((homologyFunctor (ModuleCat.{v} A) (p + 1)).obj K) (f ^ (n + 1))) := by
  let H := homologyFunctor (ModuleCat.{v} A)
  let F := completion ⋙ P.ι
  let N := (H (p + 1)).obj K
  let Y := (CompletionSequences.truncGE A (p + 1)).obj K
  let π := (CompletionSequences.truncOut A (p + 1)).app K
  let j := t.upper.inv ≫ (CompletionSequences.truncIn A (p + 1)).app Y
  let B (X : DerivedCategory (ModuleCat.{v} A)) := derivedCompletionBoundary f c X p (p + 1) rfl n
  have hj : (H (p + 1)).map j = (CompletionSequences.singleHomology A (p + 1) N).hom ≫ (H (p +
    1)).map π := by
    dsimp only [j]
    rw [Functor.map_comp, ← t.upper_homology, ← Functor.map_comp_assoc, t.upper.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hY : B Y = inv ((H p).map (F.map j)) ≫ B ((CompletionSequences.single A (p + 1)).obj N) ≫
      (H (p + 1)).map j := by
    apply (cancel_epi ((H p).map (F.map j))).1
    rw [IsIso.hom_inv_id_assoc]
    exact derivedCompletionBoundary_naturality f adj c j p (p + 1) rfl n
  have hs : B ((CompletionSequences.single A (p + 1)).obj N) ≫
      (CompletionSequences.singleHomology A (p + 1) N).hom =
      (p + 1).negOnePow • ((s.singleIso N (p + 1) p (-1) (by omega)).hom ≫
        seq.tateIso.hom ≫ limit.π (PrincipalTorsionTower.powerTorsionSystem A N f) ⟨n⟩ ≫
          kernel.ι (PrincipalTorsionTower.powerMultiplication A N (f ^ (n + 1)))) := by
    dsimp only [B]
    erw [derivedCompletionBoundary_eq f adj c
      ((CochainComplex.singleFunctor (ModuleCat.{v} A) (p + 1)).obj N) _ (Iso.refl _) p (p + 1) rfl
        n]
    simp only [Iso.refl_hom, Iso.refl_inv, CategoryTheory.Functor.map_id, Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact completionConeBoundary_single f adj c s N seq p n
  have : Mono ((H (p + 1)).map π) := homologyMap_truncGEπ_mono K (p + 1) (p + 1) le_rfl
  apply (cancel_mono ((H (p + 1)).map π)).1
  change B K ≫ (H (p + 1)).map π = _
  have hπ : (H p).map (F.map π) ≫ B Y = B K ≫ (H (p + 1)).map π :=
    derivedCompletionBoundary_naturality f adj c π p (p + 1) rfl n
  rw [← hπ, hY, hj]
  rw [reassoc_of% hs]
  simp only [CompletionSequences.TruncationIdentifications.projection, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private abbrev principalConeProjection
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :=
  CochainComplex.mappingCocone.fst
    (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f C)) ≫
  Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩) n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private abbrev completionConeProjection
    {A : Type u} [CommRing A] (f : A)
    {F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A)}
    {η : 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F}
    (c : CompletionSequences.CompletionComparison A f F η)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :=
  (c.iso C).hom ≫ Q.map (principalConeProjection f C n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def principalConeShiftIso
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) (n : ℕ) :
    Q.obj (CochainComplex.mappingCone (f ^ (n + 1) • 𝟙 (C⟦m⟧))) ≅
      (Q.obj (CochainComplex.mappingCone (f ^ (n + 1) • 𝟙 C)))⟦m⟧ :=
  (Q.mapIso (CochainComplex.mappingCone.shiftIso (f ^ (n + 1) • 𝟙 C) m)).symm ≪≫
    (Q.commShiftIso m).app (CochainComplex.mappingCone (f ^ (n + 1) • 𝟙 C))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalConeShiftIso_inr
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) (n : ℕ) :
    Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 (C⟦m⟧))) ≫
      (principalConeShiftIso f C m n).hom =
    (Q.commShiftIso m).hom.app C ≫
      (Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C)))⟦m⟧' := by
  dsimp only [principalConeShiftIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_hom]
  rw [← Functor.map_comp_assoc]
  have h : CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 (C⟦m⟧)) ≫
      (CochainComplex.mappingCone.shiftIso (f ^ (n + 1) • 𝟙 C) m).inv =
      (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C))⟦m⟧' :=
    (Iso.comp_inv_eq (CochainComplex.mappingCone.shiftIso (f ^ (n + 1) • 𝟙 C) m)).2
      (CompletionSequences.coneShiftIso_hom_inr (f ^ (n + 1) • 𝟙 C) m).symm
  rw [h, Q.commShiftIso_hom_naturality]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem completionConeProjection_shift
    {A : Type u} [CommRing A] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (s : CompletionSequences.CompletionShift A (completion ⋙ P.ι) adj.unit)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) (n : ℕ) :
    completionConeProjection f c (C⟦m⟧) n ≫ (principalConeShiftIso f C m n).hom =
      (completion ⋙ P.ι).map ((Q.commShiftIso m).hom.app C) ≫
      (s.iso (Q.obj C) m).hom ≫ (completionConeProjection f c C n)⟦m⟧' := by
  have h : (principalCompletionShiftMap f C m ≫ principalConeProjection f (C⟦m⟧) n) ≫
      (CochainComplex.mappingCone.shiftIso (f ^ (n + 1) • 𝟙 C) m).inv =
      (principalConeProjection f C n)⟦m⟧' := by
    apply (Iso.comp_inv_eq (CochainComplex.mappingCone.shiftIso (f ^ (n + 1) • 𝟙 C) m)).2
    exact principalCompletionShiftMap_projection f C m n
  dsimp only [completionConeProjection, principalConeShiftIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_inv, Iso.app_hom]
  rw [← completionComparison_shift f adj c s C m]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, h]
  erw [Q.commShiftIso_hom_naturality]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem completionConeProjection_map
    {A : Type u} [CommRing A] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} (g : C ⟶ D) (n : ℕ) :
    (completion ⋙ P.ι).map (Q.map g) ≫ completionConeProjection f c D n =
    completionConeProjection f c C n ≫ Q.map ((principalComplexSystemMap f g).app ⟨n⟩) := by
  dsimp only [completionConeProjection, principalConeProjection]
  rw [← Category.assoc, completionComparison_naturality f adj c g, Category.assoc]
  erw [Functor.map_comp, ← Category.assoc (milnorTriangleMap (principalComplexSystemMap f g)).hom₁,
    ← (milnorTriangleMap (principalComplexSystemMap f g)).comm₁, milnorTriangleMap_hom₂]
  simp only [Category.assoc, ← Functor.map_comp, Pi.map_π]
  simp only [Functor.map_comp]
  rfl
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem completionConeProjection_single
    {A : Type u} [CommRing A] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (s : CompletionSequences.CompletionShift A (completion ⋙ P.ι) adj.unit)
    (M : ModuleCat.{v} A) (seq : CompletionSequences.ModuleCompletionSequence A f
      (completion ⋙ P.ι) adj.unit c M) (p : ℤ) (n : ℕ) :
    let D := (CochainComplex.singleFunctor (ModuleCat.{v} A) p).obj M
    ∃ q : (homologyFunctor (ModuleCat.{v} A) p).obj
        (Q.obj (CochainComplex.mappingCone (f ^ (n + 1) • 𝟙 D))) ⟶
        cokernel (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1))),
      (homologyFunctor (ModuleCat.{v} A) p).map
          (Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 D))) ≫ q =
        (CompletionSequences.singleHomology A p M).hom ≫
          cokernel.π (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1))) ∧
      (homologyFunctor (ModuleCat.{v} A) p).map (completionConeProjection f c D n) ≫ q =
        (s.singleIso M p p 0 (by omega)).hom ≫ seq.projection ≫
          limit.π (CompletionSequences.powerQuotientSystem A M f) ⟨n⟩ := by
  dsimp only
  let H := homologyFunctor (ModuleCat.{v} A)
  let F := completion ⋙ P.ι
  let C := CompletionSequences.moduleComplex A M
  let D := (CochainComplex.singleFunctor (ModuleCat.{v} A) p).obj M
  let m := -p
  let d := ((CochainComplex.singleFunctors (ModuleCat.{v} A)).shiftIso m p 0 (by
    dsimp [m]
    omega)).app M
  let e := Q.mapIso d
  let g := d.hom
  let a := Q.map ((principalComplexSystemMap f g).app ⟨n⟩)
  have : IsIso (Functor.whiskerRight (principalComplexSystemMap f g) Q) :=
    principalComplexSystemMap_isIso f g
  have : IsIso a := inferInstanceAs (IsIso
    ((Functor.whiskerRight (principalComplexSystemMap f g) Q).app ⟨n⟩))
  let β := inv a ≫ (principalConeShiftIso f C m n).hom
  let U := Q.obj (CochainComplex.mappingCone (f ^ (n + 1) • 𝟙 C))
  let hs := ((H 0).shiftIso m p 0 (by dsimp [m]; omega)).hom
  have he : ((singleFunctors (ModuleCat.{v} A)).shiftIso m p 0 (by dsimp [m]; omega)).inv.app M =
      e.inv ≫ (Q.commShiftIso m).hom.app C := by
    simp only [DerivedCategory.singleFunctors, SingleFunctors.postcomp_shiftIso_inv_app]
    rfl
  have hi : Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 D)) ≫ β =
      e.inv ≫ (Q.commShiftIso m).hom.app C ≫
        (Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C)))⟦m⟧' := by
    have hm : e.hom ≫ Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 D)) =
        Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 (C⟦m⟧))) ≫ a := by
      have hh := (congrArg Q.map (principalComplexSystemMap_inr f g n)).symm
      simp only [Functor.map_comp] at hh
      exact hh
    have hh := (Iso.inv_comp_eq e).2 hm.symm
    dsimp only [β]
    rw [← hh]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [principalConeShiftIso_inr]
  have hc : completionConeProjection f c D n ≫ β =
      F.map e.inv ≫ F.map ((Q.commShiftIso m).hom.app C) ≫
      (s.iso (Q.obj C) m).hom ≫ (completionConeProjection f c C n)⟦m⟧' := by
    have hm : F.map e.hom ≫ completionConeProjection f c D n =
        completionConeProjection f c (C⟦m⟧) n ≫ a := completionConeProjection_map f adj c g n
    have hh := (Iso.inv_comp_eq (F.mapIso e)).2 hm.symm
    dsimp only [β]
    rw [← hh]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    have hshift := completionConeProjection_shift f adj c s C m n
    simpa only [Category.assoc, Functor.mapIso_inv, completionConeProjection] using
      congrArg (F.map e.inv ≫ ·) hshift
  have hsingle := singleHomology_shift M m p 0 (by dsimp [m]; omega)
  rw [he] at hsingle
  simp only [Functor.map_comp, Category.assoc] at hsingle
  have hcomp : (s.singleIso M p p 0 (by omega)).hom =
      (H p).map (F.map e.inv ≫ F.map ((Q.commShiftIso m).hom.app C) ≫ (s.iso (Q.obj C) m).hom) ≫
        hs.app (F.obj (Q.obj C)) := by
    change (H p).map (F.map (((singleFunctors (ModuleCat.{v} A)).shiftIso m p 0
      (by dsimp [m]; omega)).inv.app M) ≫ (s.iso (Q.obj C) m).hom) ≫ _ = _
    rw [he, Functor.map_comp]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hquo : (H 0).map (Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C))) ≫
      seq.quotientIso.hom.app ⟨n⟩ =
      (CompletionSequences.singleHomology A 0 M).hom ≫
        cokernel.π (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1))) :=
    (Iso.inv_comp_eq _).1 (seq.π_quotientIso n)
  have hproj : seq.projection ≫ limit.π (CompletionSequences.powerQuotientSystem A M f) ⟨n⟩ =
      (H 0).map (completionConeProjection f c C n) ≫ seq.quotientIso.hom.app ⟨n⟩ := by
    rw [seq.projection_π]
    simp only [completionConeProjection, principalConeProjection, Functor.map_comp, Category.assoc]
    rfl
  refine ⟨(H p).map β ≫ hs.app U ≫ seq.quotientIso.hom.app ⟨n⟩, ?_, ?_⟩
  · rw [← Functor.map_comp_assoc, hi]
    simp only [Functor.map_comp, Category.assoc]
    erw [hs.naturality_assoc]
    erw [hquo, reassoc_of% hsingle]
    rfl
  · rw [← Functor.map_comp_assoc, hc]
    simp only [Functor.map_comp, Category.assoc]
    erw [hs.naturality_assoc]
    rw [hproj, hcomp]
    simp only [Functor.map_comp, Category.assoc]
    repeat' erw [hs.naturality_assoc]
    rfl
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem completionConeProjection_naturality
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (C D : CochainComplex (ModuleCat.{v} A) ℤ) (g : Q.obj C ⟶ Q.obj D) (n : ℕ) :
    ∃ ψ : Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C)) ⟶
        Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 D)),
      ψ.hom₁ = g ∧ ψ.hom₂ = g ∧
      (completion ⋙ P.ι).map g ≫ completionConeProjection f c D n =
        completionConeProjection f c C n ≫ ψ.hom₃ := by
  obtain ⟨α, φ, ψ, hψ₁, hψ₂, hψ₃, hφ₂, hφ₃, hc⟩ :=
    principalTriangles_naturality f adj c C D g
  refine ⟨ψ n, hψ₁ n, hψ₂ n, ?_⟩
  simp only [completionConeProjection, principalConeProjection, Functor.map_comp, Category.assoc]
  change (completion ⋙ P.ι).map g ≫ (c.iso D).hom ≫
      (CompletionSequences.milnorTriangle A (PrincipalTorsionTower.principalComplexSystem A f
        D)).mor₁ ≫ _ =
    (c.iso C).hom ≫ (CompletionSequences.milnorTriangle A
      (PrincipalTorsionTower.principalComplexSystem A f C)).mor₁ ≫ _
  rw [← Category.assoc, hc, Category.assoc, ← Category.assoc φ.hom₁,
    ← φ.comm₁, Category.assoc, hφ₂, hψ₃]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem completionConeProjection_truncation
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (s : CompletionSequences.CompletionShift A (completion ⋙ P.ι) adj.unit)
    (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ)
    (t : CompletionSequences.TruncationIdentifications A (completion ⋙ P.ι) K p)
    (seq : CompletionSequences.ModuleCompletionSequence A f (completion ⋙ P.ι) adj.unit c
      ((homologyFunctor (ModuleCat.{v} A) p).obj K))
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (eK : Q.obj C ≅ K) (n : ℕ)
    (i : cokernel (PrincipalTorsionTower.powerMultiplication A ((homologyFunctor (ModuleCat.{v} A)
      p).obj K)
        (f ^ (n + 1))) ⟶ (homologyFunctor (ModuleCat.{v} A) p).obj
          (Q.obj (CochainComplex.mappingCone (f ^ (n + 1) • 𝟙 C))))
    (hi : cokernel.π (PrincipalTorsionTower.powerMultiplication A ((homologyFunctor (ModuleCat.{v}
      A) p).obj K)
      (f ^ (n + 1))) ≫ i = (homologyFunctor (ModuleCat.{v} A) p).map
        (eK.inv ≫ Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C)))) :
    t.inclusion s ≫ (homologyFunctor (ModuleCat.{v} A) p).map ((completion ⋙ P.ι).map eK.inv) ≫
      (homologyFunctor (ModuleCat.{v} A) p).map (completionConeProjection f c C n) =
    seq.projection ≫ limit.π (CompletionSequences.powerQuotientSystem A
      ((homologyFunctor (ModuleCat.{v} A) p).obj K) f) ⟨n⟩ ≫ i := by
  let H := homologyFunctor (ModuleCat.{v} A)
  let F := completion ⋙ P.ι
  let M := (H p).obj K
  let L := (CompletionSequences.truncLE A p).obj K
  let CL := Q.objPreimage L
  let eL := Q.objObjPreimageIso L
  let ι := (CompletionSequences.truncIn A p).app K
  let lam := (CompletionSequences.truncOut A p).app L ≫ t.lower.hom
  let D := (CochainComplex.singleFunctor (ModuleCat.{v} A) p).obj M
  let gK := eL.hom ≫ ι ≫ eK.inv
  let gD := eL.hom ≫ lam
  obtain ⟨qD, hqD, hρD⟩ := completionConeProjection_single f adj c s M seq p n
  obtain ⟨ψK, hψK₁, hψK₂, hK⟩ := completionConeProjection_naturality f adj c CL C gK n
  obtain ⟨ψD, hψD₁, hψD₂, hD⟩ := completionConeProjection_naturality f adj c CL D gD n
  have hl : (H p).map gD ≫ (CompletionSequences.singleHomology A p M).hom =
      (H p).map (eL.hom ≫ ι) := by
    dsimp only [gD, lam]
    simp only [Functor.map_comp, Category.assoc]
    rw [t.lower_homology]
  let TL := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 CL))
  have hz : IsZero ((H (p + 1)).obj TL.obj₁) :=
    IsZero.of_iso (DerivedCategory.isZero_of_isLE L p (p + 1) (by omega)) ((H (p + 1)).mapIso eL)
  have : Epi ((H p).map TL.mor₂) :=
    ((H 0).homologySequence_exact₃ TL (mappingCone_triangle_distinguished _) p (p + 1) rfl).epi_f
      (hz.eq_of_tgt _ _)
  have hα : (H p).map ψK.hom₃ = (H p).map ψD.hom₃ ≫ qD ≫ i := by
    apply (cancel_epi ((H p).map TL.mor₂)).1
    rw [← Functor.map_comp, ← Functor.map_comp_assoc, ψK.comm₂, ψD.comm₂, hψK₂, hψD₂]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% hqD, hi, reassoc_of% hl]
    simp only [gK, Functor.map_comp, Category.assoc]
    rfl
  let u := (H p).map (F.map gD) ≫ (s.singleIso M p p 0 (by omega)).hom
  have : IsIso ((H p).map (F.map gD)) := by
    dsimp only [gD]
    simp only [Functor.map_comp]
    infer_instance
  have : IsIso u := inferInstance
  have hu : u ≫ t.inclusion s = (H p).map (F.map (eL.hom ≫ ι)) := by
    dsimp only [u, gD]
    simp only [Functor.map_comp, Category.assoc]
    rw [t.inclusion_truncIn s]
  have hleft : u ≫ t.inclusion s ≫ (H p).map (F.map eK.inv) ≫
      (H p).map (completionConeProjection f c C n) =
      (H p).map (completionConeProjection f c CL n) ≫ (H p).map ψK.hom₃ := by
    rw [reassoc_of% hu]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
    rw [Category.assoc eL.hom ι eK.inv]
    change (H p).map (F.map gK ≫ completionConeProjection f c C n) = _
    rw [hK, Functor.map_comp]
  have hright : u ≫ seq.projection ≫ limit.π (CompletionSequences.powerQuotientSystem A M f) ⟨n⟩ ≫ i
    =
      (H p).map (completionConeProjection f c CL n) ≫ (H p).map ψD.hom₃ ≫ qD ≫ i := by
    dsimp only [u]
    rw [Category.assoc, ← reassoc_of% hρD]
    rw [← Functor.map_comp_assoc, hD, Functor.map_comp, Category.assoc]
  apply (cancel_epi u).1
  simpa only [Category.assoc] using
    (hleft.trans (congrArg ((H p).map (completionConeProjection f c CL n) ≫ ·) hα)).trans
      hright.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_epi_of_epi_epi_mono
    {C : Type u} [Category.{v} C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type*} [Category D] [Abelian D]
    (H : C ⥤ D) [H.IsHomological] [H.ShiftSequence ℤ]
    {T U : Triangle C} (ψ : T ⟶ U) (hT : T ∈ distTriang C) (hU : U ∈ distTriang C)
    (a b : ℤ) (hab : a + 1 = b)
    [Epi ((H.shift a).map ψ.hom₂)] [Epi ((H.shift b).map ψ.hom₁)]
    [Mono ((H.shift b).map ψ.hom₂)] : Epi ((H.shift a).map ψ.hom₃) := by
  let R := ComposableArrows.mk₃ ((H.shift a).map T.mor₂)
    (H.homologySequenceδ T a b hab) ((H.shift b).map T.mor₁)
  let S := ComposableArrows.mk₃ ((H.shift a).map U.mor₂)
    (H.homologySequenceδ U a b hab) ((H.shift b).map U.mor₁)
  let φ : R ⟶ S := ComposableArrows.homMk₃
    ((H.shift a).map ψ.hom₂) ((H.shift a).map ψ.hom₃)
    ((H.shift b).map ψ.hom₁) ((H.shift b).map ψ.hom₂)
    (by change (H.shift a).map T.mor₂ ≫ (H.shift a).map ψ.hom₃ =
          (H.shift a).map ψ.hom₂ ≫ (H.shift a).map U.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, ψ.comm₂])
    (H.homologySequenceδ_naturality ψ a b hab).symm
    (by change (H.shift b).map T.mor₁ ≫ (H.shift b).map ψ.hom₂ =
          (H.shift b).map ψ.hom₁ ≫ (H.shift b).map U.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, ψ.comm₁])
  exact Abelian.epi_of_epi_of_epi_of_mono' φ
    (H.homologySequence_exact₁ T hT a b hab).exact_toComposableArrows
    (H.homologySequence_exact₃ U hU a b hab).exact_toComposableArrows
    (H.homologySequenceδ_comp U hU a b hab)
    (by dsimp [φ, R, S]; infer_instance) (by dsimp [φ, R, S]; infer_instance)
    (by dsimp [φ, R, S]; infer_instance)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem mappingCoconeShiftIso_hom_mor₃
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (d : K ⟶ L) (m : ℤ) :
    (CochainComplex.mappingCocone.triangle d).mor₃⟦m⟧' ≫
      (shiftFunctorComm (CochainComplex C ℤ) 1 m).hom.app (CochainComplex.mappingCocone d) ≫
      (mappingCoconeShiftIso d m).hom⟦(1 : ℤ)⟧' =
    m.negOnePow • (CochainComplex.mappingCocone.triangle (d⟦m⟧')).mor₃ := by
  ext p
  simp only [CochainComplex.mappingCocone.triangle, CochainComplex.mappingCocone, Int.reduceNeg,
    CochainComplex.mappingCone.triangle, Triangle.mk_obj₃, Triangle.mk_mor₂, shiftFunctorCompIsoId,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.id_obj, Functor.comp_obj,
    CochainComplex.shiftFunctor_obj_X', Triangle.mk_obj₁, Triangle.mk_mor₃, Functor.map_comp,
    mappingCoconeShiftIso, CochainComplex.mappingCone.shiftIso, smul_iso_hom, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_units_smul, comp_units_smul, Category.assoc,
    HomologicalComplex.units_smul_f_apply, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorZero_inv_app_f,
    HomologicalComplex.XIsoOfEq, eqToIso, CochainComplex.shiftFunctorAdd'_hom_app_f',
    CochainComplex.shiftFunctorComm_hom_app_f, eqToHom_trans_assoc, add_comm, add_assoc,
    add_neg_cancel, add_zero, eqToHom_naturality_assoc, eqToHom_trans, eqToHom_naturality,
    smul_left_cancel_iff]
  congr 1
  exact congrArg (fun k => k.f (p + 1 + -1)) (CompletionSequences.coneShiftIso_hom_inr d m)
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalCompletionShiftMap_connecting
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) :
    (CochainComplex.mappingCocone.triangle
      (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
        C))).mor₃⟦m⟧' ≫
      (shiftFunctorComm (CochainComplex (ModuleCat.{v} A) ℤ) 1 m).hom.app _ ≫
      (principalCompletionShiftMap f C m)⟦(1 : ℤ)⟧' =
    m.negOnePow • (principalProductShiftMap f C m ≫
      (CochainComplex.mappingCocone.triangle
        (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
          (C⟦m⟧)))).mor₃) := by
  dsimp only [principalCompletionShiftMap]
  rw [Functor.map_comp]
  erw [reassoc_of% mappingCoconeShiftIso_hom_mor₃
    (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f C))
      m]
  rw [Linear.units_smul_comp]
  congr 1
  have h := (mappingCoconeTriangleMap _ _ (principalProductShiftMap f C m)
    (principalProductShiftMap f C m) (principalProductShiftMap_difference f C m)).comm₃.symm
  rw [mappingCoconeTriangleMap_hom₃] at h
  exact h.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private abbrev milnorConnecting
    {A : Type u} [CommRing A] (f : A)
    {F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A)}
    {η : 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F}
    (c : CompletionSequences.CompletionComparison A f F η)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (a b : ℤ) (hab : a + 1 = b) :=
  (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
    (CompletionSequences.milnorTriangle A (PrincipalTorsionTower.principalComplexSystem A f C)) a b
      hab ≫
      (homologyFunctor (ModuleCat.{v} A) b).map (c.iso C).inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem milnorConnecting_naturality
    {A : Type u} [CommRing A] (f : A)
    {F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A)}
    {η : 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F}
    (c : CompletionSequences.CompletionComparison A f F η)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} (g : Q.obj C ⟶ Q.obj D)
    (φ : CompletionSequences.milnorTriangle A (PrincipalTorsionTower.principalComplexSystem A f C) ⟶
      CompletionSequences.milnorTriangle A (PrincipalTorsionTower.principalComplexSystem A f D))
    (hc : F.map g ≫ (c.iso D).hom = (c.iso C).hom ≫ φ.hom₁)
    (a b : ℤ) (hab : a + 1 = b) :
    (homologyFunctor (ModuleCat.{v} A) a).map φ.hom₃ ≫ milnorConnecting f c D a b hab =
      milnorConnecting f c C a b hab ≫ (homologyFunctor (ModuleCat.{v} A) b).map (F.map g) := by
  have hh : φ.hom₁ ≫ (c.iso D).inv = (c.iso C).inv ≫ F.map g := by
    apply (cancel_epi (c.iso C).hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp only [milnorConnecting]
  erw [← Category.assoc, (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ_naturality]
  simp only [Category.assoc]
  congr 1
  change (homologyFunctor (ModuleCat.{v} A) b).map φ.hom₁ ≫
    (homologyFunctor (ModuleCat.{v} A) b).map (c.iso D).inv = _
  rw [← Functor.map_comp, hh, Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem milnorConnecting_eq
    {A : Type u} [CommRing A] (f : A)
    {F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A)}
    {η : 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F}
    (c : CompletionSequences.CompletionComparison A f F η)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (a b : ℤ) (hab : a + 1 = b) :
    milnorConnecting f c C a b hab =
      (homologyFunctorFactors (ModuleCat.{v} A) a).hom.app _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingCocone.triangle
          (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
            C))).mor₃ a b (by omega) ≫
      (homologyFunctorFactors (ModuleCat.{v} A) b).inv.app _ ≫
      (homologyFunctor (ModuleCat.{v} A) b).map (c.iso C).inv := by
  have h := shiftMap_homologyFunctor_map_Q
    (CochainComplex.mappingCocone.triangle
      (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
        C))).mor₃ a b (by omega)
  simpa only [milnorConnecting, CompletionSequences.milnorTriangle, Functor.mapTriangle,
    Triangle.mk, Functor.homologySequenceδ, Functor.shiftMap, ShiftedHom.map,
    Functor.map_comp, Category.assoc] using
    congrArg (fun k => k ≫ (homologyFunctor (ModuleCat.{v} A) b).map (c.iso C).inv) h

end PrincipalCompletionDiagram
end

end
