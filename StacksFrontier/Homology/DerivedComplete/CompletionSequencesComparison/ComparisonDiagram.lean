module

public import StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.BoundaryMaps
import all StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.ShortExactSequences
import all StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.ShiftCompatibility
import all StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.BoundaryMaps

/-!
# Comparison of completions at a principal ideal: the diagram

This part proves the compatibility of the Milnor connecting map with shifts, single complexes
and truncations, assembles the solution of the comparison diagram, and proves
`PrincipalCompletionDiagram.derivedCompletion_principal_homology_comparison`
(**Stacks 0H32**): the commutative diagram of four short exact sequences comparing ordinary
and derived completion at `(f)`.
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

/-- `shiftMap` of the homology functor commutes with a sign scalar. -/
private theorem shiftMap_negOnePow_smul {A : Type u} [CommRing A] (m a b : ℤ) (hab : 1 + a = b)
    {X Y : CochainComplex (ModuleCat.{v} A) ℤ} (k : X ⟶ Y⟦(1 : ℤ)⟧) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) 0).shiftMap
        (m.negOnePow • k) a b hab =
      m.negOnePow • (HomologicalComplex.homologyFunctor (ModuleCat.{v} A)
        (ComplexShape.up ℤ) 0).shiftMap k a b hab := by
  dsimp only [Functor.shiftMap]
  erw [show (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) a).map
      (m.negOnePow • k) = m.negOnePow • (HomologicalComplex.homologyFunctor (ModuleCat.{v} A)
        (ComplexShape.up ℤ) a).map k from map_zsmul_unit (HomologicalComplex.homologyFunctor
          (ModuleCat.{v} A) (ComplexShape.up ℤ) a).mapAddHom _ _, Linear.units_smul_comp]
  rfl

/-- Compatibility of the homology functor shift isomorphisms with `Q.commShiftIso`. -/
private theorem homologyFunctorFactors_inv_commShift_shiftIso
    {A : Type u} [CommRing A] (X : CochainComplex (ModuleCat.{v} A) ℤ) (m b b' : ℤ)
    (hb : m + b = b') :
    (homologyFunctorFactors (ModuleCat.{v} A) b).inv.app (X⟦m⟧) ≫
      (homologyFunctor (ModuleCat.{v} A) b).map ((Q.commShiftIso m).hom.app X) ≫
      ((homologyFunctor (ModuleCat.{v} A) 0).shiftIso m b b' hb).hom.app (Q.obj X) =
    ((HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) 0).shiftIso
      m b b' hb).hom.app X ≫ (homologyFunctorFactors (ModuleCat.{v} A) b').inv.app X := by
  set_option backward.isDefEq.respectTransparency false in
  rw [homologyShiftIso_hom_app_Q_obj]
  simp only [Iso.inv_hom_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem milnorConnecting_shift
    {A : Type u} [CommRing A] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (s : CompletionSequences.CompletionShift A (completion ⋙ P.ι) adj.unit)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m a b a' b' : ℤ)
    (hab : a + 1 = b) (ha : m + a = a') (hb : m + b = b') :
    let X := CompletionSequences.complexProduct A (PrincipalTorsionTower.principalComplexSystem A f
      C)
    (homologyFunctor (ModuleCat.{v} A) a).map (Q.map (principalProductShiftMap f C m)) ≫
      milnorConnecting f c (C⟦m⟧) a b hab ≫
      (homologyFunctor (ModuleCat.{v} A) b).map
        ((completion ⋙ P.ι).map ((Q.commShiftIso m).hom.app C) ≫ (s.iso (Q.obj C) m).hom) ≫
      ((homologyFunctor (ModuleCat.{v} A) 0).shiftIso m b b' hb).hom.app
        ((completion ⋙ P.ι).obj (Q.obj C)) =
    m.negOnePow • ((homologyFunctor (ModuleCat.{v} A) a).map ((Q.commShiftIso m).hom.app X) ≫
      ((homologyFunctor (ModuleCat.{v} A) 0).shiftIso m a a' ha).hom.app (Q.obj X) ≫
      milnorConnecting f c C a' b' (by omega)) := by
  dsimp only
  let H := homologyFunctor (ModuleCat.{v} A)
  let HC := HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ)
  let F := completion ⋙ P.ι
  let E := PrincipalTorsionTower.principalComplexSystem A f C
  let B := CochainComplex.mappingCocone (CompletionSequences.complexDifference A E)
  let κ : CompletionSequences.complexProduct A E ⟶ B⟦(1 : ℤ)⟧ :=
    (CochainComplex.mappingCocone.triangle (CompletionSequences.complexDifference A E)).mor₃
  let V := F.map ((Q.commShiftIso m).hom.app C) ≫ (s.iso (Q.obj C) m).hom
  have hv : Q.map (principalCompletionShiftMap f C m) ≫ (c.iso (C⟦m⟧)).inv ≫ V =
      (Q.commShiftIso m).hom.app B ≫ ((c.iso C).inv)⟦m⟧' := by
    have hc := completionComparison_shift f adj c s C m
    apply (cancel_epi (V ≫ ((c.iso C).hom)⟦m⟧' ≫ (Q.commShiftIso m).inv.app B)).1
    have hc' : (V ≫ ((c.iso C).hom)⟦m⟧' ≫ (Q.commShiftIso m).inv.app B) ≫
        Q.map (principalCompletionShiftMap f C m) = (c.iso (C⟦m⟧)).hom := by
      simpa only [V, Category.assoc] using hc
    rw [← Category.assoc _ (Q.map (principalCompletionShiftMap f C m)), hc']
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  have hk := principalCompletionShiftMap_connecting f C m
  have hd : (HC 0).shiftMap (n := (1 : ℤ)) (κ⟦m⟧' ≫
        (shiftFunctorComm (CochainComplex (ModuleCat.{v} A) ℤ) 1 m).hom.app B) a b (by omega) ≫
      (HC b).map (principalCompletionShiftMap f C m) =
      m.negOnePow • ((HC a).map (principalProductShiftMap f C m) ≫
        (HC 0).shiftMap (CochainComplex.mappingCocone.triangle
          (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
            (C⟦m⟧)))).mor₃ a b (by omega)) := by
    erw [← (HC 0).shiftMap_comp]
    erw [hk]
    rw [shiftMap_negOnePow_smul, (HC 0).shiftMap_comp']
    rfl
  have hd' := congrArg (m.negOnePow • ·) hd
  simp only [smul_smul, Int.units_mul_self, one_smul] at hd'
  rw [milnorConnecting_eq, milnorConnecting_eq]
  rw [reassoc_of% homologyShiftIso_hom_app_Q_obj _ m a a' ha]
  simp only [Category.assoc]
  erw [(homologyFunctorFactors (ModuleCat.{v} A) a).hom.naturality_assoc]
  rw [reassoc_of% hd'.symm]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul]
  congr 1
  simp only [Category.assoc]
  erw [(homologyFunctorFactors (ModuleCat.{v} A) b).inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  erw [hv]
  simp only [Functor.map_comp, Category.assoc]
  erw [((H 0).shiftIso m b b' hb).hom.naturality]
  rw [reassoc_of% homologyFunctorFactors_inv_commShift_shiftIso B m b b' hb]
  rw [reassoc_of% shiftMap_shift (HC 0) κ m a b a' b' hab ha hb]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem coneHomologyBoundary_shift
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m a b a' b' : ℤ)
    (hab : a + 1 = b) (ha : m + a = a') (hb : m + b = b') (n : ℕ) :
    let T := CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C)
    let U := CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 (C⟦m⟧))
    (homologyFunctor (ModuleCat.{v} A) a).map
      (Q.map (CochainComplex.mappingCone.shiftIso (f ^ (n + 1) • 𝟙 C) m).hom) ≫
      (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ (Q.mapTriangle.obj U) a b hab ≫
      (homologyFunctor (ModuleCat.{v} A) b).map ((Q.commShiftIso m).hom.app C) ≫
      ((homologyFunctor (ModuleCat.{v} A) 0).shiftIso m b b' hb).hom.app (Q.obj C) =
    m.negOnePow • ((homologyFunctor (ModuleCat.{v} A) a).map ((Q.commShiftIso m).hom.app T.obj₃) ≫
      ((homologyFunctor (ModuleCat.{v} A) 0).shiftIso m a a' ha).hom.app (Q.obj T.obj₃) ≫
      (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ (Q.mapTriangle.obj T) a' b' (by
        omega)) := by
  dsimp only
  let H := homologyFunctor (ModuleCat.{v} A)
  let HC := HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ)
  let T := CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C)
  let U := CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 (C⟦m⟧))
  have hc := CompletionSequences.coneShiftIso_hom_mor₃ (f ^ (n + 1) • 𝟙 C) m
  have heq (V : Triangle (CochainComplex (ModuleCat.{v} A) ℤ)) (x y : ℤ) (hxy : x + 1 = y) :
      (H 0).homologySequenceδ (Q.mapTriangle.obj V) x y hxy =
      (homologyFunctorFactors (ModuleCat.{v} A) x).hom.app V.obj₃ ≫
        (HC 0).shiftMap V.mor₃ x y (by omega) ≫
        (homologyFunctorFactors (ModuleCat.{v} A) y).inv.app V.obj₁ :=
    shiftMap_homologyFunctor_map_Q V.mor₃ x y (by omega)
  rw [heq U a b hab, heq T a' b' (by omega)]
  simp only [Category.assoc]
  erw [(homologyFunctorFactors (ModuleCat.{v} A) a).hom.naturality_assoc]
  erw [← (HC 0).shiftMap_comp'_assoc, hc]
  rw [shiftMap_negOnePow_smul]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul]
  congr 1
  erw [homologyFunctorFactors_inv_commShift_shiftIso C m b b' hb]
  erw [reassoc_of% shiftMap_shift (HC 0) T.mor₃ m a b a' b' hab ha hb]
  rw [reassoc_of% homologyShiftIso_hom_app_Q_obj T.obj₃ m a a' ha]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem homologyMap_truncLEι_isIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (p a : ℤ) (ha : a ≤ p) :
    IsIso ((homologyFunctor C a).map ((TStructure.t.truncLEι p).app K)) := by
  let T := (TStructure.t.triangleLEGE p (p + 1) rfl).obj K
  have ht := TStructure.t.triangleLEGE_distinguished p (p + 1) rfl K
  have : T.obj₃.IsGE (p + 1) := by
    show ((TStructure.t.truncGE (p + 1)).obj K).IsGE (p + 1)
    infer_instance
  have hz : IsZero ((homologyFunctor C a).obj T.obj₃) :=
    DerivedCategory.isZero_of_isGE T.obj₃ (p + 1) a (by omega)
  have hz' : IsZero ((homologyFunctor C (a - 1)).obj T.obj₃) :=
    DerivedCategory.isZero_of_isGE T.obj₃ (p + 1) (a - 1) (by omega)
  have : Epi ((homologyFunctor C a).map T.mor₁) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff T ht a).2 (hz.eq_of_tgt _ _)
  have : Mono ((homologyFunctor C a).map T.mor₁) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
      T ht (a - 1) a (by omega)).2 (hz'.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((homologyFunctor C a).map T.mor₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem piMap_epi
    {C : Type*} [Category C] [Abelian C] [HasProductsOfShape ℕ C]
    [HasExactLimitsOfShape (Discrete ℕ) C]
    {X Y : ℕ → C} (f : ∀ n, X n ⟶ Y n) [∀ n, Epi (f n)] : Epi (Limits.Pi.map f) := by
  let α : Discrete.functor X ⟶ Discrete.functor Y := Discrete.natTrans (fun n ↦ f n.as)
  have : ∀ n : Discrete ℕ, Epi (α.app n) := fun n ↦ inferInstanceAs (Epi (f n.as))
  have : Epi α := NatTrans.epi_of_epi_app α
  show Epi (lim.map α)
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem homologyProductMap_epi
    {A : Type u} [CommRing A]
    {E D : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ}
    (g : Q.obj (CompletionSequences.complexProduct A E) ⟶ Q.obj (CompletionSequences.complexProduct
      A D))
    (α : ∀ n : ℕ, Q.obj (E.obj ⟨n⟩) ⟶ Q.obj (D.obj ⟨n⟩))
    (hg : ∀ n : ℕ, g ≫ Q.map (Pi.π (fun n : ℕ ↦ D.obj ⟨n⟩) n) =
      Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n) ≫ α n)
    (p : ℤ) [∀ n, Epi ((homologyFunctor (ModuleCat.{v} A) p).map (α n))] :
    Epi ((homologyFunctor (ModuleCat.{v} A) p).map g) := by
  let H := homologyFunctor (ModuleCat.{v} A) p
  have : PreservesLimitsOfShape (Discrete ℕ) (Q ⋙ H) := by
    have := Stacks.DerivedProducts.preservesLimitsOfShape_homologyFunctor
      (A := ModuleCat.{v} A) (I := ℕ) p
    exact preservesLimitsOfShape_of_natIso (homologyFunctorFactors (ModuleCat.{v} A) p).symm
  let eE := asIso (piComparison (Q ⋙ H) (fun n : ℕ ↦ E.obj ⟨n⟩))
  let eD := asIso (piComparison (Q ⋙ H) (fun n : ℕ ↦ D.obj ⟨n⟩))
  let a := Limits.Pi.map (fun n : ℕ ↦ H.map (α n))
  have ha : Epi a := piMap_epi _
  have heq : H.map g ≫ eD.hom = eE.hom ≫ a := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, a]
    erw [piComparison_comp_π, Pi.map_π, piComparison_comp_π_assoc]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp, hg]
  have heq' : H.map g = eE.hom ≫ a ≫ eD.inv := (Iso.eq_comp_inv eD).2 heq
  rw [heq']
  infer_instance

-- The product and shift comparisons require elaborating several large functor composites.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem milnorConnecting_single_shift
    {A : Type u} [CommRing A] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (s : CompletionSequences.CompletionShift A (completion ⋙ P.ι) adj.unit)
    (M : ModuleCat.{v} A) (seq : CompletionSequences.ModuleCompletionSequence A f
      (completion ⋙ P.ι) adj.unit c M) (p : ℤ) :
    let C := CompletionSequences.moduleComplex A M
    let D := C⟦-p⟧
    let e : Q.obj D ≅ (CompletionSequences.single A p).obj M := (Q.commShiftIso (-p)).app C ≪≫
      ((singleFunctors (ModuleCat.{v} A)).shiftIso (-p) p 0 (by omega)).app M
    ∃ q : (homologyFunctor (ModuleCat.{v} A) (p - 1)).obj
        (Q.obj (CompletionSequences.complexProduct A (PrincipalTorsionTower.principalComplexSystem A
          f D))) ⟶
        CompletionSequences.moduleProduct A (PrincipalTorsionTower.powerTorsionSystem A M f),
      (∀ n : ℕ, q ≫ Pi.π _ n ≫
          kernel.ι (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1))) =
        (homologyFunctor (ModuleCat.{v} A) (p - 1)).map
          (Q.map (Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f D).obj ⟨n⟩)
            n)) ≫
        (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
          (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 D)))
          (p - 1) p (by omega) ≫
        (homologyFunctor (ModuleCat.{v} A) p).map e.hom ≫ (CompletionSequences.singleHomology A p
          M).hom) ∧
      q ≫ cokernel.π (CompletionSequences.moduleDifference A
        (PrincipalTorsionTower.powerTorsionSystem A M f)) ≫
          seq.inclusion = milnorConnecting f c D (p - 1) p (by omega) ≫
        (homologyFunctor (ModuleCat.{v} A) p).map ((completion ⋙ P.ι).map e.hom) ≫
        (s.singleIso M p p 0 (by omega)).hom := by
  dsimp only
  let H := homologyFunctor (ModuleCat.{v} A)
  let F := completion ⋙ P.ι
  let C := CompletionSequences.moduleComplex A M
  let D := C⟦-p⟧
  let d := ((singleFunctors (ModuleCat.{v} A)).shiftIso (-p) p 0 (by omega)).app M
  let e : Q.obj D ≅ (CompletionSequences.single A p).obj M := (Q.commShiftIso (-p)).app C ≪≫ d
  let X := CompletionSequences.complexProduct A (PrincipalTorsionTower.principalComplexSystem A f C)
  let β := (H (p - 1)).map (Q.map (principalProductShiftMap f C (-p)))
  have : IsIso (principalComplexSystemShiftMap f C (-p)) := principalComplexSystemShiftMap_isIso f C
    (-p)
  let : HasLimitsOfSize.{0, 0} (ModuleCat.{v} A) := ModuleCat.hasLimitsOfSize.{0, 0, v, u}
  have hproducts : HasProductsOfShape ℕ (CochainComplex (ModuleCat.{v} A) ℤ) :=
    HomologicalComplex.instHasLimitsOfShape (J := Discrete ℕ)
  have hpres : PreservesLimitsOfShape (Discrete ℕ)
      (shiftFunctor (CochainComplex (ModuleCat.{v} A) ℤ) (-p)) := inferInstance
  have hciso : IsIso (piComparison (shiftFunctor (CochainComplex (ModuleCat.{v} A) ℤ) (-p))
      (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩)) := inferInstance
  have hpiso : IsIso (Limits.Pi.map (fun n : ℕ ↦
      (principalComplexSystemShiftMap f C (-p)).app ⟨n⟩)) :=
    Limits.Pi.map_isIso (C := CochainComplex (ModuleCat.{v} A) ℤ)
      (β := ℕ) (fun n ↦ (principalComplexSystemShiftMap f C (-p)).app ⟨n⟩)
  have : IsIso (principalProductShiftMap f C (-p)) := by
    dsimp only [principalProductShiftMap]
    infer_instance
  have : IsIso β := by dsimp only [β]; infer_instance
  let γ := (H (p - 1)).map ((Q.commShiftIso (-p)).hom.app X) ≫
    ((H 0).shiftIso (-p) (p - 1) (-1) (by omega)).hom.app (Q.obj X)
  let q := (-p).negOnePow • (inv β ≫ γ ≫ seq.productIso.hom)
  have hβ : β ≫ q = (-p).negOnePow • (γ ≫ seq.productIso.hom) := by
    simp only [q, Linear.comp_units_smul, IsIso.hom_inv_id_assoc]
  have he : (H p).map e.hom ≫ (CompletionSequences.singleHomology A p M).hom =
      (H p).map ((Q.commShiftIso (-p)).hom.app C) ≫
      ((H 0).shiftIso (-p) p 0 (by omega)).hom.app (Q.obj C) ≫
      (CompletionSequences.singleHomology A 0 M).hom := by
    have hd : (H p).map d.hom ≫ (CompletionSequences.singleHomology A p M).hom =
        ((H 0).shiftIso (-p) p 0 (by omega)).hom.app (Q.obj C) ≫
        (CompletionSequences.singleHomology A 0 M).hom := by
      apply (cancel_epi ((H p).map d.inv)).1
      rw [← Functor.map_comp_assoc, d.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
      exact (singleHomology_shift M (-p) p 0 (by omega)).symm
    dsimp only [e, Iso.trans_hom]
    rw [Functor.map_comp, Category.assoc, hd]
    rfl
  have hr : (H p).map (F.map e.hom) ≫ (s.singleIso M p p 0 (by omega)).hom =
      (H p).map (F.map ((Q.commShiftIso (-p)).hom.app C) ≫ (s.iso (Q.obj C) (-p)).hom) ≫
      ((H 0).shiftIso (-p) p 0 (by omega)).hom.app (F.obj (Q.obj C)) := by
    show (H p).map (F.map (((Q.commShiftIso (-p)).hom.app C) ≫ d.hom)) ≫
      (H p).map (F.map d.inv ≫ (s.iso (Q.obj C) (-p)).hom) ≫ _ = _
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc, d.hom_inv_id]
    erw [Category.comp_id]
    rfl
  refine ⟨q, ?_, ?_⟩
  · intro n
    apply (cancel_epi β).1
    rw [← Category.assoc β q, hβ]
    simp only [Linear.units_smul_comp, Category.assoc]
    rw [reassoc_of% seq.productIso_π n, seq.torsionIso_ι]
    have hπ : β ≫ (H (p - 1)).map
        (Q.map (Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f D).obj ⟨n⟩) n))
          =
      (H (p - 1)).map (Q.map ((Pi.π
        (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩) n)⟦-p⟧')) ≫
      (H (p - 1)).map (Q.map (CochainComplex.mappingCone.shiftIso (f ^ (n + 1) • 𝟙 C) (-p)).hom) :=
        by
      dsimp only [β]
      rw [← Functor.map_comp, ← Functor.map_comp, principalProductShiftMap_π]
      simp only [Functor.map_comp]
      rfl
    rw [← Category.assoc β, hπ]
    simp only [Category.assoc]
    rw [he]
    rw [reassoc_of% coneHomologyBoundary_shift f C (-p) (p - 1) p (-1) 0
      (by omega) (by omega) (by omega) n]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp]
    congr 1
    dsimp only [γ]
    simp only [Category.assoc]
    erw [← Functor.map_comp_assoc, Q.commShiftIso_hom_naturality]
    rw [(H (p - 1)).map_comp ((Q.commShiftIso (-p)).hom.app X)
      ((Q.map (Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩)
        n))⟦-p⟧')]
    simp only [Category.assoc]
    erw [((H 0).shiftIso (-p) (p - 1) (-1) (by omega)).hom.naturality_assoc]
    rfl
  · apply (cancel_epi β).1
    rw [← Category.assoc β q, hβ]
    simp only [Linear.units_smul_comp, Category.assoc]
    rw [seq.connecting_inclusion]
    rw [hr]
    exact (milnorConnecting_shift f adj c s C (-p) (p - 1) p (-1) 0
      (by omega) (by omega) (by omega)).symm

set_option maxHeartbeats 1000000 in
-- The product and shift comparisons require elaborating several large functor composites.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem milnorConnecting_truncation
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
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (eK : Q.obj C ≅ K)
    (qK : (homologyFunctor (ModuleCat.{v} A) (p - 1)).obj
        (Q.obj (CompletionSequences.complexProduct A (PrincipalTorsionTower.principalComplexSystem A
          f C))) ⟶
      CompletionSequences.moduleProduct A
        (PrincipalTorsionTower.powerTorsionSystem A ((homologyFunctor (ModuleCat.{v} A) p).obj K)
          f))
    (hqK : ∀ n : ℕ, qK ≫ Pi.π _ n ≫ kernel.ι (PrincipalTorsionTower.powerMultiplication A
        ((homologyFunctor (ModuleCat.{v} A) p).obj K) (f ^ (n + 1))) =
      (homologyFunctor (ModuleCat.{v} A) (p - 1)).map
        (Q.map (Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩) n))
          ≫
      (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
        (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C)))
        (p - 1) p (by omega) ≫ (homologyFunctor (ModuleCat.{v} A) p).map eK.hom) :
    milnorConnecting f c C (p - 1) p (by omega) ≫
        (homologyFunctor (ModuleCat.{v} A) p).map ((completion ⋙ P.ι).map eK.hom) =
      qK ≫ cokernel.π (CompletionSequences.moduleDifference A
        (PrincipalTorsionTower.powerTorsionSystem A ((homologyFunctor (ModuleCat.{v} A) p).obj K)
          f)) ≫
        seq.inclusion ≫ t.inclusion s := by
  let H := homologyFunctor (ModuleCat.{v} A)
  let F := completion ⋙ P.ι
  let M := (H p).obj K
  let L := (CompletionSequences.truncLE A p).obj K
  let CL := Q.objPreimage L
  let eL := Q.objObjPreimageIso L
  let ι := (CompletionSequences.truncIn A p).app K
  let lam := (CompletionSequences.truncOut A p).app L ≫ t.lower.hom
  let D := (CompletionSequences.moduleComplex A M)⟦-p⟧
  let eD : Q.obj D ≅ (CompletionSequences.single A p).obj M :=
    (Q.commShiftIso (-p)).app (CompletionSequences.moduleComplex A M) ≪≫
      ((singleFunctors (ModuleCat.{v} A)).shiftIso (-p) p 0 (by omega)).app M
  let gK := eL.hom ≫ ι ≫ eK.inv
  let gD := eL.hom ≫ lam ≫ eD.inv
  obtain ⟨qD, hqD, hcD⟩ := milnorConnecting_single_shift f adj c s M seq p
  obtain ⟨αK, φK, ψK, hψK₁, hψK₂, hψK₃, hφK₂, hφK₃, hcK⟩ :=
    principalTriangles_naturality f adj c CL C gK
  obtain ⟨αD, φD, ψD, hψD₁, hψD₂, hψD₃, hφD₂, hφD₃, hcD'⟩ :=
    principalTriangles_naturality f adj c CL D gD
  have hl : (H p).map gD ≫ (H p).map eD.hom ≫ (CompletionSequences.singleHomology A p M).hom =
      (H p).map (eL.hom ≫ ι) := by
    simp only [gD, lam, Functor.map_comp, Category.assoc]
    rw [← (H p).map_comp_assoc eD.inv eD.hom, eD.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    rw [t.lower_homology]
  have hi (a : ℤ) (ha : a ≤ p) : IsIso ((H a).map gK) := by
    have := homologyMap_truncLEι_isIso K p a ha
    dsimp only [gK]
    simp only [Functor.map_comp]
    infer_instance
  have hαK (n : ℕ) : Epi ((H (p - 1)).map (αK.app ⟨n⟩)) := by
    have := hi (p - 1) (by omega)
    have := hi p le_rfl
    have h₂ : Epi ((H (p - 1)).map (ψK n).hom₂) := by rw [hψK₂]; infer_instance
    have h₁ : Epi ((H p).map (ψK n).hom₁) := by rw [hψK₁]; infer_instance
    have h₂' : Mono ((H p).map (ψK n).hom₂) := by rw [hψK₂]; infer_instance
    have : Epi (((H 0).shift (p - 1)).map (ψK n).hom₂) := h₂
    have : Epi (((H 0).shift p).map (ψK n).hom₁) := h₁
    have : Mono (((H 0).shift p).map (ψK n).hom₂) := h₂'
    rw [← hψK₃]
    exact homologyMap_epi_of_epi_epi_mono (H 0) (ψK n)
      (mappingCone_triangle_distinguished _) (mappingCone_triangle_distinguished _)
      (p - 1) p (by omega)
  have hφ : Epi ((H (p - 1)).map φK.hom₃) :=
    homologyProductMap_epi φK.hom₃ (fun n ↦ αK.app ⟨n⟩) hφK₃ (p - 1)
  have hq : (H (p - 1)).map φK.hom₃ ≫ qK = (H (p - 1)).map φD.hom₃ ≫ qD := by
    apply Pi.hom_ext
    intro n
    apply (cancel_mono (kernel.ι (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1))))).1
    simp only [Category.assoc]
    rw [hqK, hqD]
    rw [← Functor.map_comp_assoc, hφK₃, Functor.map_comp,
      ← Functor.map_comp_assoc, hφD₃, Functor.map_comp]
    simp only [Category.assoc]
    rw [← hψK₃, ← hψD₃]
    erw [(H 0).homologySequenceδ_naturality_assoc (ψK n) (p - 1) p (by omega),
      (H 0).homologySequenceδ_naturality_assoc (ψD n) (p - 1) p (by omega)]
    rw [hψK₁, hψD₁]
    erw [hl]
    simp only [gK, Functor.map_comp, Category.assoc]
    erw [← (H p).map_comp eK.inv eK.hom, eK.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
    rfl
  have hu : (H p).map (F.map gD) ≫ (H p).map (F.map eD.hom) ≫
      (s.singleIso M p p 0 (by omega)).hom ≫ t.inclusion s =
      (H p).map (F.map gK) ≫ (H p).map (F.map eK.hom) := by
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
    simp only [gD, gK, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [Functor.map_comp, Category.assoc]
    rw [t.inclusion_truncIn s]
  apply (cancel_epi ((H (p - 1)).map φK.hom₃)).1
  simp only [Category.assoc]
  rw [reassoc_of% milnorConnecting_naturality f c gK φK hcK (p - 1) p (by omega)]
  rw [reassoc_of% hq]
  rw [reassoc_of% hcD]
  rw [reassoc_of% milnorConnecting_naturality f c gD φD hcD' (p - 1) p (by omega)]
  exact congrArg (milnorConnecting f c CL (p - 1) p (by omega) ≫ ·) hu.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalCompletionDiagramSolution
    (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (f : A) (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) :
    let I : Ideal A := Ideal.span {f}
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun L ↦ IsDerivedComplete I L
    ∀ (completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory)
      (adj : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      ∃ S : CompletionSequences.PrincipalCompletionSequences A f completed adj.unit,
      let H (q : ℤ) := (homologyFunctor (ModuleCat.{v} A) q).obj K
      let C := DerivedCategory.Q.objPreimage K
      let eK := DerivedCategory.Q.objObjPreimageIso K
      let E := PrincipalTorsionTower.principalComplexSystem A f C
      let tensorSystem := principalDerivedTensorSystem A f K
      let homologySystem (q : ℤ) := tensorSystem ⋙ homologyFunctor (ModuleCat.{v} A) q
      let T := CompletionSequences.milnorTriangle A E
      let completionIso := completed.mapIso eK.symm ≪≫ S.comparison.iso C
      let coneTriangle (n : ℕ) := DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C))
      let ordinaryCompletion := limit (CompletionSequences.powerQuotientSystem A (H p) f)
      let limitHpTensor := limit (homologySystem p)
      let tate := CompletionSequences.adicTateModule A (H (p + 1)) f
      let H0CompletedHp := (homologyFunctor (ModuleCat.{v} A) 0).obj
        (completed.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj (H p)))
      let HpCompletedK := (homologyFunctor (ModuleCat.{v} A) p).obj (completed.obj K)
      let R1Torsion := CompletionSequences.firstDerivedLimit A
        (PrincipalTorsionTower.powerTorsionSystem A (H p) f)
      let R1PreviousTensor := CompletionSequences.firstDerivedLimit A (homologySystem (p - 1))
      let middleIn : H0CompletedHp ⟶ HpCompletedK := (S.truncation K p).inclusion S.shift
      let middleOut : HpCompletedK ⟶ tate :=
        (S.truncation K p).projection f S.shift (S.moduleSequence (H (p + 1))).tateIso
      let leftIn : R1Torsion ⟶ H0CompletedHp := (S.moduleSequence (H p)).inclusion
      let leftOut : H0CompletedHp ⟶ ordinaryCompletion := (S.moduleSequence (H p)).projection
      ∃ (termIn : CompletionSequences.powerQuotientSystem A (H p) f ⟶ homologySystem p)
        (termOut : homologySystem p ⟶ PrincipalTorsionTower.powerTorsionSystem A (H (p + 1)) f)
        (previousOut : homologySystem (p - 1) ⟶ PrincipalTorsionTower.powerTorsionSystem A (H p) f)
        (productIso : (homologyFunctor (ModuleCat.{v} A) (p - 1)).obj T.obj₃ ≅
            CompletionSequences.moduleProduct A (homologySystem (p - 1)))
        (topIn : ordinaryCompletion ⟶ limitHpTensor)
        (topOut : limitHpTensor ⟶ tate)
        (htop : topIn ≫ topOut = 0)
        (columnIn : R1PreviousTensor ⟶ HpCompletedK)
        (columnOut : HpCompletedK ⟶ limitHpTensor)
        (hcolumn : columnIn ≫ columnOut = 0)
        (bottom : R1Torsion ≅ R1PreviousTensor),
        (∀ n : ℕ,
          cokernel.π (PrincipalTorsionTower.powerMultiplication A (H p) (f ^ (n + 1))) ≫
              termIn.app ⟨n⟩ =
            (homologyFunctor (ModuleCat.{v} A) p).map (eK.inv ≫ (coneTriangle n).mor₂)) ∧
        (∀ n : ℕ,
          termOut.app ⟨n⟩ ≫
              kernel.ι (PrincipalTorsionTower.powerMultiplication A (H (p + 1)) (f ^ (n + 1))) =
            (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
              (coneTriangle n) p (p + 1) (by omega) ≫
                (homologyFunctor (ModuleCat.{v} A) (p + 1)).map eK.hom) ∧
        (∀ n : ℕ,
          previousOut.app ⟨n⟩ ≫
              kernel.ι (PrincipalTorsionTower.powerMultiplication A (H p) (f ^ (n + 1))) =
            (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
              (coneTriangle n) (p - 1) p (by omega) ≫
                (homologyFunctor (ModuleCat.{v} A) p).map eK.hom) ∧
        (∀ n : ℕ, topIn ≫ limit.π (homologySystem p) ⟨n⟩ =
          limit.π (CompletionSequences.powerQuotientSystem A (H p) f) ⟨n⟩ ≫ termIn.app ⟨n⟩) ∧
        (∀ n : ℕ, topOut ≫ limit.π (PrincipalTorsionTower.powerTorsionSystem A (H (p + 1)) f) ⟨n⟩ =
          limit.π (homologySystem p) ⟨n⟩ ≫ termOut.app ⟨n⟩) ∧
        (∀ n : ℕ, productIso.hom ≫
            Pi.π (fun n : ℕ ↦ (homologySystem (p - 1)).obj ⟨n⟩) n =
          (homologyFunctor (ModuleCat.{v} A) (p - 1)).map
            (DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n))) ∧
        (productIso.hom ≫ cokernel.π (CompletionSequences.moduleDifference A (homologySystem (p -
          1))) ≫
            columnIn = (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ T (p - 1) p
              (by omega) ≫ (homologyFunctor (ModuleCat.{v} A) p).map completionIso.inv) ∧
        (cokernel.π (CompletionSequences.moduleDifference A (homologySystem (p - 1))) ≫ bottom.inv =
          (Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ (homologySystem (p - 1)).obj ⟨n⟩) n ≫
              previousOut.app ⟨n⟩) ≫
            cokernel.π (CompletionSequences.moduleDifference A
              (PrincipalTorsionTower.powerTorsionSystem A (H p) f))) ∧
        (∀ n : ℕ, columnOut ≫ limit.π (homologySystem p) ⟨n⟩ =
          (homologyFunctor (ModuleCat.{v} A) p).map (completionIso.hom ≫ T.mor₁ ≫
            DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n))) ∧
        (ShortComplex.mk topIn topOut htop).ShortExact ∧
        (ShortComplex.mk middleIn middleOut (S.truncation_zero K p)).ShortExact ∧
        (ShortComplex.mk leftIn leftOut (S.moduleSequence (H p)).zero).ShortExact ∧
        (ShortComplex.mk columnIn columnOut hcolumn).ShortExact ∧
        middleIn ≫ columnOut = leftOut ≫ topIn ∧
        middleOut = columnOut ≫ topOut ∧
        bottom.hom ≫ columnIn = leftIn ≫ middleIn := by
  dsimp only
  intro completion adj
  obtain ⟨S, hS⟩ := CompletionSequences.derivedCompletion_principal_homology A f completion adj
  refine ⟨S, ?_⟩
  let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
    fun L ↦ IsDerivedComplete (Ideal.span {f}) L
  let F := completion ⋙ P.ι
  let H := homologyFunctor (ModuleCat.{v} A)
  let C := Q.objPreimage K
  let eK := Q.objObjPreimageIso K
  let E := PrincipalTorsionTower.principalComplexSystem A f C
  let V (q : ℤ) := principalDerivedTensorSystem A f K ⋙ H q
  let T := CompletionSequences.milnorTriangle A E
  let e := F.mapIso eK.symm ≪≫ S.comparison.iso C
  obtain ⟨termIn, termOut, htermIn, htermOut, htermZero, htermExact⟩ :=
    principalCone_shortExact A f C K eK p (p + 1) rfl
  obtain ⟨previousIn, previousOut, hpreviousIn, hpreviousOut, hpreviousZero, hpreviousExact⟩ :=
    principalCone_shortExact A f C K eK (p - 1) p (by omega)
  obtain ⟨productIso, milnorIn, milnorOut, hmilnor, hproduct, hmilnorIn, hmilnorOut,
    hmilnorExact⟩ := milnorTriangle_homology_shortExact A E p
  let topIn := limMap termIn
  let topOut := limMap termOut
  have htop : topIn ≫ topOut = 0 := by
    show lim.map termIn ≫ lim.map termOut = 0
    rw [← Functor.map_comp, htermZero, Functor.map_zero]
  have htopExact : (ShortComplex.mk topIn topOut htop).ShortExact :=
    ShortComplex.shortExact_map_lim_of_isMittagLeffler
      (ShortComplex.mk termIn termOut htermZero) htermExact
      (powerQuotientSystem_isMittagLeffler A ((H p).obj K) f)
  let columnIn := milnorIn ≫ (H p).map e.inv
  let columnOut := (H p).map e.hom ≫ milnorOut
  have hcolumn : columnIn ≫ columnOut = 0 := by
    simp [columnIn, columnOut, ← Functor.map_comp_assoc, hmilnor]
  have hcolumnExact : (ShortComplex.mk columnIn columnOut hcolumn).ShortExact := by
    apply ShortComplex.shortExact_of_iso _ hmilnorExact
    exact ShortComplex.isoMk (Iso.refl _) ((H p).mapIso e.symm) (Iso.refl _)
      (by simp [columnIn]) (by simp [columnOut, ← Functor.map_comp_assoc])
  obtain ⟨_, eQ, _, _, _, _, _, hQ, _⟩ := hS.1 ((H (p - 1)).obj K)
  have hQzero : IsZero (CompletionSequences.firstDerivedLimit A
      (CompletionSequences.powerQuotientSystem A ((H (p - 1)).obj K) f)) :=
    IsZero.of_iso hQ eQ.iso.symm
  have : Epi (CompletionSequences.moduleDifference A
      (CompletionSequences.powerQuotientSystem A ((H (p - 1)).obj K) f)) :=
    epi_of_isZero_cokernel _ hQzero
  let b := cokernel.map (CompletionSequences.moduleDifference A (V (p - 1)))
    (CompletionSequences.moduleDifference A (PrincipalTorsionTower.powerTorsionSystem A ((H p).obj
      K) f))
    (Limits.Pi.map (fun n : ℕ ↦ previousOut.app ⟨n⟩))
    (Limits.Pi.map (fun n : ℕ ↦ previousOut.app ⟨n⟩))
    (moduleDifference_naturality previousOut)
  have : IsIso b := firstDerivedLimit_map_isIso
    (ShortComplex.mk previousIn previousOut hpreviousZero) hpreviousExact
  let bottom := (asIso b).symm
  refine ⟨termIn, termOut, previousOut, productIso, topIn, topOut, htop,
    columnIn, columnOut, hcolumn, bottom, htermIn, htermOut, hpreviousOut,
    ?topInProjection, ?topOutProjection, hproduct, ?columnConnecting, ?bottomNormalization,
    ?columnProjection, htopExact, S.truncation_shortExact K p,
    (S.moduleSequence ((H p).obj K)).shortExact, hcolumnExact,
    ?leftSquare, ?rightSquare, ?bottomSquare⟩
  case topInProjection =>
    intro n
    exact limMap_π termIn ⟨n⟩
  case topOutProjection =>
    intro n
    exact limMap_π termOut ⟨n⟩
  case columnConnecting =>
    show productIso.hom ≫ cokernel.π (CompletionSequences.moduleDifference A (V (p - 1))) ≫
      (milnorIn ≫ (H p).map e.inv) = _
    erw [← Category.assoc _ milnorIn, ← Category.assoc productIso.hom,
      hmilnorIn]
  case bottomNormalization =>
    show cokernel.π (CompletionSequences.moduleDifference A (V (p - 1))) ≫ b = _
    dsimp only [b]
    rw [cokernel.map, cokernel.π_desc]
    congr 1
  case columnProjection =>
    intro n
    show ((H p).map e.hom ≫ milnorOut) ≫ limit.π (V p) ⟨n⟩ = _
    erw [Category.assoc, hmilnorOut]
    exact (Functor.map_comp _ _ _).symm
  case leftSquare =>
    apply limit.hom_ext
    intro n
    have hc : columnOut ≫ limit.π (V p) n =
        (H p).map (F.map eK.inv) ≫
          (H p).map (completionConeProjection f S.comparison C n.unop) := by
      dsimp only [columnOut]
      erw [Category.assoc, hmilnorOut]
      simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        completionConeProjection, principalConeProjection, Functor.map_comp, Category.assoc]
      rfl
    simp only [Category.assoc]
    erw [hc, limMap_π]
    exact completionConeProjection_truncation f adj S.comparison S.shift K p
      (S.truncation K p) (S.moduleSequence ((H p).obj K)) C eK n.unop
      (termIn.app n) (htermIn n.unop)
  case rightSquare =>
    have hcanon (n : ℕ) :
        columnOut ≫ topOut ≫
          limit.π (PrincipalTorsionTower.powerTorsionSystem A ((H (p + 1)).obj K) f) ⟨n⟩ ≫
          kernel.ι (PrincipalTorsionTower.powerMultiplication A ((H (p + 1)).obj K) (f ^ (n + 1))) =
        derivedCompletionBoundary f S.comparison K p (p + 1) rfl n := by
      dsimp only [columnOut, topOut]
      simp only [Category.assoc]
      rw [limMap_π_assoc, htermOut]
      rw [reassoc_of% hmilnorOut n]
      dsimp only [derivedCompletionBoundary, completionConeBoundary, e, Iso.trans_hom,
        Functor.mapIso_hom, Iso.symm_hom]
      simp only [Functor.map_comp, Category.assoc]
      rfl
    apply limit.hom_ext
    intro n
    apply (cancel_mono (kernel.ι (PrincipalTorsionTower.powerMultiplication A
      ((H (p + 1)).obj K) (f ^ (n.unop + 1))))).1
    have ht := derivedCompletionBoundary_projection f adj S.comparison S.shift K p
      (S.truncation K p) (S.moduleSequence ((H (p + 1)).obj K)) n.unop
    simpa only [Category.assoc] using ht.symm.trans (hcanon n.unop).symm
  case bottomSquare =>
    let qK := productIso.hom ≫ Limits.Pi.map (fun n : ℕ ↦ previousOut.app ⟨n⟩)
    have hqK (n : ℕ) : qK ≫ Pi.π _ n ≫
        kernel.ι (PrincipalTorsionTower.powerMultiplication A ((H p).obj K) (f ^ (n + 1))) =
      (H (p - 1)).map (Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n)) ≫
      (H 0).homologySequenceδ (Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C))) (p - 1) p (by omega) ≫
      (H p).map eK.hom := by
      dsimp only [qK]
      simp only [Category.assoc]
      rw [Pi.map_π_assoc, hpreviousOut]
      erw [reassoc_of% hproduct n]
    have ht := milnorConnecting_truncation f adj S.comparison S.shift K p
      (S.truncation K p) (S.moduleSequence ((H p).obj K)) C eK qK hqK
    show inv b ≫ columnIn = _
    apply (cancel_epi b).1
    simp only [IsIso.hom_inv_id_assoc]
    apply (cancel_epi (cokernel.π (CompletionSequences.moduleDifference A (V (p - 1))))).1
    apply (cancel_epi productIso.hom).1
    simp only
    show productIso.hom ≫ cokernel.π (CompletionSequences.moduleDifference A (V (p - 1))) ≫
        milnorIn ≫ (H p).map e.inv = _
    erw [reassoc_of% hmilnorIn]
    have hb : cokernel.π (CompletionSequences.moduleDifference A (V (p - 1))) ≫ b =
        Limits.Pi.map (fun n : ℕ ↦ previousOut.app ⟨n⟩) ≫
        cokernel.π (CompletionSequences.moduleDifference A (PrincipalTorsionTower.powerTorsionSystem
          A ((H p).obj K) f)) := by
      dsimp only [b]
      rw [cokernel.map, cokernel.π_desc]
    rw [reassoc_of% hb]
    dsimp only [milnorConnecting, qK, e, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv] at ht ⊢
    simpa only [Functor.map_comp, Category.assoc] using ht

end PrincipalCompletionDiagram
end

end

section


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory PrincipalTorsionTower

universe u v w x

namespace PrincipalCompletionDiagram

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] DerivedCategory.homologyFunctor_linear

/-- **Stacks 0H32.** For `K ∈ D(A)`, the ordinary completion of `Hᵖ(K)`, the cohomology
of the derived completion of `Hᵖ(K)`, the cohomology of the derived completion of `K`, and the
inverse limits of the cohomology of `K ⊗ᴸ_A (A →[f^n] A)` form the canonical commutative
diagram of four short exact sequences from the source.  Its bottom comparison is an isomorphism
between the indicated first derived inverse limits. -/
@[stacks 0H32]
public theorem derivedCompletion_principal_homology_comparison
    (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (f : A) (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) :
    let I : Ideal A := Ideal.span {f}
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun L ↦ IsDerivedComplete I L
    ∀ (completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory)
      (adj : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      ∃ S : CompletionSequences.PrincipalCompletionSequences A f completed adj.unit,
      let H (q : ℤ) := (homologyFunctor (ModuleCat.{v} A) q).obj K
      let C := DerivedCategory.Q.objPreimage K
      let eK := DerivedCategory.Q.objObjPreimageIso K
      let E := PrincipalTorsionTower.principalComplexSystem A f C
      let tensorSystem := principalDerivedTensorSystem A f K
      let homologySystem (q : ℤ) := tensorSystem ⋙ homologyFunctor (ModuleCat.{v} A) q
      let T := CompletionSequences.milnorTriangle A E
      let completionIso := completed.mapIso eK.symm ≪≫ S.comparison.iso C
      let coneTriangle (n : ℕ) := DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C))
      let ordinaryCompletion := limit (CompletionSequences.powerQuotientSystem A (H p) f)
      let limitHpTensor := limit (homologySystem p)
      let tate := CompletionSequences.adicTateModule A (H (p + 1)) f
      let H0CompletedHp := (homologyFunctor (ModuleCat.{v} A) 0).obj
        (completed.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj (H p)))
      let HpCompletedK := (homologyFunctor (ModuleCat.{v} A) p).obj (completed.obj K)
      let R1Torsion := CompletionSequences.firstDerivedLimit A
        (PrincipalTorsionTower.powerTorsionSystem A (H p) f)
      let R1PreviousTensor := CompletionSequences.firstDerivedLimit A (homologySystem (p - 1))
      let middleIn : H0CompletedHp ⟶ HpCompletedK := (S.truncation K p).inclusion S.shift
      let middleOut : HpCompletedK ⟶ tate :=
        (S.truncation K p).projection f S.shift (S.moduleSequence (H (p + 1))).tateIso
      let leftIn : R1Torsion ⟶ H0CompletedHp := (S.moduleSequence (H p)).inclusion
      let leftOut : H0CompletedHp ⟶ ordinaryCompletion := (S.moduleSequence (H p)).projection
      ∃ (termIn : CompletionSequences.powerQuotientSystem A (H p) f ⟶ homologySystem p)
        (termOut : homologySystem p ⟶ PrincipalTorsionTower.powerTorsionSystem A (H (p + 1)) f)
        (previousOut : homologySystem (p - 1) ⟶ PrincipalTorsionTower.powerTorsionSystem A (H p) f)
        (productIso : (homologyFunctor (ModuleCat.{v} A) (p - 1)).obj T.obj₃ ≅
            CompletionSequences.moduleProduct A (homologySystem (p - 1)))
        (topIn : ordinaryCompletion ⟶ limitHpTensor)
        (topOut : limitHpTensor ⟶ tate)
        (htop : topIn ≫ topOut = 0)
        (columnIn : R1PreviousTensor ⟶ HpCompletedK)
        (columnOut : HpCompletedK ⟶ limitHpTensor)
        (hcolumn : columnIn ≫ columnOut = 0)
        (bottom : R1Torsion ≅ R1PreviousTensor),
        (∀ n : ℕ,
          cokernel.π (PrincipalTorsionTower.powerMultiplication A (H p) (f ^ (n + 1))) ≫
              termIn.app ⟨n⟩ =
            (homologyFunctor (ModuleCat.{v} A) p).map (eK.inv ≫ (coneTriangle n).mor₂)) ∧
        (∀ n : ℕ,
          termOut.app ⟨n⟩ ≫
              kernel.ι (PrincipalTorsionTower.powerMultiplication A (H (p + 1)) (f ^ (n + 1))) =
            (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
              (coneTriangle n) p (p + 1) (by omega) ≫
                (homologyFunctor (ModuleCat.{v} A) (p + 1)).map eK.hom) ∧
        (∀ n : ℕ,
          previousOut.app ⟨n⟩ ≫
              kernel.ι (PrincipalTorsionTower.powerMultiplication A (H p) (f ^ (n + 1))) =
            (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
              (coneTriangle n) (p - 1) p (by omega) ≫
                (homologyFunctor (ModuleCat.{v} A) p).map eK.hom) ∧
        (∀ n : ℕ, topIn ≫ limit.π (homologySystem p) ⟨n⟩ =
          limit.π (CompletionSequences.powerQuotientSystem A (H p) f) ⟨n⟩ ≫ termIn.app ⟨n⟩) ∧
        (∀ n : ℕ, topOut ≫ limit.π (PrincipalTorsionTower.powerTorsionSystem A (H (p + 1)) f) ⟨n⟩ =
          limit.π (homologySystem p) ⟨n⟩ ≫ termOut.app ⟨n⟩) ∧
        (∀ n : ℕ, productIso.hom ≫
            Pi.π (fun n : ℕ ↦ (homologySystem (p - 1)).obj ⟨n⟩) n =
          (homologyFunctor (ModuleCat.{v} A) (p - 1)).map
            (DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n))) ∧
        (productIso.hom ≫ cokernel.π (CompletionSequences.moduleDifference A (homologySystem (p -
          1))) ≫
            columnIn = (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ T (p - 1) p
              (by omega) ≫ (homologyFunctor (ModuleCat.{v} A) p).map completionIso.inv) ∧
        (cokernel.π (CompletionSequences.moduleDifference A (homologySystem (p - 1))) ≫ bottom.inv =
          (Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ (homologySystem (p - 1)).obj ⟨n⟩) n ≫
              previousOut.app ⟨n⟩) ≫
            cokernel.π (CompletionSequences.moduleDifference A
              (PrincipalTorsionTower.powerTorsionSystem A (H p) f))) ∧
        (∀ n : ℕ, columnOut ≫ limit.π (homologySystem p) ⟨n⟩ =
          (homologyFunctor (ModuleCat.{v} A) p).map (completionIso.hom ≫ T.mor₁ ≫
            DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n))) ∧
        (ShortComplex.mk topIn topOut htop).ShortExact ∧
        (ShortComplex.mk middleIn middleOut (S.truncation_zero K p)).ShortExact ∧
        (ShortComplex.mk leftIn leftOut (S.moduleSequence (H p)).zero).ShortExact ∧
        (ShortComplex.mk columnIn columnOut hcolumn).ShortExact ∧
        middleIn ≫ columnOut = leftOut ≫ topIn ∧
        middleOut = columnOut ≫ topOut ∧
        bottom.hom ≫ columnIn = leftIn ≫ middleIn :=
  principalCompletionDiagramSolution A f K p

end PrincipalCompletionDiagram
end

end
