module

public import StacksFrontier.Algebra.Homology.TriangleOfSESHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.Interface
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism.ExtendedHomologyDelta

/-!
# The connecting morphism of the extended sequence of resolutions, and its image under `RF`

*(b)* The compatibility of the connecting morphism with `RF`.  The unit
`CategoryTheory.Functor.rightDerivedFunctorPlusUnit` is a natural transformation
`F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⟶ Plus.Qh ⋙ RF` which is invertible at a bounded below
complex of injectives and commutes with the shift
(`Stacks.Cohomology.CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit`), so
`CategoryTheory.Functor.mapδ_commShift` applies to it; that is
`descKPlus_comp_unit_comp_mapδ`.  The other input is that applying `F` degreewise commutes with
the mapping-cone triangle, which is `CochainComplex.mappingCone.map_δ` composed with
`CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex` and
`DerivedCategory.descShortComplex_triangleOfSESδ`; that is `descKPlus_comp_triangleOfSESδ`.
Both squares are stated at the mapping cone `conePlusδ` of the extended sequence, read in the
bounded below homotopy category of `𝒜`, because the connecting morphism of a short exact
sequence of complexes exists only in the derived category while the unit of `RF` is a natural
transformation on `K⁺(𝒜)`; the two are related by the quasi-isomorphism `descKPlus`, which
`DerivedCategory.Plus.Qh` inverts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

/-- **`DerivedCategory.Plus.Qh` followed by the inclusion of `D⁺` is the inclusion of `K⁺`
followed by `DerivedCategory.Qh`.**  Mathlib records this as
`DerivedCategory.Plus.QhCompιIsoιCompQh`, an `Iso.refl`; it is rebuilt here as the
`CategoryTheory.ObjectProperty.liftCompιIso` of the full subcategory `D⁺`, because only in
that form does the compatibility of the isomorphism with the shift resolve as an instance. -/
noncomputable def plusQhCompιIso (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory C] :
    DerivedCategory.Plus.Qh (C := C) ⋙ DerivedCategory.Plus.ι ≅
      HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh :=
  (DerivedCategory.TStructure.t (C := C)).plus.liftCompιIso _
    (fun X => (DerivedCategory.Plus.Qh.obj X).2)

/-- `plusQhCompιIso` is compatible with the shift. -/
instance natTransCommShiftPlusQhCompιIso (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory C] : NatTrans.CommShift (plusQhCompιIso C).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- The commutation square of `mapδ_commShift` for a transformation with identity components
is an equation between the two `mapδ`s. -/
private theorem eq_of_comp_shift_id_eq_id_comp {D : Type*} [Category* D] [HasShift D ℤ]
    {P Q : D} {x y : P ⟶ Q⟦(1 : ℤ)⟧} (h : x ≫ (𝟙 Q)⟦(1 : ℤ)⟧' = 𝟙 P ≫ y) : x = y := by
  simpa using h

/-- The two spellings of the composite `K⁺(ℬ) ⥤ D(ℬ)` give the same `mapδ`. -/
theorem mapδ_plusQh_ι (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]
    {Y Z : HomotopyCategory.Plus C} (f : Y ⟶ Z⟦(1 : ℤ)⟧) :
    Functor.mapδ (DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι) f =
      Functor.mapδ (HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh) f :=
  eq_of_comp_shift_id_eq_id_comp
    (Functor.mapδ_commShift (plusQhCompιIso C).hom f)

/-- **Applying `F` degreewise commutes with the inclusion of the bounded below homotopy
category.**  As for `plusQhCompιIso`, this is written as the
`CategoryTheory.ObjectProperty.liftCompιIso` of `K⁺` so that its compatibility with the shift
is available as an instance. -/
noncomputable def mapHomotopyCategoryPlusCompιIso :
    F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ≅
      HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (up ℤ) :=
  (HomotopyCategory.plus B).liftCompιIso _ (fun X => (F.mapHomotopyCategoryPlus.obj X).2)

/-- `mapHomotopyCategoryPlusCompιIso` is compatible with the shift. -/
instance natTransCommShiftMapHomotopyCategoryPlusCompιIso :
    NatTrans.CommShift (mapHomotopyCategoryPlusCompιIso F).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] in
/-- The two spellings of the composite `K⁺(𝒜) ⥤ K(ℬ)` give the same `mapδ`. -/
theorem mapδ_mapHomotopyCategoryPlus_ι {Y Z : HomotopyCategory.Plus A} (f : Y ⟶ Z⟦(1 : ℤ)⟧) :
    Functor.mapδ (F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B) f =
      Functor.mapδ (HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (up ℤ)) f :=
  eq_of_comp_shift_id_eq_id_comp
    (Functor.mapδ_commShift (mapHomotopyCategoryPlusCompιIso F).hom f)

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] in
/-- The two spellings of the composite `CochainComplex 𝒜 ℤ ⥤ K(ℬ)` give the same `mapδ`. -/
theorem mapδ_quotient_mapHomotopyCategory {Y Z : CochainComplex A ℤ} (f : Y ⟶ Z⟦(1 : ℤ)⟧) :
    Functor.mapδ (HomotopyCategory.quotient A (up ℤ) ⋙ F.mapHomotopyCategory (up ℤ)) f =
      Functor.mapδ (F.mapHomologicalComplex (up ℤ) ⋙ HomotopyCategory.quotient B (up ℤ)) f :=
  eq_of_comp_shift_id_eq_id_comp
    (Functor.mapδ_commShift (F.mapHomotopyCategoryFactors (up ℤ)).hom f)

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

/-- An `ℕ`-indexed complex, extended by zero, as a bounded below `ℤ`-indexed complex. -/
noncomputable def extendCochainPlus (K : CochainComplex A ℕ) : CochainComplex.Plus A :=
  ⟨K.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- `extendCochainPlus` at an injective resolution is `resolutionCochainPlus`. -/
theorem extendCochainPlus_cocomplex {M : A} (I : InjectiveResolution M) :
    extendCochainPlus I.cocomplex = resolutionCochainPlus I := rfl

variable (R : ShortComplex (CochainComplex A ℕ))

/-- The extension by zero of a short complex of `ℕ`-indexed cochain complexes. -/
noncomputable abbrev extendShortComplex : ShortComplex (CochainComplex A ℤ) :=
  R.map (ComplexShape.embeddingUpNat.extendFunctor A)

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- The mapping cone of the extended sequence is bounded below. -/
theorem plus_mappingCone_extendShortComplex :
    CochainComplex.plus A (CochainComplex.mappingCone (extendShortComplex R).f) := by
  have : CochainComplex.IsStrictlyGE (extendShortComplex R).X₁ 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyGE (R.X₁.extend ComplexShape.embeddingUpNat) 0)
  have : CochainComplex.IsStrictlyGE (extendShortComplex R).X₂ 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyGE (R.X₂.extend ComplexShape.embeddingUpNat) 0)
  exact ⟨-1, CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1) (by lia) (by lia)⟩

/-- The mapping cone of the extended sequence, as a bounded below complex. -/
noncomputable def mappingConePlus : CochainComplex.Plus A :=
  ⟨CochainComplex.mappingCone (extendShortComplex R).f, plus_mappingCone_extendShortComplex R⟩

/-- `CochainComplex.mappingCone.descShortComplex`, read in `K⁺`. -/
noncomputable def descKPlus :
    (HomotopyCategory.Plus.quotient A).obj (mappingConePlus R) ⟶
      (HomotopyCategory.Plus.quotient A).obj (extendCochainPlus R.X₃) :=
  (HomotopyCategory.Plus.quotient A).map (ObjectProperty.homMk
    (CochainComplex.mappingCone.descShortComplex (extendShortComplex R)))

/-- The connecting morphism of the mapping-cone triangle of the extended sequence, read in the
bounded below homotopy category. -/
noncomputable def conePlusδ :
    (HomotopyCategory.Plus.quotient A).obj (mappingConePlus R) ⟶
      ((HomotopyCategory.Plus.quotient A).obj (extendCochainPlus R.X₁))⟦(1 : ℤ)⟧ :=
  (HomotopyCategory.Plus.fullyFaithfulι A).preimage
    ((CochainComplex.mappingCone.triangleh (extendShortComplex R).f).mor₃ ≫
      ((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ)).inv.app
        ((HomotopyCategory.Plus.quotient A).obj (extendCochainPlus R.X₁)))

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- The defining property of `conePlusδ`. -/
theorem mapδ_ι_conePlusδ :
    Functor.mapδ (HomotopyCategory.Plus.ι A) (conePlusδ R) =
      (CochainComplex.mappingCone.triangleh (extendShortComplex R).f).mor₃ := by
  dsimp only [Functor.mapδ, conePlusδ]
  have hc : ((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ)).inv.app
        ((HomotopyCategory.Plus.quotient A).obj (extendCochainPlus R.X₁)) ≫
      ((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ)).hom.app
        ((HomotopyCategory.Plus.quotient A).obj (extendCochainPlus R.X₁)) = 𝟙 _ :=
    Iso.inv_hom_id_app _ _
  rw [(HomotopyCategory.Plus.fullyFaithfulι A).map_preimage]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ hc) ?_
  exact Category.comp_id _

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] in
/-- `CochainComplex.mappingCone.triangleh` has `CochainComplex.mappingCone.triangle` as its
third morphism, read through the quotient. -/
theorem triangleh_mor₃_eq {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    (CochainComplex.mappingCone.triangleh φ).mor₃ =
      Functor.mapδ (HomotopyCategory.quotient A (up ℤ))
        (CochainComplex.mappingCone.triangle φ).mor₃ := rfl

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] in
/-- `CochainComplex.mappingCone.map_δ`, phrased with `CategoryTheory.Functor.mapδ`. -/
theorem mapδ_mapHomologicalComplex_triangle_mor₃ {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    Functor.mapδ (F.mapHomologicalComplex (up ℤ))
        (CochainComplex.mappingCone.triangle φ).mor₃ =
      (CochainComplex.mappingCone.mapHomologicalComplexIso φ F).hom ≫
        (CochainComplex.mappingCone.triangle
          ((F.mapHomologicalComplex (up ℤ)).map φ)).mor₃ :=
  CochainComplex.mappingCone.map_δ φ F

variable (R : ShortComplex (CochainComplex A ℕ))

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] in
/-- The degreewise-`F` image of the cone connecting morphism, read in the unbounded homotopy
category of `ℬ`. -/
theorem mapδ_ι_mapHomotopyCategory_conePlusδ :
    Functor.mapδ (HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (up ℤ)) (conePlusδ R) =
      Functor.mapδ (HomotopyCategory.quotient B (up ℤ))
        ((CochainComplex.mappingCone.mapHomologicalComplexIso
            (extendShortComplex R).f F).hom ≫
          (CochainComplex.mappingCone.triangle
            ((F.mapHomologicalComplex (up ℤ)).map (extendShortComplex R).f)).mor₃) := by
  refine Eq.trans (Functor.mapδ_comp (HomotopyCategory.Plus.ι A)
    (F.mapHomotopyCategory (up ℤ)) (conePlusδ R)) ?_
  refine Eq.trans (congrArg (fun g => Functor.mapδ (F.mapHomotopyCategory (up ℤ)) g)
    (mapδ_ι_conePlusδ R)) ?_
  refine Eq.trans (congrArg (fun g => Functor.mapδ (F.mapHomotopyCategory (up ℤ)) g)
    (triangleh_mor₃_eq (extendShortComplex R).f)) ?_
  refine Eq.trans (Functor.mapδ_comp (HomotopyCategory.quotient A (up ℤ))
    (F.mapHomotopyCategory (up ℤ)) _).symm ?_
  refine Eq.trans (mapδ_quotient_mapHomotopyCategory F _) ?_
  refine Eq.trans (Functor.mapδ_comp (F.mapHomologicalComplex (up ℤ))
    (HomotopyCategory.quotient B (up ℤ)) _) ?_
  exact congrArg (fun g => Functor.mapδ (HomotopyCategory.quotient B (up ℤ)) g)
    (mapδ_mapHomologicalComplex_triangle_mor₃ F (extendShortComplex R).f)

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- **The degreewise-`F` side of the comparison.**  The connecting morphism of the mapping-cone
triangle of the extended sequence of resolutions, pushed into `D(ℬ)` through the degreewise
image under `F` and the inclusion of `D⁺(ℬ)`, is the mapping-cone connecting morphism of the
`F`-image sequence. -/
theorem mapδ_conePlusδ_eq :
    Functor.mapδ ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        DerivedCategory.Plus.ι) (conePlusδ R) =
      Functor.mapδ (HomotopyCategory.quotient B (up ℤ) ⋙ DerivedCategory.Qh)
        ((CochainComplex.mappingCone.mapHomologicalComplexIso (extendShortComplex R).f F).hom ≫
          (CochainComplex.mappingCone.triangle
            ((F.mapHomologicalComplex (up ℤ)).map (extendShortComplex R).f)).mor₃) := by
  refine Eq.trans (Functor.mapδ_assoc F.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh
    DerivedCategory.Plus.ι (conePlusδ R)) ?_
  refine Eq.trans (Functor.mapδ_comp F.mapHomotopyCategoryPlus
    (DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι) (conePlusδ R)) ?_
  refine Eq.trans (mapδ_plusQh_ι B _) ?_
  refine Eq.trans (Functor.mapδ_comp (HomotopyCategory.Plus.ι B) DerivedCategory.Qh _) ?_
  refine Eq.trans (congrArg (fun g => Functor.mapδ DerivedCategory.Qh g)
    (Functor.mapδ_comp F.mapHomotopyCategoryPlus (HomotopyCategory.Plus.ι B)
      (conePlusδ R)).symm) ?_
  refine Eq.trans (congrArg (fun g => Functor.mapδ DerivedCategory.Qh g)
    (mapδ_mapHomotopyCategoryPlus_ι F (conePlusδ R))) ?_
  refine Eq.trans (congrArg (fun g => Functor.mapδ DerivedCategory.Qh g)
    (mapδ_ι_mapHomotopyCategory_conePlusδ F R)) ?_
  exact (Functor.mapδ_comp (HomotopyCategory.quotient B (up ℤ)) DerivedCategory.Qh _).symm

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
  (R : ShortComplex (CochainComplex A ℕ))

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- The mapping-cone connecting morphism of the `F`-image sequence, read in the derived
category, is `DerivedCategory.triangleOfSESδ` after the quasi-isomorphism
`CochainComplex.mappingCone.descShortComplex`. -/
theorem mapδ_Q_cone_eq
    (hFR : ((extendShortComplex R).map (F.mapHomologicalComplex (up ℤ))).ShortExact) :
    Functor.mapδ DerivedCategory.Q
        ((CochainComplex.mappingCone.mapHomologicalComplexIso
            (extendShortComplex R).f F).hom ≫
          (CochainComplex.mappingCone.triangle
            ((F.mapHomologicalComplex (up ℤ)).map (extendShortComplex R).f)).mor₃) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (up ℤ)).map
          (CochainComplex.mappingCone.descShortComplex (extendShortComplex R))) ≫
        DerivedCategory.triangleOfSESδ hFR := by
  refine Eq.trans (Functor.comp_mapδ DerivedCategory.Q _ _) ?_
  have hb : Functor.mapδ DerivedCategory.Q
      (CochainComplex.mappingCone.triangle
        ((F.mapHomologicalComplex (up ℤ)).map (extendShortComplex R).f)).mor₃ =
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.descShortComplex
            ((extendShortComplex R).map (F.mapHomologicalComplex (up ℤ)))) ≫
        DerivedCategory.triangleOfSESδ hFR :=
    (DerivedCategory.descShortComplex_triangleOfSESδ hFR).symm
  refine Eq.trans (whisker_eq _ hb) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine eq_whisker ?_ _
  refine Eq.trans (CategoryTheory.Functor.map_comp DerivedCategory.Q _ _).symm ?_
  exact congrArg (fun g => DerivedCategory.Q.map g)
    (CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex F
      (extendShortComplex R))

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- The `K⁺`-level `descShortComplex`, pushed into `D(ℬ)` through the degreewise image under
`F`, is `DerivedCategory.Qh` of the class of `F(descShortComplex)`. -/
theorem ι_map_plusQh_map_mapHomotopyCategoryPlus_descKPlus :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
        (F.mapHomotopyCategoryPlus.map (descKPlus R))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (up ℤ)).map
        ((F.mapHomologicalComplex (up ℤ)).map
          (CochainComplex.mappingCone.descShortComplex (extendShortComplex R)))) := rfl

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- **The first half of the unit comparison.** -/
theorem descKPlus_comp_triangleOfSESδ
    (hFR : ((extendShortComplex R).map (F.mapHomologicalComplex (up ℤ))).ShortExact) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
          (F.mapHomotopyCategoryPlus.map (descKPlus R))) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (up ℤ)).obj (extendShortComplex R).X₃) ≫
        DerivedCategory.triangleOfSESδ hFR =
      Functor.mapδ ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
          DerivedCategory.Plus.ι) (conePlusδ R) ≫
        ((DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (up ℤ)).obj (extendShortComplex R).X₁))⟦(1 : ℤ)⟧' := by
  have hcs := Functor.mapδ_commShift (DerivedCategory.quotientCompQhIso B).hom
    ((CochainComplex.mappingCone.mapHomologicalComplexIso (extendShortComplex R).f F).hom ≫
      (CochainComplex.mappingCone.triangle
        ((F.mapHomologicalComplex (up ℤ)).map (extendShortComplex R).f)).mor₃)
  have hnat := DerivedCategory.quotientCompQhIso_hom_naturality
    ((F.mapHomologicalComplex (up ℤ)).map
      (CochainComplex.mappingCone.descShortComplex (extendShortComplex R)))
  have hwq := (eq_whisker (ι_map_plusQh_map_mapHomotopyCategoryPlus_descKPlus F R) _).trans hnat
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hwq _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (mapδ_Q_cone_eq F R hFR).symm) ?_
  refine Eq.trans hcs.symm ?_
  exact eq_whisker (mapδ_conePlusδ_eq F R).symm _

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
  [F.rightDerivedFunctorPlus.CommShift ℤ]
  [NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ]
  (R : ShortComplex (CochainComplex A ℕ))

omit [EnoughInjectives A] [HasDerivedCategory B] [F.rightDerivedFunctorPlus.CommShift ℤ]
  [NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ] in
/-- `DerivedCategory.Plus.Qh` inverts `descKPlus`, which is a quasi-isomorphism. -/
theorem isIso_plusQh_map_descKPlus (hR : (extendShortComplex R).ShortExact) :
    IsIso (DerivedCategory.Plus.Qh.map (descKPlus R)) :=
  Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff
      (CochainComplex.mappingCone.descShortComplex (extendShortComplex R))).2
      (CochainComplex.mappingCone.quasiIso_descShortComplex hR))

omit [EnoughInjectives A] [HasDerivedCategory B] [F.rightDerivedFunctorPlus.CommShift ℤ]
  [NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ] in
/-- **The connecting morphism of the extended sequence of resolutions in `D⁺(𝒜)`**: the
mapping-cone one, read through the quasi-isomorphism `descKPlus`. -/
noncomputable def resolutionPlusδ (hR : (extendShortComplex R).ShortExact) :
    DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient A).obj (extendCochainPlus R.X₃)) ⟶
      (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient A).obj (extendCochainPlus R.X₁)))⟦(1 : ℤ)⟧ :=
  have := isIso_plusQh_map_descKPlus R hR
  inv (DerivedCategory.Plus.Qh.map (descKPlus R)) ≫
    Functor.mapδ DerivedCategory.Plus.Qh (conePlusδ R)

omit [EnoughInjectives A] [HasDerivedCategory B] [F.rightDerivedFunctorPlus.CommShift ℤ]
  [NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ] in
/-- The defining property of `resolutionPlusδ`. -/
theorem plusQh_map_descKPlus_comp_resolutionPlusδ (hR : (extendShortComplex R).ShortExact) :
    DerivedCategory.Plus.Qh.map (descKPlus R) ≫ resolutionPlusδ R hR =
      Functor.mapδ DerivedCategory.Plus.Qh (conePlusδ R) := by
  have := isIso_plusQh_map_descKPlus R hR
  dsimp only [resolutionPlusδ]
  exact IsIso.hom_inv_id_assoc _ _

/-- **The second half of the unit comparison.** -/
theorem descKPlus_comp_unit_comp_mapδ (hR : (extendShortComplex R).ShortExact) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
          (F.mapHomotopyCategoryPlus.map (descKPlus R))) ≫
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient A).obj (extendCochainPlus R.X₃))) ≫
        Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
          (resolutionPlusδ R hR) =
      Functor.mapδ ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
          DerivedCategory.Plus.ι) (conePlusδ R) ≫
        (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient A).obj (extendCochainPlus R.X₁))))⟦(1 : ℤ)⟧' := by
  have hΦ₂ : Functor.mapδ ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.ι) (conePlusδ R) =
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
          (DerivedCategory.Plus.Qh.map (descKPlus R)) ≫
        Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
          (resolutionPlusδ R hR) := by
    refine Eq.trans (Functor.mapδ_assoc DerivedCategory.Plus.Qh F.rightDerivedFunctorPlus
      DerivedCategory.Plus.ι (conePlusδ R)) ?_
    refine Eq.trans (Functor.mapδ_comp DerivedCategory.Plus.Qh
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) (conePlusδ R)) ?_
    refine Eq.trans (congrArg
      (fun g => Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) g)
      (plusQh_map_descKPlus_comp_resolutionPlusδ R hR).symm) ?_
    exact Functor.comp_mapδ _ _ _
  have hnat := F.rightDerivedFunctorPlusUnit.naturality (descKPlus R)
  have hcs := Functor.mapδ_commShift
    (Functor.whiskerRight F.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι) (conePlusδ R)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (CategoryTheory.Functor.map_comp DerivedCategory.Plus.ι _ _).symm _) ?_
  refine Eq.trans (eq_whisker (congrArg
    (fun g => DerivedCategory.Plus.ι.map g) hnat) _) ?_
  refine Eq.trans (eq_whisker (CategoryTheory.Functor.map_comp DerivedCategory.Plus.ι _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ hΦ₂.symm) ?_
  exact hcs.symm

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

/-- Cancelling a fully faithful functor off a natural isomorphism, read on components. -/
theorem map_fullyFaithfulCancelRight_hom_app {Ca Cb Cc : Type*} [Category* Ca] [Category* Cb]
    [Category* Cc] {Fa Ga : Ca ⥤ Cb} (H : Cb ⥤ Cc) [H.Full] [H.Faithful]
    (iso : Fa ⋙ H ≅ Ga ⋙ H) (X : Ca) :
    H.map ((Functor.fullyFaithfulCancelRight H iso).hom.app X) = iso.hom.app X := by
  rw [Functor.fullyFaithfulCancelRight_hom_app]
  exact CategoryTheory.Functor.map_preimage _ _

variable {A : Type*} [Category* A] [Abelian A]

/-- A square between an injective resolution's augmentation and a comparison of resolutions
commutes as soon as it commutes in degree zero. -/
theorem single₀_comm_of_degree_zero {M N : A} (I : InjectiveResolution M)
    (J : InjectiveResolution N) (φ : M ⟶ N) (ψ : I.cocomplex ⟶ J.cocomplex)
    (h : I.ι.f 0 ≫ ψ.f 0 = φ ≫ J.ι.f 0) :
    (CochainComplex.single₀ A).map φ ≫ J.ι = I.ι ≫ ψ := by
  apply HomologicalComplex.from_single_hom_ext (j := (0 : ℕ))
  simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self, Category.assoc]
  rw [h]
  exact (Category.id_comp _).trans (whisker_eq φ (Category.id_comp _))

/-- **`resolutionSingleHom` is natural**: a comparison of injective resolutions over a morphism
`φ` carries the extended augmentation of one to the extended augmentation of the other. -/
theorem resolutionSingleHom_naturality {M N : A} (I : InjectiveResolution M)
    (J : InjectiveResolution N) (φ : M ⟶ N) (ψ : I.cocomplex ⟶ J.cocomplex)
    (hψ : (CochainComplex.single₀ A).map φ ≫ J.ι = I.ι ≫ ψ) :
    (HomologicalComplex.single A (up ℤ) 0).map φ ≫ resolutionSingleHom J =
      resolutionSingleHom I ≫
        HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat := by
  apply HomologicalComplex.from_single_hom_ext (j := (0 : ℤ))
  have hψ0 := HomologicalComplex.congr_hom hψ 0
  simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self] at hψ0
  dsimp only [resolutionSingleHom]
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingUpNat.f 0 = 0 by simp),
    HomologicalComplex.extendSingleIso_inv_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← reassoc_of% hψ0]
  simp

/-- The image in the unbounded homotopy category of the comparison of the two constructions of
a single complex in `K⁺(𝒜)`. -/
theorem ι_map_singlePlusToCochainQuotientIso (M : A) :
    (HomotopyCategory.Plus.ι A).map ((singlePlusToCochainQuotientIso (A := A)).hom.app M) =
      (HomotopyCategory.singleFunctorPostcompQuotientIso A 0).hom.app M := by
  dsimp only [singlePlusToCochainQuotientIso]
  rw [map_fullyFaithfulCancelRight_hom_app]
  exact (Category.comp_id ((HomotopyCategory.Plus.singleFunctorCompιIso A 0).hom.app M ≫
      (HomotopyCategory.singleFunctorPostcompQuotientIso A 0).hom.app M)).trans
    (Category.id_comp _)

variable [HasDerivedCategory A]

/-- The three factors of `resolutionDerivedIso`. -/
theorem resolutionDerivedIso_hom_eq' {M : A} (I : InjectiveResolution M) :
    (resolutionDerivedIso I).hom =
      (Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app M ≫
        DerivedCategory.Plus.Qh.map ((singlePlusToCochainQuotientIso (A := A)).hom.app M) ≫
        DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient A).map (resolutionSinglePlusHom I)) := by
  dsimp only [resolutionDerivedIso]
  simp

/-- **`resolutionDerivedIso` is induced by `resolutionSingleHom`.**  Read in the full derived
category of `𝒜` and composed with `DerivedCategory.quotientCompQhIso`, the comparison of `M`
placed in degree zero with the extension of an injective resolution of `M` is the image under
`DerivedCategory.Q` of the extended augmentation. -/
theorem Q_map_resolutionSingleHom {M : A} (I : InjectiveResolution M) :
    DerivedCategory.Plus.ι.map (resolutionDerivedIso I).hom ≫
        (DerivedCategory.quotientCompQhIso A).hom.app
          (I.cocomplex.extend ComplexShape.embeddingUpNat) =
      DerivedCategory.Q.map (resolutionSingleHom I) := by
  have h1 : DerivedCategory.Plus.ι.map
      ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app M) =
      (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app M :=
    map_fullyFaithfulCancelRight_hom_app DerivedCategory.Plus.ι _ M
  have h2 : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
        ((singlePlusToCochainQuotientIso (A := A)).hom.app M)) =
      DerivedCategory.Qh.map
        ((HomotopyCategory.singleFunctorPostcompQuotientIso A 0).hom.app M) :=
    congrArg (fun u => DerivedCategory.Qh.map u) (ι_map_singlePlusToCochainQuotientIso M)
  have h4 : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient A).map (resolutionSinglePlusHom I))) =
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (up ℤ)).map (resolutionSingleHom I)) := rfl
  have h3 := DerivedCategory.quotientCompQhIso_hom_naturality (resolutionSingleHom I)
  have key : (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app M ≫
      DerivedCategory.Qh.map
        ((HomotopyCategory.singleFunctorPostcompQuotientIso A 0).hom.app M) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app
        ((CochainComplex.singleFunctor A 0).obj M) =
      𝟙 ((DerivedCategory.singleFunctor A 0).obj M) := by
    have e : DerivedCategory.Qh.map
        ((HomotopyCategory.singleFunctorPostcompQuotientIso A 0).hom.app M) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    have hq : (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app M =
        (DerivedCategory.quotientCompQhIso A).inv.app
          ((CochainComplex.singleFunctor A 0).obj M) ≫ 𝟙 _ := rfl
    exact (hq.trans (Category.comp_id _) =≫ _).trans
      ((whisker_eq _ ((e =≫ _).trans (Category.id_comp _))).trans (Iso.inv_hom_id_app _ _))
  rw [resolutionDerivedIso_hom_eq', CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, h1, h2, h4]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ h3)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact (eq_whisker key _).trans (Category.id_comp _)

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  (R : ShortComplex (CochainComplex A ℕ))

/-- The cone connecting morphism of the extended sequence, pushed into `D(𝒜)`. -/
theorem mapδ_ι_mapδ_plusQh_conePlusδ :
    Functor.mapδ DerivedCategory.Plus.ι
        (Functor.mapδ DerivedCategory.Plus.Qh (conePlusδ R)) =
      Functor.mapδ (HomotopyCategory.quotient A (up ℤ) ⋙ DerivedCategory.Qh)
        (CochainComplex.mappingCone.triangle (extendShortComplex R).f).mor₃ := by
  refine Eq.trans (Functor.mapδ_comp DerivedCategory.Plus.Qh DerivedCategory.Plus.ι
    (conePlusδ R)).symm ?_
  refine Eq.trans (mapδ_plusQh_ι A (conePlusδ R)) ?_
  refine Eq.trans (Functor.mapδ_comp (HomotopyCategory.Plus.ι A) DerivedCategory.Qh
    (conePlusδ R)) ?_
  refine Eq.trans (congrArg (fun u => Functor.mapδ DerivedCategory.Qh u)
    (mapδ_ι_conePlusδ R)) ?_
  refine Eq.trans (congrArg (fun u => Functor.mapδ DerivedCategory.Qh u)
    (triangleh_mor₃_eq (extendShortComplex R).f)) ?_
  exact (Functor.mapδ_comp (HomotopyCategory.quotient A (up ℤ)) DerivedCategory.Qh _).symm

/-- **`resolutionPlusδ` is `DerivedCategory.triangleOfSESδ`**, read through
`DerivedCategory.quotientCompQhIso`.  This is the content of the connecting morphism of the
extended sequence of resolutions in `D⁺(𝒜)`. -/
theorem mapδ_ι_resolutionPlusδ (hR : (extendShortComplex R).ShortExact) :
    Functor.mapδ DerivedCategory.Plus.ι (resolutionPlusδ R hR) ≫
        ((DerivedCategory.quotientCompQhIso A).hom.app
          (R.X₁.extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧' =
      (DerivedCategory.quotientCompQhIso A).hom.app
          (R.X₃.extend ComplexShape.embeddingUpNat) ≫
        DerivedCategory.triangleOfSESδ hR := by
  have hiso := isIso_plusQh_map_descKPlus R hR
  have hw : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map (descKPlus R)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (up ℤ)).map
        (CochainComplex.mappingCone.descShortComplex (extendShortComplex R))) := rfl
  have hnat := DerivedCategory.quotientCompQhIso_hom_naturality
    (CochainComplex.mappingCone.descShortComplex (extendShortComplex R))
  have hcs := Functor.mapδ_commShift (DerivedCategory.quotientCompQhIso A).hom
    (CochainComplex.mappingCone.triangle (extendShortComplex R).f).mor₃
  have hδ : Functor.mapδ DerivedCategory.Q
        (CochainComplex.mappingCone.triangle (extendShortComplex R).f).mor₃ =
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.descShortComplex (extendShortComplex R)) ≫
        DerivedCategory.triangleOfSESδ hR :=
    (DerivedCategory.descShortComplex_triangleOfSESδ hR).symm
  refine (cancel_epi (DerivedCategory.Plus.ι.map
    (DerivedCategory.Plus.Qh.map (descKPlus R)))).1 ?_
  have hleft : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map (descKPlus R)) ≫
      Functor.mapδ DerivedCategory.Plus.ι (resolutionPlusδ R hR) =
      Functor.mapδ (HomotopyCategory.quotient A (up ℤ) ⋙ DerivedCategory.Qh)
        (CochainComplex.mappingCone.triangle (extendShortComplex R).f).mor₃ :=
    (Functor.comp_mapδ DerivedCategory.Plus.ι _ _).symm.trans
      ((congrArg (fun u => Functor.mapδ DerivedCategory.Plus.ι u)
          (plusQh_map_descKPlus_comp_resolutionPlusδ R hR)).trans
        (mapδ_ι_mapδ_plusQh_conePlusδ R))
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hleft _) ?_
  refine Eq.trans hcs ?_
  refine Eq.trans (whisker_eq _ hδ) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hnat.symm _) ?_
  refine Eq.trans (eq_whisker (eq_whisker hw.symm _) _) ?_
  exact Category.assoc _ _ _

end Stacks.Cohomology.HigherDirectImagePresheaf

end
