module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsComparison

/-!
# The boundary map of a right derived functor on a short exact sequence of complexes

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, `𝒜` with enough injectives,
and let `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` be its right derived functor.  A short exact sequence
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` of bounded below complexes of `𝒜` gives a distinguished triangle
`K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` of `D⁺(𝒜)` (Derived Categories, Section 014P), hence a triangle
`RF(K₁) ⟶ RF(K₂) ⟶ RF(K₃) ⟶ RF(K₁)[1]` and boundary maps
`∂ : Hⁿ(RF(K₃)) ⟶ Hⁿ⁺¹(RF(K₁))`.

When the sequence stays short exact after applying `F`, the canonical map `F(K) ⟶ RF(K)`
carries the connecting morphism of the short exact sequence `0 ⟶ F(K₁) ⟶ F(K₂) ⟶ F(K₃) ⟶ 0` to
the third morphism of the triangle `RF(K₁) ⟶ RF(K₂) ⟶ RF(K₃) ⟶ RF(K₁)[1]`.

## Main definitions

* `Stacks.Cohomology.RightDerivedBoundary.plusδ`: the connecting morphism `K₃ ⟶ K₁[1]` in
  `D⁺(𝒜)` of a short exact sequence of bounded below complexes.
* `Stacks.Cohomology.RightDerivedBoundary.coneδ`: the same connecting morphism, built from the
  mapping cone of `K₁ ⟶ K₂`.
* `Stacks.Cohomology.RightDerivedBoundary.unitD`: the canonical map `F(K) ⟶ RF(K)` in `D(ℬ)`.

## Main results

* `Stacks.Cohomology.RightDerivedBoundary.triangleOfSESδ_comp_unitD`: the compatibility of the
  canonical map with the connecting morphisms, for a short exact sequence which `F` keeps short
  exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Pretriangulated
open Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.RightDerivedBoundary

/-- A morphism followed by a section and its retraction is the morphism itself. -/
theorem comp_comp_eq_self {C : Type*} [Category* C] {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ b) (hgh : g ≫ h = 𝟙 b) : (f ≫ g) ≫ h = f := by
  rw [Category.assoc, hgh, Category.comp_id]

/-- If `D ≫ q₃ ≫ t = M ≫ q₁` and `q₁ ≫ q₁' = 𝟙`, then `M ≫ U = D ≫ q₃ ≫ t ≫ q₁' ≫ U`. -/
theorem comp_eq_of_comp_eq {C : Type*} [Category* C] {a b c d e f : C} (D : a ⟶ b) (q₃ : b ⟶ c)
    (t : c ⟶ d) (M : a ⟶ e) (q₁ : e ⟶ d) (q₁' : d ⟶ e) (U : e ⟶ f)
    (h : D ≫ q₃ ≫ t = M ≫ q₁) (hq : q₁ ≫ q₁' = 𝟙 e) : M ≫ U = D ≫ q₃ ≫ t ≫ q₁' ≫ U := by
  calc M ≫ U = (M ≫ q₁) ≫ q₁' ≫ U := by rw [Category.assoc, ← Category.assoc q₁, hq,
        Category.id_comp]
    _ = D ≫ q₃ ≫ t ≫ q₁' ≫ U := by rw [← h]; simp only [Category.assoc]

/-- A rearrangement of composites: given `UG1 = U1 ≫ Gq1`, `Cδ ≫ Gq1 = Gq3 ≫ P`,
`U3 ≫ Cδ = qhom ≫ δ ≫ qinv1 ≫ U1` and `qinv ≫ qhom = 𝟙`, the composite `δ ≫ qinv1 ≫ UG1` is
`(qinv ≫ U3 ≫ Gq3) ≫ P`. -/
theorem unitD_aux {C : Type*} [Category* C] {a b c d e f g h : C} (qinv : a ⟶ b) (U3 : b ⟶ c)
    (Gq3 : c ⟶ d) (P : d ⟶ e) (Cδ : c ⟶ f) (Gq1 : f ⟶ e) (qhom : b ⟶ a) (δ : a ⟶ g)
    (qinv1 : g ⟶ h) (U1 : h ⟶ f) (UG1 : h ⟶ e) (hUG : UG1 = U1 ≫ Gq1)
    (h3 : Cδ ≫ Gq1 = Gq3 ≫ P)
    (hu : U3 ≫ Cδ = qhom ≫ δ ≫ qinv1 ≫ U1) (hq : qinv ≫ qhom = 𝟙 a) :
    δ ≫ qinv1 ≫ UG1 = (qinv ≫ U3 ≫ Gq3) ≫ P := by
  calc δ ≫ qinv1 ≫ UG1 = qinv ≫ (qhom ≫ δ ≫ qinv1 ≫ U1) ≫ Gq1 := by
        simp only [hUG, Category.assoc, reassoc_of% hq]
    _ = (qinv ≫ U3 ≫ Gq3) ≫ P := by rw [← hu]; simp only [Category.assoc, h3]

section Triangle

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- The connecting morphism of a short exact sequence of bounded below complexes in `D⁺(𝒜)`:
the third morphism `K₃ ⟶ K₁[1]` of the distinguished triangle of the sequence,
`DerivedCategory.triangleOfSESδ`, read in the full subcategory `D⁺(𝒜)`. -/
def plusδ (S : ShortComplex (CochainComplex.Plus A))
    (hS : (S.map (CochainComplex.Plus.ι A)).ShortExact) :
    DerivedCategory.Plus.Q.obj S.X₃ ⟶ (DerivedCategory.Plus.Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage (DerivedCategory.triangleOfSESδ hS ≫
    (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app (DerivedCategory.Plus.Q.obj S.X₁))

/-- `plusδ`, read in `D(𝒜)`, is the connecting morphism of the short exact sequence. -/
theorem mapδ_ι_plusδ (S : ShortComplex (CochainComplex.Plus A))
    (hS : (S.map (CochainComplex.Plus.ι A)).ShortExact) :
    Functor.mapδ DerivedCategory.Plus.ι (plusδ S hS) = DerivedCategory.triangleOfSESδ hS := by
  dsimp only [Functor.mapδ, plusδ]
  rw [Functor.map_preimage]
  exact comp_comp_eq_self _ _ _ (Iso.inv_hom_id_app _ _)

end Triangle

section Cone

variable {A : Type*} [Category* A] [Abelian A] (S : ShortComplex (CochainComplex.Plus A))

/-- The underlying short complex of cochain complexes. -/
abbrev toSC : ShortComplex (CochainComplex A ℤ) := S.map (CochainComplex.Plus.ι A)

/-- The mapping cone of the first map of a short complex of bounded below complexes is bounded
below. -/
theorem plus_mappingCone : CochainComplex.plus A (CochainComplex.mappingCone (toSC S).f) := by
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff A S.X₁.obj).mp S.X₁.property
  obtain ⟨b, hb⟩ := (CochainComplex.plus_iff A S.X₂.obj).mp S.X₂.property
  have : CochainComplex.IsStrictlyGE (toSC S).X₁ a := ha
  have : CochainComplex.IsStrictlyGE (toSC S).X₂ b := hb
  have : CochainComplex.IsStrictlyGE (toSC S).X₁ (min a b) :=
    CochainComplex.isStrictlyGE_of_ge _ _ _ (min_le_left a b)
  have : CochainComplex.IsStrictlyGE (toSC S).X₂ (min a b) :=
    CochainComplex.isStrictlyGE_of_ge _ _ _ (min_le_right a b)
  exact ⟨min a b - 1, CochainComplex.isStrictlyGE_mappingCone _ (min a b) (min a b) _⟩

/-- The mapping cone, as a bounded below complex. -/
def mappingConePlus : CochainComplex.Plus A :=
  ⟨CochainComplex.mappingCone (toSC S).f, plus_mappingCone S⟩

/-- `CochainComplex.mappingCone.descShortComplex`, read in `K⁺`. -/
def descKPlus :
    (HomotopyCategory.Plus.quotient A).obj (mappingConePlus S) ⟶
      (HomotopyCategory.Plus.quotient A).obj S.X₃ :=
  (HomotopyCategory.Plus.quotient A).map (ObjectProperty.homMk
    (CochainComplex.mappingCone.descShortComplex (toSC S)))

/-- The connecting morphism of the mapping-cone triangle, read in the bounded below homotopy
category. -/
def conePlusδ :
    (HomotopyCategory.Plus.quotient A).obj (mappingConePlus S) ⟶
      ((HomotopyCategory.Plus.quotient A).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (HomotopyCategory.Plus.fullyFaithfulι A).preimage
    ((CochainComplex.mappingCone.triangleh (toSC S).f).mor₃ ≫
      ((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ)).inv.app
        ((HomotopyCategory.Plus.quotient A).obj S.X₁))

/-- The defining property of `conePlusδ`. -/
theorem mapδ_ι_conePlusδ :
    Functor.mapδ (HomotopyCategory.Plus.ι A) (conePlusδ S) =
      (CochainComplex.mappingCone.triangleh (toSC S).f).mor₃ := by
  dsimp only [Functor.mapδ, conePlusδ]
  rw [(HomotopyCategory.Plus.fullyFaithfulι A).map_preimage]
  exact comp_comp_eq_self _ _ _ (Iso.inv_hom_id_app _ _)

/-- The cone connecting morphism, pushed through `Plus.ι` and any shift-commuting functor `G`, is
`G` applied to the third morphism of the cone triangle. -/
private theorem mapδ_ι_comp_conePlusδ {D : Type*} [Category* D] [HasShift D ℤ]
    (G : HomotopyCategory A (up ℤ) ⥤ D) [G.CommShift ℤ] :
    Functor.mapδ (HomotopyCategory.Plus.ι A ⋙ G) (conePlusδ S) =
      Functor.mapδ (HomotopyCategory.quotient A (up ℤ) ⋙ G)
        (CochainComplex.mappingCone.triangle (toSC S).f).mor₃ := by
  rw [Functor.mapδ_comp, mapδ_ι_conePlusδ, triangleh_mor₃_eq]
  exact (Functor.mapδ_comp _ _ _).symm

end Cone

section Unit

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
  (S : ShortComplex (CochainComplex.Plus A))

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The degreewise-`F` image of the cone connecting morphism, read in the unbounded homotopy
category of `ℬ`. -/
theorem mapδ_ι_mapHomotopyCategory_conePlusδ :
    Functor.mapδ (HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (up ℤ)) (conePlusδ S) =
      Functor.mapδ (HomotopyCategory.quotient B (up ℤ))
        ((CochainComplex.mappingCone.mapHomologicalComplexIso (toSC S).f F).hom ≫
          (CochainComplex.mappingCone.triangle
            ((F.mapHomologicalComplex (up ℤ)).map (toSC S).f)).mor₃) := by
  rw [mapδ_ι_comp_conePlusδ, mapδ_quotient_mapHomotopyCategory, Functor.mapδ_comp,
    mapδ_mapHomologicalComplex_triangle_mor₃]
  rfl

omit [HasDerivedCategory A] in
/-- The cone connecting morphism pushed into `D(ℬ)` through the degreewise image under `F` is
the mapping-cone connecting morphism of the `F`-image sequence. -/
theorem mapδ_conePlusδ_eq :
    Functor.mapδ ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        DerivedCategory.Plus.ι) (conePlusδ S) =
      Functor.mapδ (HomotopyCategory.quotient B (up ℤ) ⋙ DerivedCategory.Qh)
        ((CochainComplex.mappingCone.mapHomologicalComplexIso (toSC S).f F).hom ≫
          (CochainComplex.mappingCone.triangle
            ((F.mapHomologicalComplex (up ℤ)).map (toSC S).f)).mor₃) := by
  rw [Functor.mapδ_assoc, Functor.mapδ_comp F.mapHomotopyCategoryPlus, mapδ_plusQh_ι,
    Functor.mapδ_comp (HomotopyCategory.Plus.ι B), ← Functor.mapδ_comp F.mapHomotopyCategoryPlus,
    mapδ_mapHomotopyCategoryPlus_ι, mapδ_ι_mapHomotopyCategory_conePlusδ]
  exact (Functor.mapδ_comp _ _ _).symm

omit [HasDerivedCategory A] in
/-- The mapping-cone connecting morphism of the `F`-image sequence, read in the derived
category, is `DerivedCategory.triangleOfSESδ` after the quasi-isomorphism
`CochainComplex.mappingCone.descShortComplex`. -/
theorem mapδ_Q_cone_eq
    (hFS : ((toSC S).map (F.mapHomologicalComplex (up ℤ))).ShortExact) :
    Functor.mapδ DerivedCategory.Q
        ((CochainComplex.mappingCone.mapHomologicalComplexIso (toSC S).f F).hom ≫
          (CochainComplex.mappingCone.triangle
            ((F.mapHomologicalComplex (up ℤ)).map (toSC S).f)).mor₃) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (up ℤ)).map
          (CochainComplex.mappingCone.descShortComplex (toSC S))) ≫
        DerivedCategory.triangleOfSESδ hFS := by
  refine Eq.trans (Functor.comp_mapδ DerivedCategory.Q _ _) ?_
  have hb : Functor.mapδ DerivedCategory.Q
      (CochainComplex.mappingCone.triangle
        ((F.mapHomologicalComplex (up ℤ)).map (toSC S).f)).mor₃ =
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.descShortComplex
            ((toSC S).map (F.mapHomologicalComplex (up ℤ)))) ≫
        DerivedCategory.triangleOfSESδ hFS :=
    (DerivedCategory.descShortComplex_triangleOfSESδ hFS).symm
  refine Eq.trans (whisker_eq _ hb) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine eq_whisker ?_ _
  refine Eq.trans (CategoryTheory.Functor.map_comp DerivedCategory.Q _ _).symm ?_
  exact congrArg (fun g ↦ DerivedCategory.Q.map g)
    (CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex F (toSC S))

omit [HasDerivedCategory A] in
/-- The `K⁺`-level `descShortComplex`, pushed into `D(ℬ)` through the degreewise image under
`F`, is `DerivedCategory.Qh` of the class of `F(descShortComplex)`. -/
theorem ι_map_plusQh_map_mapHomotopyCategoryPlus_descKPlus :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
        (F.mapHomotopyCategoryPlus.map (descKPlus S))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (up ℤ)).map
        ((F.mapHomologicalComplex (up ℤ)).map
          (CochainComplex.mappingCone.descShortComplex (toSC S)))) := rfl

omit [HasDerivedCategory A] in
/-- The image under `F` of `descKPlus S`, followed by the comparison isomorphism and the
connecting morphism of the `F`-image sequence, is the image under `F` of `conePlusδ S` followed by
the shifted comparison isomorphism. -/
theorem descKPlus_comp_triangleOfSESδ
    (hFS : ((toSC S).map (F.mapHomologicalComplex (up ℤ))).ShortExact) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
          (F.mapHomotopyCategoryPlus.map (descKPlus S))) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (up ℤ)).obj (toSC S).X₃) ≫
        DerivedCategory.triangleOfSESδ hFS =
      Functor.mapδ ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
          DerivedCategory.Plus.ι) (conePlusδ S) ≫
        ((DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (up ℤ)).obj (toSC S).X₁))⟦(1 : ℤ)⟧' := by
  have hcs := Functor.mapδ_commShift (DerivedCategory.quotientCompQhIso B).hom
    ((CochainComplex.mappingCone.mapHomologicalComplexIso (toSC S).f F).hom ≫
      (CochainComplex.mappingCone.triangle
        ((F.mapHomologicalComplex (up ℤ)).map (toSC S).f)).mor₃)
  have hnat := DerivedCategory.quotientCompQhIso_hom_naturality
    ((F.mapHomologicalComplex (up ℤ)).map
      (CochainComplex.mappingCone.descShortComplex (toSC S)))
  have hwq := (eq_whisker (ι_map_plusQh_map_mapHomotopyCategoryPlus_descKPlus F S) _).trans hnat
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hwq _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (mapδ_Q_cone_eq F S hFS).symm) ?_
  refine Eq.trans hcs.symm ?_
  exact eq_whisker (mapδ_conePlusδ_eq F S).symm _

omit [HasDerivedCategory B] in
/-- `DerivedCategory.Plus.Qh` inverts `descKPlus`, which is a quasi-isomorphism. -/
theorem isIso_plusQh_map_descKPlus (hS : (toSC S).ShortExact) :
    IsIso (DerivedCategory.Plus.Qh.map (descKPlus S)) :=
  Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff
      (CochainComplex.mappingCone.descShortComplex (toSC S))).2
      (CochainComplex.mappingCone.quasiIso_descShortComplex hS))

omit [HasDerivedCategory B] in
/-- The connecting morphism of the sequence in `D⁺(𝒜)`, built from the mapping cone and read
through the quasi-isomorphism `descKPlus`. -/
def coneδ (hS : (toSC S).ShortExact) :
    DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj S.X₃) ⟶
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj S.X₁))⟦(1 : ℤ)⟧ :=
  have := isIso_plusQh_map_descKPlus S hS
  inv (DerivedCategory.Plus.Qh.map (descKPlus S)) ≫
    Functor.mapδ DerivedCategory.Plus.Qh (conePlusδ S)

omit [HasDerivedCategory B] in
/-- The defining property of `coneδ`. -/
theorem plusQh_map_descKPlus_comp_coneδ (hS : (toSC S).ShortExact) :
    DerivedCategory.Plus.Qh.map (descKPlus S) ≫ coneδ S hS =
      Functor.mapδ DerivedCategory.Plus.Qh (conePlusδ S) := by
  have := isIso_plusQh_map_descKPlus S hS
  dsimp only [coneδ]
  exact IsIso.hom_inv_id_assoc _ _

omit [HasDerivedCategory B] in
/-- The cone connecting morphism, pushed into `D(𝒜)`. -/
theorem mapδ_ι_mapδ_plusQh_conePlusδ :
    Functor.mapδ DerivedCategory.Plus.ι
        (Functor.mapδ DerivedCategory.Plus.Qh (conePlusδ S)) =
      Functor.mapδ (HomotopyCategory.quotient A (up ℤ) ⋙ DerivedCategory.Qh)
        (CochainComplex.mappingCone.triangle (toSC S).f).mor₃ := by
  rw [← Functor.mapδ_comp, mapδ_plusQh_ι, mapδ_ι_comp_conePlusδ]

omit [HasDerivedCategory B] in
/-- `coneδ` is `DerivedCategory.triangleOfSESδ`, read through
`DerivedCategory.quotientCompQhIso`. -/
theorem mapδ_ι_coneδ (hS : (toSC S).ShortExact) :
    Functor.mapδ DerivedCategory.Plus.ι (coneδ S hS) ≫
        ((DerivedCategory.quotientCompQhIso A).hom.app (toSC S).X₁)⟦(1 : ℤ)⟧' =
      (DerivedCategory.quotientCompQhIso A).hom.app (toSC S).X₃ ≫
        DerivedCategory.triangleOfSESδ hS := by
  have hiso := isIso_plusQh_map_descKPlus S hS
  have hw : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map (descKPlus S)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (up ℤ)).map
        (CochainComplex.mappingCone.descShortComplex (toSC S))) := rfl
  have hnat := DerivedCategory.quotientCompQhIso_hom_naturality
    (CochainComplex.mappingCone.descShortComplex (toSC S))
  have hcs := Functor.mapδ_commShift (DerivedCategory.quotientCompQhIso A).hom
    (CochainComplex.mappingCone.triangle (toSC S).f).mor₃
  have hδ : Functor.mapδ DerivedCategory.Q
        (CochainComplex.mappingCone.triangle (toSC S).f).mor₃ =
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.descShortComplex (toSC S)) ≫
        DerivedCategory.triangleOfSESδ hS :=
    (DerivedCategory.descShortComplex_triangleOfSESδ hS).symm
  refine (cancel_epi (DerivedCategory.Plus.ι.map
    (DerivedCategory.Plus.Qh.map (descKPlus S)))).1 ?_
  have hleft : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map (descKPlus S)) ≫
      Functor.mapδ DerivedCategory.Plus.ι (coneδ S hS) =
      Functor.mapδ (HomotopyCategory.quotient A (up ℤ) ⋙ DerivedCategory.Qh)
        (CochainComplex.mappingCone.triangle (toSC S).f).mor₃ :=
    (Functor.comp_mapδ DerivedCategory.Plus.ι _ _).symm.trans
      ((congrArg (fun u ↦ Functor.mapδ DerivedCategory.Plus.ι u)
          (plusQh_map_descKPlus_comp_coneδ S hS)).trans
        (mapδ_ι_mapδ_plusQh_conePlusδ S))
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hleft _) ?_
  refine Eq.trans hcs ?_
  refine Eq.trans (whisker_eq _ hδ) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hnat.symm _) ?_
  refine Eq.trans (eq_whisker (eq_whisker hw.symm _) _) ?_
  exact Category.assoc _ _ _

end Unit

section RightDerived

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
  [F.rightDerivedFunctorPlus.CommShift ℤ]
  [NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ]
  (S : ShortComplex (CochainComplex.Plus A))

/-- The image under `F` of `descKPlus S`, followed by the unit of `RF` at `K₃` and the image of
`coneδ S hS` under `RF`, is the image under `F` of `conePlusδ S` followed by the shifted unit of
`RF` at `K₁`. -/
theorem descKPlus_comp_unit_comp_mapδ (hS : (toSC S).ShortExact) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
          (F.mapHomotopyCategoryPlus.map (descKPlus S))) ≫
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient A).obj S.X₃)) ≫
        Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) (coneδ S hS) =
      Functor.mapδ ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
          DerivedCategory.Plus.ι) (conePlusδ S) ≫
        (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient A).obj S.X₁)))⟦(1 : ℤ)⟧' := by
  have hΦ₂ : Functor.mapδ ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.ι) (conePlusδ S) =
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
          (DerivedCategory.Plus.Qh.map (descKPlus S)) ≫
        Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) (coneδ S hS) := by
    refine Eq.trans (Functor.mapδ_assoc DerivedCategory.Plus.Qh F.rightDerivedFunctorPlus
      DerivedCategory.Plus.ι (conePlusδ S)) ?_
    refine Eq.trans (Functor.mapδ_comp DerivedCategory.Plus.Qh
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) (conePlusδ S)) ?_
    refine Eq.trans (congrArg
      (fun g ↦ Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) g)
      (plusQh_map_descKPlus_comp_coneδ S hS).symm) ?_
    exact Functor.comp_mapδ _ _ _
  have hnat := F.rightDerivedFunctorPlusUnit.naturality (descKPlus S)
  have hcs := Functor.mapδ_commShift
    (Functor.whiskerRight F.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι) (conePlusδ S)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (CategoryTheory.Functor.map_comp DerivedCategory.Plus.ι _ _).symm _) ?_
  refine Eq.trans (eq_whisker (congrArg
    (fun g ↦ DerivedCategory.Plus.ι.map g) hnat) _) ?_
  refine Eq.trans (eq_whisker (CategoryTheory.Functor.map_comp DerivedCategory.Plus.ι _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ hΦ₂.symm) ?_
  exact hcs.symm

omit [HasDerivedCategory A] [EnoughInjectives A] [F.rightDerivedFunctorPlus.CommShift ℤ]
  [NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ] in
/-- `F` applied to `descKPlus` is a quasi-isomorphism when `F` keeps the sequence short exact. -/
theorem isIso_ι_map_plusQh_map_mapHomotopyCategoryPlus_descKPlus
    (hFS : ((toSC S).map (F.mapHomologicalComplex (up ℤ))).ShortExact) :
    IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
      (F.mapHomotopyCategoryPlus.map (descKPlus S)))) := by
  have hdesc : QuasiIso ((F.mapHomologicalComplex (up ℤ)).map
      (CochainComplex.mappingCone.descShortComplex (toSC S))) := by
    rw [← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex F (toSC S)]
    have := CochainComplex.mappingCone.quasiIso_descShortComplex hFS
    infer_instance
  have hw : IsIso (DerivedCategory.Plus.Qh.map
      (F.mapHomotopyCategoryPlus.map (descKPlus S))) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hdesc)
  infer_instance

/-- The unit of `RF` carries the connecting morphism of `F` applied to a short exact sequence
to the connecting morphism of the image under `RF` of the triangle of the sequence: for a
short exact sequence `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` of bounded below complexes which `F` keeps short
exact, the third morphism of `RF(K₁) ⟶ RF(K₂) ⟶ RF(K₃) ⟶ RF(K₁)[1]`, precomposed with the unit
`F(K₃) ⟶ RF(K₃)`, is the connecting morphism of `0 ⟶ F(K₁) ⟶ F(K₂) ⟶ F(K₃) ⟶ 0` followed by
the unit at `K₁`. -/
theorem unit_comp_mapδ_coneδ (hS : (toSC S).ShortExact)
    (hFS : ((toSC S).map (F.mapHomologicalComplex (up ℤ))).ShortExact) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient A).obj S.X₃)) ≫
        Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) (coneδ S hS) =
      (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (up ℤ)).obj (toSC S).X₃) ≫
        DerivedCategory.triangleOfSESδ hFS ≫
          ((DerivedCategory.quotientCompQhIso B).inv.app
            ((F.mapHomologicalComplex (up ℤ)).obj (toSC S).X₁))⟦(1 : ℤ)⟧' ≫
          (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient A).obj S.X₁)))⟦(1 : ℤ)⟧' := by
  have := isIso_ι_map_plusQh_map_mapHomotopyCategoryPlus_descKPlus F S hFS
  refine (cancel_epi (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
    (F.mapHomotopyCategoryPlus.map (descKPlus S))))).1 ?_
  refine Eq.trans (descKPlus_comp_unit_comp_mapδ F S hS) ?_
  have h1 := descKPlus_comp_triangleOfSESδ F S hFS
  have hz : ((DerivedCategory.quotientCompQhIso B).hom.app
        ((F.mapHomologicalComplex (up ℤ)).obj (toSC S).X₁))⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.quotientCompQhIso B).inv.app
        ((F.mapHomologicalComplex (up ℤ)).obj (toSC S).X₁))⟦(1 : ℤ)⟧' = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  exact comp_eq_of_comp_eq _ _ _ _ _ _ _ h1 hz

omit [EnoughInjectives A] in
/-- `coneδ` is `plusδ`, read through the identification of `Plus.Qh` of the homotopy quotient with
`Plus.Q`. -/
theorem coneδ_comp_quotientQhIsoQ (hS : (toSC S).ShortExact) :
    coneδ S hS ≫
        ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ A).hom.app S.X₁)⟦(1 : ℤ)⟧' =
      (StacksDraft.DerivedSectionsComparison.quotientQhIsoQ A).hom.app S.X₃ ≫ plusδ S hS := by
  refine Functor.mapδ_cancel DerivedCategory.Plus.ι _ _ _ _ ?_
  have hq : ∀ K, DerivedCategory.Plus.ι.map
      ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ A).hom.app K) =
        (DerivedCategory.quotientCompQhIso A).hom.app K.obj := fun K ↦
    StacksDraft.DerivedSectionsComparison.liftNatIso_hom_app _ _ _ _ K
  rw [hq, hq, mapδ_ι_plusδ]
  exact mapδ_ι_coneδ S hS

/-- The canonical map `F(K) ⟶ RF(K)` in `D(ℬ)` for a bounded below complex `K`: the unit of
the right derived functor, read through the identifications of the localisations. -/
def unitD (L : CochainComplex.Plus A) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (up ℤ)).obj L.obj) ⟶
      DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L)) :=
  (DerivedCategory.quotientCompQhIso B).inv.app ((F.mapHomologicalComplex (up ℤ)).obj L.obj) ≫
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient A).obj L)) ≫
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlus.map
      ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ A).hom.app L))

/-- The canonical map `F(K) ⟶ RF(K)` carries the connecting morphism of `F` applied to a short
exact sequence of bounded below complexes to the connecting morphism of `RF` applied to its
distinguished triangle, whenever `F` keeps the sequence short exact. -/
theorem triangleOfSESδ_comp_unitD (hS : (toSC S).ShortExact)
    (hFS : ((toSC S).map (F.mapHomologicalComplex (up ℤ))).ShortExact) :
    DerivedCategory.triangleOfSESδ hFS ≫ (unitD F S.X₁)⟦(1 : ℤ)⟧' =
      unitD F S.X₃ ≫
        Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) (plusδ S hS) := by
  have h3 := Functor.mapδ_naturality (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    _ _ _ _ (coneδ_comp_quotientQhIsoQ S hS)
  have hu := unit_comp_mapδ_coneδ F S hS hFS
  dsimp only [unitD]
  refine (whisker_eq _ (Functor.map_comp _ _ _)).trans ?_
  exact unitD_aux _ _ _ _ _ _ _ _ _ _ _ (Functor.map_comp _ _ _) h3 hu
    (Iso.inv_hom_id_app (DerivedCategory.quotientCompQhIso B) _)

end RightDerived

end Stacks.Cohomology.RightDerivedBoundary
