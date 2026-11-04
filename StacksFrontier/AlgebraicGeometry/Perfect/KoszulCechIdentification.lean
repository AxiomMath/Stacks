module

public import Mathlib.Algebra.Category.Grp.Ulift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplexFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AlternatingDerivedGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace

/-!
# Morphism diagrams, K-injective models and transport of the alternating Čech complex

Machinery used in the identification of the colimit of the morphism groups out of a Koszul
system with Čech cohomology over a union of basic opens.

## Main results

* `Stacks.Koszul.Cech.homDiagramMapIso`: a fully faithful additive functor identifies the
  diagram of morphism groups out of an inverse system with the diagram for the image system.
* `Stacks.Koszul.Cech.resolutionDerivedIso`: on a functorial K-injective resolution, the
  degreewise image of an additive functor computes its total right derived functor.
* `Stacks.Koszul.Cech.alternatingCechTotalIntersectionsNatIso` and
  `Stacks.Koszul.Cech.alternatingCechTotalUliftNatIso`: the total alternating Čech complex is
  unchanged by a functor of opens identifying the intersections of two families, and by lifting
  the index type of the family to another universe.
* `Stacks.Koszul.Cech.globalSectionsResolutionIso`: derived global sections computed on a
  functorial K-injective resolution is derived sections over the whole space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe wG wD wC t w v u

namespace Stacks.Koszul.Cech

/-! ### Diagrams of morphism groups out of an inverse system -/

section HomDiagrams

variable {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type w} [Category.{v} D] [Preadditive D]

/-- The diagram `e ↦ Hom(Iₑ, -)` of morphism groups out of an inverse system indexed by `ℕᵒᵖ`. -/
abbrev homDiagramFunctor (I : ℕᵒᵖ ⥤ C) : C ⥤ (ℕ ⥤ AddCommGrpCat.{v}) :=
  preadditiveYoneda ⋙ (Functor.whiskeringLeft ℕ Cᵒᵖ AddCommGrpCat.{v}).obj I.rightOp

/-- **A fully faithful additive functor identifies the diagrams of morphism groups.** -/
def homDiagramMapIso (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive]
    (I : ℕᵒᵖ ⥤ C) : homDiagramFunctor I ≅ F ⋙ homDiagramFunctor (I ⋙ F) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun n ↦ (AddEquiv.ofBijective F.mapAddHom
      ⟨F.map_injective, F.map_surjective⟩).toAddCommGrpIso)
    (by
      intro i j g
      ext h
      exact F.map_comp _ _))
    (by
      intro X Y g
      ext n h
      exact F.map_comp _ _)

end HomDiagrams

/-! ### Right derived functors on a functorial K-injective resolution -/

section DerivedResolutions

variable {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{t} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)

/-- The comparison from the degreewise image of `F`, localized, to a right derived functor
of `F`. -/
def derivedComplexComparison :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF :=
  (Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
    (DerivedCategory.quotientCompQhIso D)).inv ≫
  (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    DerivedCategory.Qh).inv ≫
  Functor.whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ)) α ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) RF).hom

variable [IsGrothendieckAbelian.{wG} C]
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- On a K-injective complex the comparison is invertible. -/
theorem derivedComplexComparison_isIso (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso ((derivedComplexComparison F RF α).app I) := by
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    (C := C) _ RF α I
  dsimp [derivedComplexComparison]
  infer_instance

/-- **On a functorial K-injective resolution the degreewise image of `F` computes `RF`.** -/
def resolutionDerivedIso :
    Stacks.Injectives.kInjectiveResolutionFunctor C ⋙
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RF := by
  let β := Functor.whiskerLeft (Stacks.Injectives.kInjectiveResolutionFunctor C)
    (derivedComplexComparison F RF α)
  letI : IsIso β := by
    have : ∀ K, IsIso (β.app K) := fun K ↦ derivedComplexComparison_isIso F RF α _
    exact NatIso.isIso_of_isIso_app β
  let γ := Functor.whiskerRight (Stacks.Injectives.kInjectiveResolutionInclusion C)
    (DerivedCategory.Q ⋙ RF)
  letI : IsIso γ := by
    have : ∀ K, IsIso (γ.app K) := by
      intro K
      change IsIso (RF.map (DerivedCategory.Q.map
        ((Stacks.Injectives.kInjectiveResolutionInclusion C).app K)))
      infer_instance
    exact NatIso.isIso_of_isIso_app γ
  exact asIso β ≪≫ (asIso γ).symm

end DerivedResolutions

/-- The universe lift of abelian groups into their own universe is the identity functor. -/
def uliftSelfIso : AddCommGrpCat.uliftFunctor.{u, u} ≅ 𝟭 AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun X ↦ Stacks.Cech.uliftSectionsIso X) (by intros; rfl)

/-! ### Transporting the alternating Čech complex along a functor of opens -/

section CechRestriction

open TopologicalSpace CechCochains

-- (no transparency relaxation needed)

/-- Two morphisms of opens with the same source and target agree, so a presheaf cannot tell
them apart. -/
theorem presheaf_map_eq_of_thin {X : TopCat.{u}} (F : TopCat.Presheaf AddCommGrpCat.{t} X)
    {V W : (Opens X)ᵒᵖ} (a b : V ⟶ W) : F.map a = F.map b :=
  congrArg F.map (Quiver.Hom.unop_inj (Subsingleton.elim a.unop b.unop))

/-- Two restrictions of a presheaf along composable pairs of inclusions with the same total
source and target agree on sections. -/
theorem presheaf_map_two_eq_of_thin {X : TopCat.{u}} (F : TopCat.Presheaf AddCommGrpCat.{t} X)
    {V W W' Z : (Opens X)ᵒᵖ} (a : V ⟶ W) (b : W ⟶ Z) (a' : V ⟶ W') (b' : W' ⟶ Z)
    (x : (F.obj V : Type t)) : F.map b (F.map a x) = F.map b' (F.map a' x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.map_comp, ← F.map_comp]
  exact ConcreteCategory.congr_hom (presheaf_map_eq_of_thin F _ _) x

variable {X : TopCat.{u}} {Y : TopCat.{v}} {I : Type w}
    (U : I → Opens X) (V : I → Opens Y) (T : Opens Y ⥤ Opens X)
    (e : ∀ p (i : Fin (p + 1) → I), T.obj (inter V i) ≅ inter U i)
    (F : TopCat.Presheaf AddCommGrpCat.{t} X)

/-- Restriction along the identifications of the intersections, on alternating cochains. -/
def alternatingCechIntersectionsEquiv (p : ℕ) :
    alternatingSubgroup U F p ≃+ alternatingSubgroup V (T.op ⋙ F) p where
  toFun s := ⟨fun i ↦ F.map (e p i).hom.op (s.1 i), by
    refine ⟨fun i hi ↦ ?_, fun i j k hjk ↦ ?_⟩
    · change F.map (e p i).hom.op (s.1 i) = 0
      rw [s.2.1 i hi, map_zero]
    · change F.map (e p (i ∘ Equiv.swap j k)).hom.op
          (s.1 (i ∘ Equiv.swap j k)) =
        - (T.op ⋙ F).map _ (F.map (e p i).hom.op (s.1 i))
      rw [s.2.2 i j k hjk, map_neg]
      congr 1
      exact presheaf_map_two_eq_of_thin F _ _ _ _ (s.1 i)⟩
  invFun s := ⟨fun i ↦ F.map (e p i).inv.op (s.1 i), by
    refine ⟨fun i hi ↦ ?_, fun i j k hjk ↦ ?_⟩
    · change F.map (e p i).inv.op (s.1 i) = 0
      rw [s.2.1 i hi, map_zero]
    · change F.map (e p (i ∘ Equiv.swap j k)).inv.op
          (s.1 (i ∘ Equiv.swap j k)) =
        - F.map _ (F.map (e p i).inv.op (s.1 i))
      rw [s.2.2 i j k hjk, map_neg]
      congr 1
      exact presheaf_map_two_eq_of_thin F _ _ _ _ (s.1 i)⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    change (F.map (e p i).hom.op ≫ F.map (e p i).inv.op) (s.1 i) = s.1 i
    rw [← F.map_comp, ← op_comp, Iso.inv_hom_id, op_id, F.map_id]
    rfl
  right_inv s := by
    apply Subtype.ext
    funext i
    change (F.map (e p i).inv.op ≫ F.map (e p i).hom.op) (s.1 i) = s.1 i
    rw [← F.map_comp, ← op_comp, Iso.hom_inv_id, op_id, F.map_id]
    rfl
  map_add' s s' := Subtype.ext <| funext fun _ ↦ map_add _ _ _

/-- The alternating Čech complexes of a family of opens and of a family identified with it
along a functor of opens agree. -/
def alternatingCechIntersectionsIso :
    Stacks.Cech.alternatingCechComplex U F ≅
      Stacks.Cech.alternatingCechComplex V (T.op ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ (alternatingCechIntersectionsEquiv U V T e F p).toAddCommGrpIso)
    (fun p q hpq ↦ by
      obtain rfl : p + 1 = q := hpq
      rw [Stacks.Cech.alternatingCechComplex_d, Stacks.Cech.alternatingCechComplex_d]
      ext s
      refine Subtype.ext <| funext fun i ↦ ?_
      change (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (T.op ⋙ F).map _ (F.map (e p (i ∘ j.succAbove)).hom.op
          (s.1 (i ∘ j.succAbove)))) =
        F.map (e (p + 1) i).hom.op (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          F.map _ (s.1 (i ∘ j.succAbove)))
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_zsmul]
      congr 1
      exact presheaf_map_two_eq_of_thin F _ _ _ _ (s.1 (i ∘ j.succAbove)))

/-- The identification of alternating Čech complexes is natural in the coefficient
presheaf. -/
def alternatingCechIntersectionsNatIso :
    Stacks.Cech.alternatingCechComplexFunctor U ≅
      (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{t}).obj T.op ⋙
        Stacks.Cech.alternatingCechComplexFunctor V :=
  NatIso.ofComponents (alternatingCechIntersectionsIso U V T e) (by
    intro F G a
    ext p s
    exact Subtype.ext <| funext fun i ↦
      ConcreteCategory.congr_hom (a.naturality (e p i).hom.op).symm (s.1 i))

/-- Presheaves of abelian groups on `X` form a preadditive category. -/
local instance : Preadditive (TopCat.Presheaf AddCommGrpCat.{t} X) :=
  inferInstanceAs (Preadditive ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{t}))
/-- Presheaves of abelian groups on `Y` form a preadditive category. -/
local instance : Preadditive (TopCat.Presheaf AddCommGrpCat.{t} Y) :=
  inferInstanceAs (Preadditive ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{t}))

/-- **The total alternating Čech complexes agree**, naturally in the complex of coefficient
presheaves. -/
def alternatingCechTotalIntersectionsNatIso :
    Stacks.Cech.alternatingCechTotalComplexFunctor U ≅
      ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ
            AddCommGrpCat.{t}).obj T.op).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Stacks.Cech.alternatingCechTotalComplexFunctor V := by
  let W := (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{t}).obj T.op
  letI : W.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  letI : (Stacks.Cech.alternatingCechComplexFunctor V).PreservesZeroMorphisms :=
    Stacks.Cech.alternatingCechComplexFunctor_preservesZeroMorphisms V
  let B := ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max w t}
  let e' := NatIso.mapHomologicalComplex
    (Functor.isoWhiskerRight (alternatingCechIntersectionsNatIso U V T e) B) (ComplexShape.up ℤ)
  exact Functor.isoWhiskerRight e'
    (HomologicalComplex₂.flipFunctor AddCommGrpCat.{max w t} (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{max w t} (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ))

end CechRestriction

/-! ### Lifting the index type of a family of opens -/

section CechReindex

open TopologicalSpace CechCochains

-- (no transparency relaxation needed)

variable {X : TopCat.{u}} {I : Type w} (U : I → Opens X)
    (F : TopCat.Presheaf AddCommGrpCat.{t} X)

/-- Reindexing alternating cochains along the universe lift of the index type. -/
def alternatingCechUliftEquiv (p : ℕ) :
    alternatingSubgroup U F p ≃+
      alternatingSubgroup (fun j : ULift.{t} I ↦ U j.down) F p where
  toFun s := ⟨fun i ↦ s.1 (fun k ↦ (i k).down),
    ⟨fun _ hi ↦ s.2.1 _ (fun hinj ↦ hi fun _ _ hab ↦ hinj (congrArg ULift.down hab)),
      fun i j k hjk ↦ s.2.2 (fun k ↦ (i k).down) j k hjk⟩⟩
  invFun s := ⟨fun i ↦ s.1 (fun k ↦ ULift.up.{t} (i k)),
    ⟨fun _ hi ↦ s.2.1 _ (fun hinj ↦ hi fun _ _ hab ↦ hinj (congrArg ULift.up hab)),
      fun i j k hjk ↦ s.2.2 (fun k ↦ ULift.up.{t} (i k)) j k hjk⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The alternating Čech complex is unchanged by lifting the index type to another universe. -/
def alternatingCechUliftIso :
    Stacks.Cech.alternatingCechComplex U F ≅
      Stacks.Cech.alternatingCechComplex (fun j : ULift.{t} I ↦ U j.down) F :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ (alternatingCechUliftEquiv U F p).toAddCommGrpIso)
    (fun p q hpq ↦ by
      obtain rfl : p + 1 = q := hpq
      rw [Stacks.Cech.alternatingCechComplex_d, Stacks.Cech.alternatingCechComplex_d]
      ext s
      rfl)

/-- Lifting the index type is natural in the coefficient presheaf. -/
def alternatingCechUliftNatIso :
    Stacks.Cech.alternatingCechComplexFunctor.{u, w, t} U ≅
      Stacks.Cech.alternatingCechComplexFunctor.{u, max t w, t}
        (fun j : ULift.{t} I ↦ U j.down) :=
  NatIso.ofComponents (fun F ↦ alternatingCechUliftIso U F) (by
    intro F G a
    ext p s
    rfl)

/-- Presheaves of abelian groups on `X` form a preadditive category. -/
local instance : Preadditive (TopCat.Presheaf AddCommGrpCat.{t} X) :=
  inferInstanceAs (Preadditive ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{t}))

/-- **The total alternating Čech complex is unchanged by lifting the index type.** -/
def alternatingCechTotalUliftNatIso :
    Stacks.Cech.alternatingCechTotalComplexFunctor.{u, w, t} U ≅
      Stacks.Cech.alternatingCechTotalComplexFunctor.{u, max t w, t}
        (fun j : ULift.{t} I ↦ U j.down) := by
  letI : (Stacks.Cech.alternatingCechComplexFunctor.{u, w, t} U).PreservesZeroMorphisms :=
    Stacks.Cech.alternatingCechComplexFunctor_preservesZeroMorphisms U
  letI : (Stacks.Cech.alternatingCechComplexFunctor.{u, max t w, t}
      (fun j : ULift.{t} I ↦ U j.down)).PreservesZeroMorphisms :=
    Stacks.Cech.alternatingCechComplexFunctor_preservesZeroMorphisms _
  let B := ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max w t}
  let e' := NatIso.mapHomologicalComplex
    (Functor.isoWhiskerRight (alternatingCechUliftNatIso U) B)
    (ComplexShape.up ℤ)
  exact Functor.isoWhiskerRight e'
    (HomologicalComplex₂.flipFunctor AddCommGrpCat.{max w t} (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{max w t} (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ))

end CechReindex

/-! ### Derived global sections in the K-injective-resolution model -/

section GlobalSections

open TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The complex of global sections of a complex of sheaves of modules, in the two spellings used
by the Čech comparison and by derived sections over an open. -/
def ordinaryGlobalSectionsIso :
    Stacks.Cech.underlyingPresheafComplexFunctor X O ⋙
        Stacks.Cech.globalSectionsUliftComplexFunctor.{u, u, u} X ≅
      (Stacks.Cohomology.OpenSubspace.sectionsOnOpen O ⊤).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex
    (Functor.isoWhiskerLeft
      (SheafOfModules.forget O ⋙ PresheafOfModules.toPresheaf O.obj ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) uliftSelfIso ≪≫
      Functor.rightUnitor _) (ComplexShape.up ℤ)

/-- **Derived global sections computed on a functorial K-injective resolution is derived
sections over the whole space.** -/
def globalSectionsResolutionIso
    [(Stacks.Cohomology.OpenSubspace.homotopySectionsOnOpen O ⊤).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    Stacks.Cech.unboundedDerivedGlobalSectionsFunctor X O ≅
      DerivedCategory.Q ⋙ Stacks.Cohomology.OpenSubspace.derivedSectionsOnOpen O ⊤ :=
  Functor.isoWhiskerLeft (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O))
    (Functor.isoWhiskerRight (ordinaryGlobalSectionsIso O) DerivedCategory.Q) ≪≫
  resolutionDerivedIso (Stacks.Cohomology.OpenSubspace.sectionsOnOpen O ⊤)
    (Stacks.Cohomology.OpenSubspace.derivedSectionsOnOpen O ⊤)
    ((Stacks.Cohomology.OpenSubspace.homotopySectionsOnOpen O ⊤).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)))

end GlobalSections

end Stacks.Koszul.Cech

end
