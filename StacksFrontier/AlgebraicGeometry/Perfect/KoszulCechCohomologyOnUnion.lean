module

public import StacksFrontier.Algebra.Homology.Koszul.AlternatingCechTotal
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AlternatingAffineIntersections
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverCofinality
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechIdentification
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparison

/-!
# The alternating Čech complex computes cohomology over a union of basic opens

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`.  For a complex `M^•` of `A`-modules the
total alternating Čech complex of the associated complex of sheaves, taken for the covering of
`U` by the basic opens, computes the hypercohomology of `M̃^•` over `U`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace

universe u

namespace Koszul.DerivedSystem

attribute [local instance] HasDerivedCategory.standard

variable {A : CommRingCat.{u}} {r : ℕ}

/-! ### The covering of the union by the basic opens -/

/-- The open subscheme `U = D(f₁) ∪ ⋯ ∪ D(f_r)` of `X = Spec A`. -/
abbrev openSubscheme (f : Fin r → A) : Scheme.{u} := (unionOfBasicOpens f).toScheme

/-- The covering of `U` by the basic opens `D(fᵢ)`, indexed in the universe of the ring. -/
abbrev unionCover (f : Fin r → A) : ULift.{u} (Fin r) → (openSubscheme f).Opens :=
  fun j ↦ (unionOfBasicOpens f).ι ⁻¹ᵁ basicOpens f j.down

/-- The basic opens cover `U`. -/
theorem iSup_unionCover (f : Fin r → A) :
    (⊤ : (openSubscheme f).Opens) = iSup (unionCover f) := by
  have h : iSup (unionCover f) =
      (unionOfBasicOpens f).ι ⁻¹ᵁ (⨆ j : ULift.{u} (Fin r), basicOpens f j.down) :=
    (Opens.map_iSup _ _).symm
  rw [h, show (⨆ j : ULift.{u} (Fin r), basicOpens f j.down) = unionOfBasicOpens f from
    Equiv.ulift.iSup_comp (g := basicOpens f)]
  exact ((unionOfBasicOpens f).ι_preimage_self).symm

/-- A finite intersection of the basic opens `D(fᵢ)` is an affine open of `X = Spec A`. -/
theorem isAffineOpen_iInf_basicOpens (f : Fin r → A) {p : ℕ}
    (s : Fin (p + 1) → ULift.{u} (Fin r)) :
    IsAffineOpen (⨅ k, basicOpens f (s k).down) := by
  have h : ∀ i : Fin r, basicOpens f i =
      (Spec A).basicOpen ((Scheme.ΓSpecIso A).inv (f i)) :=
    fun i ↦ (basicOpen_eq_of_affine (f i)).symm
  simp only [h]
  exact Stacks.Cohomology.Cech.isAffineOpen_iInf_basicOpen (isAffineOpen_top (Spec A))
    (fun i ↦ (Scheme.ΓSpecIso A).inv (f i)) (fun k ↦ (s k).down)

/-- The intersections occurring in the Čech complex of the covering of `U` by the basic opens
are affine opens of `U`. -/
theorem isAffineOpen_iInf_unionCover (f : Fin r → A) {p : ℕ}
    (s : Fin (p + 1) → ULift.{u} (Fin r)) :
    IsAffineOpen (⨅ k, unionCover f (s k)) := by
  have h : (⨅ k, unionCover f (s k)) =
      (unionOfBasicOpens f).ι ⁻¹ᵁ (⨅ k, basicOpens f (s k).down) := by
    apply Opens.ext
    simpa only [Opens.coe_iInf, Opens.map_coe] using (Set.preimage_iInter).symm
  rw [h]
  refine (isAffineOpen_iInf_basicOpens f s).preimage_of_isOpenImmersion _ ?_
  rw [Scheme.Opens.opensRange_ι]
  exact le_trans (iInf_le _ 0) (le_iSup (basicOpens f) (s 0).down)

/-- **The alternating Čech complex of the covering of `U` by the basic opens computes derived
global sections on `U`**, at every complex of quasi-coherent modules. -/
theorem isIso_alternatingCechToDerivedComparison_unionCover (f : Fin r → A)
    (K : CochainComplex (SheafOfModules.{u} (openSubscheme f).ringCatSheaf) ℤ)
    (hK : ∀ q : ℤ, (K.X q).IsQuasicoherent) :
    IsIso ((Stacks.Cech.alternatingCechToDerivedComparison _ (openSubscheme f).ringCatSheaf
      (unionCover f) (iSup_unionCover f)).app K) :=
  Stacks.Cech.isIso_alternatingCechToDerivedComparison_of_isAffineOpen (openSubscheme f)
    (unionCover f) (iSup_unionCover f) (fun _ s ↦ isAffineOpen_iInf_unionCover f s) K hK

/-! ### Restriction to the union -/

/-- Restriction of modules along the open immersion `U ⟶ X` is restriction to the open
subspace `U`. -/
theorem restrictFunctor_eq_jStar {X : Scheme.{u}} (U : X.Opens) :
    Scheme.Modules.restrictFunctor U.ι = jStar U X.ringCatSheaf := by
  unfold Scheme.Modules.restrictFunctor ExtensionByZeroModules.jStar
  congr 1
  ext V
  simp only [op_unop, Scheme.Opens.ι_appIso, Iso.refl_inv, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.op_obj, ObjectProperty.FullSubcategory.id_hom]
  rfl

/-- The identification of the intersections of the covering of `U` with the corresponding
intersections of the basic opens of `X`. -/
def basicIntersectionIso (f : Fin r → A) (p : ℕ) (i : Fin (p + 1) → ULift.{u} (Fin r)) :
    (TopCat.Presheaf.imF (unionOfBasicOpens f)).obj (CechCochains.inter (unionCover f) i) ≅
      CechCochains.inter (fun j : ULift.{u} (Fin r) ↦ basicOpens f j.down) i := by
  refine eqToIso (Eq.trans (Topology.IsOpenEmbedding.functor_obj_iInf _
    (unionOfBasicOpens f).isOpenEmbedding _) ?_)
  refine iInf_congr fun k ↦ Eq.trans (Opens.functor_map_eq_inf _ _) ?_
  exact inf_of_le_left (le_iSup (basicOpens f) (i k).down)

/-- Restriction of complexes of modules to the open subscheme `U`. -/
abbrev restrictionComplexFunctor (f : Fin r → A) :
    CochainComplex (SheafOfModules.{u} (Spec A).ringCatSheaf) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (openSubscheme f).ringCatSheaf) ℤ :=
  (Scheme.Modules.restrictFunctor (unionOfBasicOpens f).ι).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The abelian presheaf underlying the restriction of a module to `U` is the restriction of
the underlying abelian presheaf. -/
def restrictionPresheafIso (f : Fin r → A) :
    Scheme.Modules.restrictFunctor (unionOfBasicOpens f).ι ⋙
        Scheme.Modules.toPresheaf (openSubscheme f) ≅
      Scheme.Modules.toPresheaf (Spec A) ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
          (TopCat.Presheaf.imF (unionOfBasicOpens f)).op :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun V ↦ Iso.refl _) (by intros; rfl))
    (by intros; rfl)

/-- The same identification on complexes. -/
def restrictionPresheafComplexIso (f : Fin r → A) :
    restrictionComplexFunctor f ⋙
        Stacks.Cech.underlyingPresheafComplexFunctor _ (openSubscheme f).ringCatSheaf ≅
      Stacks.Cech.underlyingPresheafComplexFunctor _ (Spec A).ringCatSheaf ⋙
        ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
            (TopCat.Presheaf.imF (unionOfBasicOpens f)).op).mapHomologicalComplex
          (ComplexShape.up ℤ) := by
  letI : (Scheme.Modules.restrictFunctor (unionOfBasicOpens f).ι ⋙
      Scheme.Modules.toPresheaf (openSubscheme f)).PreservesZeroMorphisms := ⟨by intros; rfl⟩
  letI : (Scheme.Modules.toPresheaf (Spec A) ⋙
      (Functor.whiskeringLeft (Opens (openSubscheme f))ᵒᵖ (Opens (Spec A))ᵒᵖ
          AddCommGrpCat.{u}).obj
        (TopCat.Presheaf.imF (unionOfBasicOpens f)).op).PreservesZeroMorphisms :=
    ⟨by intros; rfl⟩
  exact NatIso.mapHomologicalComplex (restrictionPresheafIso f) (ComplexShape.up ℤ)

/-- **The total alternating Čech complex of the basic opens is that of the covering of `U`.** -/
def cechRestrictionIso (f : Fin r → A) :
    Stacks.Cech.underlyingPresheafComplexFunctor _ (Spec A).ringCatSheaf ⋙
        Stacks.Cech.alternatingCechTotalComplexFunctor
          (fun j : ULift.{u} (Fin r) ↦ basicOpens f j.down) ≅
      restrictionComplexFunctor f ⋙
        Stacks.Cech.underlyingPresheafComplexFunctor _ (openSubscheme f).ringCatSheaf ⋙
        Stacks.Cech.alternatingCechTotalComplexFunctor (unionCover f) :=
  Functor.isoWhiskerLeft _
      (Stacks.Koszul.Cech.alternatingCechTotalIntersectionsNatIso
        (fun j : ULift.{u} (Fin r) ↦ basicOpens f j.down) (unionCover f)
        (TopCat.Presheaf.imF (unionOfBasicOpens f)) (basicIntersectionIso f)) ≪≫
    Functor.isoWhiskerRight (restrictionPresheafComplexIso f).symm
      (Stacks.Cech.alternatingCechTotalComplexFunctor (unionCover f))

/-! ### The Koszul-side Čech complex -/

/-- Degreewise sheafification of a complex of `A`-modules. -/
abbrev tildeComplexFunctor (A : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Spec A).ringCatSheaf) ℤ :=
  (sheafifyModule A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The total alternating Čech complex of the associated complex of sheaves, with the
covering indexed in the universe of the ring. -/
def koszulCechTotalIso (f : Fin r → A) :
    Koszul.alternatingCechTotalFunctor f ≅
      tildeComplexFunctor A ⋙
        Stacks.Cech.underlyingPresheafComplexFunctor _ (Spec A).ringCatSheaf ⋙
        Stacks.Cech.alternatingCechTotalComplexFunctor
          (fun j : ULift.{u} (Fin r) ↦ basicOpens f j.down) :=
  Functor.isoWhiskerLeft _ (Stacks.Koszul.Cech.alternatingCechTotalUliftNatIso (basicOpens f))

/-! ### Derived sections on the union -/

/-- Derived restriction to an open subspace is the functor induced by restriction: restriction
of modules is exact, so the functor it induces on derived categories already is its total right
derived functor. -/
def derivedRestrictionIso {Y : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (V : Opens Y) :
    derivedRestriction O V ≅ (jStar V O).mapDerivedCategory := by
  let J := jStar V O
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)
  letI : J.mapDerivedCategory.IsRightDerivedFunctor J.mapDerivedCategoryFactorsh.inv W :=
    Functor.isRightDerivedFunctor_of_inverts W J.mapDerivedCategory
      J.mapDerivedCategoryFactorsh
  exact Functor.rightDerivedNatIso (derivedRestriction O V) J.mapDerivedCategory
    ((homotopyRestriction O V).totalRightDerivedUnit DerivedCategory.Qh W)
    J.mapDerivedCategoryFactorsh.inv W (Iso.refl _)

/-- Sections over the whole of `U` have a total right derived functor. -/
theorem subspaceSections_hasRightDerivedFunctor (f : Fin r → A) :
    (homotopySectionsOnOpen (openSubscheme f).ringCatSheaf ⊤).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (openSubscheme f).ringCatSheaf) (ComplexShape.up ℤ)) := by
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
    u + 1, u + 1, u + 1, u + 1, u + 1}
    (homotopySectionsOnOpen (openSubscheme f).ringCatSheaf ⊤)
    Stacks.Cohomology.Localization.enoughKInjectives).1
  infer_instance

attribute [local instance] subspaceSections_hasRightDerivedFunctor

/-- **The total alternating Čech complex of the covering of `U` computes derived sections over
`U`** of a complex of sheaves coming from a complex of `A`-modules. -/
def cechDerivedSectionsIso (f : Fin r → A) :
    Koszul.alternatingCechTotalFunctor f ⋙ DerivedCategory.Q ≅
      tildeComplexFunctor A ⋙ restrictionComplexFunctor f ⋙ DerivedCategory.Q ⋙
        derivedSectionsOnOpen (openSubscheme f).ringCatSheaf ⊤ := by
  let T := tildeComplexFunctor A ⋙ restrictionComplexFunctor f
  let α := Functor.whiskerLeft T (Stacks.Cech.alternatingCechToDerivedComparison _
    (openSubscheme f).ringCatSheaf (unionCover f) (iSup_unionCover f))
  have hα : IsIso α := by
    have : ∀ K, IsIso (α.app K) := by
      intro K
      refine isIso_alternatingCechToDerivedComparison_unionCover f _ (fun q ↦ ?_)
      change ((Scheme.Modules.restrictFunctor (unionOfBasicOpens f).ι).obj
        ((sheafifyModule A).obj (K.X q))).IsQuasicoherent
      have : ((sheafifyModule A).obj (K.X q)).IsQuasicoherent :=
        inferInstanceAs ((tilde.functor A).obj (K.X q)).IsQuasicoherent
      exact Scheme.Modules.isQuasicoherent_restrictFunctor (unionOfBasicOpens f).ι
        ((sheafifyModule A).obj (K.X q))
    exact NatIso.isIso_of_isIso_app α
  exact Functor.isoWhiskerRight (koszulCechTotalIso f) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (tildeComplexFunctor A)
      (cechRestrictionIso f)) DerivedCategory.Q ≪≫
    @asIso _ _ _ _ α hα ≪≫
    Functor.isoWhiskerLeft T
      (Stacks.Koszul.Cech.globalSectionsResolutionIso (openSubscheme f).ringCatSheaf)

/-- Degreewise restriction to `U`, localized, is derived restriction to `U`. -/
def restrictionComplexDerivedIso (f : Fin r → A) :
    restrictionComplexFunctor f ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ restrictionToUnion f := by
  let U := unionOfBasicOpens f
  let O := (Spec A).ringCatSheaf
  let J := jStar U O
  let e : restrictionComplexFunctor f ≅ J.mapHomologicalComplex (ComplexShape.up ℤ) :=
    @NatIso.mapHomologicalComplex _ _ _ _ _ _ _ _ _ _ ⟨by intros; rfl⟩
      (eqToIso (restrictFunctor_eq_jStar U)) (ComplexShape.up ℤ)
  exact Functor.isoWhiskerRight e DerivedCategory.Q ≪≫
    J.mapDerivedCategoryFactors.symm ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q (derivedRestrictionIso O U).symm

/-- **The degree-zero cohomology of the total alternating Čech complex is degree-zero
hypercohomology over `U`.** -/
def cechCohomologyIso (f : Fin r → A) :
    Koszul.alternatingCechTotalFunctor f ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0 ≅
      tildeComplexFunctor A ⋙ DerivedCategory.Q ⋙ sectionsOnUnion f :=
  (Functor.isoWhiskerLeft (Koszul.alternatingCechTotalFunctor f)
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0)).symm ≪≫
    Functor.isoWhiskerRight (cechDerivedSectionsIso f)
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0) ≪≫
    Functor.isoWhiskerLeft (tildeComplexFunctor A)
      (Functor.isoWhiskerRight (restrictionComplexDerivedIso f)
        (derivedSectionsOnOpen (openSubscheme f).ringCatSheaf ⊤ ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0)) ≪≫
    Functor.isoWhiskerLeft (tildeComplexFunctor A ⋙ DerivedCategory.Q)
      (cohomologyOnOpenIsoRestriction (Spec A).ringCatSheaf (unionOfBasicOpens f) 0).symm

end Koszul.DerivedSystem

end
