module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.TwistQuadrupleTwisting
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegChart
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.TwistTensor.UniversalVeroneseSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjFunctorSurjective
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartHomUniversal
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartAgreement
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineFdRepresentable
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineScaleRepresentation

/-!
# The twisting of the glued twists, compared with the absolute universal family on a chart

Let `U` be an affine open of the base and `φ` a morphism into the absolute degree-`d` open
`U_d ⊆ Proj Γ(U, 𝒜)`. For `ρ = φ ≫ (chart of U)` the pullback along `ρ` of the glued twist
`𝒪(nd)` of [Stacks, Tag 01NR] is identified with the `n`-th tensor power of `φ^*𝒪_{U_d}(d)`,
and this identification carries the pullback of the homogeneous-section map `ψ_{nd}` to the
pullback along `φ` of the universal family of [Stacks, Tag 01N9]. This is the chart-wise
comparison the proof of [Stacks, Tag 01O1] rests on.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeVeroneseTwists
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents (universalTwist)
open Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple (universalVeroneseSections)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullbackNatTensorPowIso pullSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A) (d : ℕ)
  (U : S.Opens) (hU : IsAffineOpen U)

/-! ### The absolute half of the comparison -/

/-- The chart identification `chart^*𝒪(m) ≅ 𝒪_{Proj Γ(U, 𝒜)}(m)` in inverse-image form. -/
def chartPieceIso (m : ℤ) :
    (Scheme.Modules.pullback ((relativeProj A).chart U hU)).obj (D.algebra.piece m) ≅
      twistingSheaf (A.grading U) m :=
  let := D.chartData.chart_isOpenImmersion U hU
  ((Scheme.Modules.restrictFunctorIsoPullback ((relativeProj A).chart U hU)).app
      (D.algebra.piece m)).symm ≪≫ D.chartData.chartIso U hU m

/-- **The absolute half of the comparison.** For `ρ = φ ≫ (chart of U)` with `φ` through the
absolute degree-`d` open, `ρ^*𝒪(nd) ≅ (φ^*𝒪_{U_d}(d))^{⊗ n}`. -/
def chartAbsIso {Y : Scheme.{u}}
    (φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).toScheme)
    (ρ : Y ⟶ (relativeProj A).scheme)
    (hρ : ρ = toProj (A.grading U) φ ≫ (relativeProj A).chart U hU) (n : ℕ) :
    (Scheme.Modules.pullback ρ).obj (D.algebra.piece ((n * d : ℕ) : ℤ)) ≅
      natTensorPow ((Scheme.Modules.pullback φ).obj (universalTwist (A.grading U) d)) n :=
  (Scheme.Modules.pullbackCongr hρ).app _ ≪≫
    ((Scheme.Modules.pullbackComp (toProj (A.grading U) φ)
      ((relativeProj A).chart U hU)).app _).symm ≪≫
    (Scheme.Modules.pullback (toProj (A.grading U) φ)).mapIso
      (chartPieceIso D U hU ((n * d : ℕ) : ℤ)) ≪≫
    ((Scheme.Modules.pullbackComp φ
      (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι).app _).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso
      (ProjTwistTensorPowDegreeOpen.thetaNat (A.grading U) d n).symm ≪≫
    (pullbackNatTensorPowIso φ (universalTwist (A.grading U) d) n).symm

/-! ### The chart identification on the homogeneous sections -/

/-- A section heterogeneously equal to a section over an equal open is its restriction. -/
theorem eq_map_of_heq {X : Scheme.{u}} (M : X.Modules) {V₁ V₂ : X.Opens} (h : V₁ = V₂)
    (t : M.val.obj (op V₁)) (s : M.val.obj (op V₂)) (hts : HEq t s) :
    t = M.val.map (homOfLE h.le).op s := by
  subst h
  refine (eq_of_heq hts).trans ?_
  rw [show (homOfLE (le_refl V₁)).op = 𝟙 (op V₁) from Subsingleton.elim _ _]
  simp

/-- **The chart identification carries the pulled-back homogeneous section to the absolute
one.** For `a` a section of `𝒜_k` over `U`, the pullback along the chart of `ψ_k(a)` is carried by
`chartPieceIso` to the global section of `𝒪(k)` on `Proj Γ(U, 𝒜)` that `a` defines. -/
theorem chartPieceIso_pullbackSection (k : ℕ) (a : A.sectionPieces U k)
    (h : (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens) ≤
      (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)) :
    ((chartPieceIso D U hU ((k : ℕ) : ℤ)).hom.app ⊤)
        (Scheme.Modules.pullbackSection ((relativeProj A).chart U hU)
          (D.algebra.piece ((k : ℕ) : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ U) ⊤ h
          ((D.psiTransposeNat k).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).unit.app
              (A.piece ((k : ℕ) : ℤ))).val.app (op U) a))) =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) k
        ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩ := by
  let := D.chartData.chart_isOpenImmersion U hU
  have hle : (relativeProj A).chart U hU ''ᵁ ⊤ ≤ (relativeProj A).toBase ⁻¹ᵁ U :=
    (D.chartData.chart_range U hU).le
  have h1 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection
    ((relativeProj A).chart U hU) (D.algebra.piece ((k : ℕ) : ℤ))
    ((relativeProj A).toBase ⁻¹ᵁ U) ⊤ h hle
    ((D.psiTransposeNat k).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).unit.app
        (A.piece ((k : ℕ) : ℤ))).val.app (op U) a))
  have h2 := D.psiTransposeNat_chart U hU k a
  have h3 : HEq (D.chartData.mapSection U hU (k : ℤ) ⊤
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) k
        ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩))
      ((D.psiTransposeNat k).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).unit.app
          (A.piece ((k : ℕ) : ℤ))).val.app (op U) a)) := by
    rw [h2]
    first
      | exact eqRec_heq _ _
      | exact cast_heq _ _
      | simp
  have h4 := eq_map_of_heq (D.algebra.piece ((k : ℕ) : ℤ)) (D.chartData.chart_range U hU) _ _ h3
  refine (congrArg (fun z => (D.chartData.chartIso U hU ((k : ℕ) : ℤ)).hom.val.app (op ⊤) z)
    (h1.trans h4.symm)).trans ?_
  exact congrArg (fun φ => φ.val.app (op ⊤)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) k
      ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩))
    (D.chartData.chartIso U hU ((k : ℕ) : ℤ)).inv_hom_id

/-! ### Two spellings of the unit of the pullback adjunction -/

/-- The unit of `g^* ⊣ g_*` over the ringed-space morphism is the unit of the scheme-level
adjunction, on sections. -/
theorem pullbackUnit_eq_unit {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) (V : Y.Opens)
    (x : M.val.obj (op V)) :
    pullbackUnit (ringedSpaceHom g) M (op V) x =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op V) x := rfl

/-! ### The absolute half on the pulled-back homogeneous section -/

/-- The inverse of the composition isomorphism of pullbacks splits the pullback section along a
composite into two successive pullback sections. -/
private theorem pullbackComp_symm_hom_pullbackSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (W : Y.Opens) (V : X.Opens)
    (hg : W ≤ g ⁻¹ᵁ U) (hf : V ≤ f ⁻¹ᵁ W) (h : V ≤ (f ≫ g) ⁻¹ᵁ U) (a : M.val.obj (op U)) :
    (((Scheme.Modules.pullbackComp f g).app M).symm).hom.app V
        (Scheme.Modules.pullbackSection (f ≫ g) M U V h a) =
      Scheme.Modules.pullbackSection f ((Scheme.Modules.pullback g).obj M) W V hf
        (Scheme.Modules.pullbackSection g M U W hg a) := by
  refine (congrArg (fun z => ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op V) z)
    (Scheme.Modules.pullbackSection_comp f g M U W V hg hf h a).symm).trans ?_
  exact congrArg (fun ξ => ξ.val.app (op V) (Scheme.Modules.pullbackSection f
      ((Scheme.Modules.pullback g).obj M) W V hf (Scheme.Modules.pullbackSection g M U W hg a)))
    (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp f g) M)

/-- **The absolute half of the comparison, on a pulled-back section** whose pullback along the
chart is the global section of `𝒪(nd)` attached to `y`: it goes to the degree-`n` value at `y`
of the pullback along `φ` of the universal family of [Stacks, Tag 01N9]. -/
theorem chartAbsIso_pullbackSection_of {Y : Scheme.{u}}
    (φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).toScheme)
    (ρ : Y ⟶ (relativeProj A).scheme)
    (hρ : ρ = toProj (A.grading U) φ ≫ (relativeProj A).chart U hU) (n : ℕ)
    (y : A.grading U (n * d)) (V : (relativeProj A).scheme.Opens)
    (s : (D.algebra.piece ((n * d : ℕ) : ℤ)).val.obj (op V))
    (h : (⊤ : Y.Opens) ≤ ρ ⁻¹ᵁ V)
    (h3 : (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens) ≤
      (relativeProj A).chart U hU ⁻¹ᵁ V)
    (hs : (chartPieceIso D U hU ((n * d : ℕ) : ℤ)).hom.app ⊤
        (Scheme.Modules.pullbackSection ((relativeProj A).chart U hU)
          (D.algebra.piece ((n * d : ℕ) : ℤ)) V ⊤ h3 s) =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) (n * d) y) :
    (chartAbsIso D d U hU φ ρ hρ n).hom.app ⊤
        (Scheme.Modules.pullbackSection ρ (D.algebra.piece ((n * d : ℕ) : ℤ)) V ⊤ h s) =
      (ProjTriplePullback.pullbackSections (A.grading U)
        (universalVeroneseSections (A.grading U) d) φ).toFun n y := by
  subst hρ
  have h2 : (⊤ : Y.Opens) ≤ toProj (A.grading U) φ ⁻¹ᵁ
      (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens) := fun _ _ => trivial
  -- step 1: the congruence is the identity
  have k1 : ((Scheme.Modules.pullbackCongr (rfl : toProj (A.grading U) φ ≫
        (relativeProj A).chart U hU = _)).app (D.algebra.piece ((n * d : ℕ) : ℤ))).hom.app ⊤
      (Scheme.Modules.pullbackSection (toProj (A.grading U) φ ≫ (relativeProj A).chart U hU)
        (D.algebra.piece ((n * d : ℕ) : ℤ)) V ⊤ h s) =
      Scheme.Modules.pullbackSection (toProj (A.grading U) φ ≫ (relativeProj A).chart U hU)
        (D.algebra.piece ((n * d : ℕ) : ℤ)) V ⊤ h s :=
    Scheme.Modules.pullbackSection_congr rfl _ V ⊤ h h s
  -- step 2: split the composite
  have k2 : (((Scheme.Modules.pullbackComp (toProj (A.grading U) φ)
        ((relativeProj A).chart U hU)).app (D.algebra.piece ((n * d : ℕ) : ℤ))).symm).hom.app ⊤
      (Scheme.Modules.pullbackSection (toProj (A.grading U) φ ≫ (relativeProj A).chart U hU)
        (D.algebra.piece ((n * d : ℕ) : ℤ)) V ⊤ h s) =
      Scheme.Modules.pullbackSection (toProj (A.grading U) φ)
        ((Scheme.Modules.pullback ((relativeProj A).chart U hU)).obj
          (D.algebra.piece ((n * d : ℕ) : ℤ))) ⊤ ⊤ h2
        (Scheme.Modules.pullbackSection ((relativeProj A).chart U hU)
          (D.algebra.piece ((n * d : ℕ) : ℤ)) V ⊤ h3 s) := by
    exact pullbackComp_symm_hom_pullbackSection _ _ _ _ _ _ h3 h2 h s
  -- step 3: the chart identification
  have k3 : ((Scheme.Modules.pullback (toProj (A.grading U) φ)).mapIso
        (chartPieceIso D U hU ((n * d : ℕ) : ℤ))).hom.app ⊤
      (Scheme.Modules.pullbackSection (toProj (A.grading U) φ)
        ((Scheme.Modules.pullback ((relativeProj A).chart U hU)).obj
          (D.algebra.piece ((n * d : ℕ) : ℤ))) ⊤ ⊤ h2
        (Scheme.Modules.pullbackSection ((relativeProj A).chart U hU)
          (D.algebra.piece ((n * d : ℕ) : ℤ)) V ⊤ h3 s)) =
      Scheme.Modules.pullbackSection (toProj (A.grading U) φ)
        (twistingSheaf (A.grading U) ((n * d : ℕ) : ℤ)) ⊤ ⊤ h2
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) (n * d) y) :=
    (Scheme.Modules.pullbackSection_naturality (toProj (A.grading U) φ)
      (chartPieceIso D U hU ((n * d : ℕ) : ℤ)).hom ⊤ ⊤ h2 _).trans
      (congrArg (Scheme.Modules.pullbackSection (toProj (A.grading U) φ)
        (twistingSheaf (A.grading U) ((n * d : ℕ) : ℤ)) ⊤ ⊤ h2) hs)
  -- step 4: split `toProj φ = φ ≫ ι`
  have h4 : (⊤ : Y.Opens) ≤ φ ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Proj.degreeOpen
      (A.grading U) d).toScheme.Opens) := fun _ _ => trivial
  have h5 : (⊤ : (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).toScheme.Opens) ≤
      (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι ⁻¹ᵁ
        (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens) := fun _ _ => trivial
  have k4 : (((Scheme.Modules.pullbackComp φ
        (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι).app
          (twistingSheaf (A.grading U) ((n * d : ℕ) : ℤ))).symm).hom.app ⊤
      (Scheme.Modules.pullbackSection (toProj (A.grading U) φ)
        (twistingSheaf (A.grading U) ((n * d : ℕ) : ℤ)) ⊤ ⊤ h2
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) (n * d) y)) =
      Scheme.Modules.pullbackSection φ
        ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι).obj
          (twistingSheaf (A.grading U) ((n * d : ℕ) : ℤ))) ⊤ ⊤ h4
        (Scheme.Modules.pullbackSection (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι
          (twistingSheaf (A.grading U) ((n * d : ℕ) : ℤ)) ⊤ ⊤ h5
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) (n * d) y)) := by
    exact pullbackComp_symm_hom_pullbackSection _ _ _ _ _ _ h5 h4 h2 _
  -- step 5: the comparison of the twists with the tensor powers
  have k5 : ((Scheme.Modules.pullback φ).mapIso
        (ProjTwistTensorPowDegreeOpen.thetaNat (A.grading U) d n).symm).hom.app ⊤
      (Scheme.Modules.pullbackSection φ
        ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι).obj
          (twistingSheaf (A.grading U) ((n * d : ℕ) : ℤ))) ⊤ ⊤ h4
        (Scheme.Modules.pullbackSection (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι
          (twistingSheaf (A.grading U) ((n * d : ℕ) : ℤ)) ⊤ ⊤ h5
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) (n * d) y))) =
      Scheme.Modules.pullbackSection φ
        (natTensorPow (universalTwist (A.grading U) d) n) ⊤ ⊤ h4
        ((universalVeroneseSections (A.grading U) d).toFun n y) :=
    (Scheme.Modules.pullbackSection_naturality φ
      (ProjTwistTensorPowDegreeOpen.thetaNat (A.grading U) d n).inv ⊤ ⊤ h4 _).trans
      (congrArg (fun z => Scheme.Modules.pullbackSection φ
        (natTensorPow (universalTwist (A.grading U) d) n) ⊤ ⊤ h4
        ((ProjTwistTensorPowDegreeOpen.thetaNat (A.grading U) d n).inv.val.app (op ⊤) z))
        (ProjChartRatioPullback.pullbackSectionHom_top
          (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι _ _))
  -- the composite
  refine (congrArg (fun z => (((Scheme.Modules.pullbackComp (toProj (A.grading U) φ)
      ((relativeProj A).chart U hU)).app _).symm ≪≫
    (Scheme.Modules.pullback (toProj (A.grading U) φ)).mapIso
      (chartPieceIso D U hU ((n * d : ℕ) : ℤ)) ≪≫
    ((Scheme.Modules.pullbackComp φ
      (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι).app _).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso
      (ProjTwistTensorPowDegreeOpen.thetaNat (A.grading U) d n).symm ≪≫
    (pullbackNatTensorPowIso φ (universalTwist (A.grading U) d) n).symm).hom.app ⊤ z) k1).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullback (toProj (A.grading U) φ)).mapIso
      (chartPieceIso D U hU ((n * d : ℕ) : ℤ)) ≪≫
    ((Scheme.Modules.pullbackComp φ
      (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι).app _).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso
      (ProjTwistTensorPowDegreeOpen.thetaNat (A.grading U) d n).symm ≪≫
    (pullbackNatTensorPowIso φ (universalTwist (A.grading U) d) n).symm).hom.app ⊤ z) k2).trans ?_
  refine (congrArg (fun z => (((Scheme.Modules.pullbackComp φ
      (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι).app _).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso
      (ProjTwistTensorPowDegreeOpen.thetaNat (A.grading U) d n).symm ≪≫
    (pullbackNatTensorPowIso φ (universalTwist (A.grading U) d) n).symm).hom.app ⊤ z) k3).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullback φ).mapIso
      (ProjTwistTensorPowDegreeOpen.thetaNat (A.grading U) d n).symm ≪≫
    (pullbackNatTensorPowIso φ (universalTwist (A.grading U) d) n).symm).hom.app ⊤ z) k4).trans ?_
  exact congrArg (fun z => (pullbackNatTensorPowIso φ (universalTwist (A.grading U) d) n).inv.app
    ⊤ z) k5

/-- Three restrictions of a section compose to one, the category of opens being thin. -/
theorem restrictₛₗ_three_eq_map {X : Scheme.{u}}
    (N : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    {V₀ V₁ V₂ V₃ : (Opens X.toRingedSpace.carrier)ᵒᵖ} (e₂ : V₀ ⟶ V₁) (e₁ : V₁ ⟶ V₂)
    (e : V₂ ⟶ V₃) (ρ : V₀ ⟶ V₃) (w : N.val.obj V₀) :
    N.val.restrictₛₗ e (N.val.restrictₛₗ e₁ (N.val.restrictₛₗ e₂ w)) = N.val.map ρ w := by
  refine (PresheafOfModules.map_comp_apply N.val e₁ e _).symm.trans ?_
  refine (PresheafOfModules.map_comp_apply N.val e₂ (e₁ ≫ e) w).symm.trans ?_
  rw [show e₂ ≫ e₁ ≫ e = ρ from Subsingleton.elim _ _]

/-! ### A family of isomorphisms matching two triples -/

/-- **Two graded maps of one weight matched by a family of isomorphisms of the iterated tensor
powers have the same generation condition.** -/
theorem iSup_nonvanishingOpen_psiSection_of_family {σ : Type*} {R : Type u} [CommRing R]
    [SetLike σ R] [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {e : ℕ}
    {L L' : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]
    [Stacks.Ample.IsInvertibleModule Y L']
    {ψ : VeroneseSections 𝒜 e L} {ψ' : VeroneseSections 𝒜 e L'}
    (c : ∀ n : ℕ, natTensorPow L n ≅ natTensorPow L' n)
    (hc : ∀ (n : ℕ) (x : 𝒜 (n * e)), (c n).hom.app ⊤ (ψ.toFun n x) = ψ'.toFun n x)
    (hgen' : ⨆ f : 𝒜 e, Stacks.NonvanishingOpen.nonvanishingOpen Y L'
      (MorphismToProjUniversal.psiSection 𝒜 ψ' f) = ⊤) :
    ⨆ f : 𝒜 e, Stacks.NonvanishingOpen.nonvanishingOpen Y L
      (MorphismToProjUniversal.psiSection 𝒜 ψ f) = ⊤ := by
  refine Eq.trans (iSup_congr fun f => ?_) hgen'
  rw [MorphismToProjUniversal.nonvanishingOpen_psiSection,
    MorphismToProjUniversal.nonvanishingOpen_psiSection]
  refine Opens.ext ?_
  rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen, Stacks.NonvanishingOpen.coe_nonvanishingOpen,
    ← Stacks.Ample.nonvanishingLocus_congr (c 1)]
  exact congrArg _ (hc 1 _)

/-! ### The twisting of the glued twists on sections -/

section Relative

variable {T : Scheme.{u}} (r : T ⟶ (relativeProj A).scheme)
  (hg : ∀ t : T, r.base t ∈ (relativeProj A).degreeOpen d)
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
    (twistLine D d r)]

/-- **The twisting of the glued twists on sections**: a section `a` of `𝒜_{nd}` over an open `V`
of the base goes to the recognition comparison applied to the pullback along `r` of
`ψ_{nd}(a)`, the transpose of the homogeneous-section map read through the unit of `π^* ⊣ π_*`. -/
theorem twistTwisting_sectionHom (n : ℤ) (V : (Opens S.toRingedSpace.carrier)ᵒᵖ)
    (a : ((situationAlgebra A).piece (n * d)).val.obj V) :
    (twistTwisting D d r hg rfl).sectionHom n V a =
      ((twistRecognition D d r hg).hom.app n).val.app _
        (pullbackUnit (ringedSpaceHom r) (D.algebra.piece (n * d))
          ((opensMap (ringedSpaceHom (relativeProj A).toBase)).op.obj V)
          ((D.psiTranspose (n * d)).val.app _
            (pullbackUnit (ringedSpaceHom (relativeProj A).toBase) (A.piece (n * d)) V a))) := by
  refine congrArg (fun z => ((twistRecognition D d r hg).hom.app n).val.app _ z) ?_
  refine (congrArg (fun φ => φ.val.app _ (pullbackUnit (ringedSpaceHom (r ≫
      (relativeProj A).toBase)) (A.piece (n * d)) V a)) (D.psiLeg_rfl_eq r (n * (d : ℤ)))).trans ?_
  refine (congrArg (fun z =>
      ((pullbackFunctor (ringedSpaceHom r)).map (D.psiTranspose (n * (d : ℤ)))).val.app _ z)
    (Stacks.PullbackCompMonoidal.comparison_pullbackUnit
      (ringedSpaceHom (relativeProj A).toBase) (ringedSpaceHom r) _ V a)).trans ?_
  exact pullbackUnit_naturality (ringedSpaceHom r) (D.psiTranspose (n * (d : ℤ)))
    ((opensMap (ringedSpaceHom (relativeProj A).toBase)).op.obj V)
    (pullbackUnit (ringedSpaceHom (relativeProj A).toBase) (A.piece (n * d)) V a)

/-! ### The chart-wise Veronese family of the twisting -/

/-- The factorization of `r ≫ π` restricted to the preimage of `U` through `U`. -/
abbrev chartBase : ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  (r ≫ (relativeProj A).toBase) ∣_ U

theorem chartBase_ι : chartBase U r ≫ U.ι =
    ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ r ≫ (relativeProj A).toBase :=
  morphismRestrict_ι _ U

/-- The twisting pulled back to the preimage of `U`, read over the factorization through `U`. -/
def chartTwistingOf :
    Twisting (chartBase U r ≫ U.ι) (situationAlgebra A) (d : ℤ)
      ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r)) :=
  Twisting.congrBase (chartBase_ι U r).symm
    ((twistTwisting D d r hg rfl).pullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)

/-- **The chart-wise Veronese family of the twisting, computed.** -/
theorem veroneseSections_chartTwistingOf (n : ℕ)
    (x : (A.restrict U.ι).grading (⊤ : U.toScheme.Opens) (n * d))
    (yU : A.sectionPieces U (n * d))
    (hx : (x : (A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)) (n * d) =
      A.resPiece (U.ι_image_top).le (n * d) yU)
    (hW : (⊤ : Opens ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme.carrier) ≤
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ⁻¹ᵁ ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U)) :
    letI : Stacks.Ample.IsInvertibleModule ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme
        ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
          (twistLine D d r)) :=
      Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
    (veroneseSections (chartTwisting A U (chartBase U r) (chartTwistingOf D d U r hg))).toFun n x =
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare
          ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
            (twistLine D d r)) n).inv.app ⊤
        ((laurentPullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι (twistLine D d r)
            (n : ℤ)).val.app (op ⊤)
          (Scheme.Modules.pullbackSection ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι
            ((laurent (twistLine D d r)).piece (n : ℤ)) ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U)
            ⊤ hW
            (((twistRecognition D d r hg).hom.app (n : ℤ)).val.app _
              (pullbackUnit (ringedSpaceHom r) (D.algebra.piece ((n : ℤ) * d))
                (op ((relativeProj A).toBase ⁻¹ᵁ U))
                ((D.psiTranspose ((n : ℤ) * d)).val.app _
                  (pullbackUnit (ringedSpaceHom (relativeProj A).toBase) (A.piece ((n : ℤ) * d))
                    (op U) yU)))))) := by
  let : Stacks.Ample.IsInvertibleModule ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme
      ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r)) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  refine (veroneseSections_chartTwisting' A U (chartBase U r) (chartTwistingOf D d U r hg) n x
    (homOfLE (top_le_preimage_image_top U (chartBase U r))).op).trans ?_
  refine congrArg (fun z => (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare
      ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r)) n).inv.app ⊤ z) ?_
  have h1 := Twisting.sectionHom_heq (chartBase_ι U r).symm
    ((twistTwisting D d r hg rfl).pullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)
    (chartTwistingOf D d U r hg) (Twisting.heq_congrBase _ _).symm (n : ℤ)
    (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)))
    ((x : (A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)) (n * d))
    (eqToHom (congrArg (fun g => (opensMap (ringedSpaceHom g)).op.obj
      (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)))) (chartBase_ι U r).symm))
  refine (congrArg (fun z => ((laurent ((pullbackFunctor (ringedSpaceHom
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r))).piece (n : ℤ)).val.restrictₛₗ
      (homOfLE (top_le_preimage_image_top U (chartBase U r))).op z) h1).trans ?_
  have h2 := sectionHom_resPiece A
    ((twistTwisting D d r hg rfl).pullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι) n
    (U.ι_image_top).le yU
  have h3 := Twisting.sectionHom_pullback (twistTwisting D d r hg rfl)
    ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι (n : ℤ) (op U) yU
  have h4 := twistTwisting_sectionHom D d r hg (n : ℤ) (op U) yU
  refine (congrArg (fun z => ((laurent ((pullbackFunctor (ringedSpaceHom
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r))).piece (n : ℤ)).val.restrictₛₗ
      (homOfLE (top_le_preimage_image_top U (chartBase U r))).op
      (((laurent ((pullbackFunctor (ringedSpaceHom
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r))).piece (n : ℤ)).val.restrictₛₗ
      (eqToHom (congrArg (fun g => (opensMap (ringedSpaceHom g)).op.obj
        (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)))) (chartBase_ι U r).symm))
      (((twistTwisting D d r hg rfl).pullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι).sectionHom
        (n : ℤ) (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))) z))) hx).trans ?_
  refine (congrArg (fun z => ((laurent ((pullbackFunctor (ringedSpaceHom
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r))).piece (n : ℤ)).val.restrictₛₗ
      (homOfLE (top_le_preimage_image_top U (chartBase U r))).op
      (((laurent ((pullbackFunctor (ringedSpaceHom
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r))).piece (n : ℤ)).val.restrictₛₗ
      (eqToHom (congrArg (fun g => (opensMap (ringedSpaceHom g)).op.obj
        (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)))) (chartBase_ι U r).symm)) z))
    (h2.trans (congrArg _ (h3.trans (congrArg _ (congrArg _ h4)))))).trans ?_
  refine (restrictₛₗ_three_eq_map _ _ _ _ (homOfLE hW).op _).trans ?_
  exact (PresheafOfModules.naturality_apply (laurentPullback
    ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι (twistLine D d r) (n : ℤ)).val (homOfLE hW).op _).symm

/-! ### The relative half of the comparison -/

/-- The degree-`n` component of the recognition comparison, as an isomorphism. -/
def twistRecognitionPiece (n : ℤ) :
    (pullbackTwistVeronese D (d : ℤ) r).piece n ≅ (laurent (twistLine D d r)).piece n :=
  GradedLaurentRecognition.pieceIso _ _ (Iso.refl _)
    (isIso_mulSheaf_pullbackTwistVeronese_of_mem_degreeOpen D d r hg)
    (isInvertible_pullbackTwistVeronese_piece_zero D r (d : ℤ)) n

theorem twistRecognitionPiece_hom (n : ℤ) :
    (twistRecognitionPiece D d r hg n).hom = (twistRecognition D d r hg).hom.app n := rfl

/-- **The relative half of the comparison**: on the preimage `W` of `U`,
`(j^*r^*𝒪(d))^{⊗ n} ≅ (j ≫ r)^*𝒪(nd)`, `j` the inclusion of `W`. -/
def chartRelIso (n : ℕ) :
    letI : Stacks.Ample.IsInvertibleModule ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme
        ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
          (twistLine D d r)) :=
      Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
    natTensorPow (C := ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme.Modules)
      ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r)) n ≅
      (Scheme.Modules.pullback (((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ r)).obj
        (D.algebra.piece ((n : ℤ) * d)) :=
  let : Stacks.Ample.IsInvertibleModule ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme
      ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r)) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  Stacks.AlgebraicGeometry.CoherentMulSections.powCompare _ n ≪≫
    (asIso (laurentPullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι (twistLine D d r)
      (n : ℤ))).symm ≪≫
    (Scheme.Modules.pullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι).mapIso
      (twistRecognitionPiece D d r hg (n : ℤ)).symm ≪≫
    (Scheme.Modules.pullbackComp ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι r).app _

/-- **The relative half of the comparison on the chart-wise Veronese family**: it undoes the
recognition comparison and the pullback along the inclusion of `W`, leaving the pullback along
`j ≫ r` of a section of `𝒪(nd)`. -/
theorem chartRelIso_hom_app (n : ℕ) (s : (D.algebra.piece ((n : ℤ) * d)).val.obj
      (op ((relativeProj A).toBase ⁻¹ᵁ U)))
    (hW : (⊤ : Opens ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme.carrier) ≤
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ⁻¹ᵁ ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U))
    (h : (⊤ : Opens ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme.carrier) ≤
      (((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ r) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)) :
    letI : Stacks.Ample.IsInvertibleModule ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme
        ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
          (twistLine D d r)) :=
      Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
    (chartRelIso D d U r hg n).hom.app ⊤
      ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare
          ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
            (twistLine D d r)) n).inv.app ⊤
        ((laurentPullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι (twistLine D d r)
            (n : ℤ)).val.app (op ⊤)
          (Scheme.Modules.pullbackSection ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι
            ((laurent (twistLine D d r)).piece (n : ℤ)) ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U)
            ⊤ hW
            (((twistRecognition D d r hg).hom.app (n : ℤ)).val.app _
              (pullbackUnit (ringedSpaceHom r) (D.algebra.piece ((n : ℤ) * d))
                (op ((relativeProj A).toBase ⁻¹ᵁ U)) s))))) =
      Scheme.Modules.pullbackSection (((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ r)
        (D.algebra.piece ((n : ℤ) * d)) ((relativeProj A).toBase ⁻¹ᵁ U) ⊤ h s := by
  let : Stacks.Ample.IsInvertibleModule ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme
      ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r)) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  have hle : r ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) ≤ r ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) :=
    le_rfl
  -- the unit image is the pullback of the section over the whole preimage
  have hu : pullbackUnit (ringedSpaceHom r) (D.algebra.piece ((n : ℤ) * d))
      (op ((relativeProj A).toBase ⁻¹ᵁ U)) s =
      Scheme.Modules.pullbackSection r (D.algebra.piece ((n : ℤ) * d))
        ((relativeProj A).toBase ⁻¹ᵁ U) (r ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)) hle s := by
    unfold Scheme.Modules.pullbackSection
    rw [show (homOfLE hle).op = 𝟙 _ from Subsingleton.elim _ _]
    simp
    rfl
  have ka := Stacks.AlgebraicGeometry.CoherentMulSections.powCompare_hom_app_inv_app
    ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
      (twistLine D d r)) n
    ((laurentPullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι (twistLine D d r)
            (n : ℤ)).val.app (op ⊤)
          (Scheme.Modules.pullbackSection ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι
            ((laurent (twistLine D d r)).piece (n : ℤ)) ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U)
            ⊤ hW
            (((twistRecognition D d r hg).hom.app (n : ℤ)).val.app _
              (pullbackUnit (ringedSpaceHom r) (D.algebra.piece ((n : ℤ) * d))
                (op ((relativeProj A).toBase ⁻¹ᵁ U)) s))))
  refine (congrArg (fun z => ((asIso (laurentPullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι
      (twistLine D d r) (n : ℤ))).symm ≪≫
    (Scheme.Modules.pullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι).mapIso
      (twistRecognitionPiece D d r hg (n : ℤ)).symm ≪≫
    (Scheme.Modules.pullbackComp ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι r).app _).hom.val.app
      (op ⊤) z) ka).trans ?_
  have kb := congrArg (fun φ => φ.val.app (op ⊤)
      (Scheme.Modules.pullbackSection ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι
            ((laurent (twistLine D d r)).piece (n : ℤ)) ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U)
            ⊤ hW
            (((twistRecognition D d r hg).hom.app (n : ℤ)).val.app _
              (pullbackUnit (ringedSpaceHom r) (D.algebra.piece ((n : ℤ) * d))
                (op ((relativeProj A).toBase ⁻¹ᵁ U)) s))))
    (IsIso.hom_inv_id (laurentPullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι
      (twistLine D d r) (n : ℤ)))
  refine (congrArg (fun z => ((Scheme.Modules.pullback
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι).mapIso
      (twistRecognitionPiece D d r hg (n : ℤ)).symm ≪≫
    (Scheme.Modules.pullbackComp ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι r).app _).hom.val.app
      (op ⊤) z) kb).trans ?_
  have kc := (Scheme.Modules.pullbackSection_naturality ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι
    (twistRecognitionPiece D d r hg (n : ℤ)).inv _ ⊤ hW _).trans
      (congrArg (Scheme.Modules.pullbackSection ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι _ _ ⊤ hW)
        (congrArg (fun φ => φ.val.app _ (pullbackUnit (ringedSpaceHom r)
          (D.algebra.piece ((n : ℤ) * d)) (op ((relativeProj A).toBase ⁻¹ᵁ U)) s))
          (twistRecognitionPiece D d r hg (n : ℤ)).hom_inv_id))
  refine (congrArg (fun z => ((Scheme.Modules.pullbackComp
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι r).app _).hom.val.app (op ⊤) z) kc).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullbackComp
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι r).app _).hom.val.app (op ⊤)
      (Scheme.Modules.pullbackSection ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι _ _ ⊤ hW z))
    hu).trans ?_
  exact Scheme.Modules.pullbackSection_comp _ r _ _ _ ⊤ hle hW h s

/-! ### The morphism of the chart-wise class, and the comparison family -/

/-- The morphism `W ⟶ Proj Γ(U, 𝒜)` through which `j ≫ r` factors, `j` the inclusion of the
preimage `W` of `U`. -/
def chartLiftProj : ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme ⟶
    AlgebraicGeometry.Proj (A.grading U) :=
  let := D.chartData.chart_isOpenImmersion U hU
  IsOpenImmersion.lift ((relativeProj A).chart U hU)
    (((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ r) (by
      rintro _ ⟨x, rfl⟩
      have hx : r.base (((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι.base x) ∈
          (relativeProj A).toBase ⁻¹ᵁ U := x.2
      rw [← D.chartData.chart_range U hU] at hx
      obtain ⟨z, -, hz⟩ := hx
      exact ⟨z, hz⟩)

theorem chartLiftProj_fac : chartLiftProj D U hU r ≫ (relativeProj A).chart U hU =
    ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ r := by
  let := D.chartData.chart_isOpenImmersion U hU
  exact IsOpenImmersion.lift_fac _ _ _

/-- **The morphism of the chart-wise class**: `W ⟶ U_d ⊆ Proj Γ(U, 𝒜)`, the factorization of
`j ≫ r` through the absolute degree-`d` open. -/
def chartLift (hg : ∀ t : T, r.base t ∈ (relativeProj A).degreeOpen d) :
    ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme ⟶
    (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).toScheme :=
  IsOpenImmersion.lift (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι
    (chartLiftProj D U hU r) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hmem : ((chartLiftProj D U hU r).base x) ∈
          (relativeProj A).chart U hU ⁻¹ᵁ (relativeProj A).degreeOpen d := by
        change ((chartLiftProj D U hU r) ≫ (relativeProj A).chart U hU).base x ∈
          (relativeProj A).degreeOpen d
        rw [chartLiftProj_fac]
        exact hg _
      rw [(relativeProj A).chart_preimage_degreeOpen U hU d] at hmem
      exact hmem)

omit [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
  (twistLine D d r)] in
theorem chartLift_fac : toProj (A.grading U) (chartLift D d U hU r hg) ≫
    (relativeProj A).chart U hU = ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ r := by
  rw [← chartLiftProj_fac D U hU r]
  exact congrArg (· ≫ (relativeProj A).chart U hU) (IsOpenImmersion.lift_fac _ _ _)

/-- **The comparison family**: `(j^*r^*𝒪(d))^{⊗ n} ≅ (φ^*𝒪_{U_d}(d))^{⊗ n}`, `φ = chartLift`. -/
def chartFamily (n : ℕ) :
    letI : Stacks.Ample.IsInvertibleModule ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme
        ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
          (twistLine D d r)) :=
      Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
    natTensorPow (C := ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme.Modules)
      ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
        (twistLine D d r)) n ≅
      natTensorPow ((Scheme.Modules.pullback (chartLift D d U hU r hg)).obj
        (universalTwist (A.grading U) d)) n :=
  chartRelIso D d U r hg n ≪≫
    chartAbsIso D d U hU (chartLift D d U hU r hg) _ (chartLift_fac D d U hU r hg).symm n

/-- Two heterogeneously equal homogeneous elements over two equal opens have components related
by the restriction. -/
theorem component_eq_resPiece_of_heq {V₁ V₂ : S.Opens} (h : V₁ = V₂) {k : ℕ}
    (x : A.grading V₁ k) (y : A.grading V₂ k) (hxy : HEq x y) :
    (x : A.sectionRing V₁) k = A.resPiece h.le k ((y : A.sectionRing V₂) k) := by
  subst h
  obtain rfl := eq_of_heq hxy
  rw [SheafGradedAlgebra.resPiece_apply,
    show (homOfLE (le_refl V₁)).op = 𝟙 (op V₁) from Subsingleton.elim _ _]
  simp

omit D in
/-- An element of the grading at an open equal to the image of `⊤` is heterogeneously equal to an
element of the grading of the global sections of the restriction. -/
theorem exists_restrict_grading_heq (U' : S.Opens)
    (h : U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier) = U') {m : ℕ}
    (y : A.grading U' m) :
    ∃ x : (A.restrict U.ι).grading (⊤ : U.toScheme.Opens) m, HEq x y := by
  subst h
  exact ⟨y, HEq.rfl⟩

/-- The pulled-back degree-one piece is invertible, in the spelling of the ample theory. -/
abbrev chartLineInv : Stacks.Ample.IsInvertibleModule
    ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme
    ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
      (twistLine D d r)) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance

attribute [local instance] chartLineInv

/-- **The comparison family carries the chart-wise Veronese family of the twisting to the
pullback of the universal family of [Stacks, Tag 01N9]**, degreewise. -/
theorem chartFamily_toFun
    (ψ : VeroneseSections (A.grading U) d
        ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
          (twistLine D d r)))
    (hψ : HEq (veroneseSections (chartTwisting A U (chartBase U r) (chartTwistingOf D d U r hg)))
      ψ)
    (n : ℕ) (y : A.grading U (n * d)) :
    (chartFamily D d U hU r hg n).hom.app ⊤ (ψ.toFun n y) =
      (ProjTriplePullback.pullbackSections (A.grading U)
        (universalVeroneseSections (A.grading U) d) (chartLift D d U hU r hg)).toFun n y := by
  obtain ⟨x, hx⟩ := exists_restrict_grading_heq U U U.ι_image_top y
  have e1 : ψ.toFun n y = (veroneseSections (chartTwisting A U (chartBase U r)
      (chartTwistingOf D d U r hg))).toFun n x :=
    (veroneseSections_restrict_toFun_heq A U _ U.ι_image_top _ ψ hψ n x y hx).symm
  have hxU := component_eq_resPiece_of_heq U.ι_image_top x y hx
  have hW : (⊤ : Opens ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme.carrier) ≤
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ⁻¹ᵁ ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U) :=
    fun z _ => z.2
  have h : (⊤ : Opens ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme.carrier) ≤
      (((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ r) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) :=
    fun z _ => z.2
  have h3 : (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens) ≤
      (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) := by
    let := D.chartData.chart_isOpenImmersion U hU
    intro z _
    have hz : (relativeProj A).chart U hU z ∈ (relativeProj A).chart U hU ''ᵁ ⊤ :=
      ⟨z, trivial, rfl⟩
    rw [D.chartData.chart_range U hU] at hz
    exact hz
  have hs := chartPieceIso_pullbackSection D U hU (n * d) ((y : A.sectionRing U) (n * d)) h3
  rw [show (⟨DirectSum.of (A.sectionPieces U) (n * d) ((y : A.sectionRing U) (n * d)),
      A.of_mem_grading U _⟩ : A.grading U (n * d)) = y from
    Subtype.ext (SheafGradedAlgebra.of_component A U y)] at hs
  refine (congrArg (fun z => (chartFamily D d U hU r hg n).hom.app ⊤ z) e1).trans ?_
  refine (congrArg (fun z => (chartFamily D d U hU r hg n).hom.app ⊤ z)
    (veroneseSections_chartTwistingOf D d U r hg n x ((y : A.sectionRing U) (n * d)) hxU
      hW)).trans ?_
  refine (congrArg (fun z => (chartAbsIso D d U hU (chartLift D d U hU r hg) _
      (chartLift_fac D d U hU r hg).symm n).hom.app ⊤ z)
    (chartRelIso_hom_app D d U r hg n _ hW h)).trans ?_
  exact chartAbsIso_pullbackSection_of D d U hU _ _ _ n y _ _ h h3 hs

omit [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
  (twistLine D d r)] in
/-- The generation condition of the pulled-back universal family. -/
theorem iSup_nonvanishingOpen_chartUniversal :
    ⨆ f : A.grading U d, Stacks.NonvanishingOpen.nonvanishingOpen _
      ((Scheme.Modules.pullback (chartLift D d U hU r hg)).obj (universalTwist (A.grading U) d))
      (MorphismToProjUniversal.psiSection (A.grading U)
        (ProjTriplePullback.pullbackSections (A.grading U)
          (universalVeroneseSections (A.grading U) d) (chartLift D d U hU r hg)) f) = ⊤ :=
  ProjTriplePullback.iSup_nonvanishingOpen_pullbackSections _ _ _
    (ProjDegreeOpenUniversalTriple.iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top
      _ d)

include hU in
/-- **The generation condition of the chart-wise Veronese family of the twisting.** -/
theorem iSup_nonvanishingOpen_chartTwistingOf
    (ψ : VeroneseSections (A.grading U) d
        ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
          (twistLine D d r)))
    (hψ : HEq (veroneseSections (chartTwisting A U (chartBase U r) (chartTwistingOf D d U r hg)))
      ψ) :
    ⨆ f : A.grading U d, Stacks.NonvanishingOpen.nonvanishingOpen _ _
      (MorphismToProjUniversal.psiSection (A.grading U) ψ f) = ⊤ :=
  iSup_nonvanishingOpen_psiSection_of_family (A.grading U) (chartFamily D d U hU r hg)
    (chartFamily_toFun D d U hU r hg ψ hψ) (iSup_nonvanishingOpen_chartUniversal D d U hU r hg)

/-- **The morphism classified by the chart-wise Veronese family of the twisting is `chartLift`**:
the factorization of `j ≫ r` through the absolute degree-`d` open. -/
theorem classifyingHom_chartTwistingOf (hd : 0 < d)
    (ψ : VeroneseSections (A.grading U) d
        ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
          (twistLine D d r)))
    (hψ : HEq (veroneseSections (chartTwisting A U (chartBase U r) (chartTwistingOf D d U r hg)))
      ψ) :
    ProjTripleClassifying.classifyingHom (A.grading U) hd ψ
        (iSup_nonvanishingOpen_chartTwistingOf D d U hU r hg ψ hψ) =
      chartLift D d U hU r hg := by
  refine (ProjTripleClassifying.classifyingHom_eq_of_family (A.grading U) hd _
    (iSup_nonvanishingOpen_chartUniversal D d U hU r hg) (chartFamily D d U hU r hg)
    (chartFamily_toFun D d U hU r hg ψ hψ)).trans ?_
  refine (ProjClassifyingPullback.classifyingHom_pullbackSections (A.grading U) hd _
    (ProjDegreeOpenUniversalTriple.iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top
      _ d) _).trans ?_
  rw [ProjClassifyingPullback.classifyingHom_universalVeroneseSections]
  exact Category.comp_id _

end Relative

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
