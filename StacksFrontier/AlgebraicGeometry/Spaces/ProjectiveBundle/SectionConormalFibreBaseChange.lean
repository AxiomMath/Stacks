module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalChartNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalSchemeBaseChange

/-!
# Base change of the identification of the section of `𝐏(ℰ)` at a point with the fibre section

Let `σ` be a section of `π : 𝐏(ℰ) ⟶ X`, `x : T ⟶ X` a scheme point and `h : T' ⟶ T` a morphism
of test objects.  At `x` the section `s_x` of `𝐏((x^*ℰ)_Zar) ⟶ T` is the section `k_x` of the
fibre `T ×_X 𝐏(ℰ)` of Stacks 084B followed by the identification of the fibre with
`𝐏((x^*ℰ)_Zar)`, and the conormal sheaves of `s_x` and `k_x` are identified accordingly
(`AlgebraicGeometry.Space.sectionPointConormalFibreIso`).  This file proves that the comparison of
fibres of Stacks 084B (3) is the base-change morphism of projective bundles under these
identifications, and deduces that the identifications of conormal sheaves at `x` and at `x ∘ h`
are intertwined by the base-change maps of conormal sheaves.

## Main results

* `AlgebraicGeometry.Space.fibreComparison_eq_projComparison`: the comparison of fibres is the
  comparison morphism of Stacks 084B (3).
* `AlgebraicGeometry.Space.toScheme_map_fibreComparison_comp_pointFibreProjectiveBundleIso`: the
  comparison of fibres is the base change of projective bundles.
* `AlgebraicGeometry.Space.sectionPointConormalFibreIso_baseChange`: the base change of the
  identification of conormal sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
  {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T)

/-- **The comparison of fibres is the comparison morphism of Stacks 084B (3)**: both lie over
`h` and over the morphism of the fibres to `𝐏(ℰ)`. -/
theorem fibreComparison_eq_projComparison :
    (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h =
      (projectiveBundleSituation X E hE hb).quadrupleRestriction.projComparison
        (projectiveBundleSituation X E hE hb).shrink.contains_relativeProj_pointAlgebra x h := by
  have hP := (projectiveBundleSituation X E hE hb).isPullback_projComparison x h
  apply Yoneda.fullyFaithful.map_injective
  refine ((projectiveBundleSituation X E hE hb).relativeProjPoints.isPullback T x).hom_ext ?_ ?_
  · exact (RelativeProjPoints.map_fibreComparison_comp_fibreToSpace _ T x h).trans hP.2.1.symm
  · exact ((yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map
      (RelativeProjPoints.fibreComparison_comp_fibreHom _ T x h)).trans
        ((congrArg yoneda.map hP.1.w).symm))).trans (yoneda.map_comp _ _)

/-- **The comparison of fibres is the base-change morphism of projective bundles**, through the
identifications `pointFibreProjectiveBundleIso` of the fibres with `𝐏((x^*ℰ)_Zar)` and
`𝐏(((x ∘ h)^*ℰ)_Zar)`. -/
theorem toScheme_map_fibreComparison_comp_pointFibreProjectiveBundleIso :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    haveI := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ x)
    (pointFibreProjectiveBundleIso X E hE hb T' (yoneda.map h ≫ x)).hom ≫
        Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map h)
          (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
          (pointZariskiModuleBaseChangeIso X E hE x h) =
      (BigFppfOver.toScheme B S hS).map
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h) ≫
        (pointFibreProjectiveBundleIso X E hE hb T x).hom := by
  have := isQuasicoherent_pointZariskiModule X E hE T x
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ x)
  have h1 := situationProjectiveBundleIso_hom_comp_projectiveBundleBaseChange
    ((BigFppfOver.toScheme B S hS).map h) (pointZariskiModule X E T x)
    (pointZariskiModule X E T' (yoneda.map h ≫ x)) (pointZariskiModuleBaseChangeIso X E hE x h)
  have h2 := toScheme_map_projComparison_comp_pointProjIso X E hE hb x h
  rw [fibreComparison_eq_projComparison]
  simp only [pointFibreProjectiveBundleIso, Iso.trans_hom, Category.assoc, pointProjIso] at h2 ⊢
  rw [h1]
  simp only [← Category.assoc]
  refine congrArg (· ≫ _) ?_
  simp only [Category.assoc]
  exact (Category.id_comp _).trans (h2.symm.trans (congrArg (_ ≫ ·) (Category.id_comp _).symm))

/-- The base-change maps of conormal sheaves of two stacked squares agree, read through
identifications `𝒞_τ ≅ 𝒞_σ` given by the base-change maps of squares with an identity edge
(`Stacks.Conormal.conormalBaseChangeMap_comp_unit_square` with the identifications named). -/
theorem _root_.Stacks.Conormal.conormalUnitSquareIso_baseChange {X X' P P' Q Q' : Scheme.{u}}
    (g : X' ⟶ X) {σ : X ⟶ P} {σ' : X' ⟶ P'} {τ : X ⟶ Q} {τ' : X' ⟶ Q'}
    [AlgebraicGeometry.IsImmersion σ] [AlgebraicGeometry.IsImmersion σ']
    [AlgebraicGeometry.IsImmersion τ] [AlgebraicGeometry.IsImmersion τ']
    {a : P ⟶ Q} {a' : P' ⟶ Q'} [IsIso a] [IsIso a'] {kp : P' ⟶ P} {kb : Q' ⟶ Q}
    (S : σ ≫ a = 𝟙 X ≫ τ) (S' : σ' ≫ a' = 𝟙 X' ≫ τ') (cb : τ' ≫ kb = g ≫ τ)
    (c : σ' ≫ kp = g ≫ σ) (hk : a' ≫ kb = kp ≫ a) :
    Stacks.Conormal.conormalBaseChangeMap cb ≫ (Stacks.Conormal.conormalUnitSquareIso S').hom =
      (Scheme.Modules.pullback g).map (Stacks.Conormal.conormalUnitSquareIso S).hom ≫
        Stacks.Conormal.conormalBaseChangeMap c :=
  (Stacks.Conormal.conormalBaseChangeMap_comp_unit_square g S S' cb c hk).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) ((Scheme.Modules.pullback g).map_comp _ _).symm))

variable (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb)
  (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)

/-- The section of the fibre is compatible with the comparison of fibres, on schemes. -/
theorem toScheme_map_sectionFibreLift_comp_fibreComparison :
    (BigFppfOver.toScheme B S hS).map (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)) ≫
        (BigFppfOver.toScheme B S hS).map
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h) =
      (BigFppfOver.toScheme B S hS).map h ≫
        (BigFppfOver.toScheme B S hS).map (sectionFibreLift X E hE hb σ hσ T x) :=
  ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
    ((congrArg (BigFppfOver.toScheme B S hS).map
      (sectionFibreLift_comp_fibreComparison X E hE hb σ hσ h x)).trans
      ((BigFppfOver.toScheme B S hS).map_comp _ _))

/-- **The identifications of the conormal sheaves of `s_x` and `k_x` are compatible with base
change**: along `h`, the base-change maps of conormal sheaves of the squares of sections
`s_{x ∘ h}, s_x` and `k_{x ∘ h}, k_x` intertwine `sectionPointConormalFibreIso` at `x` and at
`x ∘ h`. -/
theorem sectionPointConormalFibreIso_baseChange :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    haveI := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ x)
    haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
      (sectionPointBundleSection X E hE hb σ hσ T x).1
      (sectionPointBundleSection X E hE hb σ hσ T x).2
    haveI := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
      (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).1
      (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).2
    haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
    haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)
    Stacks.Conormal.conormalBaseChangeMap
        (sectionPointBundleSection_baseChange X E hE hb σ hσ x h) ≫
        (sectionPointConormalFibreIso X E hE hb σ hσ T' (yoneda.map h ≫ x)).hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          (sectionPointConormalFibreIso X E hE hb σ hσ T x).hom ≫
        Stacks.Conormal.conormalBaseChangeMap
          (toScheme_map_sectionFibreLift_comp_fibreComparison X E hE hb x h σ hσ) := by
  have := isQuasicoherent_pointZariskiModule X E hE T x
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ x)
  have := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
    (sectionPointBundleSection X E hE hb σ hσ T x).1
    (sectionPointBundleSection X E hE hb σ hσ T x).2
  have := Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase _ _
    (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).1
    (sectionPointBundleSection X E hE hb σ hσ T' (yoneda.map h ≫ x)).2
  have := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T x
  have := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)
  unfold sectionPointConormalFibreIso
  refine Stacks.Conormal.conormalUnitSquareIso_baseChange _ _ _ _ _ ?_
  exact toScheme_map_fibreComparison_comp_pointFibreProjectiveBundleIso X E hE hb x h

end AlgebraicGeometry.Space

end
