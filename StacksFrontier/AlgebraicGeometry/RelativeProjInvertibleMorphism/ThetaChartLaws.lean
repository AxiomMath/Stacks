module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaTarget
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTriple

/-!
# The local datum of the relative `θ` of Stacks Tag 01O9 is multiplicative and reads `ψ`

Over the chart of an affine open `V` of the base, the local datum `…GradedPowerMap.thetaLoc` of the
relative `θ` is, through `…GradedPowerMap.lam`, [Stacks, Tag 01NK]'s `θ` for the induced datum
composed with [Stacks, Tag 01NR]'s chart identification. Both of those are multiplicative and both
read `ψ` on homogeneous sections over `V`; this file transports the two properties to the local
datum.

## Main results

* `…GradedPowerMap.lam_bijective`, `lam_chartTargetHom_app`, `lam_localMul`: the section-level
  inverse of the target comparison is bijective and multiplicative.
* `…GradedPowerMap.thetaLoc_mul`: **the local datum is multiplicative**, on every open of the
  chart.
* `…GradedPowerMap.thetaLoc_psiU`: **the local datum carries `ψ(a)` to `ψ(a)`** for every
  homogeneous section `a` of `𝒜` over `V`: the first `ψ` is [Stacks, Tag 01NR]'s
  homogeneous-section map, the second the datum of [Stacks, Tag 01O8].

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

section Absolute

variable {σ R : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- The canonical product of local sections of the absolute twists is the product of
`⨁_{n ∈ ℤ} 𝒪(n)`. -/
theorem absoluteTwistProduct_eq_mul (i j : ℤ) (W : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒜 i).val.obj (op W))
    (b : (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒜 j).val.obj (op W)) :
    Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct 𝒜 i j W a b =
      ((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).mul i j).app (op W) a b :=
  Subtype.ext (funext fun x =>
    Stacks.AlgebraicGeometry.TwistRigidity.absoluteTwistProduct_apply 𝒜 i j W a b x)

variable {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections 𝒜 L)

/-- The product of the target of [Stacks, Tag 01NK]'s `θ` in pushforward form, over any open, is
the product of local sections of the tensor powers. -/
theorem pushforward_laurentRestrict_mul (i j : ℤ) (W : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : Γ(ψ.pushLaurent i, W)) (b : Γ(ψ.pushLaurent j, W)) :
    ((Stacks.RingedSpace.pushforwardAlgebra ψ.glued.toLRSHom.toShHom
        (Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.laurentRestrict 𝒜 ψ)).mul i j).app
        (op W) a b = Stacks.TensorPowerDivision.localMul L a b := rfl

end Absolute

namespace GradedPowerMap

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- `ℒ` restricted to `f^{-1}(V)`. -/
abbrev Lres (V : S.Opens) : (f ⁻¹ᵁ V).toScheme.Modules :=
  (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L

/-- **The section-level comparison** of the target of the relative `θ` over a chart open with
the target of [Stacks, Tag 01NK]'s `θ` for the induced datum: `pullPow` followed by the
identification of the two opens. -/
def lam (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (t : Γ(tensorPowerModule T P.L n, P.targetOpen V hV W₁)) :
    Γ(tensorPowerModule (f ⁻¹ᵁ V).toScheme (P.Lres V) n, P.sourceOpen V W₁) :=
  (tensorPowerModule (f ⁻¹ᵁ V).toScheme (P.Lres V) n).presheaf.map
    (homOfLE (P.sourceOpen_le V hV W₁)).op (P.pullPow V n _ t)

/-- The section-level comparison `lam` is injective. -/
theorem lam_injective (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) :
    Function.Injective (P.lam V hV n W₁) := by
  intro a b hab
  apply P.pullPow_injective V n (P.targetOpen_le V hV W₁)
  have := congrArg ((tensorPowerModule (f ⁻¹ᵁ V).toScheme (P.Lres V) n).presheaf.map
    (eqToHom (P.sourceOpen_eq V hV W₁).symm).op) hab
  unfold lam at this
  rwa [map_map _ _ _ (𝟙 _), map_map _ _ _ (𝟙 _), map_id_apply, map_id_apply] at this

/-- The target comparison `chartTargetHom` is a left inverse of `lam`. -/
theorem lam_chartTargetHom (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (t : Γ(tensorPowerModule T P.L n, P.targetOpen V hV W₁)) :
    (P.chartTargetHom V hV n).app W₁ (P.lam V hV n W₁ t) = t :=
  P.chartTargetHom_app_pullPow V hV n W₁ t

/-- The section-level comparison `lam` is bijective. -/
theorem lam_bijective (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) :
    Function.Bijective (P.lam V hV n W₁) :=
  (map_bijective_of_eq _ _ (P.sourceOpen_eq V hV W₁).symm).comp
    (P.pullPow_bijective V n (P.targetOpen_le V hV W₁))

/-- **`lam` inverts the target comparison.** -/
theorem lam_chartTargetHom_app (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (z : Γ((P.affineDatum V).pushLaurent n, W₁)) :
    P.lam V hV n W₁ ((P.chartTargetHom V hV n).app W₁ z) = z := by
  obtain ⟨t, rfl⟩ := (P.lam_bijective V hV n W₁).2 z
  exact congrArg (P.lam V hV n W₁) (P.lam_chartTargetHom V hV n W₁ t)

/-- **`lam` is multiplicative.** -/
theorem lam_localMul (V : S.Opens) (hV : IsAffineOpen V) (i j : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (a : Γ(tensorPowerModule T P.L i, P.targetOpen V hV W₁))
    (b : Γ(tensorPowerModule T P.L j, P.targetOpen V hV W₁)) :
    P.lam V hV (i + j) W₁ (Stacks.TensorPowerDivision.localMul P.L a b) =
      Stacks.TensorPowerDivision.localMul (P.Lres V) (P.lam V hV i W₁ a)
        (P.lam V hV j W₁ b) := by
  unfold lam
  rw [P.pullPow_localMul V i j]
  exact Stacks.TensorPowerDivision.map_localMul (P.Lres V) _ _ _

/-- The twist datum of [Stacks, Tag 01NR] on `Proj_S(𝒜)`. -/
abbrev twD (A : SheafGradedAlgebra.{u} S) : RelativeProjTwists.TwistData A :=
  GluedTwistAlgebra.twistDataOfGradedAlgebra A

/-- An isomorphism of modules is a left inverse on sections over any open. -/
private theorem iso_inv_app_hom_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (W : X.Opens)
    (s : Γ(M, W)) : e.inv.app W (e.hom.app W s) = s :=
  (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ W) e.hom_inv_id) s).trans
    rfl

/-- An isomorphism of modules is a right inverse on sections over any open. -/
private theorem iso_hom_app_inv_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (W : X.Opens)
    (t : Γ(N, W)) : e.hom.app W (e.inv.app W t) = t :=
  (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ W) e.inv_hom_id) t).trans
    rfl

/-- The chart identification of [Stacks, Tag 01NR] carries the product to the canonical product. -/
theorem chartIso_hom_mul (V : S.Opens) (hV : IsAffineOpen V) (i j : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (s : Γ(Scheme.Modules.restrict ((twD A).algebra.piece i) ((relativeProj A).chart V hV), W₁))
    (t : Γ(Scheme.Modules.restrict ((twD A).algebra.piece j) ((relativeProj A).chart V hV), W₁)) :
    ((twD A).chartData.chartIso V hV (i + j)).hom.app W₁
        (((twD A).algebra.mul i j).app (op ((relativeProj A).chart V hV ''ᵁ W₁)) s t) =
      ((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra (A.grading V)).mul i j).app
        (op W₁) (((twD A).chartData.chartIso V hV i).hom.app W₁ s)
        (((twD A).chartData.chartIso V hV j).hom.app W₁ t) := by
  have hm := (twD A).chartIso_mul V hV i j W₁ (((twD A).chartData.chartIso V hV i).hom.app W₁ s)
    (((twD A).chartData.chartIso V hV j).hom.app W₁ t)
  have hs : (twD A).chartData.mapSection V hV i W₁
      (((twD A).chartData.chartIso V hV i).hom.app W₁ s) = s := iso_inv_app_hom_app _ _ _
  have ht : (twD A).chartData.mapSection V hV j W₁
      (((twD A).chartData.chartIso V hV j).hom.app W₁ t) = t := iso_inv_app_hom_app _ _ _
  rw [hs, ht] at hm
  refine Eq.trans ?_ (absoluteTwistProduct_eq_mul (A.grading V) i j W₁ _ _)
  refine (congrArg (((twD A).chartData.chartIso V hV (i + j)).hom.app W₁) hm.symm).trans ?_
  exact iso_hom_app_inv_app _ _ _

/-- `θ`'s local datum, read through `lam`, is [Stacks, Tag 01NK]'s `θ` on the chart. -/
theorem lam_thetaLoc (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (s : Γ(Scheme.Modules.restrict ((twD A).algebra.piece n) ((relativeProj A).chart V hV), W₁)) :
    P.lam V hV n W₁ ((P.thetaLoc V hV n).app W₁ s) =
      (Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta (A.grading V)
        (P.affineDatum V) n).app W₁ (((twD A).chartData.chartIso V hV n).hom.app W₁ s) :=
  P.lam_chartTargetHom_app V hV n W₁ _

/-- **The local datum of the relative `θ` is multiplicative**, on every open of the chart. -/
theorem thetaLoc_mul (V : S.Opens) (hV : IsAffineOpen V) (i j : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (s : Γ(Scheme.Modules.restrict ((twD A).algebra.piece i) ((relativeProj A).chart V hV), W₁))
    (t : Γ(Scheme.Modules.restrict ((twD A).algebra.piece j) ((relativeProj A).chart V hV), W₁)) :
    (P.thetaLoc V hV (i + j)).app W₁
        (((twD A).algebra.mul i j).app (op ((relativeProj A).chart V hV ''ᵁ W₁)) s t) =
      Stacks.TensorPowerDivision.localMul P.L ((P.thetaLoc V hV i).app W₁ s)
        ((P.thetaLoc V hV j).app W₁ t) := by
  apply P.lam_injective V hV (i + j) W₁
  refine (P.lam_thetaLoc V hV (i + j) W₁ _).trans ?_
  refine (congrArg ((Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta (A.grading V)
    (P.affineDatum V) (i + j)).app W₁) (chartIso_hom_mul V hV i j W₁ s t)).trans ?_
  refine (Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta_mul (A.grading V)
    (P.affineDatum V) i j (op W₁) _ _).trans ?_
  refine (pushforward_laurentRestrict_mul (A.grading V) (P.affineDatum V) i j W₁ _ _).trans ?_
  refine Eq.trans ?_ (P.lam_localMul V hV i j W₁ _ _).symm
  exact congrArg₂ (Stacks.TensorPowerDivision.localMul (P.Lres V))
    (P.lam_thetaLoc V hV i W₁ s).symm (P.lam_thetaLoc V hV j W₁ t).symm

/-- A transport of a section along an equality of opens is a restriction. -/
theorem eqRec_eq_map {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : U = V)
    (x : Γ(M, U)) :
    (h ▸ x : Γ(M, V)) = M.presheaf.map (eqToHom h.symm).op x := by
  subst h
  exact (map_id_apply M _ x).symm

/-- **The value of the induced datum, in the integer powers**, is `pullPow` of the value of `ψ`. -/
theorem intValue_affineDatum (V : S.Opens) (d : ℕ) (p : A.grading V d) :
    Stacks.AlgebraicGeometry.ProjChartGradedDivision.intValue (P.affineDatum V) d p =
      (tensorPowerModule (f ⁻¹ᵁ V).toScheme (P.Lres V) (d : ℤ)).presheaf.map
        (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self (f ⁻¹ᵁ V))).op
        (P.pullPow V d (f ⁻¹ᵁ V)
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
            (P.value d V (A.componentEquiv V d p)))) := by
  show (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare (P.Lres V) d).hom.app ⊤
      (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection P.L (f ⁻¹ᵁ V) d
        (P.value d V (A.componentEquiv V d p))) = _
  unfold Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection
    Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.pullPowSection
  refine (app_map (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare (P.Lres V) d).hom
    (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self (f ⁻¹ᵁ V))).op _).trans ?_
  refine congrArg ((tensorPowerModule (f ⁻¹ᵁ V).toScheme (P.Lres V) (d : ℤ)).presheaf.map
    (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self (f ⁻¹ᵁ V))).op) ?_
  refine (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app _ _ _).trans ?_
  exact (P.pullPow_eq V d (f ⁻¹ᵁ V) _).symm

/-- **`lam` of the value of `ψ` is the value of the induced datum**, restricted. -/
theorem lam_value (V : S.Opens) (hV : IsAffineOpen V) (d : ℕ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) (p : A.grading V d) :
    P.lam V hV d W₁ ((tensorPowerModule T P.L d).presheaf.map
        (homOfLE (P.targetOpen_le V hV W₁)).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
          (P.value d V (A.componentEquiv V d p)))) =
      Stacks.TensorPowerTrivialize.resTop (tensorPowerModule (f ⁻¹ᵁ V).toScheme (P.Lres V) d)
        (Stacks.AlgebraicGeometry.ProjChartGradedDivision.intValue (P.affineDatum V) d p)
        (P.sourceOpen V W₁) := by
  have hX : P.sourceOpen V W₁ ≤ (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ V) :=
    le_top.trans (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self (f ⁻¹ᵁ V))
  refine (congrArg ((tensorPowerModule (f ⁻¹ᵁ V).toScheme (P.Lres V) d).presheaf.map
    (homOfLE (P.sourceOpen_le V hV W₁)).op)
    (P.pullPow_map V d (P.targetOpen_le V hV W₁) _)).trans ?_
  refine Eq.trans ?_ (congrArg (fun u =>
    Stacks.TensorPowerTrivialize.resTop (tensorPowerModule (f ⁻¹ᵁ V).toScheme (P.Lres V) (d : ℤ))
      u (P.sourceOpen V W₁)) (P.intValue_affineDatum V d p)).symm
  exact (map_map _ _ _ (homOfLE hX).op _).trans (map_map _ _ _ _ _).symm

/-- `𝒪_{Proj_S(𝒜)}(n)`, the `n`-th piece of [Stacks, Tag 01NR]'s graded algebra. -/
abbrev Otw (A : SheafGradedAlgebra.{u} S) (n : ℤ) : (relativeProj A).scheme.Modules :=
  (twD A).algebra.piece n

/-- **`ψ : 𝒜_d(V) ⟶ Γ(π^{-1}(V), 𝒪(d))`**, the homogeneous-section map of [Stacks, Tag 01NR]. -/
abbrev psiU (A : SheafGradedAlgebra.{u} S) (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    Γ(Otw A d, (relativeProj A).toBase ⁻¹ᵁ V) :=
  ((twD A).ψ d).app V a

/-- The image under the chart of `V` of any open `W₁` lies in the preimage of `V` in
`Proj_S(𝒜)`. -/
theorem chart_image_le (V : S.Opens) (hV : IsAffineOpen V)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) :
    (relativeProj A).chart V hV ''ᵁ W₁ ≤ (relativeProj A).toBase ⁻¹ᵁ V :=
  (Scheme.Hom.image_mono _ le_top).trans
    (RelativeProjTwistGlue.chart_image_top (relativeProj A) V hV).le

/-- **[Stacks, Tag 01NR]'s chart identification carries `ψ(a)` to the section of `a`.** -/
theorem chartIso_hom_psiU (V : S.Opens) (hV : IsAffineOpen V) (d : ℕ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) (a : Γ(A.piece (d : ℤ), V)) :
    ((twD A).chartData.chartIso V hV d).hom.app W₁
        ((Otw A d).presheaf.map (homOfLE (chart_image_le V hV W₁)).op (psiU A d V a)) =
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading V) d).val.map
        (homOfLE (le_top : W₁ ≤ ⊤)).op
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading V) d
          ⟨DirectSum.of (A.sectionPieces V) d a, A.of_mem_grading V a⟩) := by
  have hc := (twD A).ψ_chart V hV d a
  have he := RelativeProjTwistGlue.chart_image_top (relativeProj A) V hV
  have hc1 := hc.trans (eqRec_eq_map (Otw A d) ((twD A).chartData.chart_range V hV).symm _)
  have hc' : ((twD A).chartData.chartIso V hV d).inv.app ⊤
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading V) d
          ⟨DirectSum.of (A.sectionPieces V) d a, A.of_mem_grading V a⟩) =
      (Otw A d).presheaf.map (eqToHom he).op (psiU A d V a) := hc1
  have h1 : (Otw A d).presheaf.map (homOfLE (chart_image_le V hV W₁)).op (psiU A d V a) =
      (Otw A d).presheaf.map
        (((relativeProj A).chart V hV).opensFunctor.map (homOfLE (le_top : W₁ ≤ ⊤))).op
        ((Otw A d).presheaf.map (eqToHom he).op (psiU A d V a)) :=
    (map_map (Otw A d) (eqToHom he).op _ _ (psiU A d V a)).symm
  refine (congrArg (((twD A).chartData.chartIso V hV d).hom.app W₁) h1).trans ?_
  refine (app_map ((twD A).chartData.chartIso V hV d).hom (homOfLE (le_top : W₁ ≤ ⊤)).op
    ((Otw A d).presheaf.map (eqToHom he).op (psiU A d V a))).trans ?_
  refine congrArg _ ?_
  rw [← hc']
  exact iso_hom_app_inv_app _ _ _

/-- **The local datum of the relative `θ` reads `ψ`**: on the restriction of `ψ(a)` for a
homogeneous section `a` of `𝒜_d` over `V`, it is the restriction of `ψ(a)`. -/
theorem thetaLoc_psiU (V : S.Opens) (hV : IsAffineOpen V) (d : ℕ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) (a : Γ(A.piece (d : ℤ), V)) :
    (P.thetaLoc V hV d).app W₁
        ((Otw A d).presheaf.map (homOfLE (chart_image_le V hV W₁)).op (psiU A d V a)) =
      (tensorPowerModule T P.L d).presheaf.map (homOfLE (P.targetOpen_le V hV W₁)).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
          (P.value d V a)) := by
  apply P.lam_injective V hV d W₁
  refine (P.lam_thetaLoc V hV d W₁ _).trans ?_
  refine (congrArg ((Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta (A.grading V)
    (P.affineDatum V) d).app W₁) (chartIso_hom_psiU V hV d W₁ a)).trans ?_
  refine (app_map (Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta (A.grading V)
    (P.affineDatum V) d) (homOfLE (le_top : W₁ ≤ ⊤)).op _).trans ?_
  refine (congrArg (((P.affineDatum V).pushLaurent d).presheaf.map (homOfLE (le_top : W₁ ≤ ⊤)).op)
    (Stacks.AlgebraicGeometry.ProjChartGradedTriple.pushTheta_app_top_degreeSection (A.grading V)
      (P.affineDatum V) d (A.of_mem_grading V a))).trans ?_
  have hy : A.componentEquiv V d ⟨DirectSum.of (A.sectionPieces V) d a, A.of_mem_grading V a⟩
      = a := (A.componentEquiv V d).apply_symm_apply a
  refine Eq.trans ?_ (congrArg (fun y => P.lam V hV d W₁
    ((tensorPowerModule T P.L d).presheaf.map (homOfLE (P.targetOpen_le V hV W₁)).op
      ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
        (P.value d V y)))) hy)
  refine Eq.trans ?_ (P.lam_value V hV d W₁ _).symm
  refine (pushforward_restrict_map ((P.affineDatum V).coveringOpen).ι (P.affineDatum V).glued
    (tensorPowerModule (f ⁻¹ᵁ V).toScheme (P.Lres V) d) (homOfLE (le_top : W₁ ≤ ⊤)) _).trans ?_
  exact map_map _ _ _ _ _

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
