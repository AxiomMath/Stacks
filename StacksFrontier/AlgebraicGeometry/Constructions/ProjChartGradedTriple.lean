module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaBuild
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistAwayPieceScalars
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleReduction.Basic

/-!
# Stacks Tag 01NK: the triple `(U(ψ), r_{L, ψ}, θ)` and its characterization

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj A`, `T` a scheme, `L` an invertible
`𝒪_T`-module and `ψ : A → Γ_*(T, L)` a graded map, in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. The open
`U(ψ) = ⋃_{f ∈ A_+} T_{ψ(f)}` is `GradedSections.coveringOpen`, the morphism
`r_{L, ψ} : U(ψ) ⟶ X` is `GradedSections.glued`, and the map of `ℤ`-graded algebras
`θ : r_{L, ψ}^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)}` is
`Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.theta`. This file proves that the triple
`(U(ψ), r_{L, ψ}, θ)` has the two properties of [Stacks, Tag 01NK] and is the only triple that
has them.

## Main definitions

* `laurentOn L U'`: `⨁_{d ∈ ℤ} L^{⊗ d}|_{U'}` for an arbitrary open `U'` of `T`.
* `IsClauseOne`, `IsClauseTwo`: properties (1) and (2) of the tag for an arbitrary triple
  `(U', r', θ')`.
* `Triple`, `IsTriple`, `canonicalTriple`: the triples, the property, and `(U(ψ), r_{L, ψ}, θ)`.
* `thetaUnital`: `θ` as a unital map of graded algebras.

## Main results

* `isClauseTwo_theta`: **property (2)** — `θ` carries the pullback of the global section of
  `𝒪_X(d)` attached to `a ∈ A_d` by [Stacks, Tag 01MP] to `ψ(a)|_{U(ψ)}`.
* `theta_map_one`: `θ` preserves the unit.
* `eq_coveringOpen_of_isClauseOne`, `eq_glued_of_isClause`, `eq_theta_of_isClauseTwo`, and
  together `eq_canonicalTriple`: **the uniqueness of the triple**, following the source — property
  (1) forces the open, property (2) together with the linearity of `θ'` forces the ring maps
  `a / f ^ j ↦ ψ(a) / ψ(f ^ j)` of `r'` on each `D₊(f)`, and property (2) together with the
  multiplicativity of `θ'` forces `θ'` on the pullback of every section over every `D₊(f)`.

## Implementation notes

The value `ψ(a) ∈ Γ(T, L^{⊗ d})` is read in the tensor powers of [Stacks, Tag 01CU], the pieces of
the Laurent algebra, through the canonical comparison of
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intValue`.
Property (2) is stated on the global sections over `U'`: the composite
`Γ(X, 𝒪_X(d)) ⟶ Γ(U', r'^*𝒪_X(d)) ⟶ Γ(U', L^{⊗ d})` is the map the source calls `θ`.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf integerGrading)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece
  coe_sectionsTwistEquivGradedPiece_degreeSection)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intChartSection intChartSection_mk
  intChartSectionOf intValue)
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.TensorPowerTrivialize (resTop res_resTop)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedTriple

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

section MkOne

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  {d : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 d)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))

/-- **The chart comparison on a fraction `x / 1` is the restriction of `ψ(x)`**, in Tag 01CU's
family. -/
theorem intChartSection_mk_one (hd : 0 < d) (n : ℕ) {x : A} (hx : x ∈ 𝒜 n)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ))
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (1 : Submonoid.powers f)) :
    intChartSection ψ hf hV hd (n : ℤ) y
      = resTop (tensorPowerModule T L (n : ℤ)) (intValue ψ n ⟨x, hx⟩) V := by
  have hf1 : f ^ 1 ∈ 𝒜 (1 * d) := Stacks.MorphismToProj.HomogeneousRatios.pow_mem hf 1
  have hfx : f ^ 1 * x ∈ 𝒜 (1 * d + n) := SetLike.mul_mem_graded hf1 hx
  have he : ((1 * d : ℕ) : ℤ) + (n : ℤ) = ((1 * d + n : ℕ) : ℤ) := (Nat.cast_add _ _).symm
  have hrep' : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk (f ^ 1 * x) (⟨f ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers f) := by
    rw [hrep]
    exact LocalizedModule.mk_eq.2 ⟨1, by simp [Submonoid.smul_def, smul_eq_mul]⟩
  rw [intChartSection_mk ψ hf hV hd (n : ℤ) y 1 (1 * d + n) he (f ^ 1 * x) hfx hrep']
  unfold intChartSectionOf
  have hmul := Stacks.AlgebraicGeometry.ProjChartGradedDivision.intMulSections_intValue ψ
    (1 * d) n ⟨f ^ 1, hf1⟩ ⟨x, hx⟩ ⟨f ^ 1 * x, hfx⟩ rfl
  refine Eq.trans ?_ (Stacks.TensorPowerDivision.intDivTop_intMulSections L
    (intValue ψ (1 * d) ⟨f ^ 1, hf1⟩)
    (Stacks.AlgebraicGeometry.ProjChartGradedDivision.le_nonvanishingOpen_intValue_pow ψ hf hV 1)
    (intValue ψ n ⟨x, hx⟩))
  exact congrArg _ hmul.symm

end MkOne


section ClauseTwo

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- **Clause (2) in the pushforward form of `θ`**: the degree-`d` component
`𝒪_X(d) ⟶ (r_{L, ψ})_*(L^{⊗ d}|_{U(ψ)})` carries the global section of `a ∈ 𝒜 d` to `ψ(a)`
restricted to `U(ψ)`. -/
theorem pushTheta_app_top_degreeSection (d : ℕ) {a : A} (ha : a ∈ 𝒜 d) :
    (pushTheta 𝒜 ψ (d : ℤ)).app ⊤ (degreeSection 𝒜 d ⟨a, ha⟩)
      = resTop (tensorPowerModule T L (d : ℤ)) (intValue ψ d ⟨a, ha⟩)
          (ψ.coveringOpen.ι ''ᵁ (ψ.glued ⁻¹ᵁ ⊤)) := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (ψ.pushLaurent (d : ℤ)).isSheaf
    (ι := Idx 𝒜) (fun p => AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))
    (fun _ => le_top) ?_ ?_
  · intro z _
    have hz : z ∈ (⨆ p : Idx 𝒜, chartIncl 𝒜 p ''ᵁ ⊤) := by
      rw [iSup_chartIncl_image_eq_top 𝒜]
      trivial
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨p, ?_⟩
    rwa [Stacks.AlgebraicGeometry.ProjChartGradedTheta.awayι_image_top 𝒜 p.1.2.2 p.2] at hp
  · intro p
    refine Eq.trans (Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map
      (pushTheta 𝒜 ψ (d : ℤ)) le_top (degreeSection 𝒜 d ⟨a, ha⟩)) ?_
    refine Eq.trans (pushTheta_app_basicOpen 𝒜 ψ (d : ℤ) p _) ?_
    refine Eq.trans (chartTargetIso_inv_apply 𝒜 ψ (d : ℤ) (p.1.2 : A) _) ?_
    refine Eq.trans (intChartSection_mk_one ψ p.1.2.2 (ψ.chartOpen_eq p.1.2.2 p.2).le p.2 d ha _
      (coe_sectionsTwistEquivGradedPiece_degreeSection 𝒜 p.1.2.2 p.2 d ⟨a, ha⟩)) ?_
    exact (res_resTop (tensorPowerModule T L (d : ℤ)) (intValue ψ d ⟨a, ha⟩)
      (homOfLE (Scheme.Hom.image_mono _ (Scheme.Hom.preimage_mono _ le_top)))).symm

end ClauseTwo

section Clauses

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} (L : T.Modules)
  [Stacks.Ample.IsInvertibleModule T L]

/-- **`⨁_{d ∈ ℤ} L^{⊗ d}|_{U'}`** for an open `U'` of `T`: the restriction to `U'` of the
Laurent algebra of `L`. -/
def laurentOn (U' : T.Opens) :
    SheafOfModules.GradedAlgebra.{u, u} U'.toScheme.ringCatSheaf :=
  haveI := isInvertible_of_isInvertibleModule (L := L)
  restrictGradedAlgebra U'.ι (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent L)

variable {L}

/-- `laurentRestrict 𝒜 ψ` is the restriction `laurentOn L U(ψ)` of the Laurent algebra of `L` to
the open `U(ψ)`. -/
theorem laurentRestrict_eq_laurentOn (ψ : GradedSections 𝒜 L) :
    laurentRestrict 𝒜 ψ = laurentOn L ψ.coveringOpen := rfl

variable {𝒜} (ψ : GradedSections 𝒜 L)

/-- **Property (1) of the tag** for a morphism `r' : U' ⟶ Proj A` out of an open `U'` of `T`:
`r'^{-1}(D₊(f)) = T_{ψ(f)}` for every homogeneous `f` of positive degree, read as an equality of
opens of `T`. -/
def IsClauseOne {U' : T.Opens} (r' : U'.toScheme ⟶ AlgebraicGeometry.Proj 𝒜) : Prop :=
  ∀ {e : ℕ} {f : A} (hf : f ∈ 𝒜 e), 0 < e →
    U'.ι ''ᵁ (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
      = nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩)

/-- **Property (2) of the tag** for a morphism `r' : U' ⟶ Proj A` and a map of `ℤ`-graded
`𝒪_{U'}`-algebras `θ' : r'^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U'}`: for every `d ≥ 0` and
`a ∈ A_d`, `θ'` carries the pullback of the global section of `𝒪_X(d)` attached to `a` by
[Stacks, Tag 01MP] to the restriction of `ψ(a)` to `U'`. -/
def IsClauseTwo {U' : T.Opens} (r' : U'.toScheme ⟶ AlgebraicGeometry.Proj 𝒜)
    (θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback r'
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜))
      (laurentOn L U')) : Prop :=
  ∀ (d : ℕ) {a : A} (ha : a ∈ 𝒜 d),
    (θ'.app (d : ℤ)).val.app (op ⊤)
        (Scheme.Modules.pullbackSection r' (twistM 𝒜 (d : ℤ)) ⊤ ⊤ (fun _ _ => trivial)
          (degreeSection 𝒜 d ⟨a, ha⟩))
      = resTop (tensorPowerModule T L (d : ℤ)) (intValue ψ d ⟨a, ha⟩) (U'.ι ''ᵁ ⊤)

/-- `r_{L, ψ}` has property (1). -/
theorem isClauseOne_glued : IsClauseOne ψ ψ.glued :=
  fun hf he => ψ.image_preimage_basicOpen_glued hf he

/-- **`θ` on a pulled-back section is its pushforward form on the section.** -/
theorem theta_app_pullbackSection (n : ℤ) (W : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : Γ(twistM 𝒜 n, W)) :
    ((theta 𝒜 ψ).app n).val.app (op (ψ.glued ⁻¹ᵁ W))
        (Scheme.Modules.pullbackSection ψ.glued (twistM 𝒜 n) W (ψ.glued ⁻¹ᵁ W) le_rfl s)
      = (pushTheta 𝒜 ψ n).app W s :=
  Eq.trans (congrArg (fun z => ((theta 𝒜 ψ).app n).val.app (op (ψ.glued ⁻¹ᵁ W)) z)
    (Stacks.Conormal.pullbackSection_self ψ.glued (twistM 𝒜 n) W s))
    (transposeAppHom_pullbackUnit ψ.glued.toLRSHom.toShHom (pushThetaHom 𝒜 ψ) n W s)

/-- `θ` in degree `d` carries the restriction to `W` of the pullback of the global section of
`a ∈ 𝒜 d` to the restriction of `ψ(a)` to `W`. -/
private theorem theta_app_map_pullbackSection_degreeSection (d : ℕ) {a : A} (ha : a ∈ 𝒜 d)
    {W : ψ.coveringOpen.toScheme.Opens} (hW : W ≤ ψ.glued ⁻¹ᵁ ⊤) :
    ((theta 𝒜 ψ).app (d : ℤ)).val.app (op W)
        (((Scheme.Modules.pullback ψ.glued).obj (twistM 𝒜 (d : ℤ))).presheaf.map (homOfLE hW).op
          (Scheme.Modules.pullbackSection ψ.glued (twistM 𝒜 (d : ℤ)) ⊤ (ψ.glued ⁻¹ᵁ ⊤) le_rfl
            (degreeSection 𝒜 d ⟨a, ha⟩)))
      = resTop (tensorPowerModule T L (d : ℤ)) (intValue ψ d ⟨a, ha⟩)
          (ψ.coveringOpen.ι ''ᵁ W) := by
  refine Eq.trans (Stacks.AlgebraicGeometry.ProjChartRatioPullback.app_map
    ((theta 𝒜 ψ).app (d : ℤ)) (homOfLE hW) _) ?_
  refine Eq.trans (congrArg (fun z => (ψ.laurentPiece (d : ℤ)).presheaf.map (homOfLE hW).op z)
    ((theta_app_pullbackSection ψ (d : ℤ) ⊤ _).trans
      (pushTheta_app_top_degreeSection 𝒜 ψ d ha))) ?_
  exact res_resTop (tensorPowerModule T L (d : ℤ)) (intValue ψ d ⟨a, ha⟩)
    (homOfLE (Scheme.Hom.image_mono _ hW))

/-- **`(r_{L, ψ}, θ)` has property (2).** -/
theorem isClauseTwo_theta : IsClauseTwo ψ ψ.glued (theta 𝒜 ψ) := by
  intro d a ha
  have hle : (⊤ : ψ.coveringOpen.toScheme.Opens) ≤ ψ.glued ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have h1 : Scheme.Modules.pullbackSection ψ.glued (twistM 𝒜 (d : ℤ)) ⊤ ⊤ hle
        (degreeSection 𝒜 d ⟨a, ha⟩)
      = ((Scheme.Modules.pullback ψ.glued).obj (twistM 𝒜 (d : ℤ))).presheaf.map
          (homOfLE hle).op
          (Scheme.Modules.pullbackSection ψ.glued (twistM 𝒜 (d : ℤ)) ⊤ (ψ.glued ⁻¹ᵁ ⊤) le_rfl
            (degreeSection 𝒜 d ⟨a, ha⟩)) :=
    (Stacks.AlgebraicGeometry.ProjChartRatioPullback.map_pullbackSectionHom ψ.glued
      (twistM 𝒜 (d : ℤ)) ⊤ _ ⊤ (homOfLE hle) le_rfl hle _).symm
  exact (congrArg (fun z => ((theta 𝒜 ψ).app (d : ℤ)).val.app (op ⊤) z) h1).trans
    (theta_app_map_pullbackSection_degreeSection ψ d ha hle)

end Clauses

section Morphism

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- **Property (1) forces the open**: a morphism `r' : U' ⟶ Proj A` with property (1) has
`U' = U(ψ)`, since the standard opens `D₊(f)` cover `Proj A`. -/
theorem eq_coveringOpen_of_isClauseOne {U' : T.Opens}
    {r' : U'.toScheme ⟶ AlgebraicGeometry.Proj 𝒜} (h1 : IsClauseOne ψ r') :
    U' = ψ.coveringOpen := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨m, g, hm, hg, hxg, -⟩ :=
      Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le 𝒜
        (Opens.mem_top (r'.base ⟨x, hx⟩))
    have hmem : x ∈ U'.ι ''ᵁ (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 g) :=
      ⟨⟨x, hx⟩, hxg, rfl⟩
    rw [h1 hg hm] at hmem
    exact ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hg hm hmem
  · obtain ⟨k, g, hg⟩ := ψ.exists_mem_nonvanishingOpenAt_of_mem_coveringOpen hx
    have hmem : x ∈ U'.ι ''ᵁ (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A)) := by
      rwa [h1 g.2 (Nat.succ_pos k)]
    obtain ⟨y, -, rfl⟩ := hmem
    exact y.2

/-- **The twist-side identity behind the ring maps**: on `D₊(f)`, the section of `𝒪_X(je)`
attached to `a ∈ A_{je}` is `a / f ^ j` times the one attached to `f ^ j`. -/
theorem awayToSection_smul_degreeSection {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) (j : ℕ)
    {a : A} (ha : a ∈ 𝒜 (j * e)) (ha' : a ∈ 𝒜 (j • e)) :
    (AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom (Away.mk 𝒜 hf j a ha') •
        (twistM 𝒜 ((j * e : ℕ) : ℤ)).presheaf.map
          (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⊤)).op
          (degreeSection 𝒜 (j * e) ⟨f ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hf j⟩)
      = (twistM 𝒜 ((j * e : ℕ) : ℤ)).presheaf.map
          (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⊤)).op
          (degreeSection 𝒜 (j * e) ⟨a, ha⟩) := by
  apply (sectionsTwistEquivGradedPiece 𝒜 hf he ((j * e : ℕ) : ℤ)).injective
  apply Subtype.ext
  refine (Stacks.AlgebraicGeometry.ProjTwistAwayPiece.coe_sectionsTwistEquivGradedPiece_smul 𝒜
    hf he _ _ _).trans ?_
  have h1 := coe_sectionsTwistEquivGradedPiece_degreeSection 𝒜 hf he (j * e)
    ⟨f ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hf j⟩
  have h2 := coe_sectionsTwistEquivGradedPiece_degreeSection 𝒜 hf he (j * e) ⟨a, ha⟩
  refine (congrArg (fun z => HomogeneousLocalization.val (Away.mk 𝒜 hf j a ha') • z) h1).trans
    (Eq.trans ?_ h2.symm)
  simp only
  rw [Away.val_mk, LocalizedModule.mk_smul_mk]
  refine LocalizedModule.mk_eq.2 ⟨1, ?_⟩
  simp [Submonoid.smul_def, smul_eq_mul, mul_comm]

variable {ψ}

/-- Property (2) read over a subset `W` of the preimage of a standard open. -/
private theorem app_pullbackSection_res_degreeSection_aux {U' : T.Opens}
    {r' : U'.toScheme ⟶ AlgebraicGeometry.Proj 𝒜}
    {θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback r'
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜))
      (laurentOn L U')} (h2 : IsClauseTwo ψ r' θ') {f : A}
    {W : U'.toScheme.Opens} (hW : W ≤ r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (k : ℕ) {b : A} (hb : b ∈ 𝒜 k) :
    (θ'.app (k : ℤ)).val.app (op W)
        (pullbackSectionHom r' (twistM 𝒜 (k : ℤ)) (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W hW
          ((twistM 𝒜 (k : ℤ)).presheaf.map
            (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⊤)).op
            (degreeSection 𝒜 k ⟨b, hb⟩)))
      = resTop (tensorPowerModule T L (k : ℤ)) (intValue ψ k ⟨b, hb⟩) (U'.ι ''ᵁ W) := by
  have hWt : W ≤ r' ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have e1 := pullbackSectionHom_map r' (twistM 𝒜 (k : ℤ)) ⊤
    (AlgebraicGeometry.Proj.basicOpen 𝒜 f) le_top W hW hWt (degreeSection 𝒜 k ⟨b, hb⟩)
  have e2 := Stacks.AlgebraicGeometry.ProjChartRatioPullback.map_pullbackSectionHom r'
    (twistM 𝒜 (k : ℤ)) ⊤ ⊤ W (homOfLE le_top) (fun _ _ => trivial) hWt
    (degreeSection 𝒜 k ⟨b, hb⟩)
  refine Eq.trans (congrArg (fun z => (θ'.app (k : ℤ)).val.app (op W) z)
    (e1.trans e2.symm)) ?_
  refine Eq.trans (Stacks.AlgebraicGeometry.ProjChartRatioPullback.app_map
    (θ'.app (k : ℤ)) (homOfLE le_top) _) ?_
  refine Eq.trans (congrArg (fun z => (((laurentOn L U').piece (k : ℤ))).val.map
    (homOfLE (le_top : W ≤ ⊤)).op z) (h2 k hb)) ?_
  exact res_resTop (tensorPowerModule T L (k : ℤ)) (intValue ψ k ⟨b, hb⟩)
    (homOfLE (Scheme.Hom.image_mono _ le_top))

/-- **The identity `ψ(a)|_W = r'^♯(a / f ^ j) · ψ(f ^ j)|_W`** for any triple with property (2),
over the preimage `W` of `D₊(f)`, read on `T`. -/
theorem resTop_intValue_eq_smul {U' : T.Opens} {r' : U'.toScheme ⟶ AlgebraicGeometry.Proj 𝒜}
    {θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback r'
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜))
      (laurentOn L U')} (h2 : IsClauseTwo ψ r' θ')
    {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) {W : U'.toScheme.Opens}
    (hW : r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f = W) (j : ℕ) {a : A}
    (ha : a ∈ 𝒜 (j * e)) (ha' : a ∈ 𝒜 (j • e)) :
    resTop (tensorPowerModule T L ((j * e : ℕ) : ℤ)) (intValue ψ (j * e) ⟨a, ha⟩) (U'.ι ''ᵁ W)
      = (U'.ι.appIso W).inv (r'.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W hW.ge
            ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom (Away.mk 𝒜 hf j a ha'))) •
          resTop (tensorPowerModule T L ((j * e : ℕ) : ℤ))
            (intValue ψ (j * e) ⟨f ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hf j⟩)
            (U'.ι ''ᵁ W) := by
  have hfj : f ^ j ∈ 𝒜 (j * e) := Stacks.MorphismToProj.HomogeneousRatios.pow_mem hf j
  have hval : ∀ {b : A} (hb : b ∈ 𝒜 (j * e)),
      (θ'.app ((j * e : ℕ) : ℤ)).val.app (op W)
          (pullbackSectionHom r' (twistM 𝒜 ((j * e : ℕ) : ℤ))
            (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W hW.ge
            ((twistM 𝒜 ((j * e : ℕ) : ℤ)).presheaf.map
              (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⊤)).op
              (degreeSection 𝒜 (j * e) ⟨b, hb⟩)))
        = resTop (tensorPowerModule T L ((j * e : ℕ) : ℤ)) (intValue ψ (j * e) ⟨b, hb⟩)
            (U'.ι ''ᵁ W) :=
    fun hb => app_pullbackSection_res_degreeSection_aux h2 hW.ge (j * e) hb
  have htw := awayToSection_smul_degreeSection hf he j ha ha'
  have hps := pullbackSectionHom_smul r' (twistM 𝒜 ((j * e : ℕ) : ℤ))
    (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W hW.ge
    ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom (Away.mk 𝒜 hf j a ha'))
    ((twistM 𝒜 ((j * e : ℕ) : ℤ)).presheaf.map
      (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⊤)).op
      (degreeSection 𝒜 (j * e) ⟨f ^ j, hfj⟩))
  refine (hval ha).symm.trans ?_
  refine Eq.trans (congrArg (fun z => (θ'.app ((j * e : ℕ) : ℤ)).val.app (op W)
    (pullbackSectionHom r' (twistM 𝒜 ((j * e : ℕ) : ℤ))
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W hW.ge z)) htw.symm) ?_
  refine Eq.trans (congrArg (fun z => (θ'.app ((j * e : ℕ) : ℤ)).val.app (op W) z) hps) ?_
  refine Eq.trans (Scheme.Modules.Hom.app_smul (θ'.app ((j * e : ℕ) : ℤ)) _ _) ?_
  exact congrArg _ (hval hfj)

end Morphism

section MorphismUnique

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- **Two morphisms into `Proj A` with the same preimages of the standard opens and the same
ring maps on the fractions `a / f ^ j` are equal.** -/
theorem eq_of_appLE_eq_proj {Y : Scheme.{u}} {Φ Φ' : Y ⟶ AlgebraicGeometry.Proj 𝒜}
    (W : Idx 𝒜 → Y.Opens)
    (hW : ∀ p : Idx 𝒜, Φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A) = W p)
    (hW' : ∀ p : Idx 𝒜, Φ' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A) = W p)
    (happ : ∀ (p : Idx 𝒜) (j : ℕ) (a : A) (ha : a ∈ 𝒜 (j • p.1.1)),
      Φ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) (W p) (hW p).ge
          ((AlgebraicGeometry.Proj.awayToSection 𝒜 (p.1.2 : A)).hom
            (Away.mk 𝒜 p.1.2.2 j a ha)) =
        Φ'.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) (W p) (hW' p).ge
          ((AlgebraicGeometry.Proj.awayToSection 𝒜 (p.1.2 : A)).hom
            (Away.mk 𝒜 p.1.2.2 j a ha))) :
    Φ = Φ' := by
  refine Scheme.hom_ext_of_forall _ _ fun y => ?_
  obtain ⟨m, g, hm, hg, hyg, -⟩ :=
    Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le 𝒜
      (Opens.mem_top (Φ.base y))
  let p : Idx 𝒜 := ⟨⟨m, ⟨g, hg⟩⟩, hm⟩
  have hy : y ∈ W p := (hW p) ▸ hyg
  refine ⟨W p, hy, ?_⟩
  have : IsAffine (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)).toScheme :=
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (p.1.2 : A) p.1.2.2 p.2
  have hmor : Φ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) (W p) (hW p).ge =
      Φ'.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) (W p) (hW' p).ge := by
    ext z
    obtain ⟨n, a, ha, hmk⟩ := Away.mk_surjective 𝒜 p.1.2.2
      ((AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (p.1.2 : A) p.1.2.2 p.2).inv z)
    have hz : (AlgebraicGeometry.Proj.awayToSection 𝒜 (p.1.2 : A)).hom
        (Away.mk 𝒜 p.1.2.2 n a ha) = z := by
      rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom 𝒜 (p.1.2 : A) p.1.2.2 p.2, hmk]
      exact ConcreteCategory.congr_hom
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (p.1.2 : A) p.1.2.2 p.2).inv_hom_id z
    rw [← hz]
    exact happ p n a ha
  rw [← Scheme.Hom.resLE_comp_ι Φ (hW p).ge, ← Scheme.Hom.resLE_comp_ι Φ' (hW' p).ge]
  refine congrArg (· ≫ _) (AlgebraicGeometry.ext_of_isAffine ?_)
  simp only [Scheme.Hom.resLE_app_top, hmor]

variable {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  {ψ : GradedSections 𝒜 L}

/-- **A morphism `U(ψ) ⟶ Proj A` which is part of a triple with properties (1) and (2) is
`r_{L, ψ}`.** -/
theorem eq_glued_of_isClause {r' : ψ.coveringOpen.toScheme ⟶ AlgebraicGeometry.Proj 𝒜}
    {θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback r'
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜))
      (laurentOn L ψ.coveringOpen)} (h1 : IsClauseOne ψ r') (h2 : IsClauseTwo ψ r' θ') :
    r' = ψ.glued := by
  have hW : ∀ p : Idx 𝒜, r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)
      = ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A) := fun p =>
    Scheme.Hom.image_injective ψ.coveringOpen.ι
      ((h1 p.1.2.2 p.2).trans (isClauseOne_glued ψ p.1.2.2 p.2).symm)
  refine eq_of_appLE_eq_proj (fun p => ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))
    hW (fun _ => rfl) fun p j a ha => ?_
  have ha' : a ∈ 𝒜 (j * p.1.1) := by simpa [smul_eq_mul] using ha
  have hx := resTop_intValue_eq_smul h2 p.1.2.2 p.2 (hW p) j ha' ha
  have hy := resTop_intValue_eq_smul (isClauseTwo_theta ψ) p.1.2.2 p.2 rfl j ha' ha
  have hV : ψ.coveringOpen.ι ''ᵁ (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))
      ≤ nonvanishingOpen T (tensorPowerModule T L ((j * p.1.1 : ℕ) : ℤ))
          (intValue ψ (j * p.1.1)
            ⟨(p.1.2 : A) ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem p.1.2.2 j⟩) :=
    Stacks.AlgebraicGeometry.ProjChartGradedDivision.le_nonvanishingOpen_intValue_pow ψ p.1.2.2
      (ψ.chartOpen_eq p.1.2.2 p.2).le j
  have hxy := Stacks.AlgebraicGeometry.ProjSectionsUnique.eq_of_smul_restrict_eq
    (tensorPowerModule T L ((j * p.1.1 : ℕ) : ℤ)) _ hV hx hy
  exact (ConcreteCategory.bijective_of_isIso
    (ψ.coveringOpen.ι.appIso _).inv).1 hxy

end MorphismUnique

section ThetaUnique

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- **A morphism out of the pullback of a module on `Proj A` is determined by its values on the
pullbacks of sections over the standard opens `D₊(f)`, `f` homogeneous of positive degree.** -/
theorem hom_ext_of_pullbackSection_basicOpen {Y : Scheme.{u}}
    (g : Y ⟶ AlgebraicGeometry.Proj 𝒜) {M : (AlgebraicGeometry.Proj 𝒜).Modules} {N : Y.Modules}
    {α β : (Scheme.Modules.pullback g).obj M ⟶ N}
    (h : ∀ (p : Idx 𝒜) (s : Γ(M, AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))),
      α.app (g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))
          (pullbackSectionHom g M _ _ le_rfl s)
        = β.app (g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))
          (pullbackSectionHom g M _ _ le_rfl s)) :
    α = β := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullbackSection g fun U a => ?_
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf N.isSheaf
    (ι := {p : Idx 𝒜 // AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A) ≤ U})
    (fun p => g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.1.2 : A))
    (fun p => Scheme.Hom.preimage_mono _ p.2) ?_ ?_
  · intro y hy
    obtain ⟨m, b, hm, hb, hyb, hbU⟩ :=
      Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le 𝒜 hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨⟨m, ⟨b, hb⟩⟩, hm⟩, hbU⟩, hyb⟩
  · intro p
    have hres : ∀ γ : (Scheme.Modules.pullback g).obj M ⟶ N,
        N.presheaf.map (homOfLE (Scheme.Hom.preimage_mono g p.2)).op
            (γ.app (g ⁻¹ᵁ U) (pullbackSectionHom g M U (g ⁻¹ᵁ U) le_rfl a))
          = γ.app (g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.1.2 : A))
              (pullbackSectionHom g M _ _ le_rfl (M.presheaf.map (homOfLE p.2).op a)) := by
      intro γ
      refine (Stacks.AlgebraicGeometry.ProjChartRatioPullback.app_map γ _ _).symm.trans ?_
      refine congrArg (γ.app _) ?_
      refine (Stacks.AlgebraicGeometry.ProjChartRatioPullback.map_pullbackSectionHom g M U _ _
        (homOfLE (Scheme.Hom.preimage_mono g p.2)) le_rfl (Scheme.Hom.preimage_mono g p.2)
        a).trans ?_
      exact (pullbackSectionHom_map g M U _ p.2 _ le_rfl _ a).symm
    exact (hres α).trans ((h p.1 _).trans (hres β).symm)

variable {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  {ψ : GradedSections 𝒜 L} {U' : T.Opens} {r' : U'.toScheme ⟶ AlgebraicGeometry.Proj 𝒜}
  {θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback r'
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜))
      (laurentOn L U')}

/-- **Property (2) read over the preimage of a standard open.** -/
theorem app_pullbackSection_res_degreeSection (h2 : IsClauseTwo ψ r' θ') {f : A}
    {W : U'.toScheme.Opens} (hW : W ≤ r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (k : ℕ) {b : A} (hb : b ∈ 𝒜 k) :
    (θ'.app (k : ℤ)).val.app (op W)
        (pullbackSectionHom r' (twistM 𝒜 (k : ℤ)) (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W hW
          ((twistM 𝒜 (k : ℤ)).presheaf.map
            (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⊤)).op
            (degreeSection 𝒜 k ⟨b, hb⟩)))
      = resTop (tensorPowerModule T L (k : ℤ)) (intValue ψ k ⟨b, hb⟩) (U'.ι ''ᵁ W) :=
  app_pullbackSection_res_degreeSection_aux h2 hW k hb

/-- Transport of `θ'` along an equality of degrees, on two sections of the twists over `D₊(f)`
with the same fraction. -/
theorem intPowReindex_app_pullbackSection {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e)
    {W : U'.toScheme.Opens} (hW : W ≤ r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    {n m : ℤ} (h : n = m) (z : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 f))
    (w : Γ(twistM 𝒜 m, AlgebraicGeometry.Proj.basicOpen 𝒜 f))
    (hzw : (sectionsTwistEquivGradedPiece 𝒜 hf he n z : LocalizedModule.Away f A)
      = (sectionsTwistEquivGradedPiece 𝒜 hf he m w : LocalizedModule.Away f A)) :
    (Stacks.TensorPowerDivision.intPowReindex L h).hom.app (U'.ι ''ᵁ W)
        ((θ'.app n).val.app (op W) (pullbackSectionHom r' (twistM 𝒜 n) _ W hW z))
      = (θ'.app m).val.app (op W) (pullbackSectionHom r' (twistM 𝒜 m) _ W hW w) := by
  subst h
  obtain rfl : z = w := (sectionsTwistEquivGradedPiece 𝒜 hf he n).injective (Subtype.ext hzw)
  rfl

/-- **`θ'` on the pullback of a section over `D₊(f)` is the chart comparison** `x / f ^ j ↦
ψ(x) / ψ(f ^ j)`, for any triple with property (2): the product of the value with
`ψ(f ^ j)` is `ψ(x)`, by the multiplicativity of `θ'` and property (2), and division by the
nonvanishing `ψ(f ^ j)` is unique. -/
theorem app_pullbackSection_eq_intChartSection (h2 : IsClauseTwo ψ r' θ') {e : ℕ} {f : A}
    (hf : f ∈ 𝒜 e) (he : 0 < e)
    (hV : U'.ι ''ᵁ (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
      ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))
    (n : ℤ) (s : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :
    (θ'.app n).val.app (op (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f))
        (pullbackSectionHom r' (twistM 𝒜 n) _ _ le_rfl s)
      = intChartSection ψ hf hV he n (sectionsTwistEquivGradedPiece 𝒜 hf he n s) := by
  obtain ⟨j, E, he', x, hx, hrep⟩ :=
    Stacks.AlgebraicGeometry.ProjChartGradedDivision.exists_int_rep hf he n
      (sectionsTwistEquivGradedPiece 𝒜 hf he n s)
  refine Eq.trans ?_ (intChartSection_mk ψ hf hV he n _ j E he' x hx hrep).symm
  have hfj : f ^ j ∈ 𝒜 (j * e) := Stacks.MorphismToProj.HomogeneousRatios.pow_mem hf j
  set σf := (twistM 𝒜 ((j * e : ℕ) : ℤ)).presheaf.map
    (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⊤)).op
    (degreeSection 𝒜 (j * e) ⟨f ^ j, hfj⟩) with hσf
  set σx := (twistM 𝒜 (E : ℤ)).presheaf.map
    (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⊤)).op
    (degreeSection 𝒜 E ⟨x, hx⟩) with hσx
  have hcoe : (sectionsTwistEquivGradedPiece 𝒜 hf he (E : ℤ) σx : LocalizedModule.Away f A)
      = (sectionsTwistEquivGradedPiece 𝒜 hf he (((j * e : ℕ) : ℤ) + n)
          (Stacks.AlgebraicGeometry.ProjConeTwist.twistMulSection 𝒜 ((j * e : ℕ) : ℤ) n
            (op (ProjectiveSpectrum.basicOpen 𝒜 f)) σf s) : LocalizedModule.Away f A) := by
    refine (coe_sectionsTwistEquivGradedPiece_degreeSection 𝒜 hf he E ⟨x, hx⟩).trans ?_
    refine Eq.trans ?_
      (Stacks.AlgebraicGeometry.ProjTwistAwayPiece.coe_sectionsTwistEquivGradedPiece_mul
        𝒜 hf he _ _ σf s).symm
    refine Eq.trans ?_ (congrArg (fun z => z * _)
      (coe_sectionsTwistEquivGradedPiece_degreeSection 𝒜 hf he (j * e) ⟨f ^ j, hfj⟩).symm)
    refine Eq.trans ?_ (congrArg (fun z => _ * z) hrep.symm)
    refine Eq.trans ?_ (LocalizedModule.mk_mul_mk (R := A) (S := Submonoid.powers f)
      (A := A)).symm
    refine LocalizedModule.mk_eq.2 ⟨1, ?_⟩
    simp [Submonoid.smul_def, smul_eq_mul, mul_comm]
  have hcast := intPowReindex_app_pullbackSection (θ' := θ') hf he le_rfl he'.symm σx _ hcoe
  have hmul : (θ'.app (((j * e : ℕ) : ℤ) + n)).val.app
        (op (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f))
        (pullbackSectionHom r' (twistM 𝒜 (((j * e : ℕ) : ℤ) + n)) _ _ le_rfl
          (Stacks.AlgebraicGeometry.ProjConeTwist.twistMulSection 𝒜 ((j * e : ℕ) : ℤ) n
            (op (ProjectiveSpectrum.basicOpen 𝒜 f)) σf s))
      = Stacks.TensorPowerDivision.localMul L
          ((θ'.app ((j * e : ℕ) : ℤ)).val.app (op (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f))
            (pullbackSectionHom r' (twistM 𝒜 ((j * e : ℕ) : ℤ)) _ _ le_rfl σf))
          ((θ'.app n).val.app (op (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f))
            (pullbackSectionHom r' (twistM 𝒜 n) _ _ le_rfl s)) :=
    (congrArg (fun z => (θ'.app (((j * e : ℕ) : ℤ) + n)).val.app
        (op (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)) z)
      (Stacks.Conormal.gradedPullback_mul_pullbackSection r'
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜) ((j * e : ℕ) : ℤ) n
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f) σf s).symm).trans
      (θ'.map_mul ((j * e : ℕ) : ℤ) n _ _ _)
  have hvf := app_pullbackSection_res_degreeSection h2 (le_refl
    (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)) (j * e) hfj
  have hvx := app_pullbackSection_res_degreeSection h2 (le_refl
    (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)) E hx
  symm
  refine Stacks.TensorPowerDivision.intDivOf_eq_of_mul_eq L _ _ n le_rfl ?_
  refine (Stacks.TensorPowerDivision.intMulMap_app_localMul L _ n _ _).trans ?_
  refine Eq.trans ?_ (Stacks.TensorPowerTrivialize.resTop_app _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun z =>
    (Stacks.TensorPowerDivision.intPowReindex L he'.symm).hom.app
      (U'.ι ''ᵁ (r' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)) z) hvx)
  refine Eq.trans ?_ hcast.symm
  refine Eq.trans ?_ hmul.symm
  exact congrArg (fun z => Stacks.TensorPowerDivision.localMul L z _) hvf.symm

/-- **`θ` is the only map of graded algebras out of `r_{L, ψ}^*(⨁ 𝒪_X(d))` with property (2).** -/
theorem eq_theta_of_isClauseTwo
    {θ'' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback ψ.glued
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜))
      (laurentOn L ψ.coveringOpen)} (h2 : IsClauseTwo ψ ψ.glued θ'') :
    θ'' = theta 𝒜 ψ := by
  refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
  refine hom_ext_of_pullbackSection_basicOpen ψ.glued fun p s => ?_
  exact (app_pullbackSection_eq_intChartSection h2 p.1.2.2 p.2
      (ψ.chartOpen_eq p.1.2.2 p.2).le n s).trans
    (app_pullbackSection_eq_intChartSection (isClauseTwo_theta ψ) p.1.2.2 p.2
      (ψ.chartOpen_eq p.1.2.2 p.2).le n s).symm

end ThetaUnique

section Unit

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- **`ψ(1)` is the unit section on every `T_{ψ(f)}`**: `ψ(f) = ψ(f · 1) = ψ(f) ψ(1)`, and
multiplication by the nonvanishing `ψ(f)` is injective. -/
theorem resTop_intValue_one {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) {W : T.Opens}
    (hW : W ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩)) :
    resTop (tensorPowerModule T L ((0 : ℕ) : ℤ)) (intValue ψ 0 ⟨1, SetLike.GradedOne.one_mem⟩) W
      = (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent L).one.eval (op W) := by
  have := isInvertible_of_isInvertibleModule (L := L)
  have hW' := Stacks.AlgebraicGeometry.ProjChartGradedDivision.le_nonvanishingOpen_intValue ψ hf hW
  apply (Stacks.TensorPowerDivision.bijective_intMulLinear L (intValue ψ e ⟨f, hf⟩) hW'
    ((0 : ℕ) : ℤ) (le_refl W)).1
  refine (Stacks.TensorPowerDivision.intMulLinear_resTop L _ _ W).trans ?_
  have hmul := Stacks.AlgebraicGeometry.ProjChartGradedDivision.intMulSections_intValue ψ e 0
    ⟨f, hf⟩ ⟨1, SetLike.GradedOne.one_mem⟩ ⟨f * 1, by simpa using hf⟩ rfl
  have hf1 : (⟨f * 1, by simpa using hf⟩ : 𝒜 (e + 0)) = ⟨f, hf⟩ := Subtype.ext (mul_one f)
  rw [hmul, hf1]
  refine Eq.trans ?_ (Stacks.TensorPowerDivision.intMulMap_app_localMul L _ _ W _).symm
  exact (eq_of_heq ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent L).mul_one
    (e : ℤ) (op W) (resTop (tensorPowerModule T L (e : ℤ)) (intValue ψ e ⟨f, hf⟩) W))).symm

/-- **`θ` preserves the unit**: it is a map of graded algebras in the unital sense. -/
theorem theta_map_one :
    SheafOfModules.sectionsMap ((theta 𝒜 ψ).app 0)
        (Stacks.Conormal.gradedPullback ψ.glued
          (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜)).one
      = (laurentRestrict 𝒜 ψ).one := by
  have := isInvertible_of_isInvertibleModule (L := L)
  refine (SheafOfModules.GradedAlgebra.UnitalHom.map_one_iff _).1 fun W => ?_
  obtain ⟨W⟩ := W
  have hWt : W ≤ ψ.glued ⁻¹ᵁ ⊤ := fun _ _ => trivial
  -- the unit of `⨁ 𝒪_X(d)` is the degree-zero section of `1`
  have hone : (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).one.eval
        (op (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens))
      = degreeSection 𝒜 0 ⟨1, SetLike.GradedOne.one_mem⟩ :=
    Stacks.AlgebraicGeometry.ProjConeTwist.twistSection_ext 𝒜 fun x =>
      (OreLocalization.one_def).trans rfl
  have hsrc : (Stacks.Conormal.gradedPullback ψ.glued
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜)).one.eval (op W)
      = ((Scheme.Modules.pullback ψ.glued).obj (twistM 𝒜 0)).presheaf.map (homOfLE hWt).op
          (Scheme.Modules.pullbackSection ψ.glued (twistM 𝒜 0) ⊤ (ψ.glued ⁻¹ᵁ ⊤) le_rfl
            (degreeSection 𝒜 0 ⟨1, SetLike.GradedOne.one_mem⟩)) :=
    (PresheafOfModules.sections_property (Stacks.Conormal.gradedPullback ψ.glued
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜)).one
        (homOfLE hWt).op).symm.trans
      (congrArg (fun z => ((Scheme.Modules.pullback ψ.glued).obj (twistM 𝒜 0)).presheaf.map
          (homOfLE hWt).op z)
        ((Stacks.Conormal.gradedPullback_one_eval ψ.glued
          (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜) ⊤).trans
          (congrArg (Scheme.Modules.pullbackSection ψ.glued (twistM 𝒜 0) ⊤ (ψ.glued ⁻¹ᵁ ⊤)
            le_rfl) hone)))
  refine Eq.trans (congrArg (fun z => ((theta 𝒜 ψ).app 0).val.app (op W) z) hsrc) ?_
  refine Eq.trans (theta_app_map_pullbackSection_degreeSection ψ 0 SetLike.GradedOne.one_mem hWt) ?_
  -- `ψ(1)` is the unit over `U(ψ)`, checked on the cover by the `T_{ψ(f)}`
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf
    (tensorPowerModule T L ((0 : ℕ) : ℤ)).isSheaf
    (fun p : (k : ℕ) × 𝒜 (k + 1) => ψ.coveringOpen.ι ''ᵁ W ⊓ ψ.nonvanishingOpenAt (p.1 + 1) p.2)
    (fun _ => inf_le_left) ?_ fun p => ?_
  · intro x hx
    obtain ⟨y, hyW, rfl⟩ := hx
    obtain ⟨k, g, hg⟩ := ψ.exists_mem_nonvanishingOpenAt_of_mem_coveringOpen y.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, g⟩, ⟨⟨y, hyW, rfl⟩, hg⟩⟩
  · refine Eq.trans (res_resTop _ _ _) ?_
    refine Eq.trans (resTop_intValue_one ψ p.2.2 inf_le_right) ?_
    exact (PresheafOfModules.sections_property _ _).symm

/-- **`θ` as a unital map of `ℤ`-graded `𝒪_{U(ψ)}`-algebras.** -/
def thetaUnital : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback ψ.glued
      (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜))
    (laurentRestrict 𝒜 ψ) :=
  SheafOfModules.GradedAlgebra.UnitalHom.ofHom (theta 𝒜 ψ) (theta_map_one ψ)

end Unit

section Triple

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} (L : T.Modules)
  [Stacks.Ample.IsInvertibleModule T L]

/-- **The triples `(U', r', θ')` of [Stacks, Tag 01NK]**: an open `U'` of `T`, a morphism of
schemes `r' : U' ⟶ Proj A` and a map of `ℤ`-graded `𝒪_{U'}`-algebras
`θ' : r'^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U'}`. -/
abbrev Triple : Type _ :=
  Σ U' : T.Opens, Σ r' : U'.toScheme ⟶ AlgebraicGeometry.Proj 𝒜,
    SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback r'
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜))
      (laurentOn L U')

variable {𝒜 L}

/-- A triple **has properties (1) and (2)** of the tag for `ψ`. -/
def IsTriple (ψ : GradedSections 𝒜 L) (t : Triple 𝒜 L) : Prop :=
  IsClauseOne ψ t.2.1 ∧ IsClauseTwo ψ t.2.1 t.2.2

/-- **The triple `(U(ψ), r_{L, ψ}, θ)`.** -/
def canonicalTriple (ψ : GradedSections 𝒜 L) : Triple 𝒜 L :=
  ⟨ψ.coveringOpen, ψ.glued, theta 𝒜 ψ⟩

/-- `(U(ψ), r_{L, ψ}, θ)` has properties (1) and (2). -/
theorem isTriple_canonicalTriple (ψ : GradedSections 𝒜 L) : IsTriple ψ (canonicalTriple ψ) :=
  ⟨isClauseOne_glued ψ, isClauseTwo_theta ψ⟩

/-- **Properties (1) and (2) characterize the triple**: any triple with them is
`(U(ψ), r_{L, ψ}, θ)`. -/
theorem eq_canonicalTriple {ψ : GradedSections 𝒜 L} {t : Triple 𝒜 L} (h : IsTriple ψ t) :
    t = canonicalTriple ψ := by
  obtain ⟨U', r', θ'⟩ := t
  obtain ⟨h1, h2⟩ := h
  obtain rfl := eq_coveringOpen_of_isClauseOne ψ h1
  obtain rfl := eq_glued_of_isClause h1 h2
  obtain rfl := eq_theta_of_isClauseTwo h2
  rfl

/-- **The triple is characterized by properties (1) and (2).** -/
theorem existsUnique_isTriple (ψ : GradedSections 𝒜 L) : ∃! t : Triple 𝒜 L, IsTriple ψ t :=
  ⟨canonicalTriple ψ, isTriple_canonicalTriple ψ, fun _ h => eq_canonicalTriple h⟩

end Triple

end Stacks.AlgebraicGeometry.ProjChartGradedTriple

end
