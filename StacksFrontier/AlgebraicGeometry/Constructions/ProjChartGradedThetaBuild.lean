module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaChartHom
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedIntegerOverlap
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedMultiplicative
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGradedGluing
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.RestrictRefine
public import StacksFrontier.AlgebraicGeometry.Morphism.Twist
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.WeightSplittingNaturality
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction
public import StacksFrontier.AlgebraicGeometry.ProjShared.RelevantCover
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPresentation
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedClauseTwoGlobal
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedVeronese
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedAlphaMaps
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedVeroneseOpen

/-!
# The map `θ` of Stacks Tag 01NK

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj 𝒜`, `T` a scheme, `L` an invertible
`𝒪_T`-module and `ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. The sibling files build the
morphism `r_{L, ψ} : U(ψ) ⟶ X` of [Stacks, Tag 01NK] and, on each standard open `D₊(f)` of a
homogeneous `f` of positive degree, the chart-level comparison

  `θ_f : (A_f)_n ⟶ Γ(L ^⊗ n, T_{ψ(f)})`,   `x / f ^ j ↦ ψ(x) / ψ(f ^ j)`,

together with its additivity, its `A_{(f)}`-semilinearity, its multiplicativity, and its
agreement with the chart of another homogeneous element on the overlap. **This file assembles
those charts into the map of `ℤ`-graded `𝒪_T`-algebras**

  `θ : r_{L, ψ}^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)}`

of that tag.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta` — **the degree-`n` component of
  `θ` in its pushforward form**, the morphism `𝒪_X(n) ⟶ (r_{L, ψ})_*(L^{⊗ n}|_{U(ψ)})` of
  sheaves of `𝒪_X`-modules glued from the chart data.
* `…laurentRestrict` — **the target `⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)}`**, the restriction to `U(ψ)` of
  the Laurent algebra of `L`, as a sheaf of `ℤ`-graded algebras.
* `…pushThetaHom` — the pushforward form of `θ` as a homomorphism of sheaves of graded algebras.
* `…theta` — **`θ` itself**, the adjoint transpose of `pushThetaHom`.

## Main results

* `…intChartSection_res` — **the chart comparison of a smaller standard open is the restriction
  of the chart comparison of a larger one.** This is the step the assembly turned on: the two
  chart comparisons are compared through the naturality of the identification of the sections of
  a twist with a graded piece of a localization
  (`Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_map_homOfLE`) and the overlap
  identity `…ProjChartGradedOverlap.intChartSection_eq_of_mk_eq_away`.
* `…nested_localApp_eq` — **the chart data of two nested standard opens agree at every open of
  `Proj 𝒜` the smaller one sees.** A section over the smaller standard open is, after
  multiplication by a unit, the restriction of a section over the larger
  (`exists_isUnit_smul_eq_res`, from the quasi-coherence of the twist), and on such restrictions
  the two data agree by `intChartSection_res`.
* `…localApp_chartTheta_eq` — the compatibility of the chart data over the whole cover, obtained
  from the nested case by `Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine` with the
  product `f g` as the common refinement.
* `…existsUnique_pushTheta` — **the degreewise component of `θ` exists and is unique.**
* `…pushTheta_mul` — **`θ` is multiplicative over an arbitrary open of `Proj 𝒜`**: the standard
  opens of positive-degree homogeneous elements are a basis
  (`Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le`), the target is a sheaf,
  and on a standard open multiplicativity is
  `…ProjChartGradedDivision.intChartSection_mul`.

## Implementation notes

**Why the chart datum had to be compared at a sub-chart.** The chart datum
`…ProjChartGradedTheta.chartRestrictHom` is produced by `…ModuleLimits.restrictHomOfΓMap`, which
pins it only by its action on the sections over the whole chart. Gluing, however, asks two charts
to agree over an arbitrary open seen by both, and the reduction to a common refinement
(`…ModuleHomGlue.localApp_restrictComp` with `…ModuleLimits.restrict_hom_ext_app_top`) leaves the
action of the larger chart's datum on the sections over the *smaller* standard open. That is not
settled by rigidity: it is the one place where the sections over a basic open have to be
described. They are, by the quasi-coherence of the twist, through
`AlgebraicGeometry.Scheme.Modules.exists_res_eq_pow_smul_of_isCompact` read on the affine chart
and `AlgebraicGeometry.Proj.awayι_preimage_basicOpen`, which identifies the preimage of `D₊(g)`
in `Spec A_{(f)}` with a basic open.

**`rw` is unusable on most of these goals and term mode is not.** The sections of a restriction
*are* the sections over the image, and the sections of a direct image *are* the sections over the
preimage, both by `rfl`; so the chains below are written with `Eq.trans` and `congrArg`, whose
elaboration is defeq-tolerant, rather than with rewriting, whose motive checks fail on the mixed
spellings.

**The target is the restriction of the Laurent algebra, not the Laurent algebra of the
restriction.** `laurentRestrict` is `restrictGradedAlgebra` applied to
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent`, so its degree-`n` piece is
`…GradedSections.laurentPiece n` on the nose and no comparison between tensor powers and
restriction is needed; `laurentRestrict_piece` is `rfl`. Likewise
`pushforward_laurentRestrict_piece` and `integerTwistAlgebra_piece` are `rfl`, so the universes
and base spellings of the source, the target and the transpose agree without a bridge.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleHomGlue

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild


/-- The compatibility of two members of a cover when one factors through the other through a
spectrum: it is enough that they agree on the sections over the image of the smaller. -/
theorem localApp_eq_of_nested {Y Z₁ : Scheme.{u}} {R : CommRingCat.{u}}
    (g : Z₁ ⟶ Y) [IsOpenImmersion g] (k : Spec R ⟶ Z₁) [IsOpenImmersion k]
    {g' : Spec R ⟶ Y} [IsOpenImmersion g'] (hk : k ≫ g = g')
    {M N : Y.Modules} [SheafOfModules.IsQuasicoherent M]
    (χ : M.restrict g ⟶ N.restrict g) (χ' : M.restrict g' ⟶ N.restrict g')
    (htop : ∀ (W : Z₁.Opens) (V' : Y.Opens) (e : g ''ᵁ W = V')
      (e' : g' ''ᵁ (⊤ : (Spec R).Opens) = V'), localApp g χ e = localApp g' χ' e')
    {W₁ : Z₁.Opens} {W₂ : (Spec R).Opens} {V : Y.Opens}
    (h₁ : g ''ᵁ W₁ = V) (h₂ : g' ''ᵁ W₂ = V) :
    localApp g χ h₁ = localApp g' χ' h₂ := by
  subst hk
  have e₁ : g ''ᵁ (k ''ᵁ (⊤ : (Spec R).Opens)) = (k ≫ g) ''ᵁ (⊤ : (Spec R).Opens) :=
    (Scheme.Hom.comp_image k g ⊤).symm
  have hmor : restrictComp g k χ = χ' := by
    refine Stacks.AlgebraicGeometry.ModuleLimits.restrict_hom_ext_app_top (k ≫ g) fun a => ?_
    have key : localApp (k ≫ g) (restrictComp g k χ) rfl = localApp (k ≫ g) χ' rfl :=
      (localApp_restrictComp g k χ e₁ rfl).symm.trans (htop _ _ e₁ rfl)
    exact congrArg
      (fun φ : Γ(M, (k ≫ g) ''ᵁ (⊤ : (Spec R).Opens)) ⟶
          Γ(N, (k ≫ g) ''ᵁ (⊤ : (Spec R).Opens)) => ConcreteCategory.hom φ a) key
  exact (localApp_restrictComp g k χ h₁ h₂).trans
    (congrArg (fun φ => localApp (k ≫ g) φ h₂) hmor)

/-- **A section of a quasi-coherent module over a basic open of an affine chart is, after
multiplication by a unit, the restriction of a section over the whole chart.** -/
theorem exists_isUnit_smul_eq_res {R : CommRingCat.{u}} {Y : Scheme.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] {M : Y.Modules} [SheafOfModules.IsQuasicoherent M]
    (s : Γ(Spec R, ⊤)) {W : (Spec R).Opens} (hW : W = ⊤ ⊓ (Spec R).basicOpen s)
    {V U : Y.Opens} (hV : j ''ᵁ W = V) (hU : j ''ᵁ (⊤ : (Spec R).Opens) = U)
    (hVle : V ≤ U) (a : Γ(M, V)) :
    ∃ (σ : Γ(Y, V)) (b : Γ(M, U)), IsUnit σ ∧
      σ • a = (ConcreteCategory.hom (M.presheaf.map (homOfLE hVle).op)) b := by
  subst hU
  subst hW
  subst hV
  have : SheafOfModules.IsQuasicoherent (M.restrict j) := inferInstance
  have hcpt : IsCompact ((⊤ : (Spec R).Opens) : Set (Spec R)) := by
    rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ
  have hsep : IsQuasiSeparated ((⊤ : (Spec R).Opens) : Set (Spec R)) := by
    rw [TopologicalSpace.Opens.coe_top]; exact isQuasiSeparated_univ
  obtain ⟨b, m, hb⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_res_eq_pow_smul_of_isCompact (M.restrict j) s
      hsep ⊤ hcpt le_rfl a
  refine ⟨((j.appIso _).inv
      (((Spec R).presheaf.map (homOfLE
        ((inf_le_left : (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen s ≤ ⊤).trans
          le_rfl)).op s) ^ m)), b, ?_, ?_⟩
  · refine IsUnit.map (j.appIso _).inv.hom (IsUnit.pow m ?_)
    have h0 : IsUnit ((Spec R).presheaf.map (homOfLE ((Spec R).basicOpen_le s)).op s) :=
      RingedSpace.isUnit_res_basicOpen (Spec R).toRingedSpace s
    have h1 := h0.map ((Spec R).presheaf.map (homOfLE
      (inf_le_right : (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen s ≤
        (Spec R).basicOpen s)).op).hom
    have h2 : ((Spec R).presheaf.map (homOfLE
          (inf_le_right : (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen s ≤
            (Spec R).basicOpen s)).op).hom
        (((Spec R).presheaf.map (homOfLE ((Spec R).basicOpen_le s)).op).hom s)
        = ((Spec R).presheaf.map (homOfLE
          ((inf_le_left : (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen s ≤ ⊤).trans
            le_rfl)).op).hom s := by
      have hhom : ((homOfLE ((Spec R).basicOpen_le s)).op ≫
          (homOfLE (inf_le_right : (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen s ≤
            (Spec R).basicOpen s)).op)
          = (homOfLE ((inf_le_left : (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen s ≤ ⊤).trans
              le_rfl)).op := Subsingleton.elim _ _
      rw [← CommRingCat.comp_apply, ← (Spec R).presheaf.map_comp, hhom]
    exact h2 ▸ h1
  · exact hb.symm

/-- A unit acts injectively. -/
theorem eq_of_isUnit_smul_eq {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {σ : R} (hσ : IsUnit σ) {p q : M} (h : σ • p = σ • q) : p = q := by
  obtain ⟨u, rfl⟩ := hσ
  have := congrArg (fun z : M => ((u⁻¹ : Rˣ) : R) • z) h
  simpa only [smul_smul, Units.inv_mul, one_smul] using this

open AlgebraicGeometry.ProjectiveSpectrum.Proj (imageSectionsIso)

/-- `localApp` is the action on the sections over the image, conjugated by the identification
of restricted sections with sections over the image. -/
theorem localApp_apply_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] {M N : Y.Modules}
    (χ : M.restrict g ⟶ N.restrict g) {W : X.Opens} {V : Y.Opens} (h : g ''ᵁ W = V)
    (s : Γ(M, V)) :
    (localApp g χ h) s =
      (imageSectionsIso g N W V h).hom (χ.app W ((imageSectionsIso g M W V h).inv s)) := by
  subst h
  simp [localApp, appImage, imageSectionsIso]

open HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf integerGrading)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intChartSection intChartSectionHom)
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM chartRestrictHom
  chartRestrictHom_app_top chartΓLinearMap chartΓAddHom_apply chartSectionsIso awayι_image_top)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.NonvanishingOpen (nonvanishingOpen)

section Value

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {e : ℕ} {f : A}

/-- **The chart morphism, read on the honest sections over `D₊(f)`, is the chart comparison.** -/
theorem chartLocalApp_apply (hf : f ∈ 𝒜 e) (he : 0 < e) (n : ℤ)
    (s : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :
    (localApp (AlgebraicGeometry.Proj.awayι 𝒜 f hf he)
        (chartRestrictHom 𝒜 ψ hf he n) (awayι_image_top 𝒜 hf he)) s
      = (ψ.chartTargetIso n f).inv
          (intChartSection ψ hf (ψ.chartOpen_eq hf he).le he n
            (sectionsTwistEquivGradedPiece 𝒜 hf he n s)) := by
  refine Eq.trans (localApp_apply_eq _ _ _ s) ?_
  refine Eq.trans (congrArg
    (fun z : Γ((ψ.pushLaurent n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he), ⊤) =>
      (chartSectionsIso 𝒜 (ψ.pushLaurent n) hf he).hom z)
    (chartRestrictHom_app_top 𝒜 ψ hf he n
      ((chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).inv s))) ?_
  change (chartSectionsIso 𝒜 (ψ.pushLaurent n) hf he).hom
      ((chartSectionsIso 𝒜 (ψ.pushLaurent n) hf he).inv
        ((ψ.chartTargetIso n f).inv
          (intChartSectionHom ψ hf (ψ.chartOpen_eq hf he).le he n
            (sectionsTwistEquivGradedPiece 𝒜 hf he n
              ((chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).hom
                ((chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).inv s)))))) = _
  refine Eq.trans (CategoryTheory.Iso.inv_hom_id_apply _ _) ?_
  exact congrArg
    (fun z : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 f) =>
      (ψ.chartTargetIso n f).inv
        (intChartSectionHom ψ hf (ψ.chartOpen_eq hf he).le he n
          (sectionsTwistEquivGradedPiece 𝒜 hf he n z)))
    (CategoryTheory.Iso.inv_hom_id_apply _ s)

end Value

section Nested

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {e : ℕ} {f : A}

/-- The identification of the sections of the direct image with the sections of `L ^⊗ n` over
the chart open commutes with restriction to a smaller chart. -/
theorem chartTargetIso_naturality (n : ℤ) (f x : A)
    (hfx : AlgebraicGeometry.Proj.basicOpen 𝒜 x ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (hcc : ψ.chartOpen x ≤ ψ.chartOpen f)
    (z : Γ(ψ.pushLaurent n, AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :
    (ψ.chartTargetIso n x).hom ((ψ.pushLaurent n).presheaf.map (homOfLE hfx).op z)
      = (tensorPowerModule T L n).presheaf.map (homOfLE hcc).op
        ((ψ.chartTargetIso n f).hom z) := by
  have hV : ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 x
      ≤ ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f := fun _ hp => hfx hp
  have hnat := AlgebraicGeometry.ProjectiveSpectrum.Proj.imageSectionsIso_naturality
    ψ.coveringOpen.ι (tensorPowerModule T L n)
    (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 x)
    (ψ.chartOpen f) (ψ.chartOpen x) rfl rfl hV hcc
  exact congr($hnat z)

end Nested

section Algebra

open _root_.ProjectiveSpectrum (moduleRestrictionMaps localizedRingMap)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGrading)

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Clearing the denominator across the localization map of [Stacks, Tag 01M4]: the image of
`a / f ^ N` multiplied by `f ^ N` is `a / 1`. -/
theorem localizedMap_mk_cancel {f g : A} {d d' : ℕ} (hd : 0 < d) (hd' : 0 < d')
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d')
    (hfg : _root_.ProjectiveSpectrum.basicOpen 𝒜 g ≤ _root_.ProjectiveSpectrum.basicOpen 𝒜 f)
    (n : ℤ) (N : ℕ) (a : A) :
    (algebraMap A (Localization.Away g) (f ^ N)) •
        (moduleRestrictionMaps 𝒜 (twistGrading (S := A) 𝒜 n) f g ⟨d, hd, hf⟩ ⟨d', hd', hg⟩
          hfg).localizedMap
          (LocalizedModule.mk a (⟨f ^ N, ⟨N, rfl⟩⟩ : Submonoid.powers f))
      = LocalizedModule.mk a (1 : Submonoid.powers g) := by
  let : Module (Localization.Away f) (LocalizedModule.Away (R := A) g A) :=
    Module.compHom (R := Localization.Away g) (S := Localization.Away f)
      (LocalizedModule.Away (R := A) g A)
      (localizedRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨d', hd', hg⟩ hfg).toRingHom
  have hcom : (algebraMap A (Localization.Away g)) (f ^ N)
      = (localizedRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨d', hd', hg⟩ hfg)
          ((algebraMap A (Localization.Away f)) (f ^ N)) :=
    ((localizedRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨d', hd', hg⟩ hfg).commutes (f ^ N)).symm
  rw [hcom]
  refine Eq.trans
    (((moduleRestrictionMaps 𝒜 (twistGrading (S := A) 𝒜 n) f g ⟨d, hd, hf⟩ ⟨d', hd', hg⟩
      hfg).localizedMap.map_smul ((algebraMap A (Localization.Away f)) (f ^ N))
      (LocalizedModule.mk a (⟨f ^ N, ⟨N, rfl⟩⟩ : Submonoid.powers f))).symm) ?_
  refine Eq.trans (congrArg
    (moduleRestrictionMaps 𝒜 (twistGrading (S := A) 𝒜 n) f g ⟨d, hd, hf⟩ ⟨d', hd', hg⟩
      hfg).localizedMap ?_)
    ((moduleRestrictionMaps 𝒜 (twistGrading (S := A) 𝒜 n) f g ⟨d, hd, hf⟩ ⟨d', hd', hg⟩
      hfg).map_mk a)
  rw [← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp [Submonoid.smul_def, mul_comm]


variable {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections 𝒜 L)

/-- **The chart comparison of a smaller standard open agrees with the restriction of the chart
comparison of a larger one.** -/
theorem intChartSection_res {e d' : ℕ} {f X : A} (hf : f ∈ 𝒜 e) (he : 0 < e)
    (hX : X ∈ 𝒜 d') (hd' : 0 < d')
    (hXf : _root_.ProjectiveSpectrum.basicOpen 𝒜 X ≤ _root_.ProjectiveSpectrum.basicOpen 𝒜 f)
    (hcc : ψ.chartOpen X ≤ ψ.chartOpen f) (n : ℤ)
    (b : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :
    intChartSection ψ hX (ψ.chartOpen_eq hX hd').le hd' n
        (sectionsTwistEquivGradedPiece 𝒜 hX hd' n
          ((twistM 𝒜 n).presheaf.map (homOfLE hXf).op b))
      = (tensorPowerModule T L n).presheaf.map (homOfLE hcc).op
          (intChartSection ψ hf (ψ.chartOpen_eq hf he).le he n
            (sectionsTwistEquivGradedPiece 𝒜 hf he n b)) := by
  obtain ⟨k₁, ez, hez, xz, hxz, hz⟩ :=
    Stacks.AlgebraicGeometry.ProjChartGradedDivision.exists_int_rep hf he n
      (sectionsTwistEquivGradedPiece 𝒜 hf he n b)
  obtain ⟨j₁, ey, hey, xy, hxy, hy⟩ :=
    Stacks.AlgebraicGeometry.ProjChartGradedDivision.exists_int_rep hX hd' n
      (sectionsTwistEquivGradedPiece 𝒜 hX hd' n
        ((twistM 𝒜 n).presheaf.map (homOfLE hXf).op b))
  have hnat : ((sectionsTwistEquivGradedPiece 𝒜 hX hd' n
        ((twistM 𝒜 n).presheaf.map (homOfLE hXf).op b) : LocalizedModule.Away X A))
      = (moduleRestrictionMaps 𝒜 (twistGrading (S := A) 𝒜 n) f X ⟨e, he, hf⟩ ⟨d', hd', hX⟩
          hXf).localizedMap
          ((sectionsTwistEquivGradedPiece 𝒜 hf he n b : LocalizedModule.Away f A)) :=
    Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_map_homOfLE 𝒜 hf he hX hd'
      hXf n b
  have hcan := localizedMap_mk_cancel 𝒜 he hd' hf hX hXf n k₁ xz
  rw [← hz] at hcan
  rw [← hnat, hy] at hcan
  have hsm : (algebraMap A (Localization.Away X)) (f ^ k₁) •
      LocalizedModule.mk xy (⟨X ^ j₁, ⟨j₁, rfl⟩⟩ : Submonoid.powers X)
      = LocalizedModule.mk (f ^ k₁ * xy) (⟨X ^ j₁, ⟨j₁, rfl⟩⟩ : Submonoid.powers X) := by
    rw [← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk, one_mul, smul_eq_mul]
  rw [hsm] at hcan
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 hcan
  obtain ⟨m, hm⟩ := u.2
  simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul] at hu
  rw [← hm] at hu
  rw [Stacks.AlgebraicGeometry.ProjChartGradedDivision.map_intChartSection]
  refine Stacks.AlgebraicGeometry.ProjChartGradedOverlap.intChartSection_eq_of_mk_eq_away ψ hX hf
    (ψ.chartOpen_eq hX hd').le ((homOfLE hcc).le.trans (ψ.chartOpen_eq hf he).le) hd' he n j₁ k₁
    hey hez _ _ hxy hxz hy hz ?_
  refine LocalizedModule.mk_eq.mpr ⟨⟨(X * f) ^ m, ⟨m, rfl⟩⟩, ?_⟩
  simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul]
  linear_combination (f ^ m) * hu


/-- The chart opens are monotone in the standard open. -/
theorem chartOpen_mono {f X : A}
    (hXf : AlgebraicGeometry.Proj.basicOpen 𝒜 X ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f) :
    ψ.chartOpen X ≤ ψ.chartOpen f :=
  Scheme.Hom.image_mono _ (fun _ hp => hXf hp)

/-- **The two chart data agree on the sections coming from the larger chart.** -/
theorem nested_agree_res {e d' : ℕ} {f X : A} (hf : f ∈ 𝒜 e) (he : 0 < e)
    (hX : X ∈ 𝒜 d') (hd' : 0 < d')
    (hXf : AlgebraicGeometry.Proj.basicOpen 𝒜 X ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (n : ℤ) {W : (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).Opens}
    (hW : AlgebraicGeometry.Proj.awayι 𝒜 f hf he ''ᵁ W = AlgebraicGeometry.Proj.basicOpen 𝒜 X)
    (b : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :
    (localApp (AlgebraicGeometry.Proj.awayι 𝒜 f hf he) (chartRestrictHom 𝒜 ψ hf he n) hW)
        ((twistM 𝒜 n).presheaf.map (homOfLE hXf).op b)
      = (localApp (AlgebraicGeometry.Proj.awayι 𝒜 X hX hd')
          (chartRestrictHom 𝒜 ψ hX hd' n) (awayι_image_top 𝒜 hX hd'))
        ((twistM 𝒜 n).presheaf.map (homOfLE hXf).op b) := by
  have hcc : ψ.chartOpen X ≤ ψ.chartOpen f := chartOpen_mono 𝒜 ψ hXf
  refine (ConcreteCategory.bijective_of_isIso (ψ.chartTargetIso n X).hom).1 ?_
  refine Eq.trans ?_ (congrArg (ψ.chartTargetIso n X).hom
    (chartLocalApp_apply 𝒜 ψ hX hd' n _)).symm
  refine Eq.trans (congrArg (ψ.chartTargetIso n X).hom
    (Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_map
      (AlgebraicGeometry.Proj.awayι 𝒜 f hf he) (chartRestrictHom 𝒜 ψ hf he n)
      (awayι_image_top 𝒜 hf he) hW hXf b)) ?_
  refine Eq.trans (chartTargetIso_naturality 𝒜 ψ n f X hXf hcc _) ?_
  refine Eq.trans (congrArg ((tensorPowerModule T L n).presheaf.map (homOfLE hcc).op)
    (congrArg (ψ.chartTargetIso n f).hom (chartLocalApp_apply 𝒜 ψ hf he n b))) ?_
  refine Eq.trans (congrArg ((tensorPowerModule T L n).presheaf.map (homOfLE hcc).op)
    (CategoryTheory.Iso.inv_hom_id_apply (ψ.chartTargetIso n f) _)) ?_
  refine Eq.trans ?_ (CategoryTheory.Iso.inv_hom_id_apply (ψ.chartTargetIso n X) _).symm
  exact (intChartSection_res 𝒜 ψ hf he hX hd' hXf hcc n b).symm


/-- **The compatibility of the chart data of two nested standard opens, at every open of
`Proj 𝒜` the smaller one sees.** -/
theorem nested_localApp_eq {e d' : ℕ} {f X : A} (hf : f ∈ 𝒜 e) (he : 0 < e)
    (hX : X ∈ 𝒜 d') (hd' : 0 < d') (n : ℤ)
    {W : (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).Opens}
    {V : (AlgebraicGeometry.Proj 𝒜).Opens}
    (hW : AlgebraicGeometry.Proj.awayι 𝒜 f hf he ''ᵁ W = V)
    (hW' : AlgebraicGeometry.Proj.awayι 𝒜 X hX hd' ''ᵁ (⊤ : (Spec _).Opens) = V) :
    localApp (AlgebraicGeometry.Proj.awayι 𝒜 f hf he) (chartRestrictHom 𝒜 ψ hf he n) hW
      = localApp (AlgebraicGeometry.Proj.awayι 𝒜 X hX hd')
          (chartRestrictHom 𝒜 ψ hX hd' n) hW' := by
  obtain rfl : V = AlgebraicGeometry.Proj.basicOpen 𝒜 X :=
    hW'.symm.trans (awayι_image_top 𝒜 hX hd')
  have hXf : AlgebraicGeometry.Proj.basicOpen 𝒜 X
      ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
    rw [← awayι_image_top 𝒜 hf he, ← hW]
    exact Scheme.Hom.image_mono _ le_top
  have hpre : AlgebraicGeometry.Proj.awayι 𝒜 f hf he ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen 𝒜 X
      = PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hf hX) :=
    AlgebraicGeometry.Proj.awayι_preimage_basicOpen 𝒜 hf he hX hd'
  have hbo : (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv
          (HomogeneousLocalization.Away.isLocalizationElem hf hX))
      = PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hf hX) :=
    AlgebraicGeometry.basicOpen_eq_of_affine _
  have hV₀ : AlgebraicGeometry.Proj.awayι 𝒜 f hf he ''ᵁ
        ((⊤ : (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).Opens) ⊓
          (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).basicOpen
            ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv
              (HomogeneousLocalization.Away.isLocalizationElem hf hX)))
      = AlgebraicGeometry.Proj.basicOpen 𝒜 X := by
    have hW₀ : (⊤ : (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).Opens) ⊓
          (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).basicOpen
            ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv
              (HomogeneousLocalization.Away.isLocalizationElem hf hX))
        = AlgebraicGeometry.Proj.awayι 𝒜 f hf he ⁻¹ᵁ
            AlgebraicGeometry.Proj.basicOpen 𝒜 X := by
      rw [hpre]
      exact Eq.trans (top_inf_eq _) hbo
    rw [hW₀]
    exact Stacks.AlgebraicGeometry.ModuleHomGlue.image_preimage_eq_self _
      (by rw [awayι_image_top 𝒜 hf he]; exact hXf)
  have : SheafOfModules.IsQuasicoherent (twistM 𝒜 n) :=
    Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_twistingSheaf 𝒜 n
  refine ConcreteCategory.hom_ext _ _ fun a => ?_
  obtain ⟨σ, b, hσ, hb⟩ := exists_isUnit_smul_eq_res
    (AlgebraicGeometry.Proj.awayι 𝒜 f hf he) (M := twistM 𝒜 n)
    ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv
      (HomogeneousLocalization.Away.isLocalizationElem hf hX)) rfl hV₀
    (awayι_image_top 𝒜 hf he) hXf a
  refine eq_of_isUnit_smul_eq hσ ?_
  rw [← Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_smul,
    ← Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_smul, hb]
  refine Eq.trans (Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_congr
    (AlgebraicGeometry.Proj.awayι 𝒜 f hf he) (chartRestrictHom 𝒜 ψ hf he n) hW hV₀ ▸
      nested_agree_res 𝒜 ψ hf he hX hd' hXf n hV₀ b) ?_
  exact congrArg (fun h => (localApp (AlgebraicGeometry.Proj.awayι 𝒜 X hX hd')
    (chartRestrictHom 𝒜 ψ hX hd' n) h)
      ((twistM 𝒜 n).presheaf.map (homOfLE hXf).op b))
    (Subsingleton.elim _ _)

end Algebra




section Glue

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- `Proj.awayι` does not depend on the recorded degree of its homogeneous element. -/
theorem awayι_congr_deg {y : A} {m m' : ℕ} (h : y ∈ 𝒜 m) (hp : 0 < m)
    (h' : y ∈ 𝒜 m') (hp' : 0 < m') :
    AlgebraicGeometry.Proj.awayι 𝒜 y h hp = AlgebraicGeometry.Proj.awayι 𝒜 y h' hp' := rfl


variable {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections 𝒜 L)

/-- The index of the cover of `Proj 𝒜` by the standard opens of homogeneous elements of
positive degree. -/
abbrev Idx : Type u := {p : (m : ℕ) × ↥(𝒜 m) // 0 < p.1}

/-- The affine chart of a member of the cover. -/
abbrev chartSpec (p : Idx 𝒜) : Scheme.{u} :=
  Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (p.1.2 : A)))

/-- The open immersion of the chart of a member of the cover. -/
abbrev chartIncl (p : Idx 𝒜) : chartSpec 𝒜 p ⟶ AlgebraicGeometry.Proj 𝒜 :=
  AlgebraicGeometry.Proj.awayι 𝒜 (p.1.2 : A) p.1.2.2 p.2

/-- The product of two members of the cover, again a member. -/
abbrev prodIdx (p q : Idx 𝒜) : Idx 𝒜 :=
  ⟨⟨p.1.1 + q.1.1, ⟨(p.1.2 : A) * (q.1.2 : A),
    SetLike.mul_mem_graded p.1.2.2 q.1.2.2⟩⟩, Nat.add_pos_left p.2 _⟩

/-- One member of the cover refines another when its chart factors through the other's. -/
def Refines (p q : Idx 𝒜) : Prop :=
  ∃ (k : chartSpec 𝒜 q ⟶ chartSpec 𝒜 p) (_ : IsOpenImmersion k),
    k ≫ chartIncl 𝒜 p = chartIncl 𝒜 q

/-- A member of the cover whose element is `p * q` is refined by the chart of `p`: the chart of the
product factors through the chart of `p` by the open immersion `Spec (awayMap)`. -/
private theorem refines_of_mul_eq (p q r : Idx 𝒜) (hx : (r.1.2 : A) = (p.1.2 : A) * (q.1.2 : A)) :
    Refines 𝒜 p r := by
  refine ⟨Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜 q.1.2.2 hx)), ?_, ?_⟩
  · have h := AlgebraicGeometry.Proj.SpecMap_awayMap_awayι 𝒜 p.1.2.2 p.2 q.1.2.2 hx
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜
        q.1.2.2 hx)) ≫ chartIncl 𝒜 p) := h ▸ inferInstance
    exact AlgebraicGeometry.IsOpenImmersion.of_comp _ (chartIncl 𝒜 p)
  · exact AlgebraicGeometry.Proj.SpecMap_awayMap_awayι 𝒜 p.1.2.2 p.2 q.1.2.2 hx

/-- The product member `prodIdx 𝒜 p q` refines `p`: the chart of the product factors through the
chart of `p` by an open immersion. -/
theorem refines_prodIdx_left (p q : Idx 𝒜) : Refines 𝒜 p (prodIdx 𝒜 p q) :=
  refines_of_mul_eq 𝒜 p q _ rfl

/-- The product member `prodIdx 𝒜 p q` refines `q`: the chart of the product factors through the
chart of `q` by an open immersion. -/
theorem refines_prodIdx_right (p q : Idx 𝒜) : Refines 𝒜 q (prodIdx 𝒜 p q) :=
  refines_of_mul_eq 𝒜 q p _ (mul_comm _ _)

/-- **The standard opens of the homogeneous elements of positive degree cover `Proj 𝒜`.** -/
theorem iSup_chartIncl_image_eq_top :
    ⨆ p : Idx 𝒜, chartIncl 𝒜 p ''ᵁ (⊤ : (chartSpec 𝒜 p).Opens) = ⊤ := by
  refine Eq.trans (iSup_congr fun p => awayι_image_top 𝒜 p.1.2.2 p.2) ?_
  refine AlgebraicGeometry.Proj.iSup_basicOpen_eq_top 𝒜 (fun p : Idx 𝒜 => (p.1.2 : A)) ?_
  classical
  intro z hz
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Ideal.sum_mem _ fun c _ => if hc0 : c = 0 then ?_ else
    Ideal.subset_span ⟨⟨⟨c, DirectSum.decompose 𝒜 z c⟩, Nat.pos_of_ne_zero hc0⟩, rfl⟩
  convert! Ideal.zero_mem _
  subst hc0
  exact hz


/-- The chart datum of `θ` in degree `n` at a member of the cover. -/
abbrev chartTheta (p : Idx 𝒜) (n : ℤ) :
    (twistM 𝒜 n).restrict (chartIncl 𝒜 p) ⟶ (ψ.pushLaurent n).restrict (chartIncl 𝒜 p) :=
  chartRestrictHom 𝒜 ψ p.1.2.2 p.2 n

/-- **The chart data agree wherever two members of the cover see the same open.** -/
theorem localApp_chartTheta_eq (n : ℤ) (p q : Idx 𝒜) (W₁ : (chartSpec 𝒜 p).Opens)
    (W₂ : (chartSpec 𝒜 q).Opens) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (h₁ : chartIncl 𝒜 p ''ᵁ W₁ = V) (h₂ : chartIncl 𝒜 q ''ᵁ W₂ = V) :
    localApp (chartIncl 𝒜 p) (chartTheta 𝒜 ψ p n) h₁
      = localApp (chartIncl 𝒜 q) (chartTheta 𝒜 ψ q n) h₂ := by
  have : SheafOfModules.IsQuasicoherent (twistM 𝒜 n) :=
    Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_twistingSheaf 𝒜 n
  refine Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine (chartIncl 𝒜)
    (fun r => chartTheta 𝒜 ψ r n) (κ := fun _ _ => PUnit.{u + 1})
    (fun r r' _ => prodIdx 𝒜 r r') (Refines 𝒜)
    (fun r r' _ => refines_prodIdx_left 𝒜 r r') (fun r r' _ => refines_prodIdx_right 𝒜 r r')
    ?_ ?_ p q W₁ W₂ V h₁ h₂
  · intro r r'
    refine le_trans ?_ (le_iSup
      (fun _ : PUnit.{u + 1} => chartIncl 𝒜 (prodIdx 𝒜 r r') ''ᵁ
        (⊤ : (chartSpec 𝒜 (prodIdx 𝒜 r r')).Opens)) PUnit.unit)
    rw [awayι_image_top 𝒜 r.1.2.2 r.2, awayι_image_top 𝒜 r'.1.2.2 r'.2,
      awayι_image_top 𝒜 (prodIdx 𝒜 r r').1.2.2 (prodIdx 𝒜 r r').2]
    exact (AlgebraicGeometry.Proj.basicOpen_mul 𝒜 (r.1.2 : A) (r'.1.2 : A)).ge
  · rintro r r' ⟨k, hk, hkeq⟩ V' W' W'' e₁ e₂
    exact localApp_eq_of_nested (chartIncl 𝒜 r) k hkeq _ _
      (fun _ _ e e' => nested_localApp_eq 𝒜 ψ r.1.2.2 r.2 r'.1.2.2 r'.2 n e e') e₁ e₂

/-- **The degreewise component of `θ`, in its pushforward form**: the unique morphism
`𝒪_X(n) ⟶ (r_{L, ψ})_*(L ^⊗ n|_{U(ψ)})` restricting on each standard open to the chart datum. -/
theorem existsUnique_pushTheta (n : ℤ) :
    ∃! φ : twistM 𝒜 n ⟶ ψ.pushLaurent n,
      ∀ p : Idx 𝒜, (Scheme.Modules.restrictFunctor (chartIncl 𝒜 p)).map φ
        = chartTheta 𝒜 ψ p n :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover (chartIncl 𝒜)
    (iSup_chartIncl_image_eq_top 𝒜) (fun p => chartTheta 𝒜 ψ p n)
    (localApp_chartTheta_eq 𝒜 ψ n)


/-- **The degree-`n` component of `θ` in its pushforward form.** -/
def pushTheta (n : ℤ) : twistM 𝒜 n ⟶ ψ.pushLaurent n :=
  (existsUnique_pushTheta 𝒜 ψ n).exists.choose

/-- The restriction of `pushTheta 𝒜 ψ n` to the chart of a member of the cover is the chart datum
`chartTheta 𝒜 ψ p n`. -/
theorem restrictFunctor_map_pushTheta (n : ℤ) (p : Idx 𝒜) :
    (Scheme.Modules.restrictFunctor (chartIncl 𝒜 p)).map (pushTheta 𝒜 ψ n)
      = chartTheta 𝒜 ψ p n :=
  (existsUnique_pushTheta 𝒜 ψ n).exists.choose_spec p

/-- **The degree-`n` component of `θ` acts on the sections over `D₊(f)` by the chart
comparison of the tag.** -/
theorem pushTheta_app_basicOpen (n : ℤ) (p : Idx 𝒜)
    (s : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))) :
    (pushTheta 𝒜 ψ n).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) s
      = (ψ.chartTargetIso n (p.1.2 : A)).inv
          (intChartSection ψ p.1.2.2 (ψ.chartOpen_eq p.1.2.2 p.2).le p.2 n
            (sectionsTwistEquivGradedPiece 𝒜 p.1.2.2 p.2 n s)) := by
  have h1 := Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_restrictFunctor_map
    (chartIncl 𝒜 p) (pushTheta 𝒜 ψ n) (awayι_image_top 𝒜 p.1.2.2 p.2)
  rw [restrictFunctor_map_pushTheta] at h1
  exact Eq.trans (congrArg
    (fun φ : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) ⟶
        Γ(ψ.pushLaurent n, AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) =>
      ConcreteCategory.hom φ s) h1.symm)
    (chartLocalApp_apply 𝒜 ψ p.1.2.2 p.2 n s)

end Glue


section RestrictAlgebra

variable {Z X : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j]

/-- **The restriction of a sheaf of graded algebras to an open subscheme.** The sections of a
restriction over `W` are the sections over the image `j ''ᵁ W`, by `rfl`, so every structure
map is the original one read at the image open. -/
def restrictGradedAlgebra (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) :
    SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf where
  piece n := Scheme.Modules.restrict (A.piece n) j
  mul i k :=
    { app W := (A.mul i k).app (op (j ''ᵁ W.unop))
      map_smul_left W _r x y := (A.mul i k).map_smul_left (op (j ''ᵁ W.unop)) _ x y
      map_smul_right W _r x y := (A.mul i k).map_smul_right (op (j ''ᵁ W.unop)) _ x y
      naturality {_W _W'} g x y := (A.mul i k).naturality (j.opensFunctor.map g.unop).op x y }
  one := PresheafOfModules.sectionsMk (fun W => A.one.eval (op (j ''ᵁ W.unop)))
    (fun _ _ g => PresheafOfModules.sections_property A.one (j.opensFunctor.map g.unop).op)
  mul_assoc i k l W x y z := A.mul_assoc i k l (op (j ''ᵁ W.unop)) x y z
  one_mul i W x := A.one_mul i (op (j ''ᵁ W.unop)) x
  mul_one i W x := A.mul_one i (op (j ''ᵁ W.unop)) x

/-- The degree-`n` piece of the restriction of a sheaf of graded algebras is the restriction of
its degree-`n` piece. -/
@[simp] theorem restrictGradedAlgebra_piece
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (n : ℤ) :
    (restrictGradedAlgebra j A).piece n = Scheme.Modules.restrict (A.piece n) j := rfl

end RestrictAlgebra


section Target

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- The invertibility of `L` in the spelling the Laurent algebra takes. -/
theorem isInvertible_of_isInvertibleModule :
    Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isSheafStruct T) L :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    T.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf T) L).mpr inferInstance

/-- **The target of `θ`: `⨁_{n ∈ ℤ} L^{⊗ n}|_{U(ψ)}`**, the restriction to `U(ψ)` of the
Laurent algebra of `L`. -/
def laurentRestrict : SheafOfModules.GradedAlgebra.{u, u} ψ.coveringOpen.toScheme.ringCatSheaf :=
  haveI := isInvertible_of_isInvertibleModule (L := L)
  restrictGradedAlgebra ψ.coveringOpen.ι (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent L)

/-- The degree-`n` piece of `laurentRestrict 𝒜 ψ` is `ψ.laurentPiece n`. -/
theorem laurentRestrict_piece (n : ℤ) : (laurentRestrict 𝒜 ψ).piece n = ψ.laurentPiece n := rfl

/-- The degree-`n` piece of the direct image of `laurentRestrict 𝒜 ψ` along `ψ.glued` is
`ψ.pushLaurent n`. -/
theorem pushforward_laurentRestrict_piece (n : ℤ) :
    (Stacks.RingedSpace.pushforwardAlgebra ψ.glued.toLRSHom.toShHom
      (laurentRestrict 𝒜 ψ)).piece n = ψ.pushLaurent n := rfl

/-- The degree-`n` piece of the integer twist algebra of `Proj 𝒜` is the twist `twistM 𝒜 n`. -/
theorem integerTwistAlgebra_piece (n : ℤ) :
    (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).piece n = twistM 𝒜 n := rfl


/-- The identification of the sections of the direct image with the sections over the chart
open is the identity: the chart open *is* the image of the preimage. -/
theorem chartTargetIso_inv_apply (n : ℤ) (f : A)
    (z : Γ(tensorPowerModule T L n, ψ.chartOpen f)) :
    (ψ.chartTargetIso n f).inv z = z := by
  simp [Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.chartTargetIso,
    AlgebraicGeometry.ProjectiveSpectrum.Proj.imageSectionsIso,
    AlgebraicGeometry.Scheme.Modules.restrictAppIso]
  rfl

/-- The multiplication of the target graded algebra over `D₊(f)` is the product of local
sections of the tensor powers over the chart open. -/
theorem target_mul_apply (i k : ℤ) (f : A)
    (a : Γ(tensorPowerModule T L i, ψ.chartOpen f))
    (b : Γ(tensorPowerModule T L k, ψ.chartOpen f)) :
    ((Stacks.RingedSpace.pushforwardAlgebra ψ.glued.toLRSHom.toShHom
        (laurentRestrict 𝒜 ψ)).mul i k).app (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f)) a b
      = Stacks.TensorPowerDivision.localMul L a b := rfl


/-- **`θ` is multiplicative on the sections over a standard open.** -/
theorem pushTheta_mul_basicOpen (i k : ℤ) (p : Idx 𝒜)
    (x : Γ(twistM 𝒜 i, AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)))
    (y : Γ(twistM 𝒜 k, AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))) :
    (pushTheta 𝒜 ψ (i + k)).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))
        (((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).mul i k).app
          (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))) x y)
      = ((Stacks.RingedSpace.pushforwardAlgebra ψ.glued.toLRSHom.toShHom
            (laurentRestrict 𝒜 ψ)).mul i k).app
          (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)))
          ((pushTheta 𝒜 ψ i).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) x)
          ((pushTheta 𝒜 ψ k).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) y) := by
  have hval : ∀ (m : ℤ) (z : Γ(twistM 𝒜 m, AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))),
      (pushTheta 𝒜 ψ m).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) z
        = intChartSection ψ p.1.2.2 (ψ.chartOpen_eq p.1.2.2 p.2).le p.2 m
            (sectionsTwistEquivGradedPiece 𝒜 p.1.2.2 p.2 m z) :=
    fun m z => Eq.trans (pushTheta_app_basicOpen 𝒜 ψ m p z)
      (chartTargetIso_inv_apply 𝒜 ψ m (p.1.2 : A) _)
  refine Eq.trans (Eq.trans (hval (i + k) _)
    (Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection_mul ψ p.1.2.2
      (ψ.chartOpen_eq p.1.2.2 p.2).le p.2 i k
      (sectionsTwistEquivGradedPiece 𝒜 p.1.2.2 p.2 i x)
      (sectionsTwistEquivGradedPiece 𝒜 p.1.2.2 p.2 k y) _
      (Stacks.AlgebraicGeometry.ProjTwistAwayPiece.coe_sectionsTwistEquivGradedPiece_mul
        𝒜 p.1.2.2 p.2 i k x y))) ?_
  refine Eq.trans ?_ (target_mul_apply 𝒜 ψ i k (p.1.2 : A)
    ((pushTheta 𝒜 ψ i).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) x)
    ((pushTheta 𝒜 ψ k).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) y)).symm
  exact congrArg₂
    (fun (a : Γ(tensorPowerModule T L i, ψ.chartOpen (p.1.2 : A)))
        (b : Γ(tensorPowerModule T L k, ψ.chartOpen (p.1.2 : A))) =>
      Stacks.TensorPowerDivision.localMul L a b) (hval i x).symm (hval k y).symm


/-- **`θ` is multiplicative on the sections over an arbitrary open of `Proj 𝒜`.** The standard
opens of homogeneous elements of positive degree form a basis, the target is a sheaf, and on a
standard open the identity is the multiplicativity of the chart comparison. -/
theorem pushTheta_mul (i k : ℤ) (U : (Opens (AlgebraicGeometry.Proj 𝒜).carrier)ᵒᵖ)
    (x : ((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).piece i).val.obj U)
    (y : ((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).piece k).val.obj U) :
    (pushTheta 𝒜 ψ (i + k)).val.app U
        (((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).mul i k).app U x y)
      = ((Stacks.RingedSpace.pushforwardAlgebra ψ.glued.toLRSHom.toShHom
            (laurentRestrict 𝒜 ψ)).mul i k).app U
          ((pushTheta 𝒜 ψ i).val.app U x) ((pushTheta 𝒜 ψ k).val.app U y) := by
  obtain ⟨U⟩ := U
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (ψ.pushLaurent (i + k)).isSheaf
    (ι := {p : Idx 𝒜 // AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A) ≤ U})
    (fun a => AlgebraicGeometry.Proj.basicOpen 𝒜 (a.1.1.2 : A)) (fun a => a.2) ?_ ?_
  · intro z hz
    obtain ⟨m, g, hm, hg, hzg, hgU⟩ :=
      Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le 𝒜 hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨⟨m, ⟨g, hg⟩⟩, hm⟩, hgU⟩, hzg⟩
  · intro a
    have hres := Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map
      (pushTheta 𝒜 ψ (i + k)) a.2
      (((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).mul i k).app (op U) x y)
    refine Eq.trans hres ?_
    have hnatA :=
      ((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).mul i k).naturality
        (homOfLE a.2).op x y
    refine Eq.trans (congrArg
      ((pushTheta 𝒜 ψ (i + k)).app
        (AlgebraicGeometry.Proj.basicOpen 𝒜 (a.1.1.2 : A))) hnatA) ?_
    refine Eq.trans (pushTheta_mul_basicOpen 𝒜 ψ i k a.1 _ _) ?_
    have hnatB := ((Stacks.RingedSpace.pushforwardAlgebra ψ.glued.toLRSHom.toShHom
      (laurentRestrict 𝒜 ψ)).mul i k).naturality (homOfLE a.2).op
      ((pushTheta 𝒜 ψ i).val.app (op U) x) ((pushTheta 𝒜 ψ k).val.app (op U) y)
    refine Eq.trans ?_ hnatB.symm
    exact congrArg₂
      (fun (p : Γ(ψ.pushLaurent i, AlgebraicGeometry.Proj.basicOpen 𝒜 (a.1.1.2 : A)))
          (q : Γ(ψ.pushLaurent k, AlgebraicGeometry.Proj.basicOpen 𝒜 (a.1.1.2 : A))) =>
        ((Stacks.RingedSpace.pushforwardAlgebra ψ.glued.toLRSHom.toShHom
          (laurentRestrict 𝒜 ψ)).mul i k).app
          (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (a.1.1.2 : A))) p q)
      (Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map (pushTheta 𝒜 ψ i) a.2 x).symm
      (Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map (pushTheta 𝒜 ψ k) a.2 y).symm

end Target


section TransposeHom

open Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction
open _root_.Stacks.PresheafOfModules

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)}
  {C : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}

/-- The degreewise adjoint transpose of a homomorphism `A ⟶ f_*C` of sheaves of graded
algebras, the unit not being involved. -/
def transposeAppHom (h : SheafOfModules.GradedAlgebra.Hom A (pushforwardAlgebra f C)) (n : ℤ) :
    (pullbackGradedAlgebra f A).piece n ⟶ C.piece n :=
  ((pullbackAdjunction f).homEquiv (A.piece n) (C.piece n)).symm (h.app n)

/-- The degreewise transpose `transposeAppHom f h n`, evaluated on the image under the pullback
unit of a section `a` of `A.piece n` over `V`, is the value of `h.app n` on `a`. -/
theorem transposeAppHom_pullbackUnit
    (h : SheafOfModules.GradedAlgebra.Hom A (pushforwardAlgebra f C)) (n : ℤ)
    (V : Opens Y.carrier) (a : (A.piece n).val.obj (op V)) :
    (transposeAppHom f h n).val.app (op ((opensMap f).obj V))
        (pullbackUnit f (A.piece n) (op V) a) = (h.app n).val.app (op V) a :=
  SheafOfModules.GradedAlgebra.homEquiv_symm_val_app_unit f (M := A.piece n)
    (N := C.piece n) (h.app n) (op V) a

/-- **The adjoint transpose of a homomorphism `A ⟶ f_*C` is a homomorphism `f^*A ⟶ C`.** -/
def transposeHom (h : SheafOfModules.GradedAlgebra.Hom A (pushforwardAlgebra f C)) :
    SheafOfModules.GradedAlgebra.Hom (pullbackGradedAlgebra f A) C where
  app := transposeAppHom f h
  map_mul i j U x y := by
    obtain ⟨U⟩ := U
    refine pullbackBilinear_ext f
      (bilinPostcomp ((pullbackGradedAlgebra f A).mul i j) (transposeAppHom f h (i + j)))
      ((((C.mul i j).compLeft (transposeAppHom f h i).val).compRight
        (transposeAppHom f h j).val)) (fun V a b => ?_) U x y
    change (transposeAppHom f h (i + j)).val.app (op ((opensMap f).obj V))
        (((pullbackGradedAlgebra f A).mul i j).app (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece i) (op V) a) (pullbackUnit f (A.piece j) (op V) b)) =
      (C.mul i j).app (op ((opensMap f).obj V))
        ((transposeAppHom f h i).val.app (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece i) (op V) a))
        ((transposeAppHom f h j).val.app (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece j) (op V) b))
    rw [pullbackGradedAlgebra_mul_pullbackUnit f A i j V a b, transposeAppHom_pullbackUnit,
      transposeAppHom_pullbackUnit, transposeAppHom_pullbackUnit]
    exact h.map_mul i j (op V) a b

end TransposeHom


section Theta

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- **`θ` in its pushforward form**: the homomorphism of sheaves of `ℤ`-graded algebras
`⨁_{d ∈ ℤ} 𝒪_X(d) ⟶ (r_{L, ψ})_* (⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)})` on `Proj 𝒜`. -/
def pushThetaHom : SheafOfModules.GradedAlgebra.Hom
    (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜)
    (Stacks.RingedSpace.pushforwardAlgebra ψ.glued.toLRSHom.toShHom (laurentRestrict 𝒜 ψ)) where
  app n := pushTheta 𝒜 ψ n
  map_mul := pushTheta_mul 𝒜 ψ

/-- **`θ` of [Stacks, Tag 01NK]**: the map of `ℤ`-graded `𝒪_T`-algebras
`r_{L, ψ}^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)}`. -/
def theta : SheafOfModules.GradedAlgebra.Hom
    (Stacks.Conormal.gradedPullback ψ.glued
      (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜))
    (laurentRestrict 𝒜 ψ) :=
  transposeHom ψ.glued.toLRSHom.toShHom (pushThetaHom 𝒜 ψ)

end Theta



section Carrier

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open Stacks.AlgebraicGeometry.ProjChartGradedDivision (chartSection)
open Stacks.AlgebraicGeometry.ProjChartGradedClauseTwoGlobal
  (existsUnique_section_res_eq_chartSection)
open Stacks.AlgebraicGeometry.ProjChartGradedVeroneseOpen
  (iSup_nonvanishingOpen_pullback_eq_top homOfLE_glued_eq_gluedVeronese_pullback)
open Stacks.AlgebraicGeometry.ProjChartGradedVeronese (iSup_nonvanishingOpen_le_coveringOpen
  gluedVeronese)
open Stacks.AlgebraicGeometry.ProjChartGradedAlphaMatch (alphaVeronese)
open Stacks.AlgebraicGeometry.ProjChartGradedAlphaMaps (eq_chartSection_of_smul_of_alpha)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.GradedLocalization (smul_mem_gradedPiece)
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance (pullbackDegreeSection)
open Stacks.TensorPowers (natTensorPow)

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- **Chart-level facts about `r_{L, ψ}` and `θ`**, collected: property (1) of
[Stacks, Tag 01NK]; `θ` as the transpose of its pushforward form; the chart formula
`x / f ^ j ↦ ψ(x) / ψ(f ^ j)` of that form on `D₊(f)`; the square of property (2) read through the
charts; the uniqueness of `r_{L, ψ}` among morphisms restricting on each `T_{ψ(f)}` to the
dehomogenisation chart; and, for `d ≥ 1`, the agreement of `r_{L, ψ}` with the morphism of
[Stacks, Tag 01N8] on an open where `ψ(A_d)` generates, and of the chart comparison with that tag's
`α` when `ψ(A_d)` generates on all of `T`.

The whole statement of [Stacks, Tag 01NK] — the triple, its characterization by properties (1)
and (2), and the final assertion — is
`Stacks.AlgebraicGeometry.ProjChartGradedTripleTag.tag01NK`. -/
theorem glued_theta_chart_facts :
    (∀ {e : ℕ} {f : A} (hf : f ∈ 𝒜 e), 0 < e →
        ψ.coveringOpen.ι ''ᵁ (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
          = nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))
      ∧ theta 𝒜 ψ = transposeHom ψ.glued.toLRSHom.toShHom (pushThetaHom 𝒜 ψ)
      ∧ (∀ (n : ℤ) (p : Idx 𝒜)
          (s : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A))),
          (pushTheta 𝒜 ψ n).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p.1.2 : A)) s
            = (ψ.chartTargetIso n (p.1.2 : A)).inv
                (intChartSection ψ p.1.2.2 (ψ.chartOpen_eq p.1.2.2 p.2).le p.2 n
                  (sectionsTwistEquivGradedPiece 𝒜 p.1.2.2 p.2 n s)))
      ∧ (∀ (d : ℕ) {a : A} (ha : a ∈ 𝒜 d),
          ∃! s : Γ(natTensorPow L d, ψ.coveringOpen),
            ∀ p : (k : ℕ) × 𝒜 (k + 1),
              (natTensorPow L d).presheaf.map
                  (homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2)).op s
                = chartSection ψ p.2.2 (le_refl _) d
                    (sectionsTwistEquivGradedPiece 𝒜 p.2.2 (Nat.succ_pos p.1) (d : ℤ)
                      ((twistingSheaf 𝒜 (d : ℤ)).val.map
                        (homOfLE (le_top :
                          ProjectiveSpectrum.basicOpen 𝒜 (p.2.1 : A) ≤ ⊤)).op
                        (degreeSection 𝒜 d ⟨a, ha⟩))))
      ∧ (∀ {Φ : ψ.coveringOpen.toScheme ⟶ AlgebraicGeometry.Proj 𝒜},
          (∀ (e : ℕ) (f : A) (hf : f ∈ 𝒜 e) (he : 0 < e),
              T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he) ≫ Φ
                = ψ.chartToProj hf
                    (le_refl (nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))) he) →
            Φ = ψ.glued)
      ∧ (∀ {d : ℕ} (hd : 0 < d) {V : T.Opens}
          (hVgen : V ≤ ⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)),
          T.homOfLE (hVgen.trans (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd)) ≫ ψ.glued
            = Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜
                (gluedVeronese 𝒜 (GradedSections.pullback V.ι ψ) hd
                  (iSup_nonvanishingOpen_pullback_eq_top 𝒜 ψ hVgen)))
      ∧ (∀ {d : ℕ} (hd : 0 < d)
          (hgen : ⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g) = ⊤)
          {f : A} (hf : f ∈ 𝒜 d) {V : T.Opens}
          (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
          (F : Stacks.GradedLocalization.gradedPiece 𝒜
                (AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading (S := A) 𝒜) f (d : ℤ) →
              Γ(natTensorPow L d, V)),
          (∀ (r : HomogeneousLocalization.Away 𝒜 f)
              (y : Stacks.GradedLocalization.gradedPiece 𝒜
                (AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading (S := A) 𝒜) f (d : ℤ)),
              F ⟨HomogeneousLocalization.val r • (y : LocalizedModule.Away f A),
                  smul_mem_gradedPiece 𝒜 _ hf (d : ℤ) r y.2⟩
                = (ψ.homogeneousRatios hf hV).lift hd r • F y) →
          (∀ y : Stacks.GradedLocalization.gradedPiece 𝒜
                (AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading (S := A) 𝒜) f (d : ℤ),
              (y : LocalizedModule.Away f A)
                  = LocalizedModule.mk f (1 : Submonoid.powers f) →
              F y = resTop (natTensorPow L d) ((alphaVeronese 𝒜 ψ hd hgen).hom.app ⊤
                  (pullbackDegreeSection 𝒜 (gluedVeronese 𝒜 ψ hd hgen) ⟨f, hf⟩)) V) →
          F = chartSection ψ hf hV d) :=
  ⟨fun hf he => ψ.image_preimage_basicOpen_glued hf he,
    rfl,
    fun n p s => pushTheta_app_basicOpen 𝒜 ψ n p s,
    fun d _ ha =>
      existsUnique_section_res_eq_chartSection 𝒜 ψ ha,
    fun h => ψ.eq_glued_of_homOfLE_eq h,
    by
      intro d hd V hVgen
      exact homOfLE_glued_eq_gluedVeronese_pullback 𝒜 ψ hd hVgen,
    by
      intro d hd hgen f hf V hV F hsmul halpha
      exact eq_chartSection_of_smul_of_alpha 𝒜 ψ hd hgen hf hV F hsmul halpha⟩

end Carrier

end Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild

end
