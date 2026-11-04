module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.VeroneseDegreeOne
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjFunctorSurjective
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedClassifying
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedVeronese
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleStructureMorphism
public import StacksFrontier.AlgebraicGeometry.TwistTensor.UniversalVeroneseSections
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections

/-!
# A morphism into `Proj` of a ring generated in degree one, read on its charts

Let `A` be a quasi-coherent graded `𝒪_S`-algebra and `U` an open of `S` over which the graded ring
`A(U)` of sections is generated in degree one, so that every morphism `h : Y ⟶ Proj A(U)` factors
through the open `U_1` of [Stacks, Tag 01NA]. Pulling the universal family of
[Stacks, Tag 01N9] back along `h` gives a graded map `ψ_h : A(U) ⟶ Γ_*(Y, h^* 𝒪(1))` whose
classified morphism is `h` ([Stacks, Tag 01NC]). Consequently any graded map `χ` into the section
ring of an invertible module that is strictly equivalent to `ψ_h` has `h` as its morphism: the
chart of `χ` at a degree-one section `s` is `h` restricted to the nonvanishing open of `χ(s)`.

The degree-zero part of `ψ_h` is the pullback of functions along `h`: an element `a` of `A(U)_0`
goes to `h^♯(a)` times the unit section.

## Main definitions

* `Stacks.Tag01VMVeryAmple.pulledUniversal`: the pullback `ψ_h` of the universal family.

## Main results

* `Stacks.Tag01VMVeryAmple.classifyingHom_pulledUniversal`: its classified morphism is `h`.
* `Stacks.Tag01VMVeryAmple.divUnit_pulledUniversal_zero`: its degree-zero part.
* `Stacks.Tag01VMVeryAmple.chartToProj_eq_of_sectionsEquiv`: the chart of a strictly equivalent
  graded map is `h`.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjTripleClassifying
open Stacks.AlgebraicGeometry.ProjTripleStructureMorphism
open Stacks.AlgebraicGeometry.ProjTriplePullback
open Stacks.AlgebraicGeometry.ProjClassifyingPullback
open Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)

universe u

namespace Stacks.Tag01VMVeryAmple

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (U : S.Opens)
  (hgen : Algebra.adjoin (A.grading U 0) (A.grading U 1 : Set (A.sectionRing U)) = ⊤)
  {Y : Scheme.{u}} (h : Y ⟶ AlgebraicGeometry.Proj (A.grading U))

omit hgen in
/-- **A degree-zero factor acts on the degree-one values of a graded map through the function it
divides to.** -/
theorem toFun_mul_zeroVeronese {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]
    (ψ : VeroneseSections (A.grading U) 1 L) (y : A.grading U (1 * 1)) (z : A.grading U 0)
    (yz : A.grading U ((1 + 0) * 1))
    (hyz : (yz : A.sectionRing U) = (y : A.sectionRing U) * (z : A.sectionRing U)) :
    ψ.toFun (1 + 0) yz = divUnit (ψ.toFun 0 (zeroVeronese (A.grading U) 1 z)) • ψ.toFun 1 y := by
  rw [ψ.map_mul 1 0 y (zeroVeronese (A.grading U) 1 z) yz hyz]
  have h3 := resTop_mulSections_smul_right L (ψ.toFun 1 y)
    (divUnit_resTop_top (ψ.toFun 0 (zeroVeronese (A.grading U) 1 z)))
  rwa [Stacks.AlgebraicGeometry.ProjTripleUnitSection.mulSections_unitGlobal_right,
    resTop_eq_self, resTop_eq_self] at h3

/-- `h` read as a morphism into the open `U_1`, which is all of `Proj A(U)`. -/
abbrev toDegreeOpenOne : Y ⟶ (degreeOpen (A.grading U) 1).toScheme :=
  Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.factorThroughDegreeOpenOne (A.grading U)
    (Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.degreeOpen_one_eq_top (A.grading U) hgen) h

/-- Composing `toDegreeOpenOne A U hgen h` with the inclusion of `U_1` into `Proj A(U)` recovers
`h`. -/
theorem toProj_toDegreeOpenOne : toProj (A.grading U) (toDegreeOpenOne A U hgen h) = h :=
  Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.toProj_factorThroughDegreeOpenOne _ _ h

/-- **The pullback `ψ_h` of the universal family along `h`.** -/
abbrev pulledUniversal :
    VeroneseSections (A.grading U) 1 ((Scheme.Modules.pullback (toDegreeOpenOne A U hgen h)).obj
      (Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents.universalTwist (A.grading U) 1)) :=
  pullbackSections (A.grading U) (universalVeroneseSections (A.grading U) 1)
    (toDegreeOpenOne A U hgen h)

/-- The degree-one values of `ψ_h` generate. -/
theorem iSup_nonvanishingOpen_pulledUniversal :
    ⨆ f : A.grading U 1, nonvanishingOpen Y _ (psiSection (A.grading U)
      (pulledUniversal A U hgen h) f) = ⊤ :=
  iSup_nonvanishingOpen_pullbackSections (A.grading U) _ _
    (iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top (A.grading U) 1)

/-- **The classified morphism of `ψ_h` is `h`**, read into `U_1`. -/
theorem classifyingHom_pulledUniversal :
    classifyingHom (A.grading U) one_pos (pulledUniversal A U hgen h)
        (iSup_nonvanishingOpen_pulledUniversal A U hgen h) = toDegreeOpenOne A U hgen h := by
  rw [classifyingHom_pullbackSections (A.grading U) one_pos _
    (iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top (A.grading U) 1),
    classifyingHom_universalVeroneseSections, Category.comp_id]

/-- `ψ_h` admits a compatible pair whose morphism is `h`, obtained by pulling back the universal
pair `(𝟙, id)`. -/
theorem exists_isCompatible_pulledUniversal :
    ∃ α, IsCompatible (A.grading U) (pulledUniversal A U hgen h)
      ⟨toDegreeOpenOne A U hgen h ≫ 𝟙 _, α⟩ :=
  ⟨_, isCompatible_pullbackSections (A.grading U) _ _
    (Stacks.AlgebraicGeometry.ProjUniversalCompatible.isCompatible_universalVeroneseSections
      (A.grading U) 1) _⟩

/-- `ψ_h` is unital. -/
theorem pulledUniversal_toFun_zero_one (a : A.grading U (0 * 1))
    (ha : (a : A.sectionRing U) = 1) :
    (pulledUniversal A U hgen h).toFun 0 a = unitGlobal _ :=
  Stacks.AlgebraicGeometry.ProjTripleUnitSection.toFun_zero_eq_unitGlobal (A.grading U) _
    (iSup_nonvanishingOpen_pulledUniversal A U hgen h) a ha

/-- **The degree-zero part of `ψ_h` is the pullback of functions along `h`**: a degree-zero element
`z` of `A(U)` goes to the unit section times the function `h^♯(z)`, where `z` is read as a
function on `Proj A(U)` through `Proj A(U) ⟶ Spec A(U)_0`. -/
theorem divUnit_pulledUniversal_zero (z : A.grading U 0) :
    divUnit ((pulledUniversal A U hgen h).toFun 0 (zeroVeronese (A.grading U) 1 z)) =
      (h ≫ AlgebraicGeometry.Proj.toSpecZero (A.grading U)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (A.grading U 0))).inv z) := by
  obtain ⟨α, hα⟩ := exists_isCompatible_pulledUniversal A U hgen h
  have hcomp := toProj_comp_toSpecZero (A.grading U) (pulledUniversal A U hgen h)
    (pulledUniversal_toFun_zero_one A U hgen h) one_pos
    (iSup_nonvanishingOpen_pulledUniversal A U hgen h) hα
  have hp : toProj (A.grading U) (toDegreeOpenOne A U hgen h ≫ 𝟙 _) = h := by
    rw [Category.comp_id, toProj_toDegreeOpenOne]
  rw [hp] at hcomp
  have hrhs : (Scheme.ΓSpecIso (CommRingCat.of (A.grading U 0))).inv ≫
      (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (degreeZeroHom (A.grading U)
        (pulledUniversal A U hgen h) (pulledUniversal_toFun_zero_one A U hgen h)))).appTop
      = CommRingCat.ofHom (degreeZeroHom (A.grading U) (pulledUniversal A U hgen h)
          (pulledUniversal_toFun_zero_one A U hgen h)) := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  have key := congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of (A.grading U 0))).inv ≫
    φ.appTop)) hcomp
  rw [hrhs] at key
  have := ConcreteCategory.congr_hom key z
  rw [← degreeZeroHom_apply (A.grading U) (pulledUniversal A U hgen h)
    (pulledUniversal_toFun_zero_one A U hgen h) z]
  exact this.symm

/-- Strictly equivalent graded maps have the same nonvanishing opens of degree-one values. -/
theorem nonvanishingOpen_psiSection_eq_of_sectionsEquiv {L L' : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y L] [Stacks.Ample.IsInvertibleModule Y L']
    {ψ : VeroneseSections (A.grading U) 1 L} {ψ' : VeroneseSections (A.grading U) 1 L'}
    (hψ : SectionsEquiv (A.grading U) ψ ψ') (f : A.grading U 1) :
    nonvanishingOpen Y L' (psiSection (A.grading U) ψ' f) =
      nonvanishingOpen Y L (psiSection (A.grading U) ψ f) := by
  obtain ⟨β, hβ⟩ := hψ
  rw [nonvanishingOpen_psiSection, nonvanishingOpen_psiSection]
  have e : ψ'.pow f.2 1 = (natTensorPowCongr β 1).hom.app ⊤ (ψ.pow f.2 1) := (hβ 1 _).symm
  rw [e]
  exact Opens.ext (Stacks.Ample.nonvanishingLocus_congr (natTensorPowCongr β 1) _)

/-- **The chart of a graded map strictly equivalent to `ψ_h` is `h`.** If `χ : A(U) ⟶ Γ_*(Y, M)`
is a graded map in the degreewise spelling of [Stacks, Tag 01NK] whose restriction to weight one
is strictly equivalent to `ψ_h`, then on the nonvanishing open of `χ(s)`, for `s` of degree one,
the chart of `χ` at `s` is the inclusion followed by `h`. -/
theorem chartToProj_eq_of_sectionsEquiv {M : Y.Modules} [Stacks.Ample.IsInvertibleModule Y M]
    (χ : GradedSections (A.grading U) M)
    (hχ : SectionsEquiv (A.grading U) (pulledUniversal A U hgen h)
      (Stacks.AlgebraicGeometry.ProjChartGradedVeronese.veroneseAt (A.grading U) χ 1))
    {s : A.sectionRing U} (hs : s ∈ A.grading U 1) :
    χ.chartToProj hs le_rfl one_pos =
      (nonvanishingOpen Y (natTensorPow M 1) (χ.toFun 1 ⟨s, hs⟩)).ι ≫ h := by
  let ψv := Stacks.AlgebraicGeometry.ProjChartGradedVeronese.veroneseAt (A.grading U) χ 1
  have hgenv : ⨆ f : A.grading U 1, nonvanishingOpen Y _ (psiSection (A.grading U) ψv f) = ⊤ := by
    rw [← iSup_nonvanishingOpen_pulledUniversal A U hgen h]
    exact iSup_congr fun f => nonvanishingOpen_psiSection_eq_of_sectionsEquiv A U hχ f
  have hcl : classifyingHom (A.grading U) one_pos ψv hgenv = toDegreeOpenOne A U hgen h :=
    (classifyingHom_eq_of_sectionsEquiv (A.grading U) one_pos
      (iSup_nonvanishingOpen_pulledUniversal A U hgen h) hgenv hχ).symm.trans
      (classifyingHom_pulledUniversal A U hgen h)
  let g : A.grading U 1 := ⟨s, hs⟩
  have hVV : nonvanishingOpen Y (natTensorPow M 1) (χ.toFun 1 ⟨s, hs⟩) ≤
      nonvanishingOpen Y (natTensorPow M 1) (psiSection (A.grading U) ψv g) := by
    refine le_of_eq ?_
    rw [nonvanishingOpen_psiSection]
    exact (Stacks.AlgebraicGeometry.ProjChartGradedVeronese.nonvanishingOpen_veroneseAt_pow_one
      (A.grading U) χ hs).symm
  have h1 := Stacks.AlgebraicGeometry.ProjChartGradedClassifying.ι_toProj_classifyingHom
    (A.grading U) one_pos ψv hgenv g
  rw [hcl, toProj_toDegreeOpenOne] at h1
  rw [← Y.homOfLE_ι hVV, Category.assoc, h1, homOfLE_chartToProj (A.grading U) ψv hs one_pos]
  unfold GradedSections.chartToProj Stacks.MorphismToProj.HomogeneousRatios.chartToProj
    Stacks.MorphismToProj.HomogeneousRatios.toSpecAway
  rw [Stacks.AlgebraicGeometry.ProjChartGradedVeronese.lift_veroneseAt_eq (A.grading U) χ hs
    one_pos le_rfl]

end Stacks.Tag01VMVeryAmple

end
