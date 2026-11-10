module

public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistEpi.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.ProjIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaClauseThree
public import StacksFrontier.AlgebraicGeometry.SectionPowerOverOpen.Basic
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.SectionRingProjGoodOpen.Basic
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Pointwise
public import StacksFrontier.AlgebraicGeometry.VeryAmpleGlue.TwistPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twist of a relatively ample module: Stacks Tag 01QI (2) over a base, in degree one

Let `f : X ⟶ S` be quasi-compact and quasi-separated and `L` an invertible `𝒪_X`-module ample
relative to `f`. [Stacks, Tag 01VJ] gives the canonical morphism
`r : X ⟶ Proj_S(⨁_{d ≥ 0} f_* L^{⊗ d})` (`Stacks.RelativeAmple.relativeAmpleProjHom`), which
[Stacks, Tag 01O9] equips with the map of graded algebras
`θ : r^*(⨁_d 𝒪(d)) ⟶ ⨁_d L^{⊗ d}` (`…GradedPowerMap.theta`). This file proves that `θ` is an
isomorphism in degree one, so that `r^* 𝒪(1) ≅ L`: the second claim of [Stacks, Tag 01QI],
relative to the base, in the degree conclusion (5) of [Stacks, Tag 0D4F] uses.

## Main results

* `Stacks.RelativeAmple.TwistIdentification.isIso_theta_one`: the absolute statement, for
  [Stacks, Tag 01NK]'s `θ` attached to a graded map `ψ : A → Γ_*(T, L)` whose morphism
  `r_{L, ψ}` lands in the open `W₁` of [Stacks, Tag 01MU].
* `Stacks.RelativeAmple.TwistIdentification.affineDatum_glued_mem_ratioLocus`: over an affine open
  of the base, the morphism of the induced datum lands in `W₁` (the first claim of
  [Stacks, Tag 01QI], from sections of consecutive degrees, [Stacks, Tag 01Q3]).
* `Stacks.RelativeAmple.TwistIdentification.isIso_theta_one_directImagePowerMap`: **`θ` is an
  isomorphism in degree one**, for `L` ample relative to `f`.
* `Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistIso`: **`r^* 𝒪(1) ≅ L`.**

## The proof

As in the source. In the absolute case both `r^* 𝒪(1)` and `L|_{U(ψ)}` are invertible, the first
because `𝒪(1)` is invertible on `W₁`, so it suffices that `θ` be an epimorphism. Near a point `t`
with `r(t) ∈ D₊(p q)`, `deg p = deg q + 1`, the section `p / q` of `𝒪(1)` satisfies
`q · (p / q) = p`, so by the multiplicativity of `θ` its image satisfies
`ψ(q) · θ(p / q) = ψ(p)`; as `ψ(p)` does not vanish at `t`, neither does `θ(p / q)`
(`mem_nonvanishingLocusOn_of_localMul`). The relative statement is local on `U(ψ)`, and over the
piece lying over an affine open of the base clause (3) of [Stacks, Tag 01O9] identifies `θ` with
the absolute one for the induced datum.

## References

* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)

universe u

namespace Stacks.RelativeAmple.TwistIdentification

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

section Product

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The product of the tensor powers, as an isomorphism out of the monoidal tensor product. -/
def mulIso (i j : ℤ) :
    (tensorPowerModule X L i ⊗ tensorPowerModule X L j : X.Modules) ≅
      tensorPowerModule X L (i + j) :=
  (Stacks.SectionTensorFormula.tensorSheafIsoTensorObj X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _ _).symm ≪≫
    Stacks.SheafOfModules.TensorPower.coherentMulIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L i j

/-- The product of two local sections of the tensor powers is their tensor product, read through
`mulIso`. -/
theorem localMul_eq_mulIso {i j : ℤ} {W : X.Opens} (s : Γ(tensorPowerModule X L i, W))
    (t : Γ(tensorPowerModule X L j, W)) :
    Stacks.TensorPowerDivision.localMul L s t =
      (mulIso L i j).hom.app W (Stacks.SectionTensorFormula.tensorSection _ _ s t) := by
  have e := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
    (Stacks.SectionTensorFormula.tensorSheafIsoTensorObj X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (tensorPowerModule X L i)
      (tensorPowerModule X L j)).symm W
    (Stacks.SheafOfModules.tensorSectionsAt X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (op W)
      (tensorPowerModule X L i) (tensorPowerModule X L j) s t)
  exact (congrArg (fun z => (Stacks.SheafOfModules.TensorPower.coherentMulIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L i j).hom.val.app (op W) z)
    e).symm

/-- **A product of sections of tensor powers that does not vanish at a point has factors that do
not vanish there**, [Stacks, Tag 01CY]: the product is the tensor product of the two sections read
through the multiplication isomorphism. -/
theorem mem_nonvanishingLocusOn_of_localMul {i j : ℤ} {W : X.Opens}
    (s : Γ(tensorPowerModule X L i, W)) (t : Γ(tensorPowerModule X L j, W)) {y : X}
    (h : y ∈ nonvanishingLocusOn (tensorPowerModule X L (i + j)) W
      (Stacks.TensorPowerDivision.localMul L s t)) :
    y ∈ nonvanishingLocusOn (tensorPowerModule X L i) W s ∧
      y ∈ nonvanishingLocusOn (tensorPowerModule X L j) W t := by
  rwa [localMul_eq_mulIso,
    Stacks.SectionPowerOverOpen.mem_nonvanishingLocusOn_congr_iff (mulIso L i j) W _ h.1,
    Stacks.SectionPowerOverOpen.nonvanishingLocusOn_tensorSection] at h

/-- `mem_nonvanishingLocusOn_of_localMul` for a section equal to the product up to a degree
identification. -/
theorem mem_nonvanishingLocusOn_of_heq_localMul {i j n : ℤ} (hn : i + j = n) {W : X.Opens}
    (s : Γ(tensorPowerModule X L i, W)) (t : Γ(tensorPowerModule X L j, W))
    (w : Γ(tensorPowerModule X L n, W)) (hw : HEq (Stacks.TensorPowerDivision.localMul L s t) w)
    {y : X} (h : y ∈ nonvanishingLocusOn (tensorPowerModule X L n) W w) :
    y ∈ nonvanishingLocusOn (tensorPowerModule X L j) W t := by
  subst hn
  exact (mem_nonvanishingLocusOn_of_localMul L s t (eq_of_heq hw ▸ h)).2

end Product

/-! ### Nonvanishing on an open subscheme -/

/-- **A section over the image of an open of an open subscheme, nonvanishing at the image of a
point, is nonvanishing at the point as a section of the restriction.** -/
theorem mem_nonvanishingLocusOn_restrict_of {T : Scheme.{u}} (U : T.Opens) (N : T.Modules)
    (O : U.toScheme.Opens) (s : Γ(N, U.ι ''ᵁ O)) {z : U.toScheme} (hz : z ∈ O)
    (h : U.ι.base z ∈ nonvanishingLocusOn N (U.ι ''ᵁ O) s) :
    z ∈ nonvanishingLocusOn (N.restrict U.ι) O s := by
  have h2 := Stacks.VeryAmpleGlue.mem_nonvanishingLocusOn_restrict U N (U.ι ''ᵁ O) s z h
  have hle : O ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ O) := (U.ι.preimage_image_eq O).ge
  have h3 := (Set.ext_iff.mp (Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res
    (N.restrict U.ι) hle _) z).mpr ⟨hz, h2⟩
  have e : ((N.restrict U.ι).presheaf.map (homOfLE hle).op).hom
      ((N.presheaf.map (homOfLE (U.ι.image_preimage_le (U.ι ''ᵁ O))).op).hom s) = s :=
    (Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.map_map N
      (homOfLE (U.ι.image_preimage_le (U.ι ''ᵁ O))).op
      (U.ι.opensFunctor.map (homOfLE hle)).op (𝟙 _) s).trans
      (Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.map_id_apply N (𝟙 _) s)
  rwa [e] at h3

/-! ### The absolute case: Tag 01NK's `θ` in degree one -/

section Absolute

open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGrading degreeSection)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intValue)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.TwistRigidity (degreeSectionOn)

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {σ : Type u} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- A point of `D₊(p q)` does not contain `q`. -/
theorem right_notMem_of_mem_basicOpen {p q : A} (w : AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q)) :
    q ∉ w.1.asHomogeneousIdeal := fun hq =>
  w.2 (w.1.asHomogeneousIdeal.toIdeal.mul_mem_left p hq)

/-- **The section `p / q` of `𝒪(1)` over `D₊(p q)`**, for `p` homogeneous of degree `k + 1` and
`q` of degree `k`. -/
def quotientSection {k : ℕ} {p q : A} (hp : p ∈ 𝒜 (k + 1)) (hq : q ∈ 𝒜 k) :
    (twistingSheaf 𝒜 1).val.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))) :=
  Stacks.AlgebraicGeometry.ProjTwistEpi.fractionSection 𝒜 1
    (show p ∈ AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading (S := A) 𝒜
        ((k + 1 : ℕ) : ℤ) from
      Stacks.AlgebraicGeometry.ProjTrivialization.mem_integerGrading_natCast 𝒜 hp)
    hq right_notMem_of_mem_basicOpen

/-- **`q · (p / q) = p`** on `D₊(p q)`, as sections of the twists. -/
theorem absoluteTwistProduct_quotientSection {k : ℕ} {p q : A} (hp : p ∈ 𝒜 (k + 1))
    (hq : q ∈ 𝒜 k) :
    Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct 𝒜 (k : ℤ) 1
        (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))
        (degreeSectionOn 𝒜 k hq (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q)))
        (quotientSection hp hq) =
      degreeSectionOn 𝒜 (k + 1) hp (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q)) :=
  Subtype.ext (funext fun y =>
    (Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn_mul_apply 𝒜 k hq 1 _ _
      right_notMem_of_mem_basicOpen (fun _ => rfl) y).trans
    (Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn_apply 𝒜 (k + 1) hp _ y).symm)

variable {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections 𝒜 L)

/-- **`θ` in pushforward form on a restricted homogeneous section**: clause (2) of
[Stacks, Tag 01NK], restricted to an open. -/
theorem pushTheta_degreeSectionOn (n : ℕ) {c : A} (hc : c ∈ 𝒜 n)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    (pushTheta 𝒜 ψ (n : ℤ)).app U (degreeSectionOn 𝒜 n hc U) =
      Stacks.TensorPowerTrivialize.resTop (tensorPowerModule T L (n : ℤ)) (intValue ψ n ⟨c, hc⟩)
        (ψ.coveringOpen.ι ''ᵁ (ψ.glued ⁻¹ᵁ U)) := by
  have h := Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map (pushTheta 𝒜 ψ (n : ℤ))
    (le_top : U ≤ ⊤) (degreeSection 𝒜 n ⟨c, hc⟩)
  refine h.symm.trans ?_
  rw [Stacks.AlgebraicGeometry.ProjChartGradedTriple.pushTheta_app_top_degreeSection]
  refine (Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.pushforward_restrict_map
    ψ.coveringOpen.ι ψ.glued (tensorPowerModule T L (n : ℤ)) (homOfLE (le_top : U ≤ ⊤)) _).trans ?_
  exact Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.map_map
    (tensorPowerModule T L (n : ℤ)) _ _ _ _

/-- **`ψ(q) · θ(p / q) = ψ(p)`** over the preimage of `D₊(p q)`: the multiplicativity of `θ`. -/
theorem localMul_pushTheta_quotientSection {k : ℕ} {p q : A} (hp : p ∈ 𝒜 (k + 1))
    (hq : q ∈ 𝒜 k) :
    Stacks.TensorPowerDivision.localMul L
        (Stacks.TensorPowerTrivialize.resTop (tensorPowerModule T L (k : ℤ)) (intValue ψ k ⟨q, hq⟩)
          (ψ.chartOpen (p * q)))
        ((pushTheta 𝒜 ψ 1).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))
          (quotientSection hp hq)) =
      Stacks.TensorPowerTrivialize.resTop (tensorPowerModule T L ((k + 1 : ℕ) : ℤ))
        (intValue ψ (k + 1) ⟨p, hp⟩) (ψ.chartOpen (p * q)) := by
  have h1 := pushTheta_mul 𝒜 ψ (k : ℤ) 1 (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q)))
    (degreeSectionOn 𝒜 k hq (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))) (quotientSection hp hq)
  have h2 := (Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.absoluteTwistProduct_eq_mul
    𝒜 (k : ℤ) 1 (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))
    (degreeSectionOn 𝒜 k hq (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q)))
    (quotientSection hp hq)).symm.trans (absoluteTwistProduct_quotientSection hp hq)
  have h3 : (pushTheta 𝒜 ψ ((k + 1 : ℕ) : ℤ)).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))
      (degreeSectionOn 𝒜 (k + 1) hp (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))) =
      Stacks.TensorPowerDivision.localMul L
        ((pushTheta 𝒜 ψ (k : ℤ)).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))
          (degreeSectionOn 𝒜 k hq (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))))
        ((pushTheta 𝒜 ψ 1).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))
          (quotientSection hp hq)) := by
    rwa [← h2]
  refine Eq.trans ?_ (h3.symm.trans (pushTheta_degreeSectionOn ψ (k + 1) hp _))
  exact congrArg (fun z => Stacks.TensorPowerDivision.localMul L z
    ((pushTheta 𝒜 ψ 1).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q)) (quotientSection hp hq)))
    (pushTheta_degreeSectionOn ψ k hq _).symm

/-- The restriction of a tensor power of `L` to `U(ψ)` is invertible. -/
instance isInvertibleModule_laurentPiece (n : ℤ) :
    Stacks.Ample.IsInvertibleModule ψ.coveringOpen.toScheme ((laurentRestrict 𝒜 ψ).piece n) :=
  Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    (Stacks.AmplePullbackPart1.restrictIsoPullback ψ.coveringOpen
      (tensorPowerModule T L n)).symm

/-- **[Stacks, Tag 01QI] (2) in degree one, for Tag 01NK's `θ`.** If `r_{L, ψ}` maps `U(ψ)` into
the open `W₁` of [Stacks, Tag 01MU] — the union of the `D₊(p q)` with `deg p = deg q + 1` — then
`θ : r_{L, ψ}^* 𝒪(1) ⟶ L|_{U(ψ)}` is an isomorphism.

`r_{L, ψ}^* 𝒪(1)` is invertible, `𝒪(1)` being invertible on `W₁`
(`Stacks.AlgebraicGeometry.GoodOpenClose.isInvertible_pullback_twistingSheaf_of_le_ratioLocus`),
and so is `L|_{U(ψ)}`; so it suffices that `θ` be an epimorphism. Near a point `t` with
`r(t) ∈ D₊(p q)` the section `p / q` of `𝒪(1)` pulls back to a section whose image `θ(p / q)`
satisfies `ψ(q) · θ(p / q) = ψ(p)` by the multiplicativity of `θ`
(`localMul_pushTheta_quotientSection`); `ψ(p)` does not vanish at `t`, hence neither does
`θ(p / q)`. -/
theorem isIso_theta_one
    (hR : ∀ t : ψ.coveringOpen.toScheme,
      ψ.glued.base t ∈ Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒜 1) :
    IsIso ((theta 𝒜 ψ).app 1) := by
  have hepi : Epi ((theta 𝒜 ψ).app 1) := by
    refine Stacks.VeryAmpleGlue.epi_of_forall_mem_nonvanishingLocusOn _ fun t => ?_
    obtain ⟨k, p, q, hp, hq, hpt, hqt⟩ :=
      (Stacks.AlgebraicGeometry.ProjShared.mem_ratioLocus_iff 𝒜 1 _).mp (hR t)
    have htD : t ∈ ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q) := by
      change p * q ∉ (ψ.glued.base t).asHomogeneousIdeal
      exact fun hpq => ((ψ.glued.base t).isPrime.mem_or_mem hpq).elim hpt hqt
    refine ⟨ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q),
      Stacks.RingedSpace.pullbackUnit ψ.glued.toLRSHom.toShHom (twistM 𝒜 1)
        (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))) (quotientSection hp hq), ?_⟩
    have h1 : Scheme.Modules.Hom.app ((theta 𝒜 ψ).app 1)
        (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))
        (Stacks.RingedSpace.pullbackUnit ψ.glued.toLRSHom.toShHom (twistM 𝒜 1)
          (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))) (quotientSection hp hq)) =
        (pushTheta 𝒜 ψ 1).app (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q))
          (quotientSection hp hq) :=
      transposeAppHom_pullbackUnit ψ.glued.toLRSHom.toShHom (pushThetaHom 𝒜 ψ) 1
        (AlgebraicGeometry.Proj.basicOpen 𝒜 (p * q)) (quotientSection hp hq)
    rw [h1]
    refine mem_nonvanishingLocusOn_restrict_of ψ.coveringOpen (tensorPowerModule T L 1) _ _ htD ?_
    have hpe : ψ.coveringOpen.ι.base t ∈ nonvanishingLocusOn
        (tensorPowerModule T L ((k + 1 : ℕ) : ℤ)) (ψ.chartOpen (p * q))
        (Stacks.TensorPowerTrivialize.resTop (tensorPowerModule T L ((k + 1 : ℕ) : ℤ))
          (intValue ψ (k + 1) ⟨p, hp⟩) (ψ.chartOpen (p * q))) := by
      rw [Stacks.TensorPowerTrivialize.resTop,
        Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res,
        Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top]
      refine ⟨⟨t, htD, rfl⟩, ?_⟩
      have hp' : t ∈ ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 p := hpt
      rwa [ψ.preimage_basicOpen_glued hp (Nat.succ_pos k),
        ← Stacks.AlgebraicGeometry.ProjChartGradedDivision.nonvanishingOpen_intValue ψ (k + 1)
          ⟨p, hp⟩] at hp'
    exact mem_nonvanishingLocusOn_of_heq_localMul L (by ring) _ _ _
      (heq_of_eq (localMul_pushTheta_quotientSection ψ hp hq)) hpe
  let RL := Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒜 1
  have hrange : Set.range ψ.glued.base ⊆ Set.range RL.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hR t
  let g' : ψ.coveringOpen.toScheme ⟶ RL.toScheme := IsOpenImmersion.lift RL.ι ψ.glued hrange
  have hg' : g' ≫ RL.ι = ψ.glued := IsOpenImmersion.lift_fac RL.ι ψ.glued hrange
  have h0 : Stacks.Ample.IsInvertibleModule RL.toScheme
      ((Scheme.Modules.pullback RL.ι).obj (twistM 𝒜 1)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (Stacks.AlgebraicGeometry.GoodOpenClose.isInvertible_pullback_twistingSheaf_of_le_ratioLocus
        𝒜 (d := 1) (le_refl RL) 1)
  have h1 : Stacks.Ample.IsInvertibleModule ψ.coveringOpen.toScheme
      ((Scheme.Modules.pullback RL.ι ⋙ Scheme.Modules.pullback g').obj (twistM 𝒜 1)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback g' _
  have h2 : Stacks.Ample.IsInvertibleModule ψ.coveringOpen.toScheme
      ((Scheme.Modules.pullback ψ.glued).obj (twistM 𝒜 1)) :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _
      ((Scheme.Modules.pullbackComp g' RL.ι).app (twistM 𝒜 1) ≪≫
        (Scheme.Modules.pullbackCongr hg').app (twistM 𝒜 1))
  exact @Stacks.SheafOfModules.isIso_of_epi_of_isInvertible
    ψ.coveringOpen.toScheme.toRingedSpace _ _ ((theta 𝒜 ψ).app 1) hepi
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr h2)
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr inferInstance)

end Absolute

/-! ### Consecutive degrees for an ample module -/

section Consecutive

open Stacks.GradedSections (powSections)
open Stacks.AmpleFiniteAvoidance (nvLocus)

/-- **For `M` ample every point has nonvanishing sections of two consecutive positive degrees.**
This is where ampleness is spent, through the eventual generation of the tensor powers by global
sections (the first half of clause (7) of [Stacks, Tag 01Q3]). -/
theorem exists_consecutive_mem_nvLocus {Y : Scheme.{u}} (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] (hM : Stacks.Ample.IsAmple Y M) (y : Y) :
    ∃ (e : ℕ) (a : powSections M (e + 1 + 1)) (b : powSections M (e + 1)),
      y ∈ Stacks.AmpleFiniteAvoidance.nvLocus M a ∧
        y ∈ Stacks.AmpleFiniteAvoidance.nvLocus M b := by
  obtain ⟨n₀, hgen⟩ := Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple M hM
  obtain ⟨e, he⟩ : ∃ e : ℕ, n₀ ≤ ((e + 1 : ℕ) : ℤ) :=
    ⟨n₀.toNat, by have := Int.self_le_toNat n₀; push_cast; omega⟩
  obtain ⟨a, ha⟩ := Stacks.SectionRingProjGoodOpen.exists_powSections_mem_nvLocus_of_isFinGen M
    (n := e + 1 + 1) (hgen ((e + 1 + 1 : ℕ) : ℤ) (by push_cast at he ⊢; omega)) y
  obtain ⟨b, hb⟩ := Stacks.SectionRingProjGoodOpen.exists_powSections_mem_nvLocus_of_isFinGen M
    (n := e + 1) (hgen ((e + 1 : ℕ) : ℤ) he) y
  exact ⟨e, a, b, ha, hb⟩

end Consecutive

/-! ### The relative case -/

section Relative

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)
open Stacks.SectionRingGluedComparison (canonicalSections)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)

/-- **For `M` ample, the morphism of [Stacks, Tag 01NK] attached to the canonical datum of
`Γ_*(Y, M)`, read along a graded ring isomorphism, maps into the open `W₁` of
[Stacks, Tag 01MU].** At every point there are sections of consecutive degrees not vanishing there
(`exists_consecutive_mem_nvLocus`), and clause (1) of [Stacks, Tag 01NK] places the image of the
point in the standard opens of their preimages. -/
theorem comap_glued_mem_ratioLocus {Y : Scheme.{u}} (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] (hM : Stacks.Ample.IsAmple Y M)
    {σ B : Type u} [CommRing B] [SetLike σ B] [AddSubgroupClass σ B] {ℬ : ℕ → σ} [GradedRing ℬ]
    (φ : ℬ →+*ᵍ grading M) (φ' : grading M →+*ᵍ ℬ) (h : φ.comp φ' = GradedRingHom.id _)
    (t : (comap φ (canonicalSections M)).coveringOpen.toScheme) :
    (comap φ (canonicalSections M)).glued.base t ∈
      Stacks.AlgebraicGeometry.ProjShared.ratioLocus ℬ 1 := by
  obtain ⟨e, a, b, ha, hb⟩ := exists_consecutive_mem_nvLocus M hM
    ((comap φ (canonicalSections M)).coveringOpen.ι.base t)
  have hmem : ∀ (n : ℕ) (c : Stacks.GradedSections.powSections M n), 0 < n →
      (comap φ (canonicalSections M)).coveringOpen.ι.base t ∈
        Stacks.AmpleFiniteAvoidance.nvLocus M c →
      ∃ x : B, x ∈ ℬ n ∧ t ∈ (comap φ (canonicalSections M)).glued ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen ℬ x := by
    intro n c hn hc
    refine ⟨φ'.gradedAddHom n ⟨_, Stacks.ExternalGrading.of_mem_summand n c⟩, (φ'.gradedAddHom n
      ⟨_, Stacks.ExternalGrading.of_mem_summand n c⟩).2, ?_⟩
    rw [(comap φ (canonicalSections M)).preimage_basicOpen_glued
      (φ'.gradedAddHom n ⟨_, Stacks.ExternalGrading.of_mem_summand n c⟩).2 hn]
    have h1 : (comap φ (canonicalSections M)).toFun n
        (φ'.gradedAddHom n ⟨_, Stacks.ExternalGrading.of_mem_summand n c⟩) =
        (canonicalSections M).toFun n ⟨_, Stacks.ExternalGrading.of_mem_summand n c⟩ :=
      (Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap_toFun _ _ n _).trans
        (congrArg _ (Subtype.ext congr($h (DirectSum.of _ n c))))
    change (comap φ (canonicalSections M)).coveringOpen.ι.base t ∈
      Stacks.NonvanishingOpen.nonvanishingOpen Y (Stacks.TensorPowers.natTensorPow M n) _
    rw [h1, Stacks.SectionRingGluedComparison.nonvanishingOpen_canonicalSections_of]
    exact hc
  obtain ⟨p, hp, hpt⟩ := hmem (e + 1 + 1) a (by omega) ha
  obtain ⟨q, hq, hqt⟩ := hmem (e + 1) b (by omega) hb
  exact (Stacks.AlgebraicGeometry.ProjShared.mem_ratioLocus_iff ℬ 1 _).mpr
    ⟨e + 1, p, q, hp, hq, hpt, hqt⟩

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  [QuasiCompact f] [QuasiSeparated f]

/-- **Over an affine open `V` of the base, the morphism of [Stacks, Tag 01NK] for the induced datum
maps into the open `W₁` of [Stacks, Tag 01MU]**, for `L` ample relative to `f`. -/
theorem affineDatum_glued_mem_ratioLocus (hL : IsRelativelyAmple f L) {V : S.Opens}
    (hV : IsAffineOpen V) :
    ∀ t : ((directImagePowerMap f L).affineDatum V).coveringOpen.toScheme,
      ((directImagePowerMap f L).affineDatum V).glued.base t ∈
        Stacks.AlgebraicGeometry.ProjShared.ratioLocus ((directImageAlgebra f L).grading V) 1 := by
  rw [affineDatum_eq_comap]
  exact comap_glued_mem_ratioLocus (restrictedModule f L V) (isAmple_restrictedModule hL hV)
    (sectionGradedHom f L V) (sectionGradedHomInv f L V) (sectionGradedHom_comp f L V)

/-- A morphism conjugate to an isomorphism by two isomorphisms is an isomorphism. -/
theorem isIso_of_inv_comp_comp_hom_eq {C : Type*} [Category C] {W X' Y Z : C} (a : X' ≅ W)
    (m : X' ⟶ Y) (b : Y ≅ Z) (t : W ⟶ Z) (h : a.inv ≫ m ≫ b.hom = t) (ht : IsIso t) : IsIso m := by
  have e : m = a.hom ≫ t ≫ b.inv := by
    rw [← h]
    simp
  rw [e]
  infer_instance

/-- **[Stacks, Tag 01QI] (2) over a base, in degree one.** For `L` ample relative to a
quasi-compact quasi-separated `f`, the degree-one component of the map `θ` of [Stacks, Tag 01O9]
for the adjunction map `ψ : f^*(⨁_{d ≥ 0} f_* L^{⊗ d}) ⟶ ⨁_{d ≥ 0} L^{⊗ d}` is an isomorphism
`r_{L, ψ}^* 𝒪(1) ≅ L|_{U(ψ)}`.

Being an isomorphism is local, and the pieces of `U(ψ)` over the affine opens `V` of the base
cover it. Over such a piece, clause (3) of [Stacks, Tag 01O9]
(`…GradedPowerMap.theta_clauseThree_app`) identifies `θ` with [Stacks, Tag 01NK]'s `θ` for the
induced datum over `V`, which is an isomorphism in degree one by `isIso_theta_one`, its morphism
landing in `W₁` by `affineDatum_glued_mem_ratioLocus`. -/
theorem isIso_theta_one_directImagePowerMap (hL : IsRelativelyAmple f L) :
    IsIso ((directImagePowerMap f L).theta.app 1) := by
  have : ∀ V : S.affineOpens, IsOpenImmersion
      ((directImagePowerMap f L).affineDatumInclusion V) := fun V => by
    unfold GradedPowerMap.affineDatumInclusion
    infer_instance
  refine Scheme.Modules.isIso_of_isIso_restrictFunctor_map _
    (fun V : S.affineOpens => (directImagePowerMap f L).affineDatumInclusion V)
    (fun z => ?_) (fun V => ?_)
  · obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f.base ((directImagePowerMap f L).coveringOpen.ι.base z))) isOpen_univ
    have hz : z ∈ (directImagePowerMap f L).toBase ⁻¹ᵁ V := hzV
    refine ⟨⟨V, hV⟩, ((directImagePowerMap f L).pieceIso V hV).hom.base ⟨z, hz⟩, ?_⟩
    change (((directImagePowerMap f L).pieceIso V hV).hom ≫
      ((directImagePowerMap f L).pieceIso V hV).inv ≫
      ((directImagePowerMap f L).toBase ⁻¹ᵁ V).ι).base ⟨z, hz⟩ = z
    rw [Iso.hom_inv_id_assoc]
    rfl
  · have key := (directImagePowerMap f L).theta_clauseThree_app V
      ((directImagePowerMap f L).affineDatumInclusion V)
      ((directImagePowerMap f L).affineDatumInclusion_ι V) 1
    have h0 : IsIso ((Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.theta
        ((directImageAlgebra f L).grading V.1)
          ((directImagePowerMap f L).affineDatum V.1)).app 1) :=
      isIso_theta_one _ (affineDatum_glued_mem_ratioLocus f L hL V.2)
    have h3 : IsIso ((Scheme.Modules.pullback
        ((directImagePowerMap f L).affineDatumInclusion V)).map
        ((directImagePowerMap f L).theta.app 1)) :=
      isIso_of_inv_comp_comp_hom_eq _ _ _ _ key h0
    exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback
      ((directImagePowerMap f L).affineDatumInclusion V))
        ((directImagePowerMap f L).theta.app 1)).mpr h3

/-- **[Stacks, Tag 01QI] (2) over a base, in degree one: `r^* 𝒪(1) ≅ L`.** For `L` ample relative
to a quasi-compact quasi-separated `f`, the canonical morphism
`r : X ⟶ Proj_S(⨁_{d ≥ 0} f_* L^{⊗ d})` of [Stacks, Tag 01VJ] pulls the first Serre twist back to
`L`, through the map `θ` of [Stacks, Tag 01O9] in degree one
(`isIso_theta_one_directImagePowerMap`). -/
@[ega "II 4.6.3" "(4.6.3.1) for n = 1"]
def relativeAmpleTwistIso (hL : IsRelativelyAmple f L) :
    (Scheme.Modules.pullback (relativeAmpleProjHom f L hL)).obj
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist (directImageAlgebra f L) 1) ≅ L := by
  have hθ := isIso_theta_one_directImagePowerMap f L hL
  let Z := (directImagePowerMap f L).coveringOpen
  let r := (directImagePowerMap f L).globalMorphism
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (directImageAlgebra f L))
  let j : X ⟶ Z.toScheme :=
    X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImagePowerMap hL).symm).hom
  have hj : j ≫ Z.ι = 𝟙 X := by
    simp only [j, Z, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]
  have hr : relativeAmpleProjHom f L hL = j ≫ r := by
    simp only [relativeAmpleProjHom, j, r, Category.assoc]
  exact (Scheme.Modules.pullbackCongr hr).app _ ≪≫
    ((Scheme.Modules.pullbackComp j r).app _).symm ≪≫
    (Scheme.Modules.pullback j).mapIso
      (@asIso _ _ _ _ ((directImagePowerMap f L).theta.app 1) hθ) ≪≫
    (Scheme.Modules.pullback j).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback Z.ι).app (tensorPowerModule X L 1)) ≪≫
    (Scheme.Modules.pullbackComp j Z.ι).app _ ≪≫
    (Scheme.Modules.pullbackCongr hj).app _ ≪≫
    (Scheme.Modules.pullbackId X).app _ ≪≫
    (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).symm ≪≫ λ_ L

end Relative

end Stacks.RelativeAmple.TwistIdentification
