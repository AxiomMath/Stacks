module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaBuild
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.GluedComparison
public import StacksFrontier.AlgebraicGeometry.SectionRingProjGoodOpen.Basic
public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Restriction
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleReduction.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.Theta
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ThetaIso
public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Multiplicative
public import StacksFrontier.AlgebraicGeometry.VeryAmpleGlue.TwistPullback

/-!
# The pulled-back twists in Situation Stacks Tag 01QH

Situation Stacks Tag 01QH: `X` is a scheme, `L` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, L)` the graded section ring of Stacks Tag 01CV, `Y = Proj S`, and `f : X ⟶ Y` the
canonical morphism of Stacks Tag 01PZ. **The situation also carries a map of `ℤ`-graded
`𝒪_X`-algebras `⨁_n f^*𝒪_Y(n) ⟶ ⨁_n L^{⊗ n}`**, namely the `θ` of Constructions, Lemma
Stacks Tag 01NK for the datum `ψ =` the identity of `Γ_*(X, L)`: that datum is
`Stacks.SectionRingGluedComparison.canonicalSections L`, its morphism
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued` is `f`
(`Stacks.SectionRingGluedComparison.ι_comp_projHomOfIsAmple_eq_glued`), and `θ` is
`Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.theta`, whose degree-`n` component is a
morphism

`θ_n : f^*𝒪_Y(n) ⟶ L^{⊗ n}|_{U(ψ)}`

of `𝒪`-modules on `U(ψ) = ⋃_a X_a`, by `Stacks.Conormal.gradedPullback_piece` and
`Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.laurentRestrict_piece`, both `rfl`.

The second claim of Stacks Tag 01QI is that these `θ_n` are all isomorphisms, and this file
proves it **in every integer degree** (`isIso_projTheta_app`). Two inputs meet:

* **both the source and the target of `θ_n` are invertible modules, for every `n : ℤ`** — the
  source side is where the *first* claim of Stacks Tag 01QI is spent, which is why the source
  states the two claims together: `𝒪_Y(n)` is invertible only after restriction to the good open
  `W₁` of Stacks Tag 01MU, and what puts `f^*𝒪_Y(n)` in reach is exactly that `f` maps `X` into
  `W₁`. An epimorphism between invertible modules is an isomorphism, so the claim reduces to local
  surjectivity of `θ_n`; and
* **a degree-`n` fraction at every point whose value under `θ_n` vanishes nowhere on its chart.**
  For two homogeneous `c ∈ S_p`, `b ∈ S_q` with `p = q + n`, neither vanishing at a given point,
  the fraction `c² / cb` has degree `2 p - (p + q) = n` and a numerator that vanishes nowhere on
  `X_{cb} ⊆ X_c`. Ampleness supplies `c` and `b` at every point for *every* integer `n`, negative
  included: both `p` and `q` are free to be as large as the `n₀` of clause (7) of Stacks Tag 01Q3
  demands, only their difference being prescribed.

## Main definitions

* `Stacks.SectionRingProjTwistIso.gluedToGood`: **the factorisation of `f` through `W₁`**, the
  morphism `U(ψ) ⟶ W₁` with `gluedToGood ≫ W₁.ι = f`.

## Main results

* `Stacks.SectionRingProjTwistIso.glued_preimage_whereInvertible`: the first claim of Stacks Tag
  01QI read for the Stacks Tag 01NK datum — `f ⁻¹ᵁ W₁ = ⊤` on `U(ψ)`.
* `Stacks.SectionRingProjTwistIso.isInvertibleModule_restrict_whereInvertible`: `𝒪_Y(n)|_{W₁}` is
  invertible, for every `n : ℤ`. This is the invertibility half of Stacks Tag 01MU's goodness of
  `W₁`, read at `d = 1`.
* `Stacks.SectionRingProjTwistIso.isInvertibleModule_pullback_twistM`: **`f^*𝒪_Y(n)` is
  invertible**, for every `n : ℤ`.
* `Stacks.SectionRingProjTwistIso.isInvertibleModule_laurentPiece`: **`L^{⊗ n}|_{U(ψ)}` is
  invertible**, for every `n : ℤ`.
* `Stacks.SectionRingProjTwistIso.isIso_theta_app_of_epi`: **`θ_n` is an isomorphism as soon as
  it is an epimorphism**, for every `n : ℤ`.
* `Stacks.SectionRingProjTwistIso.epi_theta_app_of_forall_chartSection`: **`θ_n` is an
  epimorphism once every point lies on a chart carrying a degree-`n` fraction whose chart value
  vanishes nowhere on it**, for an arbitrary graded map `ψ` and an arbitrary `n : ℤ`.
* `Stacks.SectionRingProjTwistIso.exists_powSections_mem_nvLocus`: for `L` ample, every point has
  a homogeneous element of `S_n` not vanishing there, for every `n` above some `n₀`.
* `Stacks.SectionRingProjTwistIso.exists_chartSection_nonvanishing`: **for `L` ample, the
  fraction `c² / cb` at every point and in every integer degree.**
* `Stacks.SectionRingProjTwistIso.epi_projTheta_app_int`: **`θ_n` is an epimorphism for every
  `n : ℤ`.**
* `Stacks.SectionRingProjTwistIso.isIso_projTheta_app`: **the second claim of Stacks Tag 01QI —
  `θ_n` is an isomorphism for every `n : ℤ`.**
* `Stacks.SectionRingProjTwistIso.epi_projTheta_app`,
  `Stacks.SectionRingProjTwistIso.isIso_projTheta_app_of_forall_nvLocus` and
  `Stacks.SectionRingProjTwistIso.exists_isIso_projTheta_app`: the same conclusion in a degree
  `n ≥ 0` in which `L ^⊗ n` is globally generated, by the shorter global-section route, which
  needs no fraction but reaches only the degrees above some `n₀`.

## Implementation notes

**The factorisation is Mathlib's `AlgebraicGeometry.IsOpenImmersion.lift`.** `f ⁻¹ᵁ W₁ = ⊤` says
that the range of `f` lies in the range of the open immersion `W₁.ι`, which is the hypothesis
that lemma consumes, and `AlgebraicGeometry.IsOpenImmersion.lift_fac` is the factorisation
identity. No uniqueness is needed below.

**Invertibility travels along the factorisation and not along `f` itself.** `𝒪_Y(n)` is *not*
invertible on `Y`; `Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_whereInvertible` makes it
invertible on `W₁`, `Stacks.InvertiblePullback.isInvertibleModule_pullback` (Stacks Tag 0B8L)
carries that along `gluedToGood`, and `AlgebraicGeometry.Scheme.Modules.pullbackComp` together
with `AlgebraicGeometry.Scheme.Modules.pullbackCongr` identifies the iterated pullback with the
pullback along `f`. The same two-step pattern is
`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.isInvertibleModule_pullbackTwist` for the
degree open `U_d` of Stacks Tag 01N8.

**The degree index of goodness is `1 * n`.**
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.IsGoodOpen` is stated for the `d`-divisible twists
`𝒪(d * n)`, so at `d = 1` the twist comes out as `𝒪((1 : ℕ) * n)`; `Nat.cast_one` and `one_mul`
are the only transport needed.

**The target is a restriction, not a pullback.**
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.laurentPiece` is
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` applied to `L^{⊗ n}`, and
`Stacks.AmplePullbackPart1.restrictIsoPullback` is the comparison with the pullback along
`U(ψ).ι` for which the invertibility instance is available.

**The epimorphism criterion is already pointwise, so nothing is glued.**
`Stacks.VeryAmpleGlue.epi_of_forall_mem_nonvanishingLocusOn` asks for one local section per point
and concludes a global epimorphism, so `epi_theta_app_of_forall_chartSection` may let the chart
vary from point to point and still conclude about `θ_n` on all of `U(ψ)`. No locality statement
for `IsIso` is needed, and in particular the local isomorphy of clause (4) of Stacks Tag 01PZ
(`Stacks.SectionRingProjMorphism.Theta.exists_isIso_pullback_projTheta_app_intMul`) is not what is
promoted here: that clause reaches the degrees `e n` with `n : ℤ` for an `e` depending on the
point, and the degrees between consecutive multiples of `e` are not among them.

**The route is sectionwise, and spends `./TensorCancel.lean` only through the chart value.**
The source closes the remaining degrees with the sentence "by compatibility with the algebra
structure and the fact that `f` maps into `W`", read as a morphism identity: `θ_n ⊗ θ_q` is an
isomorphism whenever `θ_{n + q}` and `θ_q` are, so `θ_n` follows by cancelling the invertible
`f^*𝒪_Y(q)`, which is `Stacks.InvertibleTensorCancel.isIso_of_isIso_whiskerLeft_modules` and its
right-handed twin. That reading needs the multiplicativity of `θ` as a commuting square of
morphisms out of tensor products — `SheafOfModules.GradedAlgebra.mulSheaf` — and the monoidality
of `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which
`../SectionRingProjTheta/TwistSquare.lean` records as absent. The argument here reads the same
compatibility one section at a time instead: the fraction `c² / cb` names a section of `𝒪_Y(n)`
over `D₊(cb)`
(`Stacks.AlgebraicGeometry.ProjTwistAwayPiece.sectionsTwistEquivGradedPiece`), the chart-level
reading of condition (2) of Stacks Tag 01NK computes `θ_n` on its pullback as the chart value
`ψ(c²) / ψ(cb)`
(`Stacks.AlgebraicGeometry.ProjChartGradedTriple.app_pullbackSection_eq_intChartSection`), and
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.le_nonvanishingLocusOn_intChartSection` reads
the non-vanishing of that quotient off its numerator. Of the two cancellations only the
section-level one is consumed, and only inside that last step, where
`Stacks.TensorPowerDivision.nonvanishingLocusOn_intDivTop` separates the factors of
`(a / t) · t = a`.

## References

* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)

-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.GradedSections (powSections)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild (theta)
open Stacks.SectionRingGluedComparison (canonicalSections)
open Stacks.AlgebraicGeometry.ProjInvertibleLocus (whereInvertible)
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild (laurentRestrict)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AmpleFiniteAvoidance (nvLocus)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.TensorPowerTrivialize (resTop)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection integerGrading)
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)
open Stacks.SectionRingProjMorphism.Theta (projTheta)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.AmpleFiniteAvoidance (nvOpen)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intChartSection)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece)

universe u w

namespace Stacks.SectionRingProjTwistIso

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-! ### Local surjectivity of `θ_n` from one chart fraction per point -/

section Chartwise

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {M : T.Modules}
  [Stacks.Ample.IsInvertibleModule T M] (ψ : GradedSections 𝒜 M)

/-- **`θ_n` is an epimorphism as soon as every point of `T` lies on a chart `T_{ψ(f)}` carrying a
degree-`n` element of `A_f` whose chart value vanishes nowhere on that chart**, for any integer
`n`. The conclusion is global on `U(ψ)`; the hypothesis is one chart and one fraction per point.

`Stacks.VeryAmpleGlue.epi_of_forall_mem_nonvanishingLocusOn` asks, at each point of `U(ψ)`, for a
local section of the source whose image does not vanish there, so no gluing is needed: the section
is the pullback along `r_{L, ψ}` of the section of `𝒪_X(n)` over `D₊(f)` that the fraction names,
over the open `r_{L, ψ} ⁻¹ᵁ D₊(f)`. Its image is computed by
`Stacks.AlgebraicGeometry.ProjChartGradedTriple.app_pullbackSection_eq_intChartSection` — the
chart value of the fraction — and non-vanishing travels into `U(ψ)` along
`Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocusOn_restrict_image`, the chart open being
the image of `r_{L, ψ} ⁻¹ᵁ D₊(f)` by the definition of
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.chartOpen`.

`Stacks.AlgebraicGeometry.ProjChartGradedThetaIso.epi_pullback_theta_app` is the same argument for
a single chart and a morphism already restricted to an open `V` of it; what is different here is
that the chart is allowed to vary with the point, which is what makes the conclusion global. -/
theorem epi_theta_app_of_forall_chartSection (n : ℤ)
    (h : ∀ x : T, ∃ (d : ℕ) (hd : 0 < d) (f : A) (hf : f ∈ 𝒜 d)
      (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n), x ∈ ψ.chartOpen f ∧
        (ψ.chartOpen f : Set T) ⊆ nonvanishingLocusOn (tensorPowerModule T M n) (ψ.chartOpen f)
          (intChartSection ψ hf (ψ.chartOpen_eq hf hd).le hd n y)) :
    Epi ((theta 𝒜 ψ).app n) := by
  have : Stacks.Ample.IsInvertibleModule ψ.coveringOpen.toScheme
      ((laurentRestrict 𝒜 ψ).piece n) :=
    Stacks.AlgebraicGeometry.ProjChartGradedThetaIso.isInvertibleModule_laurentPiece 𝒜 ψ n
  refine Stacks.VeryAmpleGlue.epi_of_forall_mem_nonvanishingLocusOn _ fun z => ?_
  obtain ⟨d, hd, f, hf, y, hzc, hy⟩ := h (ψ.coveringOpen.ι.base z)
  set W := ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f with hWdef
  set s0 := (AlgebraicGeometry.pullbackSectionHom ψ.glued (twistM 𝒜 n)
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W le_rfl
      ((sectionsTwistEquivGradedPiece 𝒜 hf hd n).symm y) :
    Γ((Stacks.Conormal.gradedPullback ψ.glued
      (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜)).piece n, W)) with hs0
  refine ⟨W, s0, ?_⟩
  have hval : Scheme.Modules.Hom.app ((theta 𝒜 ψ).app n) W s0
      = intChartSection ψ hf (ψ.chartOpen_eq hf hd).le hd n y := by
    refine Eq.trans
      (Stacks.AlgebraicGeometry.ProjChartGradedTriple.app_pullbackSection_eq_intChartSection
        (Stacks.AlgebraicGeometry.ProjChartGradedTriple.isClauseTwo_theta ψ) hf hd
        (ψ.chartOpen_eq hf hd).le n _) ?_
    exact congrArg (intChartSection ψ hf (ψ.chartOpen_eq hf hd).le hd n)
      ((sectionsTwistEquivGradedPiece 𝒜 hf hd n).apply_symm_apply y)
  rw [hval]
  exact Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocusOn_restrict_image
    ψ.coveringOpen (tensorPowerModule T M n) W _ _ (hy hzc)

end Chartwise

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### The first claim of Tag 01QI, for the Tag 01NK datum -/

/-- **The morphism `r_{L, ψ}` of Stacks Tag 01NK for the identity datum maps `U(ψ)` into `W₁`.**
This is the first claim of Stacks Tag 01QI
(`Stacks.SectionRingProjGoodOpen.projHomOfIsAmple_preimage_whereInvertible`) read for
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued`, the two morphisms being
identified by `Stacks.SectionRingGluedComparison.ι_comp_projHomOfIsAmple_eq_glued`. -/
theorem glued_preimage_whereInvertible (hL : Stacks.Ample.IsAmple X L) :
    (canonicalSections L).glued ⁻¹ᵁ whereInvertible (grading L) 1 = ⊤ := by
  rw [← Stacks.SectionRingGluedComparison.ι_comp_projHomOfIsAmple_eq_glued L hL,
    Scheme.Hom.comp_preimage,
    Stacks.SectionRingProjGoodOpen.projHomOfIsAmple_preimage_whereInvertible L hL]
  simp

/-- **The factorisation of `f` through the good open `W₁`.** -/
def gluedToGood (hL : Stacks.Ample.IsAmple X L) :
    (canonicalSections L).coveringOpen.toScheme ⟶ (whereInvertible (grading L) 1).toScheme :=
  IsOpenImmersion.lift (whereInvertible (grading L) 1).ι (canonicalSections L).glued (by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨z, rfl⟩
    have hz : z ∈ (canonicalSections L).glued ⁻¹ᵁ whereInvertible (grading L) 1 := by
      rw [glued_preimage_whereInvertible L hL]; trivial
    exact hz)

/-- The factorisation is one: `gluedToGood ≫ W₁.ι = f`. -/
theorem gluedToGood_fac (hL : Stacks.Ample.IsAmple X L) :
    gluedToGood L hL ≫ (whereInvertible (grading L) 1).ι = (canonicalSections L).glued :=
  IsOpenImmersion.lift_fac _ _ _

/-! ### Both sides of `θ_n` are invertible -/

/-- **`𝒪_Y(n)|_{W₁}` is an invertible module, for every `n : ℤ`.** This is the invertibility half
of Stacks Tag 01MU's goodness of `W₁`
(`Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_whereInvertible`) at `d = 1`. -/
instance isInvertibleModule_restrict_whereInvertible (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (whereInvertible (grading L) 1).toScheme
      ((Scheme.Modules.pullback (whereInvertible (grading L) 1).ι).obj (twistM (grading L) n)) := by
  have h := (Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_whereInvertible
    (grading L) 1).1 n
  rw [Nat.cast_one, one_mul] at h
  exact h

/-- **The source of `θ_n` is invertible: `f^*𝒪_Y(n)` is an invertible `𝒪_{U(ψ)}`-module**, for
every `n : ℤ`. The twist is invertible only on `W₁`, and the first claim of Stacks Tag 01QI is
what lets `f` be read as a morphism into `W₁`; the pullback of an invertible module is invertible
by Stacks Tag 0B8L. -/
theorem isInvertibleModule_pullback_twistM (hL : Stacks.Ample.IsAmple X L) (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (canonicalSections L).coveringOpen.toScheme
      ((Scheme.Modules.pullback (canonicalSections L).glued).obj (twistM (grading L) n)) :=
  let : Stacks.Ample.IsInvertibleModule (canonicalSections L).coveringOpen.toScheme
      ((Scheme.Modules.pullback (whereInvertible (grading L) 1).ι ⋙
        Scheme.Modules.pullback (gluedToGood L hL)).obj (twistM (grading L) n)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (gluedToGood L hL) _
  Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    ((Scheme.Modules.pullbackComp (gluedToGood L hL)
        (whereInvertible (grading L) 1).ι).app (twistM (grading L) n) ≪≫
      (Scheme.Modules.pullbackCongr (gluedToGood_fac L hL)).app (twistM (grading L) n))

/-- **The target of `θ_n` is invertible: `L^{⊗ n}|_{U(ψ)}` is an invertible
`𝒪_{U(ψ)}`-module**, for every `n : ℤ`. -/
instance isInvertibleModule_laurentPiece (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (canonicalSections L).coveringOpen.toScheme
      ((canonicalSections L).laurentPiece n) := by
  have : Stacks.Ample.IsInvertibleModule (canonicalSections L).coveringOpen.toScheme
      ((Scheme.Modules.pullback (canonicalSections L).coveringOpen.ι).obj
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L n)) := inferInstance
  exact Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    (Stacks.AmplePullbackPart1.restrictIsoPullback (canonicalSections L).coveringOpen _).symm

/-! ### The second claim of Tag 01QI, reduced to local surjectivity -/

/-- **The second claim of Stacks Tag 01QI holds in degree `n` as soon as `θ_n` is an
epimorphism.** Both sides are invertible modules on `U(ψ)`, and an epimorphism between invertible
modules on a scheme is an isomorphism
(`Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible`): read through
trivialisations of the two sides it is multiplication by a section of the structure sheaf, and
local surjectivity makes that section a unit. -/
theorem isIso_theta_app_of_epi (hL : Stacks.Ample.IsAmple X L) (n : ℤ)
    (h : Epi ((theta (grading L) (canonicalSections L)).app n)) :
    IsIso ((theta (grading L) (canonicalSections L)).app n) :=
  have : Stacks.Ample.IsInvertibleModule (canonicalSections L).coveringOpen.toScheme
      ((Stacks.Conormal.gradedPullback (canonicalSections L).glued
        (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra (grading L))).piece n) :=
    isInvertibleModule_pullback_twistM L hL n
  have : Stacks.Ample.IsInvertibleModule (canonicalSections L).coveringOpen.toScheme
      ((Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.laurentRestrict (grading L)
        (canonicalSections L)).piece n) :=
    isInvertibleModule_laurentPiece L n
  Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible _ h

/-! ### Ampleness gives a nonvanishing homogeneous element in every large degree -/

/-- **For `L` ample there is an `n₀` beyond which every point has a homogeneous element of the
section ring of that exact degree not vanishing there.** This is the first half of clause (7) of
Stacks Tag 01Q3 (`Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple`): generation
of `L ^⊗ n` by global sections holds in all degrees above `n₀`, and at a point one member of a
generating family does not vanish
(`Stacks.SheafOfModules.exists_generatingSection_nonvanishing`); the member is then replaced by a
homogeneous element of `Γ_*(X, L)` with the same locus
(`Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq`), which is the vocabulary clause (3)
of Stacks Tag 01PZ speaks.

The sibling `../SectionRingProjGoodOpen/Basic.lean` runs the same argument at two *consecutive*
degrees, which is what the first claim of Stacks Tag 01QI needs; here one degree at a time is
enough. -/
theorem exists_powSections_mem_nvLocus (hL : Stacks.Ample.IsAmple X L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x : X,
      ∃ a : powSections L n, x ∈ Stacks.AmpleFiniteAvoidance.nvLocus L a := by
  obtain ⟨m₀, hgen⟩ := Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple L hL
  refine ⟨m₀.toNat, fun n hn x => ?_⟩
  obtain ⟨σ, -⟩ := hgen (n : ℤ) (Int.toNat_le.mp hn)
  obtain ⟨i, hi⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing
    (Stacks.Ample.tensorPowModule X L (n : ℤ)) σ x
  obtain ⟨a, ha⟩ := Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq L n
    ((σ.s i).eval (op ⊤))
  refine ⟨a, ?_⟩
  rw [ha, ← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X
    (Stacks.Ample.tensorPowModule X L (n : ℤ)) (σ.s i)]
  exact hi

/-! ### The second claim of Tag 01QI where `L ^⊗ n` is globally generated -/

/-- **`θ_n` is an epimorphism in a degree `n ≥ 0` in which every point has a homogeneous element
of `S_n` not vanishing there.** Clause (3) of Stacks Tag 01PZ
(`Stacks.SectionRingProjMorphism.Theta.projTheta_app_top_degreeSection`) says that `θ_n` carries
the pullback of the global section of `𝒪_Y(n)` attached to a homogeneous `z ∈ S_n` to `z` itself,
so a `z` not vanishing at the point exhibits the local surjectivity that
`Stacks.VeryAmpleGlue.epi_of_forall_mem_nonvanishingLocusOn` asks for: around a point where a
section of an invertible module does not vanish, every section is a multiple of it. -/
theorem epi_projTheta_app {n : ℕ}
    (h : ∀ x : X, ∃ a : powSections L n, x ∈ nvLocus L a) :
    Epi ((projTheta L).app (n : ℤ)) := by
  have : Stacks.Ample.IsInvertibleModule (canonicalSections L).coveringOpen.toScheme
      ((laurentRestrict (grading L) (canonicalSections L)).piece (n : ℤ)) :=
    isInvertibleModule_laurentPiece L (n : ℤ)
  refine Stacks.VeryAmpleGlue.epi_of_forall_mem_nonvanishingLocusOn _ fun z => ?_
  obtain ⟨a, ha⟩ := h ((canonicalSections L).coveringOpen.ι.base z)
  refine ⟨⊤, Scheme.Modules.pullbackSection (canonicalSections L).glued
      (twistM (grading L) (n : ℤ)) ⊤ ⊤ (fun _ _ => trivial)
      (degreeSection (grading L) n
        ⟨DirectSum.of (powSections L) n a, Stacks.ExternalGrading.of_mem_summand n a⟩), ?_⟩
  have hv := Stacks.SectionRingProjMorphism.Theta.projTheta_app_top_degreeSection L n
    (Stacks.ExternalGrading.of_mem_summand n a)
  have hx : (canonicalSections L).coveringOpen.ι.base z ∈
      nonvanishingLocusOn (tensorPowerModule X L (n : ℤ)) ⊤
        ((powCompare L n).hom.app ⊤
          (globalSection X (natTensorPow L n)
            ((DirectSum.of (powSections L) n a : Stacks.GradedSections.sectionRing L) n))) := by
    refine (Stacks.SectionPowerOverOpen.mem_nonvanishingLocusOn_congr_iff
      (powCompare L n) ⊤ _ trivial).mpr ?_
    rw [Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top, DirectSum.of_eq_same]
    exact ha
  have hgoal := Stacks.VeryAmpleGlue.mem_nonvanishingLocusOn_restrict
    (canonicalSections L).coveringOpen (tensorPowerModule X L (n : ℤ)) ⊤ _ z hx
  exact hv ▸ hgoal

/-- **The map `f^*𝒪_Y(n) ⟶ L^{⊗ n}` of clause (2) of Stacks Tag 01PZ is an isomorphism in a
degree `n ≥ 0` in which `L ^⊗ n` is generated by global sections.** Both sides are invertible —
the source by the *first* claim of Stacks Tag 01QI together with Stacks Tag 01MU — and `θ_n` is an
epimorphism, which for invertible modules is enough.

`isIso_projTheta_app` is the second claim of Stacks Tag 01QI itself, in every integer degree and
with no generation hypothesis; this is the global-section route to the same conclusion where that
hypothesis happens to hold, and the one that spends no fraction. -/
theorem isIso_projTheta_app_of_forall_nvLocus (hL : Stacks.Ample.IsAmple X L) {n : ℕ}
    (h : ∀ x : X, ∃ a : powSections L n, x ∈ nvLocus L a) :
    IsIso ((projTheta L).app (n : ℤ)) :=
  isIso_theta_app_of_epi L hL (n : ℤ) (epi_projTheta_app L h)

/-- **For `L` ample there is an `n₀` such that `f^*𝒪_Y(n) ⟶ L^{⊗ n}` is an isomorphism for every
natural `n ≥ n₀`**, by the global-section route. `isIso_projTheta_app` has no such bound. -/
theorem exists_isIso_projTheta_app (hL : Stacks.Ample.IsAmple X L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsIso ((projTheta L).app (n : ℤ)) := by
  obtain ⟨n₀, hgen⟩ := exists_powSections_mem_nvLocus L hL
  exact ⟨n₀, fun n hn => isIso_projTheta_app_of_forall_nvLocus L hL (hgen n hn)⟩

/-! ### The second claim of Tag 01QI in every integer degree -/

/-- **For `L` ample, every point of `X` and every integer `n` admit a chart `X_{cb}` through the
point and a degree-`n` fraction on it whose chart value vanishes nowhere on the chart.** The
fraction is `c² / cb` for two homogeneous elements `c ∈ S_p`, `b ∈ S_q` with `p = q + n`, neither
vanishing at the point: its numerator has degree `2 p = (p + q) + n`, so the fraction has degree
`n`, and the numerator is `c²`, which vanishes nowhere on `X_c ⊇ X_{cb}`.

Both degrees are above the `n₀` of `exists_powSections_mem_nvLocus`, and that is the only place
ampleness enters: `q = max n₀ 1 + n⁻` and `p = q + n` are then both admissible for every integer
`n`, negative ones included, and `p + q ≥ 1` makes `cb` a homogeneous element of positive degree.
`Stacks.SectionRingChartMap.nvOpen_mul` is `X_{cb} = X_c ∩ X_b`, which gives both the membership of
the point and the containment `X_{cb} ≤ X_{c²}`. -/
theorem exists_chartSection_nonvanishing (hL : Stacks.Ample.IsAmple X L) (n : ℤ) (x : X) :
    ∃ (d : ℕ) (hd : 0 < d) (f : Stacks.GradedSections.sectionRing L) (hf : f ∈ grading L d)
      (y : gradedPiece (grading L) (integerGrading (grading L)) f n),
      x ∈ (canonicalSections L).chartOpen f ∧
        ((canonicalSections L).chartOpen f : Set X) ⊆
          nonvanishingLocusOn (tensorPowerModule X L n) ((canonicalSections L).chartOpen f)
            (intChartSection (canonicalSections L) hf
              ((canonicalSections L).chartOpen_eq hf hd).le hd n y) := by
  obtain ⟨n₀, hgen⟩ := exists_powSections_mem_nvLocus L hL
  obtain ⟨q, p, hqN, hpN, hpq, hd⟩ :
      ∃ q p : ℕ, n₀ ≤ q ∧ n₀ ≤ p ∧ (p : ℤ) = (q : ℤ) + n ∧ 0 < p + q := by
    have hm : n₀ ≤ max n₀ 1 := le_max_left n₀ 1
    have hm1 : 1 ≤ max n₀ 1 := le_max_right n₀ 1
    exact ⟨max n₀ 1 + (-n).toNat, (((max n₀ 1 + (-n).toNat : ℕ) : ℤ) + n).toNat,
      by omega, by omega, by omega, by omega⟩
  obtain ⟨c, hc⟩ := hgen p hpN x
  obtain ⟨b, hb⟩ := hgen q hqN x
  refine ⟨p + q, hd, DirectSum.of (powSections L) (p + q) (Stacks.GradedSections.mul c b),
    Stacks.ExternalGrading.of_mem_summand (p + q) _, ?_⟩
  have hchart : (canonicalSections L).chartOpen
      (DirectSum.of (powSections L) (p + q) (Stacks.GradedSections.mul c b))
      = nvOpen L (Stacks.GradedSections.mul c b) :=
    ((canonicalSections L).chartOpen_eq
      (Stacks.ExternalGrading.of_mem_summand (p + q) _) hd).trans
      (Stacks.SectionRingGluedComparison.nonvanishingOpen_canonicalSections_of L (p + q) _ _)
  have hnum : DirectSum.of (powSections L) (p + p) (Stacks.GradedSections.mul c c)
      ∈ grading L (p + p) := Stacks.ExternalGrading.of_mem_summand (p + p) _
  have he : (((1 * (p + q) : ℕ) : ℤ)) + n = ((p + p : ℕ) : ℤ) := by push_cast; omega
  refine ⟨⟨LocalizedModule.mk
      (DirectSum.of (powSections L) (p + p) (Stacks.GradedSections.mul c c))
      (⟨DirectSum.of (powSections L) (p + q) (Stacks.GradedSections.mul c b) ^ 1, ⟨1, rfl⟩⟩ :
        Submonoid.powers _),
    Stacks.GradedLocalization.mk_mem_gradedPiece (grading L) _
      (Stacks.ExternalGrading.of_mem_summand (p + q) (Stacks.GradedSections.mul c b)) (by
        rw [show n + (1 : ℕ) • ((p + q : ℕ) : ℤ) = ((p + p : ℕ) : ℤ) from by
          rw [nsmul_eq_mul]; push_cast; omega]
        rw [AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast,
          AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_homogeneousSubmodule]
        exact hnum)⟩, ?_, ?_⟩
  · have hmem : x ∈ (nvOpen L (Stacks.GradedSections.mul c b) : Set X) := by
      rw [Stacks.AmpleFiniteAvoidance.coe_nvOpen, Stacks.AmpleFiniteAvoidance.nvLocus_mul]
      exact ⟨hc, hb⟩
    rw [hchart]
    exact hmem
  · refine Stacks.AlgebraicGeometry.ProjChartGradedDivision.le_nonvanishingLocusOn_intChartSection
      (canonicalSections L) _ _ hd n _ 1 (p + p) he hnum rfl ?_
    have hc2 : nonvanishingOpen X (natTensorPow L (p + p))
        ((canonicalSections L).toFun (p + p) ⟨_, hnum⟩)
        = nvOpen L (Stacks.GradedSections.mul c c) :=
      Stacks.SectionRingGluedComparison.nonvanishingOpen_canonicalSections_of L (p + p) _ _
    have hcb : nvOpen L (Stacks.GradedSections.mul c b) ≤ nvOpen L c := by
      rw [Stacks.SectionRingChartMap.nvOpen_mul]
      exact inf_le_left
    rw [hchart, hc2]
    exact Stacks.SectionRingChartMap.le_nvOpen_mul L hcb hcb

/-- **`θ_n` is an epimorphism for every `n : ℤ`**, `L` being ample. Every point lies on a chart
`X_{cb}` carrying a degree-`n` fraction whose chart value vanishes nowhere on it
(`exists_chartSection_nonvanishing`), and that is all `epi_theta_app_of_forall_chartSection`
asks. -/
theorem epi_projTheta_app_int (hL : Stacks.Ample.IsAmple X L) (n : ℤ) :
    Epi ((projTheta L).app n) :=
  epi_theta_app_of_forall_chartSection (canonicalSections L) n
    (exists_chartSection_nonvanishing L hL n)

/-- **The second claim of Stacks Tag 01QI: the maps `f^*𝒪_Y(n) ⟶ L^{⊗ n}` are isomorphisms for
every `n : ℤ`.** In Situation Stacks Tag 01QH — `X` a scheme, `L` an ample invertible
`𝒪_X`-module, `S = Γ_*(X, L)`, `Y = Proj S` and `f : X ⟶ Y` the canonical morphism of Stacks Tag
01PZ — these maps are the components of clause (2) of that tag
(`Stacks.SectionRingProjMorphism.Theta.projTheta`), and every one of them, in every integer
degree, is an isomorphism.

Both sides are invertible modules on `U(ψ) = ⋃_a X_a` in every degree: the target by Stacks Tag
01CU, the source because the *first* claim of Stacks Tag 01QI puts the image of `f` in the good
open `W₁` of Stacks Tag 01MU, where `𝒪_Y(n)` is invertible
(`isInvertibleModule_pullback_twistM`). So `isIso_theta_app_of_epi` reduces the claim to `θ_n`
being an epimorphism, which is `epi_projTheta_app_int`. -/
@[stacks 01QI "second claim: the maps f^*O_Y(n) -> L^{tensor n} of clause (2) of Tag 01PZ are \
isomorphisms for every n in Z, positive, zero and negative"]
theorem isIso_projTheta_app (hL : Stacks.Ample.IsAmple X L) (n : ℤ) :
    IsIso ((projTheta L).app n) :=
  isIso_theta_app_of_epi L hL n (epi_projTheta_app_int L hL n)

end Stacks.SectionRingProjTwistIso

end
