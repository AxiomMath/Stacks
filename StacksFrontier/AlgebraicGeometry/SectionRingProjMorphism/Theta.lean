module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.GluedComparison
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTripleTag

/-!
# The twisting maps of the canonical morphism to `Proj` of the section ring: clauses (2) and (3)

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, `S = Γ_*(X, L)` the graded section ring and
`f : X ⟶ Y = Proj S` the canonical morphism of [Stacks, Tag 01PZ]. This file proves clauses (2) and
(3) of that tag:

* **clause (2)**: there are `𝒪_X`-module maps `f^*𝒪_Y(n) ⟶ L^{⊗ n}`, compatible with the
  multiplication maps of Constructions, Equation 01MO;
* **clause (3)**: the composite `S_n ⟶ Γ(Y, 𝒪_Y(n)) ⟶ Γ(X, L^{⊗ n})` is the identity.

Both are stated for the triple `(U(ψ), r_{L, ψ}, θ)` of [Stacks, Tag 01NK] at the identity map
`ψ = Stacks.SectionRingGluedComparison.canonicalSections L` of `Γ_*(X, L)`, where `θ` is
`Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.theta`, and `r_{L, ψ}` is identified with
`Stacks.SectionRingProjMorphism.projHom`.

## Main results

* `Stacks.SectionRingProjMorphism.Theta.homOfLE_projHom_eq_glued`: **the canonical morphism of
  [Stacks, Tag 01PZ] is `r_{L, ψ}` at `ψ` the identity**, with no hypothesis on `L`.
* `Stacks.SectionRingProjMorphism.Theta.glued_preimage_projBasicOpen`: **clause (1)**,
  `f^{-1}(D₊(s)) = X_s`, at `r_{L, ψ}`.
* `Stacks.SectionRingProjMorphism.Theta.projTheta`: **clause (2)** — the maps `f^*𝒪_Y(n) ⟶ L^{⊗ n}`
  for all `n ∈ ℤ` at once, as a homomorphism of sheaves of `ℤ`-graded algebras, whose `map_mul` is
  the compatibility with the multiplication maps.
* `Stacks.SectionRingProjMorphism.Theta.projThetaUnital` and
  `Stacks.SectionRingProjMorphism.Theta.coveringOpen_eq_top_and_ι_comp_projHomOfIsAmple`:
  **Situation [Stacks, Tag 01QH]** — for `L` ample, `θ` is a unital map of `ℤ`-graded algebras
  `⨁ f^*𝒪_Y(n) ⟶ ⨁ L^{⊗ n}` along the canonical morphism, defined on all of `X`.
* `Stacks.SectionRingProjMorphism.Theta.projTheta_app_top_degreeSection`: **clause (3)** — for a
  homogeneous `z` of degree `d`, the degree-`d` component of `θ` carries the pullback of the global
  section of `𝒪_Y(d)` attached to `z` to `z` itself.

## References

* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing)
open Stacks.SectionProduct (globalSection)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild (theta laurentRestrict)
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.TensorPowerTrivialize (resTop)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.SectionRingGluedComparison (canonicalSections coveringOpen_canonicalSections
  nonvanishingOpen_canonicalSections_of lift_eq_chartRingMap)

universe u

namespace Stacks.SectionRingProjMorphism.Theta

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### The canonical morphism is `r_{L, ψ}` at `ψ` the identity -/

/-- **On an open inside `X_s` the canonical morphism of [Stacks, Tag 01PZ] is the chart of
[Stacks, Tag 01NK] at `s`**, with no hypothesis on `L`: the inclusion `V ⟶ ⋃_a X_a` followed by
`Stacks.SectionRingProjMorphism.projHom` is the chart morphism `V ⟶ Proj S` at `s`. -/
theorem homOfLE_projHom_eq_chartToProj {e : ℕ} (s : powSections L e) (he : 0 < e)
    (hf : DirectSum.of (powSections L) e s ∈ grading L e) {V : X.Opens}
    (hV : V ≤ nonvanishingOpen X (natTensorPow L e) ((canonicalSections L).toFun e ⟨_, hf⟩))
    (hVU : V ≤ Stacks.SectionRingProjMorphism.nvUnion L) :
    X.homOfLE hVU ≫ Stacks.SectionRingProjMorphism.projHom L
      = (canonicalSections L).chartToProj hf hV he := by
  have hV' : V ≤ nvOpen L s := hV.trans (le_of_eq (nonvanishingOpen_canonicalSections_of L e s hf))
  rw [← Scheme.homOfLE_homOfLE X hV' (Stacks.SectionRingProjMorphism.nvOpen_le_nvUnion L s he),
    Category.assoc, Stacks.SectionRingProjMorphism.homOfLE_projHom L s he,
    ← Stacks.SectionRingChartOpen.chartHomOn_self L s he,
    Stacks.SectionRingChartOpen.homOfLE_chartHomOn L s he le_rfl hV' hV',
    Stacks.SectionRingChartOpen.chartHomOn_val L s he hV']
  change _ = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (((canonicalSections L).homogeneousRatios hf hV).lift he)) ≫
    AlgebraicGeometry.Proj.awayι (grading L) _ hf he
  rw [lift_eq_chartRingMap L s he hf hV hV']

/-- **The canonical morphism `Stacks.SectionRingProjMorphism.projHom` is the morphism `r_{L, ψ}` of
[Stacks, Tag 01NK] at `ψ` the identity map of `Γ_*(X, L)`**, with no hypothesis on `L`: the two
morphisms have the same source `U(ψ) = ⋃_a X_a`
(`Stacks.SectionRingGluedComparison.coveringOpen_canonicalSections`) and agree there. -/
@[stacks 01PZ "the canonical morphism is the morphism r_{L,psi} of Tag 01NK at psi the identity \
map of the section ring, with no hypothesis on L; this is what the clauses below are clauses about"]
theorem homOfLE_projHom_eq_glued :
    X.homOfLE (coveringOpen_canonicalSections L).le
        ≫ Stacks.SectionRingProjMorphism.projHom L
      = (canonicalSections L).glued := by
  refine (canonicalSections L).eq_glued_of_homOfLE_eq fun e f hf he => ?_
  rw [← Category.assoc, Scheme.homOfLE_homOfLE]
  obtain ⟨s, rfl⟩ := hf
  exact homOfLE_projHom_eq_chartToProj L s he _ le_rfl _

/-! ### Clause (1) at `r_{L, ψ}` -/

/-- `f^{-1}(D₊(s)) = X_s` for every homogeneous `s ∈ S_+`, where `f` is `r_{L, ψ}` at `ψ` the
identity map of `S = Γ_*(X, L)`. Both sides are opens of the source `U(ψ) = ⋃_a X_a` of `f`, the
right-hand side being `X_s`, which lies inside it. -/
@[stacks 01PZ "clause (1): f^{-1}(D_+(s)) = X_s for every homogeneous s in S_+, for the morphism \
f = r_{L,psi} that clauses (2), (3) and (4) are stated at, as opens of its source U(psi)"]
theorem glued_preimage_projBasicOpen {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    (canonicalSections L).glued ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)
      = (canonicalSections L).coveringOpen.ι ⁻¹ᵁ nvOpen L a := by
  rw [(canonicalSections L).preimage_basicOpen_glued
    (Stacks.ExternalGrading.of_mem_summand d a) hd,
    nonvanishingOpen_canonicalSections_of]

/-! ### Clause (2): the maps `f^*𝒪_Y(n) ⟶ L^{⊗ n}` -/

/-- **The `𝒪_X`-module maps `f^*𝒪_Y(n) ⟶ L^{⊗ n}`, compatible with the multiplication maps of
Constructions, Equation 01MO.** All degrees at once, as a homomorphism of sheaves of `ℤ`-graded
`𝒪_X`-algebras `f^*(⨁_{n ∈ ℤ} 𝒪_Y(n)) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}`: its component in degree `n` is the map
`f^*𝒪_Y(n) ⟶ L^{⊗ n}`, and its `map_mul` field is exactly the compatibility, the multiplication
maps of the two graded algebras being those of Equation 01MO on the source and the tensor product
of sections on the target. It is `θ` of [Stacks, Tag 01NK] at `ψ` the identity map of `Γ_*(X, L)`,
taken along `f = r_{L, ψ}`. -/
@[stacks 01PZ "clause (2): the O_X-module maps f^*O_Y(n) -> L^{tensor n} for all n in Z, as a \
homomorphism of sheaves of Z-graded algebras, whose map_mul is their compatibility with the \
multiplication maps of Constructions Equation 01MO"]
def projTheta : SheafOfModules.GradedAlgebra.Hom
    (Stacks.Conormal.gradedPullback (canonicalSections L).glued
      (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra (grading L)))
    (laurentRestrict (grading L) (canonicalSections L)) :=
  theta (grading L) (canonicalSections L)

/-- The degree-`n` component of `projTheta` is the degree-`n` component of `θ`. -/
theorem projTheta_app (n : ℤ) :
    (projTheta L).app n = ((theta (grading L) (canonicalSections L)).app n) := rfl

/-! ### Situation 01QH: the canonical morphism and its graded algebra map -/

/-- **The `ℤ`-graded `𝒪_X`-algebra map `⨁ f^*𝒪_Y(n) ⟶ ⨁ L^{⊗ n}` of Situation
[Stacks, Tag 01QH]**: `projTheta`, i.e. `θ` of [Stacks, Tag 01NK] at `ψ` the identity map of
`Γ_*(X, L)`, taken along `f = r_{L, ψ}`, together with its preservation of the unit
(`Stacks.AlgebraicGeometry.ProjChartGradedTriple.theta_map_one`). Its degreewise components are
the maps of clause (2) of [Stacks, Tag 01PZ] and its `map_mul` is their compatibility with the
multiplication maps.

It is stated on the source `U(ψ) = ⋃_a X_a` of `r_{L, ψ}`, with no hypothesis on `L`. In the
Situation, where `L` is ample, `U(ψ)` is all of `X` and `r_{L, ψ}` is the canonical morphism
`f : X ⟶ Proj S` of [Stacks, Tag 01PZ] restricted to it:
`Stacks.SectionRingProjMorphism.Theta.coveringOpen_eq_top_and_ι_comp_projHomOfIsAmple`. -/
@[stacks 01QH "the Z-graded O_X-algebra map sum_n f^*O_Y(n) -> sum_n L^{tensor n} the Situation \
equips the canonical morphism with: theta of Tag 01NK at psi the identity of Gamma_*(X, L), along \
f = r_{L,psi}, multiplicative and unital, on the source U(psi) of r_{L,psi}; in the Situation \
U(psi) = X and r_{L,psi} is the canonical morphism of Tag 01PZ, which is \
coveringOpen_eq_top_and_ι_comp_projHomOfIsAmple"]
def projThetaUnital : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback (canonicalSections L).glued
      (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra (grading L)))
    (laurentRestrict (grading L) (canonicalSections L)) :=
  Stacks.AlgebraicGeometry.ProjChartGradedTriple.thetaUnital (canonicalSections L)

/-- Forgetting the unit law, `projThetaUnital` is `projTheta`. -/
@[simp] theorem projThetaUnital_toHom : (projThetaUnital L).toHom = projTheta L := rfl

/-- **In Situation [Stacks, Tag 01QH] the map `θ` lives on all of `X` and along the canonical
morphism**: for `L` ample, the source `U(ψ) = ⋃_a X_a` of `r_{L, ψ}` (at `ψ` the identity of
`Γ_*(X, L)`) is all of `X`, and `r_{L, ψ}` is the inclusion `U(ψ) ⟶ X` followed by the canonical
morphism `f : X ⟶ Proj S` of [Stacks, Tag 01PZ]. So `projThetaUnital` is the Situation's map
`⨁ f^*𝒪_Y(n) ⟶ ⨁ L^{⊗ n}`. -/
@[stacks 01QH "the canonical morphism of the Situation: for L ample, U(psi) = X and \
r_{L,psi} = (U(psi) -> X) followed by the canonical morphism f : X -> Proj S of Tag 01PZ, so \
projThetaUnital is the graded algebra map along f"]
theorem coveringOpen_eq_top_and_ι_comp_projHomOfIsAmple (hL : Stacks.Ample.IsAmple X L) :
    (canonicalSections L).coveringOpen = ⊤ ∧
      (canonicalSections L).coveringOpen.ι ≫ Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL
        = (canonicalSections L).glued :=
  ⟨Stacks.SectionRingGluedComparison.coveringOpen_canonicalSections_eq_top L hL,
    Stacks.SectionRingGluedComparison.ι_comp_projHomOfIsAmple_eq_glued L hL⟩

/-! ### Clause (3): the composite `S_n ⟶ Γ(Y, 𝒪_Y(n)) ⟶ Γ(X, L^{⊗ n})` is the identity -/

/-- **The composite `S_d ⟶ Γ(Y, 𝒪_Y(d)) ⟶ Γ(X, L^{⊗ d})` is the identity map.** For a homogeneous
element `z` of `S = Γ_*(X, L)` of degree `d`, the first map sends `z` to the global section of
`𝒪_Y(d)` attached to it by [Stacks, Tag 01MP], the second pulls that back along `f` and applies the
degree-`d` component of `projTheta`, and the result is `z` itself: the global section of `L^{⊗ d}`
that the degree-`d` component `z d` of `z` names.

Both sides are sections of `L^{⊗ d}` over `⋃_a X_a`, where `f` is defined, with `L^{⊗ d}` read in
the family `Stacks.AmpleProjectiveImmersion.tensorPowerModule` and compared with the iterated
tensor power by `Stacks.AlgebraicGeometry.CoherentMulSections.powCompare`. -/
@[stacks 01PZ "clause (3): the composite S_d -> Gamma(Y, O_Y(d)) -> Gamma(X, L^{tensor d}) is the \
identity map, read on the open where the canonical morphism is defined"]
theorem projTheta_app_top_degreeSection (d : ℕ) {z : sectionRing L} (hz : z ∈ grading L d) :
    ((projTheta L).app (d : ℤ)).val.app (op ⊤)
        (Scheme.Modules.pullbackSection (canonicalSections L).glued
          (twistM (grading L) (d : ℤ)) ⊤ ⊤ (fun _ _ => trivial)
          (degreeSection (grading L) d ⟨z, hz⟩))
      = resTop (tensorPowerModule X L (d : ℤ))
          ((powCompare L d).hom.app ⊤ (globalSection X (natTensorPow L d) (z d)))
          ((canonicalSections L).coveringOpen.ι ''ᵁ ⊤) :=
  Stacks.AlgebraicGeometry.ProjChartGradedTriple.isClauseTwo_theta (canonicalSections L) d hz

end Stacks.SectionRingProjMorphism.Theta

end
