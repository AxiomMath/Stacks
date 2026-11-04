module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedClassifying
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGradedGluing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationGluing
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedVeronese

/-!
# Tag 01NK's morphism is Tag 01N8's classifying morphism, degreewise

Let `A` be a graded ring, `Y` a scheme, `ψ : A → Γ_*(Y, M)` a datum of [Stacks, Tag 01NK] and
`χ : A^{(k)} → Γ_*(Y, N)` a triple of [Stacks, Tag 01N8] generating `N`. Suppose that in every
degree `n` some isomorphism `M^{⊗ nk} ≅ N^{⊗ n}` carries `ψ` on `A_{nk}` to `χ` on `A_{nk}`.
Then the morphism `U(ψ) ⟶ Proj A` of Tag 01NK is the restriction of the morphism `Y ⟶ Proj A`
that `χ` classifies.

The isomorphisms need not be compatible with each other: both morphisms are, on the chart of a
homogeneous `h` of degree `k`, `Spec` of the ring map `a / h^n ↦ (value at a) / (value at h^n)`,
and a ratio of two sections of one invertible module is unchanged by an isomorphism applied to
both (`…ProjChartGradedVeronese.ratioOf_iso`). Only the degree `n` of each fraction is involved.

This is the comparison behind clause (2) of [Stacks, Tag 01O9]: there, on an open where `ψ` is
surjective in degree `k`, the two morphisms are the restriction of `r_{ℒ,ψ}` and the morphism
the relative homogeneous spectrum attaches to the quadruple `(k, ℒ^{⊗ k}, ψ|_{𝒜^{(k)}})`.

## Main results

* `…RelativeProjInvertibleMorphism.coveringOpen_ι_toProj_classifyingHom`: the comparison.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (psiSection)
open Stacks.AlgebraicGeometry.ProjTripleClassifying (classifyingHom)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.MorphismToProj (HomogeneousRatios)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {Y : Scheme.{u}} {M N : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y M] [Stacks.Ample.IsInvertibleModule Y N]

/-- Two families of homogeneous ratios with the same values are equal. -/
theorem homogeneousRatios_ext {d : ℕ} {f : A} {hf : f ∈ 𝒜 d} {P : Type u} [CommRing P]
    {R R' : HomogeneousRatios 𝒜 hf P} (h : ∀ n (a : 𝒜 (n * d)), R.toFun n a = R'.toFun n a) :
    R = R' := by
  cases R; cases R'
  congr
  funext n
  exact AddMonoidHom.ext (h n)

/-- **Tag 01NK's morphism is the restriction of the morphism Tag 01N8's triple classifies**,
when in every degree an isomorphism of the powers carries the one datum to the other. -/
theorem coveringOpen_ι_toProj_classifyingHom (ψ : GradedSections 𝒜 M) {k : ℕ} (hk : 0 < k)
    (χ : VeroneseSections 𝒜 k N)
    (hgen : ⨆ g : 𝒜 k, nonvanishingOpen Y N (psiSection 𝒜 χ g) = ⊤)
    (Φ : ∀ n : ℕ, (natTensorPow M (n * k) : Y.Modules) ≅ natTensorPow N n)
    (hΦ : ∀ (n : ℕ) (a : 𝒜 (n * k)), (Φ n).hom.app ⊤ (ψ.toFun (n * k) a) = χ.toFun n a) :
    ψ.coveringOpen.ι ≫ toProj 𝒜 (classifyingHom 𝒜 hk χ hgen) = ψ.glued := by
  -- the nonvanishing opens of `ψ` and `χ` at a homogeneous element of degree `k` agree
  have hT : ∀ g : 𝒜 k, nonvanishingOpen Y (natTensorPow M k) (ψ.toFun k g)
      = nonvanishingOpen Y (natTensorPow N 1) (χ.pow g.2 1) := by
    intro g
    have h1 := Stacks.Ample.nonvanishingLocus_congr (Φ 1)
      (ψ.toFun (1 * k) ⟨(g : A) ^ 1, HomogeneousRatios.pow_mem g.2 1⟩)
    rw [hΦ] at h1
    refine (ψ.nonvanishingOpen_congr g.2 (HomogeneousRatios.pow_mem g.2 1) (one_mul k).symm
      (pow_one _).symm).trans (Opens.ext h1.symm)
  have hT' : ∀ g : 𝒜 k, nonvanishingOpen Y (natTensorPow M k) (ψ.toFun k g)
      = nonvanishingOpen Y N (psiSection 𝒜 χ g) := fun g =>
    (hT g).trans (Stacks.AlgebraicGeometry.MorphismToProjUniversal.nonvanishingOpen_psiSection
      𝒜 χ g).symm
  have hle : ∀ g : 𝒜 k, nonvanishingOpen Y (natTensorPow M k) (ψ.toFun k g) ≤ ψ.coveringOpen :=
    fun g => ψ.nonvanishingOpenAt_le_coveringOpen_of_pos g.2 hk
  refine Stacks.Thickenings.hom_ext_of_opens
    (fun g : 𝒜 k => nonvanishingOpen Y (natTensorPow M k) (ψ.toFun k g)) hle ?_ _ _ fun g => ?_
  · intro x _
    have hx : x ∈ (⨆ g : 𝒜 k, nonvanishingOpen Y N (psiSection 𝒜 χ g)) := by
      rw [hgen]; trivial
    obtain ⟨g, hg⟩ := Opens.mem_iSup.mp hx
    refine ⟨g, ?_⟩
    rwa [hT' g]
  · have hVW := (hT' g).le
    have hV := (hT g).le
    have e1 : Y.homOfLE (hle g) ≫ ψ.coveringOpen.ι ≫ toProj 𝒜 (classifyingHom 𝒜 hk χ hgen)
        = (χ.homogeneousRatios g.2 hV).chartToProj hk := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
      exact Stacks.AlgebraicGeometry.ProjChartGradedClassifying.homOfLE_toProj_classifyingHom
        𝒜 hk χ hgen g hVW hV
    have e2 : Y.homOfLE (hle g) ≫ ψ.glued
        = (ψ.homogeneousRatios g.2 le_rfl).chartToProj hk :=
      ψ.homOfLE_glued_of_pos g.2 hk
    rw [e1, e2]
    congr 1
    refine homogeneousRatios_ext fun n a => ?_
    show ratioOf N (χ.pow g.2 n) (χ.le_nonvanishingOpen g.2 hV n) (χ.toFun n a)
      = ratioOf M (ψ.toFun (n * k) ⟨(g : A) ^ n, HomogeneousRatios.pow_mem g.2 n⟩)
          (ψ.le_nonvanishingOpen_pow g.2 le_rfl n) (ψ.toFun (n * k) a)
    have hpow : χ.pow g.2 n
        = (Φ n).hom.app ⊤ (ψ.toFun (n * k) ⟨(g : A) ^ n, HomogeneousRatios.pow_mem g.2 n⟩) :=
      (hΦ n _).symm
    have hval : χ.toFun n a = (Φ n).hom.app ⊤ (ψ.toFun (n * k) a) := (hΦ n a).symm
    simp only [hval, hpow]
    exact Stacks.AlgebraicGeometry.ProjChartGradedVeronese.ratioOf_iso M N (Φ n) _ _ _ _

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
