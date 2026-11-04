module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjImmersion.ProjBasis
public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasiCompact.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical morphism to `Proj Γ_*(X, L)` is an open immersion with dense image: Tag 01Q1

Let `X` be a scheme, `L` an **ample** invertible `𝒪_X`-module and `S = Γ_*(X, L)` the graded
section ring of Stacks Tag 01CV. Stacks Tag 01PZ constructs the canonical morphism
`f : X ⟶ Proj S` (`Stacks.SectionRingProjMorphism.projHomOfIsAmple`). **Stacks Tag 01Q1** says
that `f` is an open immersion with dense image, and that is what is proved here.

## The two halves

Both halves rest on the same two known facts and on the bijectivity of the chart ring map.

* Clause (1) of Tag 01PZ,
  `Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen`: the preimage of the
  chart `D₊(a)` is the nonvanishing open `X_a`.
* `Stacks.SectionRingProjImmersion.ι_comp_projHomOfIsAmple`: on `X_a` the morphism **is** the
  chart `Stacks.SectionRingChartMap.chartHom`, which is clause (2) of Tag 01PZ transported from
  the open `⋃_a X_a` the gluing lives on to `X` itself.

**Open immersion.** Ampleness puts an *affine* `X_a`, with `a` homogeneous of positive degree,
through every point of `X` (`Stacks.SectionExtension.exists_pos_affine_nvOpen`). Over such an `a`
the chart factors as `X_a ⟶ Spec Γ(X, X_a) ⟶ Spec S₍a₎ ⟶ Proj S`
(`Stacks.SectionRingChartOpen.chartHomOn_val`), whose first arrow is an isomorphism because `X_a`
is affine, whose second is `Spec` of the chart ring map and so an isomorphism because that map is
bijective (`Stacks.SectionRingChartBijective.chartRingMap_bijective`, which is the "in particular"
of Stacks Tag 01PW at the degree of `a`), and whose third is Mathlib's open immersion
`AlgebraicGeometry.Proj.awayι`. So `X_a ⟶ Proj S` is an open immersion, and
`AlgebraicGeometry.IsZariskiLocalAtTarget.of_forall_source_exists_preimage` assembles the charts:
the `D₊(a)` of the affine charts need not cover `Proj S`, only the range of `f`, which is exactly
what that glue asks for.

**Dense image.** This half of Tag 01Q1 is **Stacks Tag 01Q0**, which the source cites here and
which is proved under its own weaker hypotheses in
`StacksFrontier/AlgebraicGeometry/SectionRingProjQuasiCompact/Basic.lean`: it needs only that the
`X_s` cover `X` and that `X` is quasi-compact, both of which ampleness supplies. Nothing about it
is redone here.

## Main results

* `Stacks.SectionRingProjImmersion.ι_comp_projHomOfIsAmple`: the restriction of the canonical
  morphism to `X_a` is the chart at `a`.
* `Stacks.SectionRingProjImmersion.isOpenImmersion_chartHom`: the chart at `a` is an open
  immersion when `X_a` is affine.
* `Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple`: **Stacks Tag 01Q1, the open
  immersion.**
* `Stacks.SectionRingProjImmersion.denseRange_projHomOfIsAmple`: **Stacks Tag 01Q1, the dense
  image**, read off Stacks Tag 01Q0.

## References

* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
* [Stacks Project, Tag 01Q0](https://stacks.math.columbia.edu/tag/01Q0)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionExtension (resTop exists_pos_affine_nvOpen)

universe u

namespace Stacks.SectionRingProjImmersion

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### The restriction of the canonical morphism to a chart -/

/-- **On `X_a` the canonical morphism of Stacks Tag 01PZ is the chart at `a`.** This is
`Stacks.SectionRingProjMorphism.homOfLE_projHom` read on `X` rather than on the open `⋃_b X_b`
the gluing lives on; the identification of the two is the isomorphism `X ≅ ⋃_b X_b` that ampleness
supplies, and it is pinned by the fact that `⋃_b X_b ⟶ X` is a monomorphism. -/
theorem ι_comp_projHomOfIsAmple (hL : IsAmple X L) {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    (nvOpen L a).ι ≫ Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL
      = Stacks.SectionRingChartMap.chartHom L a hd := by
  have hι : (Scheme.topIso X).inv
      ≫ (X.isoOfEq (Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple L hL)).inv
      ≫ (Stacks.SectionRingProjMorphism.nvUnion L).ι = 𝟙 X := by
    have h1 : (X.isoOfEq (Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple L hL)).inv
        ≫ (Stacks.SectionRingProjMorphism.nvUnion L).ι = (⊤ : X.Opens).ι := by
      rw [Iso.inv_comp_eq, Scheme.isoOfEq_hom_ι]
    rw [h1, ← Scheme.topIso_hom, Iso.inv_hom_id]
  have hcl : (nvOpen L a).ι ≫ (Scheme.topIso X).inv
      ≫ (X.isoOfEq (Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple L hL)).inv
      = X.homOfLE (Stacks.SectionRingProjMorphism.nvOpen_le_nvUnion L a hd) := by
    refine (cancel_mono (Stacks.SectionRingProjMorphism.nvUnion L).ι).mp ?_
    rw [Category.assoc, Category.assoc, hι, Scheme.homOfLE_ι, Category.comp_id]
  rw [Stacks.SectionRingProjMorphism.projHomOfIsAmple,
    Stacks.SectionRingProjMorphism.projHomOfCovers,
    ← Stacks.SectionRingProjMorphism.homOfLE_projHom L a hd, ← hcl]
  simp only [Category.assoc]

/-! ### The open immersion -/

/-- **The chart at a homogeneous element of positive degree with affine nonvanishing open is an
open immersion.** The chart factors as the unit `X_a ⟶ Spec Γ(X, X_a)`, which is an isomorphism
because `X_a` is affine, followed by `Spec` of the chart ring map, an isomorphism because that map
is bijective, followed by Mathlib's open immersion `AlgebraicGeometry.Proj.awayι`. -/
theorem isOpenImmersion_chartHom (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d) (a : powSections L d)
    (haff : IsAffineOpen (nvOpen L a)) :
    IsOpenImmersion (Stacks.SectionRingChartMap.chartHom L a hd) := by
  have h1 : IsIso ((nvOpen L a).toSpecΓ) :=
    haff.isoSpec_hom ▸ (inferInstance : IsIso haff.isoSpec.hom)
  have h2 : IsIso (CommRingCat.ofHom
      (Stacks.SectionRingChartMap.chartRingMap L a (le_refl (nvOpen L a)))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr
      (Stacks.SectionRingChartBijective.chartRingMap_bijective L hL hd a)
  rw [← Stacks.SectionRingChartOpen.chartHomOn_self L a hd,
    Stacks.SectionRingChartOpen.chartHomOn_val L a hd (le_refl (nvOpen L a))]
  infer_instance

/-- **Stacks Tag 01Q1, the open immersion.** For `L` an ample invertible `𝒪_X`-module, the
canonical morphism `X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ is an open immersion. -/
@[stacks 01Q1 "open immersion", ega "II 4.5.2" "partial"]
theorem isOpenImmersion_projHomOfIsAmple (hL : IsAmple X L) :
    IsOpenImmersion (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL) := by
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage
    (P := @IsOpenImmersion) _ fun x ↦ ?_
  obtain ⟨d, a, hd, hxa, haff⟩ := exists_pos_affine_nvOpen L hL x
  have hpre := Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL a hd
  refine ⟨Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a), hpre.ge hxa, ?_⟩
  · have hfac : (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL
          ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)).ι
        ≫ Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL
        = (X.isoOfEq hpre).hom ≫ Stacks.SectionRingChartMap.chartHom L a hd := by
      rw [← ι_comp_projHomOfIsAmple L hL a hd, ← Category.assoc, Scheme.isoOfEq_hom_ι]
    rw [hfac]
    have := isOpenImmersion_chartHom L hL hd a haff
    infer_instance

/-! ### The dense image -/

/-- **Stacks Tag 01Q1, the dense image.** For `L` an ample invertible `𝒪_X`-module, the canonical
morphism `X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ has dense image.

This is Stacks Tag 01Q0 (`Stacks.SectionRingProjQuasiCompact.denseRange_projHomOfCovers`), which
the source cites here: ampleness gives both of that tag's hypotheses, that the `X_s` cover `X`
(`Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple`) and that `X` is quasi-compact. -/
@[stacks 01Q1 "dense image"]
theorem denseRange_projHomOfIsAmple (hL : IsAmple X L) :
    DenseRange (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL).base := by
  have := hL.compactSpace
  exact Stacks.SectionRingProjQuasiCompact.denseRange_projHomOfCovers L
    (Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple L hL)

end Monoidal

end Stacks.SectionRingProjImmersion

end
