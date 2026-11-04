module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SectionsInfinitesimalUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SectionsInfinitesimalAmalgamate
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftComorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpRestrictedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceSurjective

/-!
# Equation (0CKE): the sections of `Γ₀` are a torsor under the `𝒪_{U₀}`-linear maps

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, let `U₀ ⊆ U` be a
first order thickening, let `R₀ = s^{-1}(U₀) ⊆ R` and let `Γ₀` be the set of
[Stacks Project, Tag 0CKB] of sections of the source agreeing with the unit on `U₀`.

This file closes Equation [Stacks Project, Tag 0CKE].  What was still owed was the bare
existence clause — that for `δ ∈ Γ₀` and an `𝒪_{U₀}`-linear map
`θ : e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` there is an `ε ∈ Γ₀` with
`infinitesimalSectionDiff G U₀ hU₀ δ ε = θ`; the uniqueness half is already proved
unconditionally in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsInfinitesimalUnique.lean`.  With
the existence clause the datum
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference` is constructed from
the thickening alone, and the displayed bijection of (0CKE) holds outright.

## The argument

`AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_infinitesimalSection_eq_chartSiteHom`
amalgamates the chartwise morphisms attached to the moved solution
`g = δ^♯ − ι ∘ D ∘ j^♯` into a section `ε ∈ Γ₀` whose restriction to every chart carrying an
index over an affine chart of `R` is the attached morphism of charts.  Three steps turn that into
the existence clause.

1. The comorphism of `ε` read through the thickening is that solution carried back to the
   ambient site: by
   `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom` the
   solution read at the tautological index is the comorphism of `ε`, the chart morphisms of the
   solution being chart morphisms of `ε`; and
   `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_eq_of_eq_thickeningLiftOfIndex`
   carries that to the index the solution arrives in.
2. The transport to the site of `R₀` is injective
   (`AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening_injective`), so the transported
   comorphism of `ε` *is* `g`.
3. The descended difference of `g` from the transported comorphism of `δ` is `θ`, by
   `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_liftDifferenceDataOfHom`; and the
   descended difference of the pair `(δ, ε)` is the same linear map, the two pairs having the
   same two maps, by
   `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_add` against the pair `(ε, ε)`, whose
   descended difference vanishes.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_infinitesimalSectionDiff_eq`: **every
  `𝒪_{U₀}`-linear map is the difference from a given section of some section of `Γ₀`** — the
  existence clause of [Stacks Project, Tag 04D0] in this situation.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDifference`: the datum
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference`, built from the
  first order thickening alone.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.bijective_vadd_unitInfinitesimalSection`:
  **Equation (0CKE)** — translation of the unit is a bijection from the `𝒪_{U₀}`-linear maps onto
  `Γ₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.unitVAddEquiv`: the same bijection bundled with
  its inverse.

## Implementation notes

The two statements of Equation (0CKE) are stated here rather than in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsInfinitesimal.lean`, where the
structure `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference` and the
torsor machinery attached to an arbitrary such datum live: that file is at the bottom of this
chain of imports, so the datum built here cannot be named there.  The machinery there carries
the datum as a hypothesis and is untagged; what the tag registers is what is proved here, with
the thickening for its only hypothesis.

The morphism of charts attached to the solution is extracted inside a term-mode `Exists.elim`
rather than by `obtain`: at the shape of these goals the tactic's motive is a deterministic
heartbeat timeout.

## References

* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bas : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Bas)
  (U₀ : ClosedSubspaces C S hS G.objects.1)
  (hU₀ : Space.IsFirstOrderThickening C S hS G.objects U₀.1)

include hU₀ in
/-- **The transported comorphism of the amalgamated section is the moved solution.**

The section `ε ∈ Γ₀` which the chartwise morphisms of the moved solution amalgamate to has, for
its comorphism read through the thickening, that very solution carried back to the ambient site
of `R`; so its transport to the site of `R₀`, the transport being injective, is the solution
`g = δ^♯ − ι ∘ D ∘ j^♯` itself.

The hypothesis `hchart` is the conclusion of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_infinitesimalSection_eq_chartSiteHom`: that
the morphism of charts the solution attaches over an affine chart of `R` is a chart morphism of
`ε`. -/
theorem restrictedSharpThroughThickening_eq_infinitesimalSectionLiftData_g
    (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀)
    (ε : InfinitesimalSections G U₀)
    (hchart : ∀ (V : Space.SmallEtale C S hS G.arrows.1)
      [IsAffine ((BigFppfOver.toScheme C S hS).obj
        ((Space.SmallEtale.toOver C S hS G.arrows.1).obj V))]
      (j : StructuredArrow (op (chartBaseChange C S hS δ.1.1 V))
        (comparisonFunctor C S hS G.objects).op)
      (ψ : (Space.SmallEtale.toOver C S hS G.objects.1).obj j.right.unop ⟶
        (Space.SmallEtale.toOver C S hS G.arrows.1).obj V),
      (BigFppfOver.toScheme C S hS).map ψ =
        thickeningLiftChartHom C S hS U₀ hU₀.1 δ.1.1
          (thickeningLiftOfIndex C S hS U₀ δ.1.1
            (restrictedUnit G U₀ ≫
              subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
            (comp_eq_restrictedUnit_comp G U₀ δ.2)
            (liftRestrictedSharpThroughThickening C S hS U₀
              (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
              (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g)) V j →
      j.right.unop.1.hom ≫ ε.1.1.hom = yoneda.map ψ ≫ V.1.hom) :
    restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
        ε.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ ε.2) =
      (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g := by
  have hA : structureSharpThroughThickeningAt C S hS U₀ ε.1.1
        (restrictedUnit G U₀ ≫
          subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
        (comp_eq_restrictedUnit_comp G U₀ ε.2) =
      liftRestrictedSharpThroughThickening C S hS U₀
        (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
        (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g := by
    refine structureSharpThroughThickeningAt_eq_of_eq_thickeningLiftOfIndex C S hS U₀
      δ.1.1 ε.1.1 _ (comp_eq_restrictedUnit_comp G U₀ δ.2)
      (comp_eq_restrictedUnit_comp G U₀ ε.2) _ ?_
    exact structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom C S hS U₀ hU₀.1
      δ.1.1 ε.1.1 _ _ (infinitesimalSectionLiftData_comp_reduction_eq G U₀ hU₀ δ θ)
      G.source (app_infinitesimalSectionLiftComorphism_eq G U₀ hU₀ δ θ)
      fun Q hQaff j ψ hψ ↦ @hchart Q hQaff j ψ hψ
  exact liftRestrictedSharpThroughThickening_injective C S hS U₀
    (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀) _ _
    ((liftRestrictedSharpThroughThickening_restrictedSharpThroughThickening C S hS U₀
      (preimageSubspace C S hS G.source U₀) ε.1.1 (restrictedUnit G U₀)
      (comp_eq_restrictedUnit_comp G U₀ ε.2)).trans hA)

include hU₀ in
/-- Every `𝒪_{U₀}`-linear map `θ : e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` is the difference
`infinitesimalSectionDiff G U₀ hU₀ δ ε` of a given element `δ` of `Γ₀` and some element `ε` of
`Γ₀`. -/
theorem exists_infinitesimalSectionDiff_eq (δ : InfinitesimalSections G U₀)
    (θ : InfinitesimalSectionsHom G U₀) :
    ∃ ε : InfinitesimalSections G U₀, infinitesimalSectionDiff G U₀ hU₀ δ ε = θ := by
  obtain ⟨ε, hchart⟩ := exists_infinitesimalSection_eq_chartSiteHom G U₀ hU₀ δ θ
  refine ⟨ε, ?_⟩
  have hg :=
    restrictedSharpThroughThickening_eq_infinitesimalSectionLiftData_g G U₀ hU₀ δ θ ε hchart
  rw [infinitesimalSectionDiff_eq G U₀ hU₀ δ ε]
  let := isLocallySurjective_restrictedArrowsSharp G U₀
  have hzero := liftDifferenceDifferentialsHom_eq_zero C S hS
    (preimageProjection C S hS G.source U₀) (restrictedUnit G U₀)
    (conormalModule C S hS G.objects U₀)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ ε ε)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ ε ε)
    ((infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ ε ε).trans
      (infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ ε ε).symm)
  have hadd := liftDifferenceDifferentialsHom_add C S hS
    (preimageProjection C S hS G.source U₀) (restrictedUnit G U₀)
    (conormalModule C S hS G.objects U₀)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ ε)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ ε ε)
    (infinitesimalSectionLiftData G U₀ hU₀ δ θ)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ δ ε)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ ε ε)
    (liftDifferenceDataOfHom_descend_eq_zero C S hS
      (preimageProjection C S hS G.source U₀) (restrictedUnit G U₀)
      (conormalModule C S hS G.objects U₀)
      (E := restrictedSquareZeroValues C S hS U₀ (preimageSubspace C S hS G.source U₀)
        (restrictedUnit G U₀) hU₀)
      (restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
        δ.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ.2))
      (fun _ x m ↦ restrictedSquareZeroValues_ι_smul C S hS U₀
        (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀) hU₀ δ.1.1
        (comp_eq_restrictedUnit_comp G U₀ δ.2) x m) θ)
    ((infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ δ ε).trans
      (infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ ε ε).symm)
    ((infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ δ ε).trans
      (infinitesimalSectionLiftData_f G U₀ hU₀ δ θ).symm)
    ((infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ ε ε).trans hg)
  have hθ := liftDifferenceDifferentialsHom_liftDifferenceDataOfHom C S hS
    (preimageProjection C S hS G.source U₀) (restrictedUnit G U₀)
    (conormalModule C S hS G.objects U₀)
    (E := restrictedSquareZeroValues C S hS U₀ (preimageSubspace C S hS G.source U₀)
      (restrictedUnit G U₀) hU₀)
    (restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
      δ.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ.2))
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul C S hS U₀
      (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀) hU₀ δ.1.1
      (comp_eq_restrictedUnit_comp G U₀ δ.2) x m) θ
  rw [← hadd.trans hθ, hzero, add_zero]

include hU₀ in
/-- **The difference of two sections of `Γ₀`, with the existence and uniqueness of the section
with a given difference.**  All five fields of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference` are proved: the
existence clause is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_infinitesimalSectionDiff_eq` and the
uniqueness half is free, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.existsUnique_infinitesimalSectionDiff_of_exists`.

So the datum is built from the first order thickening alone; nothing is carried. -/
noncomputable def infinitesimalSectionDifference : InfinitesimalSectionDifference G U₀ :=
  infinitesimalSectionDifferenceOfExists G U₀ hU₀ (exists_infinitesimalSectionDiff_eq G U₀ hU₀)

include hU₀ in
/-- **The displayed bijection of Equation (0CKE).**  Translation of the unit is a bijection from
the `𝒪_{U₀}`-linear maps `θ : e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` onto the sections `Γ₀` of the source
which agree with the unit on `U₀`: every `δ ∈ Γ₀` is `θ · e` for exactly one `θ`. -/
@[stacks 0CKE "the displayed bijection Hom_{O_{U_0}}(e_0^*Omega_{R_0/U_0}, C_{U_0/U}) -> \
Gamma_0, theta |-> theta . e, for a groupoid in algebraic spaces and a first order thickening \
U_0 of U"]
theorem bijective_vadd_unitInfinitesimalSection :
    letI := (infinitesimalSectionDifference G U₀ hU₀).addAction
    Function.Bijective
      (fun θ : InfinitesimalSectionsHom G U₀ => θ +ᵥ unitInfinitesimalSection G U₀) :=
  (infinitesimalSectionDifference G U₀ hU₀).bijective_vadd_unitInfinitesimalSection

include hU₀ in
/-- **Equation (0CKE) as a bijection.**  The map `θ ↦ θ · e` from the `𝒪_{U₀}`-linear maps
`e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` to the sections `Γ₀` infinitesimally close to the unit, bundled with
its inverse. -/
@[stacks 0CKE "the displayed arrow Hom_{O_{U_0}}(e_0^*Omega_{R_0/U_0}, C_{U_0/U}) -> Gamma_0 \
bundled as a bijection, for a groupoid in algebraic spaces and a first order thickening U_0 of U"]
noncomputable def unitVAddEquiv :
    InfinitesimalSectionsHom G U₀ ≃ InfinitesimalSections G U₀ :=
  (infinitesimalSectionDifference G U₀ hU₀).unitVAddEquiv

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
