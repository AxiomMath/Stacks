module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionExact
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraExtendScalarsTensor

/-!
# The equivalence of Stacks 08AI is local at the affine charts, over the direct-image algebra

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝒜 = f_*𝒪_Y`.  The first assertion of Stacks 08AI is that `ℱ ↦ f_*ℱ` is
an equivalence from the quasi-coherent `𝒪_Y`-modules onto the quasi-coherent `𝒜`-modules, and
`AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_unit_counit` reduces it to the
invertibility of the unit and the counit of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` at quasi-coherent modules.

This file makes both of those invertibility statements **local at the affine étale charts**, and
supplies the presentation that a chartwise argument about them consumes.  Both are statements
over `𝒜`, which is not a structure sheaf; what makes them available is that the two tools they
need — the joint conservativity of the restrictions to the slices and the existence of a global
presentation on the slice at an affine chart — are both stated in this tree over an **arbitrary**
sheaf of rings on the small étale site, so no comparison of `𝒜` with a structure sheaf is
involved.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_over_affineCharts` — **the restrictions to the slices
  at the affine étale charts jointly reflect isomorphisms of sheaves of modules over an arbitrary
  sheaf of rings on the small étale site of an algebraic space.**
* `AlgebraicGeometry.Space.hasGlobalPresentation_over_affine_chart_directImageAlgebra` — **a
  quasi-coherent `𝒜`-module has a global presentation on the slice at every affine étale chart
  of `X`**, for an affine morphism `f`, with no further hypothesis.
* `AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_over_affineCharts` — the first
  assertion of Stacks 08AI holds as soon as the unit and the counit of the adjunction become
  invertible after restriction to the slice at each affine étale chart.

## Implementation notes

### Why the two tools apply over `𝒜`

`Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionExact.lean`) is the joint
conservativity of restriction to the slices at a family covering the final object, over an
arbitrary sheaf of rings on an arbitrary site; the covering family here is the affine étale
charts, `AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`, which is the geometric input
of the equivalence of conditions (1) and (4) of Stacks 03M0.

`AlgebraicGeometry.Space.hasGlobalPresentation_over_affine_chart`
(`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentOverAlgebraIff.lean`) is likewise stated for
an arbitrary sheaf of rings `A` with a structure map `α : 𝒪_X ⟶ A`, under the single standing
hypothesis that `A` is quasi-coherent as an `𝒪_X`-module.  At `A = 𝒜` that hypothesis is the
first assertion of Stacks 07U8 at the structure sheaf,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage`,
and the second hypothesis — quasi-coherence of the module after restriction of scalars — is the
second assertion of Stacks 08AI,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureSharp_iff`.  So the
presentation over `𝒜` at an affine chart needs nothing beyond affineness of `f`.

### How the unit and the counit are reached chartwise

At an affine étale chart `V` of `X`, the morphism that
`AlgebraicGeometry.Space.isIso_of_isIso_over_affineCharts` tests on the unit is compared, after
transport to the small étale site of the chart, with the unit of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` for the base change
`f_V : V ×_X Y ⟶ V` of `f`.  That base change has a representable target, which is the generality
of the presentation argument: for an affine morphism with representable target, direct image
preserves the colimits of a presentation
(`AlgebraicGeometry.Space.preservesColimit_modulePushforward_of_schemeTarget` and
`AlgebraicGeometry.Space.preservesColimit_moduleDirectImage_of_schemeTarget`), and the unit and
the counit are invertible at a presentation
(`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_of_presentation`
and `...counit_app_of_presentation`), exactly as in the scheme-level case of the tag.  The
presentation on the slice at an affine chart is
`AlgebraicGeometry.Space.hasGlobalPresentation_over_affine_chart_directImageAlgebra` below; it
becomes a `SheafOfModules.Presentation` at a terminal object of the small étale site of a
representable space (`AlgebraicGeometry.Space.isTerminal_isoChart` and
`AlgebraicGeometry.Space.hasGlobalPresentation_of_over_isTerminal`).

The comparison of the restricted unit of `f` with the unit of `f_V` goes through the mate of
étale base change for direct image across the two adjunctions: the restricted unit of `f` is
invertible as soon as the unit of `f_V` and that mate are.  The invertibility of the mate is the
isomorphism `(f_V)^*(𝒢|_V) ≅ (f^*𝒢)|_{V ×_X Y}`, the footnote of Stacks 03LX read over the
direct-image algebras, with the restrictions read as étale restriction.  When the horizontal
functors of the base-change square are left adjoints as well, the mate taken twice is the
conjugate of the original square, so the mate is invertible as soon as the square made of the four
right adjoints is.  That is a square of direct images `i_* ⋙ f_* ⟶ (f_V)_* ⋙ g_*` over `𝒜`,
where `g : V ⟶ X` is the chart and `i : V ×_X Y ⟶ Y` is the base change of `g` along `f`.
Direct image is left exact (`AlgebraicGeometry.Space.preservesFiniteLimits_modulePushforward`),
so only colimits are at stake.

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public section

universe u m

open CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The restrictions to the slices at the affine étale charts jointly reflect isomorphisms.**
For an arbitrary sheaf of rings `R` on the small étale site of an algebraic space `F`, a morphism
of sheaves of `R`-modules whose restriction to the slice at every affine étale chart of `F` is an
isomorphism is an isomorphism.

The affine étale charts cover the final object of the small étale site
(`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`), and restriction to the slices at a
covering family is jointly conservative over any sheaf of rings
(`Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map`).  Neither statement mentions the
structure sheaf, so this applies to modules over the direct-image algebra of Stacks 03G8 as it
stands. -/
theorem isIso_of_isIso_over_affineCharts {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (R : Sheaf (SmallEtale.topology B S hS F) RingCat.{u})
    {M N : SheafOfModules.{m} R} (φ : M ⟶ N)
    (hφ : ∀ V : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V) →
        IsIso ((SheafOfModules.overFunctor.{m} R V).map φ)) :
    IsIso φ :=
  Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map
    (SmallEtale.coversTop_affineCharts B S hS F) φ fun V ↦ hφ V.1 V.2

variable {Y X : AlgebraicSpaces B S hS}

/-- **A quasi-coherent `𝒜`-module has a global presentation on the slice at every affine étale
chart**, for `𝒜 = f_*𝒪_Y` along an affine morphism `f : Y ⟶ X` of algebraic spaces, with no
further hypothesis.

This is `AlgebraicGeometry.Space.hasGlobalPresentation_over_affine_chart` — stated there for an
arbitrary sheaf of rings on the small étale site with a structure map from the structure sheaf —
instantiated at the structure map `f♯ : 𝒪_X ⟶ 𝒜` of Stacks 03G8.  Its two hypotheses are
discharged: the quasi-coherence of `𝒜` as an `𝒪_X`-module is the first assertion of Stacks 07U8
at the structure sheaf, and the quasi-coherence of the module after restriction of scalars along
`f♯` is the second assertion of Stacks 08AI. -/
theorem hasGlobalPresentation_over_affine_chart_directImageAlgebra (f : Y ⟶ X)
    (hf : IsAffineHom B S hS f.hom)
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f))
    (hG : G.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    (SheafOfModules.over G V).HasGlobalPresentation :=
  hasGlobalPresentation_over_affine_chart B S hS (structureSharp B S hS f)
    (isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage B S hS f hf) G
    ((isQuasicoherentOnSite_restrictScalars_structureSharp_iff B S hS f hf G).2 hG) V hV

/-- **The first assertion of Stacks 08AI is local at the affine étale charts.**  For an affine
morphism `f : Y ⟶ X` of algebraic spaces, `AlgebraicGeometry.Space.AffineDirectImageEquivalence`
holds as soon as the unit and the counit of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` become invertible after restriction
to the slice at each affine étale chart — of `X` for the unit, which is a morphism of
`𝒜`-modules, and of `Y` for the counit, which is a morphism of `𝒪_Y`-modules.

The hypothesis `hL` of
`AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_unit_counit` is discharged by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback`, and the two
invertibility hypotheses are the conclusions of
`AlgebraicGeometry.Space.isIso_of_isIso_over_affineCharts`. -/
theorem affineDirectImageEquivalence_of_isIso_over_affineCharts (f : Y ⟶ X)
    (hf : IsAffineHom B S hS f.hom)
    (hunit : ∀ G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      G.IsQuasicoherentOnSite → ∀ V : SmallEtale B S hS X.1,
        IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
          IsIso ((SheafOfModules.overFunctor.{u}
              (structureRingSheafDirectImage B S hS f) V).map
            ((directImageAlgebraPullbackAdjunction B S hS f).unit.app G)))
    (hcounit : ∀ M : Modules.{u, u} B S hS Y.1 Y.2, M.IsQuasicoherentOnSite →
      ∀ W : SmallEtale B S hS Y.1,
        IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
          IsIso ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS Y) W).map
            ((directImageAlgebraPullbackAdjunction B S hS f).counit.app M))) :
    AffineDirectImageEquivalence B S hS f :=
  affineDirectImageEquivalence_of_isIso_unit_counit B S hS f
    (fun G hG ↦ isQuasicoherentOnSite_directImageAlgebraPullback B S hS f hf G hG) hf
    (fun G hG ↦ isIso_of_isIso_over_affineCharts B S hS
      (structureRingSheafDirectImage B S hS f) _ (hunit G hG))
    (fun M hM ↦ isIso_of_isIso_over_affineCharts B S hS
      (structureRingSheaf B S hS Y) _ (hcounit M hM))

end AlgebraicGeometry.Space

end
