module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport

/-!
# The comparison map of Stacks 05VP is surjective for a quasi-coherent module

Let `X` be an algebraic space over a scheme `S`, let `F` be a quasi-coherent `𝒪_X`-module, let
`x̄` be a geometric point of `X` and let `V` be a small étale neighbourhood of `x̄` whose chart
is a scheme `U`.  Stacks 05VP asserts that the comparison map
`AlgebraicGeometry.Space.chartStalkTensorComparison`

`(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} → F_{x̄}`

is an isomorphism.  This file proves that it is surjective, which is the half of that assertion
carried by quasi-coherence in the form of Stacks 03DX(2): a quasi-coherent module is cartesian
on affine charts, so every section over a small affine étale neighbourhood is a sum of
multiples of restrictions of sections over a fixed one.

## Main results

* `AlgebraicGeometry.Space.surjective_chartStalkTensorComparison`: for a quasi-coherent `F` the
  comparison map of Stacks 05VP is surjective.

## Implementation notes

The hypothesis is `SheafOfModules.IsQuasicoherentOnSite F`, and it is needed: with no
hypothesis on `F` the comparison map is not surjective, since the two sides are then unrelated
away from the chart.  It enters exactly once, through
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, which is Stacks
03DX(2) for the small étale site.

The statement is at module universe `m = u`, that is for `AlgebraicGeometry.Space.Modules.{u, u}`,
because the cartesian criterion
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` is available only
there; `AlgebraicGeometry.Space.chartStalkTensorComparison` itself is universe-polymorphic in the
module universe.

The argument runs over germs.  An affine open `W₀` of the chart containing the point under the
chosen lift gives a small étale neighbourhood `U₀` with affine chart
(`AlgebraicGeometry.Space.chartOpenNeighborhood`), and
`AlgebraicGeometry.Space.chartStalkTensorComparison_germ` puts every germ of a section over `U₀`
in the range of the comparison.  An arbitrary neighbourhood is refined by one lying over `U₀`
(the neighbourhoods are cofiltered) and that refinement by an affine one
(`AlgebraicGeometry.Space.exists_smallEtaleNeighborhoodHom_isAffine`); the cartesian property of
the resulting morphism of affine charts writes the restricted section as a sum of multiples of
restrictions from `U₀`, and the range is a submodule, so the germ of the original section lies
in it.  Joint surjectivity of the geometric germ maps
(`AlgebraicGeometry.Space.geometricModuleStalkGerm_jointly_surjective`) finishes it.

What is *not* here is injectivity, which needs the inverse map: a descent of the family of
section-level descents `F(N) → (φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` over the affine neighbourhoods
lying over `U₀`, along the cofinality of that family.  So no isomorphism is asserted here.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- **The comparison map of Stacks 05VP is surjective for a quasi-coherent module.**  Every germ
at the geometric point of a section of a quasi-coherent `𝒪_X`-module is the image of a base
changed Zariski germ on the chart.

Quasi-coherence is required: it enters through Stacks 03DX(2), which writes a section over a
small affine étale neighbourhood as a sum of multiples of restrictions of sections over a fixed
affine neighbourhood of the point. -/
@[stacks 05VP "the comparison map is surjective for a quasi-coherent module"]
theorem surjective_chartStalkTensorComparison {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] :
    Function.Surjective (chartStalkTensorComparison B S hS hX V F) := by
  have : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS X hX x
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX F inferInstance
  obtain ⟨W₀, hW₀, hw₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (show chartPoint B S hS X V ∈ (⊤ : (chartScheme V.chart).Opens) from trivial)
  let U₀ := chartOpenNeighborhood B S hS V W₀ hw₀
  have hU₀aff : IsAffine (chartScheme U₀.chart) := hW₀
  let R := LinearMap.range (chartStalkTensorComparison B S hS hX V F).hom
  have hU₀ : ∀ t : F.val.obj (op U₀.chart),
      geometricModuleStalkGerm B S hS ⟨X, hX⟩ x F U₀ t ∈ R :=
    fun t => ⟨_, chartStalkTensorComparison_germ B S hS hX V F W₀ hw₀ t⟩
  have key : ∀ (N : SmallEtaleNeighborhood x) (s : F.val.obj (op N.chart)),
      geometricModuleStalkGerm B S hS ⟨X, hX⟩ x F N s ∈ R := by
    intro N s
    obtain ⟨M₀, gN, gU, -⟩ := IsCofilteredOrEmpty.cone_objs N U₀
    obtain ⟨M, gM, hMaff⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS ⟨X, hX⟩ x M₀
    let := chartAlgebra (B := B) (S := S) (hS := hS) (hF := hX) (gM ≫ gU).hom
    have hbij := hcart U₀.chart M.chart hU₀aff hMaff (gM ≫ gU).hom
    obtain ⟨w, hw⟩ := hbij.2 (F.val.map (gM ≫ gN).hom.op s)
    have hkey : ∀ w', geometricModuleStalkGerm B S hS ⟨X, hX⟩ x F M
        (sectionsBaseChange F (gM ≫ gU).hom w') ∈ R := by
      intro w'
      induction w' using TensorProduct.induction_on with
      | zero => simpa only [map_zero] using Submodule.zero_mem R
      | add a b ha hb => simpa only [map_add] using Submodule.add_mem R ha hb
      | tmul b t =>
        have hb : geometricModuleStalkGerm B S hS ⟨X, hX⟩ x F M
              (sectionsBaseChange F (gM ≫ gU).hom (TensorProduct.tmul _ b t)) =
            etaleLocalRingGerm B S hS X x (op M) b •
              geometricModuleStalkGerm B S hS ⟨X, hX⟩ x F U₀ t := by
          refine Eq.trans (congrArg (geometricModuleStalkGerm B S hS ⟨X, hX⟩ x F M)
            (chartBaseChange_tmul F (gM ≫ gU).hom b t)) ?_
          refine Eq.trans (geometricModuleStalkGerm_smul B S hS ⟨X, hX⟩ x F M b
            (F.val.map (gM ≫ gU).hom.op t)) ?_
          exact congrArg (fun y => etaleLocalRingGerm B S hS X x (op M) b • y)
            (geometricModuleStalkGerm_map B S hS ⟨X, hX⟩ x F (gM ≫ gU) t)
        rw [hb]
        exact Submodule.smul_mem R _ (hU₀ t)
    have h2 := hkey w
    rw [hw, geometricModuleStalkGerm_map] at h2
    exact h2
  intro z
  obtain ⟨N, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS ⟨X, hX⟩ x F z
  exact key N s

end AlgebraicGeometry.Space

end
