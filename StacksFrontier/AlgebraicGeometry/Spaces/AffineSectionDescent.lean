module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartAffineTensorGerm

/-!
# Germs of sections over an affine refinement, by descent along the cartesian property

Let `X` be an algebraic space over a scheme `S`, let `F` be a quasi-coherent `𝒪_X`-module and
let `x̄` be a geometric point with small étale neighbourhood `V`. Fix a Zariski open `W` of the
chart of `V` containing the point under the chosen lift, whose étale chart is affine, and write
`U_0` for the small étale neighbourhood it defines. For a small étale neighbourhood `N` with
affine chart lying over `U_0`, the sections of `F` over `N` are the base change of the sections
over `U_0`, by Stacks 03DX(2); so the germ map
`AlgebraicGeometry.Space.chartAffineTensorGerm` on `U_0` extends uniquely to `N`.

This file constructs that extension and shows it is compatible with refinement.

## Main definitions

* `AlgebraicGeometry.Space.affineSectionDesc` is the extension of the germ map to an affine
  neighbourhood lying over `U_0`.
* `AlgebraicGeometry.Space.affineSectionDescComp` is that map precomposed with restriction along
  a refinement, as a semilinear map.

## Main results

* `AlgebraicGeometry.Space.affineSectionDesc_restrict`: the extension agrees with
  `AlgebraicGeometry.Space.chartAffineTensorGerm` on restricted sections.
* `AlgebraicGeometry.Space.affineSectionDesc_map`: the extensions attached to two affine
  neighbourhoods over `U_0` agree on a refinement which commutes over `U_0`.

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

/-- The algebra structure on the regular functions of a refinement over the étale chart of a
Zariski open of the chart, declared with that chart as the base ring. -/
noncomputable abbrev chartOpenAlgebra {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) {N : SmallEtaleNeighborhood x}
    (φ : N ⟶ chartOpenNeighborhood B S hS V W hw) :
    Algebra (chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W))
      (chartRing B S hS X hX N.chart) :=
  chartAlgebra (hF := hX) φ.hom

/-- The module structure on the sections over a refinement given by restriction of scalars,
declared over the regular functions on the étale chart of the open. -/
noncomputable abbrev chartOpenSectionsModule {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    {N : SmallEtaleNeighborhood x} (φ : N ⟶ chartOpenNeighborhood B S hS V W hw) :
    Module (chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W))
      (F.val.obj (op N.chart)) :=
  chartSectionsModule F φ.hom

/-- Restriction of sections along a refinement, declared as a linear map over the regular
functions on the étale chart of the open. -/
noncomputable abbrev chartOpenRestrictLinear {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    {N : SmallEtaleNeighborhood x} (φ : N ⟶ chartOpenNeighborhood B S hS V W hw) :
    letI := chartOpenAlgebra B S hS hX V W hw φ
    letI := chartOpenSectionsModule B S hS hX V F W hw φ
    (F.val.obj (op ((chartOpens B S hS V.chart).obj W)) : Type u) →ₗ[
        chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W)]
      (F.val.obj (op N.chart) : Type u) :=
  chartRestrictLinear F φ.hom

/-- **The germ of a section over an affine refinement.** For a small étale neighbourhood `N`
with affine chart lying over the affine neighbourhood given by a Zariski open `W` of the chart,
the sections of a quasi-coherent `𝒪_X`-module over `N` are the base change of the sections over
that neighbourhood, so the germ map on `W` extends uniquely to `N`. -/
noncomputable def affineSectionDesc {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    {N : SmallEtaleNeighborhood x} (φ : N ⟶ chartOpenNeighborhood B S hS V W hw)
    (hN : IsAffine (chartScheme N.chart)) :
    F.val.obj (op N.chart) →ₛₗ[pointRingGerm B S hS hX N]
      ↥(chartZariskiFibreTensor B S hS hX V F) := by
  letI := chartOpenAlgebra B S hS hX V W hw φ
  letI := chartOpenSectionsModule B S hS hX V F W hw φ
  letI : IsScalarTower (chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W))
      (chartRing B S hS X hX N.chart) (F.val.obj (op N.chart)) :=
    chartSections_isScalarTower F φ.hom
  have hbij : Function.Bijective ((chartOpenRestrictLinear B S hS hX V F W hw φ).liftBaseChange
      (chartRing B S hS X hX N.chart)) :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX F inferInstance
      ((chartOpens B S hS V.chart).obj W) N.chart hW hN φ.hom
  exact baseChangeDesc (chartOpenRestrictLinear B S hS hX V F W hw φ) hbij
    (pointRingGerm B S hS hX N) (affineRingGermHom B S hS hX V F W hw φ)

/-- The extended germ map agrees with `AlgebraicGeometry.Space.chartAffineTensorGerm` on
sections restricted from the open. -/
theorem affineSectionDesc_restrict {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    {N : SmallEtaleNeighborhood x} (φ : N ⟶ chartOpenNeighborhood B S hS V W hw)
    (hN : IsAffine (chartScheme N.chart))
    (t : F.val.obj (op ((chartOpens B S hS V.chart).obj W))) :
    affineSectionDesc B S hS hX V F W hw hW φ hN (F.val.map φ.hom.op t) =
      chartAffineTensorGerm B S hS hX V F W hw t := by
  let := chartOpenAlgebra B S hS hX V W hw φ
  let := chartOpenSectionsModule B S hS hX V F W hw φ
  let : IsScalarTower (chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W))
      (chartRing B S hS X hX N.chart) (F.val.obj (op N.chart)) :=
    chartSections_isScalarTower F φ.hom
  exact baseChangeDesc_apply _ _ _ _ t

/-- The extended germ map `AlgebraicGeometry.Space.affineSectionDesc` on `N` precomposed with
restriction of sections along a refinement `k : N ⟶ M`, as a semilinear map along the germ map
of the regular functions on `M`. -/
noncomputable def affineSectionDescComp {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    {M N : SmallEtaleNeighborhood x} (φ : N ⟶ chartOpenNeighborhood B S hS V W hw)
    (hN : IsAffine (chartScheme N.chart)) (k : N ⟶ M) :
    F.val.obj (op M.chart) →ₛₗ[pointRingGerm B S hS hX M]
      ↥(chartZariskiFibreTensor B S hS hX V F) where
  toFun s := affineSectionDesc B S hS hX V F W hw hW φ hN (F.val.map k.hom.op s)
  map_add' s s' := by
    refine Eq.trans (congrArg (affineSectionDesc B S hS hX V F W hw hW φ hN)
      (map_add (ConcreteCategory.hom (F.val.map k.hom.op)) s s')) ?_
    exact map_add (affineSectionDesc B S hS hX V F W hw hW φ hN) _ _
  map_smul' a s := by
    refine Eq.trans (congrArg (affineSectionDesc B S hS hX V F W hw hW φ hN)
      (F.val.map_smul k.hom.op a s)) ?_
    refine Eq.trans ((affineSectionDesc B S hS hX V F W hw hW φ hN).map_smulₛₗ
      (chartRestrict (hF := hX) k.hom a) (F.val.map k.hom.op s)) ?_
    exact congrArg (fun y => y •
        affineSectionDesc B S hS hX V F W hw hW φ hN (F.val.map k.hom.op s))
      (pointRingGerm_map B S hS hX k a)

/-- **The extended germ maps are compatible with refinement.** The maps attached to two affine
neighbourhoods `N` and `M` over the fixed one agree along any refinement `k : N ⟶ M` which
commutes over it. -/
theorem affineSectionDesc_map {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    {M N : SmallEtaleNeighborhood x} (φ : N ⟶ chartOpenNeighborhood B S hS V W hw)
    (hN : IsAffine (chartScheme N.chart))
    (ψ : M ⟶ chartOpenNeighborhood B S hS V W hw) (hM : IsAffine (chartScheme M.chart))
    (k : N ⟶ M) (hk : k ≫ ψ = φ) (s : F.val.obj (op M.chart)) :
    affineSectionDesc B S hS hX V F W hw hW φ hN (F.val.map k.hom.op s) =
      affineSectionDesc B S hS hX V F W hw hW ψ hM s := by
  let := chartOpenAlgebra B S hS hX V W hw ψ
  let := chartOpenSectionsModule B S hS hX V F W hw ψ
  let : IsScalarTower (chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W))
      (chartRing B S hS X hX M.chart) (F.val.obj (op M.chart)) :=
    chartSections_isScalarTower F ψ.hom
  have hbij : Function.Bijective ((chartOpenRestrictLinear B S hS hX V F W hw ψ).liftBaseChange
      (chartRing B S hS X hX M.chart)) :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX F inferInstance
      ((chartOpens B S hS V.chart).obj W) M.chart hW hM ψ.hom
  have hhom : ψ.hom.op ≫ k.hom.op = φ.hom.op :=
    congrArg (fun l => (SmallEtaleNeighborhood.Hom.hom l).op) hk
  have he : ∀ t : F.val.obj (op ((chartOpens B S hS V.chart).obj W)),
      affineSectionDescComp B S hS hX V F W hw hW φ hN k
          (chartOpenRestrictLinear B S hS hX V F W hw ψ t) =
        affineSectionDesc B S hS hX V F W hw hW ψ hM
          (chartOpenRestrictLinear B S hS hX V F W hw ψ t) := by
    intro t
    have hcomp : F.val.map k.hom.op (F.val.map ψ.hom.op t) = F.val.map φ.hom.op t := by
      refine Eq.trans (ConcreteCategory.comp_apply (F.val.presheaf.map ψ.hom.op)
        (F.val.presheaf.map k.hom.op) t).symm ?_
      exact ConcreteCategory.congr_hom
        ((F.val.presheaf.map_comp ψ.hom.op k.hom.op).symm.trans
          (congrArg F.val.presheaf.map hhom)) t
    exact (congrArg (affineSectionDesc B S hS hX V F W hw hW φ hN) hcomp).trans
      ((affineSectionDesc_restrict B S hS hX V F W hw hW φ hN t).trans
        (affineSectionDesc_restrict B S hS hX V F W hw hW ψ hM t).symm)
  exact DFunLike.congr_fun (baseChangeDesc_unique
    (chartOpenRestrictLinear B S hS hX V F W hw ψ) hbij (pointRingGerm B S hS hX M)
    (affineSectionDescComp B S hS hX V F W hw hW φ hN k)
    (affineSectionDesc B S hS hX V F W hw hW ψ hM) he) s

end AlgebraicGeometry.Space

end
