module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorFibreBijective

/-!
# Stacks 05VP: the comparison map of stalks is an isomorphism

Let `X` be an algebraic space over a scheme `S`, let `F` be a quasi-coherent `𝒪_X`-module, let
`x̄` be a geometric point of `X` and let `φ : (U, ū) → (X, x̄)` be an étale neighbourhood
whose chart `U` is a scheme.  Stacks 05VP asserts

`(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} = F_{x̄}`,

and this file proves it: the canonical comparison map
`AlgebraicGeometry.Space.chartStalkTensorComparison` is an isomorphism.

`AlgebraicGeometry.Space.bijective_chartStalkTensorFibreComparison` proves the same statement
over the fibre of the structure sheaf at the point of the small étale site, which is where the
descent producing the inverse has to live.  What is done here is the transport of that across
the two comparisons identifying the fibre-level data with the data over the étale local ring,
namely `AlgebraicGeometry.Space.pointStalkRingEquiv` and
`AlgebraicGeometry.Space.chartZariskiFiberIso`.

## Main results

* `AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`: **Stacks 05VP.** For a
  quasi-coherent `𝒪_X`-module the comparison map of Stacks 05VP is an isomorphism.
* `AlgebraicGeometry.Space.chartStalkTensorComparisonAux_eq`: the comparison map is the lift of
  the semilinear map assembled from the fibre-level descent, which is what puts it in the form
  the transport consumes.

## Implementation notes

The statement is at module universe `m = u`, that is for `AlgebraicGeometry.Space.Modules.{u, u}`,
because quasi-coherence enters through
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, which is available
only there.  The comparison map itself is universe-polymorphic in the module universe.

Quasi-coherence is required and is not decoration: without it the comparison map is not
surjective, since the two sides are unrelated away from the chart.

`AlgebraicGeometry.Space.chartStalkTensorComparison` is defined by choosing it from a subtype,
so the semilinear map it lifts is not accessible.  It is therefore restated here as
`AlgebraicGeometry.Space.chartStalkTensorComparisonAux`, the lift of the semilinear map built
from `AlgebraicGeometry.Space.chartZariskiToGeometricFibreData`, and the two are identified by
`ModuleCat.ExtendScalars.hom_ext` on pure tensors `1 ⊗ (germ)` — the only place in the
transport where a cross-spelling conversion occurs, which is why it has a declaration to
itself.  The two semilinear equivalences the transport needs likewise have their own
declarations: for the Zariski stalk the underlying map is the identity and its semilinearity is
the definition of `ModuleCat.restrictScalars`, so it must be read rather than checked.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] ringEquivInvPair ringEquivInvPairSymm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The comparison map of Stacks 05VP, restated as the lift of the semilinear map assembled
from the fibre-level descent.  This is `AlgebraicGeometry.Space.chartStalkTensorComparison`
(see `AlgebraicGeometry.Space.chartStalkTensorComparisonAux_eq`), written so that the
semilinear map it lifts can be named. -/
noncomputable def chartStalkTensorComparisonAux {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX) :
    chartStalkTensorEtaleLocalRing B S hS X hX V F ⟶
      geometricModuleStalk B S hS ⟨X, hX⟩ x F :=
  baseChangeLiftHom (chartLocalRingToEtaleLocalRing B S hS X hX V)
    (chartZariskiModuleStalk B S hS X hX V F)
    (geometricModuleStalk B S hS ⟨X, hX⟩ x F)
    (geometricStalkSemilinear B S hS hX V F
      (chartZariskiToGeometricFibreData B S hS hX V F).1.toAddMonoidHom
      (fun r z => (chartZariskiToGeometricFibreData B S hS hX V F).1.map_smulₛₗ r z))

/-- The local ring of the chart is the fibre of its structure sheaf at the Zariski point, as a
ring equivalence. -/
noncomputable abbrev chartZariskiFibreRingEquiv {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    ↥(chartLocalRing B S hS X V) ≃+* ↥(chartZariskiFiber B S hS V) :=
  (chartZariskiFiberIso B S hS X V).symm.commRingCatIsoToRingEquiv

/-- The Zariski stalk and its form before the scalars are restricted are the same additive
group, semilinearly over `AlgebraicGeometry.Space.chartZariskiFibreRingEquiv`. -/
noncomputable def chartZariskiModuleStalkFibreEquiv {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX) :
    ↥(chartZariskiModuleStalk B S hS X hX V F) ≃ₛₗ[
        (chartZariskiFibreRingEquiv B S hS V).toRingHom]
      ↥(chartZariskiModuleStalkLarge B S hS hX V F) where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl

/-- The additive comparison of the geometric stalk with the stalk before the extension of
scalars is semilinear in the inverse direction too. -/
theorem geometricModuleStalkAddEquiv_symm_smul {x : GeometricPoint B S hS X}
    (F : Modules.{u, u} B S hS X hX) (a : ↥(etaleLocalRing B S hS X x))
    (z : ↥(geometricModuleStalk B S hS ⟨X, hX⟩ x F)) :
    (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).symm (a • z) =
      (pointStalkRingEquiv B S hS ⟨X, hX⟩ x).symm a •
        (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).symm z := by
  apply (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).injective
  refine Eq.trans ((geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).apply_symm_apply (a • z)) ?_
  refine Eq.trans ?_ (geometricModuleStalkAddEquiv_smul B S hS ⟨X, hX⟩ x F
    ((pointStalkRingEquiv B S hS ⟨X, hX⟩ x).symm a)
    ((geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).symm z)).symm
  refine Eq.trans (congrArg (fun c => c • z)
    ((pointStalkRingEquiv B S hS ⟨X, hX⟩ x).apply_symm_apply a).symm) ?_
  exact congrArg (fun w => (pointStalkRingEquiv B S hS ⟨X, hX⟩ x)
      ((pointStalkRingEquiv B S hS ⟨X, hX⟩ x).symm a) • w)
    ((geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).apply_symm_apply z).symm

/-- The geometric stalk and the stalk before the extension of scalars are the same additive
group, semilinearly over the inverse of `AlgebraicGeometry.Space.pointStalkRingEquiv`. -/
noncomputable def geometricModuleStalkFibreEquiv {x : GeometricPoint B S hS X}
    (F : Modules.{u, u} B S hS X hX) :
    ↥(geometricModuleStalk B S hS ⟨X, hX⟩ x F) ≃ₛₗ[
        (pointStalkRingEquiv B S hS ⟨X, hX⟩ x).symm.toRingHom]
      ↥(geometricModuleStalkLarge B S hS hX x F) where
  toFun := (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).symm
  map_add' := map_add (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).symm
  map_smul' := geometricModuleStalkAddEquiv_symm_smul B S hS hX F
  invFun := geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F
  left_inv := (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).apply_symm_apply
  right_inv := (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).symm_apply_apply

/-- The restatement is the comparison map: both send `1 ⊗ (Zariski germ of s)` to the geometric
germ of `s`, and a map out of an extension of scalars is determined by its values on pure
tensors with first factor `1`. -/
theorem chartStalkTensorComparisonAux_eq {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX) :
    chartStalkTensorComparisonAux B S hS hX V F =
      chartStalkTensorComparison B S hS hX V F := by
  refine ModuleCat.ExtendScalars.hom_ext ?_
  intro m
  obtain ⟨W, hw, s, rfl⟩ := chartZariskiSectionGerm_jointly_surjective B S hS hX V F m
  refine Eq.trans (baseChangeLift_tmul (chartLocalRingToEtaleLocalRing B S hS X hX V)
    (chartZariskiModuleStalk B S hS X hX V F)
    _
    1 (chartZariskiSectionGerm B S hS hX V F W hw s)) ?_
  refine Eq.trans (one_smul _ _) ?_
  refine Eq.trans (congrArg (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F)
    ((chartZariskiToGeometricFibreData B S hS hX V F).2 W hw s)) ?_
  exact (chartStalkTensorComparison_germ B S hS hX V F W hw s).symm

/-- The comparison map is bijective, transported from its fibre-level form along the two
comparisons of rings and the two of modules. -/
theorem bijective_chartStalkTensorComparisonAux {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W))) :
    Function.Bijective (chartStalkTensorComparisonAux B S hS hX V F) := by
  refine baseChangeLift_bijective_of_equiv
    (chartLocalRingToEtaleLocalRing B S hS X hX V)
    (chartZariskiFiberToEtaleFiber B S hS hX V)
    (chartZariskiFibreRingEquiv B S hS V)
    (pointStalkRingEquiv B S hS ⟨X, hX⟩ x).symm
    (fun a => congrArg (fun c => (pointStalkRingEquiv B S hS ⟨X, hX⟩ x).symm
        (chartLocalRingToEtaleLocalRing B S hS X hX V c))
      (ConcreteCategory.congr_hom (chartZariskiFiberIso B S hS X V).inv_hom_id a))
    (chartZariskiModuleStalk B S hS X hX V F)
    (chartZariskiModuleStalkLarge B S hS hX V F)
    (chartZariskiModuleStalkFibreEquiv B S hS hX V F)
    (geometricModuleStalkFibreEquiv B S hS hX F)
    _
    (chartZariskiToGeometricFibreData B S hS hX V F).1
    (fun t => ((geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F).symm_apply_apply _).symm)
    (bijective_chartStalkTensorFibreComparison B S hS hX V F W hw hW)

/-- **Stacks 05VP.**  Let `F` be a quasi-coherent `𝒪_X`-module on an algebraic space `X`, let
`x̄` be a geometric point of `X` and let `φ : (U, ū) → (X, x̄)` be an étale neighbourhood whose
chart `U` is a scheme.  Then the canonical comparison map

`(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} → F_{x̄}`

is an isomorphism.

The hypothesis of quasi-coherence is necessary: for a general `𝒪_X`-module the comparison map
is not even surjective.  The statement is at module universe `m = u`, that is for
`AlgebraicGeometry.Space.Modules.{u, u}`, which is where the cartesian criterion of Stacks
03DX(2) that quasi-coherence is used through is available. -/
@[stacks 05VP "the comparison map is an isomorphism"]
theorem isIso_chartStalkTensorComparison {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite] :
    IsIso (chartStalkTensorComparison B S hS hX V F) := by
  obtain ⟨W, hWaff, hw, -⟩ := exists_isAffineOpen_mem_and_subset
    (show chartPoint B S hS X V ∈ (⊤ : (chartScheme V.chart).Opens) from trivial)
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  rw [← chartStalkTensorComparisonAux_eq B S hS hX V F]
  exact bijective_chartStalkTensorComparisonAux B S hS hX V F W hw hWaff


end AlgebraicGeometry.Space

end
