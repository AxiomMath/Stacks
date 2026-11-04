module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePointFibreGerms

/-!
# The germ of a section into the base-changed Zariski stalk

Let `X` be an algebraic space over a scheme `S`, let `F` be an `𝒪_X`-module and let `x̄` be a
geometric point of `X` with small étale neighbourhood `V`.  Inverting the comparison map of
Stacks 05VP means producing, for each small étale neighbourhood `N` of `x̄`, a map from the
sections of `F` over `N` into the base-changed Zariski stalk, compatibly with refinement.  This
file supplies the start of that family: the map attached to a Zariski open `W` of the chart of
`V`, sending a section `t` to `1 ⊗ (germ of t at u)`.

Everything here is formed over `AlgebraicGeometry.Space.étalePointFiber` rather than over the
étale local ring, since that is the universe a descent out of a stalk can land in.

## Main definitions

* `AlgebraicGeometry.Space.chartZariskiFibreTensor` is the tensor product
  `(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` formed over the fibre at the point of the small
  étale site.
* `AlgebraicGeometry.Space.chartAffineTensorGerm` is the map sending a section of `F` over the
  étale chart of a Zariski open `W ∋ u` to `1 ⊗ (germ at u)`, semilinear along
  `AlgebraicGeometry.Space.chartOpenRingGerm`.
* `AlgebraicGeometry.Space.affineRingGermHom` is the same map read as semilinear along the
  composite with restriction to a refinement, which is the shape
  `AlgebraicGeometry.Space.baseChangeDesc` consumes.

## Main results

* `AlgebraicGeometry.Space.chartRestrictionRingHom_app_topIso` and
  `AlgebraicGeometry.Space.chartZariskiFiberToEtaleFiber_topIso`: a regular function on the
  étale chart of a Zariski open of the chart is the restriction of its own transport along
  `TopologicalSpace.Opens.topIso`, and the fibre comparison sends the Zariski class of that
  transport to the germ of the function at the geometric point.
* `AlgebraicGeometry.Space.chartZariskiSectionGermLarge_smul'`: the Zariski germ map is
  semilinear along the Zariski class of that transport.

## Implementation notes

Three ascribed `abbrev`s carry the whole file:
`AlgebraicGeometry.Space.chartOpenRingGerm`, `AlgebraicGeometry.Space.chartOpenRestrict` and
`AlgebraicGeometry.Space.chartZariskiFibreTensor`.  Their bodies are terms one could write
inline, but the chart of
`AlgebraicGeometry.Space.chartOpenNeighborhood` and the étale chart of a Zariski open are the
same object under two spellings, and scalar-action instance search finds a module structure only
for the second; declaring the type on an `abbrev` is what makes the semilinear maps below
elaborate at all.

The semilinearity of `AlgebraicGeometry.Space.chartAffineTensorGerm` needs the `R`-module
structure on the fibre which the extension of scalars uses, and that structure is not an
instance; it is supplied locally as `Module.compHom`, which is the term the pure-tensor notation
itself writes down, so the two agree syntactically and `TensorProduct.smul_tmul` applies.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The left-hand side of Stacks 05VP formed over the fibre of the structure sheaf at the
point of the small étale site rather than over the étale local ring.  Its sections live one
universe lower, which is what lets a descent out of a stalk land in it. -/
noncomputable abbrev chartZariskiFibreTensor {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX) :
    ModuleCat.{u} ↥(etalePointFiber B S hS hX x) :=
  (ModuleCat.extendScalars (chartZariskiFiberToEtaleFiber B S hS hX V)).obj
    (chartZariskiModuleStalkLarge B S hS hX V F)

/-- A regular function on the étale chart of a Zariski open of the chart is the restriction of
its transport along `TopologicalSpace.Opens.topIso`. -/
theorem chartRestrictionRingHom_app_topIso {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (a : chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W)) :
    ((chartRestrictionRingHom B S hS hX V.chart).app (op W)).hom (W.topIso.hom a) = a :=
  (chartRestrictionRingHom_app_apply B S hS hX V W (W.topIso.hom a)).trans
    (ConcreteCategory.congr_hom W.topIso.hom_inv_id a)

/-- The comparison of the two fibres sends the Zariski class of a function transported along
`TopologicalSpace.Opens.topIso` to the germ of that function at the geometric point, read on
the small étale neighbourhood the open defines. -/
theorem chartZariskiFiberToEtaleFiber_topIso {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W)
    (a : chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W)) :
    chartZariskiFiberToEtaleFiber B S hS hX V
        ((chartZariskiPoint B S hS X V).toPresheafFiber W ⟨⟨hw⟩⟩
          (chartZariskiRingSheaf B S hS V).obj (W.topIso.hom a)) =
      pointRingGerm B S hS hX (chartOpenNeighborhood B S hS V W hw) a :=
  (chartZariskiFiberToEtaleFiber_apply B S hS hX V W hw (W.topIso.hom a)).trans
    (congrArg (pointRingGerm B S hS hX (chartOpenNeighborhood B S hS V W hw))
      (chartRestrictionRingHom_app_topIso B S hS hX V W a))

/-- The Zariski germ map is semilinear along the Zariski class of a regular function on the
étale chart of the open, transported along `TopologicalSpace.Opens.topIso`. -/
theorem chartZariskiSectionGermLarge_smul' {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (a : chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W))
    (t : F.val.obj (op ((chartOpens B S hS V.chart).obj W))) :
    chartZariskiSectionGermLarge B S hS hX V F W hw (a • t) =
      (chartZariskiPoint B S hS X V).toPresheafFiber W ⟨⟨hw⟩⟩
          (chartZariskiRingSheaf B S hS V).obj (W.topIso.hom a) •
        chartZariskiSectionGermLarge B S hS hX V F W hw t := by
  refine Eq.trans (congrArg (chartZariskiSectionGermLarge B S hS hX V F W hw)
    (congrArg (fun y => y • t) (chartRestrictionRingHom_app_topIso B S hS hX V W a).symm)) ?_
  exact chartZariskiSectionGermLarge_smul B S hS hX V F W hw (W.topIso.hom a) t

/-- The germ map of regular functions on the étale chart of a Zariski open of the chart,
declared with that chart as its source so that instance search finds the module structures on
the sections over it. -/
noncomputable abbrev chartOpenRingGerm {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) :
    chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W) →+*
      ↥(etalePointFiber B S hS hX x) :=
  pointRingGerm B S hS hX (chartOpenNeighborhood B S hS V W hw)

/-- **The germ of a section into the base-changed Zariski stalk.**  A section of `F` over the
étale chart of a Zariski open `W` of the chart containing the point is sent to `1` tensored with
its Zariski germ at that point.  The map is semilinear along the germ map of regular
functions. -/
noncomputable def chartAffineTensorGerm {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    F.val.obj (op ((chartOpens B S hS V.chart).obj W)) →ₛₗ[
        chartOpenRingGerm B S hS hX V W hw]
      ↥(chartZariskiFibreTensor B S hS hX V F) where
  toFun t := (1 : ↥(etalePointFiber B S hS hX x)) ⊗ₜ[↥(chartZariskiFiber B S hS V),
      chartZariskiFiberToEtaleFiber B S hS hX V]
    chartZariskiSectionGermLarge B S hS hX V F W hw t
  map_add' t t' := by
    let : Module ↥(chartZariskiFiber B S hS V) ↥(etalePointFiber B S hS hX x) :=
      Module.compHom _ (chartZariskiFiberToEtaleFiber B S hS hX V)
    refine Eq.trans (congrArg (fun z => (1 : ↥(etalePointFiber B S hS hX x)) ⊗ₜ[
      ↥(chartZariskiFiber B S hS V), chartZariskiFiberToEtaleFiber B S hS hX V] z)
      (map_add (chartZariskiSectionGermLarge B S hS hX V F W hw) t t')) ?_
    exact TensorProduct.tmul_add _ _ _
  map_smul' a t := by
    let : Module ↥(chartZariskiFiber B S hS V) ↥(etalePointFiber B S hS hX x) :=
      Module.compHom _ (chartZariskiFiberToEtaleFiber B S hS hX V)
    refine Eq.trans (congrArg (fun z => (1 : ↥(etalePointFiber B S hS hX x)) ⊗ₜ[
      ↥(chartZariskiFiber B S hS V), chartZariskiFiberToEtaleFiber B S hS hX V] z)
      (chartZariskiSectionGermLarge_smul' B S hS hX V F W hw a t)) ?_
    refine Eq.trans (TensorProduct.smul_tmul
      ((chartZariskiPoint B S hS X V).toPresheafFiber W ⟨⟨hw⟩⟩
        (chartZariskiRingSheaf B S hS V).obj (W.topIso.hom a))
      (1 : ↥(etalePointFiber B S hS hX x))
      (chartZariskiSectionGermLarge B S hS hX V F W hw t)).symm ?_
    refine Eq.trans ?_ (ModuleCat.ExtendScalars.smul_tmul
      (chartZariskiFiberToEtaleFiber B S hS hX V)
      (pointRingGerm B S hS hX (chartOpenNeighborhood B S hS V W hw) a)
      (1 : ↥(etalePointFiber B S hS hX x))
      (chartZariskiSectionGermLarge B S hS hX V F W hw t)).symm
    exact congrArg (fun y => y ⊗ₜ[↥(chartZariskiFiber B S hS V),
        chartZariskiFiberToEtaleFiber B S hS hX V]
        chartZariskiSectionGermLarge B S hS hX V F W hw t)
      (congrArg (fun y => y * (1 : ↥(etalePointFiber B S hS hX x)))
        (chartZariskiFiberToEtaleFiber_topIso B S hS hX V W hw a))

/-- Restriction of regular functions along a refinement of the small étale neighbourhood given
by a Zariski open of the chart, declared with that open's étale chart as its source. -/
noncomputable abbrev chartOpenRestrict {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) {N : SmallEtaleNeighborhood x}
    (φ : N ⟶ chartOpenNeighborhood B S hS V W hw) :
    chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W) →+*
      chartRing B S hS X hX N.chart :=
  chartRestrict (hF := hX) φ.hom

/-- `AlgebraicGeometry.Space.chartAffineTensorGerm` read as semilinear along the composite of
the germ map at a refinement with restriction to it.  This is the shape in which
`AlgebraicGeometry.Space.baseChangeDesc` consumes it. -/
noncomputable def affineRingGermHom {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    {N : SmallEtaleNeighborhood x} (φ : N ⟶ chartOpenNeighborhood B S hS V W hw) :
    F.val.obj (op ((chartOpens B S hS V.chart).obj W)) →ₛₗ[
        (pointRingGerm B S hS hX N).comp (chartOpenRestrict B S hS hX V W hw φ)]
      ↥(chartZariskiFibreTensor B S hS hX V F) :=
  { chartAffineTensorGerm B S hS hX V F W hw with
    map_smul' := fun c t => Eq.trans
      ((chartAffineTensorGerm B S hS hX V F W hw).map_smul' c t)
      (congrArg (fun y => y • chartAffineTensorGerm B S hS hX V F W hw t)
        (pointRingGerm_map B S hS hX φ c).symm) }


end AlgebraicGeometry.Space

end
