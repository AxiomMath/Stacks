module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingGermsOnOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkGerm

/-!
# The comparison map of Stacks 05VP

Let `X` be an algebraic space over a scheme `S`, let `F` be an `𝒪_X`-module, let `x̄` be a
geometric point of `X` and let `V` be a small étale neighbourhood of `x̄` whose chart is a scheme
`U`. Stacks 05VP compares the base change of the Zariski stalk of `F` on the chart with the
geometric stalk of `F`:

`(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}  →  F_{x̄}`.

This file constructs that comparison map and computes it on germs: the base change of the Zariski
germ of a section of `F` over a Zariski open `W` of the chart containing `u` is the geometric germ
of the same section at `x̄`, read on the small étale neighbourhood `W`. The map is defined for an
arbitrary `𝒪_X`-module; it is an isomorphism when `F` is quasi-coherent.

## Main definitions

* `AlgebraicGeometry.Space.chartStalkTensorComparison` is the comparison map of Stacks 05VP.
* `AlgebraicGeometry.Space.baseChangeLift` and `AlgebraicGeometry.Space.baseChangeLiftHom` lift a
  semilinear map along a ring map to the extension of scalars, with the source and target module
  universes independent.
* `AlgebraicGeometry.Space.chartZariskiFiberToEtaleFiber` is the ring map from the fibre of the
  structure sheaf of the chart at the Zariski point to the fibre of the structure sheaf of the
  algebraic space at the geometric point.
* `AlgebraicGeometry.Space.chartOpenGeometricGerm` is the family of geometric germ maps on the
  sections of `F` over the Zariski opens of the chart, and
  `AlgebraicGeometry.Space.geometricStalkSemilinear` assembles their descent into a semilinear
  map out of the Zariski stalk.
* `AlgebraicGeometry.Space.chartOpenNeighborhoodMap` is the morphism of small étale
  neighbourhoods induced by an inclusion of Zariski opens of the chart.

## Main results

* `AlgebraicGeometry.Space.chartStalkTensorComparison_germ`: the comparison map sends the base
  change of the Zariski germ of a section to its geometric germ.
* `AlgebraicGeometry.Space.chartZariskiFiberToEtaleFiber_apply`: that ring map sends the class of
  a regular function on a Zariski open of the chart to the class of its restriction.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ChangeOfRings

universe u m

namespace AlgebraicGeometry.Space

section BaseChange

universe r k c n

/-- The `A`-linear map `A ⊗_R M → N`, `a ⊗ s ↦ a • g s`, induced by a map `g : M → N` which is
semilinear along a ring map `f : R →+* A`. -/
noncomputable def baseChangeLift {R : Type r} {A : Type k} [CommRing R] [CommRing A]
    (f : R →+* A) (M : ModuleCat.{c} R) {N : Type n} [AddCommGroup N] [Module A N]
    (g : M →ₛₗ[f] N) :
    (ModuleCat.extendScalars f).obj M →ₗ[A] N :=
  letI : Algebra R A := f.toAlgebra
  letI : Module R N := Module.compHom N f
  letI : IsScalarTower R A N := ⟨fun r a n => mul_smul (f r) a n⟩
  letI : IsScalarTower R A ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A)) :=
    ⟨fun r a b => mul_assoc (f r) a b⟩
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton A (M →ₗ[R] N) { g with map_smul' := g.map_smul' })

/-- The lift of a semilinear map sends a pure tensor to the scalar acting on the value. -/
theorem baseChangeLift_tmul {R : Type r} {A : Type k} [CommRing R] [CommRing A]
    (f : R →+* A) (M : ModuleCat.{c} R) {N : Type n} [AddCommGroup N] [Module A N]
    (g : M →ₛₗ[f] N) (a : A) (s : M) :
    baseChangeLift f M g (a ⊗ₜ[R, f] s) = a • g s := rfl

/-- **The lift of a semilinear map to the extension of scalars.** A map `M → N` which is
semilinear along a ring map `f : R →+* A`, from an `R`-module to an `A`-module, extends to an
`A`-linear map out of `A ⊗_R M`.  The universes of `M` and `N` are independent of each other
and of the two rings. -/
noncomputable def baseChangeLiftHom {R : Type r} {A : Type k} [CommRing R] [CommRing A]
    (f : R →+* A) (M : ModuleCat.{c} R) (N : ModuleCat.{max k c} A) (g : M →ₛₗ[f] N) :
    (ModuleCat.extendScalars f).obj M ⟶ N :=
  ModuleCat.homEquiv.symm (baseChangeLift f M g)

end BaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- An inclusion of Zariski opens of the chart of a small étale neighbourhood, both containing
the point under the chosen lift, as a morphism of small étale neighbourhoods. -/
noncomputable def chartOpenNeighborhoodMap {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) {W W' : (chartScheme V.chart).Opens} (i : W' ⟶ W)
    (hw' : chartPoint B S hS X V ∈ W') (hw : chartPoint B S hS X V ∈ W) :
    chartOpenNeighborhood B S hS V W' hw' ⟶ chartOpenNeighborhood B S hS V W hw where
  hom := (chartOpens B S hS V.chart).map i
  point_comp := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    refine (cancel_mono W.ι).1 ?_
    change (chartOpenLift B S hS V W' hw' ≫ (chartScheme V.chart).homOfLE i.le) ≫ W.ι =
      chartOpenLift B S hS V W hw ≫ W.ι
    rw [Category.assoc, Scheme.homOfLE_ι, chartOpenLift_comp, chartOpenLift_comp]

/-- The structure sheaf of the scheme underlying a small étale neighbourhood, read as a sheaf
of commutative rings on its site of Zariski opens. -/
abbrev chartZariskiRingSheaf {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x) :
    Sheaf (Opens.grothendieckTopology (chartScheme V.chart)) CommRingCat.{u} :=
  (chartScheme V.chart).sheaf

/-- The fibre of the structure sheaf of the chart at the point of the Zariski site under the
chosen lift of the geometric point.  It is the local ring `𝒪_{U, u}` up to
`AlgebraicGeometry.Space.chartZariskiFiberIso`. -/
noncomputable abbrev chartZariskiFiber {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) : CommRingCat.{u} :=
  ((chartZariskiPoint B S hS X V).presheafFiber (A := CommRingCat.{u})).obj
    (chartZariskiRingSheaf B S hS V).obj

/-- The Zariski stalk of the restriction of an `𝒪_X`-module to the chart, before its scalars
are restricted to the local ring of the chart. -/
noncomputable abbrev chartZariskiModuleStalkLarge {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX) :
    ModuleCat.{max u m} (chartZariskiFiber B S hS V) :=
  Stacks.moduleStalkLarge (chartZariskiPoint B S hS X V) (chartZariskiRingSheaf B S hS V)
    (restrictToChart B S hS hX F V.chart)

/-- The stalk of an `𝒪_X`-module at the point of the small étale site determined by a
geometric point, before its scalars are extended to the étale local ring. Its module sections
live in `max u m`. -/
noncomputable abbrev geometricModuleStalkLarge (x : GeometricPoint B S hS X)
    (F : Modules.{u, m} B S hS X hX) :
    ModuleCat.{max u m} (((etaleSitePoint B S hS X x hX).presheafFiber
      (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O.obj) :=
  Stacks.moduleStalkLarge (etaleSitePoint B S hS X x hX)
    (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F

/-- The ring map from the fibre of the structure sheaf of the chart at the Zariski point to the
fibre of the structure sheaf of the algebraic space at the geometric point: the comparison map
`𝒪_{U, u} → 𝒪_{X, x̄}` of Stacks 05VP, read between the two fibres. -/
noncomputable def chartZariskiFiberToEtaleFiber {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    (((chartZariskiPoint B S hS X V).presheafFiber (A := CommRingCat.{u})).obj
        (chartZariskiRingSheaf B S hS V).obj) →+*
      (((etaleSitePoint B S hS X x hX).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O.obj) :=
  ((pointStalkRingEquiv B S hS ⟨X, hX⟩ x).symm.toRingHom).comp
    ((chartLocalRingToEtaleLocalRing B S hS X hX V).comp
      (chartZariskiFiberIso B S hS X V).hom.hom)

/-- The comparison of the two fibres sends the class of a regular function on a Zariski open of
the chart to the class of its restriction to the corresponding small étale neighbourhood. -/
theorem chartZariskiFiberToEtaleFiber_apply {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (chartScheme V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) (r : Γ(chartScheme V.chart, W)) :
    chartZariskiFiberToEtaleFiber B S hS hX V
        ((chartZariskiPoint B S hS X V).toPresheafFiber W ⟨⟨hw⟩⟩
          (chartZariskiRingSheaf B S hS V).obj r) =
      (etaleSitePoint B S hS X x hX).toPresheafFiber
        ((chartOpens B S hS V.chart).obj W)
        ⟨(chartOpenNeighborhood B S hS V W hw).point,
          (chartOpenNeighborhood B S hS V W hw).point_comp⟩
        (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O.obj
        (((chartRestrictionRingHom B S hS hX V.chart).app (op W)).hom r) := by
  apply (pointStalkRingEquiv B S hS ⟨X, hX⟩ x).injective
  refine Eq.trans ((pointStalkRingEquiv B S hS ⟨X, hX⟩ x).apply_symm_apply _) ?_
  refine Eq.trans ?_ (pointStalkRingEquiv_germ_neighborhood B S hS ⟨X, hX⟩ x
    (chartOpenNeighborhood B S hS V W hw) _).symm
  exact Eq.trans (congrArg (chartLocalRingToEtaleLocalRing B S hS X hX V)
    (ConcreteCategory.congr_hom (Opens.toPresheafFiber_pointFiberStalkHom
      (chartPoint B S hS X V) (chartZariskiRingSheaf B S hS V).obj W ⟨⟨hw⟩⟩) r))
    (chartLocalRingToEtaleLocalRing_germ_open' B S hS hX V W hw r)

/-- The geometric germ at `x̄` of a section of `F` over a Zariski open of the chart, read on
the small étale neighbourhood that open defines, as a map out of the sections of
`AlgebraicGeometry.Space.chartRestrictionPresheaf`. -/
noncomputable def chartOpenGeometricGerm {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    (W : (chartScheme V.chart).Opens) (xw : (chartZariskiPoint B S hS X V).fiber.obj W) :
    (chartRestrictionPresheaf B S hS hX F V.chart).obj (op W) →+
      Stacks.moduleStalkLarge (etaleSitePoint B S hS X x hX)
        (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F :=
  (Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X x hX)
      (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F ((chartOpens B S hS V.chart).obj W)
      ⟨(chartOpenNeighborhood B S hS V W xw.down.down).point,
        (chartOpenNeighborhood B S hS V W xw.down.down).point_comp⟩).comp
    (AddMonoidHom.mk' ULift.down (fun _ _ => rfl))

/-- The geometric germ of a section of `F` over a Zariski open of the chart is unchanged by
restricting the section to a smaller open. -/
theorem chartOpenGeometricGerm_w {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    ⦃W' W : (chartScheme V.chart).Opens⦄ (i : W' ⟶ W)
    (xw' : (chartZariskiPoint B S hS X V).fiber.obj W')
    (s : (chartRestrictionPresheaf B S hS hX F V.chart).obj (op W)) :
    chartOpenGeometricGerm B S hS hX V F W' xw'
        ((chartRestrictionPresheaf B S hS hX F V.chart).map i.op s) =
      chartOpenGeometricGerm B S hS hX V F W
        ((chartZariskiPoint B S hS X V).fiber.map i xw') s :=
  Eq.trans (Stacks.moduleStalkLargeGerm_w (etaleSitePoint B S hS X x hX)
      (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F ((chartOpens B S hS V.chart).map i) _ s.down)
    (congrArg (fun y => Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X x hX)
        (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F ((chartOpens B S hS V.chart).obj W) y s.down)
      (Subtype.ext (chartOpenNeighborhoodMap B S hS V i xw'.down.down
        ((chartZariskiPoint B S hS X V).fiber.map i xw').down.down).point_comp))

/-- The geometric germ map on the sections over a Zariski open of the chart is semilinear along
`AlgebraicGeometry.Space.chartZariskiFiberToEtaleFiber`. -/
theorem chartOpenGeometricGerm_smul {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    (W : (chartScheme V.chart).Opens) (xw : (chartZariskiPoint B S hS X V).fiber.obj W)
    (r : (chartScheme V.chart).ringCatSheaf.obj.obj (op W))
    (s : (chartRestrictionPresheaf B S hS hX F V.chart).obj (op W)) :
    chartOpenGeometricGerm B S hS hX V F W xw (r • s) =
      chartZariskiFiberToEtaleFiber B S hS hX V
          ((chartZariskiPoint B S hS X V).toPresheafFiber W xw
            (chartZariskiRingSheaf B S hS V).obj r) •
        chartOpenGeometricGerm B S hS hX V F W xw s :=
  Eq.trans (Stacks.moduleStalkLargeGerm_smul (etaleSitePoint B S hS X x hX)
      (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F ((chartOpens B S hS V.chart).obj W) _ _ s.down)
    (congrArg (fun c => c • chartOpenGeometricGerm B S hS hX V F W xw s)
      (chartZariskiFiberToEtaleFiber_apply B S hS hX V W xw.down.down r).symm)

/-- **The semilinear map from the Zariski stalk to the geometric stalk.** An additive map out
of the Zariski stalk which is semilinear along
`AlgebraicGeometry.Space.chartZariskiFiberToEtaleFiber` becomes, after the extension of scalars
defining the geometric stalk, a map which is semilinear along the comparison of local rings
`AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing`. -/
noncomputable def geometricStalkSemilinear {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    (Ψ₀ : ↥(chartZariskiModuleStalkLarge B S hS hX V F) →+
      ↥(geometricModuleStalkLarge B S hS hX x F))
    (hΨ₀ : ∀ (r : ↥(chartZariskiFiber B S hS V))
        (z : ↥(chartZariskiModuleStalkLarge B S hS hX V F)),
      Ψ₀ (r • z) = chartZariskiFiberToEtaleFiber B S hS hX V r • Ψ₀ z) :
    chartZariskiModuleStalk B S hS X hX V F →ₛₗ[chartLocalRingToEtaleLocalRing B S hS X hX V]
      geometricModuleStalk B S hS ⟨X, hX⟩ x F where
  toFun z := geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F (Ψ₀ z)
  map_add' z z' := Eq.trans
    (congrArg (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F) (map_add Ψ₀ z z'))
    (map_add (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F) _ _)
  map_smul' b z := by
    refine Eq.trans (congrArg (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F)
      (hΨ₀ ((chartZariskiFiberIso B S hS X V).inv.hom b) z)) ?_
    refine Eq.trans (geometricModuleStalkAddEquiv_smul B S hS ⟨X, hX⟩ x F _ _) ?_
    refine congrArg (fun c => c • geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F (Ψ₀ z)) ?_
    refine Eq.trans ((pointStalkRingEquiv B S hS ⟨X, hX⟩ x).apply_symm_apply _) ?_
    exact congrArg (chartLocalRingToEtaleLocalRing B S hS X hX V)
      (ConcreteCategory.congr_hom (chartZariskiFiberIso B S hS X V).inv_hom_id b)

/-- The comparison map of Stacks 05VP together with its value on germs. -/
noncomputable def chartStalkTensorComparisonData {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX) :
    { c : chartStalkTensorEtaleLocalRing B S hS X hX V F ⟶
            geometricModuleStalk B S hS ⟨X, hX⟩ x F //
      ∀ (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
        (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))),
        c ((1 : ↥(etaleLocalRing B S hS X x)) ⊗ₜ[↥(chartLocalRing B S hS X V),
              chartLocalRingToEtaleLocalRing B S hS X hX V]
            chartZariskiSectionGerm B S hS hX V F W hw s :
            chartStalkTensorEtaleLocalRing B S hS X hX V F) =
          geometricModuleStalkGerm B S hS ⟨X, hX⟩ x F
            (chartOpenNeighborhood B S hS V W hw) s } := by
  let Y := etaleChartScheme B S hS V.chart
  let J := Opens.grothendieckTopology Y
  let M₀ := chartRestrictionPresheaf B S hS hX F V.chart
  let MU := restrictToChart B S hS hX F V.chart
  let OU : Sheaf J CommRingCat.{u} := Y.sheaf
  let pZ : J.Point.{u} := chartZariskiPoint B S hS X V
  letI : HasSheafify J AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u m} _ _
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u m} _
  let unit : M₀.presheaf ⟶ MU.val.presheaf := CategoryTheory.toSheafify J M₀.presheaf
  haveI : Presheaf.IsLocallySurjective J unit :=
    (inferInstance : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J M₀.presheaf))
  haveI : Presheaf.IsLocallyInjective J unit :=
    (inferInstance : Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J M₀.presheaf))
  let unitMod : M₀ ⟶ (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).obj MU.val :=
    PresheafOfModules.toSheafify _ unit
  have hψ : ∀ (Z : (Opens Y)ᵒᵖ) (a : Y.ringCatSheaf.obj.obj Z) (t : M₀.obj Z),
      unit.app Z (a • t) = a • unit.app Z t :=
    fun Z a t => (unitMod.app Z).hom.map_smul a t
  refine ⟨baseChangeLiftHom (chartLocalRingToEtaleLocalRing B S hS X hX V)
    (chartZariskiModuleStalk B S hS X hX V F) (geometricModuleStalk B S hS ⟨X, hX⟩ x F)
    (geometricStalkSemilinear B S hS hX V F
      (Stacks.moduleStalkLargeDescOfLocallyBijective pZ OU MU unit
        (chartOpenGeometricGerm B S hS hX V F) (chartOpenGeometricGerm_w B S hS hX V F))
      (Stacks.moduleStalkLargeDescOfLocallyBijective_smul pZ OU MU unit
        (chartOpenGeometricGerm B S hS hX V F) (chartOpenGeometricGerm_w B S hS hX V F)
        (chartZariskiFiberToEtaleFiber B S hS hX V) hψ
        (chartOpenGeometricGerm_smul B S hS hX V F))), ?_⟩
  intro W hw s
  refine Eq.trans (baseChangeLift_tmul (chartLocalRingToEtaleLocalRing B S hS X hX V)
    (chartZariskiModuleStalk B S hS X hX V F) _ 1 _) ?_
  refine Eq.trans (one_smul _ _) ?_
  exact congrArg (geometricModuleStalkAddEquiv B S hS ⟨X, hX⟩ x F)
    (Stacks.moduleStalkLargeDescOfLocallyBijective_germ pZ OU MU unit
      (chartOpenGeometricGerm B S hS hX V F) (chartOpenGeometricGerm_w B S hS hX V F)
      W ⟨⟨hw⟩⟩ (ULift.up s))

/-- The comparison map from the Zariski stalk `(φ^* F)_u` of the restriction of an `𝒪_X`-module
to an étale scheme chart, base changed along the canonical map `𝒪_{U, u} → 𝒪_{X, x̄}`, to the
stalk `F_{x̄}` of `F` at the geometric point. -/
@[stacks 05VP "the comparison map (phi^* F)_u tensor O_{U, u} O_{X, xbar} to F_xbar"]
noncomputable def chartStalkTensorComparison {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX) :
    chartStalkTensorEtaleLocalRing B S hS X hX V F ⟶
      geometricModuleStalk B S hS ⟨X, hX⟩ x F :=
  (chartStalkTensorComparisonData B S hS hX V F).1

/-- The comparison map `(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} → F_{x̄}` sends the base change of the
Zariski germ at `u` of a section of `F` over a Zariski open `W` of the chart containing `u` to the
germ at `x̄` of the same section, read on the small étale neighbourhood `W`. -/
@[stacks 05VP "the comparison map is the identity on germs of sections"]
theorem chartStalkTensorComparison_germ {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))) :
    chartStalkTensorComparison B S hS hX V F
        ((1 : ↥(etaleLocalRing B S hS X x)) ⊗ₜ[↥(chartLocalRing B S hS X V),
            chartLocalRingToEtaleLocalRing B S hS X hX V]
          chartZariskiSectionGerm B S hS hX V F W hw s :
          chartStalkTensorEtaleLocalRing B S hS X hX V F) =
      geometricModuleStalkGerm B S hS ⟨X, hX⟩ x F
        (chartOpenNeighborhood B S hS V W hw) s :=
  (chartStalkTensorComparisonData B S hS hX V F).2 W hw s

end AlgebraicGeometry.Space

end
