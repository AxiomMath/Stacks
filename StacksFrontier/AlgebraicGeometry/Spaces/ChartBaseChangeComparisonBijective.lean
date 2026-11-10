module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartDiagramsOfModulePullback

/-!
# The canonical base-change comparison of a pullback of modules is bijective

Let `g : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`, let
`M` be an `𝒪_Y`-module and let `e` be a commuting square of affine étale scheme charts over `g`
— a chart `e.U` of `X` above a chart `e.V` of `Y`.  There is a canonical `𝒪_X(e.U)`-linear
comparison

`𝒪_X(e.U) ⊗_{𝒪_Y(e.V)} M(e.V) ⟶ (g^*M)(e.U)`,

`AlgebraicGeometry.Space.modulePullbackChartBaseChange`, extending the chart component of the
unit of the Stacks 03D7 adjunction.  This file shows it is **bijective** whenever `M` is
quasi-coherent and carries a global presentation which is right exact on the sections over
`e.V`.

`AlgebraicGeometry.Space.nonempty_linearEquiv_modulePullbackChartBaseChange` already produces, in
exactly this situation, *some* linear equivalence between the two sides, and
`AlgebraicGeometry.Space.isCartesianOnAffineChartDiagrams_of_isQuasicoherentOnSite` removes the
presentation hypothesis from that statement.  Neither says anything about the canonical map, and
an abstract equivalence is useless to a consumer that has to transport a *morphism*: a map
`u : M ⟶ M'` is carried to `g^*u` by the comparison only because the comparison is natural
(`AlgebraicGeometry.Space.modulePullbackChartBaseChange_map`), and naturality is a statement
about the canonical map alone.  That is why this file exists.

## Main results

* `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange`: **the canonical comparison
  is bijective** at a presented quasi-coherent module over a diagram of affine charts.
* `AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_iff`: consequently, over such a
  diagram, the base change of a map `u : M ⟶ M'` of quasi-coherent modules vanishes on the
  sections over `e.U` exactly when the extension of scalars of `u(e.V)` vanishes.
* `AlgebraicGeometry.Space.etaleChartSpaceBaseChangeNatIso`: restricting a module to the chart
  `d.V` of `Y` and pulling back along the morphism of chart spaces agrees with pulling back
  along `f` and restricting to the chart `d.U` of `X`, as a natural isomorphism of *functors* —
  `AlgebraicGeometry.Space.etaleModulePullbackChartSpaceBaseChangeIso` is the same isomorphism at
  a fixed module, and what a map of modules needs is the naturality.
* `AlgebraicGeometry.Space.val_app_eq_zero_iff_chartSpace`: the vanishing of the base change of
  `u` along the morphism of chart spaces, on the sections over the identity chart, is the
  vanishing of the base change along `f` on the sections over `d.U`.

## Implementation notes

The proof is the proof of
`AlgebraicGeometry.Space.nonempty_linearEquiv_modulePullbackChartBaseChange` with its last step
changed: instead of `AlgebraicGeometry.Space.nonempty_linearEquiv_baseChange_of_rightExact`,
which *builds* a comparison at the right-hand terms of the two right exact sequences by
descending along a surjection, it ends in
`AlgebraicGeometry.Space.bijective_baseChange_of_rightExact`, which takes a comparison as given
and needs one further square — that the comparison at the generators, followed by the generating
map upstairs, is the generating map downstairs followed by the comparison at `M`.  That square is
again naturality of the comparison in the module, applied to `P.generators.π`, together with
`SheafOfModules.Presentation.map_π_eq`: the generating map of the transported presentation
`AlgebraicGeometry.Space.presentationModulePullback` is the inverse image of the generating map,
read through `AlgebraicGeometry.Space.modulePullbackFreeIso`.

The second result is stated as an `Iff` on the map on sections rather than on the map of modules,
because that is the form the chart-wise criterion
`AlgebraicGeometry.Space.Modules.eq_zero_of_forall_app_isAffine_eq_zero` consumes.  Its forward
direction uses injectivity of the comparison at the *target* module and its backward direction
surjectivity of the comparison at the *source* module, so both halves of bijectivity are needed
and the hypotheses are carried for both modules.

**What is not assembled here.**  The two main results together give the presentation-free
statement a consumer wants — over a diagram of affine charts, and for `F`, `G` merely
quasi-coherent on `Y`, the base change of `u : F ⟶ G` vanishes on the sections over `d.U`
exactly when the extension of scalars of `u(d.V)` does — by applying
`modulePullback_map_val_app_eq_zero_iff` to the morphism of chart spaces (where the presentations
exist, `AlgebraicGeometry.Space.exists_presentation_rightExact_app_idEtaleChart`) and moving the
conclusion back with `val_app_eq_zero_iff_chartSpace`.  Every identification that step needs is
definitional, and each is cheap in isolation: the sections over the identity chart of a chart
space are the sections over the chart, the ring of the identity chart is the ring of the chart,
and `chartDiagramAlgebra` of the chart-space diagram is `chartDiagramAlgebra` of the given one.
What does not go through is the single unification that asks for all of them at once inside
`LinearMap.lTensor`, whose module instances on the tensor product each depend on the algebra:
it exhausts the heartbeat budget, and raising the budget is not permitted here.  So the
assembly is left to a consumer that can take the two statements in the chart-space spelling.

Everything is at `Modules.{u, u}`, the module universe of the structure rings, as the pullback of
Stacks 03LU and its comparison are.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The canonical base-change comparison is bijective at a presented quasi-coherent module
over a diagram of affine charts.**

The two right exact sequences are the sections of `P` over `e.V` and the sections over `e.U` of
its transport `AlgebraicGeometry.Space.presentationModulePullback` along the pullback of modules,
which has the same index types and is right exact there because `e.U` is affine and the pullback
of `M` is quasi-coherent.  The comparisons at the two free modules are bijective by
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_free`, and the two squares are
naturality of the comparison in the module applied to the presenting map and to the generating
map. -/
theorem bijective_modulePullbackChartBaseChange
    {X' Y' : AlgebraicSpaces B S hS} (g : X' ⟶ Y') (M : Modules.{u, u} B S hS Y'.1 Y'.2)
    (hM : M.IsQuasicoherentOnSite) (P : M.Presentation)
    (e : ChartDiagram B S hS X'.1 Y'.1 g.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj e.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj e.V))
    (hgen : Function.Surjective (P.generators.π.val.app (op e.V)))
    (hex : Function.Exact ((P.relations.π ≫ kernel.ι P.generators.π).val.app (op e.V))
      (P.generators.π.val.app (op e.V))) :
    letI := chartDiagramAlgebra B S hS g e
    Function.Bijective (modulePullbackChartBaseChange B S hS g M e) := by
  have hpc := preservesColimitsOfSize_modulePullback B S hS g
  let _ := chartDiagramAlgebra B S hS g e
  have hq : ((modulePullback B S hS g).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g M hM
  -- the presenting map of the transported presentation, read through the two free comparisons
  have h1 : (presentationModulePullback B S hS g P).relations.π ≫
        kernel.ι (presentationModulePullback B S hS g P).generators.π =
      P.mapRelations (modulePullback B S hS g) (modulePullbackUnitIso B S hS g).symm :=
    Eq.trans (congrArg (fun m ↦ m ≫
        kernel.ι (presentationModulePullback B S hS g P).generators.π)
      ((SheafOfModules.freeHomEquiv _).symm_apply_apply _)) (kernel.lift_ι _ _ _)
  have h2 : P.mapRelations (modulePullback B S hS g) (modulePullbackUnitIso B S hS g).symm =
      (modulePullbackFreeIso B S hS g P.relations.I).hom ≫
        (modulePullback B S hS g).map (P.relations.π ≫ kernel.ι P.generators.π) ≫
        (modulePullbackFreeIso B S hS g P.generators.I).inv := by
    rw [Functor.map_comp]
    rfl
  have hν : ∀ (I : Type u) w, (modulePullbackFreeIso B S hS g I).hom.val.app (op e.U)
      ((modulePullbackFreeIso B S hS g I).inv.val.app (op e.U) w) = w := fun I w ↦
    congrArg (fun m : (modulePullback B S hS g).obj (free I) ⟶
        (modulePullback B S hS g).obj (free I) ↦ m.val.app (op e.U) w)
      (modulePullbackFreeIso B S hS g I).inv_hom_id
  have hφV : ∀ y, ((presentationModulePullback B S hS g P).relations.π ≫
        kernel.ι (presentationModulePullback B S hS g P).generators.π).val.app (op e.U) y =
      (modulePullbackFreeIso B S hS g P.generators.I).inv.val.app (op e.U)
        (((modulePullback B S hS g).map
            (P.relations.π ≫ kernel.ι P.generators.π)).val.app (op e.U)
          ((modulePullbackFreeIso B S hS g P.relations.I).hom.val.app (op e.U) y)) := fun y ↦
    congrArg (fun m ↦ m.val.app (op e.U) y) (h1.trans h2)
  -- the generating map of the transported presentation, read through the free comparison
  have hπI : ∀ w, (presentationModulePullback B S hS g P).generators.π.val.app (op e.U) w =
      ((modulePullback B S hS g).map P.generators.π).val.app (op e.U)
        ((modulePullbackFreeIso B S hS g P.generators.I).hom.val.app (op e.U) w) := fun w ↦
    congrArg (fun m ↦ m.val.app (op e.U) w)
      (SheafOfModules.Presentation.map_π_eq P (modulePullback B S hS g)
        (modulePullbackUnitIso B S hS g).symm)
  -- the two right exact sequences
  have hπU : Function.Surjective (P.generators.π.val.app (op e.V)).hom := hgen
  have hexU : Function.Exact
      ((P.relations.π ≫ kernel.ι P.generators.π).val.app (op e.V)).hom
      (P.generators.π.val.app (op e.V)).hom := hex
  have hπV : Function.Surjective
      ((presentationModulePullback B S hS g P).generators.π.val.app (op e.U)).hom :=
    surjective_generators_app_of_isAffine B S hS X'.1 X'.2 hq
      (presentationModulePullback B S hS g P) e.U hU
  have hexV : Function.Exact
      (((presentationModulePullback B S hS g P).relations.π ≫
        kernel.ι (presentationModulePullback B S hS g P).generators.π).val.app (op e.U)).hom
      ((presentationModulePullback B S hS g P).generators.π.val.app (op e.U)).hom :=
    exact_app_of_presentation B S hS X'.1 X'.2 hq
      (presentationModulePullback B S hS g P) e.U hU
  -- the two comparison maps at the free modules
  have hcG : ∀ I : Type u, Function.Bijective
      ((((modulePullbackFreeIso B S hS g I).inv.val.app (op e.U)).hom) ∘ₗ
        modulePullbackChartBaseChange B S hS g (free I) e) := fun I ↦
    (SheafOfModules.bijective_iso_hom_val_app
        (modulePullbackFreeIso B S hS g I).symm (op e.U)).comp
      (bijective_modulePullbackChartBaseChange_free B S hS g I e hU hV)
  -- the square at the presenting map
  have hsq : ∀ z, (((presentationModulePullback B S hS g P).relations.π ≫
          kernel.ι (presentationModulePullback B S hS g P).generators.π).val.app (op e.U)).hom
        ((((modulePullbackFreeIso B S hS g P.relations.I).inv.val.app (op e.U)).hom ∘ₗ
          modulePullbackChartBaseChange B S hS g (free P.relations.I) e) z) =
      (((modulePullbackFreeIso B S hS g P.generators.I).inv.val.app (op e.U)).hom ∘ₗ
          modulePullbackChartBaseChange B S hS g (free P.generators.I) e)
        (LinearMap.lTensor (chartRing B S hS X'.1 X'.2 e.U)
          ((P.relations.π ≫ kernel.ι P.generators.π).val.app (op e.V)).hom z) := by
    intro z
    refine Eq.trans (hφV _) ?_
    refine congrArg
      (fun w ↦ (modulePullbackFreeIso B S hS g P.generators.I).inv.val.app (op e.U) w) ?_
    refine Eq.trans (congrArg (fun w ↦ ((modulePullback B S hS g).map
      (P.relations.π ≫ kernel.ι P.generators.π)).val.app (op e.U) w) (hν _ _)) ?_
    exact modulePullbackChartBaseChange_map B S hS g
      (P.relations.π ≫ kernel.ι P.generators.π) e z
  -- the square at the generating map
  have hsq' : ∀ z, (((presentationModulePullback B S hS g P).generators.π.val.app
          (op e.U)).hom)
        ((((modulePullbackFreeIso B S hS g P.generators.I).inv.val.app (op e.U)).hom ∘ₗ
          modulePullbackChartBaseChange B S hS g (free P.generators.I) e) z) =
      modulePullbackChartBaseChange B S hS g M e
        (LinearMap.lTensor (chartRing B S hS X'.1 X'.2 e.U)
          (P.generators.π.val.app (op e.V)).hom z) := by
    intro z
    refine Eq.trans (hπI _) ?_
    refine Eq.trans (congrArg
      (fun w ↦ ((modulePullback B S hS g).map P.generators.π).val.app (op e.U) w) (hν _ _)) ?_
    exact modulePullbackChartBaseChange_map B S hS g P.generators.π e z
  exact bijective_baseChange_of_rightExact hπU hexU hπV hexV hsq hsq' (hcG _).surjective (hcG _)

/-- **Over a diagram of affine charts, the base change of a map of quasi-coherent modules
vanishes on sections exactly when the extension of scalars of its sections does.**

The comparison is natural in the module, so the map on sections of `g^*u` over `e.U` and the
extension of scalars of `u(e.V)` are conjugate by the comparisons at the source and at the
target; both are bijective, so one vanishes exactly when the other does. -/
theorem modulePullback_map_val_app_eq_zero_iff
    {X' Y' : AlgebraicSpaces B S hS} (g : X' ⟶ Y')
    {M M' : Modules.{u, u} B S hS Y'.1 Y'.2}
    (hM : M.IsQuasicoherentOnSite) (hM' : M'.IsQuasicoherentOnSite)
    (P : M.Presentation) (P' : M'.Presentation) (u : M ⟶ M')
    (e : ChartDiagram B S hS X'.1 Y'.1 g.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj e.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj e.V))
    (hgen : Function.Surjective (P.generators.π.val.app (op e.V)))
    (hex : Function.Exact ((P.relations.π ≫ kernel.ι P.generators.π).val.app (op e.V))
      (P.generators.π.val.app (op e.V)))
    (hgen' : Function.Surjective (P'.generators.π.val.app (op e.V)))
    (hex' : Function.Exact ((P'.relations.π ≫ kernel.ι P'.generators.π).val.app (op e.V))
      (P'.generators.π.val.app (op e.V))) :
    letI := chartDiagramAlgebra B S hS g e
    ((modulePullback B S hS g).map u).val.app (op e.U) = 0 ↔
      LinearMap.lTensor (chartRing B S hS X'.1 X'.2 e.U) (u.val.app (op e.V)).hom = 0 := by
  let _ := chartDiagramAlgebra B S hS g e
  have hbM := bijective_modulePullbackChartBaseChange B S hS g M hM P e hU hV hgen hex
  have hbM' := bijective_modulePullbackChartBaseChange B S hS g M' hM' P' e hU hV hgen' hex'
  have key := modulePullbackChartBaseChange_map B S hS g u e
  constructor
  · intro h
    refine LinearMap.ext fun z ↦ ?_
    rw [LinearMap.zero_apply]
    refine hbM'.1 ?_
    rw [map_zero, ← key z, h]
    rfl
  · intro h
    have hz : ∀ z, modulePullbackChartBaseChange B S hS g M' e
          (LinearMap.lTensor (chartRing B S hS X'.1 X'.2 e.U) (u.val.app (op e.V)).hom z) = 0 :=
      fun z ↦ by rw [h, LinearMap.zero_apply, map_zero]
    refine ModuleCat.hom_ext (LinearMap.ext fun w ↦ ?_)
    obtain ⟨z, rfl⟩ := hbM.2 w
    change ((modulePullback B S hS g).map u).val.app (op e.U)
      (modulePullbackChartBaseChange B S hS g M e z) = 0
    rw [key z]
    exact hz z

/-! ### Removing the presentation hypothesis -/

/-- Two functors of modules related by a natural isomorphism have the same vanishing on the
sections of the image of a morphism over a chart: the two images are conjugate by the components
of the isomorphism, which are bijective on sections over every chart. -/
private theorem val_app_eq_zero_iff_of_natIso {Z W : AlgebraicSpaces B S hS}
    {Phi Psi : Modules.{u, u} B S hS Z.1 Z.2 ⥤ Modules.{u, u} B S hS W.1 W.2} (α : Phi ≅ Psi)
    {M M' : Modules.{u, u} B S hS Z.1 Z.2} (u : M ⟶ M') (V : SmallEtale B S hS W.1) :
    (Phi.map u).val.app (op V) = 0 ↔ (Psi.map u).val.app (op V) = 0 := by
  have hM := SheafOfModules.bijective_iso_hom_val_app (α.app M) (op V)
  have hM' := SheafOfModules.bijective_iso_hom_val_app (α.app M') (op V)
  have hpt : ∀ x, (α.app M').hom.val.app (op V) ((Phi.map u).val.app (op V) x) =
      (Psi.map u).val.app (op V) ((α.app M).hom.val.app (op V) x) := fun x ↦
    congrArg (fun m : Phi.obj M ⟶ Psi.obj M' ↦ m.val.app (op V) x) (α.hom.naturality u)
  constructor
  · intro h
    have h' : ∀ x, (Phi.map u).val.app (op V) x = 0 := fun x ↦ by rw [h]; rfl
    refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
    obtain ⟨x, rfl⟩ := hM.2 y
    change (Psi.map u).val.app (op V) ((α.app M).hom.val.app (op V) x) = 0
    rw [← hpt x, h' x, map_zero]
  · intro h
    have h' : ∀ x, (Psi.map u).val.app (op V) x = 0 := fun x ↦ by rw [h]; rfl
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    change (Phi.map u).val.app (op V) x = 0
    refine hM'.1 ?_
    rw [hpt x, h' _, map_zero]

variable {X Y : AlgebraicSpaces B S hS}

/-- **Restricting to a chart and pulling back along the morphism of chart spaces agrees with
pulling back and restricting to a chart**, as a natural isomorphism of functors.

This is `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso`, which is stated for the
inverse-image reading of the chart restriction, whiskered with the comparison of Stacks 03LW at
each end so that both sides read the chart restriction as
`AlgebraicGeometry.Space.etaleModulePullback`.  That is the reading whose sections over the
identity chart of the chart space are the sections over the chart.

`AlgebraicGeometry.Space.etaleModulePullbackChartSpaceBaseChangeIso` is the same isomorphism at a
fixed module; what is needed here is its naturality, so it is built as a transformation of
functors from the start. -/
noncomputable def etaleChartSpaceBaseChangeNatIso (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
          (isEtale_chartToSpace B S hS Y d.V) ⋙
        modulePullback B S hS (chartSpaceMapOver B S hS d.g) ≅
      modulePullback B S hS f ⋙
        etaleModulePullback B S hS (chartToSpace B S hS X d.U)
          (isEtale_chartToSpace B S hS X d.U) :=
  Functor.isoWhiskerRight (modulePullbackIsoEtaleModulePullback B S hS
        (chartToSpace B S hS Y d.V) (isEtale_chartToSpace B S hS Y d.V)).symm
      (modulePullback B S hS (chartSpaceMapOver B S hS d.g)) ≪≫
    chartModuleRestrictionBaseChangeIso B S hS f d.g d.comm.symm ≪≫
      Functor.isoWhiskerLeft (modulePullback B S hS f)
        (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X d.U)
          (isEtale_chartToSpace B S hS X d.U))

/-- **The base change along the morphism of chart spaces vanishes on the sections over the
identity chart exactly when the base change along `f` vanishes on the sections over `d.U`.**  The
identification of the two modules is
`AlgebraicGeometry.Space.etaleChartSpaceBaseChangeNatIso`, and the identification of the sections
over the identity chart of a chart space with the sections over the chart is definitional. -/
theorem val_app_eq_zero_iff_chartSpace (f : X ⟶ Y)
    {F G : Modules.{u, u} B S hS Y.1 Y.2} (u : F ⟶ G)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    ((modulePullback B S hS (chartSpaceMapOver B S hS d.g)).map
          ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
            (isEtale_chartToSpace B S hS Y d.V)).map u)).val.app
          (op (chartSpaceIdChartDiagram B S hS f d).U) = 0 ↔
      ((modulePullback B S hS f).map u).val.app (op d.U) = 0 :=
  val_app_eq_zero_iff_of_natIso B S hS (etaleChartSpaceBaseChangeNatIso B S hS f d) u
    (chartSpaceIdChartDiagram B S hS f d).U

end AlgebraicGeometry.Space

end
