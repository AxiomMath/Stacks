module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# The affine-chart description of a pullback of quasi-coherent modules

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` and
let `F` be a quasi-coherent `𝒪_Y`-module on the small étale site.  Over a diagram of affine
étale scheme charts over `f` — a chart `d.U` of `X` above a chart `d.V` of `Y` — the sections of
`f^*F` over `d.U` are the base change of the sections of `F` over `d.V` along the pullback of
regular functions.  That is `AlgebraicGeometry.Space.IsCartesianOnAffineChartDiagrams`, Descent,
Proposition 03DX(2) read across `f`, and this file proves it.

## Main results

* `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange`: **the canonical base-change
  comparison `AlgebraicGeometry.Space.modulePullbackChartBaseChange` is bijective at a module
  with a global
  presentation which is right exact on the sections over the target chart of a diagram of affine
  charts.**  The two right exact sequences of the algebra step are the sections of that
  presentation and of its transport
  `AlgebraicGeometry.Space.presentationModulePullback` along the pullback, which have the *same*
  index types, and the comparison is bijective at the generators and surjective at the relations
  because it is bijective at a free module.  The *canonical* comparison can stand as the third
  vertical map because it is natural in the module, and
  `AlgebraicGeometry.Space.bijective_baseChange_of_rightExact` takes that map as an argument
  rather than constructing one.
* `AlgebraicGeometry.Space.nonempty_linearEquiv_modulePullbackChartBaseChange`: the `Nonempty`
  reading of the same statement, which is the shape
  `AlgebraicGeometry.Space.IsCartesianOnAffineChartDiagrams` asks for.
* `AlgebraicGeometry.Space.isCartesianOnAffineChartDiagrams_of_isQuasicoherentOnSite`: **the
  affine-chart description of the pullback of a quasi-coherent module.**

## Implementation notes

*The presentation is taken on the chart spaces, not on `Y`.*  A quasi-coherent module on an
algebraic space has a global presentation only locally, so there is no presentation of `F` on
`Y` to transport.  What there is, by
`AlgebraicGeometry.Space.exists_presentation_rightExact_app_idEtaleChart`, is a presentation of
the restriction of `F` to the algebraic space represented by the affine chart `d.V`, right exact
on the sections over the identity chart of that chart space — which are the sections `F(d.V)`.
So the general statement is applied to the morphism
`AlgebraicGeometry.Space.chartSpaceMapOver` of chart spaces attached to the vertical morphism of
the diagram, at the diagram
`AlgebraicGeometry.Space.chartSpaceIdChartDiagram` of the two identity charts, whose vertical
morphism is the same; the pullback of regular functions, and therefore the algebra structure, is
literally the same map, so nothing has to be transported on the algebra side.

*Where the two readings of the chart restriction meet.*  The sections of the restriction of a
module to a chart, over the identity chart of the chart space, are the sections of the module
over the chart *definitionally* only in the étale-restriction reading
`AlgebraicGeometry.Space.etaleModulePullback`
(`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_obj_val_obj_idEtaleChart` is `rfl`),
whereas the base-change compatibility
`AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso` of the chart restriction holds for
the inverse-image reading `AlgebraicGeometry.Space.chartModuleRestriction`.  The crossing is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, Stacks 03LW, applied once on
each side; that is
`AlgebraicGeometry.Space.etaleModulePullbackChartSpaceBaseChangeIso`.

*Where the canonicity is lost.*  The comparison
`AlgebraicGeometry.Space.modulePullbackChartBaseChange` is canonical, and
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange` says that
*it*, and not some isomorphism assembled from the presentation, is bijective.  Only the
existence of the presentation is non-canonical, and that does not reach the statement, which
does not mention it.

What is lost is the *transport*: that theorem is applied at the morphism of chart spaces and at
the diagram `AlgebraicGeometry.Space.chartSpaceIdChartDiagram`, so it is the comparison for
`chartSpaceMapOver d.g` that comes out bijective, and
`AlgebraicGeometry.Space.etaleModulePullbackChartSpaceBaseChangeIso` is then composed on, after
which only the existence of an isomorphism survives.  Making
`AlgebraicGeometry.Space.isCartesianOnAffineChartDiagrams_of_isQuasicoherentOnSite` canonical —
bijectivity of `modulePullbackChartBaseChange B S hS f F d` itself, which is what a consumer
comparing two modules *along a morphism* needs, `IsCartesianOnAffineChartDiagrams` being unable
to supply that — is exactly the one identity

`(etaleModulePullbackChartSpaceBaseChangeIso B S hS f F d).hom.val.app (op e.U)`
`  (modulePullbackChartSection B S hS (chartSpaceMapOver B S hS d.g) _ e s)`
`    = modulePullbackChartSection B S hS f F d s`,  `e := chartSpaceIdChartDiagram B S hS f d`,

since both comparisons are the `liftBaseChange` of the chart component of the unit.  That
identity is *well typed as written* — the two chart rings and the two modules of sections are
definitionally equal, by the two `rfl`s recorded in the paragraphs above — and it is not
definitionally true.  Its three factors are:

* the two components of Stacks 03LW,
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, on a chart section: the first
  moves out of the way by naturality of the chart section in the module
  (`AlgebraicGeometry.Space.modulePullbackChartSection_map`), which leaves the value of
  `(03LW.app F).inv` on the sections over an identity chart, and no lemma computes it;  the
  nearest statement is `AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison_eq_of_unitSquare`
  of `StacksFrontier/AlgebraicGeometry/Spaces/ModuleEtaleBaseChangeUnitSquare.lean`, which
  *assumes* the unit square it would need;
* `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso` on a chart section.  That iso is
  built from `AlgebraicGeometry.Space.modulePullbackCompIso` alone, whose unit equation
  `AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom` is available and
  determines it.  The *square* part of this factor is now closed:
  `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso_hom_app_val_app` reads the
  comparison on a section as the two composition comparisons of Stacks 03LU with the transport of
  the module of sections along the commutation of the square between them, and the implementation
  note on `AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app_eqToHom` records the
  kernel measurement that made it reachable.  What remains is
  `AlgebraicGeometry.Space.modulePullbackCompIso` *itself* on a chart section.  Reading its unit
  equation on sections goes through `AlgebraicGeometry.Space.modulePushforwardCompIso`, which
  carries two `eqToIso`s on equalities of *functors* between categories of sheaves of modules;
  those are gone too —
  `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_natIso` replaces them by componentwise
  natural isomorphisms and
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app_apply` reads
  the direct-image comparison on a section as the geometric comparison of Stacks 03G2, part (3).
  The transport of that reading across the adjunction to the inverse-image side is now supplied
  as well, in
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompMate.lean`:
  `AlgebraicGeometry.Space.unit_comp_map_modulePullbackCompIso_hom_app` is the unit equation on a
  module with every factor other than the comparison itself named, and
  `AlgebraicGeometry.Space.unit_comp_map_modulePullbackCompIso_hom_app_val_app` reads it on a
  section, with `AlgebraicGeometry.Space.unit_comp_val_app_apply` and
  `AlgebraicGeometry.Space.comp_modulePushforwardCompIso_hom_app_val_app` splitting the one
  remaining composite at the unit of the chart structure morphism and at the comparison of direct
  images.  There is no elementwise formula for the comparison itself and there cannot be one, the
  inverse image being a sheafification;  what the unit equation gives is its value on the unit
  sections, which is what a chart section is.

So the obstruction to the canonical form is not the presentation, not the algebra step, not the
square and no longer the mate correspondence either:  what the pair of unit-transport identities
still needs is the first of the two factors above, the value of Stacks 03LW on the sections over
an identity chart.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison at a presented module -/

/-- **The base-change comparison at a module with a right exact global presentation over the
target chart is an isomorphism.**  The `Nonempty` reading of
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange`, which is the shape
`AlgebraicGeometry.Space.IsCartesianOnAffineChartDiagrams` asks for. -/
theorem nonempty_linearEquiv_modulePullbackChartBaseChange
    {X' Y' : AlgebraicSpaces B S hS} (g : X' ⟶ Y') (M : Modules.{u, u} B S hS Y'.1 Y'.2)
    (hM : M.IsQuasicoherentOnSite) (P : M.Presentation)
    (e : ChartDiagram B S hS X'.1 Y'.1 g.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj e.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj e.V))
    (hgen : Function.Surjective (P.generators.π.val.app (op e.V)))
    (hex : Function.Exact ((P.relations.π ≫ kernel.ι P.generators.π).val.app (op e.V))
      (P.generators.π.val.app (op e.V))) :
    letI := chartDiagramAlgebra B S hS g e
    Nonempty (TensorProduct (chartRing B S hS Y'.1 Y'.2 e.V) (chartRing B S hS X'.1 X'.2 e.U)
        (M.val.obj (op e.V)) ≃ₗ[chartRing B S hS X'.1 X'.2 e.U]
      (((modulePullback B S hS g).obj M).val.obj (op e.U))) :=
  let _ := chartDiagramAlgebra B S hS g e
  have key : Function.Bijective (modulePullbackChartBaseChange B S hS g M e) := by
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
    -- the generating map of the transported presentation, read through one free comparison
    have h3 : (presentationModulePullback B S hS g P).generators.π =
        (modulePullbackFreeIso B S hS g P.generators.I).hom ≫
          (modulePullback B S hS g).map P.generators.π :=
      SheafOfModules.Presentation.map_π_eq P (modulePullback B S hS g)
        (modulePullbackUnitIso B S hS g).symm
    have hν : ∀ (J : Type u) w, (modulePullbackFreeIso B S hS g J).hom.val.app (op e.U)
        ((modulePullbackFreeIso B S hS g J).inv.val.app (op e.U) w) = w := fun J w ↦
      congrArg (fun m : (modulePullback B S hS g).obj (free J) ⟶
          (modulePullback B S hS g).obj (free J) ↦ m.val.app (op e.U) w)
        (modulePullbackFreeIso B S hS g J).inv_hom_id
    have hφV : ∀ y, ((presentationModulePullback B S hS g P).relations.π ≫
          kernel.ι (presentationModulePullback B S hS g P).generators.π).val.app (op e.U) y =
        (modulePullbackFreeIso B S hS g P.generators.I).inv.val.app (op e.U)
          (((modulePullback B S hS g).map
              (P.relations.π ≫ kernel.ι P.generators.π)).val.app (op e.U)
            ((modulePullbackFreeIso B S hS g P.relations.I).hom.val.app (op e.U) y)) := fun y ↦
      congrArg (fun m ↦ m.val.app (op e.U) y) (h1.trans h2)
    have hπVval : ∀ y,
        (presentationModulePullback B S hS g P).generators.π.val.app (op e.U) y =
        ((modulePullback B S hS g).map P.generators.π).val.app (op e.U)
          ((modulePullbackFreeIso B S hS g P.generators.I).hom.val.app (op e.U) y) := fun y ↦
      congrArg (fun m ↦ m.val.app (op e.U) y) h3
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
    -- the two comparison maps
    have hcG : ∀ J : Type u, Function.Bijective
        ((((modulePullbackFreeIso B S hS g J).inv.val.app (op e.U)).hom) ∘ₗ
          modulePullbackChartBaseChange B S hS g (free J) e) := fun J ↦
      (SheafOfModules.bijective_iso_hom_val_app
          (modulePullbackFreeIso B S hS g J).symm (op e.U)).comp
        (bijective_modulePullbackChartBaseChange_free B S hS g J e hU hV)
    -- the square over the relations
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
    -- the square over the generators, whose third vertical map is the canonical comparison
    have hsq' : ∀ z,
        ((presentationModulePullback B S hS g P).generators.π.val.app (op e.U)).hom
          ((((modulePullbackFreeIso B S hS g P.generators.I).inv.val.app (op e.U)).hom ∘ₗ
            modulePullbackChartBaseChange B S hS g (free P.generators.I) e) z) =
        modulePullbackChartBaseChange B S hS g M e
          (LinearMap.lTensor (chartRing B S hS X'.1 X'.2 e.U)
            (P.generators.π.val.app (op e.V)).hom z) := by
      intro z
      refine Eq.trans (hπVval _) ?_
      refine Eq.trans (congrArg (fun w ↦ ((modulePullback B S hS g).map
        P.generators.π).val.app (op e.U) w) (hν _ _)) ?_
      exact modulePullbackChartBaseChange_map B S hS g P.generators.π e z
    exact bijective_baseChange_of_rightExact hπU hexU hπV hexV hsq hsq'
      (hcG _).surjective (hcG _)
  ⟨LinearEquiv.ofBijective (modulePullbackChartBaseChange B S hS g M e) key⟩

/-! ### The diagram of identity charts of two chart spaces -/

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The diagram of étale scheme charts over the morphism of chart spaces attached to a diagram
of étale charts over `f`: the two identity charts, joined by the vertical morphism of the
original diagram. -/
def chartSpaceIdChartDiagram (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    ChartDiagram B S hS (chartSpace B S hS X d.U).1 (chartSpace B S hS Y d.V).1
      (chartSpaceMapOver B S hS d.g).hom where
  U := idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj d.U)
  V := idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj d.V)
  g := d.g
  comm := (Category.id_comp _).trans (Category.comp_id _).symm

/-- **The base-change compatibility of the chart restriction of modules, in the
étale-restriction reading.** Restricting `F` to the chart `d.V` of `Y` and pulling back along
the morphism of chart spaces agrees with pulling back along `f` and restricting to the chart
`d.U` of `X`.

This is `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso`, which is stated for the
inverse-image reading of the chart restriction, with the comparison of Stacks 03LW composed on
at each end.  The étale reading is the one whose sections over the identity chart of the chart
space are the sections over the chart. -/
noncomputable def etaleModulePullbackChartSpaceBaseChangeIso
    (F : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (modulePullback B S hS (chartSpaceMapOver B S hS d.g)).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
          (isEtale_chartToSpace B S hS Y d.V)).obj F) ≅
      (etaleModulePullback B S hS (chartToSpace B S hS X d.U)
        (isEtale_chartToSpace B S hS X d.U)).obj ((modulePullback B S hS f).obj F) :=
  (modulePullback B S hS (chartSpaceMapOver B S hS d.g)).mapIso
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS Y d.V)).app F).symm ≪≫
    (chartModuleRestrictionBaseChangeIso B S hS f d.g d.comm.symm).app F ≪≫
      (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X d.U)
        (isEtale_chartToSpace B S hS X d.U)).app ((modulePullback B S hS f).obj F)

/-! ### Descent, Proposition 03DX(2) read across a morphism -/

/-- **The affine-chart description of the pullback of a quasi-coherent module.** Over every
diagram of affine étale scheme charts over `f`, the sections of `f^*F` over the chart of `X` are
the base change of the sections of `F` over the chart of `Y`.

The chart of `Y` being affine, the restriction of `F` to the algebraic space it represents has a
global presentation which is right exact on the sections over the identity chart of that chart
space, and those sections are `F(d.V)`; so
`AlgebraicGeometry.Space.nonempty_linearEquiv_modulePullbackChartBaseChange` applies to the
morphism of chart spaces attached to the vertical morphism of the diagram, whose pullback of
regular functions is the same map.  What it produces is an isomorphism onto the sections of the
pullback of that restriction, and
`AlgebraicGeometry.Space.etaleModulePullbackChartSpaceBaseChangeIso` identifies those with the
sections of `f^*F` over the chart of `X`. -/
theorem isCartesianOnAffineChartDiagrams_of_isQuasicoherentOnSite
    (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) :
    IsCartesianOnAffineChartDiagrams B S hS f F := by
  intro d hU hV
  obtain ⟨P, hgen, hrel, hex⟩ :=
    exists_presentation_rightExact_app_idEtaleChart B S hS Y F hF d.V hV
  refine (nonempty_linearEquiv_modulePullbackChartBaseChange B S hS
    (chartSpaceMapOver B S hS d.g)
    ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V)).obj F)
    (isQuasicoherentOnSite_etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V) F hF)
    P (chartSpaceIdChartDiagram B S hS f d) hU hV hgen hex).elim (fun c ↦ ?_)
  have c' := c.trans (isoValAppLinearEquiv B S hS
    (etaleModulePullbackChartSpaceBaseChangeIso B S hS f F d)
    (chartSpaceIdChartDiagram B S hS f d).U)
  exact ⟨c'⟩

end AlgebraicGeometry.Space

end
