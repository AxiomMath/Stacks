module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison

/-!
# The defining ideal of a closed subspace at a presented chart thickening

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`Z ⊆ X` be a closed subspace and let `U` be an étale scheme chart of `X`.
`AlgebraicGeometry.Space.definingIdealAt_eq_ker` computes the defining ideal of `Z` over `U` as
the kernel of pullback of regular functions along the *canonical* base change
`Z ×_X U ⟶ U`, the one the representability of `Z.1.ι` chooses.

A consumer that builds its own chart thickening — `AlgebraicGeometry.Space.ChartLiftPresentation`
of `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` is the motivating one —
does not hold the canonical base change: it holds *some* closed immersion `i : T ⟶ U` of objects
of the big fppf site together with a cartesian square exhibiting `T` as `Z ×_X U`.  This file
shows that the defining ideal is the kernel of `i^♯` for any such presentation, so that the
conormal data of such a presentation is the defining ideal sheaf read at the chart.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_eq_ker_of_isPullback`: **the defining ideal of `Z`
  over `U` is `RingHom.ker i^♯` for every presentation of `Z ×_X U` by a morphism `i : T ⟶ U`
  of the big fppf site.**
* `AlgebraicGeometry.Space.firstOrderConormalChartSectionsIso`: for a first-order thickening,
  the sections over `U` of the pushed-forward conormal module `i_*𝒞_{Z/X}` are the defining
  ideal at `U`, hence `RingHom.ker i^♯` by the previous statement.  This is
  `AlgebraicGeometry.Space.firstOrderConormalModuleIso` read on the sections over one chart.
* `AlgebraicGeometry.Space.firstOrderConormalChartSectionsIso_hom_apply_coe`: the characterising
  property of that identification — composed with
  `AlgebraicGeometry.Space.firstOrderConormalModuleι` it is the inclusion of the ideal into the
  regular functions on the chart.  Without it the identification asserts nothing about which
  regular function a conormal section is.
* `AlgebraicGeometry.Space.conormalChartSectionsIso`: **the conormal module read on the sections
  over the base-changed chart.**  The sections of `𝒞_{Z/X}` over `Z ×_X U` are the defining ideal
  of `Z` at `U`.
* `AlgebraicGeometry.Space.conormalChartKerEquiv`: **the conormal data of a presented chart
  thickening.**  The two previous statements composed: `RingHom.ker i^♯` is in bijection with the
  sections of `𝒞_{Z/X}` over `Z ×_X U`.  This is the target-side half of the comparison of
  `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` with the sections of
  `AlgebraicGeometry.Space.liftActionSheaf`.

## Implementation notes

Neither of the two lifts used in the proof of
`AlgebraicGeometry.Space.definingIdealAt_eq_ker_of_isPullback` needs the comparison isomorphism
of the two cartesian squares: the two inclusions of kernels are each an instance of
`AlgebraicGeometry.Space.ker_le_ker_comp`, one per lift, and `le_antisymm` finishes.  The lift
towards the canonical base change is
`CategoryTheory.Functor.relativelyRepresentable.lift`, available because `yoneda` is full; the
lift back is the universal property of the *given* square, taken in presheaves and brought back
to the big fppf site by full faithfulness of `yoneda`.

**The sectionwise reading of the direct image was already in the tree.**
`AlgebraicGeometry.Space.conormalChartSectionsIso` needs the sections of `i_*𝒞_{Z/X}` over `U`
to be the sections of `𝒞_{Z/X}` over `Z ×_X U`, and that is
`AlgebraicGeometry.Space.modulePushforwardChartIso` — the identification of the direct image of
Stacks 03LU with base change of charts, valid for any representable morphism, a closed immersion
being one — together with
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward_obj_val_obj`, which says the sections
of the base-change direct image over `U` *are* the sections over `Z ×_X U`, by `rfl`.  The
argument behind it, that the index category of the limit computing the sections has the
base-changed chart as an initial object, is
`AlgebraicGeometry.Space.chartBaseChangeArrowIsInitial` with
`AlgebraicGeometry.Space.chartRanAppIso`.  A note saying this tree has no sectionwise
identification of sheaves on `Z` with sheaves on `X` — only natural isomorphisms of
direct-image functors — is therefore wrong for a representable morphism.

**The identifications are stated as isomorphisms of `ModuleCat`, or as bare bijections, and not
as `LinearEquiv`s.**  The ideal `RingHom.ker i^♯` is a submodule over the `CommRingCat`-valued
ring of global regular functions on the chart's scheme, while the sections of a module on the
small étale site are indexed by the `RingCat`-valued structure sheaf; the two spellings are
definitionally equal but carry no common `Module` instance that instance resolution finds, so
`LinearEquiv.ofEq` and `Equiv.subtypeEquivRight` both fail on the equality of ideals — the
latter with an `implicit`-transparency type error, which is the signature of that clash.  What
does work is rewriting the *goal's type* by the equality of ideals, which is how
`AlgebraicGeometry.Space.conormalChartKerEquiv` is proved; `…_hom_apply_coe` is what identifies
the underlying regular function of a conormal section, and is what a consumer needing linearity
should go through.

No `@[stacks]` attribute is placed: the computation of the defining ideal over a chart is
[Stacks Project, Tag 03MB], registered on
`AlgebraicGeometry.Space.definingIdealAt_eq_ker`, and the invertibility of the unit is the
first-order case of [Stacks Project, Tag 04CN] discussed in the "Partial coverage" section of
`StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal`.  Nothing here is a new
assertion of either.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : AlgebraicSpaces B S hS}

/-- **The defining ideal of a closed subspace at a presented chart thickening.**  Let `Z ⊆ X` be
a closed subspace, `U` an étale scheme chart of `X`, and let `i : T ⟶ U` be a morphism of the big
fppf site fitting into a cartesian square exhibiting `T` as `Z ×_X U`.  Then the defining ideal
of `Z` over `U` is the kernel of pullback of regular functions along `i`.

`AlgebraicGeometry.Space.definingIdealAt_eq_ker` is this statement at the canonical base change
chosen by representability of `Z.1.ι`; the point here is that any cartesian square will do, which
is what a consumer carrying its own chart thickening has. -/
theorem definingIdealAt_eq_ker_of_isPullback (Z : ClosedSubspaces B S hS X.1)
    (U : SmallEtale B S hS X.1) {T : BigFppfOver B S hS}
    (incl : T ⟶ (SmallEtale.toOver B S hS X.1).obj U)
    (c : yoneda.obj T ⟶ Z.1.toFunctor)
    (hsq : IsPullback (yoneda.map incl) c U.1.hom Z.1.ι) :
    definingIdealAt B S hS X Z (op U) =
      RingHom.ker ((BigFppfOver.toScheme B S hS).map incl).appTop.hom := by
  have hm : Z.2.2.rep.lift c incl hsq.w.symm ≫ Z.2.2.rep.snd U.1.hom = incl :=
    Z.2.2.rep.lift_snd c incl hsq.w.symm
  have hn : yoneda.preimage (hsq.lift (yoneda.map (Z.2.2.rep.snd U.1.hom))
      (Z.2.2.rep.fst U.1.hom) (Z.2.2.rep.isPullback U.1.hom).w.symm) ≫ incl =
      Z.2.2.rep.snd U.1.hom := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, Functor.map_preimage]
    exact hsq.lift_fst _ _ _
  rw [definingIdealAt_eq_ker B S hS X Z U, ← Scheme.Γ_map_op]
  refine le_antisymm ?_ ?_
  · exact hm ▸ ker_le_ker_comp B S hS _ (Z.2.2.rep.snd U.1.hom)
  · exact hn ▸ ker_le_ker_comp B S hS _ incl

/-- **The conormal module of a first-order thickening, read on the sections over an étale scheme
chart of the ambient space.**  The sections over `U` of the pushed-forward conormal module
`i_*𝒞_{Z/X}` are the defining ideal of `Z` at `U`, which
`AlgebraicGeometry.Space.definingIdealAt_eq_ker_of_isPullback` identifies with `RingHom.ker i^♯`
for any presentation of the chart thickening.

This is `AlgebraicGeometry.Space.firstOrderConormalModuleIso` — the unit `𝓘 ⟶ i_*i^*𝓘`, an
isomorphism because the thickening is first order — evaluated at `U`.  It is pinned by
`AlgebraicGeometry.Space.firstOrderConormalChartSectionsIso_hom_apply_coe`. -/
def firstOrderConormalChartSectionsIso (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : SmallEtale B S hS X.1) :
    (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj (op U) ≅
      ((modulePullback B S hS (subspaceInclusion B S hS X Z) ⋙
          modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules).val.obj (op U) :=
  (SheafOfModules.evaluation _ (op U)).mapIso (firstOrderConormalModuleIso B S hS Z hZ)

/-- **The characterising property of
`AlgebraicGeometry.Space.firstOrderConormalChartSectionsIso`.**  The conormal section attached to
a regular function in the defining ideal is carried back to that regular function by
`AlgebraicGeometry.Space.firstOrderConormalModuleι`, the inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X`.

This is `AlgebraicGeometry.Space.firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι`
read on sections. -/
theorem firstOrderConormalChartSectionsIso_hom_apply_coe (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : SmallEtale B S hS X.1)
    (a : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj (op U)) :
    ((firstOrderConormalModuleι B S hS Z hZ).val.app (op U)).hom
        ((firstOrderConormalChartSectionsIso B S hS Z hZ U).hom.hom a) =
      ((definingIdealSheaf B S hS X Z).ι.val.app (op U)).hom a :=
  congrArg (fun m : _ ⟶ SheafOfModules.unit (structureRingSheaf B S hS X) ↦
      (m.val.app (op U)).hom a)
    (firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι B S hS Z hZ)

/-- **The conormal module of a first-order thickening, read on the sections over the
base-changed chart.**  For a chart `U` of `X` the sections of `𝒞_{Z/X}` over the base-changed
chart `Z ×_X U` are the defining ideal of `Z` at `U`.

The three steps: the unit `𝓘 ⟶ i_*𝒞_{Z/X}` is invertible for a first-order thickening
(`AlgebraicGeometry.Space.firstOrderConormalChartSectionsIso`); the conormal module is the
inverse image of the defining ideal sheaf
(`AlgebraicGeometry.Space.modulePushforward_conormalModule_eq`); and for the representable `i`
the direct image is base change of charts, so its sections over `U` are the sections over
`Z ×_X U` (`AlgebraicGeometry.Space.modulePushforwardChartIso`, whose target's sections are
those by `AlgebraicGeometry.Space.smallBaseChangeModulePushforward_obj_val_obj`). -/
def conormalChartSectionsIso (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : SmallEtale B S hS X.1) :
    (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj (op U) ≅
      ((smallBaseChangeModulePushforward.{u, u} B S hS
            (subspaceInclusion B S hS X Z) Z.2.2.rep).obj
        (conormalModule B S hS X Z)).val.obj (op U) :=
  firstOrderConormalChartSectionsIso B S hS Z hZ U ≪≫
    eqToIso (congrArg (fun N : Modules.{u, u} B S hS X.1 X.2 ↦ N.val.obj (op U))
      (modulePushforward_conormalModule_eq B S hS Z).symm) ≪≫
    (SheafOfModules.evaluation _ (op U)).mapIso
      ((modulePushforwardChartIso B S hS (subspaceInclusion B S hS X Z) Z.2.2.rep).app
        (conormalModule B S hS X Z))

/-- **The conormal data of a presented chart thickening is the conormal module's sections over
the base-changed chart.**  For a first-order thickening `Z ⊆ X` and a presentation of
`Z ×_X U` by a closed immersion `i : T ⟶ U` of objects of the big fppf site, the kernel of
`i^♯` on global regular functions is in bijection with the sections of `𝒞_{Z/X}` over the
base-changed chart.

This is the identification that a consumer of the acting sheaf of [Stacks Project, Tag 061D]
needs on the target side: `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` lands in
`RingHom.ker i^♯` and `AlgebraicGeometry.Space.liftActionSheafChartEval` lands in the sections of
`AlgebraicGeometry.Space.conormalModule`. -/
def conormalChartKerEquiv (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : SmallEtale B S hS X.1)
    {T : BigFppfOver B S hS} (incl : T ⟶ (SmallEtale.toOver B S hS X.1).obj U)
    (c : yoneda.obj T ⟶ Z.1.toFunctor)
    (hsq : IsPullback (yoneda.map incl) c U.1.hom Z.1.ι) :
    RingHom.ker ((BigFppfOver.toScheme B S hS).map incl).appTop.hom ≃
      ToType (((smallBaseChangeModulePushforward.{u, u} B S hS
            (subspaceInclusion B S hS X Z) Z.2.2.rep).obj
          (conormalModule B S hS X Z)).val.obj (op U)) :=
  by
  rw [← definingIdealAt_eq_ker_of_isPullback B S hS Z U incl c hsq]
  exact (conormalChartSectionsIso B S hS Z hZ U).toLinearEquiv.toEquiv

end AlgebraicGeometry.Space

end
