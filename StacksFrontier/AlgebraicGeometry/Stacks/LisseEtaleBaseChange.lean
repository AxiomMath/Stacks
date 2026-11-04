module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothObject
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleTopologyComparison
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.EqualizerCollapse

/-!
# Base change on the lisse-étale site of a scheme

Let `f : X ⟶ Y` be a morphism of schemes over `S` in a big fppf site. Base change along `f`
carries a scheme smooth over `Y` to a scheme smooth over `X`, so it induces a functor between the
lisse-étale sites of the algebraic stacks `X` and `Y` represent, and that functor is continuous.

Continuity is the positive half of **Stacks 07BG**, whose point is that the functor is *not* a
morphism of sites; the counterexample is in
`StacksFrontier/Examples/Stacks/LisseEtaleNotFunctorial.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.LisseEtale.pullback`: the base-change functor
  `Y_{lisse,étale} ⥤ X_{lisse,étale}`.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.associatedTopology_schemeStack`: the étale site of
  **Stacks 06TP** at the stack of a scheme `U` over `S` is the localization at `U` of the big
  étale topology localized at `S`.
* `AlgebraicGeometry.Stack.LisseEtale.isContinuous_pullback`: the base-change functor is
  continuous.

## Implementation notes

`AlgebraicGeometry.Stack.LisseEtale.pullback` is `CategoryTheory.ObjectProperty.lift` of the
composite of the inclusion with `CategoryTheory.Over.pullback`, so composing it with the
inclusion gives that composite back *definitionally*; nothing else would make the continuity
argument below typecheck without a transport.

Continuity is read off from continuity into the ambient étale site by
`CategoryTheory.Functor.isContinuous_of_comp_of_fullyFaithful`: the inclusion of the smooth
objects is fully faithful, continuous and cocontinuous — the last of these being exactly what
`AlgebraicGeometry.Stack.LisseEtale.isCocontinuous_inclusion_topology'` supplies for the generated
topology — and the composite `pullback f ⋙ ι` is `ι ⋙ Over.pullback f`, continuous because
`CategoryTheory.Over.pullback` is right adjoint to `CategoryTheory.Over.map`, which is
cocontinuous for the localized topologies.

That the lisse-étale site of a scheme stack sits inside a *localized* site, rather than inside
the inherited site of a general category fibred in groupoids, is
`CategoryTheory.Over.forget_inheritedTopology`: the structure functor of the stack of `U` is
`CategoryTheory.Over.forget U`.

## References

* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07BG](https://stacks.math.columbia.edu/tag/07BG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The étale site of the stack of a scheme is a localized big étale site.** The structure
functor of the algebraic stack of `U : (Sch/S)_{fppf}` is `CategoryTheory.Over.forget U`, and the
topology a slice inherits along its forgetful functor is the localized topology. -/
theorem associatedTopology_schemeStack (U : BigFppfOver B S hS) :
    associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B) =
      ((etaleTopology B).over (B.obj hS)).over U :=
  Over.forget_inheritedTopology ((etaleTopology B).over (B.obj hS)) U

/-- **Base change on lisse-étale sites of schemes.** For `f : X ⟶ Y` in `(Sch/S)_{fppf}`, the
functor sending a scheme `V` smooth over `Y` to `V ×_Y X`, which is smooth over `X` because
smoothness is stable under base change. -/
noncomputable def pullback {X Y : BigFppfOver B S hS} (f : X ⟶ Y) :
    LisseEtale.{u, w} B S hS (schemeStack.{u, w} B S hS Y) ⥤
      LisseEtale.{u, w} B S hS (schemeStack.{u, w} B S hS X) :=
  (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS X)).lift
    (inclusion.{u, w} B S hS (schemeStack.{u, w} B S hS Y) ⋙ Over.pullback f) (fun V => by
      refine (smoothObject_schemeStack_iff.{u, w} B S hS X _).mpr ?_
      have hV := (smoothObject_schemeStack_iff.{u, w} B S hS Y V.obj).mp V.property
      exact MorphismProperty.of_isPullback
        ((IsPullback.of_hasPullback V.obj.hom f).map (BigFppfOver.toScheme B S hS)) hV)

/-- The base-change functor composed with the inclusion of the smooth objects is the inclusion
followed by base change in the slice. This holds definitionally. -/
theorem pullback_comp_inclusion {X Y : BigFppfOver B S hS} (f : X ⟶ Y) :
    pullback.{u, w} B S hS f ⋙ inclusion.{u, w} B S hS (schemeStack.{u, w} B S hS X) =
      inclusion.{u, w} B S hS (schemeStack.{u, w} B S hS Y) ⋙ Over.pullback f :=
  rfl

/-- **The base-change functor on lisse-étale sites of schemes is continuous.** This is the half
of **Stacks 07BG** that holds: the functor induces an adjoint pair on sheaves, and the point of
07BG is that it is nevertheless not a morphism of sites. -/
theorem isContinuous_pullback {X Y : BigFppfOver B S hS} (f : X ⟶ Y) :
    (pullback.{u, w} B S hS f).IsContinuous
      (topology.{u, w} B S hS (schemeStack.{u, w} B S hS Y))
      (topology.{u, w} B S hS (schemeStack.{u, w} B S hS X)) := by
  have hcont : ∀ Z : BigFppfOver B S hS,
      (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS Z)).ι.IsContinuous
      (topology.{u, w} B S hS (schemeStack.{u, w} B S hS Z))
      (((etaleTopology B).over (B.obj hS)).over Z) := fun Z => by
    rw [← associatedTopology_schemeStack.{u, w} B S hS Z]
    exact isContinuous_inclusion_topology'.{u, w} B S hS _
  have hcoX : (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS X)).ι.IsCocontinuous
      (topology.{u, w} B S hS (schemeStack.{u, w} B S hS X))
      (((etaleTopology B).over (B.obj hS)).over X) := by
    rw [← associatedTopology_schemeStack.{u, w} B S hS X]
    exact isCocontinuous_inclusion_topology'.{u, w} B S hS _
  have hcpb : (Over.pullback f).IsContinuous (((etaleTopology B).over (B.obj hS)).over Y)
      (((etaleTopology B).over (B.obj hS)).over X) := inferInstance
  have hcomp : (pullback.{u, w} B S hS f ⋙
      inclusion.{u, w} B S hS (schemeStack.{u, w} B S hS X)).IsContinuous
      (topology.{u, w} B S hS (schemeStack.{u, w} B S hS Y))
      (((etaleTopology B).over (B.obj hS)).over X) :=
    @Functor.isContinuous_comp _ _ _ _ _ _
      (inclusion.{u, w} B S hS (schemeStack.{u, w} B S hS Y)) (Over.pullback f) _
      (((etaleTopology B).over (B.obj hS)).over Y) _ (hcont Y) hcpb
  exact @Functor.isContinuous_of_comp_of_fullyFaithful _ _ _ _ _ _
    (pullback.{u, w} B S hS f)
    (inclusion.{u, w} B S hS (schemeStack.{u, w} B S hS X)) _ _
    (((etaleTopology B).over (B.obj hS)).over X) (hcont X) hcoX inferInstance inferInstance hcomp

end AlgebraicGeometry.Stack.LisseEtale

end
