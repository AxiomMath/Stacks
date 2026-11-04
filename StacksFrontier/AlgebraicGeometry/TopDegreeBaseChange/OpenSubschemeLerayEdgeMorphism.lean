module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeCrossingInvertible
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite

/-!
# The edge morphism carried across the open-subscheme reading of the Leray comparison's target

The `γ⁺` side of conclusion (c) of [Stacks, Tag 0EX3] reads its prefix at `(f, V)` on the ambient
`X`, through the edge morphism of the Leray comparison's target `Rf_* ⋙ RΓ(V, -)`; the `ψ` side's
[Stacks, Tag 089W] reads the same place on the open subscheme `f⁻¹V`, through the edge morphism of
`…TopDegreeBaseChange.derivedPushforwardSectionsOpenSubscheme`. Those two targets are two right
derived functors of **one** degreewise functor — `Stacks.Cohomology.DerivedSectionsLeray`
`.preimageSections f V`, by `…TopDegreeBaseChange.openSubschemeLerayUnit` being
`…openSubschemeUnitOfIsoUnit` at that functor's own crossing — so the passage between the two edge
morphisms costs no hypothesis at all: it is
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.derivedHomologyComparison_naturality_natTrans` at the **identity** transformation, with
`Rα := …openSubschemeLerayComparison f V`.

This file performs that passage. It is the engine of the join that instantiates the `hPre` of
`…TopDegreeBaseChange.prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison` —
which reads the `γ⁺` prefix at `(f, V)` — from
`…TopDegreeBaseChange.prefix_transport_eq_openSubschemeSectionsComparison_comp`, which matches
factor (1) of [Stacks, Tag 089W] at `((f ∣_ V), ⊤)`.

## Main results

* `…TopDegreeBaseChange.isRightDerivedFunctor_openSubschemeLerayUnit` — **the open-subscheme
  reading of the Leray comparison's target is a right derived functor of degreewise sections over
  `f⁻¹V`**, at `…TopDegreeBaseChange.openSubschemeLerayUnit`. Nothing is assumed of `f` or of `V`.
* `…TopDegreeBaseChange.openSubschemeLerayComparison_fac` — the factorisation that characterises
  `…TopDegreeBaseChange.openSubschemeLerayComparison`, at the level of transformations rather than
  at a component.
* `…TopDegreeBaseChange.derivedHomologyComparison_lerayUnit_eq` — **the passage.** The edge
  morphism of `Rf_* ⋙ RΓ(V, -)` at `lerayUnit` in degree `q` is the degree-`q` cohomology of
  `…openSubschemeLerayComparison f V`, then the edge morphism of
  `…derivedPushforwardSectionsOpenSubscheme f V` at `…openSubschemeLerayUnit f V`.

  **Nothing is assumed** of `f`, of `V` or of `q` — no affineness, no quasi-compactness, no
  quasi-separatedness, no boundedness and no quasi-coherence.

## Implementation notes

*The instance is the general brick at the Leray unit upstairs.*
`…TopDegreeBaseChange.isRightDerivedFunctor_openSubschemeUnitOfIsoUnit`
(`LerayOpenSubschemeCrossingInvertible.lean`) takes an iso presentation of the degreewise crossing
and any right derived functor upstairs; the one here is
`…TopDegreeBaseChange.preimageSectionsOpenSubschemePushforwardIso` together with
`Stacks.Cohomology.DerivedSectionsLeray.lerayUnit (f ∣_ V) ⊤`, whose universal property is
`…DerivedSectionsLeray.isRightDerivedFunctor_lerayUnit`. Its sibling
`…isRightDerivedFunctor_openSubschemeSectionsUnit` is the same brick at the *preimage-sections*
unit upstairs; neither subsumes the other, the two targets being different functors.

*It has to be an `instance` and not a `have` inside the proof.*
`…HomologyComparison.derivedHomologyComparison` takes the universal property as an **instance**
argument, so it is demanded while the statement below is being elaborated, before any tactic runs
— with the universal property supplied only by a `haveI` in the proof, instance
synthesis fails on the statement itself and the `derivedHomologyComparison` of its right-hand side
is replaced by an elaboration placeholder, so the goal that reaches the tactic block is not the
statement that was written.

*The transformation-level factorisation is written out rather than reused.*
`…TopDegreeBaseChange.openSubschemeLerayComparison_fac_app` (`LerayOpenSubschemeDerived.lean`) is
the same content at a component; the brick's `hRα` is an equation of transformations, so the
un-applied form is what it consumes. Both are one `CategoryTheory.Functor.rightDerived_fac`
(respectively `…_fac_app`) and neither is a second proof of anything.

*The identity transformation's two whiskerings are the whole of the bookkeeping.* At `α = 𝟙` the
brick's `hRα` carries `NatTrans.mapHomotopyCategory (𝟙 _) (ComplexShape.up ℤ)` whiskered by
`DerivedCategory.Qh`, and its conclusion carries `𝟙` whiskered by the homology functor;
`CategoryTheory.NatTrans.mapHomotopyCategory_id`, `CategoryTheory.Functor.whiskerRight_id'` and
`CategoryTheory.Functor.whiskerLeft_id'` dispose of them.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 0D5W] carries its own where the Leray
comparison is built, and conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward
  exists_quasiIso_isKInjective)
open Stacks.Cohomology.DerivedSectionsLeray (preimageSections derivedSectionsOverOpen lerayUnit)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison
  derivedHomologyComparison_naturality_natTrans)

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- **The open-subscheme reading of the Leray comparison's target is a right derived functor of
degreewise sections over `f⁻¹V`**, at `…TopDegreeBaseChange.openSubschemeLerayUnit`. It is
`…TopDegreeBaseChange.isRightDerivedFunctor_openSubschemeUnitOfIsoUnit` at the direct-image
presentation `…TopDegreeBaseChange.preimageSectionsOpenSubschemePushforwardIso` of the degreewise
crossing and at `Stacks.Cohomology.DerivedSectionsLeray.lerayUnit (f ∣_ V) ⊤`, whose own universal
property is `…DerivedSectionsLeray.isRightDerivedFunctor_lerayUnit`.

Its sibling `…TopDegreeBaseChange.isRightDerivedFunctor_openSubschemeSectionsUnit` is the same
brick with `RΓ((f ∣_ V)⁻¹⊤, -)` upstairs instead of the Leray comparison's target; the two targets
are different functors, so neither instance subsumes the other.

**Nothing is assumed** of `f` or of `V`. -/
instance isRightDerivedFunctor_openSubschemeLerayUnit :
    (derivedPushforwardSectionsOpenSubscheme f V).IsRightDerivedFunctor
      (openSubschemeLerayUnit f V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_openSubschemeUnitOfIsoUnit f V
    (preimageSectionsOpenSubschemePushforwardIso f V)
    (lerayUnit (f ∣_ V).toLRSHom.toShHom ⊤)

/-- **The equation characterizing `…TopDegreeBaseChange.openSubschemeLerayComparison`, at the level
of transformations.** Composing it with `Stacks.Cohomology.DerivedSectionsLeray.lerayUnit f V`
recovers `…TopDegreeBaseChange.openSubschemeLerayUnit f V`.

`…TopDegreeBaseChange.openSubschemeLerayComparison_fac_app` is the same content at a component;
this is `CategoryTheory.Functor.rightDerived_fac` where that is `…_fac_app`, and the un-applied
form is what an equation of transformations consumes. Nothing is assumed of `f` or of `V`. -/
theorem openSubschemeLerayComparison_fac :
    lerayUnit f.toLRSHom.toShHom V ≫
        Functor.whiskerLeft DerivedCategory.Qh (openSubschemeLerayComparison f V) =
      openSubschemeLerayUnit f V :=
  (derivedPushforward f.toLRSHom.toShHom ⋙
      derivedSectionsOverOpen S.toRingedSpace V).rightDerived_fac
    (lerayUnit f.toLRSHom.toShHom V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ (openSubschemeLerayUnit f V)

/-- **The edge morphism of the Leray comparison's target, carried onto the open-subscheme
reading.** For a morphism of schemes `f : X ⟶ S`, an open `V ⊆ S` and a degree `q`, the edge
morphism of `Rf_* ⋙ RΓ(V, -)` at `Stacks.Cohomology.DerivedSectionsLeray.lerayUnit f V` is the
degree-`q` cohomology of `…TopDegreeBaseChange.openSubschemeLerayComparison f V`, followed by the
edge morphism of `…TopDegreeBaseChange.derivedPushforwardSectionsOpenSubscheme f V` at
`…TopDegreeBaseChange.openSubschemeLerayUnit f V`.

Both targets are right derived functors of the **same** degreewise functor
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections f V` — the second by
`isRightDerivedFunctor_openSubschemeLerayUnit` — so this is
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.derivedHomologyComparison_naturality_natTrans` at the **identity** transformation of that
functor, with `Rα := openSubschemeLerayComparison f V` and `hRα := openSubschemeLerayComparison`
`_fac`. Nothing canonical relates two right derived functors of two *different* functors, which is
why that brick takes `Rα` as data; here it is already named.

**Nothing is assumed** of `f`, of `V` or of `q`: no affineness, no quasi-compactness, no
quasi-separatedness, no boundedness and no quasi-coherence. In particular
`…TopDegreeBaseChange.isIso_openSubschemeLerayComparison` is not used — the passage is an equation
and inverts nothing. -/
theorem derivedHomologyComparison_lerayUnit_eq (q : ℤ) :
    derivedHomologyComparison (preimageSections f.toLRSHom.toShHom V)
          (derivedPushforward f.toLRSHom.toShHom ⋙ derivedSectionsOverOpen S.toRingedSpace V)
          (lerayUnit f.toLRSHom.toShHom V)
          (exists_quasiIso_isKInjective X.toRingedSpace) q =
      Functor.whiskerRight (openSubschemeLerayComparison f V)
          (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) q) ≫
        derivedHomologyComparison (preimageSections f.toLRSHom.toShHom V)
          (derivedPushforwardSectionsOpenSubscheme f V)
          (openSubschemeLerayUnit f V)
          (exists_quasiIso_isKInjective X.toRingedSpace) q := by
  have hbrick := derivedHomologyComparison_naturality_natTrans
    (F := preimageSections f.toLRSHom.toShHom V)
    (G := preimageSections f.toLRSHom.toShHom V) (𝟙 _)
    (derivedPushforward f.toLRSHom.toShHom ⋙ derivedSectionsOverOpen S.toRingedSpace V)
    (lerayUnit f.toLRSHom.toShHom V)
    (derivedPushforwardSectionsOpenSubscheme f V) (openSubschemeLerayUnit f V)
    (openSubschemeLerayComparison f V)
    (by rw [NatTrans.mapHomotopyCategory_id, Functor.whiskerRight_id', Category.id_comp]
        exact (openSubschemeLerayComparison_fac f V).symm)
    (exists_quasiIso_isKInjective X.toRingedSpace) q
  rw [Functor.whiskerLeft_id', Category.comp_id] at hbrick
  exact hbrick

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
