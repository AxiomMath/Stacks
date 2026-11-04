module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OverFunctorPullbackMate
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceTransition

/-!
# The transition on a slice of a restricted module is the restricted transition

Let `X` be a simplicial scheme, `(a, W)` an object of its total Zariski site, `φ : b ⟶ a` a map
of simplicial degrees and `F` a sheaf of `𝒪_X`-modules on the whole total Zariski site. The
transition of Stacks 09WF of the restriction `F|_{(a,W)}` to the slice at `(a, W)`, which is
`AlgebraicGeometry.SimplicialScheme.sliceComponentModuleTransition`, is the transition
`(X φ)^* F_a ⟶ F_b` of `F` itself restricted to the open `(X φ)⁻¹W` of `X_b`, read through the
Beck–Chevalley isomorphism `AlgebraicGeometry.SimplicialScheme.sliceSchemePullbackOverFunctorIso`
for the localization of `X φ` at `W`.

Consequently `F` is cartesian in the sense of Stacks 07TF (2) exactly when all the transitions
of all of its restrictions to slices are isomorphisms — which is the form both directions of
Stacks 0D7M use, the local statements of the source being about slices and the cartesian
condition being about the whole simplicial scheme.

## Main results

* `AlgebraicGeometry.SimplicialScheme.sliceComponentModuleTransition_over`: **the transition on
  the slice at `(a, W)` of a restricted module is the restriction to `(X φ)⁻¹W` of the transition
  of the module.**
* `AlgebraicGeometry.SimplicialScheme.isIso_sliceComponentModuleTransition_over_iff`: the two are
  invertible together.
* `AlgebraicGeometry.SimplicialScheme.isIso_componentModuleTransition_of_coversTop`: a transition
  invertible on the preimages of a family of opens covering `X_a` is invertible.

## Implementation notes

Both transitions are mates, so the identity is checked after applying the `homEquiv` of the
localized pullback, which is injective. On the left that returns the *direct* transition on the
slice, which at a restricted module is the restriction of the direct transition of `F` on the
nose: the two composites `(X φ)_* ∘ (-)|_W` and `(-)|_{(X φ)⁻¹W} ∘ (X φ|)_*` are the same
functor, both being the direct image along the inclusion of the slice followed by the inverse
image of opens. On the right it returns, by
`SheafOfModules.homEquiv_overFunctorPullbackIso_hom_app`, the restriction of the unit of the
pullback adjunction followed by the restriction of the direct image of the transition, and that
is the restriction of the direct transition because the direct transition is the image of the
transition under the adjunction.

## References

* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Topology.Simplicial
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable (X : SimplicialObject Scheme.{u}) {a b : SimplexCategoryᵒᵖ} (W : Opens ↥(X.obj a))
  (φ : b ⟶ a)

/-- **The direct transition on a slice of a restricted module is the restricted direct
transition.** On sections over an open `V ≤ W` of `X_a` both sides are the restriction map of `F`
along the arrow of the total Zariski site lying over `φ` above `V`, and the two composites
`(X φ)_* ∘ (-)|_W` and `(-)|_{(X φ)⁻¹W} ∘ (X φ|)_*` are the same functor, so the two sides are the
same morphism. -/
public theorem sliceComponentModuleDirectTransition_over (F : Modules X) :
    (sliceComponentModuleDirectTransition X W φ).app (F.over (sliceObj X a W)) =
      (SheafOfModules.overFunctor.{u} ((X.obj a).ringCatSheaf) W).map
        ((componentModuleDirectTransition X φ).app F) := rfl

/-- **The localized direct image of a restriction is the restriction of the direct image.** The
two composites `(X φ)_* ∘ (-)|_W` and `(-)|_{(X φ)⁻¹W} ∘ (X φ|)_*` are the same functor, so they
agree on morphisms. -/
public theorem sliceSchemePushforward_map_over {G G' : (X.obj b).Modules} (t : G ⟶ G') :
    (sliceSchemePushforward X W φ).map (t.over (slicePreimage X W φ)) =
      (SheafOfModules.overFunctor.{u} ((X.obj a).ringCatSheaf) W).map
        ((Scheme.Modules.pushforward (X.map φ)).map t) := rfl

/-- The direct transition on the slice at `(a, W)` of a restricted module, factored as the
restriction of the unit of the pullback adjunction of `X φ` followed by the localized direct
image of the transition of `F`. -/
public theorem sliceComponentModuleDirectTransition_over_comp (F : Modules X) :
    (sliceComponentModuleDirectTransition X W φ).app (F.over (sliceObj X a W)) =
      (SheafOfModules.overFunctor.{u} ((X.obj a).ringCatSheaf) W).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ)).unit.app
            ((componentModule X a).obj F)) ≫
        (sliceSchemePushforward X W φ).map
          ((componentModuleTransition X φ F).over (slicePreimage X W φ)) := by
  have hdir : (Scheme.Modules.pullbackPushforwardAdjunction (X.map φ)).unit.app
        ((componentModule X a).obj F) ≫
      (Scheme.Modules.pushforward (X.map φ)).map (componentModuleTransition X φ F) =
      (componentModuleDirectTransition X φ).app F :=
    Equiv.apply_symm_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ)).homEquiv
        ((componentModule X a).obj F) ((componentModule X b).obj F))
      ((componentModuleDirectTransition X φ).app F)
  refine Eq.trans (sliceComponentModuleDirectTransition_over X W φ F) ?_
  rw [sliceSchemePushforward_map_over X W φ (componentModuleTransition X φ F)]
  refine Eq.trans ?_ (Functor.map_comp
    (SheafOfModules.overFunctor.{u} ((X.obj a).ringCatSheaf) W)
    ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ)).unit.app
      ((componentModule X a).obj F))
    ((Scheme.Modules.pushforward (X.map φ)).map (componentModuleTransition X φ F)))
  exact congrArg (fun t => (SheafOfModules.overFunctor.{u} ((X.obj a).ringCatSheaf) W).map t)
    hdir.symm

/-- **The transition on a slice of a restricted module is the restricted transition.** For a
sheaf of `𝒪_X`-modules `F` on the whole total Zariski site, the transition of Stacks 09WF of
`F|_{(a,W)}` on the slice at `(a, W)` is the transition `(X φ)^* F_a ⟶ F_b` of `F` restricted to
the open `(X φ)⁻¹W` of `X_b`, through the Beck–Chevalley isomorphism for the localization of
`X φ` at `W`. -/
public theorem sliceComponentModuleTransition_over (F : Modules X) :
    sliceComponentModuleTransition X W φ (F.over (sliceObj X a W)) =
      (sliceSchemePullbackOverFunctorIso X W φ).hom.app ((componentModule X a).obj F) ≫
        ((componentModuleTransition X φ F).over (slicePreimage X W φ)) := by
  have hmate : ((sliceSchemePullbackAdj X W φ).homEquiv _ _)
        ((sliceSchemePullbackOverFunctorIso X W φ).hom.app ((componentModule X a).obj F)) =
      (SheafOfModules.overFunctor.{u} _ W).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ)).unit.app
          ((componentModule X a).obj F)) :=
    SheafOfModules.homEquiv_overFunctorPullbackIso_hom_app.{u}
      ((X.map φ).toRingCatSheafHom) W (starCompOverPostIso (Opens.map (X.map φ).base) W)
      (fun _ => rfl) ((componentModule X a).obj F)
  have hslice : ((sliceSchemePullbackAdj X W φ).homEquiv _ _)
      (sliceComponentModuleTransition X W φ (F.over (sliceObj X a W))) =
      (sliceComponentModuleDirectTransition X W φ).app (F.over (sliceObj X a W)) :=
    Equiv.apply_symm_apply _ _
  refine ((sliceSchemePullbackAdj X W φ).homEquiv _ _).injective ?_
  refine Eq.trans hslice ?_
  refine Eq.trans (sliceComponentModuleDirectTransition_over_comp X W φ F) ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right (sliceSchemePullbackAdj X W φ)
    ((sliceSchemePullbackOverFunctorIso X W φ).hom.app ((componentModule X a).obj F))
    ((componentModuleTransition X φ F).over (slicePreimage X W φ))).symm
  exact congrArg (fun t => t ≫ (sliceSchemePushforward X W φ).map
    ((componentModuleTransition X φ F).over (slicePreimage X W φ))) hmate.symm

/-- The transition on the slice at `(a, W)` of a restricted module and the restriction of the
transition of the module to `(X φ)⁻¹W` are invertible together: they differ by the
Beck–Chevalley isomorphism for the localization of `X φ` at `W`. -/
public theorem isIso_sliceComponentModuleTransition_over_iff (F : Modules X) :
    IsIso (sliceComponentModuleTransition X W φ (F.over (sliceObj X a W))) ↔
      IsIso ((componentModuleTransition X φ F).over (slicePreimage X W φ)) := by
  have heq : sliceComponentModuleTransition X W φ (F.over (sliceObj X a W)) =
      ((sliceSchemePullbackOverFunctorIso X W φ).app ((componentModule X a).obj F)).hom ≫
        (componentModuleTransition X φ F).over (slicePreimage X W φ) :=
    sliceComponentModuleTransition_over X W φ F
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have key : (componentModuleTransition X φ F).over (slicePreimage X W φ) =
        (((sliceSchemePullbackOverFunctorIso X W φ).app
            ((componentModule X a).obj F)).symm ≪≫ (@asIso _ _ _ _ _ h)).hom :=
      ((Iso.inv_comp_eq
        ((sliceSchemePullbackOverFunctorIso X W φ).app ((componentModule X a).obj F))).2 heq).symm
    rw [key]
    exact Iso.isIso_hom _
  · have key : sliceComponentModuleTransition X W φ (F.over (sliceObj X a W)) =
        ((sliceSchemePullbackOverFunctorIso X W φ).app ((componentModule X a).obj F) ≪≫
          (@asIso _ _ _ _ _ h)).hom := heq
    rw [key]
    exact Iso.isIso_hom _

/-- **A transition invertible on the preimages of a covering family is invertible.** If a family
of opens of `X_a` covers the top and the transition of `F` at `φ : b ⟶ a` is invertible after
restriction to the preimage of each member, then the transition is invertible. -/
public theorem isIso_componentModuleTransition_of_coversTop (F : Modules X) {I : Type u}
    (V : I → Opens ↥(X.obj a))
    (hV : (Opens.grothendieckTopology ↥(X.obj b)).CoversTop
      fun i => slicePreimage X (V i) φ)
    (h : ∀ i, IsIso (sliceComponentModuleTransition X (V i) φ
      (F.over (sliceObj X a (V i))))) :
    IsIso (componentModuleTransition X φ F) :=
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hV _
    fun i => (isIso_sliceComponentModuleTransition_over_iff X (V i) φ F).1 (h i)

end AlgebraicGeometry.SimplicialScheme

end
