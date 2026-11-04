module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceTransition

/-!
# The counit of the slice adjunction, and the transition it factors

Let `X` be a simplicial scheme and `(a, W)` an object of its total Zariski site. The pullback
`AlgebraicGeometry.SimplicialScheme.sliceModulePullback` to the slice at `(a, W)` is left adjoint
to the degree-`a` component functor on the slice, and its counit `ε_M : L_a(M_a) ⟶ M` is the
comparison that makes `M` the pullback of its degree-`a` component. For a map of simplicial
degrees `φ : b ⟶ a` the degree-`φ` component of that counit is what the converse direction of
Stacks 0D7M has to invert.

This file factors the transition of Stacks 09WF on the slice through that counit: there is a
comparison `γ_N : (X φ|)^* N ⟶ (L_a N)_φ` — the localized pullback along `X φ` of a module on the
slice of the degree-`a` site, compared with the degree-`φ` component of its pullback to the slice
of the total site — and

  `transition at M = γ at M_a  followed by  the degree-φ component of the counit at M`.

Both factors on the right are invertible when `M_a` admits a presentation and the transition is
invertible, so the counit itself is then invertible by the joint conservativity of the component
functors on a slice. That is the step the converse of Stacks 0D7M turns into a presentation.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.sliceModulePullbackComparison`: the comparison `γ`, the mate
  of the unit of the slice adjunction followed by the direct transition.

## Main results

* `AlgebraicGeometry.SimplicialScheme.sliceComponentModuleTransition_eq`: **the transition on the
  slice factors as `γ` followed by the degree-`φ` component of the counit.**
* `AlgebraicGeometry.SimplicialScheme.isIso_sliceModulePullbackComparison_unit`: `γ` is invertible
  on the structure sheaf of the slice of the degree-`a` site.
* `AlgebraicGeometry.SimplicialScheme.isIso_sliceModulePullbackComparison_of_presentation`: hence
  on every module with a global presentation.
* `AlgebraicGeometry.SimplicialScheme.isIso_sliceCounit_of_isIso_transition`: **the counit is
  invertible as soon as the degree-`a` component of `M` admits a presentation and every
  transition of `M` is invertible.**

## Implementation notes

The factorization is proved by applying the `homEquiv` of the localized pullback, which is
injective: on the left it returns the direct transition at `M`, and on the right the unit of the
slice adjunction at `M_a` followed by the direct transition at `L_a(M_a)` followed by the
direct image of the degree-`φ` component of the counit. Naturality of the direct transition turns
the last two into the degree-`a` component of the counit followed by the direct transition at
`M`, and the triangle identity of the slice adjunction kills the first two.

Invertibility of `γ` on the structure sheaf is read off the same factorization at `M` the
structure sheaf of the slice of the total site, where both the transition and the counit are
already known to be invertible; the value at the structure sheaf of the slice of the *degree*
site is then reached along the identification of the two, which is
`AlgebraicGeometry.SimplicialScheme.sliceComponentUnitHom`.

## References

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

/-- **The comparison between the localized pullback along `X φ` and the degree-`φ` component of
the pullback to the slice.** For a module `N` on the slice of the degree-`a` site at `W` it is the
mate of the unit of the slice adjunction at `N` followed by the direct transition of Stacks 09WF
at `L_a N`. -/
public noncomputable def sliceModulePullbackComparison :
    sliceSchemePullback X W φ ⟶
      sliceModulePullback X a W ⋙ sliceComponentModuleAt X W φ where
  app N := ((sliceSchemePullbackAdj X W φ).homEquiv _ _).symm
    ((sliceModulePullbackAdj X a W).unit.app N ≫
      (sliceComponentModuleDirectTransition X W φ).app ((sliceModulePullback X a W).obj N))
  naturality N N' f := by
    refine ((sliceSchemePullbackAdj X W φ).homEquiv _ _).injective ?_
    refine Eq.trans (Adjunction.homEquiv_naturality_left (sliceSchemePullbackAdj X W φ) f _) ?_
    refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right (sliceSchemePullbackAdj X W φ) _
      ((sliceModulePullback X a W ⋙ sliceComponentModuleAt X W φ).map f)).symm
    have hnat1 : f ≫ (sliceModulePullbackAdj X a W).unit.app N' =
        (sliceModulePullbackAdj X a W).unit.app N ≫
          (sliceComponentModule X a W).map ((sliceModulePullback X a W).map f) :=
      (sliceModulePullbackAdj X a W).unit.naturality f
    have hnat2 : (sliceComponentModule X a W).map ((sliceModulePullback X a W).map f) ≫
        (sliceComponentModuleDirectTransition X W φ).app
          ((sliceModulePullback X a W).obj N') =
        (sliceComponentModuleDirectTransition X W φ).app
            ((sliceModulePullback X a W).obj N) ≫
          (sliceSchemePushforward X W φ).map
            ((sliceModulePullback X a W ⋙ sliceComponentModuleAt X W φ).map f) :=
      (sliceComponentModuleDirectTransition X W φ).naturality
        ((sliceModulePullback X a W).map f)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← Category.assoc, hnat1, Category.assoc,
      hnat2, ← Category.assoc]

/-- The component of `sliceModulePullbackComparison` at `N` is the adjunct, under the
adjunction `sliceSchemePullbackAdj`, of the unit of `sliceModulePullbackAdj` at `N` followed by
`sliceComponentModuleDirectTransition` at the pullback of `N`. -/
@[simp] public theorem sliceModulePullbackComparison_app
    (N : @SheafOfModules.{u} (Over W) _ _ (sliceDegreeRingSheaf X a W)) :
    (sliceModulePullbackComparison X W φ).app N =
      ((sliceSchemePullbackAdj X W φ).homEquiv _ _).symm
        ((sliceModulePullbackAdj X a W).unit.app N ≫
          (sliceComponentModuleDirectTransition X W φ).app
            ((sliceModulePullback X a W).obj N)) := rfl

/-- **The transition on the slice factors through the counit.** The transition of Stacks 09WF at
a module `M` on the slice at `(a, W)` is the comparison `γ` at the degree-`a` component of `M`,
followed by the degree-`φ` component of the counit of the slice adjunction at `M`. -/
public theorem sliceComponentModuleTransition_eq
    (M : @SheafOfModules.{u} (Over (sliceObj X a W)) _ _ (sliceStructureRingSheaf X a W)) :
    sliceComponentModuleTransition X W φ M =
      (sliceModulePullbackComparison X W φ).app ((sliceComponentModule X a W).obj M) ≫
        (sliceComponentModuleAt X W φ).map ((sliceModulePullbackAdj X a W).counit.app M) := by
  have hts : ((sliceSchemePullbackAdj X W φ).homEquiv _ _)
      (sliceComponentModuleTransition X W φ M) =
      (sliceComponentModuleDirectTransition X W φ).app M :=
    Equiv.apply_symm_apply _ _
  have hγ : ((sliceSchemePullbackAdj X W φ).homEquiv _ _)
      ((sliceModulePullbackComparison X W φ).app ((sliceComponentModule X a W).obj M)) =
      (sliceModulePullbackAdj X a W).unit.app ((sliceComponentModule X a W).obj M) ≫
        (sliceComponentModuleDirectTransition X W φ).app
          ((sliceModulePullback X a W).obj ((sliceComponentModule X a W).obj M)) :=
    Equiv.apply_symm_apply _ _
  have hnat : (sliceComponentModuleDirectTransition X W φ).app
        ((sliceModulePullback X a W).obj ((sliceComponentModule X a W).obj M)) ≫
      (sliceSchemePushforward X W φ).map ((sliceComponentModuleAt X W φ).map
        ((sliceModulePullbackAdj X a W).counit.app M)) =
      (sliceComponentModule X a W).map ((sliceModulePullbackAdj X a W).counit.app M) ≫
        (sliceComponentModuleDirectTransition X W φ).app M :=
    ((sliceComponentModuleDirectTransition X W φ).naturality
      ((sliceModulePullbackAdj X a W).counit.app M)).symm
  refine ((sliceSchemePullbackAdj X W φ).homEquiv _ _).injective ?_
  refine Eq.trans hts ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right (sliceSchemePullbackAdj X W φ)
    ((sliceModulePullbackComparison X W φ).app ((sliceComponentModule X a W).obj M))
    ((sliceComponentModuleAt X W φ).map
      ((sliceModulePullbackAdj X a W).counit.app M))).symm
  rw [hγ, Category.assoc, hnat, ← Category.assoc, Adjunction.right_triangle_components,
    Category.id_comp]

/-- **The comparison `γ` is invertible on the structure sheaf of the slice of the degree-`a`
site.** -/
public theorem isIso_sliceModulePullbackComparison_unit :
    IsIso ((sliceModulePullbackComparison X W φ).app
      (SheafOfModules.unit (sliceDegreeRingSheaf X a W))) := by
  have h₁ : IsIso ((sliceModulePullbackComparison X W φ).app
      ((sliceComponentModule X a W).obj
        (SheafOfModules.unit (sliceStructureRingSheaf X a W)))) := by
    have ht := isIso_sliceComponentModuleTransition_unit X W φ
    have he := isIso_sliceCounit_unit X a W
    have hc : IsIso ((sliceComponentModuleAt X W φ).map
        ((sliceModulePullbackAdj X a W).counit.app
          (SheafOfModules.unit (sliceStructureRingSheaf X a W)))) := Functor.map_isIso _ _
    exact IsIso.of_isIso_fac_right
      (sliceComponentModuleTransition_eq X W φ
        (SheafOfModules.unit (sliceStructureRingSheaf X a W))).symm
  have hcu : IsIso ((sliceModulePullback X a W ⋙ sliceComponentModuleAt X W φ).map
      (sliceComponentUnitHom X W)) := Functor.map_isIso _ _
  have hmu : IsIso ((sliceSchemePullback X W φ).map (sliceComponentUnitHom X W)) :=
    Functor.map_isIso _ _
  have : IsIso ((sliceSchemePullback X W φ).map (sliceComponentUnitHom X W) ≫
      (sliceModulePullbackComparison X W φ).app _) := inferInstance
  exact IsIso.of_isIso_fac_right
    ((sliceModulePullbackComparison X W φ).naturality (sliceComponentUnitHom X W)).symm

/-- **The comparison `γ` is invertible on a presented module.** It is a natural transformation
between two functors that preserve colimits and it is invertible on the structure sheaf. -/
public theorem isIso_sliceModulePullbackComparison_of_presentation
    (N : @SheafOfModules.{u} (Over W) _ _ (sliceDegreeRingSheaf X a W))
    (P : N.Presentation) :
    IsIso ((sliceModulePullbackComparison X W φ).app N) := by
  have h1 : PreservesColimitsOfSize.{u, u}
      (sliceModulePullback X a W ⋙ sliceComponentModuleAt X W φ) :=
    Limits.comp_preservesColimits _ _
  have h2 : PreservesFiniteColimits
      (sliceModulePullback X a W ⋙ sliceComponentModuleAt X W φ) :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  have h3 : PreservesFiniteColimits (sliceSchemePullback X W φ) :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  have h4 : ∀ I : Type u, Limits.PreservesColimitsOfShape (Discrete I)
      (sliceModulePullback X a W ⋙ sliceComponentModuleAt X W φ) := fun _ => inferInstance
  have h5 : ∀ I : Type u, Limits.PreservesColimitsOfShape (Discrete I)
      (sliceSchemePullback X W φ) := fun _ => inferInstance
  exact Stacks.SheafOfModules.isIso_app_of_presentation_of_unit
    (sliceModulePullbackComparison X W φ)
    (isIso_sliceModulePullbackComparison_unit X W φ) P

/-- **The counit of the slice adjunction is invertible when the component is presented and every
transition is invertible.** This is the step the converse direction of Stacks 0D7M runs on: the
degree-`φ` component of the counit is a factor of the transition, the other factor is invertible
because the degree-`a` component of `M` admits a presentation, and the component functors on a
slice are jointly conservative. -/
public theorem isIso_sliceCounit_of_isIso_transition
    (M : @SheafOfModules.{u} (Over (sliceObj X a W)) _ _ (sliceStructureRingSheaf X a W))
    (P : ((sliceComponentModule X a W).obj M).Presentation)
    (h : ∀ (c : SimplexCategoryᵒᵖ) (ψ : c ⟶ a),
      IsIso (sliceComponentModuleTransition X W ψ M)) :
    IsIso ((sliceModulePullbackAdj X a W).counit.app M) := by
  refine isIso_of_forall_isIso_sliceComponentModuleAt X W _ fun c ψ => ?_
  have ht := h c ψ
  have hγ := isIso_sliceModulePullbackComparison_of_presentation X W ψ
    ((sliceComponentModule X a W).obj M) P
  exact IsIso.of_isIso_fac_left (sliceComponentModuleTransition_eq X W ψ M).symm

end AlgebraicGeometry.SimplicialScheme

end
