module

public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.HypercoveringSections

/-!
# A kernel of a map of module sheaves, recognised on sections

Let `S` be a scheme and let `k : W ⟶ Y`, `g : Y ⟶ Z` be morphisms of `𝒪_S`-modules with
`k ≫ g = 0`.  **If over every open `V` of `S` the sections of `k` exhibit `W(V)` as a kernel of the
sections of `g`, then `k` exhibits `W` as a kernel of `g`.**

This is the transport that the degree-zero half of the relative form of [Stacks, Tag 01GV] needs:
the degree-zero clause of
`Stacks.AlgebraicGeometry.UniversalPushforward.quasiIso_hypercoveringAugNat_app` asks for
`IsIso (kernel.lift ...)` in the category of `𝒪_S`-modules, while what the theory of hypercoverings
supplies is a statement about complexes of sections.

The transport is one-directional, and only that direction is available:  evaluation of sheaves of
modules at an open set is left exact but not exact, so an isomorphism recognised on sections need
not come from an isomorphism of sheaves — except that it does here, because the two statements
being compared are about a *kernel*, which evaluation preserves, and because evaluation is jointly
conservative (`Stacks.SheafOfModulesEvaluation.isIso_of_forall_isIso_evaluation`).

## Main results

* `Stacks.KernelLift.isIso_map_kernelLift`:  for a functor preserving the relevant kernel, the
  image of a `kernel.lift` is an isomorphism as soon as the `kernel.lift` of the images is.  Stated
  for arbitrary categories with zero morphisms.
* `Stacks.AlgebraicGeometry.UniversalPushforward.isIso_kernelLift_of_forall_sections`:  **the
  transport above**, for `𝒪_S`-modules.

## Implementation notes

`Stacks.KernelLift.isIso_map_kernelLift` is the one piece of mathematics:  a kernel-preserving
functor `G` takes `kernel.lift g k w` to `kernel.lift (G g) (G k) w'` composed with the comparison
`CategoryTheory.Limits.kernelComparison`, which is an isomorphism exactly because `G` preserves
that kernel.  The identity is proved by composing with the monomorphism `kernel.ι (G g)`.

Both left exactness of sections — `Stacks.Cohomology.preservesFiniteLimits_sectionsFunctor` — and
additivity are supplied as explicit terms rather than found by typeclass search:
`AlgebraicGeometry.Scheme.Modules` is a `def`, so the `Mathlib` and library instances stated for
`CategoryTheory.SheafOfModules` are not found at the scheme-level spelling.

## References

* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.GenericPointSheaf

universe u

namespace Stacks.KernelLift

/-- **A functor preserving a kernel takes a `kernel.lift` to an isomorphism as soon as the
`kernel.lift` of the images is one.**  The two differ by the comparison
`CategoryTheory.Limits.kernelComparison`, which is an isomorphism because the kernel is
preserved. -/
theorem isIso_map_kernelLift {A B : Type*} [Category A] [Category B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (G : A ⥤ B) [G.PreservesZeroMorphisms]
    {Y Z : A} (g : Y ⟶ Z) [HasKernel g] [HasKernel (G.map g)]
    [PreservesLimit (parallelPair g 0) G] {W : A} (k : W ⟶ Y) (w : k ≫ g = 0)
    (h : IsIso (kernel.lift (G.map g) (G.map k) (by rw [← G.map_comp, w, G.map_zero]))) :
    IsIso (G.map (kernel.lift g k w)) := by
  have : IsIso (G.map (kernel.lift g k w) ≫ kernelComparison g G) := by
    convert h using 1
    refine (cancel_mono (kernel.ι (G.map g))).1 ?_
    rw [Category.assoc, kernelComparison_comp_ι, ← G.map_comp, kernel.lift_ι, kernel.lift_ι]
  exact IsIso.of_isIso_comp_right _ (kernelComparison g G)

end Stacks.KernelLift

namespace Stacks.AlgebraicGeometry.UniversalPushforward

variable {S : Scheme.{u}}

/-- **A morphism of `𝒪_S`-modules which exhibits a kernel on the sections over every open set
exhibits a kernel.**

Evaluation at an open set preserves the kernel, so it takes the comparison `kernel.lift g k w` to
the comparison of the sections; and a morphism of `𝒪_S`-modules whose evaluation at every open set
is an isomorphism is an isomorphism. -/
theorem isIso_kernelLift_of_forall_sections {Y Z W : S.Modules} (g : Y ⟶ Z) (k : W ⟶ Y)
    (w : k ≫ g = 0)
    (h : ∀ V : S.Opens, IsIso (kernel.lift ((sectionsAG S V).map g) ((sectionsAG S V).map k)
      (by rw [← Functor.map_comp, w, Functor.map_zero]))) :
    IsIso (kernel.lift g k w) := by
  refine Stacks.SheafOfModulesEvaluation.isIso_of_forall_isIso_evaluation S.ringCatSheaf
    (kernel.lift g k w) (fun T ↦ ?_)
  have : Limits.PreservesFiniteLimits (sectionsFunctor S T.unop) :=
    Stacks.Cohomology.preservesFiniteLimits_sectionsFunctor S T.unop
  have : IsIso ((forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (op T.unop)))
      AddCommGrpCat.{u}).map ((sectionsFunctor S T.unop).map (kernel.lift g k w))) :=
    Stacks.KernelLift.isIso_map_kernelLift (sectionsAG S T.unop) g k w (h T.unop)
  exact isIso_of_reflects_iso ((sectionsFunctor S T.unop).map (kernel.lift g k w))
    (forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (op T.unop))) AddCommGrpCat.{u})

end Stacks.AlgebraicGeometry.UniversalPushforward

end
