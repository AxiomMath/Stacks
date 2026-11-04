module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import Mathlib.CategoryTheory.Subobject.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.GraphKernel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending quasi-coherent modules across a quasi-compact open immersion

Let `j : U ⟶ X` be a quasi-compact open immersion of schemes. Three extension statements hold,
and together they are Stacks Tag 01PE: a quasi-coherent module on `U` is the restriction of one
on `X`; a morphism from a quasi-coherent module on `U` into the restriction of a quasi-coherent
module `F` on `X` is the restriction of a morphism into `F`; and a quasi-coherent submodule of
the restriction of `F` is the restriction of a quasi-coherent submodule of `F`.

## Main results

* `AlgebraicGeometry.exists_quasicoherent_extension`: the morphism extension. The module
  extension it builds on is `AlgebraicGeometry.exists_quasicoherent_restrict_iso`, in
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/OpenExtension.lean`.
* `AlgebraicGeometry.exists_quasicoherentSubobject_restrict`: the submodule extension, with the
  equality of subobjects after restriction expressed as an isomorphism commuting with the two
  inclusions into the restricted ambient module.

## Implementation notes

The first statement needs only that pushforward along a quasi-compact open immersion preserves
quasi-coherence (Tag 01LC) together with the counit isomorphism
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`, which says that restricting a
direct image along an open immersion returns the original module.

The other two are the graph-kernel construction of
`StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.GraphKernel`, read through the natural
isomorphism `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` between restriction
and inverse image: the graph kernel is built from a map into the inverse image, while the
statements of the tag are phrased with restriction. `AlgebraicGeometry.restrictGraphKernelIso`
and `AlgebraicGeometry.restrictGraphKernelIso_hom_comp` perform that transport once, so both
theorems are then immediate.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) (G : U.Modules)

/-- The graph kernel of a morphism `φ : G ⟶ F.restrict j` extends `G`: its restriction along `j`
is canonically isomorphic to `G`. This is `graphKernelPullbackIso` read through the natural
isomorphism between restriction and inverse image. -/
noncomputable def restrictGraphKernelIso (φ : G ⟶ F.restrict j) :
    (graphKernel j F G (φ ≫ (restrictFunctorIsoPullback j).hom.app F)).restrict j ≅ G :=
  (restrictFunctorIsoPullback j).app
      (graphKernel j F G (φ ≫ (restrictFunctorIsoPullback j).hom.app F)) ≪≫
    graphKernelPullbackIso j F G (φ ≫ (restrictFunctorIsoPullback j).hom.app F)

/-- Under `restrictGraphKernelIso`, the restriction of the graph projection is `φ`. -/
lemma restrictGraphKernelIso_hom_comp (φ : G ⟶ F.restrict j) :
    (restrictGraphKernelIso j F G φ).hom ≫ φ =
      (restrictFunctor j).map
        (graphKernelProjection j F G (φ ≫ (restrictFunctorIsoPullback j).hom.app F)) := by
  refine (cancel_mono ((restrictFunctorIsoPullback j).hom.app F)).1 ?_
  rw [restrictGraphKernelIso, Iso.trans_hom, Category.assoc, Category.assoc,
    graphKernelPullbackIso_hom_comp]
  exact ((restrictFunctorIsoPullback j).hom.naturality _).symm

end AlgebraicGeometry

namespace AlgebraicGeometry

end AlgebraicGeometry

end
