module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Exactness of a short complex of modules is étale local

Let `X` be an algebraic space over a scheme `S` and let `a : yoneda.obj U ⟶ X.1` be an étale
scheme chart of `X` which is surjective on points.  This file shows that a short complex of
modules on the small étale site of `X` is exact exactly when its inverse image along `a` is, and
likewise for short exactness.

## The two halves

The inverse image of modules along an étale morphism is exact — `AlgebraicGeometry.Space.`
`modulePullback_exact`, Stacks 03LV — and when the chart is surjective on points it is also
faithful, by `AlgebraicGeometry.Space.faithful_modulePullback`.  An exact functor preserves the
homology of a short complex, so it carries exact complexes to exact complexes; a faithful one
reflects the vanishing of that homology, because vanishing is the identity of the homology object
being zero and a faithful functor is injective on morphisms.  Both halves are therefore readings
of `CategoryTheory.ShortComplex.exact_map_iff_of_faithful`, with the exactness supplying the
homology-preservation instances and the surjectivity of the chart supplying faithfulness.

For short exactness the same functor reflects the monomorphism at the left and the epimorphism at
the right, a faithful functor reflecting both, which is the argument already made for
monomorphisms alone in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/
ConormalShortExact.lean`, in the directory
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/`,
by `AlgebraicGeometry.Space.mono_modulePullback_schemeChart_iff`.

## Main results

* `AlgebraicGeometry.Space.exact_modulePullback_schemeChart_iff`: a short complex of modules on
  the small étale site of an algebraic space is exact exactly when its inverse image along an
  étale scheme chart surjective on points is exact.
* `AlgebraicGeometry.Space.shortExact_modulePullback_schemeChart_iff`: the same for short
  exactness.
* `AlgebraicGeometry.Space.exact_of_exact_modulePullback_schemeChart` and
  `AlgebraicGeometry.Space.shortExact_of_shortExact_modulePullback_schemeChart`: the descent
  directions on their own, which is the shape in which a reduction to the case of schemes
  delivers exactness on an algebraic space.

## No tag is registered

Stacks 03LV asserts that the inverse image of modules along an étale morphism is exact, which is
the forward half here and is already carried by `AlgebraicGeometry.Space.modulePullback_exact`.
The reflection — the half with content, descending exactness from the chart — is a proof step in
the Stacks project's arguments about algebraic spaces rather than a clause of a tag of its own,
exactly as for the monomorphism case `mono_modulePullback_schemeChart_iff`, which likewise
registers nothing.  So nothing is registered here.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV), exactness of the inverse
  image of modules along an étale morphism.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the inverse image itself.
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW), its identification with
  étale restriction, through which faithfulness is proved.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart and what it gives

Everything below is read off one étale scheme chart surjective on points.  The three facts drawn
from it — étaleness of the induced morphism of spaces, faithfulness of the inverse image, and its
exactness — are isolated here so the four results share them. -/

section Chart

variable {X : AlgebraicSpaces B S hS} (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1)
    (haEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)

include haEtale

/-- The morphism of algebraic spaces induced by an étale scheme chart is étale. -/
public theorem isEtale_schemeChart_hom :
    IsEtale B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X).hom :=
  isEtale_of_presheaf_etale B S hS haEtale

/-- The inverse image of modules along an étale scheme chart is exact, by Stacks 03LV. -/
public theorem exactFunctor_modulePullback_schemeChart :
    exactFunctor (Modules.{u, u} B S hS X.1 X.2)
      (Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
      (modulePullback B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X)) :=
  modulePullback_exact B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X)
    (isEtale_schemeChart_hom B S hS U a haEtale)

include haSurj

/-- The inverse image of modules along an étale scheme chart which is surjective on points is
faithful. -/
public theorem faithful_modulePullback_schemeChart :
    (modulePullback B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X)).Faithful :=
  faithful_modulePullback B S hS U (ObjectProperty.homMk a)
    (isEtale_schemeChart_hom B S hS U a haEtale) haSurj

end Chart

/-! ### Exactness descends along a surjective étale scheme chart -/

section Descent

variable {X : AlgebraicSpaces B S hS} (σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1)
    (haEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)

include haEtale haSurj

/-- **Exactness of a short complex of modules on the small étale site is étale local.**  For an
étale scheme chart `a` of an algebraic space which is surjective on points, a short complex of
modules is exact exactly when its inverse image along `a` is: the inverse image is exact by
Stacks 03LV, hence preserves the homology of the complex, and it is faithful because `a` is
surjective, hence reflects the vanishing of that homology. -/
public theorem exact_modulePullback_schemeChart_iff :
    ((modulePullback B S hS
        (ObjectProperty.homMk a : schemeSpace U ⟶ X)).mapShortComplex.obj σ).Exact ↔ σ.Exact := by
  have hfaithful := faithful_modulePullback_schemeChart B S hS U a haEtale haSurj
  obtain ⟨hlim, hcolim⟩ :=
    (exactFunctor_iff _).mp (exactFunctor_modulePullback_schemeChart B S hS U a haEtale)
  exact σ.exact_map_iff_of_faithful
    (modulePullback B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X))

/-- **Exactness of a short complex of modules descends along a surjective étale scheme chart.**
This is the direction of `AlgebraicGeometry.Space.exact_modulePullback_schemeChart_iff` with
content: it is the shape in which a reduction to the case of schemes delivers exactness of a
short complex of modules on an algebraic space. -/
public theorem exact_of_exact_modulePullback_schemeChart
    (h : ((modulePullback B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X)).mapShortComplex.obj σ).Exact) :
    σ.Exact :=
  (exact_modulePullback_schemeChart_iff B S hS σ U a haEtale haSurj).mp h

/-- **Short exactness of a short complex of modules on the small étale site is étale local.**  For
an étale scheme chart `a` of an algebraic space which is surjective on points, a short complex of
modules is short exact exactly when its inverse image along `a` is: the inverse image is exact by
Stacks 03LV and faithful because `a` is surjective, so it preserves and reflects each of the three
clauses — the monomorphism at the left, the exactness in the middle, and the epimorphism at the
right. -/
public theorem shortExact_modulePullback_schemeChart_iff :
    ((modulePullback B S hS
        (ObjectProperty.homMk a : schemeSpace U ⟶ X)).mapShortComplex.obj σ).ShortExact ↔
      σ.ShortExact := by
  have hfaithful := faithful_modulePullback_schemeChart B S hS U a haEtale haSurj
  obtain ⟨hlim, hcolim⟩ :=
    (exactFunctor_iff _).mp (exactFunctor_modulePullback_schemeChart B S hS U a haEtale)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hmono := h.mono_f
    have hepi := h.epi_g
    exact
      { exact := (exact_modulePullback_schemeChart_iff B S hS σ U a haEtale haSurj).mp h.exact
        mono_f := (modulePullback B S hS
          (ObjectProperty.homMk a : schemeSpace U ⟶ X)).mono_of_mono_map hmono
        epi_g := (modulePullback B S hS
          (ObjectProperty.homMk a : schemeSpace U ⟶ X)).epi_of_epi_map hepi }
  · exact h.map_of_exact
      (modulePullback B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X))

/-- **Short exactness of a short complex of modules descends along a surjective étale scheme
chart**, the direction of `AlgebraicGeometry.Space.shortExact_modulePullback_schemeChart_iff` with
content. -/
public theorem shortExact_of_shortExact_modulePullback_schemeChart
    (h : ((modulePullback B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X)).mapShortComplex.obj σ).ShortExact) :
    σ.ShortExact :=
  (shortExact_modulePullback_schemeChart_iff B S hS σ U a haEtale haSurj).mp h

end Descent

end AlgebraicGeometry.Space

end
