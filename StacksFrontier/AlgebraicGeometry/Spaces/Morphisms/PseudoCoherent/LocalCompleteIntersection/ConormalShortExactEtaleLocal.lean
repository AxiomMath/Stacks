module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.ConormalSequenceCompositionExact

/-!
# Exactness of a short complex of modules on an algebraic space is étale local

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`a : U ⟶ X` be an étale scheme chart of `X` which is surjective on points.  Inverse image of
modules along `a` is exact by Stacks 03LV and faithful because `a` is surjective, so it both
preserves and reflects exactness of a short complex of `𝒪_X`-modules: a short complex is exact
exactly when its inverse image along the chart is.

This is the companion of `AlgebraicGeometry.Space.mono_modulePullback_schemeChart_iff` of
`ConormalShortExact.lean` beside this file, which says the same of a monomorphism, and it is the
étale localization step for the *middle* exactness clause of the conormal sequence of a
composition the way that one is for the injectivity clause.

## Main results

* `AlgebraicGeometry.Space.exact_map_modulePullback_schemeChart_iff`: exactness of a short
  complex of modules on the small étale site of an algebraic space is étale local — it holds
  exactly when it holds after inverse image along an étale scheme chart surjective on points.
* `AlgebraicGeometry.Space.exact_universalThickeningCompConormalSequence_of_chart`: that step for
  the conormal sequence of a composition of universal first-order thickenings — exactness of the
  sequence after inverse image along one étale chart surjective on points gives exactness on the
  algebraic space.

## What this does and does not give

**The middle exactness this reduces to a chart is proved.**  Exactness at `𝒞_{Z/X}` —
one of the two clauses of Stacks 06BD that Stacks 06CC refers to — is the hypothesis `hmid` of
`AlgebraicGeometry.Space.shortExact_iff_mono_universalThickeningCompConormalLeftMap` of
`ConormalShortExact.lean`, and the second result below reduces it to
the same statement read on one étale
scheme chart of `AlgebraicGeometry.Space.universalThickeningCompConormalBase`, the route onwards
being the scheme-level middle exactness
`Stacks.Thickenings.transitivityConormalShortComplex_exact` of
`StacksFrontier/AlgebraicGeometry/Thickenings/TransitivityConormal.lean`.  That hypothesis is also
discharged outright, and entirely inside the development of algebraic spaces, by
`AlgebraicGeometry.Space.exact_universalThickeningCompConormalSequence` of
`ConormalSequenceCompositionExact.lean`, an instantiation of
`AlgebraicGeometry.Space.exact_conormalShortComplex_preimage` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequencePreimageExact.lean`, which states the
clause for a closed subspace inside the inverse image of a closed subspace downstairs — the
presentation the fibre product `Y ×_{Y'} Z'` produces.  So neither of the two things that stood
between the chart-level statement and the scheme-level theorem is needed for it: not the
identification of `AlgebraicGeometry.Space.conormalModule` of a formally unramified morphism of
representable algebraic spaces with `Stacks.Thickenings.universalConormalSheaf` of the
corresponding morphism of schemes, and not the compatible étale localization of the *two*
thickenings `Z ⊂ Z'` and `Y ⊂ Y'` over a single chart.

What this file still gives is the étale localization of exactness of a short complex of modules,
the first result below, which is a statement about an arbitrary short complex on an arbitrary
algebraic space and is the companion of
`AlgebraicGeometry.Space.mono_modulePullback_schemeChart_iff`; the second result is its
instantiation at the conormal sequence of a composition, and is now one route to a clause that
has another.

## Implementation notes

The reflection half is `CategoryTheory.ShortComplex.exact_map_iff_of_faithful`, which asks for a
faithful functor preserving the left and the right homology of the complex.  Preservation comes
from `CategoryTheory.Functor.preservesHomologyOfExact` out of the two halves of Stacks 03LV,
`AlgebraicGeometry.Space.modulePullback_exact`, which are named in the proof because exactness
of the inverse image is a theorem in this development and not an instance; faithfulness is
`AlgebraicGeometry.Space.faithful_modulePullback`, which is where surjectivity of the chart is
used.  The homology of the source complex is not asked for: instance search delivers the
abelian structure of the `𝒪_X`-modules at the universe of the schemes in this import closure, so
no term for it is supplied, unlike in the files whose notes record that the search there
diverges.

`CategoryTheory.ShortComplex.map` asks for a functor preserving zero morphisms already in order
to be *written*, so the instance has to be in scope in the statement and not only in the proof.
It is `AlgebraicGeometry.Space.modulePullback_additive` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentAbelian.lean`, which is why that
module is imported; rederiving additivity here would duplicate it.

The general statement is made at a variable short complex over a variable algebraic space and
the conormal sequence is obtained from it by instantiation, which is the shape
`AlgebraicGeometry.Space.mono_modulePullback_schemeChart_iff` and
`AlgebraicGeometry.Space.mono_pullback_universalThickeningCompConormalLowerMap_of_chart` are in
for the same reason: the implementation notes of `ConormalSequenceCompositionExact.lean` record
that a comparison of
two spellings of one inverse image of modules exhausts the elaborator's and then the kernel's
budget, and an abstract functor leaves the kernel nothing to unfold.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV), exactness of the
  inverse image of modules along an étale morphism.
* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD), the sequence.
* [Stacks Project, Tag 06AE](https://stacks.math.columbia.edu/tag/06AE), part (2), the case of
  schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

-- The base's polymorphic abelian structure on sheaves of modules would make the universe of the
-- module category undetermined in `ShortComplex.exact_map_iff_of_faithful`; as in the base's own
-- files, it is switched off here.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Exactness of a short complex of modules is étale local -/

/-- **Exactness of a short complex of modules on the small étale site is étale local.**  For an
étale scheme chart `a` of an algebraic space which is surjective on points, a short complex of
modules is exact exactly when its inverse image along `a` is: the inverse image is exact by
Stacks 03LV, hence preserves the homology of the complex, and it is faithful because `a` is
surjective, hence reflects the vanishing of that homology. -/
public theorem exact_map_modulePullback_schemeChart_iff {X : AlgebraicSpaces B S hS}
    (T : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X.1)
    (haEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    (T.map (modulePullback B S hS
        (ObjectProperty.homMk a : schemeSpace U ⟶ X))).Exact ↔ T.Exact := by
  have hEt : IsEtale B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X).hom :=
    isEtale_of_presheaf_etale B S hS haEtale
  have hfaithful : (modulePullback B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X)).Faithful :=
    faithful_modulePullback B S hS U (ObjectProperty.homMk a) hEt haSurj
  have hexact := (exactFunctor_iff _).mp (modulePullback_exact B S hS
    (ObjectProperty.homMk a : schemeSpace U ⟶ X) hEt)
  have hlim : PreservesFiniteLimits (modulePullback B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X)) := hexact.1
  have hcolim : PreservesFiniteColimits (modulePullback B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X)) := hexact.2
  exact T.exact_map_iff_of_faithful _

/-! ### The middle exactness clause of the conormal sequence descends from a chart -/

variable {X Y' Z' : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
    {pY : Y' ⟶ X} {pZ : Z' ⟶ X} (i : Z.toFunctor ⟶ Y.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z pZ)
    (hY : IsUniversalFirstOrderThickening B S hS Y pY)
    (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)

/-- **The middle exactness clause descends from an étale chart.**  Exactness of the conormal
sequence of a composition of universal first-order thickenings after inverse image along one
étale scheme chart surjective on points gives exactness on the algebraic space, by
`exact_map_modulePullback_schemeChart_iff`.

The clause this reduces to a chart is itself proved, as
`AlgebraicGeometry.Space.exact_universalThickeningCompConormalSequence` of
`ConormalSequenceCompositionExact.lean`, so this is one route to it and not the only one; the
section *What this does and does not give* of this file says how the other goes, and no
`@[stacks]` attribute is claimed here. -/
public theorem exact_universalThickeningCompConormalSequence_of_chart
    (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ (universalThickeningCompConormalBase B S hS i hZ hY hfac).1)
    (haEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hex : (((ShortComplex.mk _ _
            (universalThickeningCompConormalSequence_comp_eq_zero B S hS i hZ hY hfac) :
          ShortComplex (Modules.{u, u} B S hS
            (universalThickeningCompConormalBase B S hS i hZ hY hfac).1
            (universalThickeningCompConormalBase B S hS i hZ hY hfac).2))).map
        (modulePullback B S hS (ObjectProperty.homMk a :
          schemeSpace U ⟶ universalThickeningCompConormalBase B S hS i hZ hY hfac))).Exact) :
    (ShortComplex.mk _ _
      (universalThickeningCompConormalSequence_comp_eq_zero B S hS i hZ hY hfac)).Exact :=
  (exact_map_modulePullback_schemeChart_iff B S hS
    (X := universalThickeningCompConormalBase B S hS i hZ hY hfac)
    (ShortComplex.mk _ _
      (universalThickeningCompConormalSequence_comp_eq_zero B S hS i hZ hY hfac))
    U a haEtale haSurj).mp hex


end AlgebraicGeometry.Space

end
