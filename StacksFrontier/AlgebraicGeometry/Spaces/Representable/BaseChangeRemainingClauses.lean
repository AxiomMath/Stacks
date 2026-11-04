module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange

/-!
# The remaining entries of the base-change list

The remaining properties of morphisms of schemes that the list of Tag 02WF declares stable
under arbitrary base change: the three kinds of immersion, quasi-affineness, syntomicity,
finite local freeness, the three forms of projectivity, and relative dimension `d`. Each is a
single existing result, in Mathlib or elsewhere in this library, so each is adopted here rather
than restated.

The entries are, with the lemma of the list that each realizes:

* closed immersions, open immersions and locally closed immersions, which is Schemes, Lemma
  26.18.2: `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`,
  `AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange` and
  `AlgebraicGeometry.IsImmersion.isStableUnderBaseChange`, Mathlib's `IsImmersion` being the
  locally closed immersions;
* quasi-affine, which is Morphisms, Lemma 29.13.5 (Tag 01SO):
  `AlgebraicGeometry.isQuasiAffineHom_isStableUnderBaseChange`;
* syntomic, which is Morphisms, Lemma 29.31.4 (Tag 01UI):
  `AlgebraicGeometry.syntomic_isStableUnderBaseChange`;
* finite locally free, which is Morphisms, Lemma 29.49.4 (Tag 02KD):
  `Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange`;
* H-projective, which is Morphisms, Lemma 29.44.8 (Tag 01WF):
  `AlgebraicGeometry.IsProjectiveMorphism.baseChange`;
* projective and locally projective, which is Morphisms, Lemma 29.44.9 (Tag 02V6):
  `AlgebraicGeometry.isStableUnderBaseChange_isProjective` and
  `AlgebraicGeometry.IsLocallyProjective.pullback_fst`;
* locally of finite type of relative dimension `d`, which is Morphisms, Lemma 29.30.2
  (Tag 02NK): `AlgebraicGeometry.RelativeDimension.of_isPullback`.

## Implementation notes

The three projectivity predicates are the three clauses of Definition 01W8, kept apart in this
library because they are not known to agree here: `AlgebraicGeometry.IsProjective` is clause
(1), a closed immersion over the base into the projective bundle of a quasi-coherent module of
finite type; `AlgebraicGeometry.IsProjectiveMorphism` is clause (2), a closed immersion over the
base into some `ℙⁿ`; and `AlgebraicGeometry.IsLocallyProjective` is clause (3). Each of the three
has its own entry, so that the list records base-change stability for the notion the reader is
using and not only for one of the three.

Most of the entries are instances of `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`
and so speak about an arbitrary cartesian square. Three are stated for Mathlib's chosen fibre
product instead — the two projectivity entries whose predicate is not carried by a morphism
property, and, for relative dimension, a cartesian-square statement whose conclusion needs the
base-changed morphism to be locally of finite type before the predicate is even well formed.

## References

* [Stacks Project, Tag 02WF](https://stacks.math.columbia.edu/tag/02WF)
-/

@[expose] public section

add_to_stacks 02WF "closed immersion"
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange

add_to_stacks 02WF "open immersion"
  AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange

add_to_stacks 02WF "locally closed immersion"
  AlgebraicGeometry.IsImmersion.isStableUnderBaseChange

add_to_stacks 02WF "quasi_affine" AlgebraicGeometry.isQuasiAffineHom_isStableUnderBaseChange

add_to_stacks 02WF "syntomic" AlgebraicGeometry.syntomic_isStableUnderBaseChange

add_to_stacks 02WF "finite_locally_free"
  Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange

add_to_stacks 02WF "h_projective" AlgebraicGeometry.IsProjectiveMorphism.baseChange

add_to_stacks 02WF "projective" AlgebraicGeometry.isStableUnderBaseChange_isProjective

add_to_stacks 02WF "locally_projective" AlgebraicGeometry.IsLocallyProjective.pullback_fst

add_to_stacks 02WF "relative_dimension_d" AlgebraicGeometry.RelativeDimension.of_isPullback

end
