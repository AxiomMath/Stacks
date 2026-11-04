module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsSequenceStructure
import StacksCore.Tactic.StacksAttribute

/-!
# The sequence of principal parts on a topological space

Let `φ : O₁ ⟶ O₂` be a homomorphism of sheaves of commutative rings on a topological space `X`.
For a sheaf of `O₂`-modules `F` the sheaf of first principal parts `P¹_{O₂/O₁}(F)` sits in a
short exact sequence

`0 ⟶ Ω_{O₂/O₁} ⊗_{O₂} F ⟶ P¹_{O₂/O₁}(F) ⟶ F ⟶ 0`

natural in `F`, the *sequence of principal parts*, with the two arrows pinned by their effect on
the universal differential operator: the inclusion sends `x ⊗ d b` to `D (b x) - b D x` and the
projection sends `D x` to `x`.

All of this content is the open-cover-site case of the sequence on a general site. The point of
this module is that the site-level statement is not applicable to a topological space as it
stands: it carries sheafification hypotheses that instance search does not supply for the
open-cover topology. They are discharged here once, from essential smallness of that site, so
that the statement about a topological space needs no hypotheses at all.

## Main results

* `AlgebraicGeometry.SheafOfModules.nonempty_principalPartsSequence_opens`: the functorial short
  exact sequence of first principal parts exists on a topological space.

## Implementation notes

The two discharged hypotheses are recorded as `local instance`s rather than instances, so that
nothing changes for other sites; they are only what the statement below needs in order to be
written down.

## References

* [Stacks Project, Tag 0G3V](https://stacks.math.columbia.edu/tag/0G3V)
* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the same sequence on an
  arbitrary site.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u m

namespace AlgebraicGeometry.SheafOfModules

/-- Sheafification of presheaves of abelian groups exists on the open-cover site of a topological
space, because that site is essentially small. -/
local instance opensHasSheafifyAddCommGrpCat {X : TopCat.{u}} :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u m} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max u m} _ _

/-- On the open-cover site of a topological space the weak equivalences of presheaves of abelian
groups are exactly the locally bijective morphisms, again because that site is essentially
small. -/
local instance opensWEqualsLocallyBijectiveAddCommGrpCat {X : TopCat.{u}} :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u m} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u m} _

/-- **Stacks Project, Tag 0G3V.** For a homomorphism `φ : O₁ ⟶ O₂` of sheaves of commutative
rings on a topological space, the sheaves of first principal parts of the sheaves of
`O₂`-modules assemble into a functor sitting in a short exact sequence

`0 ⟶ Ω_{O₂/O₁} ⊗_{O₂} F ⟶ P¹_{O₂/O₁}(F) ⟶ F ⟶ 0`

natural in `F`, with its two arrows determined by their values on universal differential
operators. -/
@[stacks 0G3V, sga "6 II AppII.1.2.4" "n = 1, top. space"]
theorem nonempty_principalPartsSequence_opens {X : TopCat.{u}}
    (O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X) (φ : O₁ ⟶ O₂) :
    Nonempty (PrincipalPartsSequence.{u, u, u, m} (J := Opens.grothendieckTopology X) O₁ O₂ φ) :=
  principalPartsSequence_nonempty.{u, u, u, m} O₁ O₂ φ

end AlgebraicGeometry.SheafOfModules

end
