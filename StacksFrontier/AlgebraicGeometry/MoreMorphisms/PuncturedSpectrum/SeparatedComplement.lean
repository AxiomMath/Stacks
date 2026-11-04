module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Divisors.PuncturedSpectrumAffineCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local dimension along the complement of an affine open

Let `U` be an affine open subset of a separated locally Noetherian scheme `X`. At the generic
point of every irreducible component of the complement of `U`, the local ring of `X` has Krull
dimension at most one, and its dimension is exactly one if `U` is dense, or more generally if
the generic point lies in the closure of `U`.

## Main results

* `Stacks.PuncturedSpectrum.isAffineHom_ι_of_isAffineOpen`: on a separated scheme, the inclusion
  of an affine open is an affine morphism.
* `Stacks.PuncturedSpectrum.krullDimLE_one_stalk_at_genericPoint_compl_affineOpen` gives the
  dimension bound.
* `Stacks.PuncturedSpectrum.ringKrullDim_stalk_at_genericPoint_compl_affineOpen_eq_one` gives
  equality when the generic point lies in the closure of the open (in particular, when the open
  is dense).

## Implementation notes

The complement is represented by the subtype of points outside `U`, so its irreducible components
and their generic points use the induced topology. The local ring is the stalk of `X` at the
image of that generic point. Dimension at most one is expressed by `Ring.KrullDimLE 1`, while
exact dimension is expressed using `ringKrullDim`.

Separatedness enters only through `Stacks.PuncturedSpectrum.isAffineHom_ι_of_isAffineOpen`: being
an affine morphism is local on the target, and on a separated scheme the intersection of two
affine opens is affine, so `U.ι` restricted over any affine open `V` of `X` is the affine
`U ⊓ V`. With that instance in hand, both statements are the corresponding results for an affine
open immersion, namely
`Stacks.Divisors.krullDimLE_one_stalk_at_genericPoint_compl_affineOpenImmersion` and
`Stacks.Divisors.ringKrullDim_stalk_at_genericPoint_compl_affineOpenImmersion_eq_one`.

## References

* [Stacks Project, Tag 0BCV](https://stacks.math.columbia.edu/tag/0BCV)
-/

@[expose] public section

open TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.PuncturedSpectrum

/-- On a separated scheme, the inclusion of an affine open subscheme is an affine morphism. -/
@[sga "6 II 2.2.6"]
theorem isAffineHom_ι_of_isAffineOpen
    (X : Scheme.{u}) [Scheme.IsSeparated X] (U : X.Opens) (hU : IsAffineOpen U) :
    IsAffineHom U.ι := by
  refine isAffineHom_of_forall_exists_isAffineOpen U.ι fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (by simp)
  refine ⟨V, hxV, hV, ?_⟩
  exact (U.ι.isAffineOpen_iff_of_isOpenImmersion).mp
    (by simpa [U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] using hU.inf hV)

/-- **Stacks Project, Tag 0BCV.** The local ring at the generic point of an irreducible
component of the complement of an affine open in a separated locally Noetherian scheme has
Krull dimension at most one. -/
@[stacks 0BCV "dimension bound",
  ega "IV 21.12.7" "dim ≤ 1, U affine open",
  sga "2 V 3.4",
  sga "6 II 2.2.6" "X sep, U affine; dim≤1"]
theorem krullDimLE_one_stalk_at_genericPoint_compl_affineOpen
    (X : Scheme.{u}) [Scheme.IsSeparated X] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U)
    {Z : Set ↑((U : Set X)ᶜ)} (hZ : Z ∈ irreducibleComponents ↑((U : Set X)ᶜ))
    {ξ : ↑((U : Set X)ᶜ)} (hξ : IsGenericPoint ξ Z) :
    Ring.KrullDimLE 1 (X.presheaf.stalk (ξ : X)) :=
  have : IsAffineHom U.ι := isAffineHom_ι_of_isAffineOpen X U hU
  Stacks.Divisors.krullDimLE_one_stalk_at_genericPoint_compl_affineOpenImmersion X U hZ hξ

/-- **Stacks Project, Tag 0BCV.** Under the hypotheses of the dimension bound, the local ring
has dimension one when the affine open is dense or the generic point is in its closure. -/
@[stacks 0BCV "equality in the closure",
  ega "IV 21.12.7" "dim = 1, U affine open",
  sga "6 II 2.2.6" "X sep, U affine; dim=1"]
theorem ringKrullDim_stalk_at_genericPoint_compl_affineOpen_eq_one
    (X : Scheme.{u}) [Scheme.IsSeparated X] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U)
    {Z : Set ↑((U : Set X)ᶜ)} (hZ : Z ∈ irreducibleComponents ↑((U : Set X)ᶜ))
    {ξ : ↑((U : Set X)ᶜ)} (hξ : IsGenericPoint ξ Z)
    (hξU : Dense (U : Set X) ∨ (ξ : X) ∈ closure (U : Set X)) :
    ringKrullDim (X.presheaf.stalk (ξ : X)) = 1 :=
  have : IsAffineHom U.ι := isAffineHom_ι_of_isAffineOpen X U hU
  Stacks.Divisors.ringKrullDim_stalk_at_genericPoint_compl_affineOpenImmersion_eq_one
    X U hZ hξ hξU

end Stacks.PuncturedSpectrum

end
