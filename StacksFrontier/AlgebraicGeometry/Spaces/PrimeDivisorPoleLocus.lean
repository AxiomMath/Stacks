module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMaps

/-!
# The prime divisors at whose generic point a rational function is not defined

Let `X` be a locally Noetherian integral algebraic space over a scheme `S` and let `f` be a
rational function on `X`. **Stacks 0ENN** asserts that two collections of prime divisors of `X`
are locally finite in `|X|`:

* the prime divisors `Z` whose generic point `ξ` is such that `f` does not lie in `𝒪_{X, ξ}`;
* the prime divisors `Z` with `ord_Z(f) ≠ 0`.

This file proves the first, which is
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_isDefinedAt` below. Both collections
together, under the source's hypotheses only, are
`Space.locallyFinite_primeDivisor_not_isDefinedAt_and_ordRationalFunction_ne_zero` (in the
namespace `AlgebraicGeometry`) of
`StacksFrontier.AlgebraicGeometry.Spaces.InvertibleRationalFunctionUnitLocus`, where Stacks 0ENN is
registered.

## Main results

* `AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_isDefinedAt`: the first collection of
  Stacks 0ENN — the prime divisors at whose generic point a rational function is not defined
  are locally finite in `|X|`.

## Implementation notes

### `f ∉ 𝒪_{X, ξ}` is `f` not being defined at `ξ`

The source writes the first collection as the prime divisors `Z` with generic point `ξ` such
that `f ∉ 𝒪_{X, ξ}`, the local ring being read inside the function field `R(X)`. An element of
`R(X)` lies in `𝒪_{X, ξ}` exactly when it is the germ at `ξ` of a section of the structure
sheaf on a neighbourhood of `ξ`, that is exactly when the rational function is *defined at* `ξ`
in the sense of Stacks 0EMQ, which is `AlgebraicGeometry.Space.RationalMap.IsDefinedAt`. That
is the form the condition takes here, and it is the form the condition takes in the source's
own proof, which produces a neighbourhood on which `f` is a section.

The same equivalence is visible in the scheme-level twin of this lemma, Stacks 02RL:
`AlgebraicGeometry.locallyFinite_closure_notMem_range_algebraMap` of
`StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle` states the condition as
`f ∉ Set.range (algebraMap (X.presheaf.stalk z) X.functionField)` and discharges it from
`X.presheaf.exists_germ_eq`, a representing section on an open set. For an algebraic space the
stalk-shaped phrasing is not available: the library has the local ring of an étale scheme chart
and the henselian local ring `𝒪^h_{X, ξ}` of Stacks 0EMY, but no ring `𝒪_{X, ξ}` of the space
itself and no canonical map from one into `R(X)`. On a scheme the two phrasings agree, and the
germ phrasing is what the source's proof uses, so it is what is used here.

Since a rational function is an equivalence class of morphisms to the relative affine line
defined on dense open subspaces, and on an irreducible space every nonempty open subspace is
dense, no generality is lost: a section of `𝒪_X` on any nonempty open neighbourhood of `ξ`
representing `f` witnesses `AlgebraicGeometry.Space.RationalMap.IsDefinedAt`.

### Hypotheses

The source assumes `X` locally Noetherian and integral and `f ∈ R(X)^*`. Local Noetherianness
is `hN`, as everywhere in this part of the library. Of integrality only irreducibility of
`|X|` is used, as the hypothesis `hirr`; and of `f` only that it is a rational function, no
invertibility — the first collection is locally finite for every `f ∈ R(X)`, because a rational
function is defined on a dense open subspace whether or not it is invertible there. Both are
weakenings of the source's hypotheses, so the statement below implies the source's.

## References

* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
* [Stacks Project, Tag 0EMQ](https://stacks.math.columbia.edu/tag/0EMQ)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

include hX in
/-- **Stacks 0ENN, the first collection.** On a locally Noetherian algebraic space over `S`
with irreducible point space, the prime divisors at whose generic point a rational function `f`
is not defined — those `Z` whose generic point `ξ` has `f ∉ 𝒪_{X, ξ}` — are locally finite in
`|X|`.

This is the source's argument. The rational function has a representative on a dense open
subspace `U`, which is nonempty because `|X|` is, so every prime divisor of the collection has
its generic point outside `U`: a representative whose domain contained that generic point
would, by definition, make `f` defined there. Such a prime divisor is an irreducible component
of the closed complement of `U`, and the irreducible components of a closed subset are locally
finite by Stacks 0EE5; both steps are
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`, which is Stacks
0EPS. -/
theorem locallyFinite_primeDivisor_not_isDefinedAt
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hirr : IrreducibleSpace (points B S hS X))
    (f : rationalFunctions B S hS hX) :
    LocallyFinite fun Z : {Z : PrimeDivisor B S hS X //
        ¬ RationalMap.IsDefinedAt B S hS f (Z.genericPoint B S hS X)} ↦
      Z.1.support B S hS X := by
  classical
  have := hirr
  obtain ⟨p, hp⟩ := RationalMap.exists_rep B S hS f
  have hUopen : IsOpen (Set.range (pointsMap B S hS p.domain.toFunctor p.domain.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS p.domain.ι p.dense_open_domain.1.2
  have hUne : (Set.range (pointsMap B S hS p.domain.toFunctor p.domain.ι)).Nonempty :=
    p.dense_open_domain.2.nonempty
  have hgen : ∀ Z : PrimeDivisor B S hS X,
      ¬ RationalMap.IsDefinedAt B S hS f (Z.genericPoint B S hS X) →
      Z.genericPoint B S hS X ∈
        (Set.range (pointsMap B S hS p.domain.toFunctor p.domain.ι))ᶜ :=
    fun _ hZ hmem ↦ hZ ⟨p, hp, hmem⟩
  have h := locallyFinite_primeDivisor_of_genericPoint_notMem B S hS hX hN hirr
    (fun Z : PrimeDivisor B S hS X ↦
      ¬ RationalMap.IsDefinedAt B S hS f (Z.genericPoint B S hS X))
    (Set.range (pointsMap B S hS p.domain.toFunctor p.domain.ι)) hUopen hUne hgen
  refine (h.comp_injective Subtype.val_injective).subset fun Z ↦ ?_
  simp only [Function.comp_apply]
  rw [if_pos Z.2]

end AlgebraicGeometry.Space

end
