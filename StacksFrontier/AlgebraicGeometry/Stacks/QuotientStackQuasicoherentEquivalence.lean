module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackQuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescentEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModulesSmall

/-!
# Quasi-coherent modules on a quotient stack

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over `S` and let `𝒳 = [U/R]` be its
quotient stack (Stacks 044Q). The category `QCoh(𝒪_𝒳)` of quasi-coherent modules on `𝒳`
(Stacks 06WG) is equivalent to the category `QCoh(U, R, s, t, c)` of quasi-coherent modules on the
groupoid (Stacks 0441). The functor sends `ℱ` to `(x^*ℱ|_{U_étale}, α)`, where
`x : 𝒮_U ⟶ [U/R]` is the canonical projection (Stacks 044R) and `α = c_t ≫ c_s⁻¹` is the
transport of the canonical 2-morphism of Stacks 044S through the comparison maps `c_s`, `c_t` of
equation 076R along the source and the target.

## Main definitions

* `AlgebraicGeometry.Stack.quasicoherentEquivalenceGroupoid`: the equivalence
  `QCoh(𝒪_{[U/R]}) ≌ QCoh(U, R, s, t, c)`.

## Main results

* `AlgebraicGeometry.Stack.quasicoherentEquivalenceGroupoid_functor`: the functor of the
  equivalence is the descent functor `ℱ ↦ (x^*ℱ|_{U_étale}, c_t ≫ c_s⁻¹)`.
* `AlgebraicGeometry.Stack.isEquivalence_quotientPrestackQuasicoherentPullback`: the restriction
  of quasi-coherent modules along the stackification map `[U/_pR] ⟶ [U/R]` is an equivalence.

## Implementation notes

The modules have their sections in `Type u`, the universe of the schemes of the big fppf site, as
the modules of `QCoh(U, R, s, t, c)` do. The functor
`AlgebraicGeometry.Stack.quotientPrestackQuasicoherentPullback` is between modules with sections
in `Type (u + 1)`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 06WR](https://stacks.math.columbia.edu/tag/06WR)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {A : AlgebraicSpaces C S hS}

/-- Every object of the quotient stack `[U/R]` is covered, for its fppf topology, by a family of
images of objects of the universe-lifted pointwise groupoid fibration `[U/_pR]` indexed by a type
in `Type u`. -/
theorem exists_ofArrows_toQuotientStack (G : GroupoidInAlgebraicSpaces C S hS A)
    (y : (quotientStack G).obj) :
    ∃ (I : Type u) (x : I → (quotientPrestack G).obj) (g : ∀ i, (toQuotientStack G).obj (x i) ⟶ y),
      Sieve.ofArrows _ g ∈ associatedTopology C S hS (quotientStack G).p C.topology y := by
  obtain ⟨I, x, g, hg⟩ := exists_ofArrows_pointwiseToQuotientStack G y
  exact ⟨I, fun i => (quotientPrestackEquivalence G).functor.obj (x i), g, hg⟩

/-- The restriction of quasi-coherent modules along the stackification map `[U/_pR] ⟶ [U/R]` is an
equivalence of categories. -/
theorem isEquivalence_quotientPrestackQuasicoherentPullback
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    (quotientPrestackQuasicoherentPullback G).IsEquivalence := by
  have := (fullyFaithfulToQuotientStack G).full
  have := (fullyFaithfulToQuotientStack G).faithful
  exact isEquivalence_quasicoherentPullback'_of_full_of_faithful.{u, u + 1, u + 1, u + 1, u + 1,
    u + 1} C S hS _ _ _ _ _ _ (exists_ofArrows_toQuotientStack G)

/-- For a groupoid `(U, R, s, t, c)` in algebraic spaces, the category of quasi-coherent modules
on the quotient stack `[U/R]` is equivalent to the category of quasi-coherent modules on
`(U, R, s, t, c)`, by the functor `ℱ ↦ (x^*ℱ|_{U_étale}, α)` with `α` the transport of the
canonical 2-morphism of Stacks 044S through the comparison maps of equation 076R. -/
@[stacks 06WT "the equivalence QCoh(𝒪_{[U/R]}) ≌ QCoh(U, R, s, t, c), with functor \
ℱ ↦ (x^*ℱ|_{U_étale}, α)"]
def quasicoherentEquivalenceGroupoid (G : GroupoidInAlgebraicSpaces C S hS A) :
    FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} C S hS (quotientStack G).p
        (isFiberedInGroupoids_quotientStack G) ≌ Space.QuasicoherentModule C S hS G :=
  haveI := (fullyFaithfulPointwiseToQuotientStack G).full
  haveI := (fullyFaithfulPointwiseToQuotientStack G).faithful
  haveI := isEquivalence_pointwiseQuasicoherentDescentFunctor (pointwiseToQuotientStack G)
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq (isFiberedInGroupoids_quotientStack G)
    (exists_ofArrows_pointwiseToQuotientStack G)
  (pointwiseQuasicoherentDescentFunctor (pointwiseToQuotientStack G)
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq
    (isFiberedInGroupoids_quotientStack G)).asEquivalence

/-- The functor of `AlgebraicGeometry.Stack.quasicoherentEquivalenceGroupoid` is the descent
functor `ℱ ↦ (x^*ℱ|_{U_étale}, c_t ≫ c_s⁻¹)` of the canonical map `[U/_pR] ⟶ [U/R]`. -/
theorem quasicoherentEquivalenceGroupoid_functor (G : GroupoidInAlgebraicSpaces C S hS A) :
    (quasicoherentEquivalenceGroupoid G).functor =
      pointwiseQuasicoherentDescentFunctor (pointwiseToQuotientStack G)
        (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq
        (isFiberedInGroupoids_quotientStack G) := rfl

end AlgebraicGeometry.Stack

end
