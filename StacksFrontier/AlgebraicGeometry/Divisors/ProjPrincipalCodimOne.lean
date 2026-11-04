module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import StacksFrontier.AlgebraicGeometry.Divisors.ProjIdealOfClosedSubscheme
public import StacksFrontier.RingTheory.PrincipalCodimOne.Basic
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Principality of the ideal of a codimension-one closed subscheme of projective space

Let `R` be a Noetherian unique factorization domain and let `Z ⊆ P^n_R` be a closed subscheme
with no embedded points all of whose irreducible components have codimension one. The homogeneous
ideal `I(Z) ⊆ R[T₀, …, Tₙ]` of `Z` is then principal.

This file assembles the parts of that statement which are purely algebraic or purely point-set,
and reduces the geometric statement to a single condition on the associated primes of `I(Z)`.

`R[T₀, …, Tₙ]` is a Noetherian unique factorization domain whenever `R` is — this is the step the
source quotes as Algebra, Lemma 0BC1 — so
`Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one`
applies to `I(Z)` directly: an ideal of a Noetherian UFD all of whose associated primes have
height one is principal. This bypasses the route taken by the source, which deduces principality
from `Pic(P^n_R) = ℤ` (Tag 0BXJ) together with the effective Cartier divisor criterion of Tag
0BXH; neither is needed here.

What is not proved *here* is the remaining geometric input, namely that the two hypotheses on `Z`
force every associated prime of `I(Z)` to have height one. That implication is
`AlgebraicGeometry.ProjectiveSpectrum.Proj`
`.height_eq_one_of_mem_associatedPrimes_idealOfClosedSubscheme`, in
`StacksFrontier/AlgebraicGeometry/CodimOneSubscheme/ProjHeightOne.lean`, which completes Tag
0BXL and carries its attribute. It needs

* the degreewise kernel criterion for `I(Z)`
  (`AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme` is defined by generators,
  and identifying its elements with the functions vanishing on `Z` over each standard chart
  `D₊(Tᵢ)` is Tag 0801, which rests on the Serre-type results Tags 0BXD and 0BXF), and
* the comparison of the associated primes of `I(Z)` with the associated points of `Z`, under
  which "no embedded points" becomes "no embedded primes" and "every component has codimension
  one" becomes "every minimal prime has height one".

For the second of these, the point-set half of the dictionary is proved here:
`AlgebraicGeometry.codimension_closureSingleton_base` computes the codimension of the closure of
a point of any scheme, in any affine chart around it, as the height of the corresponding prime
ideal. That is what turns the codimension hypothesis on `Z` into a height hypothesis once the
standard charts `D₊(Tᵢ)` of `Proj` are in play.

## Main results

* `PrimeSpectrum.codimension_closureSingleton`: the codimension of `closure {p}` in `Spec R` is
  the height of `p`.
* `Topology.IsOpenEmbedding.codimension_closureSingleton`: on sober `T0` spaces the codimension
  of the closure of a point is unchanged by an open embedding.
* `AlgebraicGeometry.codimension_closureSingleton_base`: the codimension of the closure of a
  point of a scheme is the height of the prime it corresponds to in any affine chart containing
  it.
* `Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_no_embedded_primes`: an ideal of a
  Noetherian UFD whose associated primes are all minimal over it and all of height one is
  principal — the hypothesis in the shape the geometry produces it.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme_isPrincipal_of_height_eq_one`:
  for a graded Noetherian UFD, the ideal of a closed subscheme of `Proj` is principal as soon as
  its associated primes have height one.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.projectiveSpace_idealOfClosedSubscheme_isPrincipal`:
  the same for projective space over a Noetherian UFD, which is the setting of Tag 0BXL.

## References

* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
* [Stacks Project, Tag 0BC1](https://stacks.math.columbia.edu/tag/0BC1)
-/

@[expose] public section

open TopologicalSpace

universe u

/-- The codimension of the closure of a point of `Spec R` is the height of the corresponding
prime ideal: zero loci of primes are the irreducible closed subsets of `Spec R`, and the
correspondence reverses inclusions, so coheight on one side is height on the other. -/
theorem PrimeSpectrum.codimension_closureSingleton {R : Type*} [CommRing R] (p : PrimeSpectrum R) :
    codimension (IrreducibleCloseds.closureSingleton p) = p.asIdeal.height := by
  rw [PrimeSpectrum.height_eq_orderHeight, codimension_eq_coheight, ← Order.height_toDual]
  have key : OrderDual.toDual (IrreducibleCloseds.closureSingleton p)
      = PrimeSpectrum.pointsEquivIrreducibleCloseds R p := rfl
  rw [key, Order.height_orderIso]

attribute [local instance] specializationOrder in
/-- Codimension of the closure of a point is unchanged by an open embedding: on a sober `T0`
space the irreducible closed subsets are the closures of points, and an open embedding is an
isomorphism onto its image for the specialization order. -/
@[ega "0 14.2.3" "special case"]
theorem Topology.IsOpenEmbedding.codimension_closureSingleton {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSober X] [T0Space X] [QuasiSober Y] [T0Space Y] {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) (x : X) :
    codimension (IrreducibleCloseds.closureSingleton (f x))
      = codimension (IrreducibleCloseds.closureSingleton x) := by
  have hY : IrreducibleCloseds.closureSingleton (f x)
      = irreducibleSetEquivPoints.symm (f x) := rfl
  have hX : IrreducibleCloseds.closureSingleton x = irreducibleSetEquivPoints.symm x := rfl
  rw [codimension_eq_coheight, codimension_eq_coheight, hX, hY, Order.coheight_orderIso,
    Order.coheight_orderIso, hf.coheight_eq f]

/-- The codimension of the closure of a point of a scheme, read off in an affine chart: for an
open immersion `j : Spec R ⟶ X`, the closure of `j p` has codimension the height of `p`. -/
theorem AlgebraicGeometry.codimension_closureSingleton_base {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [AlgebraicGeometry.IsOpenImmersion j] (p : PrimeSpectrum R) :
    codimension (IrreducibleCloseds.closureSingleton (j.base p)) = p.asIdeal.height := by
  rw [j.isOpenEmbedding.codimension_closureSingleton p]
  exact PrimeSpectrum.codimension_closureSingleton p

namespace Stacks.RingTheory.PrincipalCodimOne

/-- An ideal of a Noetherian unique factorization domain is principal as soon as each of its
associated primes is minimal over it and every minimal prime over it has height one.

This is the hypothesis of
`Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one` in the
shape in which geometry supplies it: the first condition is "no embedded points" and the second
is "every irreducible component has codimension one". -/
theorem isPrincipal_of_no_embedded_primes {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid R] {I : Ideal R}
    (hemb : Submodule.associatedPrimes I ⊆ I.minimalPrimes)
    (hmin : ∀ p ∈ I.minimalPrimes, p.height = 1) : I.IsPrincipal :=
  isPrincipal_of_forall_associatedPrimes_height_eq_one fun _ hp => hmin _ (hemb hp)

end Stacks.RingTheory.PrincipalCodimOne

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open AlgebraicGeometry CategoryTheory

universe w

/-- If the graded ring `S` is a Noetherian unique factorization domain, the ideal of a closed
subscheme of `Proj S` is principal as soon as all of its associated primes have height one. -/
theorem idealOfClosedSubscheme_isPrincipal_of_height_eq_one {S : Type u} {σ : Type w} [CommRing S]
    [IsDomain S] [IsNoetherianRing S] [UniqueFactorizationMonoid S] [SetLike σ S]
    [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮] {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i]
    (h : ∀ p ∈ Submodule.associatedPrimes (idealOfClosedSubscheme 𝒮 i), p.height = 1) :
    (idealOfClosedSubscheme 𝒮 i).IsPrincipal :=
  Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one h

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Stacks 0BXL, final step.** Let `R` be a Noetherian unique factorization domain and let `Z`
be a closed subscheme of `P^n_R = Proj R[T₀, …, Tₙ]`. If every associated prime of the
homogeneous ideal of `Z` has height one, that ideal is principal.

The hypotheses of the source — `Z` has no embedded points and every irreducible component of `Z`
has codimension one in `P^n_R` — are exactly what produces the height-one condition, but that
implication is not proved here; see the module docstring. -/
theorem projectiveSpace_idealOfClosedSubscheme_isPrincipal (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid R] (n : ℕ) {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsClosedImmersion i]
    (h : ∀ p ∈ Submodule.associatedPrimes
        (idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i),
      p.height = 1) :
    (idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i).IsPrincipal :=
  idealOfClosedSubscheme_isPrincipal_of_height_eq_one _ i h

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
