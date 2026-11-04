module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.TransversalIntersection

/-!
# Transporting the Tor-formula multiplicity along a quotient map

The reduction to the diagonal replaces a pair of ideals `(I, J)` of a local ring `A` by a pair
`(I', J')` on a second local ring `B` which surjects onto `A`, and matches the two families of
Tor modules. Turning that match into an equality of the two Tor-formula multiplicities is pure
bookkeeping about lengths: a module over the quotient ring `A` has the same length over `A` as
over `B`, because the two submodule lattices coincide. This is the step the source takes with
"Thus equality of lengths (by Algebra, Lemma 10.52.5 to be precise)".

The length statement itself is Mathlib's `Module.length_eq_of_surjective`. What is proved here
is its consequence for the alternating sums that define the multiplicity: the alternating sum
of lengths over `B` of a family of `A`-modules is the alternating sum of their lengths over
`A`, and therefore the Tor-formula multiplicity computed on `B` can be read off as a sum of
`A`-lengths, and equals the Tor-formula multiplicity on `A` whenever the two families of Tor
modules correspond.

## Main results

* `Stacks.Intersection.Diagonal.tsum_alternating_length_eq_of_surjective` — the alternating sum
  of lengths of a family of `A`-modules is the same over `B` and over `A`, for a surjection
  `B → A`.
* `Stacks.Intersection.Diagonal.localIntersectionMultiplicity_eq_tsum_length` — the Tor-formula
  multiplicity of a pair on `B` is the alternating sum of the `A`-lengths of modules matching
  its Tor modules.
* `Stacks.Intersection.Diagonal.localIntersectionMultiplicity_eq_of_tor_linearEquiv` — the two
  Tor-formula multiplicities agree once the two families of Tor modules correspond
  `B`-linearly.

## Implementation notes

The modules of the family carry both a `B`-module and an `A`-module structure together with
`IsScalarTower B A`, rather than only an `A`-module structure: there is no global instance
turning a module over an algebra into a module over the base ring, and spelling the two
structures out is what lets `Module.length_eq_of_surjective` apply with no transport.

Both rings and all modules live in one universe, which is what
`Ideal.localIntersectionMultiplicity` requires: it is phrased over `ModuleCat.{u} A`.

## References

* [Stacks Project, Tag 0B0U](https://stacks.math.columbia.edu/tag/0B0U)
* [Stacks Project, Lemma 10.52.5 (Tag 02M0)](https://stacks.math.columbia.edu/tag/02M0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Intersection.Diagonal

/-- **Lengths of a family of modules over a quotient ring.** If `B → A` is a surjective ring map
and every member of a family of modules is a module over `A` whose `B`-structure is the
restriction, then the alternating sum of the `B`-lengths is the alternating sum of the
`A`-lengths. This is the alternating-sum form of Mathlib's `Module.length_eq_of_surjective`,
which is the equality half of Stacks Lemma 10.52.5. -/
theorem tsum_alternating_length_eq_of_surjective {B A : Type u} [CommRing B] [CommRing A]
    [Algebra B A] (hsurj : Function.Surjective (algebraMap B A))
    (T : ℕ → Type u) [∀ i, AddCommGroup (T i)] [∀ i, Module B (T i)] [∀ i, Module A (T i)]
    [∀ i, IsScalarTower B A (T i)] :
    ∑' i : ℕ, (-1 : ℚ) ^ i * ((Module.length B (T i)).toNat : ℚ) =
      ∑' i : ℕ, (-1 : ℚ) ^ i * ((Module.length A (T i)).toNat : ℚ) :=
  tsum_congr fun i => by rw [Module.length_eq_of_surjective (R := A) (M := T i) hsurj]

/-- **The Tor-formula multiplicity on `B`, read as a sum of lengths over a quotient ring `A`.**
If `B → A` is surjective and the Tor modules of the pair `(I, N)` over `B` are `B`-linearly
isomorphic to modules `T i` which are modules over `A`, then the Tor-formula multiplicity of
the pair is the alternating sum of the `A`-lengths of the `T i`.

In the reduction to the diagonal `B = 𝒪_{X × X, Δ(ξ)}`, `A = 𝒪_{X, ξ}` is its quotient by the
local ideal of the diagonal, `(I, N)` is the pair `(I_Δ, 𝒪_{V × W})` and the `T i` are the Tor
modules on `X` at `ξ`. -/
theorem localIntersectionMultiplicity_eq_tsum_length {B : Type u} [CommRing B] (I : Ideal B)
    (N : Type u) [AddCommGroup N] [Module B N] {A : Type u} [CommRing A] [Algebra B A]
    (hsurj : Function.Surjective (algebraMap B A))
    (T : ℕ → Type u) [∀ i, AddCommGroup (T i)] [∀ i, Module B (T i)] [∀ i, Module A (T i)]
    [∀ i, IsScalarTower B A (T i)]
    (e : ∀ i : ℕ, (((Tor (ModuleCat.{u} B) i).obj (ModuleCat.of B (B ⧸ I))).obj
      (ModuleCat.of B N)) ≃ₗ[B] T i) :
    I.localIntersectionMultiplicity N =
      ∑' i : ℕ, (-1 : ℚ) ^ i * ((Module.length A (T i)).toNat : ℚ) := by
  rw [← tsum_alternating_length_eq_of_surjective hsurj T]
  exact tsum_congr fun i => by rw [(e i).length_eq]

/-- **Equality of the two Tor-formula multiplicities across the reduction.** Let `B → A` be a
surjection of commutative rings, `(I, N)` a pair on `B` and `(I₀, M)` a pair on `A`, and suppose
that for every `i` the two Tor modules correspond `B`-linearly, the `A`-side Tor modules being
read as `B`-modules through the surjection. Then the two Tor-formula multiplicities are equal.

This is the form in which the reduction to the diagonal consumes the identification
`Tor_i^{𝒪_{X × X}}(𝒪_Δ, 𝒪_{V × W})_{Δ(ξ)} ≅ Tor_i^{𝒪_X}(𝒪_V, 𝒪_W)_ξ`: the equality of
multiplicities `e(X × X, Δ · V × W, Δ(Z)) = e(X, V · W, Z)`. -/
theorem localIntersectionMultiplicity_eq_of_tor_linearEquiv {B A : Type u} [CommRing B]
    [CommRing A] [Algebra B A] (hsurj : Function.Surjective (algebraMap B A))
    (I : Ideal B) (N : Type u) [AddCommGroup N] [Module B N]
    (I₀ : Ideal A) (M : Type u) [AddCommGroup M] [Module A M]
    [hB : ∀ i : ℕ, Module B ((((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I₀))).obj
      (ModuleCat.of A M)) : Type u)]
    [∀ i : ℕ, IsScalarTower B A ((((Tor (ModuleCat.{u} A) i).obj
      (ModuleCat.of A (A ⧸ I₀))).obj (ModuleCat.of A M)) : Type u)]
    (e : ∀ i : ℕ, (((Tor (ModuleCat.{u} B) i).obj (ModuleCat.of B (B ⧸ I))).obj
        (ModuleCat.of B N)) ≃ₗ[B]
      ((((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I₀))).obj
        (ModuleCat.of A M)) : Type u)) :
    I.localIntersectionMultiplicity N = I₀.localIntersectionMultiplicity M :=
  localIntersectionMultiplicity_eq_tsum_length I N hsurj _ e

end Stacks.Intersection.Diagonal

end
