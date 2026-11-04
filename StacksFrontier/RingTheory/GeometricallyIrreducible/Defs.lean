module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u



/-!
# Geometrically irreducible algebras

Let `k` be a field and let `S` be a `k`-algebra. Then `S` is *geometrically irreducible over `k`*
if for every field extension `k'/k` the spectrum of `S ⊗[k] k'` is an irreducible topological
space; by the convention that an irreducible space is nonempty — the source's footnote to this
definition — each such tensor product is in particular nonzero. Since `Spec (S ⊗[k] k')` is the
fibre product `Spec S ×_{Spec k} Spec k'` (`AlgebraicGeometry.pullbackSpecIso`), this says
precisely that every base change of `Spec S ⟶ Spec k` along a field-valued point of `Spec k` is
an irreducible space, which is Mathlib's morphism property
`AlgebraicGeometry.GeometricallyIrreducible`. That is the shape the definition takes here, and
`Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct` is the
equivalence with the source's condition on tensor products.

## Main definitions

* `Algebra.IsGeometricallyIrreducible`: a `k`-algebra `S` is geometrically irreducible over `k`
  if every base change of `Spec S ⟶ Spec k` along a field-valued point of `Spec k` is an
  irreducible space.

## Main results

* `Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct`: `S` is
  geometrically irreducible over `k` if and only if the spectrum of `S ⊗[k] k'` is irreducible
  for every field extension `k'/k`.
* `Algebra.isGeometricallyIrreducible_self` and `Algebra.isGeometricallyIrreducible_polynomial`:
  a field and the polynomial ring over it are geometrically irreducible over that field.

## Implementation notes

Geometric irreducibility is spelled through Mathlib's
`AlgebraicGeometry.GeometricallyIrreducible` applied to `Spec S ⟶ Spec k`, the way tags 0G31,
0G32 and 0G33 spell it and the way item 5 of tag 037K's list of equivalent conditions does,
rather than by quantifying over field extensions by hand: `AlgebraicGeometry.geometrically`
unfolds to the source's quantifier, because a morphism `Spec k' ⟶ Spec k` out of the spectrum of
a field is the same as a `k`-algebra structure on `k'`, and the base change along it is
`Spec (S ⊗[k] k')`. The notion is therefore only a name for an existing one, so it is an
`abbrev`: Mathlib's API for the morphism property — stability under base change, the behaviour
of fibres, and the decomposition
`GeometricallyIntegral = GeometricallyReduced ⊓ GeometricallyIrreducible` — applies to it
unchanged, and instance search sees through it. The price of the reformulation is that the
source's own sentence has to be recovered as a theorem, which is
`Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct`; the
tensor factors there are in the order `S ⊗[k] k'`, the order in which `pullbackSpecIso`
identifies the fibre product, and the order the source and tag 037K both write.

Because the definition passes through `Spec`, the field `k` and the algebra `S` must lie in a
common universe, and the test fields `k'` lie in it too, as they do in
`AlgebraicGeometry.geometrically`; the condition on tensor products alone would allow three
unrelated universes. This is no restriction on the mathematics: by tag 037K the whole condition
is decided by the single extension `k̄/k` given by an algebraic closure, which lives in the
universe of `k`, so the property tested against extensions in one universe agrees with the
property tested against extensions in any.

The definition tests all field extensions of `k`, as the source does, and not the single
extension `AlgebraicClosure k` that Mathlib's `Algebra.IsGeometricallyReduced` tests; that the
two shapes agree is the content of tag 037K, not of this definition. No finiteness, reducedness
or Noetherian hypothesis is added, and the only data are `k` and the structure map
`algebraMap k S`.

Faithfulness to the source. (1) No hypothesis is idle: `Field k`, `CommRing S` and `Algebra k S`
are exactly the data of the `k`-algebra `S`, and both occur in the condition through
`algebraMap k S`; there is nothing else to be dead. (2) The scalars and base are the source's:
the tensor product is over `k` itself and the base change is of `S` along an extension of `k`,
with no closure or localization silently substituted for the base. (3) The map the source names
is pinned: the structure map is `algebraMap k S`, and the extension `k'/k` acts through
`algebraMap k k'`, so the base change is along the morphism that extension determines and not
some other point of `Spec k`. (4) The instantiation is not degenerate in either direction: `k`
is geometrically irreducible over `k`, since `k ⊗[k] k' ≅ k'` has a one-point spectrum, and so
is `k[X]`, since `k[X] ⊗[k] k' ≅ k'[X]` is a domain; whereas `ℚ(i)` is not geometrically
irreducible over `ℚ`, since `ℚ(i) ⊗[ℚ] ℚ(i) ≅ ℚ(i) × ℚ(i)` has two minimal primes, and the zero
algebra is not, since its spectrum is empty and an irreducible space is nonempty.

## References

* [Stacks Project, Tag 037L](https://stacks.math.columbia.edu/tag/037L)
-/

@[expose] public section



open AlgebraicGeometry CategoryTheory CommRingCat TensorProduct

/-- A `k`-algebra `S` is **geometrically irreducible over `k`** if every base change of
`Spec S ⟶ Spec k` along a field-valued point of `Spec k` is an irreducible space, equivalently
if for every field extension `k'/k` the spectrum of `S ⊗[k] k'` is irreducible
(`Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct`). An
irreducible space is nonempty, so this forces every such `S ⊗[k] k'` to be nonzero. -/
@[stacks 037L, ega "IV 4.5.2" "special case", ega "IV 4.5.9"]
public abbrev Algebra.IsGeometricallyIrreducible (k S : Type u) [Field k] [CommRing S]
    [Algebra k S] : Prop :=
  GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S)))

/-- A `k`-algebra `S` is geometrically irreducible over `k` if and only if the spectrum of
`S ⊗[k] k'` is irreducible for every field extension `k'/k`. This is the form the definition
takes in the source. -/
public theorem Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct
    (k S : Type u) [Field k] [CommRing S] [Algebra k S] :
    Algebra.IsGeometricallyIrreducible k S ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k'],
        IrreducibleSpace (PrimeSpectrum (S ⊗[k] k')) := by
  rw [Algebra.IsGeometricallyIrreducible, geometricallyIrreducible_iff,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  refine forall_congr' fun K => ?_
  exact ⟨fun h _ _ => ObjectProperty.prop_of_iso (fun X : Scheme => IrreducibleSpace X)
      (pullbackSpecIso k S K) (h ..),
    fun h _ _ => ObjectProperty.prop_of_iso (fun X : Scheme => IrreducibleSpace X)
      (pullbackSpecIso k S K).symm (h ..)⟩

/-- A field is geometrically irreducible over itself: `k ⊗[k] k' ≅ k'` has a one-point
spectrum. -/
public theorem Algebra.isGeometricallyIrreducible_self (k : Type u) [Field k] :
    Algebra.IsGeometricallyIrreducible k k := by
  rw [Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  intro K _ _
  have : IsDomain (k ⊗[k] K) := (Algebra.TensorProduct.lid k K).toMulEquiv.isDomain K
  infer_instance

/-- The affine line over a field is geometrically irreducible: `k[X] ⊗[k] k' ≅ k'[X]` is a
domain. -/
public theorem Algebra.isGeometricallyIrreducible_polynomial (k : Type u) [Field k] :
    Algebra.IsGeometricallyIrreducible k (Polynomial k) := by
  rw [Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  intro K _ _
  have e : (Polynomial k ⊗[k] K) ≃ₐ[k] Polynomial K :=
    (Algebra.TensorProduct.comm k (Polynomial k) K).trans (polyEquivTensor k K).symm
  have : IsDomain (Polynomial k ⊗[k] K) := e.toMulEquiv.isDomain (Polynomial K)
  infer_instance

end
