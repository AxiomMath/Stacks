module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Spectrum.Prime.Topology
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
public import StacksFrontier.RingTheory.GeometricallyReduced.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometrically integral algebras
-/

@[expose] public section

universe u



/-!
# Geometrically integral algebras

Let `k` be a field and let `S` be a `k`-algebra. Then `S` is *geometrically integral over `k`*
if for every field extension `k'/k` the ring `S ⊗[k] k'` is a domain. Since `Spec (S ⊗[k] k')`
is the fibre product `Spec S ×_{Spec k} Spec k'` (`AlgebraicGeometry.pullbackSpecIso`) and an
affine scheme `Spec R` is integral exactly when `R` is a domain
(`AlgebraicGeometry.affine_isIntegral_iff`), this says precisely that every base change of
`Spec S ⟶ Spec k` along a field-valued point of `Spec k` is an integral scheme, which is
Mathlib's morphism property `AlgebraicGeometry.GeometricallyIntegral`. That is the shape the
definition takes here, and `Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct` is the
equivalence with the condition on tensor products.

## Main definitions

* `Algebra.IsGeometricallyIntegral`: a `k`-algebra `S` is geometrically integral over `k` if
  every base change of `Spec S ⟶ Spec k` along a field-valued point of `Spec k` is an integral
  scheme.

## Main results

* `Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct`: `S` is geometrically integral
  over `k` if and only if `S ⊗[k] k'` is a domain for every field extension `k'/k`.

## Implementation notes

Geometric integrality is spelled through Mathlib's `AlgebraicGeometry.GeometricallyIntegral`
applied to `Spec S ⟶ Spec k`, the way tags 0G31 and 0G32 spell geometric irreducibility, rather
than by quantifying over field extensions by hand: `AlgebraicGeometry.geometrically` unfolds to
the source's quantifier, because a morphism `Spec k' ⟶ Spec k` out of the spectrum of a field is
the same as a `k`-algebra structure on `k'`, and the base change along it is `Spec (S ⊗[k] k')`.
The notion is therefore only a name for an existing one, so it is an `abbrev`: Mathlib's API for
the morphism property — stability under base change, the behaviour of fibres, and the
decomposition `GeometricallyIntegral = GeometricallyReduced ⊓ GeometricallyIrreducible`
(`AlgebraicGeometry.GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible`,
which is tag 05DY) — applies to it unchanged, and instance search sees through it. The price of
the reformulation is that the source's own sentence has to be recovered as a theorem, which is
`Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct`.

Because the definition passes through `Spec`, the field `k` and the algebra `S` must lie in a
common universe, and the test fields `k'` lie in it too, as they do in
`AlgebraicGeometry.geometrically`; the condition on tensor products would allow three unrelated
universes. This is no restriction on the mathematics: a pair of zero divisors in `S ⊗[k] k'`
involves only finitely many elements of `k'`, so it already lies in the subring `S ⊗[k] k₀` for
the subextension `k₀/k` they generate, that subring injects into `S ⊗[k] k'` because `S` is flat
over `k`, and `k₀` has an isomorphic copy in the universe of `k`.

The definition tests all field extensions of `k`, not the single extension `AlgebraicClosure k`
as Mathlib's `Algebra.IsGeometricallyReduced` does; the two shapes agree only through a theorem,
which for reducedness is still open upstream. No finiteness, reducedness or Noetherian
hypothesis is added, and the only data are `k` and the structure map `algebraMap k S`, both of
which occur in the condition. The notion is non-degenerate in both directions: `k` is
geometrically integral over `k`, and so is `k[X]`, since `k[X] ⊗[k] k'` is `k'[X]`; whereas
`ℚ(i)` is not geometrically integral over `ℚ`, since `ℚ(i) ⊗[ℚ] ℚ(i)` is `ℚ(i) × ℚ(i)`, and the
zero algebra is not, since the zero ring is not a domain.

## References

* [Stacks Project, Tag 05DX](https://stacks.math.columbia.edu/tag/05DX)
-/

@[expose] public section



open AlgebraicGeometry CategoryTheory CommRingCat TensorProduct

/-- A `k`-algebra `S` is **geometrically integral over `k`** if every base change of
`Spec S ⟶ Spec k` along a field-valued point of `Spec k` is an integral scheme, equivalently
if for every field extension `k'/k` the ring `S ⊗[k] k'` is a domain
(`Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct`). -/
@[stacks 05DX, ega "IV 4.6.2" "affine, special case", sga "6 XII 1.2" "special case"]
public abbrev Algebra.IsGeometricallyIntegral (k S : Type u) [Field k] [CommRing S]
    [Algebra k S] : Prop :=
  GeometricallyIntegral (Spec.map (ofHom (algebraMap k S)))

/-- Being an integral scheme is invariant under isomorphism.

This is `AlgebraicGeometry.IsIntegral.of_isIso` packaged as an instance, which is what makes
`AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms` and its affine variant
available for `AlgebraicGeometry.GeometricallyIntegral`. It belongs next to
`AlgebraicGeometry.IsIntegral.of_isIso` in Mathlib and should be deleted from here as soon as a
Mathlib version providing it is available. -/
public instance AlgebraicGeometry.IsIntegral.isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (AlgebraicGeometry.IsIntegral (X := ·)) :=
  ⟨fun e h => @AlgebraicGeometry.IsIntegral.of_isIso _ _ h e.hom inferInstance⟩

/-- A `k`-algebra `S` is geometrically integral over `k` if and only if `S ⊗[k] k'` is a domain
for every field extension `k'/k`. This is the form the definition takes in the source. -/
public theorem Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct
    (k S : Type u) [Field k] [CommRing S] [Algebra k S] :
    Algebra.IsGeometricallyIntegral k S ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k'], IsDomain (S ⊗[k] k') := by
  rw [Algebra.IsGeometricallyIntegral, geometricallyIntegral_iff,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  refine forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [← affine_isIntegral_iff (.of (S ⊗[k] K))]
  exact ObjectProperty.prop_iff_of_iso _ (pullbackSpecIso k S K)

end
end

/-!
# Geometrically integral algebras

Throughout, `k` is a field and `S` is a commutative unital `k`-algebra. For a field
extension `k'/k` the ring `S ⊗_k k'` is again a commutative ring, and `Spec(S ⊗_k k')`
denotes its prime spectrum with the Zariski topology.

Following the Stacks project, a *domain* is a nonzero commutative ring in which `a b = 0`
implies `a = 0` or `b = 0` (the zero ring is not a domain; in Lean `IsDomain` bundles this
with `Nontrivial`), a ring is *reduced* if it has no nonzero nilpotent element
(`IsReduced`), and a topological space is *irreducible* if it is nonempty and is not the
union of two proper closed subsets (`IrreducibleSpace`, which bundles
`PreirreducibleSpace` with `Nonempty`).

The three geometric properties of `S` over `k` are: *geometrically integral* (Stacks tag
05DX), `S ⊗_k k'` is a domain for every field extension `k'/k`; *geometrically reduced*
(Stacks tag 030S), `S ⊗_k k'` is reduced for every `k'/k`; and *geometrically irreducible*
(Stacks tag 037L), `Spec(S ⊗_k k')` is irreducible for every `k'/k`.

The main result, Stacks tag 05DY, is that `S` is geometrically integral over `k` if and
only if it is both geometrically irreducible and geometrically reduced over `k`. The
equivalence rests on the ring-theoretic fact that a commutative ring `R` is a domain iff
`R` is reduced and `Spec(R)` is irreducible; both implications follow by applying that
characterization simultaneously for all field extensions `k'/k`, using that `S ⊗_k k'` and
`k' ⊗_k S` are canonically isomorphic, so the order of the tensor factors is irrelevant.

## Implementation notes

The field extensions `k'/k` are quantified over all types `k'` in a fixed universe `w`
carrying a `Field` structure and a `k`-algebra structure. `GeometricallyReduced` comes
from `StacksFrontier.RingTheory.GeometricallyReduced.Basic`, where it is stated for `k' ⊗[k] S`.
-/

@[expose] public section

open TensorProduct

universe u v w

/-- `S` is *geometrically integral over `k`* if for every field extension `k'/k` the ring
`S ⊗[k] k'` is an integral domain. This is Stacks tag 05DX. -/
@[ega "IV 4.6.2" "affine, special case", sga "6 XII 1.2" "special case"]
def GeometricallyIntegral (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S] :
    Prop :=
  ∀ (k' : Type w) [Field k'] [Algebra k k'], IsDomain (S ⊗[k] k')

/-- `S` is *geometrically irreducible over `k`* if for every field extension `k'/k` the
prime spectrum `Spec(S ⊗[k] k')` is an irreducible topological space (and hence in
particular nonempty). This is Stacks tag 037L. -/
@[ega "IV 4.5.2" "(c), special case", ega "IV 4.5.9"]
def GeometricallyIrreducible (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S] :
    Prop :=
  ∀ (k' : Type w) [Field k'] [Algebra k k'], IrreducibleSpace (PrimeSpectrum (S ⊗[k] k'))

/-- Ring-theoretic characterization: a commutative ring `R` is an integral domain iff its
prime spectrum is irreducible and `R` is reduced.

Irreducibility of the spectrum says that the nilradical is prime and reducedness says that the
nilradical is `⊥`, so the two together say that `⊥` is prime. This is the affine counterpart of
`AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced`. -/
@[ega "I 1.1.13" "reduced rings"]
theorem isDomain_iff_irreducibleSpace_and_isReduced (R : Type*) [CommRing R] :
    IsDomain R ↔ IrreducibleSpace (PrimeSpectrum R) ∧ IsReduced R := by
  refine ⟨fun _ ↦ ⟨PrimeSpectrum.irreducibleSpace, isReduced_of_noZeroDivisors⟩,
    fun ⟨hi, hr⟩ ↦ ?_⟩
  have : (⊥ : Ideal R).IsPrime := by
    rw [← nilradical_eq_bot_iff.mpr hr, show nilradical R = (⊥ : Ideal R).radical from rfl,
      ← PrimeSpectrum.isIrreducible_zeroLocus_iff, PrimeSpectrum.zeroLocus_bot]
    exact hi.isIrreducible_univ
  exact IsDomain.of_bot_isPrime R

/-- `S ⊗[k] k'` is reduced if and only if `k' ⊗[k] S` is. -/
private theorem isReduced_tensor_comm_iff (k : Type u) [Field k] (S : Type v) [CommRing S]
    [Algebra k S] (k' : Type w) [Field k'] [Algebra k k'] :
    IsReduced (S ⊗[k] k') ↔ IsReduced (k' ⊗[k] S) :=
  ⟨isReduced_of_ringEquiv (Algebra.TensorProduct.comm k k' S).toRingEquiv,
    isReduced_of_ringEquiv (Algebra.TensorProduct.comm k S k').toRingEquiv⟩

/-- A `k`-algebra `S` is geometrically integral over `k` if and only if it is both
geometrically irreducible and geometrically reduced over `k`. This is Stacks tag 05DY.

`GeometricallyReduced` uses the convention `IsReduced (k' ⊗[k] S)` (extension on the
left). The local statements about `S ⊗[k] k'` (algebra on the left) are interchanged with
these via the canonical ring isomorphism `Algebra.TensorProduct.comm`. -/
@[stacks 05DY,
  ega "IV 4.6.14" "special case",
  ega "IV 4.6.2" "affine, special case",
  sga "3 XIX 2.1" "partial"]
theorem geometricallyIntegral_iff_irreducible_and_reduced
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S] :
    GeometricallyIntegral.{u, v, w} k S ↔
      GeometricallyIrreducible.{u, v, w} k S ∧ GeometricallyReduced.{u, v, w} k S :=
  ⟨fun h ↦ ⟨fun k' _ _ ↦ ((isDomain_iff_irreducibleSpace_and_isReduced _).mp (h k')).1,
      fun k' _ _ ↦ (isReduced_tensor_comm_iff k S k').mp
        ((isDomain_iff_irreducibleSpace_and_isReduced _).mp (h k')).2⟩,
    fun ⟨hirr, hred⟩ k' _ _ ↦ (isDomain_iff_irreducibleSpace_and_isReduced _).mpr
      ⟨hirr k', (isReduced_tensor_comm_iff k S k').mpr (hred k')⟩⟩

end
