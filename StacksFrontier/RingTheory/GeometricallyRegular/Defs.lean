module

public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v



/-!
# Geometrically regular algebras

Let `k` be a field and let `R` be a `k`-algebra. Then `R` is *geometrically regular over `k`* if
`K ⊗[k] R` is a regular ring — Noetherian, with every localization at a prime a regular local
ring, Definition 00OD — for every finitely generated field extension `K/k`. Taking `K = k` shows
that a geometrically regular algebra is itself regular, hence Noetherian; the condition is strictly
stronger, since regularity of `R` is not preserved by inseparable base change.

The extensions are restricted to the finitely generated ones because that is what keeps the
condition about *Noetherian* rings: `K ⊗[k] R` is Noetherian for `R` Noetherian and `K/k` finitely
generated (Lemma 045I), and for a general extension it need not be. By Lemma 0381 the condition is
already equivalent to its special case over the finite purely inseparable extensions `k'/k`, which
is why the source states the definition as "the equivalent conditions of Lemma 0381 hold": the two
readings define the same class of algebras, and the harder-to-check one is taken as the definition
here so that its consequences are available without invoking that lemma.

## Main definitions

* `Algebra.IsGeometricallyRegular`: a `k`-algebra `R` over a field `k` is geometrically regular
  when `K ⊗[k] R` is a regular ring for every finitely generated field extension `K/k`.

## Implementation notes

The definition is condition (1) of Lemma 0381 rather than its condition (2): the projection
`Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct` is then an instance giving regularity
of `K ⊗[k] R` for every finitely generated `K/k` directly, which is how a consumer uses geometric
regularity, while condition (2) follows from it by instance resolution alone
(`Module.Finite k K → Algebra.FiniteType k K → Algebra.EssFiniteType k K`). The converse
implication — the mathematical content, and what makes an instance cheap to construct — is Lemma
0381, `Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable`.

Regularity is Mathlib's `IsRegularRing`, which is Definition 00OD verbatim and already contains
Noetherianness (it extends `IsNoetherian R R`), so the source's hypothesis that `R` be Noetherian
is not carried: it is a consequence of the definition, via `R ≃ₐ[k] k ⊗[k] R`
(`Algebra.TensorProduct.lid`) and `IsRegularRing.of_ringEquiv`. A class with that hypothesis
attached would be the same class with a redundant field.

"Finitely generated field extension" is `Algebra.EssFiniteType k K`, which for a field `K` says
exactly that `K` is generated as a field by finitely many elements over `k`
(`IntermediateField.essFiniteType_iff`); it is not `Algebra.FiniteType`, which for fields is the
strictly stronger condition of being generated as a `k`-algebra and would make the definition miss
`K = k(t)`. This is the spelling used for the same phrase in Lemmas 0381, 037X and 037Z.

The test field ranges over `Type u`, the universe of `k`, and this is the source's condition for
extensions in every universe: a finitely generated field extension `K/k` is a localization of a
quotient of a polynomial algebra over `k` in finitely many variables, hence `k`-isomorphic to a
field in `Type u`, and both the base change and `IsRegularRing` transport along ring equivalences
(`IsRegularRing.of_ringEquiv`). A free universe parameter would instead be *weaker* and would not
be the source's condition: for `k : Type 1` of cardinality above the continuum no field in `Type 0`
carries a `k`-algebra structure at all, so the condition would hold vacuously. (Lemma 0381 states
an equivalence between two families indexed by the *same* universe, so a free universe is
appropriate there and not here.) The same choice is made for `Algebra.IsGeometricallyConnected`
(Definition 037T).

Faithfulness to the source, point by point. (1) No hypothesis is idle: `Field k`, `CommRing R` and
`Algebra k R` are exactly what makes `K ⊗[k] R` a commutative ring over which regularity can be
asserted, and the single field of the class mentions all three; the source's Noetherian hypothesis
is implied, as explained above, and is therefore not assumed. (2) The scalars and the base are the
source's: the tensor product is over the base field `k` itself, of the very algebra `R`, and
regularity is asserted of the ring `K ⊗[k] R` — not of `R` over `K`, and not over an intermediate
field. (3) Where the source names an object, this pins it: "regular" is `IsRegularRing`, Definition
00OD, not a variant such as finite global dimension (which differs for non-regular Noetherian
rings, Lemma 00OE), and the base change is Mathlib's `TensorProduct k K R` with its canonical
commutative ring structure and its canonical `k`-algebra maps, so the condition is about that ring
and not about an unspecified one. (4) The instantiation is not degenerate: `R := k` is
geometrically regular over `k`, since `K ⊗[k] k ≃ₐ[k] K` is a field, and so is `R := k[X]`; but for
`k = 𝔽_p(t)` and `R = k[X]/(X^p - t)` the algebra `R` is a field, hence regular, while for
`k' = k(t^{1/p})` the ring `k' ⊗[k] R` is `k'[X]/(X - t^{1/p})^p`, which is not even reduced, so
`R` is not geometrically regular. The class is therefore neither empty nor everything, and it is
genuinely stronger than regularity of `R`.

## References

* [Stacks Project, Tag 0382](https://stacks.math.columbia.edu/tag/0382)
* [Stacks Project, Tag 0381](https://stacks.math.columbia.edu/tag/0381)
* [Stacks Project, Tag 00OD](https://stacks.math.columbia.edu/tag/00OD)
-/

open TensorProduct

@[expose] public section



namespace Algebra

/-- A `k`-algebra `R` over a field `k` is *geometrically regular over `k`* if `K ⊗[k] R` is a
regular ring (Definition 00OD) for every finitely generated field extension `K/k`. By Lemma 0381
it is enough to require this for the finite purely inseparable extensions `k'/k`. -/
@[stacks 0382 "Stated as condition (1) of Lemma 0381; condition (2) follows by instance
resolution and the converse is that lemma. Regular ring is Definition 00OD, that is Mathlib's
`IsRegularRing`, which already contains Noetherianness, so the source's hypothesis that `R` be
Noetherian is not assumed but implied (take `K := k`). A finitely generated field extension is
`Algebra.EssFiniteType` (`IntermediateField.essFiniteType_iff`), and the test field ranges over the
universe of `k`, which is the source's condition for extensions in every universe. See the module
docstring.", ega "IV 6.7.6"]
public class IsGeometricallyRegular (k : Type u) (R : Type v) [Field k] [CommRing R]
    [Algebra k R] : Prop where
  /-- For every finitely generated field extension `K/k`, the ring `K ⊗[k] R` is regular. -/
  isRegularRing_tensorProduct (K : Type u) [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] : IsRegularRing (K ⊗[k] R)

attribute [instance] IsGeometricallyRegular.isRegularRing_tensorProduct

end Algebra

end
