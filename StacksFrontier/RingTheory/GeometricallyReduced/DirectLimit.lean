module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
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

/-!
# Directed colimits of geometrically reduced algebras

Proof of `DirectLimit.instIsGeometricallyReduced`: a directed colimit of geometrically reduced
`R`-algebras is geometrically reduced over the commutative ring `R`.

The source's proof is that tensor product commutes with colimits, so the argument here is that
sentence in two steps. Geometric reducedness of `A` is reducedness of `K ⊗[R] A` for `K` the
algebraic closure of the residue field at a prime of `R`, and the base change of the colimit is
the colimit of the base changes (`directLimitEquiv`), which is reduced because a directed colimit
of reduced rings is reduced (`isReduced_directLimit`).

## Main results

* `Stacks.GeometricallyReduced.Colimit.solution`: the statement of Stacks Tag 030T, part (3).

## Implementation notes

`isReduced_directLimit` is stated for a directed colimit of monoids with zero, the weakest
structure in which nilpotence makes sense; the base changed system is a system of rings and
uses it there. Mathlib's `TensorProduct.directLimitRight` is the module-level half of
`directLimitEquiv`, but for `Module.DirectLimit`, the colimit built as a quotient of a direct
sum, which is a different type from the `DirectLimit` of the statement; the two are only
identified by `Module.DirectLimit.linearEquiv`, which does not transport the ring structure. So
the algebra equivalence is built here from the two maps between the base change of the colimit
and the colimit of the base changes.

Of those two maps only `fromColim` is built as an algebra map, out of the colimit by its universal
property; the comparison map `toColim` in the other direction is built as a mere linear map, which
costs one `TensorProduct.lift` and no commutation side condition, and it is enough, since a
two-sided inverse of an algebra map is automatically one. `K` is not assumed flat over `R` — no
half of the equivalence is obtained by flat base change — and the members `G i` are not assumed
commutative, matching `Algebra.IsGeometricallyReduced`.

## References

* [Stacks 030T](https://stacks.math.columbia.edu/tag/030T), part (3).
-/

namespace Stacks.GeometricallyReduced.Colimit

open TensorProduct

suppress_compilation

section Reduced

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {G : ι → Type*} [∀ i, MonoidWithZero (G i)]
  {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  [∀ i j (h : i ≤ j), MonoidWithZeroHomClass (T h) (G i) (G j)]
  (f : ∀ i j (h : i ≤ j), T h) [DirectedSystem G (f · · ·)]

/-- A directed colimit of reduced monoids with zero is reduced: a nilpotent class comes from some
stage, the power of it that vanishes in the colimit already vanishes at a later stage, and there
the element itself vanishes. -/
private theorem isReduced_directLimit [∀ i, IsReduced (G i)] : IsReduced (DirectLimit G f) where
  eq_zero x := by
    induction x using DirectLimit.induction with
    | _ i a =>
      rintro ⟨n, hn⟩
      rw [DirectLimit.npow_def, DirectLimit.exists_eq_zero] at hn
      obtain ⟨j, hij, hj⟩ := hn
      rw [map_pow] at hj
      rw [← DirectLimit.mk_apply i j a hij, IsNilpotent.eq_zero ⟨n, hj⟩, ← DirectLimit.zero_def j]

end Reduced

section BaseChange

variable {R : Type*} [CommRing R] {ι : Type*} [Preorder ι]
  {G : ι → Type*} [∀ i, Ring (G i)] [∀ i, Algebra R (G i)]
  {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  [∀ i j (h : i ≤ j), AlgHomClass (T h) R (G i) (G j)]
  (K : Type*) [CommRing K] [Algebra R K] (f : ∀ i j (h : i ≤ j), T h)

/-- The base change along `R → K` of the transition maps of a directed system of `R`-algebras. -/
private def baseChange (i j : ι) (h : i ≤ j) : (K ⊗[R] G i) →ₐ[R] (K ⊗[R] G j) :=
  Algebra.TensorProduct.map (AlgHom.id R K) (AlgHom.ofClass (f i j h))

private lemma baseChange_tmul (i j : ι) (h : i ≤ j) (k : K) (x : G i) :
    baseChange K f i j h (k ⊗ₜ x) = k ⊗ₜ f i j h x := rfl

variable [IsDirectedOrder ι] [Nonempty ι] [DirectedSystem G (f · · ·)]

omit [IsDirectedOrder ι] [Nonempty ι] in
private theorem directedSystem_baseChange :
    DirectedSystem (fun i ↦ K ⊗[R] G i) (baseChange K f · · ·) where
  map_self i x := by
    induction x using TensorProduct.inductionOn <;>
      simp_all [baseChange_tmul, DirectedSystem.map_self' f]
  map_map _ _ _ hij hjk x := by
    induction x using TensorProduct.inductionOn <;>
      simp_all [baseChange_tmul, DirectedSystem.map_map' f]

attribute [local instance] directedSystem_baseChange

/-- The base change along `R → K` of the structure maps of the colimit. -/
private def baseChangeOf (i : ι) : (K ⊗[R] G i) →ₐ[R] (K ⊗[R] DirectLimit G f) :=
  Algebra.TensorProduct.map (AlgHom.id R K) (DirectLimit.Algebra.of G f i)

private lemma baseChangeOf_tmul (i : ι) (k : K) (x : G i) :
    baseChangeOf K f i (k ⊗ₜ x) = k ⊗ₜ (⟦⟨i, x⟩⟧ : DirectLimit G f) := rfl

private lemma baseChangeOf_baseChange (i j : ι) (h : i ≤ j) (y : K ⊗[R] G i) :
    baseChangeOf K f j (baseChange K f i j h y) = baseChangeOf K f i y := by
  induction y using TensorProduct.inductionOn with
  | tmul k x => rw [baseChange_tmul, baseChangeOf_tmul, baseChangeOf_tmul, DirectLimit.mk_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The comparison map from the base change of the colimit to the colimit of the base changes,
`k ⊗ₜ ⟦⟨i, x⟩⟧ ↦ ⟦⟨i, k ⊗ₜ x⟩⟧`. It is only linear: multiplicativity is not needed, because
`directLimitEquiv` obtains it by inverting the algebra map `fromColim`. -/
private def toColim :
    (K ⊗[R] DirectLimit G f) →ₗ[R] DirectLimit (fun i ↦ K ⊗[R] G i) (baseChange K f) :=
  TensorProduct.lift (DirectLimit.Module.lift R ι G f
    (fun i ↦ (TensorProduct.mk R K (G i)).flip.compr₂
      (DirectLimit.Module.of R ι _ (baseChange K f) i))
    fun _ _ hij x ↦ LinearMap.ext fun k ↦
      DirectLimit.Module.of_f (f := baseChange K f) (hij := hij) (x := k ⊗ₜ x)).flip

private lemma toColim_baseChangeOf (i : ι) (y : K ⊗[R] G i) :
    toColim K f (baseChangeOf K f i y) = ⟦⟨i, y⟩⟧ := by
  induction y using TensorProduct.inductionOn with
  | tmul k x => rfl
  | add u v hu hv => rw [map_add, map_add, hu, hv, DirectLimit.add_def]

/-- The map from the colimit of the base changes to the base change of the colimit, given by the
universal property of the colimit applied to the maps `baseChangeOf`. -/
private def fromColim :
    DirectLimit (fun i ↦ K ⊗[R] G i) (baseChange K f) →ₐ[R] (K ⊗[R] DirectLimit G f) :=
  DirectLimit.Algebra.lift _ (baseChange K f) _ (baseChangeOf K f) (baseChangeOf_baseChange K f)

private lemma fromColim_mk (i : ι) (y : K ⊗[R] G i) :
    fromColim K f ⟦⟨i, y⟩⟧ = baseChangeOf K f i y := rfl

private lemma toColim_fromColim (z : DirectLimit (fun i ↦ K ⊗[R] G i) (baseChange K f)) :
    toColim K f (fromColim K f z) = z := by
  induction z using DirectLimit.induction with
  | _ i y => rw [fromColim_mk, toColim_baseChangeOf]

private lemma fromColim_toColim (x : K ⊗[R] DirectLimit G f) :
    fromColim K f (toColim K f x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul k z =>
      induction z using DirectLimit.induction with
      | _ i x => rw [← baseChangeOf_tmul, toColim_baseChangeOf, fromColim_mk]
  | add u v hu hv => rw [map_add, map_add, hu, hv]

/-- **Base change commutes with the directed colimit**: for any commutative `R`-algebra `K`, the
base change `K ⊗[R] -` of a directed colimit of `R`-algebras is the directed colimit of the base
changes. This is the algebra-level analogue of `TensorProduct.directLimitRight`, and `K` is not
assumed flat over `R`. -/
@[sga "3 V 4.1.2" "partial"]
private def directLimitEquiv :
    (K ⊗[R] DirectLimit G f) ≃ₐ[R] DirectLimit (fun i ↦ K ⊗[R] G i) (baseChange K f) :=
  (AlgEquiv.ofBijective (fromColim K f)
    ⟨Function.LeftInverse.injective (toColim_fromColim K f),
      fun x ↦ ⟨toColim K f x, fromColim_toColim K f x⟩⟩).symm

/-- The base change of a directed colimit of `R`-algebras along `R → K` is reduced as soon as the
base change of every member is. -/
private theorem isReduced_tensorProduct_directLimit [∀ i, IsReduced (K ⊗[R] G i)] :
    IsReduced (K ⊗[R] DirectLimit G f) :=
  have := isReduced_directLimit (baseChange K f)
  isReduced_of_injective (directLimitEquiv K f) (AlgEquiv.injective _)

end BaseChange

/-- A directed colimit of geometrically reduced `R`-algebras is geometrically reduced over `R`
(Stacks 030T, part (3)): its base change to an algebraic closure of each residue field of `R` is
the directed colimit of the base changes, and hence reduced. -/
public theorem solution
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι → Type*} [∀ i, Ring (G i)] [∀ i, Algebra R (G i)]
    {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ i j (h : i ≤ j), T h}
    [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
    [∀ i j (h : i ≤ j), AlgHomClass (T h) R (G i) (G j)]
    [DirectedSystem G (f · · ·)]
    [∀ i, Algebra.IsGeometricallyReduced R (G i)] :
    Algebra.IsGeometricallyReduced R (DirectLimit G f) where
  isReduced_algebraicClosure_tensorProduct p _hp :=
    isReduced_tensorProduct_directLimit (AlgebraicClosure p.ResidueField) f

end Stacks.GeometricallyReduced.Colimit

/-!
# Directed colimits of geometrically reduced algebras

Let `R` be a commutative ring and let `G` be a directed system of `R`-algebras whose members are
geometrically reduced over `R`, that is, whose base change to an algebraic closure of the residue
field of every prime of `R` is reduced. Then the colimit of the system is geometrically reduced
over `R` as well.

The mathematics is that base change commutes with directed colimits, together with the fact that a
directed colimit of reduced rings is reduced: an element of the colimit comes from some stage, and
if a power of it vanishes in the colimit then that power already vanishes at a later stage, where
reducedness makes the element itself vanish.

## Main results

* `DirectLimit.instIsGeometricallyReduced`: a directed colimit of geometrically reduced
  `R`-algebras is geometrically reduced over `R`.

## Implementation notes

The source collects four elementary properties of geometrically reduced algebras over a field `k`;
this file states (3), the directed colimit. The others are stated in their own homes: (1) a
`k`-subalgebra of a geometrically reduced algebra is geometrically reduced,
`Subalgebra.isGeometricallyReduced`; (2) an algebra all of whose finitely generated
`k`-subalgebras are geometrically reduced is geometrically reduced, Mathlib's
`Algebra.IsGeometricallyReduced.of_forall_fg`; and (4) a localization of a geometrically reduced
algebra is geometrically reduced, `IsLocalization.isGeometricallyReduced`.

The base is generalized from a field to a commutative ring `R`: neither the statement nor the
argument uses that the base is a field, and `Algebra.IsGeometricallyReduced` is defined over a
commutative base ring. For `R = k` a field, geometric reducedness of `S` is reducedness of
`AlgebraicClosure k ⊗[k] S` (`Algebra.isGeometricallyReduced_field_iff`), which is equivalent to
the source's Definition 030S asking that `K ⊗[k] S` be reduced for every field extension `K/k`.

The colimit is `DirectLimit G f`, the colimit of a `DirectedSystem` over a nonempty directed
preorder `ι`, with the transition maps arbitrary `R`-algebra homomorphisms — they are not assumed
injective, so this is the directed colimit of the source and not merely the special case of a
directed union of subalgebras, which is already covered by parts (1) and (2). Commutativity of the
members is not assumed either, matching `Algebra.IsGeometricallyReduced`, which is stated for an
arbitrary ring.

On faithfulness. (1) No hypothesis is dead: directedness and nonemptiness of `ι` and the
`DirectedSystem` compatibility are what make the colimit and its algebra structure what they are,
and geometric reducedness of every member is needed, since for `ι` a single point the colimit is
that member. (2) The base is the source's: every algebra structure, every transition map and every
base change in sight is over the single base `R`, the source's `k`. (3) The colimit is pinned, not
merely asserted to exist: it is `DirectLimit G f` with its own `R`-algebra structure, the one whose
structure maps from the members are `DirectLimit.Algebra.of`. (4) The instantiation is not
degenerate: `ι = ℕ` with `G n = MvPolynomial (Fin n) k` and the standard inclusions is a witness,
each member being geometrically reduced over a field `k` and the colimit being the polynomial ring
in countably many variables.

## References

* [Stacks 030T](https://stacks.math.columbia.edu/tag/030T)
  (`algebra-lemma-subalgebra-separable`), part (3), in the section "Geometrically reduced
  algebras". Geometric reducedness is Definition 030S, equivalent over a field to Mathlib's
  `Algebra.IsGeometricallyReduced` by Lemma 030V; the localization statement, part (4), is also
  Lemma 04KN.
-/

@[expose] public section

namespace DirectLimit

/-- **Stacks 030T (3).** A directed colimit of geometrically reduced `R`-algebras is geometrically
reduced over `R`. -/
@[stacks 030T "Part (3): a directed colimit of geometrically reduced algebras is geometrically
  reduced, stated for `DirectLimit` of a directed system of algebras over a commutative base ring,
  which for the base a field `k` is the source's statement. Part (1) is
  `Subalgebra.isGeometricallyReduced`, part (2) is Mathlib's
  `Algebra.IsGeometricallyReduced.of_forall_fg`, part (4) is
  `IsLocalization.isGeometricallyReduced`. Geometric reducedness is Mathlib's
  `Algebra.IsGeometricallyReduced`, equivalent over a field to Definition 030S by Lemma 030V."]
public instance instIsGeometricallyReduced
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι → Type*} [∀ i, Ring (G i)] [∀ i, Algebra R (G i)]
    {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ i j (h : i ≤ j), T h}
    [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
    [∀ i j (h : i ≤ j), AlgHomClass (T h) R (G i) (G j)]
    [DirectedSystem G (f · · ·)]
    [∀ i, Algebra.IsGeometricallyReduced R (G i)] :
    Algebra.IsGeometricallyReduced R (DirectLimit G f) :=
    by apply Stacks.GeometricallyReduced.Colimit.solution

end DirectLimit

end
