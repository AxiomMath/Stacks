module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.Trace.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Differences of classes of rational points are indivisible

Let `H^*` be a Weil cohomology theory with coefficient field `F` of characteristic zero, let
`k'/k` be a finite separable extension and let `X` be a smooth projective scheme over `k'`. If
`x` and `x'` are `k'`-rational points of `X` whose cycle classes `γ([x])` and `γ([x'])` differ,
then `[x] - [x']` is not divisible by any integer `n > 1` in `CH_0(X)`.

The proof is the source's. Suppose `[x] - [x'] = n c`. By Stacks 0FH5 the class `c` is
represented by a zero-cycle supported on closed points whose residue fields are separable over
`k`, so applying `γ` gives

`γ([x]) - γ([x']) = n ∑ m_i γ([x_i])`

in `H^{2d}(X)(d)`. Poincaré duality — axiom `(A)(b)` — turns this into an identity between
functionals on `H^0(X)`, and on each closed point with separable residue field the functional
`a ↦ ∫_X a ∪ γ([x_i])` is the trace map of the finite separable `F`-algebra `H^0(x_i)` composed
with the pullback `i_i^* : H^0(X) ⟶ H^0(x_i)`, by Stacks 0FHQ and the projection formula. The
resulting identity

`Tr_{H^0(x)/F} ∘ i^* - Tr_{H^0(x')/F} ∘ (i')^* = n ∑ m_i Tr_{H^0(x_i)/F} ∘ i_i^*`

is exactly the hypothesis of Stacks 0FHT: the two pullbacks `i^*` and `(i')^*` land in
`H^0(Spec k')`, since `x` and `x'` are `k'`-rational, and they are split by the pullback along
the structure morphism `X ⟶ Spec k'`. So Stacks 0FHT forces `i^* = (i')^*`, whence
`γ([x]) = γ([x'])` by Poincaré duality again, a contradiction.

## Main definitions

* `Stacks.WeilCohomology.IsSeparableTraceCombination`: the property of a functional on an
  `F`-algebra `A` of being an integral combination of trace maps of finite separable
  `F`-algebras, composed with algebra maps out of `A`. This is the shape that Stacks 0FH5 and
  Stacks 0FHQ give to `a ↦ ∫_X a ∪ γ(c)` for a zero-cycle class `c`.
* `Stacks.WeilCohomology.rationalPointChowClass`: the class in `CH_0(X)` of a `k'`-rational
  point of a scheme `X` over `k'`, that is of a section of its structure morphism.

## Main results

* `Stacks.WeilCohomology.rationalPointChowClass_sub_ne_zsmul`: the indivisibility statement.

## Implementation notes

The cycle side of the statement is geometric: `X` is a scheme over `k'`, the points are sections
`x, x' : Spec k' ⟶ X` of its structure morphism, and `CH_0(X)` is
`Stacks.Chow.chowGroup` for `Stacks.Chow.fieldChowSituation k'` in dimension zero, so that
divisibility is divisibility in that group. As elsewhere in this directory the cohomological
data is supplied as explicit arguments rather than through a bundled Weil cohomology theory; the
bundled `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory` assumes the base field
algebraically closed, over which every finite separable extension is trivial, so it can express
only the case `k' = k`. The dictionary is as follows, with `d` the dimension of `X` over `k'`.

* `F` is the coefficient field `H^0(Spec k)` of the theory, of characteristic zero by `(D0)`.
* `A` stands for `H^0(X)`; the instance `[FiniteDimensional F A]` is axiom `(A)(a)`.
* `F'` stands for `H^0(Spec k')`, which is a finite separable `F`-algebra by Stacks 0FHQ applied
  to the zero-dimensional smooth projective `k`-scheme `Spec k'`; this is where the hypothesis
  that `k'/k` is finite separable is used, and it is recorded by the instances on `F'`.
* `T` stands for `H^{2d}(X)(d)` and `pair` for the cup-product trace pairing
  `(a, c) ↦ ∫_X a ∪ c` between `H^0(X)` and it, part of `(D1)` and `(D3)`; that it is a perfect
  pairing is axiom `(A)(b)` for `X`, recorded by `[pair.IsPerfPair]`. Only injectivity of
  `pair.flip` is used.
* `cycleClass` is the cycle class map `γ` of `(D2)` on `CH_0(X)`.
* `pullback` and `pullback'` are `i^*` and `(i')^*`, the pullbacks along the two points, which
  land in `H^0(Spec k') = F'` because the points are `k'`-rational; `structurePullback` is the
  pullback along `X ⟶ Spec k'`, and `hsplit`, `hsplit'` say that the two composites
  `H^0(Spec k') ⟶ H^0(X) ⟶ H^0(Spec k')` are the identity, which is functoriality of `(D1)`
  applied to `x ≫ p = id` and `x' ≫ p = id`. Surjectivity of `i^*` and `(i')^*` is not a
  hypothesis: it follows from having a section.
* `htrace` and `htrace'` are the identities `∫_X a ∪ γ([x]) = Tr_{H^0(x)/F}(i^*a)`, which the
  source obtains from Stacks 0FHG (the class of a closed point is `i_*1`), the projection
  formula of Stacks 0FHB and Stacks 0FHQ part (4) (integration on a zero-dimensional scheme is
  the trace map).
* `hsep` is Stacks 0FH5 together with the same three inputs for the closed points appearing in
  the representative it produces: every zero-cycle class `c` pairs against `H^0(X)` as an
  integral combination of traces of finite separable `F`-algebras.

The source reduces to `X` irreducible of dimension `d` before applying Poincaré duality, the
other case being immediate. That reduction is absorbed here into the single group `T`: the data
is one top-degree cohomology group with a perfect pairing against `H^0(X)`, which is what the
reduction produces. Smoothness and projectivity of `X` over `k'` likewise enter only through
the availability of the pairing, of the cycle class map and of the trace identities, all of
which are hypotheses here, so no smoothness or projectivity hypothesis is imposed on `p` and
the statement is more general than the source's rather than weaker.

## References

* [Stacks Project, Tag 0FHU](https://stacks.math.columbia.edu/tag/0FHU)
* [Stacks Project, Tag 0FHT](https://stacks.math.columbia.edu/tag/0FHT)
* [Stacks Project, Tag 0FHQ](https://stacks.math.columbia.edu/tag/0FHQ)
* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

namespace Stacks.WeilCohomology

/-! ### Functionals that are integral combinations of separable traces -/

/-- A functional `φ` on an `F`-algebra `A` **is an integral combination of separable traces** if
there are finitely many finite separable `F`-algebras `G i`, algebra maps `ι i : A ⟶ G i` and
integers `m i` with `φ = ∑ m i · Tr_{G i / F} ∘ ι i`.

For a Weil cohomology theory this is the shape that Stacks 0FH5 and Stacks 0FHQ give to the
functional `a ↦ ∫_X a ∪ γ(c)` attached to a zero-cycle class `c` on a smooth projective scheme:
the class `c` is represented by a cycle supported on closed points with separable residue
fields, the degree-zero cohomology of such a point is a finite separable `F`-algebra, and
integration on it is its trace map. -/
def IsSeparableTraceCombination (F : Type u) [Field F] (A : Type v) [CommRing A] [Algebra F A]
    (φ : A →ₗ[F] F) : Prop :=
  ∃ (r : ℕ) (G : Fin r → Type w) (_ : ∀ i, CommRing (G i)) (_ : ∀ i, Algebra F (G i))
    (_ : ∀ i, FiniteDimensional F (G i)) (_ : ∀ i, Algebra.IsSeparable F (G i))
    (ι : ∀ i, A →ₐ[F] G i) (m : Fin r → ℤ),
    φ = ∑ i, m i • (Algebra.trace F (G i)).comp (ι i).toLinearMap

/-! ### The zero-cycle class of a rational point -/

/-- **The class in `CH_0(X)` of a `k`-rational point of a scheme `X` over `k`**, that is of a
section `x` of its structure morphism `p`. Such a section is a closed immersion, and the class
is that of the associated zero-cycle. -/
def rationalPointChowClass (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType p]
    (x : (Stacks.Chow.fieldChowSituation k).S ⟶ X)
    (hx : x ≫ p = 𝟙 (Stacks.Chow.fieldChowSituation k).S) :
    Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) p 0 :=
  letI : IsClosedImmersion x := isClosedImmersion_of_comp_eq_id p x hx
  QuotientAddGroup.mk
    (Stacks.Chow.cycleAssociatedToClosedSubscheme (Stacks.Chow.fieldChowSituation k) p x 0)

/-! ### Indivisibility of the difference -/

/-- **Stacks Project, Tag 0FHU.** Let `H^*` be a Weil cohomology theory with coefficient field
`F` of characteristic zero, let `k'/k` be a finite separable extension and let `X` be a smooth
projective scheme over `k'`. If `x` and `x'` are `k'`-rational points of `X` with
`γ([x]) ≠ γ([x'])`, then `[x] - [x']` is not divisible by any integer `n > 1` in `CH_0(X)`.

The cohomological data and the axioms it satisfies are the explicit arguments: `[pair.IsPerfPair]`
is axiom `(A)(b)` for `X`, `cycleClass` is the cycle class map `γ` of `(D2)`, the instances on
`F' = H^0(Spec k')` are Stacks 0FHQ for `Spec k'` and are where separability of `k'/k` enters,
`hsplit` and `hsplit'` are functoriality of `(D1)` along `x ≫ p = id` and `x' ≫ p = id`,
`htrace` and `htrace'` identify `∫_X a ∪ γ([x])` with the trace of `i^*a` by Stacks 0FHG, the
projection formula and Stacks 0FHQ part (4), and `hsep` is Stacks 0FH5 with those same inputs
applied to the separable closed points it produces.

## What is assumed and what is proved

Presenting `(D0)`-`(D3)` and `(A)`-`(C)` as explicit arguments is not a restriction: "assume
given `(D0)`-`(D3)` satisfying `(A)`, `(B)`, `(C)`" is the source's own hypothesis, and the
explicit-argument presentation is this directory's convention for it.

What *is* a restriction is that three further inputs are assumed rather than derived, where the
source derives them from those axioms, because this library does not have them.

* `hsep` is Stacks 0FH5, which is not proved in this library; it is a lemma of the chapter,
  not axiom data.
* `htrace` and `htrace'` are the identification of `∫_X a ∪ γ([x])` with the trace of `i^*a`,
  which needs Stacks 0FHG, the projection formula of Stacks 0FHB and Stacks 0FHQ part (4) glued
  together on schemes.
* The reduction to `X` irreducible of dimension `d` is absorbed into the single group `T`.

So the theorem is weaker than "the axioms imply the conclusion", and the attribute records that.
Two departures go the other way and are genuine generalizations: no smoothness or projectivity
is imposed on `p`, since those enter only through the pairing, the cycle class map and the trace
identities, all of which are hypotheses here; and of axiom `(A)(b)` only injectivity of
`pair.flip` is consumed. -/
@[stacks 0FHU "(D0)-(D3), (A)-(C) as explicit arguments is the source's own hypothesis and this \
  directory's convention, not a restriction; but `hsep` (Stacks 0FH5, not proved here) \
  and `htrace`, `htrace'` (∫_X a ∪ γ([x]) = trace of i^*a, via 0FHG, 0FHB, 0FHQ(4)) are carried \
  rather than derived, as is the reduction to irreducible `X`. Generalizations: no smoothness \
  or projectivity on `p`; only `pair.flip` injectivity is used of (A)(b)"]
theorem rationalPointChowClass_sub_ne_zsmul
    {k' : Type u} [Field k'] {X : Scheme.{u}}
    (p : X ⟶ (Stacks.Chow.fieldChowSituation k').S) [LocallyOfFiniteType p]
    (x x' : (Stacks.Chow.fieldChowSituation k').S ⟶ X)
    (hx : x ≫ p = 𝟙 (Stacks.Chow.fieldChowSituation k').S)
    (hx' : x' ≫ p = 𝟙 (Stacks.Chow.fieldChowSituation k').S)
    (F : Type v) [Field F] [CharZero F]
    (F' : Type w) [CommRing F'] [Algebra F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F']
    (A : Type x) [CommRing A] [Algebra F A] [FiniteDimensional F A]
    (T : Type y) [AddCommGroup T] [Module F T]
    (pair : A →ₗ[F] T →ₗ[F] F) [pair.IsPerfPair]
    (cycleClass : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k') p 0 →+ T)
    (pullback pullback' : A →ₐ[F] F') (structurePullback : F' →ₐ[F] A)
    (hsplit : pullback.comp structurePullback = AlgHom.id F F')
    (hsplit' : pullback'.comp structurePullback = AlgHom.id F F')
    (htrace : ∀ a : A, pair a (cycleClass (rationalPointChowClass k' p x hx)) =
      Algebra.trace F F' (pullback a))
    (htrace' : ∀ a : A, pair a (cycleClass (rationalPointChowClass k' p x' hx')) =
      Algebra.trace F F' (pullback' a))
    (hsep : ∀ c : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k') p 0,
      IsSeparableTraceCombination.{v, x, z} F A (pair.flip (cycleClass c)))
    (hne : cycleClass (rationalPointChowClass k' p x hx) ≠
      cycleClass (rationalPointChowClass k' p x' hx'))
    (n : ℤ) (hn : 1 < n)
    (c : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k') p 0) :
    rationalPointChowClass k' p x hx - rationalPointChowClass k' p x' hx' ≠ n • c := by
  intro hdiv
  obtain ⟨r, G, hGring, hGalg, hGfin, hGsep, ι, m, hm⟩ := hsep c
  -- the two point classes pair against `H^0(X)` as traces
  have hflip : ∀ (f : A →ₐ[F] F') (t : T),
      (∀ a : A, pair a t = Algebra.trace F F' (f a)) →
        pair.flip t = (Algebra.trace F F').comp f.toLinearMap := fun f t h =>
    LinearMap.ext fun a => by simpa using h a
  -- the trace relation of Stacks 0FHT
  have key : (Algebra.trace F F').comp pullback.toLinearMap -
      (Algebra.trace F F').comp pullback'.toLinearMap =
        n • ∑ i, m i • (Algebra.trace F (G i)).comp (ι i).toLinearMap := by
    rw [← hflip pullback _ htrace, ← hflip pullback' _ htrace', ← hm, ← map_sub, ← map_zsmul,
      ← map_sub, hdiv, map_zsmul]
  -- Stacks 0FHT identifies the two pullbacks
  have hsurj : Function.Surjective pullback := fun b =>
    ⟨structurePullback b, by simpa using AlgHom.congr_fun hsplit b⟩
  have hsurj' : Function.Surjective pullback' := fun b =>
    ⟨structurePullback b, by simpa using AlgHom.congr_fun hsplit' b⟩
  have heq : pullback = pullback' :=
    AlgHom.eq_of_trace_sub_trace_eq_zsmul F F' A G pullback pullback' ι hsurj hsurj'
      structurePullback hsplit hsplit' n hn m key
  -- Poincaré duality turns that into equality of the two cycle classes
  exact hne <| (LinearMap.IsPerfPair.bijective_right pair).injective <| by
    rw [hflip pullback _ htrace, hflip pullback' _ htrace', heq]

end Stacks.WeilCohomology

end
