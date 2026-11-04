module

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init

public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.TowerLTensor
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Flatness across a localized base change

Let

```
S  →  S'
↑     ↑
R  →  R'
```

be a commutative square of rings in which `T` is the pushout `S ⊗_R R'` and `S'` is a localization
of `T` at a submonoid `W ⊆ T`, let `M` be an `S`-module and let `M'` be the base change `S' ⊗_S M`.
This file proves Stacks tag 00MQ:

1. if `M` is flat over `R` then `M'` is flat over `R'`;
2. if `S` and `S'` are local with `S → S'` a local homomorphism, then `M'` flat over `R'` together
   with `R → R'` flat implies `M` flat over `R`.

Parts (3) and (4) of the source are the instance `M = S`, `M' = S'` of these; see the statement of
the tag.

Both parts are instances of one calculation, carried out for a tower of rings `A → C → D` and a
`C`-module `P`. The associativity isomorphism `(D ⊗_C P) ⊗_A X ≅ D ⊗_C (P ⊗_A X)`, natural in the
`A`-module `X`, identifies the functor `(D ⊗_C P) ⊗_A -` with the composite of `P ⊗_A -` and
`D ⊗_C -`. Reading that forwards, `P` flat over `A` and `D` flat over `C` make `D ⊗_C P` flat over
`A`; reading it backwards, `D ⊗_C P` flat over `A` and `D` faithfully flat over `C` make `P` flat
over `A`.

Part (1) is the forward reading for `A = R'`, `C = T`, `D = S'` and `P = T ⊗_S M`: the pushout
identifies `T ⊗_S M` with `R' ⊗_R M`, which is flat over `R'` by flat base change (Lemma 00HI),
`S'` is flat over `T` because it is a localization (Lemma 00HT (5)), and cancelling the inner base
change identifies `S' ⊗_T (T ⊗_S M)` with `M'`. Part (2) is the backward reading for `A = R`,
`C = S`, `D = S'` and `P = M`: `S'` is faithfully flat over `S` by (3) applied to the square
reflected in the northwest diagonal (Lemma 00HR), and `S' ⊗_S M ≅ M'` is flat over `R` because it
is flat over `R'` and `R → R'` is flat.

## Main results

* `Stacks.Flatness.PushoutBaseChange.solution`: the statement of tag 00MQ, parts (1) and (2).

## Implementation notes

*The two flatness lemmas are missing from Mathlib.* `Module.Flat.tensorProduct_of_flat_left` and
`Module.Flat.of_tensorProduct_of_faithfullyFlat`, both in
`StacksFrontier.RingTheory.Flat.TowerLTensor`, concern flatness over a base `A` that is *not* the ring
the base change is taken along; Mathlib's `Module.Flat.baseChange` and
`Module.Flat.of_flat_tensorProduct` move the base along with the module, and
`Module.Flat.of_isLocalizedModule` localizes at a submonoid of the base rather than of a ring
acting over it. Their proofs are Mathlib's proof of `Module.Flat.trans` with the naturality of
`TensorProduct.AlgebraTensorModule.cancelBaseChange` in the module replaced by that of
`TensorProduct.AlgebraTensorModule.assoc` (`assoc_comp_lTensor`), which Mathlib does not record
either.

*Part (2) does not go through the ideal criterion.* The source verifies the criterion 00HD (00HG)
for `M` over `R`, using `I ⊗_R R' = IR'` for every ideal `I ⊆ R` to rewrite
`(I ⊗_R M) ⊗_S S' = IR' ⊗_{R'} M'` and reading off injectivity into `M'` from flatness of `M'`
over `R'`. The content of that computation is that `M'` is flat over `R` — which here is
`Module.Flat.trans`, flatness of `R → R'` composed with flatness of `M'` over `R'` — after which no
ideal is needed: descending flatness over the arbitrary base `R` along the faithfully flat
`S → S'` is `Module.Flat.of_tensorProduct_of_faithfullyFlat`. The mathematics is the source's; only
the ideal-by-ideal
bookkeeping is replaced by the transitivity of flatness.

*The pushout geometry is `Algebra.IsPushout.cancelBaseChange`.* The source's identification
`(S ⊗_R R') ⊗_S M = M ⊗_R R'`, which is the whole use of the square in part (1), is
`Algebra.IsPushout.cancelBaseChange R R' S T M : T ⊗[S] M ≃ₗ[R'] R' ⊗[R] M`, applied to the
reflected square `Algebra.IsPushout R R' S T` obtained from `Algebra.IsPushout.symm`.

## References

* [StacksProject 00MQ](https://stacks.math.columbia.edu/tag/00MQ)
* [StacksProject 00HI](https://stacks.math.columbia.edu/tag/00HI)
* [StacksProject 00HT](https://stacks.math.columbia.edu/tag/00HT)
* [StacksProject 00HR](https://stacks.math.columbia.edu/tag/00HR)
-/

/-!
# Flatness across a localized base change

Let

```
S  →  S'
↑     ↑
R  →  R'
```

be a commutative square of rings in which `S'` is a localization of the tensor product
`S ⊗_R R'`, let `M` be an `S`-module and set `M' = S' ⊗_S M`. Then

1. if `M` is flat over `R` then `M'` is flat over `R'`, and
2. if `S` and `S'` are local with `S → S'` a local homomorphism, then `M'` flat over `R'` together
   with `R → R'` flat implies `M` flat over `R`.

Taking `M = S`, so `M' = S'`, these become parts (3) and (4) of the source: `S` flat over `R`
implies `S'` flat over `R'`, and `R' → S'` and `R → R'` flat imply `S` flat over `R`.

The source's proof of (1): `M ⊗_R R'` is flat over `R'` by Lemma 00HI, and `M'` is the
localization of `M ⊗_R R'` at the multiplicative set `W ⊆ S ⊗_R R'` inverted by
`S ⊗_R R' → S'`, so `M'` is flat over `R'` by Lemma 00HT (5). Its proof of (2): (3), applied to
the square reflected in the northwest diagonal, makes `S → S'` flat, hence faithfully flat since
it is a local homomorphism of local rings (Lemma 00HR); one then verifies the ideal criterion
00HD (00HG) for `M` over `R`, using that `I ⊗_R R' = IR'` for every ideal `I ⊆ R` by flatness of
`R → R'` and that `(I ⊗_R M) ⊗_S S' = IR' ⊗_{R'} M'` injects into `M'`.

## Main results

* `Module.Flat.baseChange_and_of_flat_baseChange_of_isPushout_of_isLocalization`: Stacks 00MQ,
  parts (1) and (2); parts (3) and (4) are its instances at `M := S`.

## Implementation notes

*Each part carries only the hypotheses its own proof spends.* Part (1) is a statement about an
arbitrary commutative square: neither its conclusion nor the source's proof of it mentions a local
ring or a local homomorphism, and both lemmas it cites (00HI, 00HT (5)) are locality-free. Part
(2) spends locality at exactly one point, the passage from `Module.Flat S S'` to
`Module.FaithfullyFlat S S'` (`Module.FaithfullyFlat.of_flat_of_isLocalHom`); the rest of its
argument is the criterion 00HD (00HG), the general ideal criterion over an arbitrary ring. So of
the source's eight locality assumptions only three are ever used — `IsLocalRing S`,
`IsLocalRing S'` and `IsLocalHom (algebraMap S S')` — and those three, like `Module.Flat R R'`,
are bound *inside the second conjunct*, as `∀ [IsLocalRing S] …`, rather than in the signature.
Part (1) is therefore stated for an arbitrary square, with no locality and no flatness of
`R → R'` in scope, exactly as if it were a separate declaration; the locality of `R`, of `R'` and
of the legs `R → S`, `R → R'`, `R' → S'` is dropped altogether.

*The conclusion is a conjunction and not an equivalence.* Part (1) needs neither locality nor
`Module.Flat R R'` while part (2) needs both, so the two implications are not the two halves of
one `Iff`; adding part (2)'s hypotheses to part (1) in order to state an `Iff` would weaken it.

*The pushout is an abstract intermediate ring.* "`S'` is a localization of `S ⊗_R R'`" is
presented as a ring `T` with `Algebra.IsPushout R S R' T`, that is, the canonical map
`S ⊗_R R' → T` is an isomorphism, together with `IsLocalization W S'` for a submonoid `W ⊆ T`.
Taking `T = S ⊗[R] R'` recovers the source's literal form, while a pushout already presented in
another shape is covered with no intermediate isomorphism, as in the siblings 00P4 and 00RJ. The
two legs into `S'` are pinned to the ones through `T` by `IsScalarTower S T S'` and
`IsScalarTower R' T S'`, so commutativity of the square of rings is a consequence and needs no
`Algebra R S'`; the concrete sibling 00MO instead spells `T` as `S ⊗[R] R'` and pins the
right-hand leg by an equation of ring maps.

*`M' = S' ⊗_S M` is an abstract base change*, a pair of an `S'`-module `M'` and an `S`-linear map
`f : M →ₗ[S] M'` with `IsBaseChange S' f`, as in 00MO and 0GEB; `M' = S' ⊗[S] M` with
`TensorProduct.mk` recovers the source's module. No `R`-module structure on `M'` is assumed: the
two `R`-actions on `M'` through `S'` agree because the square commutes, so such an action is
determined rather than given, and neither part refers to one.

*Parts (3) and (4) are not separate declarations*, because with `M'` abstract they are the
instance `M := S`, `M' := S'`, `f := Algebra.linearMap S S'` of (1) and (2), the base change
hypothesis being `IsBaseChange.linearMap S S'`; the `R`-module structure on `S` is that of the
`R`-algebra `S`, and `Module.Flat R' S'` is the flatness of `R' → S'`. No isomorphism has to be
inserted, so a named composite would have no content beyond the instantiation.

*Both parts use the localization hypothesis only through flatness of `T → S'`*
(`Module.Flat.of_isLocalizedModule` in (1), `IsLocalization.flat` in (2)). It is kept in the
source's form because it is what pins `S'` over the square — a bare flat `T`-algebra is not
determined by the square — and because it is the shape the siblings 00MO, 00P4, 00RJ and 0GEB
share, so that the statements chain without an intermediate isomorphism.

Faithfulness to [StacksProject 00MQ], on the four points a reader should check.

1. No hypothesis is idle: `Module.Flat R M` and `Module.Flat R' M'` are the two antecedents,
   `Module.Flat R R'` and the three locality assumptions are bound inside the conjunct that
   spends them, and `W`, `T`, `f` occur through the pushout, localization and base change
   hypotheses.
2. The scalars and base are the source's: `Module.Flat R M` is flatness for the action through
   `R → S`, pinned by `IsScalarTower R S M`, not over `S`; `Module.Flat R' M'` is through
   `R' → S'`, pinned by `IsScalarTower R' S' M'`; `M` is base changed along `S → S'`, not along
   `R → R'`, and the pushout square is the one over `R` with legs `S` and `R'`.
3. The canonical maps are pinned, not merely asserted to exist: `T` is fixed by
   `Algebra.IsPushout R S R' T` up to the unique `R`-algebra isomorphism over `S` and `R'`, `S'`
   by `IsLocalization W S'` over that `T`, `M'` by `f` together with `IsBaseChange S' f` rather
   than by an isomorphism class, and each leg of the square is the `algebraMap` of its algebra
   instance, the two into `S'` being the composites through `T`.
4. The instantiation is not degenerate: with `k` a field, `R = k[x]_{(x)}`,
   `S = k[x, y]_{(x, y)}`, `R' = k[x, z]_{(x, z)}` and `S'` the localization of `T = S ⊗_R R'` at
   the maximal ideal generated by the images of `x`, `y`, `z`, all four legs are local
   homomorphisms of local rings and `R → R'` is flat; at `M = S` part (1) gives flatness of `S'`
   over `R'` and part (2) its converse, while at `M = S/xS` both `Module.Flat R M` and
   `Module.Flat R' M'` fail, so neither implication is vacuous.

## References

* [StacksProject 00MQ](https://stacks.math.columbia.edu/tag/00MQ)
* [StacksProject 00HI](https://stacks.math.columbia.edu/tag/00HI)
* [StacksProject 00HT](https://stacks.math.columbia.edu/tag/00HT)
* [StacksProject 00HR](https://stacks.math.columbia.edu/tag/00HR)
* [StacksProject 00HD](https://stacks.math.columbia.edu/tag/00HD)
-/

@[expose] public section

open TensorProduct

namespace Module.Flat

/-- If `B` and `S'` are both `T`-compatible `R`-algebras over a tower `R → B → T` and
`R → T → S'`, then `R → B → S'` is a tower. -/
private theorem isScalarTower_of_tower_through {R B S' : Type*} (T : Type*) [CommRing R]
    [CommRing B] [CommRing T] [CommRing S'] [Algebra R B] [Algebra R T] [Algebra B T]
    [Algebra R S'] [Algebra B S'] [Algebra T S'] [IsScalarTower R B T] [IsScalarTower R T S']
    [IsScalarTower B T S'] : IsScalarTower R B S' :=
  .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R T S', IsScalarTower.algebraMap_apply R B T,
      ← IsScalarTower.algebraMap_apply B T S']

/-- **Stacks 00MQ**, parts (1) and (2). Let `S ← R → R'` be ring maps, let `T` be the pushout
`S ⊗_R R'`, let `S'` be a localization of `T` at a submonoid `W`, and let `f : M →ₗ[S] M'` realize
`M'` as the base change `S' ⊗_S M` of an `S`-module `M`. Then (1) if `M` is flat over `R` then
`M'` is flat over `R'`, and (2) if moreover `S` and `S'` are local with `S → S'` a local
homomorphism, then `M'` flat over `R'` and `R → R'` flat imply `M` flat over `R`.

Part (1) holds for an arbitrary such square: the source's local rings and local homomorphisms are
used only in part (2), and only for `S`, `S'` and `S → S'`, so they are bound inside the second
conjunct instead of in the signature.

Parts (3) and (4) of the source, that `S` flat over `R` implies `S'` flat over `R'` and that
`R' → S'` and `R → R'` flat imply `S` flat over `R`, are the instance `M := S`, `M' := S'`,
`f := Algebra.linearMap S S'`; see the module docstring. -/
@[stacks 00MQ "Parts (1) and (2). Of the source's eight locality assumptions only `IsLocalRing S`,
`IsLocalRing S'` and `IsLocalHom (algebraMap S S')` are used, by part (2) alone, and they are bound
inside the second conjunct together with `Module.Flat R R'`, so that part (1) is stated for an
arbitrary commutative square; the rest are dropped. \"`S'` is a localization of `S ⊗_R R'`\" is
`IsLocalization W S'` over an abstract pushout `Algebra.IsPushout R S R' T`, as in the siblings
00P4 and 00RJ, and `M' = S' ⊗_S M` is `IsBaseChange S' f`, as in 00MO. Parts (3) and (4) are the
instance `M := S`, `M' := S'` and are not separate declarations. See the module docstring."]
public theorem baseChange_and_of_flat_baseChange_of_isPushout_of_isLocalization
    (R : Type*) {S R' T S' M M' : Type*}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing T] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra R T] [Algebra S T] [Algebra R' T]
    [IsScalarTower R S T] [IsScalarTower R R' T] [Algebra.IsPushout R S R' T]
    [Algebra S S'] [Algebra R' S'] [Algebra T S']
    [IsScalarTower S T S'] [IsScalarTower R' T S']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module S M'] [Module R' M'] [Module S' M']
    [IsScalarTower S S' M'] [IsScalarTower R' S' M']
    (W : Submonoid T) [IsLocalization W S'] (f : M →ₗ[S] M') (hf : IsBaseChange S' f) :
    (Module.Flat R M → Module.Flat R' M') ∧
      (∀ [IsLocalRing S] [IsLocalRing S'] [IsLocalHom (algebraMap S S')],
        Module.Flat R' M' → Module.Flat R R' → Module.Flat R M) := by
  -- `S'` is flat over `T` because it is a localization of it: this is the only use of `W`.
  have hTS' : Module.Flat T S' := IsLocalization.flat S' W
  refine ⟨fun hM => ?_, fun hM' hRR' => ?_⟩
  · -- Part (1). The reflected square exhibits `T ⊗_S M` as the base change `R' ⊗_R M`, which is
    -- flat over `R'` by flat base change, so `S' ⊗_T (T ⊗_S M) ≅ M'` is flat over `R'`.
    have : Algebra.IsPushout R R' S T := Algebra.IsPushout.symm inferInstance
    have : Module.Flat R' (T ⊗[S] M) :=
      Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange R R' S T M)
    have : Module.Flat R' (S' ⊗[T] (T ⊗[S] M)) :=
      Module.Flat.tensorProduct_of_flat_left (A := R') (C := T) (D := S') (P := T ⊗[S] M)
    exact Module.Flat.of_linearEquiv
      ((AlgebraTensorModule.cancelBaseChange S T S' S' M ≪≫ₗ hf.equiv).restrictScalars R').symm
  · -- Part (2). `S'` is flat over `S`, hence faithfully flat: this is part (3) for the reflected
    -- square.
    have : Module.Flat S T := Module.Flat.isBaseChange R S R' T Algebra.IsPushout.out
    have : Module.Flat S S' := Module.Flat.trans S T S'
    have : Module.FaithfullyFlat S S' := Module.FaithfullyFlat.of_flat_of_isLocalHom
    -- The two `R`-algebra structures on `S'` through the square agree, so `S'` is an `R`-algebra
    -- through either leg.
    let _ : Algebra R S' := ((algebraMap T S').comp (algebraMap R T)).toAlgebra
    have : IsScalarTower R T S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower R S S' := isScalarTower_of_tower_through T
    have : IsScalarTower R R' S' := isScalarTower_of_tower_through T
    -- `S' ⊗_S M ≅ M'` is flat over `R`, and flatness descends along the faithfully flat `S → S'`.
    have : Module.Flat R' (S' ⊗[S] M) := Module.Flat.of_linearEquiv (hf.equiv.restrictScalars R')
    have : Module.Flat R (S' ⊗[S] M) := Module.Flat.trans R R' _
    exact Module.Flat.of_tensorProduct_of_faithfullyFlat (A := R) (C := S) (D := S') (P := M)

end Module.Flat

namespace Stacks.Flatness.PushoutBaseChange

/-- **Stacks 00MQ**, parts (1) and (2). -/
public alias solution :=
    Module.Flat.baseChange_and_of_flat_baseChange_of_isPushout_of_isLocalization

end Stacks.Flatness.PushoutBaseChange

end

/-!
# Flatness descends along an injective ring map out of an Artinian ring

Let `R → S` be a map of commutative rings with `R` Artinian, let `M` be an `R`-module and let `N`
be the base change of `M` to `S`. This file proves Stacks 051L: if `R → S` is injective and `N` is
flat over `S`, then `M` is flat over `R`.

The source's first proof is the one formalised, and it is a specialisation of the local criterion
for flatness along an injective ring map (Stacks 051J,
`Module.Flat.of_flat_quotient_of_flat_tensorProduct_of_isNilpotent_of_injective`) at `I` the
Jacobson radical `J` of `R`. The criterion asks two things of `J`, that it be nilpotent and that
`M ⧸ JM` be flat over `R ⧸ J`, and both are consequences of `R ⧸ J` being semisimple with `J`
nilpotent — that is, of `R` being *semiprimary*: over a semisimple ring every module is projective,
hence flat, so the flatness hypothesis costs nothing. An Artinian ring is semiprimary, and that is
the whole use made of the Artinian hypothesis. Where the source says "`R/I` is a product of
fields", the formalisation says "`R ⧸ J` is semisimple": for `R` commutative Artinian the two are
the same statement, and semisimplicity is what carries the projectivity of every module.

## Main results

* `Stacks.Flatness.ArtinianDescent.solution`: Stacks 051L, in the shape of
  `Module.Flat.of_flat_baseChange_of_injective`.

## Implementation notes

The descent step is proved for a semiprimary ring rather than an Artinian one, since that is the
hypothesis it uses; the Artinian ring of the statement enters through the single instance
`IsArtinianRing.instIsSemiprimaryRing`, and the two facts about `J` come from the single
characterisation `isSemiprimaryRing_iff` rather than from `Ideal.jacobson ⊥` and a separate
nilpotence lemma. The statement itself is left at the Artinian hypothesis of the source, which
is the form Stacks Tag 051L is registered in here.

The base change of the statement is an arbitrary `f : M →ₗ[R] N` with `IsBaseChange S f`, whereas
the criterion consumed is stated for the concrete `S ⊗[R] M`; the two are matched by
`IsBaseChange.equiv`, the `S`-linear equivalence `S ⊗[R] M ≃ₗ[S] N`, along which flatness
transports by `Module.Flat.of_linearEquiv`.

## References

* [Stacks Project, Tag 051L](https://stacks.math.columbia.edu/tag/051L)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Flatness.ArtinianDescent

/-- Every module over a commutative semisimple ring is flat: it is projective by
`Module.projective_of_isSemisimpleRing`, and projective modules are flat. -/
private lemma flat_of_isSemisimpleRing (R : Type*) [CommRing R] [IsSemisimpleRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : Module.Flat R M :=
  have := Module.projective_of_isSemisimpleRing R M
  .of_projective

/-- Flatness descends along an injective ring map whose source is semiprimary: if `R` is a
commutative ring with `R ⧸ Ring.jacobson R` semisimple and `Ring.jacobson R` nilpotent,
`algebraMap R S` is injective and `S ⊗[R] M` is flat over `S`, then `M` is flat over `R`.

This is the local criterion for flatness along an injective ring map (Stacks 051J) at the Jacobson
radical, whose flatness hypothesis on the reduction `M ⧸ JM` is then automatic. It is the whole
content of Stacks 051L, the Artinian hypothesis of that statement being used only to produce
`IsSemiprimaryRing R`. -/
@[ega "IV 11.4.11" "special case", ega "IV 11.4.3" "special case"]
private lemma flat_of_flat_tensorProduct_of_injective_of_isSemiprimaryRing
    {R : Type*} [CommRing R] [IsSemiprimaryRing R] (S : Type*) [CommRing S] [Algebra R S]
    {M : Type*} [AddCommGroup M] [Module R M]
    (hRS : Function.Injective (algebraMap R S)) (hS : Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M :=
  have hJ := (isSemiprimaryRing_iff R).mp inferInstance
  -- a class-valued `have`, so that `R ⧸ Ring.jacobson R` is semisimple for instance search
  have := hJ.1
  Module.Flat.of_flat_quotient_of_flat_tensorProduct_of_isNilpotent_of_injective
    (Ring.jacobson R) hJ.2 hRS (flat_of_isSemisimpleRing _ _) hS

/-- Over an Artinian ring `R`, a module `M` is flat as soon as `R → S` is injective and some base
change `N` of `M` to `S` is flat over `S`. -/
@[ega "IV 11.4.11" "special case", ega "IV 11.4.3" "special case"]
public theorem solution {R : Type*} [CommRing R] [IsArtinianRing R]
    (S : Type*) [CommRing S] [Algebra R S] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (hRS : Function.Injective (algebraMap R S)) :
    Module.Flat R M :=
  flat_of_flat_tensorProduct_of_injective_of_isSemiprimaryRing S hRS
    (Module.Flat.of_linearEquiv hf.equiv)

end Stacks.Flatness.ArtinianDescent

/-!
# Flatness descends along an injective ring map out of an Artinian ring

Let `R → S` be a map of commutative rings with `R` Artinian, let `M` be an `R`-module and let `N`
be the base change of `M` to `S`. If `R → S` is injective and `N` is flat over `S`, then `M` is
flat over `R`. So flatness of a module can be tested after a base change that is merely injective,
provided the base ring is Artinian; no flatness of `R → S` itself is needed, in contrast with
faithfully flat descent (`Module.Flat.of_flat_tensorProduct`).

The source proves it in two ways, and the first is short. Let `J` be the Jacobson radical of `R`.
For `R` Artinian `J` is nilpotent and `R ⧸ J` is a finite product of fields, so every
`R ⧸ J`-module is flat, `M ⧸ JM` in particular; the local criterion for flatness along an injective
ring map (Stacks 051J: `J` nilpotent, `R → S` injective, `M/JM` flat over `R ⧸ J` and `S ⊗_R M`
flat over `S` imply `M` flat) then gives the conclusion. The second proof decomposes `R` into local
Artinian factors and, in the local case, lifts a basis of `M ⧸ 𝔪M` to a family generating `M`
(Nakayama) that is a basis of `S ⊗_R M` over `S` (Stacks 051H), injectivity of `R → S` ruling out a
nontrivial `R`-relation among its members.

## Main results

* `Module.Flat.of_flat_baseChange_of_injective`: over an Artinian ring `R`, a module `M` is flat as
  soon as `R → S` is injective and some base change of `M` to `S` is flat over `S`.

## Implementation notes

The source's module `M ⊗_R S` is replaced by an arbitrary `S`-module `N` together with an
`R`-linear `f : M →ₗ[R] N` satisfying `IsBaseChange S f`, which is Mathlib's spelling of "`N` is
the base change of `M` along `R → S`", pinned by the universal property rather than by the
construction. This is the shape of the ascent statement `Module.Flat.isBaseChange`, it is strictly
more general than the concrete form, and it specialises to the source's wording by
`TensorProduct.isBaseChange R M S : IsBaseChange S (TensorProduct.mk R S M 1)`, whose target is
`S ⊗[R] M` — Mathlib writes the base change with the scalars on the left, where the source writes
`M ⊗_R S`.

Injectivity is stated as `Function.Injective (algebraMap R S)`, the source's hypothesis (2) read on
the canonical map of the algebra structure; a caller with a `FaithfulSMul R S` instance supplies it
by `FaithfulSMul.algebraMap_injective R S`.

Generality deliberately not taken. Only two consequences of `IsArtinianRing R` are used: the
Jacobson radical `J` of `R` is nilpotent, and every `R ⧸ J`-module is flat. A commutative ring with
`J` nilpotent and `R ⧸ J` semisimple need not be Artinian — `k[x₁, x₂, …] ⧸ (xᵢxⱼ)` is local with
`𝔪 ^ 2 = 0` and `R ⧸ 𝔪 = k`, yet has an infinite descending chain of ideals inside `𝔪` — so the
weakening is strict and the statement below is not the most general one true. It is left out
because the general statement is Stacks 051J, a separate tag stated for an arbitrary nilpotent
ideal `I` with `M/IM` flat over `R ⧸ I` as a hypothesis: 051L is exactly the instance `I = J` of
051J in which the Artinian hypothesis discharges that flatness hypothesis, and it is the Artinian
hypothesis that makes it discharge.

Faithfulness. (1) No hypothesis is dead. `IsArtinianRing R`: for `R = ℤ`, `S = ℚ` and `M = ℤ ⧸ 2ℤ`
the map is injective and `ℚ ⊗_ℤ M = 0` is flat, while `M` is not flat over `ℤ`. Injectivity: for
`R = k[x] ⧸ (x ^ 2)`, `S = R ⧸ (x) = k` and `M = R ⧸ (x)` the base change `k ⊗_R M = k` is flat
over `k`, while `M` is not flat over the local Artinian `R`, not being free. Flatness of `N`: for
`S = R` and `M = R ⧸ (x)` over the same `R` it fails together with the conclusion. (2) The scalars
and base are the source's: flatness of `N` is over `S`, the conclusion is flatness of `M` over `R`,
and the `R`-action on `N` is the restriction of the `S`-action along `R → S`, which is what
`IsScalarTower R S N` says; nothing is localised. (3) The maps the source names are pinned: the
ring map is `algebraMap R S`, and the base change `M → M ⊗_R S` is the given `f`, pinned by
`IsBaseChange S f` up to the unique `S`-isomorphism with `S ⊗[R] M`. (4) The instantiation is not
degenerate: for `R = k[x] ⧸ (x ^ 2)`, `S = R[y]` and `M = R ⊕ R ^ (ℕ)` all three hypotheses hold
and the conclusion is true, while for the same `R` and `S` and `M = R ⧸ (x)` the flatness
hypothesis and the conclusion both fail, so neither side is automatic.

## References

* [Stacks Project, Tag 051L](https://stacks.math.columbia.edu/tag/051L)
-/

namespace Module.Flat

/-- **Stacks 051L**: flatness descends along an injective ring map whose source is Artinian. Let
`R → S` be a map of commutative rings with `R` Artinian and `algebraMap R S` injective, let `M` be
an `R`-module and let `f : M →ₗ[R] N` exhibit `N` as the base change of `M` to `S`, for instance
`N = S ⊗[R] M` with `f = TensorProduct.mk R S M 1`. If `N` is flat over `S`, then `M` is flat over
`R`. Compare `Module.Flat.of_flat_tensorProduct`, where `R → S` is faithfully flat instead. -/
@[stacks 051L "The source's `M ⊗_R S` is an arbitrary base change `f : M →ₗ[R] N` with
`IsBaseChange S f`, which specialises to it by `TensorProduct.isBaseChange`; injectivity of the
ring map is injectivity of `algebraMap R S`. See the module docstring."]
public theorem of_flat_baseChange_of_injective {R : Type*} [CommRing R] [IsArtinianRing R]
    (S : Type*) [CommRing S] [Algebra R S] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (hRS : Function.Injective (algebraMap R S)) :
    Module.Flat R M :=
      by exact Stacks.Flatness.ArtinianDescent.solution (f := f) S N hf hRS

end Module.Flat
