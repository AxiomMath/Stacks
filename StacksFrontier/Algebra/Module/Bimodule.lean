module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.GroupWithZero.Action.Defs

@[expose] public section



/-!
# Bimodules

Let `A` and `B` be semirings and let `N` be an additive commutative monoid that is both an
`A`-module and a `B`-module. Then `N` is an **`(A, B)`-bimodule** when the two multiplications
commute: `a • b • n = b • a • n` for all `a : A`, `b : B` and `n : N`. This is Stacks Definition
00D1, whose shorthand for the situation is `_A N_B`.

The two module structures are the data and the commuting of the actions is the one condition, so
an `(A, B)`-bimodule is a type carrying the three instances
`[Module A N] [Module B N] [SMulCommClass A B N]`. That last class *is* the condition, its field
`smul_comm` reading `a • b • n = b • a • n`, which is the source's `b (a n) = a (b n)` read from
the other side. The notion is thus Mathlib's `SMulCommClass`, on which this file records the tag.

The source phrases the condition through the multiplication operators: *multiplication by `a` and
multiplication by `b` commute*. Those operators are the additive endomorphisms
`DistribMulAction.toAddMonoidEnd A N a` and `DistribMulAction.toAddMonoidEnd B N b`, so the
condition in the source's own words is an equation in the semiring `AddMonoid.End N`, and that is
what this file states. It is the form in which the condition is used: two ring homomorphisms into
`AddMonoid.End N` whose images commute are one homomorphism out of the tensor product
(`Algebra.TensorProduct.liftEquiv`), which is why an `(A, B)`-bimodule is the same thing as a
module over `A ⊗[ℕ] B` (`TensorProduct.Algebra.module`).

The source writes the `B`-action on the right, `n b` for `b • n`, so that the compatibility reads
`(a x) b = a (x b)`. That is a notational convention, not a further condition. Where the right-hand
action is wanted as a genuine right action — for noncommutative `B`, where `n b := b • n` is
an action of `Bᵐᵒᵖ` and not of `B` — the notion is the same three instances at `Bᵐᵒᵖ`,
`[Module A N] [Module Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]`, whose compatibility
`a • op b • x = op b • a • x` is the source's `(a x) b = a (x b)`; this is the bimodule set-up of
`Mathlib/Algebra/Module/Bimodule.lean`.

## Main results

* `DistribMulAction.commute_toAddMonoidEnd`: in an `(A, B)`-bimodule the multiplication operators
  of `A` and of `B` commute in `AddMonoid.End N`.

## Implementation notes

*No predicate of our own.* The source's condition is `SMulCommClass A B N` — not up to an
equivalence, but with the same statement — so a bimodule predicate here would restate Mathlib and
send every user across a bridge; the notion is tagged where it lives, and the two module structures
stay in the binders, as they do for `Subbimodule` and for `TensorProduct.Algebra.module`.

*The operator form is a statement, the pointwise form is not.* `SMulCommClass` has
`a • b • n = b • a • n` as its one field, so a characterization of the class by that identity would
be `SMulCommClass.mk` and `SMulCommClass.smul_comm` glued into an `Iff`, which is why Mathlib
states no `smulCommClass_iff` and no `isScalarTower_iff` for the sibling mixin: a user verifies the
condition with `⟨h⟩` and consumes it with `smul_comm`. Commuting of the *operators* is not that
identity: it is an equality of bundled endomorphisms, and it is the shape the `Commute` hypothesis
of `Algebra.TensorProduct.liftEquiv` asks for.

*Stated for two distributive monoid actions.* Multiplication by `a` is an additive endomorphism as
soon as `A` is a monoid acting distributively, and commuting of operators needs no more, so the
statement holds well below the source's rings acting on an abelian group; it specializes to the
semirings acting on an additive commutative monoid of `TensorProduct.leftModule` — the setting in
which Lemma 00D2 uses this notion — where the operators are `Module.toAddMonoidEnd A N a` and
`Module.toAddMonoidEnd B N b`, the same endomorphisms. Additive inverses play no part.

*Bimodules are modules over `A ⊗[ℕ] B`.* For semirings `A`, `B` and an additive commutative monoid
`N` carrying the three instances, `TensorProduct.Algebra.module : Module (A ⊗[ℕ] B) N`; this is
Mathlib's reason for not making a bimodule a structure of its own, two-sided submodules being
submodules over that semiring.

*Not degenerate, and not vacuous.* `SMulCommClass R R M` holds for every module `M` over a
commutative semiring `R`, while for a ring `R` acting on itself by left multiplication on both
sides `SMulCommClass R R R` says `a * b = b * a`, so a noncommutative ring is not an
`(R, R)`-bimodule over itself in this way.

## References

* [StacksProject 00D1](https://stacks.math.columbia.edu/tag/00D1), Definition 10.12.13
  (`algebra-definition-bimodule`), in the section "Tensor products"; used in Lemma 00D2.
* `Mathlib/Algebra/Module/Bimodule.lean` for the same notion in the opposite spelling.
-/

/-- **Stacks 00D1.** In an `(A, B)`-bimodule multiplication by `a : A` and multiplication by
`b : B` commute, as additive endomorphisms of `N`: this is the source's own phrasing of the
bimodule condition, an equation in `AddMonoid.End N`.

The condition itself is `SMulCommClass A B N`, whose field `smul_comm` is the pointwise identity
`a • b • n = b • a • n`; commuting of the operators is the form consumed by
`Algebra.TensorProduct.liftEquiv`, hence by `TensorProduct.Algebra.module`. -/
@[stacks 00D1 "The source's condition, that multiplication by `a` and multiplication by `b` \
commute, at the level of the multiplication operators: an equation in `AddMonoid.End N`. The \
condition as a class on the two actions is `SMulCommClass`, tagged below."]
public theorem DistribMulAction.commute_toAddMonoidEnd {A B N : Type*} [Monoid A] [Monoid B]
    [AddMonoid N] [DistribMulAction A N] [DistribMulAction B N] [SMulCommClass A B N] (a : A)
    (b : B) :
    Commute (DistribMulAction.toAddMonoidEnd A N a) (DistribMulAction.toAddMonoidEnd B N b) := by
  ext n; exact smul_comm a b n

/- The notion itself: an `(A, B)`-bimodule is a type with `[Module A N] [Module B N]
[SMulCommClass A B N]`, the source's data being the two module structures and its one condition
being this class. -/
add_to_stacks 00D1 "An `(A, B)`-bimodule is a type with `[Module A N] [Module B N] \
[SMulCommClass A B N]`: the source's data is the two module structures, and its one condition, \
that the actions commute, is this class, `smul_comm` being `a • b • n = b • a • n`, the source's \
`b (a n) = a (b n)` read from the other side. The class asks only for two `SMul`s, so this covers \
semirings acting on an additive commutative monoid as well as the source's rings acting on an \
abelian group. Writing the `B`-action on the right is the source's notation, not a further \
condition; the genuine right-action form is this class at `Bᵐᵒᵖ`, the bimodule set-up of \
`Mathlib/Algebra/Module/Bimodule.lean`." SMulCommClass

end
