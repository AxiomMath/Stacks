module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProduct
public import StacksCore.Tactic.StacksAttribute

/-!
# Associativity of the intersection product

Let `X` be smooth over a field and let `Y`, `Z` and `W` be locally of finite type over `X`. The
intersection product of Stacks 0FC0, formalized as `Stacks.Chow.intersectionProduct`, sends
`α ∈ CH_n(Y)` and `β ∈ CH_m(Z)` to `α · β = Δ^!(α × β) ∈ CH_{n + m - d}(Y ×_X Z)`. Stacks 0FC1
asserts that this product is associative:

`(α · β) · γ = α · (β · γ)` in `CH_*(Y ×_X Z ×_X W)`.

The two sides do not live in the same group on the nose. The left-hand side lies over
`(Y ×_X Z) ×_X W` in degree `(n + m - d) + l - d` and the right-hand side over
`Y ×_X (Z ×_X W)` in degree `n + (m + l - d) - d`, so the equation is read after the canonical
associator of the triple fibre product and after matching the two degrees. This file supplies
both identifications and states the equation they make well formed.

## Main definitions

* `Stacks.Chow.IsAssociativeIntersectionProduct`: the assertion of Stacks 0FC1, that the two
  bracketings of the triple intersection product agree once transported to a common group.

## Main results

* `Stacks.Chow.tripleProductAssoc_hom_comp_structureMorphism`: the associator
  `(Y ×_X Z) ×_X W ≅ Y ×_X (Z ×_X W)` is a morphism of schemes over the base of the situation,
  which is what lets the left-hand side be pushed forward to where the right-hand side lives.
* `Stacks.Chow.intersectionProductAssocDegree`: the two degrees agree.
* `Stacks.Chow.isAssociativeIntersectionProduct_zero`: the equation holds when the Gysin class
  of the diagonal vanishes. This is the degenerate case, and it witnesses that the statement is
  correctly oriented: both transports land on the group the right-hand side lives in, so the
  two sides are genuinely comparable there.

## Implementation notes

Only the *statement* of Stacks 0FC1 is formalized here, together with the geometry and the
degree bookkeeping that make it well formed, and the degenerate case of a vanishing diagonal
class. The equation itself is **not** proved. The source's proof is a chain of five equalities

`(α · β) · γ = Δ^!(Δ₁₂^!((α × β) × γ)) = Δ^!(Δ₂₃^!((α × β) × γ))`
`           = Δ^!(Δ₂₃^!(α × (β × γ))) = Δ^!(α × Δ^!(β × γ)) = α · (β · γ)`

and of its four cited inputs only two are available in this repository:

* Stacks 0FBZ, associativity of the exterior product, is the fourth step and *is* available, as
  `Stacks.Chow.chowExteriorProduct_assoc`.
* Stacks 0F9Z, restriction of a bivariant class, is available as
  `Stacks.Chow.bivariantRestriction`. In this formalization it is largely free: the `cap` field
  of `Stacks.Chow.BivariantClass` is indexed by an arbitrary test morphism, so the source's
  `Δ₁₂^! ∩ -` and `Δ₂₃^! ∩ -` are cap operations of `Δ^!` itself against two different test
  morphisms of the triple product, and no triple self-product `X ×_k X ×_k X` is needed.
* Stacks 0FBY, the commutation `α × (c ∩ β) = c ∩ (α × β)` of the exterior product with a
  bivariant class, is the first and penultimate step. It has **no carrier**: there is no lemma
  anywhere in this repository relating the exterior product to a bivariant cap, nor to proper
  pushforward, which the first step also needs in order to move the pushforward inside `α · β`
  out through `× γ`.
* Stacks 0FBP, the commutation of the Gysin class of a closed subscheme with an arbitrary
  bivariant class, is the second step. It has **no carrier** either. The general notion it
  would inhabit does exist, as `Stacks.Chow.BivariantCommute` of
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting` (Stacks 0FA2), and the single
  commuting instance that is proved,
  `Stacks.Chow.bivariantCommute_flatPullbackBivariantClass`, records in its own key text that
  the `i^!` half is Stacks 0FBP and that it has no carrier here.

Neither missing step is carried as a hypothesis. Doing so would be sound in principle — the
first and penultimate steps are each a statement about *one* bivariant class and the exterior
product, and the second step is a statement about two bivariant classes and no product at all,
whereas associativity concerns three Chow classes and two caps of `Δ^!`, so none of them is the
conclusion in disguise. The obstruction is different: stating either step in the shape the
chain uses requires identifying the pullback of the diagonal along a test morphism of the
triple product with `(Y ×_X Z) ×_k W`, and that identification is not available here. Carrying
it alongside the step would amount to carrying the whole chain, and so the conclusion, outright.

No `@[stacks 0FC1]` attribute is placed anywhere in this file. A tag attribute stands for the
real statement, never for a weakened or special-cased version of it, and this file offers only
the statement itself (which asserts nothing), the geometry and degree bookkeeping that make it
well formed, and the degenerate case of a vanishing diagonal class. The associativity equation
in the generality Stacks 0FC1 asserts is left open, and nothing here should be read as covering
it.

The associator is `Stacks.Chow.tripleProductAssoc` of
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity`, which is stated over an
arbitrary base scheme and is therefore available for fibre products over `X` and not only over
`C.S`. The degree transport is `Stacks.Chow.chowGroupDegreeEquiv`; the structure-morphism
transports are `Stacks.Chow.chowGroupCongr`, needed because the product of Stacks 0FC0 is
indexed by `pr ≫ (a ≫ sX)` while feeding it back in as one of its own arguments presents the
same morphism as `(pr ≫ a) ≫ sX`.

## References

* [Stacks Project, Tag 0FC1](https://stacks.math.columbia.edu/tag/0FC1)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
* [Stacks Project, Tag 0FBZ](https://stacks.math.columbia.edu/tag/0FBZ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The geometry and the degrees of the two sides -/

section Geometry

variable (C : Stacks.Chow.ChowSituation.{u}) {X Y Z W : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X)
  [LocallyOfFiniteType b] (g : W ⟶ X) [LocallyOfFiniteType g]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType a] [LocallyOfFiniteType b]
  [LocallyOfFiniteType g] in
/-- The associator `(Y ×_X Z) ×_X W ≅ Y ×_X (Z ×_X W)` of a triple fibre product over `X` is a
morphism of schemes over the base of the situation: it carries the structure morphism of the
right-bracketed product to the structure morphism of the left-bracketed one. This is what lets
the left-hand side of Stacks 0FC1 be pushed forward into the Chow group that the right-hand
side lives in. -/
theorem tripleProductAssoc_hom_comp_structureMorphism :
    (tripleProductAssoc a b g).hom ≫
        (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX)) =
      pullback.fst (pullback.fst a b ≫ a) g ≫ ((pullback.fst a b ≫ a) ≫ sX) := by
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫ sX) (tripleProductAssoc_hom_comp_base a b g)

/-- The two sides of Stacks 0FC1 sit in the same degree: bracketing the triple product to the
left gives `(n + m - d) + l - d` and to the right gives `n + (m + l - d) - d`. -/
theorem intersectionProductAssocDegree (n m l d : ℤ) :
    (n + m - d) + l - d = n + (m + l - d) - d := by ring

end Geometry

/-! ### The statement of Stacks 0FC1 -/

section Associativity

variable (C : Stacks.Chow.ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S]
  [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {X Y Z W : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]
  (g : W ⟶ X) [LocallyOfFiniteType g] (d : ℤ)
  (Δ : BivariantClass C G sX (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) d)
  (n m l : ℤ) (hpp : ProperPushforwardDescends C)

/-- The product `α · β` of Stacks 0FC0, presented on the structure morphism
`(pr_Y ≫ a) ≫ sX` of `Y ×_X Z` rather than on `pr_Y ≫ (a ≫ sX)`. The two are the same
morphism and not the same term, and this is the presentation in which `Y ×_X Z` can be fed back
into the product as one of its own factors. -/
def intersectionProductReassoc (α : chowGroup C (a ≫ sX) n) (β : chowGroup C (b ≫ sX) m) :
    chowGroup C ((pullback.fst a b ≫ a) ≫ sX) (n + m - d) :=
  chowGroupCongr C (Category.assoc (pullback.fst a b) a sX).symm (n + m - d)
    (intersectionProduct C hδ G sX a b d Δ n m (TensorProduct.tmul ℤ α β))

/-- **Stacks Project, Tag 0FC1.** Associativity of the intersection product of Stacks 0FC0:
the two bracketings of the triple product agree, once the left-bracketed side — which lives on
`(Y ×_X Z) ×_X W` in degree `(n + m - d) + l - d` — is pushed forward along the associator of
the triple fibre product and its degree is matched with that of the right-bracketed side.

This is the equation asserted by the source. It is stated, not proved; see the implementation
notes of this file for the two cited inputs, Stacks 0FBP and Stacks 0FBY, that have no carrier
in this repository. -/
/-
No `@[stacks 0FC1]` attribute is placed on this definition, deliberately. The entire content of
Stacks 0FC1 is the associativity *equation*, and this is a `Prop`-valued definition that names
that equation without asserting it; nothing below proves it. Tagging it would record coverage of
the tag while proving none of it. The two cited inputs the proof needs, Stacks 0FBP and Stacks
0FBY, have no carrier in this repository, so the equation is stated here as a named predicate for
a later proof to discharge. No declaration in this file carries `@[stacks 0FC1]`: the degenerate
case proved below is a special case of the equation, and a tag attribute stands for the real
statement rather than for a special case of it.
-/
def IsAssociativeIntersectionProduct : Prop :=
  ∀ (α : chowGroup C (a ≫ sX) n) (β : chowGroup C (b ≫ sX) m)
    (γ : chowGroup C (g ≫ sX) l),
    chowGroupDegreeEquiv C (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX))
        (intersectionProductAssocDegree n m l d)
        (properChowPushforward C
          (pullback.fst (pullback.fst a b ≫ a) g ≫ ((pullback.fst a b ≫ a) ≫ sX))
          (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX))
          (tripleProductAssoc a b g).hom
          (tripleProductAssoc_hom_comp_structureMorphism C sX a b g)
          ((n + m - d) + l - d) (hpp _ _ _ _ _)
          (intersectionProduct C hδ G sX (pullback.fst a b ≫ a) g d Δ (n + m - d) l
            (TensorProduct.tmul ℤ
              (intersectionProductReassoc C hδ G sX a b d Δ n m α β) γ))) =
      intersectionProduct C hδ G sX a (pullback.fst b g ≫ b) d Δ n (m + l - d)
        (TensorProduct.tmul ℤ α
          (intersectionProductReassoc C hδ G sX b g d Δ m l β γ))

/-- **Stacks Project, Tag 0FC1.** The degenerate case: when the Gysin class of the diagonal
vanishes, every product built from it vanishes, and the associativity equation holds.

This carries no mathematical content about the diagonal, but it does confirm that the equation
of `Stacks.Chow.IsAssociativeIntersectionProduct` is correctly formed: the associator
pushforward and the degree transport really do land the left-bracketed side in the group that
the right-bracketed side inhabits, so that the two are comparable and the assertion is not
vacuous for want of a common target. -/
/-
No `@[stacks 0FC1]` attribute is placed here either, and the reason is worth recording. This
theorem is the associativity equation with the diagonal class instantiated to `0`, i.e. a
special case of the tag's statement rather than the statement. A tag attribute stands for the
real statement, never for a weakened or special-cased version of it, so neither this theorem nor
the `Prop`-valued `IsAssociativeIntersectionProduct` above may carry it: the first is a special
case, the second asserts nothing. What this file contributes to Stacks 0FC1 is the geometry and
the degree bookkeeping that make the equation well formed, plus this degenerate case as a
witness that both transports land in the group the right-bracketed side inhabits. The equation
itself awaits Stacks 0FBP and Stacks 0FBY, neither of which has a carrier here.
-/
theorem isAssociativeIntersectionProduct_zero :
    IsAssociativeIntersectionProduct C hδ G sX a b g d 0 n m l hpp := by
  intro α β γ
  simp only [intersectionProductReassoc, intersectionProduct_apply, BivariantClass.zero_cap,
    map_zero]

end Associativity

end Stacks.Chow

end
