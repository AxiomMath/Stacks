module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksCore.Tactic.StacksAttribute

/-!
# The composition of bivariant classes is bilinear

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes locally of finite type over `S`. Stacks 0B75 asserts that the
composition

  `A^p(X ⟶ Y) × A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)`

of `Stacks.Chow.bivariantComposite` is bilinear. Each identity is the corresponding one for the
characterization `Stacks.Chow.IsBivariantClassComposition` of Stacks 0FE0, read through the
uniqueness `Stacks.Chow.eq_of_isBivariantClassComposition`; the group structure on
`Stacks.Chow.BivariantClass` is the degreewise one.

## Main results

* `Stacks.Chow.bivariantComposite_add_left'`, `Stacks.Chow.bivariantComposite_add_right'`,
  `Stacks.Chow.bivariantComposite_neg_left`, `Stacks.Chow.bivariantComposite_neg_right`,
  `Stacks.Chow.bivariantComposite_zero_left`, `Stacks.Chow.bivariantComposite_zero_right` —
  the bilinearity of the composition.
* `Stacks.Chow.bivariantCompositeAddHomLeft`, `Stacks.Chow.bivariantCompositeAddHomRight` — the
  two partial maps as homomorphisms of groups, which is what delivers compatibility with finite
  sums and with integer multiples.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Bilinear

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p q : ℤ)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- Additivity of the composition in the first argument: `(a + a') ∘ b = a ∘ b + a' ∘ b`. -/
@[stacks 0B75 "the bilinearity of the composition, additivity in the first argument"]
theorem bivariantComposite_add_left' (a a' : BivariantClass C G sX sY f hf p)
    (b : BivariantClass C G sY sZ g hg q) :
    bivariantComposite C G sX sY sZ f g hf hg p q (a + a') b hgys hgysc =
      bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc +
        bivariantComposite C G sX sY sZ f g hf hg p q a' b hgys hgysc :=
  eq_of_isBivariantClassComposition (hpp := properPushforwardDescends C)
    (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q (a + a') b hgys
      hgysc)
    (IsBivariantClassComposition.add_left (hpp := properPushforwardDescends C)
      (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc)
      (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q a' b hgys hgysc))

/-- Additivity of the composition in the second argument: `a ∘ (b + b') = a ∘ b + a ∘ b'`. -/
@[stacks 0B75 "the bilinearity of the composition, additivity in the second argument"]
theorem bivariantComposite_add_right' (a : BivariantClass C G sX sY f hf p)
    (b b' : BivariantClass C G sY sZ g hg q) :
    bivariantComposite C G sX sY sZ f g hf hg p q a (b + b') hgys hgysc =
      bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc +
        bivariantComposite C G sX sY sZ f g hf hg p q a b' hgys hgysc :=
  eq_of_isBivariantClassComposition (hpp := properPushforwardDescends C)
    (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q a (b + b') hgys
      hgysc)
    (IsBivariantClassComposition.add_right (hpp := properPushforwardDescends C)
      (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc)
      (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q a b' hgys hgysc))

/-- The composition negates in its first argument: `(-a) ∘ b = -(a ∘ b)`. -/
@[stacks 0B75 "the bilinearity of the composition, negation in the first argument"]
theorem bivariantComposite_neg_left (a : BivariantClass C G sX sY f hf p)
    (b : BivariantClass C G sY sZ g hg q) :
    bivariantComposite C G sX sY sZ f g hf hg p q (-a) b hgys hgysc =
      -bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc :=
  eq_of_isBivariantClassComposition (hpp := properPushforwardDescends C)
    (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q (-a) b hgys hgysc)
    (IsBivariantClassComposition.neg_left (hpp := properPushforwardDescends C)
      (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc))

/-- The composition negates in its second argument: `a ∘ (-b) = -(a ∘ b)`. -/
@[stacks 0B75 "the bilinearity of the composition, negation in the second argument"]
theorem bivariantComposite_neg_right (a : BivariantClass C G sX sY f hf p)
    (b : BivariantClass C G sY sZ g hg q) :
    bivariantComposite C G sX sY sZ f g hf hg p q a (-b) hgys hgysc =
      -bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc :=
  eq_of_isBivariantClassComposition (hpp := properPushforwardDescends C)
    (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q a (-b) hgys hgysc)
    (IsBivariantClassComposition.neg_right (hpp := properPushforwardDescends C)
      (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc))

/-- The composite of the zero class with any class is zero. -/
@[stacks 0B75 "the bilinearity of the composition, the zero class on the left"]
theorem bivariantComposite_zero_left (b : BivariantClass C G sY sZ g hg q) :
    bivariantComposite C G sX sY sZ f g hf hg p q 0 b hgys hgysc = 0 :=
  eq_of_isBivariantClassComposition (hpp := properPushforwardDescends C)
    (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q 0 b hgys hgysc)
    (IsBivariantClassComposition.zero_left (hpp := properPushforwardDescends C))

/-- The composite of any class with the zero class is zero. -/
@[stacks 0B75 "the bilinearity of the composition, the zero class on the right"]
theorem bivariantComposite_zero_right (a : BivariantClass C G sX sY f hf p) :
    bivariantComposite C G sX sY sZ f g hf hg p q a 0 hgys hgysc = 0 :=
  eq_of_isBivariantClassComposition (hpp := properPushforwardDescends C)
    (isBivariantClassComposition_bivariantComposite C G sX sY sZ f g hf hg p q a 0 hgys hgysc)
    (IsBivariantClassComposition.zero_right (hpp := properPushforwardDescends C))

/-- Composition with a fixed class `b ∈ A^q(Y ⟶ Z)` on the right, as a homomorphism
`A^p(X ⟶ Y) ⟶ A^{p+q}(X ⟶ Z)` of groups. -/
@[stacks 0B75 "the bilinearity of the composition: the partial map in the first argument as a \
homomorphism of groups"]
def bivariantCompositeAddHomLeft (b : BivariantClass C G sY sZ g hg q) :
    BivariantClass C G sX sY f hf p →+
      BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q) where
  toFun a := bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc
  map_zero' := bivariantComposite_zero_left C G sX sY sZ f g hf hg p q hgys hgysc b
  map_add' a a' := bivariantComposite_add_left' C G sX sY sZ f g hf hg p q hgys hgysc a a' b

/-- Composition with a fixed class `a ∈ A^p(X ⟶ Y)` on the left, as a homomorphism
`A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)` of groups. -/
@[stacks 0B75 "the bilinearity of the composition: the partial map in the second argument as a \
homomorphism of groups"]
def bivariantCompositeAddHomRight (a : BivariantClass C G sX sY f hf p) :
    BivariantClass C G sY sZ g hg q →+
      BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q) where
  toFun b := bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc
  map_zero' := bivariantComposite_zero_right C G sX sY sZ f g hf hg p q hgys hgysc a
  map_add' b b' := bivariantComposite_add_right' C G sX sY sZ f g hf hg p q hgys hgysc a b b'

/-- The value of `Stacks.Chow.bivariantCompositeAddHomLeft` is the composite. -/
@[simp]
theorem bivariantCompositeAddHomLeft_apply (a : BivariantClass C G sX sY f hf p)
    (b : BivariantClass C G sY sZ g hg q) :
    bivariantCompositeAddHomLeft C G sX sY sZ f g hf hg p q hgys hgysc b a =
      bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc :=
  rfl

/-- The value of `Stacks.Chow.bivariantCompositeAddHomRight` is the composite. -/
@[simp]
theorem bivariantCompositeAddHomRight_apply (a : BivariantClass C G sX sY f hf p)
    (b : BivariantClass C G sY sZ g hg q) :
    bivariantCompositeAddHomRight C G sX sY sZ f g hf hg p q hgys hgysc a b =
      bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc :=
  rfl

end Bilinear

end Stacks.Chow

end
