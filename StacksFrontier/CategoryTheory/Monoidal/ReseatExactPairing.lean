module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import StacksFrontier.CategoryTheory.Monoidal.Reseat
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# An exact pairing survives re-seating

`CategoryTheory.MonoidalCategory.reseat` moves a monoidal structure onto a prescribed tensor
bifunctor and a prescribed unit object, leaving the underlying category alone.  A library that
re-seats the same base structure twice — once onto each of two isomorphic tensor bifunctors —
ends up with two monoidal structures on one category, and a statement proved against one of them
is not a statement about the other.  This file moves an exact pairing (Categories, Definition
0FFP) between them.

The route is the one `CategoryTheory.MonoidalCategory.reseatMonoidal` already sets up: the
identity functor is monoidal **from** a re-seated structure **to** the base.  What was missing was
the other direction, and that is free — the identity functor is an equivalence, so
`CategoryTheory.Equivalence.inverseMonoidal` turns a monoidal structure on it around.  Composing
the two directions moves anything functorial between two re-seats of one base, and
`CategoryTheory.ExactPairing.map` is what makes an exact pairing such a thing.

## Main results

* `CategoryTheory.MonoidalCategory.reseatMonoidalSymm`: the identity functor is monoidal from
  the base structure to a re-seated one.
* `CategoryTheory.MonoidalCategory.exactPairingReseat`: an exact pairing for the base structure
  is one for a re-seated structure.
* `CategoryTheory.MonoidalCategory.exactPairingOfReseat`: and conversely.
* `CategoryTheory.MonoidalCategory.exactPairingReseatOfReseat`: an exact pairing transported
  between two re-seats of **one** base structure along **one** unit isomorphism.  This is the
  statement a library with two re-seated tensor products needs.

## Implementation notes

*Why the unit isomorphism has to be shared.*  `reseat e ε` and `reseat e' ε'` with `ε ≠ ε'` have
different unit **objects**, and an exact pairing is a statement about the unit object — the
coevaluation starts there.  Two re-seats with the same `ε` have the same unit by
`CategoryTheory.MonoidalCategory.tensorUnit_reseat`, so no transport of the pairing's objects is
needed and `CategoryTheory.exactPairingCongr` does not enter.  `exactPairingReseatOfReseat` is
therefore stated at a single `ε` and two tensor comparisons.

*Every application is by `@`.*  A re-seated structure is a `def`, not an instance, so each
statement below names both monoidal structures positionally; left to instance search the
elaborator would pick the ambient one on both sides and the statements would say nothing.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T T' : C ⥤ C ⥤ C} {U : C}

/-- **The identity functor is monoidal from the base structure to a re-seated one.**  This is
`CategoryTheory.MonoidalCategory.reseatMonoidal` run backwards, which costs nothing because the
identity functor is an equivalence: `CategoryTheory.Equivalence.inverseMonoidal` inverts a
monoidal structure on the functor of an equivalence. -/
@[instance_reducible]
def reseatMonoidalSymm (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @Functor.Monoidal C _ _ C _ (reseat e ε) (𝟭 C) :=
  @Equivalence.inverseMonoidal C _ (reseat e ε) C _ _ (Equivalence.refl) (reseatMonoidal e ε)

/-- **An exact pairing for the base structure is an exact pairing for a re-seated one.** -/
@[instance_reducible]
def exactPairingReseat (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X Y : C) [ExactPairing X Y] :
    @ExactPairing C _ (reseat e ε) X Y :=
  @ExactPairing.map C C _ _ _ (reseat e ε) (𝟭 C) (reseatMonoidalSymm e ε) X Y inferInstance

/-- **An exact pairing for a re-seated structure is an exact pairing for the base.** -/
@[instance_reducible]
def exactPairingOfReseat (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X Y : C)
    (p : @ExactPairing C _ (reseat e ε) X Y) : ExactPairing X Y :=
  @ExactPairing.map C C _ _ (reseat e ε) _ (𝟭 C) (reseatMonoidal e ε) X Y p

/-- **An exact pairing moves between two re-seats of one base structure.**  The two re-seats must
share the unit isomorphism `ε`, since an exact pairing is a statement about the unit object; they
may re-seat onto any two tensor bifunctors. -/
@[instance_reducible]
def exactPairingReseatOfReseat (e : curriedTensor C ≅ T) (e' : curriedTensor C ≅ T')
    (ε : 𝟙_ C ≅ U) (X Y : C) (p : @ExactPairing C _ (reseat e ε) X Y) :
    @ExactPairing C _ (reseat e' ε) X Y :=
  @exactPairingReseat C _ _ T' U e' ε X Y (exactPairingOfReseat e ε X Y p)

end CategoryTheory.MonoidalCategory

end
