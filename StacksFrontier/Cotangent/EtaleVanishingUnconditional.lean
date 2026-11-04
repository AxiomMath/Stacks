module

public import StacksFrontier.Cotangent.EtaleVanishing
public import StacksFrontier.Cotangent.Triangle.ProductDescent

/-!
# Lemmas 08R1 and 08R2 with the fundamental triangle supplied

`StacksFrontier.Cotangent.DiagonalVanishing` and `StacksFrontier.Cotangent.EtaleVanishing` prove
[Stacks, Tag 08R1] and items (1) and (5) of [Stacks, Tag 08R2] for a distinguished triangle on
the three vertices of the display 92.7.0.1 of the diagonal tower `B → B ⊗_A B → B` given as a
parameter `hT`, those files being upstream of Proposition 08QX. This file supplies that triangle
from Proposition 08QX, `CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`, which holds for arbitrary ring maps; so the
statements here take exactly the source's hypotheses.

## Main results

* `CommAlgCat.isScalarTower_diagonalAlgebra`: `B → B ⊗_A B → B` is a tower of rings, the
  composite of `b ↦ b ⊗ 1` with the multiplication being the identity.
* `CommAlgCat.isZero_cotangentComplexDerived_of_torIndependent_unconditional`: **[Stacks, Tag
  08R1]**.
* `CommAlgCat.isZero_cotangentComplexDerived_of_weaklyEtale_unconditional`: **[Stacks, Tag 08R2]
  item (1)**.
* `CommAlgCat.isZero_cotangentComplexDerived_of_etale_unconditional`: **[Stacks, Tag 08R2] item
  (5)**.

## References

* [Stacks Project, Tag 08R1](https://stacks.math.columbia.edu/tag/08R1)
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), the fundamental
  triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

attribute [local instance] diagonalAlgebra

section Vanishing

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- The diagonal tower `B → B ⊗_A B → B` is a tower of rings: the composite of `b ↦ b ⊗ 1` with
the multiplication map is the identity. `CommAlgCat.diagonalAlgebra` supplies the algebra
structure on `B` over `B ⊗_A B` but nothing supplies the tower condition. -/
theorem isScalarTower_diagonalAlgebra : IsScalarTower B (B ⊗[A] B) B :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun b => by
    rw [RingHom.comp_apply, algebraMap_diagonalAlgebra]; simp).symm

/-- **[Stacks, Tag 08R1].** Let `A → B` be a ring map such that `Tor^A_i(B, B) = 0` for `i > 0`
and such that `L_{B/(B ⊗_A B)} = 0`. Then `L_{B/A} = 0` in `D(B)`.

This is `CommAlgCat.isZero_cotangentComplexDerived_of_torIndependent` at the distinguished
triangle of the tower `B → B ⊗_A B → B` that Proposition 08QX,
`CommAlgCat.productFundamentalTriangle_distinguished`, provides. -/
@[stacks 08R1 "the lemma in full, with NOTHING carried: the distinguished triangle of the tower \
`B → B ⊗_A B → B` is Proposition 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`, which holds for arbitrary ring maps and \
so covers the multiplication `B ⊗_A B → B` even though it is surjective rather than injective. \
BOTH hypotheses of the source are used: the vanishing of the higher `Tor^A_i(B, B)` is `hTor`, \
consumed by Stacks 08QQ (`CommAlgCat.derivedCotangentComplexBaseChangeIso`) in identifying the \
first vertex of the triangle with `L_{B/A}`, and `L_{B/(B ⊗_A B)} = 0` is `hCot`, the vanishing \
of the third vertex. The `B ⊗_A B`-algebra structure on `B` is the multiplication map, \
`CommAlgCat.diagonalAlgebra`"]
theorem isZero_cotangentComplexDerived_of_torIndependent_unconditional
    (hTor : RingTheory.TorIndependence.TorIndependent A B (B : Type u))
    (hCot : IsZero (fundamentalVertex₃.{u, u} (B ⊗[A] B) B)) :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)) := by
  have := isScalarTower_diagonalAlgebra A B
  obtain ⟨_, _, _, hT⟩ := exists_distTriang_fundamentalVertex.{u} B (B ⊗[A] B) B
  exact isZero_cotangentComplexDerived_of_torIndependent A B hTor hT hCot

/-- **[Stacks, Tag 08R2] item (1).** Let `A → B` be weakly étale: `A → B` flat and the
multiplication map `B ⊗_A B → B` flat. Then `L_{B/A} = 0` in `D(B)`.

This is `CommAlgCat.isZero_cotangentComplexDerived_of_weaklyEtale` at the distinguished triangle
of the tower `B → B ⊗_A B → B` that Proposition 08QX provides. -/
@[stacks 08R2 "item (1) of the lemma, `A → B` weakly étale — `Module.Flat A B` together with \
flatness of the multiplication map `B ⊗_A B → B`, which is Mathlib's `Algebra.WeaklyEtale`. \
NOTHING is carried: the distinguished triangle of the tower `B → B ⊗_A B → B` is Proposition \
08QX, `CommAlgCat.productFundamentalTriangle_distinguished`. Weak étaleness is NOT dead: \
`Module.Flat A B` supplies the Tor-independence hypothesis of Stacks 08R1, and flatness of the \
multiplication map supplies the vanishing of `L_{B/(B ⊗_A B)}` through item (2)"]
theorem isZero_cotangentComplexDerived_of_weaklyEtale_unconditional [Algebra.WeaklyEtale A B] :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)) := by
  have := isScalarTower_diagonalAlgebra A B
  obtain ⟨_, _, _, hT⟩ := exists_distTriang_fundamentalVertex.{u} B (B ⊗[A] B) B
  exact isZero_cotangentComplexDerived_of_weaklyEtale A B hT

/-- **[Stacks, Tag 08R2] item (5).** If `A → B` is étale then `L_{B/A} = 0` in `D(B)`.

An étale algebra is weakly étale, so this is the instance of item (1). -/
@[stacks 08R2 "item (5) of the lemma, `A → B` étale, obtained as the instance of item (1) along \
Mathlib's instance `Algebra.Etale → Algebra.WeaklyEtale`. NOTHING is carried, as in item (1). \
Étaleness is load-bearing, being the only source of the two flatness facts item (1) consumes"]
theorem isZero_cotangentComplexDerived_of_etale_unconditional [Algebra.Etale A B] :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)) :=
  isZero_cotangentComplexDerived_of_weaklyEtale_unconditional A B

end Vanishing

end CommAlgCat

end
