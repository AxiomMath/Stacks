module

public import StacksFrontier.Cotangent.Localization
public import StacksFrontier.Cotangent.Triangle.ProductDescent

/-!
# Lemma 08SF with the fundamental triangle supplied

`StacksFrontier.Cotangent.Localization` proves [Stacks, Tag 08SF] for a distinguished triangle on
the vertices of the display 92.7.0.1 of the tower `A → B → T⁻¹B` given as a parameter, that file
being upstream of Proposition 08QX. This file supplies the triangle from Proposition 08QX,
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`, which holds for arbitrary ring maps, and reads
the lemma both with the derived base change `⊗^𝐋_B` and with the degreewise one `⊗_B` the source
writes.

## Main results

* `CommAlgCat.nonempty_cotangentComplexDerivedBaseChange_iso_localization_unconditional`:
  **[Stacks, Tag 08SF]**, with the base change read as the derived one `⊗^𝐋_B`.
* `CommAlgCat.nonempty_extendScalars_cotangentComplex_iso_localization`: **[Stacks, Tag 08SF]**
  again, with the base change read as the *degreewise* one `⊗_B`, which is how the source writes
  it. The two readings agree because `L_{B/A}` is a complex of free `B`-modules vanishing in
  positive degrees, so it computes its own derived base change.

## The proof

The source proves the lemma in two steps, both of which are taken here.

* `L_{T⁻¹B/A} = L_{B/A} ⊗^𝐋_B T⁻¹B`, which is [Stacks, Tag 08R3] for the tower
  `A → B → T⁻¹B`. The distinguished triangle of that tower is
  `CommAlgCat.exists_distTriang_fundamentalVertex`, the existential form of Proposition 08QX.
  Its third vertex `L_{T⁻¹B/B}` vanishes by
  `CommAlgCat.isZero_cotangentComplexDerived_localization`, because a localization is flat and
  an epimorphism of rings, which is item (2) of [Stacks, Tag 08R2].
* `L_{T⁻¹B/A} = L_{T⁻¹B/S⁻¹A}`, which the source takes from [Stacks, Tag 08QZ] and which is
  `CommAlgCat.nonempty_cotangentComplexDerived_iso_localizationBase`, obtained from
  [Stacks, Tag 08QQ] applied to the pushout square `A → S⁻¹A`, `T⁻¹B → T⁻¹B`.

These two steps are combined by
`CommAlgCat.nonempty_cotangentComplexDerivedBaseChange_iso_localization` of
`StacksFrontier.Cotangent.Localization`, which takes the triangle as an argument because that file
is upstream of Proposition 08QX. The main theorems of this file pass it that triangle.

## References

* [Stacks Project, Tag 08SF](https://stacks.math.columbia.edu/tag/08SF)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), the fundamental
  triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

section Localization

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (S : Submonoid A) (T : Submonoid B)
  (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalization S A']
  (B' : Type u) [CommRing B'] [Algebra B B'] [IsLocalization T B']
  [Algebra A B'] [IsScalarTower A B B'] [Algebra A' B'] [IsScalarTower A A' B']

/-- **[Stacks, Tag 08SF].** Let `A → B` be a ring map and let `S ⊆ A` and `T ⊆ B` be
multiplicative subsets such that `S` maps into `T`. Then

`L_{T⁻¹B/S⁻¹A} = L_{B/A} ⊗^𝐋_B T⁻¹B`

in `D(T⁻¹B)`.

This is `CommAlgCat.nonempty_cotangentComplexDerivedBaseChange_iso_localization` applied to the
distinguished triangle of the tower `A → B → T⁻¹B` from Proposition 08QX,
`CommAlgCat.exists_distTriang_fundamentalVertex`. Every other input is proved as well:
`L_{T⁻¹B/B} = 0` is `CommAlgCat.isZero_cotangentComplexDerived_localization`, and
`L_{T⁻¹B/A} ≅ L_{T⁻¹B/S⁻¹A}` is
`CommAlgCat.nonempty_cotangentComplexDerived_iso_localizationBase`. -/
@[stacks 08SF "the lemma in full, with NOTHING carried. The distinguished fundamental triangle \
of the tower `A → B → T⁻¹B` is Proposition 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`. Everything else is proved outright too: \
`L_{T⁻¹B/B} = 0` is `isZero_cotangentComplexDerived_localization` from Tag 08R2 item \
(2), and `L_{T⁻¹B/A} ≅ L_{T⁻¹B/S⁻¹A}` is `nonempty_cotangentComplexDerived_iso_localizationBase` \
from Tag 08QQ at the identity base change, at the localization square. The source's \
equality is read as an isomorphism in D(T⁻¹B) without naming the arrow, as Tag 08R3 \
and Tag 08QQ do, no canonical arrow being available to pin. All four rings are in a single \
universe, which is the generality of Tag 08QQ"]
theorem nonempty_cotangentComplexDerivedBaseChange_iso_localization_unconditional
    (hST : ∀ s ∈ S, algebraMap A B s ∈ T) :
    Nonempty (cotangentComplexDerivedBaseChange.{u, u} A (CommAlgCat.of A B) B' ≅
      cotangentComplexDerived.{u, u} A' (CommAlgCat.of A' B')) := by
  obtain ⟨_, _, _, hT⟩ := exists_distTriang_fundamentalVertex.{u} A B B'
  exact nonempty_cotangentComplexDerivedBaseChange_iso_localization A B S T A' B' hST hT

/-- **[Stacks, Tag 08SF], with the base change read degreewise.** Let `A → B` be a ring map and
let `S ⊆ A` and `T ⊆ B` be multiplicative subsets such that `S` maps into `T`. Then

`L_{T⁻¹B/S⁻¹A} = L_{B/A} ⊗_B T⁻¹B`

in `D(T⁻¹B)`, where the right-hand side is the *degreewise* extension of scalars along
`B → T⁻¹B` — which is the tensor product the source writes.

This is `CommAlgCat.nonempty_cotangentComplexDerivedBaseChange_iso_localization_unconditional`
composed with the identification of the derived base change of `L_{B/A}` with the degreewise
one, `CommAlgCat.nonempty_derivedExtensionScalars_cotangentComplex_iso`. That identification
needs no hypothesis on `B → T⁻¹B`: `L_{B/A}` is a complex of free `B`-modules vanishing in
positive degrees, so it already computes its own derived base change. -/
@[stacks 08SF "the lemma in full, with NOTHING carried, reading the source's `⊗_B T⁻¹B` as the \
DEGREEWISE extension of scalars along `B → T⁻¹B` — which is the tensor product the source \
writes, the derived reading being \
`nonempty_cotangentComplexDerivedBaseChange_iso_localization_unconditional`. The two differ \
only by `nonempty_derivedExtensionScalars_cotangentComplex_iso`, which identifies the derived \
base change of `L_{B/A}` with the degreewise one and assumes nothing of `B → T⁻¹B`, `L_{B/A}` \
being a complex of free `B`-modules vanishing in positive degrees. The source's equality is \
read as an isomorphism in D(T⁻¹B) without naming the arrow, as Tag 08R3 and Tag 08QQ \
do, no canonical arrow being available to pin. All four rings are in a single universe, which \
is the generality of Tag 08QQ"]
theorem nonempty_extendScalars_cotangentComplex_iso_localization
    (hST : ∀ s ∈ S, algebraMap A B s ∈ T) :
    Nonempty (DerivedCategory.Q.obj (cotangentComplex A' (CommAlgCat.of A' B')) ≅
      DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{0, u, u}
        (algebraMap B B')).obj (cotangentComplex A (CommAlgCat.of A B)))) := by
  obtain ⟨e₁⟩ :=
    nonempty_cotangentComplexDerivedBaseChange_iso_localization_unconditional A B S T A' B' hST
  obtain ⟨e₂⟩ := nonempty_derivedExtensionScalars_cotangentComplex_iso A B B'
  exact ⟨e₁.symm ≪≫ e₂⟩

end Localization

end CommAlgCat

end
