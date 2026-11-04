module

public import StacksFrontier.Cotangent.EtaleVanishingUnconditional
public import StacksFrontier.Cotangent.Henselization

/-!
# Lemmas 08R2 (7), (8) and 08UN with the fundamental triangles supplied

`StacksFrontier.Cotangent.Henselization` proves items (7) and (8) of [Stacks, Tag 08R2] and the
identifications of [Stacks, Tag 08UN] for distinguished triangles on the vertices of the display
92.7.0.1 given as parameters: the family `CommAlgCat.HasEtaleDiagonalTriangle` of triangles of
the diagonal towers of étale algebras, and the triangles of the towers the identifications pass
through. That file is upstream of Proposition 08QX. This file supplies every one of those
triangles from Proposition 08QX, `CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`, which holds for arbitrary ring maps; so the
statements here take exactly the source's hypotheses.

## Main results

* `CommAlgCat.hasEtaleDiagonalTriangle`: the family `CommAlgCat.HasEtaleDiagonalTriangle R`
  holds for every ring `R`.
* `IsLocalRing.IsHenselization.isZero_cotangentComplexDerived_unconditional`: **[Stacks, Tag
  08R2] items (7) and (8)**.
* `CommAlgCat.nonempty_fundamentalVertex₂_iso_fundamentalVertex₃_henselization_unconditional`,
  `CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization_unconditional` and
  `CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₃_henselization_unconditional`:
  **[Stacks, Tag 08UN]**, its two equalities and the full chain.

## References

* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2)
* [Stacks Project, Tag 08UN](https://stacks.math.columbia.edu/tag/08UN)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), the fundamental
  triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

attribute [local instance] diagonalAlgebra

/-- **Proposition 08QX at the diagonal towers of étale algebras.** For every ring `R` the family
`CommAlgCat.HasEtaleDiagonalTriangle R` holds: it is Proposition 08QX,
`CommAlgCat.productFundamentalTriangle_distinguished`, at each tower `P → P ⊗_R P → P`. -/
theorem hasEtaleDiagonalTriangle (R : Type u) [CommRing R] : HasEtaleDiagonalTriangle.{u} R := by
  intro P _ _ _
  have := isScalarTower_diagonalAlgebra R P
  exact exists_distTriang_fundamentalVertex.{u} P (P ⊗[R] P) P

end CommAlgCat

namespace IsLocalRing.IsHenselization

open CommAlgCat

/-- **[Stacks, Tag 08R2] items (7) and (8).** Let `(R, 𝔪, κ)` be a local ring and let `R → Rh` be
a henselization of `R` with residue field a prescribed extension `κ ⊆ L` of its residue field.
Then `L_{Rh/R} = 0` in `D(Rh)`.

At `L = κ` this is item (7), the henselization `R → R^h`, and at `L = κ^sep` a separable
algebraic closure it is item (8), a strict henselization `R → R^{sh}`. This is
`IsLocalRing.IsHenselization.isZero_cotangentComplexDerived` with its family of diagonal
triangles supplied by `CommAlgCat.hasEtaleDiagonalTriangle`. -/
@[stacks 08R2 "items (7) and (8) of the lemma, at once: `L_{R^h/R} = 0` and `L_{R^{sh}/R} = 0` \
for `R → Rh` a henselization of the local ring `R` with residue field the prescribed extension \
`κ ⊆ L` (`IsLocalRing.IsHenselization`, Stacks 04GQ), item (7) being the case `L = κ` and item \
(8) the case `L = κ^sep`. NOTHING is carried: item (5) needs the distinguished triangle of the \
diagonal tower `P → P ⊗_R P → P` of every étale stage, and that is Proposition 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`, through \
`CommAlgCat.hasEtaleDiagonalTriangle`, so it applies at every étale stage of the colimit \
presentation even though the index category is produced inside the proof. The source's own \
route is followed: items (5) and (6), the latter being \
`CommAlgCat.cotangentComplex_isZero_of_filtered_colimit`. The henselization hypothesis is \
load-bearing through `IsLocalRing.IsHenselization.ind_etale`, which supplies the presentation \
of `Rh` as a filtered colimit of étale `R`-algebras"]
theorem isZero_cotangentComplexDerived_unconditional {R : Type u} [CommRing R] [IsLocalRing R]
    (L : Type v) [Field L] [Algebra (ResidueField R) L] {Rh : Type u} [CommRing Rh]
    [IsLocalRing Rh] [Algebra R Rh] [IsHenselization R L Rh] :
    IsZero (cotangentComplexDerived.{u, u} R (CommAlgCat.of R Rh)) :=
  isZero_cotangentComplexDerived L (hasEtaleDiagonalTriangle R)

end IsLocalRing.IsHenselization

namespace CommAlgCat

open IsLocalRing

section Identification

variable (A : Type u) [CommRing A]

/-- **[Stacks, Tag 08UN], the identification over the henselized source.** Let `A → A^h` be a
henselization of the local ring `A` and let `C` be an `A^h`-algebra. Then
`L_{C/A} = L_{C/A^h}` in `D(C)`.

This is `CommAlgCat.nonempty_fundamentalVertex₂_iso_fundamentalVertex₃_henselization` at the
triangle of the tower `A → A^h → C` that Proposition 08QX provides. -/
@[stacks 08UN "the FIRST of the lemma's two equalities, `L_{B^h/A^h} = L_{B^h/A}`, and its \
`resp.` strict variant `L_{B^{sh}/A^{sh}} = L_{B^{sh}/A}` — one statement for both, because the \
henselization and a strict henselization are the two instances `L = κ` and `L = κ^sep` of \
`IsLocalRing.IsHenselization` (Stacks 04GQ). It is proved for an ARBITRARY `A^h`-algebra `C` in \
place of `B^h`, which is a generalization of the lemma and not a weakening of it. NOTHING is \
carried: the distinguished triangle of the tower `A → A^h → C` is Proposition 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`. The source's input `L_{A^h/A} = 0` is \
not carried either: it is proved, as \
`IsLocalRing.IsHenselization.isZero_cotangentComplexDerived_unconditional`, which is what makes \
the henselization hypothesis on `A^h` load-bearing. The lemma's SECOND equality, \
`L_{B^h/A} = L_{B/A} ⊗^𝐋_B B^h`, is \
`CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization_unconditional`"]
theorem nonempty_fundamentalVertex₂_iso_fundamentalVertex₃_henselization_unconditional
    [IsLocalRing A] (L : Type v) [Field L] [Algebra (ResidueField A) L]
    (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah] [IsHenselization A L Ah]
    (C : Type u) [CommRing C] [Algebra A C] [Algebra Ah C] [IsScalarTower A Ah C] :
    Nonempty (fundamentalVertex₂.{u, u} A C ≅ fundamentalVertex₃.{u, u} Ah C) := by
  obtain ⟨_, _, _, hT⟩ := exists_distTriang_fundamentalVertex.{u} A Ah C
  exact nonempty_fundamentalVertex₂_iso_fundamentalVertex₃_henselization A L Ah C
    (hasEtaleDiagonalTriangle A) hT

/-- **[Stacks, Tag 08UN], the derived scalar-extension identification.** Let `A → B` be a ring
map, let `B → B^h` be a henselization of the local ring `B`, and let `A → B → B^h` be a tower.
Then `L_{B^h/A} = L_{B/A} ⊗^𝐋_B B^h` in `D(B^h)`.

This is `CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization` at the
triangle of the tower `A → B → B^h` that Proposition 08QX provides. -/
@[stacks 08UN "the SECOND of the lemma's two equalities, `L_{B^h/A} = L_{B/A} ⊗^𝐋_B B^h`, and \
its `resp.` strict variant `L_{B^{sh}/A} = L_{B/A} ⊗^𝐋_B B^{sh}` — one statement for both, the \
henselization and a strict henselization being the two instances `L = κ` and `L = κ^sep` of \
`IsLocalRing.IsHenselization` (Stacks 04GQ). NOTHING is carried: the distinguished triangle of \
the tower `A → B → B^h` is Proposition 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`. The source's input `L_{B^h/B} = 0` is \
not carried either: it is proved, as \
`IsLocalRing.IsHenselization.isZero_cotangentComplexDerived_unconditional`, so the \
henselization hypothesis on `B^h` is load-bearing. The lemma's FIRST equality, \
`L_{B^h/A^h} = L_{B^h/A}`, is \
`CommAlgCat.nonempty_fundamentalVertex₂_iso_fundamentalVertex₃_henselization_unconditional`. \
NOTE that the local ring homomorphism `A → B` of the source is not assumed: the conclusion holds \
for any ring map `A → B` whose target is local, which is a generalization"]
theorem nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization_unconditional
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B] (L : Type v) [Field L]
    [Algebra (ResidueField B) L]
    (Bh : Type u) [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [IsHenselization B L Bh]
    [Algebra A Bh] [IsScalarTower A B Bh] :
    Nonempty (fundamentalVertex₁.{u, u} A B Bh ≅ fundamentalVertex₂.{u, u} A Bh) := by
  obtain ⟨_, _, _, hT⟩ := exists_distTriang_fundamentalVertex.{u} A B Bh
  exact nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization A B L Bh
    (hasEtaleDiagonalTriangle B) hT

/-- **[Stacks, Tag 08UN], the full chain.** Let `A → B` be a ring map of local rings, let
`A → A^h` and `B → B^h` be henselizations, and let `A^h → B^h` be compatible with them. Then
`L_{B^h/A^h} = L_{B^h/A} = L_{B/A} ⊗^𝐋_B B^h` in `D(B^h)`, read as an isomorphism
`L_{B/A} ⊗^𝐋_B B^h ≅ L_{B^h/A^h}`.

This is `CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₃_henselization` at the
triangles of the towers `A → B → B^h` and `A → A^h → B^h` that Proposition 08QX provides. -/
@[stacks 08UN "the lemma's full chain `L_{B^h/A^h} = L_{B^h/A} = L_{B/A} ⊗^𝐋_B B^h`, read as the \
isomorphism `L_{B/A} ⊗^𝐋_B B^h ≅ L_{B^h/A^h}` in `D(B^h)` obtained by composing the two \
equalities, together with its `resp.` strict variant — one statement for both, the henselization \
and a strict henselization being the instances `L = κ` and `L = κ^sep` of \
`IsLocalRing.IsHenselization` (Stacks 04GQ). The induced map `A^h → B^h` is taken as given data \
(an `A^h`-algebra structure on `B^h` with `IsScalarTower A A^h B^h`) rather than constructed. \
NOTHING is carried: the distinguished triangles of the towers `A → B → B^h` and \
`A → A^h → B^h` are both Proposition 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`. The source's inputs `L_{A^h/A} = 0` and \
`L_{B^h/B} = 0` are not carried either: both are proved, by \
`IsLocalRing.IsHenselization.isZero_cotangentComplexDerived_unconditional`, so both \
henselization hypotheses are load-bearing"]
theorem nonempty_fundamentalVertex₁_iso_fundamentalVertex₃_henselization_unconditional
    [IsLocalRing A] (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B]
    (LA : Type v) [Field LA] [Algebra (ResidueField A) LA]
    (LB : Type w) [Field LB] [Algebra (ResidueField B) LB]
    (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah] [IsHenselization A LA Ah]
    (Bh : Type u) [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [IsHenselization B LB Bh]
    [Algebra A Bh] [IsScalarTower A B Bh] [Algebra Ah Bh] [IsScalarTower A Ah Bh] :
    Nonempty (fundamentalVertex₁.{u, u} A B Bh ≅ fundamentalVertex₃.{u, u} Ah Bh) := by
  obtain ⟨e₁⟩ :=
    nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization_unconditional A B LB Bh
  obtain ⟨e₂⟩ :=
    nonempty_fundamentalVertex₂_iso_fundamentalVertex₃_henselization_unconditional A LA Ah Bh
  exact ⟨e₁.trans e₂⟩

end Identification

end CommAlgCat

end
