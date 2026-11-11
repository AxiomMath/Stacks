module

public import StacksFrontier.Cotangent.DerivedPushoutBaseChange
public import StacksFrontier.Cotangent.SelfDerivedTensorVanishing
public import StacksFrontier.Cotangent.Triangle.FundamentalDisplay
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp

/-!
# Vanishing of the cotangent complex read off the diagonal

Let `A → B` be a ring map with no higher self-Tor of `B` over `A` and with
`L_{B/(B ⊗_A B)} = 0`. Then `L_{B/A} = 0` in `D(B)`, which is [Stacks, Tag 08R1].

The source's proof is the one carried out here. Base change along the square
```
A  --→  B
|       |
B  --→  B ⊗_A B
```
is a derived pushout exactly because the higher `Tor^A_i(B, B)` vanish, so [Stacks, Tag 08QQ]
gives `L_{B/A} ⊗^𝐋_B (B ⊗_A B) = L_{(B ⊗_A B)/B}`. The fundamental triangle of the tower
`B → B ⊗_A B → B`, whose second map is the multiplication, reads

`L_{(B ⊗_A B)/B} ⊗^𝐋_{(B ⊗_A B)} B ⟶ L_{B/B} ⟶ L_{B/(B ⊗_A B)}`;

its middle vertex vanishes because `B` is a polynomial algebra over itself and its third vertex
vanishes by hypothesis, so its first vertex vanishes. Composing the two base changes along
`B → B ⊗_A B → B`, whose composite is the identity, identifies that first vertex with `L_{B/A}`.

## Main definitions

* `CommAlgCat.diagonalAlgebra`: `B` as an algebra over `B ⊗_A B` through the multiplication map.

## Main results

* `CommAlgCat.cotangentComplexDerived_iso_fundamentalVertex₁_diagonal`: the identification
  `L_{B/A} = L_{(B ⊗_A B)/B} ⊗^𝐋_{(B ⊗_A B)} B` of the first two steps of the proof.
* `CommAlgCat.isZero_cotangentComplexDerived_of_torIndependent`: [Stacks, Tag 08R1] for a
  distinguished triangle of the tower `B → B ⊗_A B → B` given as a parameter; the triangle is
  supplied from Proposition 08QX in
  `CommAlgCat.isZero_cotangentComplexDerived_of_torIndependent_unconditional`.

## Implementation notes

*Both hypotheses of the source are load-bearing.* `hTor`, the vanishing of the higher
`Tor^A_i(B, B)`, is what makes the displayed square a derived pushout and is consumed by
`CommAlgCat.derivedCotangentComplexBaseChangeIso` ([Stacks, Tag 08QQ]) inside
`CommAlgCat.cotangentComplexDerived_iso_fundamentalVertex₁_diagonal`; without it that lemma does
not apply and the first vertex of the triangle is not `L_{B/A}`. `hCot`, the vanishing of
`L_{B/(B ⊗_A B)}`, is the third vertex of the triangle and is consumed by
`CategoryTheory.Pretriangulated.Triangle.isZero₁_of_isZero₂₃`. The hypothesis `hCot` is the
vanishing of `CommAlgCat.fundamentalVertex₃ (B ⊗_A B) B`, which is
`DerivedCategory.Q.obj (CommAlgCat.cotangentComplex (B ⊗_A B) (CommAlgCat.of (B ⊗_A B) B))`, the
relative cotangent complex of the multiplication map as an object of `D(B)`, so it is the
source's hypothesis and not the vanishing of an auxiliary zero object.

*The triangle as a parameter.* The theorem here takes the distinguished triangle on the three
vertices of the display 92.7.0.1 for the tower `B → B ⊗_A B → B` as a parameter `hT`, in the
spelling of `CommAlgCat.fundamentalVertex₁`, `CommAlgCat.fundamentalVertex₂` and
`CommAlgCat.fundamentalVertex₃`, because this file is upstream of Proposition 08QX. Proposition
08QX is proved in the library, for arbitrary ring maps, as
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`, and
`CommAlgCat.isZero_cotangentComplexDerived_of_torIndependent_unconditional` of
`StacksFrontier.Cotangent.EtaleVanishingUnconditional` supplies `hT` from it: that declaration is
[Stacks, Tag 08R1] with exactly the source's hypotheses, and carries the tag.

*Which inclusion is which.* `B ⊗_A B` is a `B`-algebra through `b ↦ b ⊗ 1`, which is the
instance Mathlib provides, and `L_{(B ⊗_A B)/B}` is taken relative to it. The base change of
[Stacks, Tag 08QQ] is along the *other* inclusion `b ↦ 1 ⊗ b`; it is that map whose composite
with the multiplication is the identity of `B`, which is what
`CommAlgCat.algebraMap_diagonalAlgebra_comp_includeRight` records and what the composition
isomorphism of derived extension of scalars then turns into the identity functor. The source does
not distinguish the two inclusions, and the statement is symmetric in them.

*The multiplication as an instance.* `CommAlgCat.diagonalAlgebra` is the algebra structure on `B`
over `B ⊗_A B` given by `Algebra.TensorProduct.lmul'`, i.e. `b ⊗ b' ↦ b b'`. It is attached as a
`local instance` so that the three vertices of the display can be written with the abbreviations
of `StacksFrontier.Cotangent.Triangle.FundamentalDisplay`; it appears explicitly in the elaborated
statements, so a consumer gets the multiplication map and no other `B ⊗_A B`-algebra structure
on `B`.

## References

* [Stacks Project, Tag 08R1](https://stacks.math.columbia.edu/tag/08R1)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ), base change along a
  derived pushout square.
* [Stacks Project, Tag 08QH](https://stacks.math.columbia.edu/tag/08QH), through
  `CommAlgCat.isZero_cotangentComplex_self`, the vanishing of `L_{B/B}`.
* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS), the display, and
  [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), that it is
  distinguished.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

/-- **`B` as an algebra over `B ⊗_A B` through the multiplication map** `b ⊗ b' ↦ b b'`. This is
the ring map whose relative cotangent complex is the `L_{B/(B ⊗_A B)}` of [Stacks, Tag 08R1]. -/
@[instance_reducible]
noncomputable def diagonalAlgebra (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] : Algebra (B ⊗[A] B) B :=
  (Algebra.TensorProduct.lmul' (S := B) A).toRingHom.toAlgebra

attribute [local instance] diagonalAlgebra

section Diagonal

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- The structure map of `CommAlgCat.diagonalAlgebra` is the multiplication map. -/
theorem algebraMap_diagonalAlgebra :
    algebraMap (B ⊗[A] B) B = (Algebra.TensorProduct.lmul' (S := B) A).toRingHom :=
  rfl

/-- The multiplication map `B ⊗_A B → B` undoes the inclusion `b ↦ 1 ⊗ b`. -/
theorem algebraMap_diagonalAlgebra_comp_includeRight :
    (algebraMap (B ⊗[A] B) B).comp
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom =
      RingHom.id B := by
  ext x
  rw [algebraMap_diagonalAlgebra]
  simp

/-- The base-change unit of the square `A → B`, `A → B`, `B → B ⊗_A B` is the identity of
`B ⊗_A B`: it sends `b ⊗ b'` to `(b ⊗ 1) * (1 ⊗ b')`. -/
theorem baseChangeUnit_includeRight_apply (z : B ⊗[A] B) :
    baseChangeUnit (A := A) (A' := B) (B := CommAlgCat.of A B)
      (B' := CommAlgCat.of B (B ⊗[A] B)) Algebra.TensorProduct.includeRight z = z := by
  induction z with
  | tmul b b' => rw [baseChangeUnit_tmul]; simp
  | add y z hy hz => rw [map_add, hy, hz]

/-- The base-change unit of the square `A → B`, `A → B`, `B → B ⊗_A B` is bijective, so that
square is a pushout of rings. -/
theorem bijective_baseChangeUnit_includeRight :
    Function.Bijective
      (baseChangeUnit (A := A) (A' := B) (B := CommAlgCat.of A B)
        (B' := CommAlgCat.of B (B ⊗[A] B)) Algebra.TensorProduct.includeRight) :=
  ⟨fun y z hyz => by
      rwa [baseChangeUnit_includeRight_apply A B y, baseChangeUnit_includeRight_apply A B z] at hyz,
    fun z => ⟨z, baseChangeUnit_includeRight_apply A B z⟩⟩

/-- **The first vertex of the fundamental triangle of `B → B ⊗_A B → B` is `L_{B/A}`.**

If the higher `Tor^A_i(B, B)` vanish then the square
```
A  --→  B
|       |
B  --→  B ⊗_A B
```
is a derived pushout, so [Stacks, Tag 08QQ] identifies `L_{B/A} ⊗^𝐋_B (B ⊗_A B)` with
`L_{(B ⊗_A B)/B}`. Extending scalars further along the multiplication map `B ⊗_A B → B` composes
the two base changes into the base change along the identity of `B`, which is the identity
functor of `D(B)`; so `L_{(B ⊗_A B)/B} ⊗^𝐋_{(B ⊗_A B)} B = L_{B/A}`. -/
def cotangentComplexDerived_iso_fundamentalVertex₁_diagonal
    (hTor : RingTheory.TorIndependence.TorIndependent A B (B : Type u)) :
    cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
      fundamentalVertex₁.{u, u} B (B ⊗[A] B) B :=
  (totalDerivedExtensionScalarsId.{u, u} B).app _ ≪≫
    eqToIso (by rw [algebraMap_diagonalAlgebra_comp_includeRight A B]; rfl) ≪≫
    ((totalDerivedExtensionScalarsComp.{u, u}
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom
      (algebraMap (B ⊗[A] B) B)).app _).symm ≪≫
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap (B ⊗[A] B) B)).functor.mapIso
      (derivedCotangentComplexBaseChangeIso (A := A) (A' := B) (B := CommAlgCat.of A B)
        (B' := CommAlgCat.of B (B ⊗[A] B)) Algebra.TensorProduct.includeRight hTor
        (bijective_baseChangeUnit_includeRight A B))

/-- **[Stacks, Tag 08R1] for a given triangle.** Let `A → B` be a ring map such that
`Tor^A_i(B, B) = 0` for `i > 0` and such that `L_{B/(B ⊗_A B)} = 0`, and let `hT` be a
distinguished triangle on the three vertices of the display of the tower `B → B ⊗_A B → B`,
whose second map is the multiplication. Then `L_{B/A} = 0` in `D(B)`.

The triangle is a parameter because this file is upstream of Proposition 08QX, which supplies it
for arbitrary ring maps; `CommAlgCat.isZero_cotangentComplexDerived_of_torIndependent_unconditional`
is the lemma with exactly the source's hypotheses. The middle vertex `L_{B/B}` vanishes by
`CommAlgCat.isZero_cotangentComplex_self`, and the third vertex `L_{B/(B ⊗_A B)}` vanishes by
`hCot`, so the first vertex vanishes; and that first vertex is `L_{B/A}` by
`CommAlgCat.cotangentComplexDerived_iso_fundamentalVertex₁_diagonal`, which is where `hTor` is
consumed. -/
theorem isZero_cotangentComplexDerived_of_torIndependent
    (hTor : RingTheory.TorIndependence.TorIndependent A B (B : Type u))
    {α : fundamentalVertex₁.{u, u} B (B ⊗[A] B) B ⟶ fundamentalVertex₂.{u, u} B B}
    {β : fundamentalVertex₂.{u, u} B B ⟶ fundamentalVertex₃.{u, u} (B ⊗[A] B) B}
    {γ : fundamentalVertex₃.{u, u} (B ⊗[A] B) B ⟶
      (fundamentalVertex₁.{u, u} B (B ⊗[A] B) B)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} B)))
    (hCot : IsZero (fundamentalVertex₃.{u, u} (B ⊗[A] B) B)) :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)) :=
  IsZero.of_iso
    (Triangle.isZero₁_of_isZero₂₃ _ hT (isZero_cotangentComplex_self B) hCot)
    (cotangentComplexDerived_iso_fundamentalVertex₁_diagonal A B hTor)

end Diagonal

end CommAlgCat

end
