module

public import StacksFrontier.Cotangent.HenselizationUnconditional
public import StacksFrontier.Cotangent.Localization

/-!
# Vanishing of the cotangent complex along a tower of ring maps

For ring maps `A → B → C`, if `L_{B/A} = 0` and `L_{C/B} = 0` then `L_{C/A} = 0`: this is read
off the fundamental triangle of Proposition 08QX, whose first vertex `L_{B/A} ⊗^𝐋_B C` and third
vertex `L_{C/B}` both vanish. The case used in the étale topology is a strict henselization of
a localization: if `A → A_𝔭` is the localization at a prime and `A_𝔭 → C` is a (strict)
henselization of the local ring `A_𝔭`, then `L_{C/A} = 0`, by items (3), (7) and (8) of
Tag 08R2.

## Main results

* `CommAlgCat.isZero_cotangentComplexDerived_of_tower`: `L_{B/A} = 0` and `L_{C/B} = 0` give
  `L_{C/A} = 0`.
* `CommAlgCat.isZero_cotangentComplexDerived_henselization_localization`: `L_{C/A} = 0` for a
  henselization `C` of a localization of `A` at a prime.

## References

* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2), items (3), (7), (8).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

/-- **The cotangent complex vanishes along a tower whose two steps have vanishing cotangent
complexes.** For ring maps `A → B → C`, the fundamental triangle of Proposition 08QX has first
vertex `L_{B/A} ⊗^𝐋_B C`, which vanishes with `L_{B/A}`, so its second arrow
`L_{C/A} ⟶ L_{C/B}` is an isomorphism, and `L_{C/B} = 0`. -/
theorem isZero_cotangentComplexDerived_of_tower (A B C : Type u) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hB : IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)))
    (hC : IsZero (cotangentComplexDerived.{u, u} B (CommAlgCat.of B C))) :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A C)) :=
  have : IsIso (fundamentalMor₂.{u} A B C) :=
    (Triangle.isZero₁_iff_isIso₂ _ (productFundamentalTriangle_distinguished A B C)).1
      (Functor.map_isZero _ hB)
  hC.of_iso (asIso (fundamentalMor₂.{u} A B C))

/-- **The cotangent complex of a henselization of a localization vanishes.** Let `A_S` be a
localization of `A` which is a local ring (for instance the localization `A_𝔭` at a prime) and
let `C` be a henselization of `A_S` with residue field an extension `L` of the residue field of
`A_S` (a strict henselization when `L` is a separable closure). Then `L_{C/A} = 0`:
`L_{A_S/A} = 0` by item (3) of Tag 08R2 and `L_{C/A_S} = 0` by items (7) and (8). -/
theorem isZero_cotangentComplexDerived_henselization_localization (A : Type u) [CommRing A]
    (S : Submonoid A) (Ap : Type u) [CommRing Ap] [Algebra A Ap]
    [IsLocalization S Ap] [IsLocalRing Ap] (L : Type v) [Field L]
    [Algebra (IsLocalRing.ResidueField Ap) L] (C : Type u) [CommRing C] [IsLocalRing C]
    [Algebra Ap C] [IsLocalRing.IsHenselization Ap L C] [Algebra A C] [IsScalarTower A Ap C] :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A C)) :=
  isZero_cotangentComplexDerived_of_tower A Ap C
    (isZero_cotangentComplexDerived_localization A S Ap)
    (IsLocalRing.IsHenselization.isZero_cotangentComplexDerived_unconditional L)

end CommAlgCat
