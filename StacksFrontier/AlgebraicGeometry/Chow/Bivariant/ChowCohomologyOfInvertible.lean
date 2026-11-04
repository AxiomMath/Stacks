module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications

/-!
# The restriction map of Chow cohomology along a closed immersion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `i : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S`. This file gives the restriction map
`res : A^p(Z ⟶ X) ⟶ A^p(Z)` of Stacks 0F9Z at the Gysin system
`Stacks.Chow.gysinSystemOfInvertible` of the first Chern class of an invertible module, and the
formula of Stacks 0FA1

  `res(c) ∩ α = c ∩ i_*α`   for `α ∈ CH_*(Z)`.

## Main definitions

* `Stacks.Chow.closedImmersionChowCohomologyRestrictionOfInvertible` — the restriction map
  `A^p(Z ⟶ X) ⟶ A^p(Z)` of a closed immersion at that Gysin system.

## Main results

* `Stacks.Chow.bivariantRestrictionCap_id_eq_cap_properChowPushforward_unconditional` — the formula
  `res(c) ∩ α = c ∩ i_*α` for the restriction of Stacks 0F9Z read at the test scheme `𝟙 Z`, for an
  arbitrary Gysin system.
* `Stacks.Chow.bivariantRestrictionOfInvertible_cap_id_eq_cap_properChowPushforward` — the formula
  `res(c) ∩ α = c ∩ i_*α` for the restricted bivariant class of Stacks 0F9Z at that Gysin system.
* `Stacks.Chow.closedImmersionChowCohomologyRestrictionOfInvertible_cap` — the formula
  `res(c) ∩ α = c ∩ i_*α` for the restriction map at that Gysin system.

## Implementation notes

The two sides of the formula are read in `CH_{k-p}(Z)` through the canonical identifications
`Z ×_Z Z ≅ Z` and `X ×_X Z ≅ Z`, as in `Stacks.Chow.closedImmersionChowCohomologyRestriction_cap`.

## References

* [Stacks Project, Tag 0FA1](https://stacks.math.columbia.edu/tag/0FA1)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section ArbitraryGysinSystem

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X)
  [IsClosedImmersion i] (hi : i ≫ sX = sZ) (p : ℤ)

/-- For a Gysin system `G`, a closed immersion `i : Z ⟶ X` of schemes locally of finite type over
the base and a bivariant class `c` of degree `p` for `i`, the restriction `res(c)` of `c` along
`i`, read at the test scheme `𝟙 Z`, satisfies

  `res(c) ∩ α = c ∩ i_*α`

in `CH_{k-p}(Z)` for every `α ∈ CH_k(Z)`. -/
@[stacks 0FA1]
theorem bivariantRestrictionCap_id_eq_cap_properChowPushforward_unconditional
    (c : BivariantClass C G sZ sX i hi p) (k : ℤ) (α : chowGroup C sZ k) :
    chowPushforwardOfIso C (pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ sZ)) sZ
        (selfPullbackIdIso i).inv (selfPullbackIdIso_inv_comp i sZ) (k - p)
        (bivariantRestrictionCap C G sZ sX i hi i p c (𝟙 Z) k
          (chowGroupCongr C (id_comp_comp_structureMorphism_eq C sZ sX i hi) k α)) =
      chowPushforwardOfIso C (pullback.fst i (𝟙 X) ≫ sZ) sZ (pullbackIdIso i).inv
        (pullbackIdIso_inv_comp i sZ) (k - p)
        (c.cap (𝟙 X) k (chowGroupCongr C (Category.id_comp sX).symm k
          (properChowPushforward C sZ sX i hi k
            (properPushforwardFactorsThroughRationalEquivalence C sZ sX i hi k) α))) :=
  bivariantRestrictionCap_id_eq_cap_properChowPushforward C G sZ sX i hi p c k
    (properPushforwardFactorsThroughRationalEquivalence C sZ sX i hi k) α

end ArbitraryGysinSystem

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (p : ℤ)

/-- At the Gysin system of the first Chern class rule of an invertible module, the restriction
`res(c)` of Stacks 0F9Z of a bivariant class `c` of degree `p` for the closed immersion `i : Z ⟶ X`
— a class for `Z ×_X Z ⟶ Z`, read at the test scheme `𝟙 Z` — satisfies

  `res(c) ∩ α = c ∩ i_*α`

in `CH_{k-p}(Z)` for every `α ∈ CH_k(Z)`. -/
@[stacks 0FA1 "for the restricted bivariant class, at the Gysin system of the first Chern class \
rule, with the isomorphism case of Stacks 02TA discharged"]
theorem bivariantRestrictionOfInvertible_cap_id_eq_cap_properChowPushforward
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) (k : ℤ)
    (α : chowGroup C sZ k) :
    chowPushforwardOfIso C (pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ sZ)) sZ
        (selfPullbackIdIso i).inv (selfPullbackIdIso_inv_comp i sZ) (k - p)
        ((bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi i p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c).cap (𝟙 Z) k
          (chowGroupCongr C (id_comp_comp_structureMorphism_eq C sZ sX i hi) k α)) =
      chowPushforwardOfIso C (pullback.fst i (𝟙 X) ≫ sZ) sZ (pullbackIdIso i).inv
        (pullbackIdIso_inv_comp i sZ) (k - p)
        (c.cap (𝟙 X) k (chowGroupCongr C (Category.id_comp sX).symm k
          (properChowPushforward C sZ sX i hi k
            (properPushforwardFactorsThroughRationalEquivalence C sZ sX i hi k) α))) :=
  bivariantRestriction_cap_id_eq_cap_properChowPushforward C (gysinSystemOfInvertible C) sZ sX i hi
    p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c k
    (properPushforwardFactorsThroughRationalEquivalence C sZ sX i hi k) α

/-- The restriction map `res : A^p(Z ⟶ X) ⟶ A^p(Z)` along a closed immersion `i : Z ⟶ X`, as a
group homomorphism, at the Gysin system of the first Chern class rule of an invertible module. -/
@[stacks 0FA1 "the restriction map to A^p(Z), at the Gysin system of the first Chern class \
rule, with the isomorphism case of Stacks 02TA discharged"]
def closedImmersionChowCohomologyRestrictionOfInvertible :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p →+
      chowCohomologyComponent C (gysinSystemOfInvertible C) (i ≫ sX) p :=
  closedImmersionChowCohomologyRestriction C (gysinSystemOfInvertible C) sZ sX i hi p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)

/-- At the Gysin system of the first Chern class rule of an invertible module, the restriction map
`res : A^p(Z ⟶ X) ⟶ A^p(Z)` of a closed immersion `i : Z ⟶ X` satisfies

  `res(c) ∩ α = c ∩ i_*α`

in `CH_{k-p}(Z)` for every `α ∈ CH_k(Z)`, both sides being read on `Z` through the canonical
identifications `Z ×_Z Z ≅ Z` and `X ×_X Z ≅ Z`. -/
@[stacks 0FA1 "the cap formula for the restriction map to A^p(Z), at the Gysin system of the \
first Chern class rule, with the isomorphism case of Stacks 02TA discharged"]
theorem closedImmersionChowCohomologyRestrictionOfInvertible_cap
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) (k : ℤ)
    (α : chowGroup C sZ k) :
    chowPushforwardOfIso C (pullback.fst (𝟙 Z) (𝟙 Z) ≫ (i ≫ sX)) sZ
        (identityBaseChangeIso (𝟙 Z)).hom
        (identityBaseChangeIso_id_comp_base C sZ sX i hi) (k - p)
        ((closedImmersionChowCohomologyRestrictionOfInvertible C sZ sX i hi p c).cap (𝟙 Z) k
          (chowGroupCongr C (id_comp_comp_structureMorphism_eq C sZ sX i hi) k α)) =
      chowPushforwardOfIso C (pullback.fst i (𝟙 X) ≫ sZ) sZ (pullbackIdIso i).inv
        (pullbackIdIso_inv_comp i sZ) (k - p)
        (c.cap (𝟙 X) k (chowGroupCongr C (Category.id_comp sX).symm k
          (properChowPushforward C sZ sX i hi k
            (properPushforwardFactorsThroughRationalEquivalence C sZ sX i hi k) α))) :=
  closedImmersionChowCohomologyRestriction_cap C (gysinSystemOfInvertible C) sZ sX i hi p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c k
    (properPushforwardFactorsThroughRationalEquivalence C sZ sX i hi k) α

end Stacks.Chow

end
