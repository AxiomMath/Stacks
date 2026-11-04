module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalConjugationArrow

/-!
# The modified self-map of a first-order thickening is invertible

Let `i : X ⟶ X'` be a first-order thickening of a scheme over `S`. For an `𝒪_X`-linear map
`u : Ω_{X/S}|_X ⟶ 𝒞_{X/X'}` the modified lift `u ⬝ 𝟙_{X'}` of [Stacks Project, Tag 0CK1] is a
self-map of `X'` over `S` restricting to the identity of `X`. This file records that it is an
**isomorphism**, with inverse the self-map of `-u`.

The two inputs are already proved: composing two modified self-maps adds their derivations
(`Stacks.Thickenings.derivationActionGlobal_comp_derivationActionGlobal`) and the zero derivation
gives the identity (`Stacks.Thickenings.derivationActionGlobal_zero`). Together they say that
`u ↦ u ⬝ 𝟙_{X'}` is a homomorphism from a group, so its values are invertible.

## Main results

* `Stacks.Thickenings.derivationActionGlobal_self_comp_neg`: `(u ⬝ 𝟙) ≫ ((-u) ⬝ 𝟙) = 𝟙`.
* `Stacks.Thickenings.isIso_derivationActionGlobal_self`: `u ⬝ 𝟙` is an isomorphism.
* `Stacks.Thickenings.inv_derivationActionGlobal_self`: its inverse is `(-u) ⬝ 𝟙`.

## Implementation notes

The invertibility is what relates the two parametrisations of conjugating a lift. The
thickening-level conjugate `Stacks.Thickenings.conjugateBaseLift` is
`(u ⬝ 𝟙) ≫ a' ≫ (v ⬝ 𝟙)`, with the source factor *not* inverted, while the
deformation-category-level `Deformation.Examples.globalLiftsOverBaseConj` is
`α⁻¹ ≫ ℓ ≫ β`. The third result here says the two agree at `α = (-u) ⬝ 𝟙`, so the two
parametrisations of the source side differ by a sign.

`Stacks.Thickenings.isIso_derivationActionGlobal_self` is a theorem rather than an instance:
`Stacks.Thickenings.derivationActionGlobal` is not a head symbol instance search should be
driven by, and the invertibility is always wanted at a derivation that is already in hand.

## References

* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

section SelfMapIso

variable {S X X' : Scheme.{u}} {i : X ⟶ X'} [IsClosedImmersion i] {p : X' ⟶ S}
  (hsq : i.ker ^ 2 = ⊥)
  (comm_i : i ≫ (𝟙 X' : X' ⟶ X') = (𝟙 X : X ⟶ X) ≫ i)
  (u : Stacks.Smooth.pullbackCotangentSheaf (i ≫ p) (𝟙 X) ⟶ conormalModules i)

/-- **The modified self-maps of a derivation and of its negative are inverse**,
`(u ⬝ 𝟙) ≫ ((-u) ⬝ 𝟙) = 𝟙`. Composing adds the derivations and the zero derivation gives the
identity. -/
theorem derivationActionGlobal_self_comp_neg :
    derivationActionGlobal hsq u comm_i ≫ derivationActionGlobal hsq (-u) comm_i = 𝟙 X' := by
  rw [derivationActionGlobal_comp_derivationActionGlobal hsq comm_i u (-u), add_neg_cancel]
  exact derivationActionGlobal_zero (q := p) hsq (𝟙 X') comm_i

/-- **The modified self-map of a first-order thickening is an isomorphism**, its inverse being
the modified self-map of the negative derivation. -/
theorem isIso_derivationActionGlobal_self : IsIso (derivationActionGlobal hsq u comm_i) := by
  have h := derivationActionGlobal_self_comp_neg hsq comm_i (-u)
  rw [neg_neg] at h
  exact ⟨⟨derivationActionGlobal hsq (-u) comm_i,
    derivationActionGlobal_self_comp_neg hsq comm_i u, h⟩⟩

/-- **The inverse of a modified self-map is the modified self-map of the negative
derivation.** -/
theorem inv_derivationActionGlobal_self
    [IsIso (derivationActionGlobal hsq u comm_i)] :
    CategoryTheory.inv (derivationActionGlobal hsq u comm_i) =
      derivationActionGlobal hsq (-u) comm_i :=
  IsIso.inv_eq_of_hom_inv_id (derivationActionGlobal_self_comp_neg hsq comm_i u)

end SelfMapIso

end Stacks.Thickenings

end
