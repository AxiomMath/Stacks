module

public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayNormalizedShift
public import StacksFrontier.RingTheory.Dualizing.DerivedHomModelComparison

/-!
# `RHom_A(κ, ω_A) ≅ κ[0]` at the locally small model

Let `(A, 𝔪, κ)` be a Cohen–Macaulay Noetherian local ring and `ω_A` a *dualizing module* for `A`
in the sense of `Stacks.Duality.IsDualizingRingModule`: a finite module which, placed in some
cohomological degree, is a dualizing complex. The normalization convention of
[Stacks, Section 47.16] identifies `RHom_A(κ, ω_A^•)` with `κ[0]` for the one shift `ω_A^•` that
is *normalized*, and over a Cohen–Macaulay local ring that shift is pinned by the dimension:
`Dualizing.isNormalizedDualizingComplex_single_neg_localRingDimension`.

That statement lives at `CategoryTheory.HasDerivedCategory.standard`, because
`Dualizing.IsNormalizedDualizingComplex` is defined in terms of `Dualizing.derivedHom`, which
bakes that model into its type. **The consumer needs it at the locally small model of
[Stacks, Tag 079Q]**: [Stacks, Tag 0A9F] at the twisted inverse image,
`AlgebraicGeometry.twistedInverseImage_spec_isoDerivedHom`, is stated against
`Dualizing.AnyModel.derivedHom` read at `StacksDraft.ModuleCat.hasDerivedCategory`, that being the
model at which the adjunction of [Stacks, Tag 0A9E] exists at all.

This file crosses that boundary, by `Dualizing.AnyModel.derivedHomModelIso`.

## Main results

* `Dualizing.nonempty_derivedHom_residueField_iso_single_of_cohenMacaulay` — for `ω_A` a dualizing
  module over a Cohen–Macaulay Noetherian local ring, `RHom_A(κ, ω_A[-dim A]) ≅ κ[0]` at the
  locally small model, with the degree in which `ω_A` is a dualizing complex left as the
  existential `Stacks.Duality.IsDualizingRingModule` gives it.

## What this does and does not supply

It supplies the **whole** normalization isomorphism, not only its vanishing half: the vanishing
half is `Dualizing.subsingleton_ext_residueField_single_of_ne_localRingDimension`, which says
`Ext^i_A(κ, ω_A) = 0` for `i ≠ dim A` and is silent in degree `dim A`, whereas
`Dualizing.IsNormalizedDualizingComplex` *is* the isomorphism `RHom_A(κ, ω_A^•) ≅ κ[0]` and the
transport below moves it unchanged.

What it does not supply is the Cohen–Macaulay hypothesis, which is carried. For `A` as in
Situation [Stacks, Tag 0B4W] — a two-dimensional normal Noetherian local domain — it is
discharged by `AlgebraicGeometry.RationalSingularitySituation.isCohenMacaulayLocalRing` of
`…/RationalSingularities/SituationCohenMacaulay.lean`: Serre's criterion gives `(S_2)` and
`(S_2)` in dimension two is Cohen–Macaulayness.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- **`RHom_A(κ, ω_A[-dim A]) ≅ κ[0]` at the locally small model of [Stacks, Tag 079Q]**, for
`ω_A` a dualizing module over a Cohen–Macaulay Noetherian local ring.

The degree `n` in which `ω_A` is a dualizing complex is the existential of
`Stacks.Duality.IsDualizingRingModule` and is not assumed known; the normalizing shift is pinned
instead by the dimension, which is
`Dualizing.isNormalizedDualizingComplex_single_neg_localRingDimension`, and that statement is
`Dualizing.IsNormalizedDualizingComplex` at the standard model. The crossing to the locally small
model is `Dualizing.AnyModel.nonempty_derivedHom_locallySmall_iso_of_standard_iso`: the two models
have the same objects, so `ω_A[-dim A]` and `κ[0]` are read unchanged and only the morphisms are
transported. -/
theorem nonempty_derivedHom_residueField_iso_single_of_cohenMacaulay
    (hA : IsCohenMacaulayLocalRing A) (ω : ModuleCat.{u} A) (n : ℤ)
    (hn : @IsDualizingComplex A _ _ (HasDerivedCategory.standard (ModuleCat.{u} A))
      ((@DerivedCategory.singleFunctor (ModuleCat.{u} A) _ _
        (HasDerivedCategory.standard (ModuleCat.{u} A)) n).obj ω)) :
    Nonempty ((@AnyModel.derivedHom.{u, u, u, u, u} A (IsLocalRing.ResidueField A) _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (ModuleCat.{u} A))
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
            (ModuleCat.{u} (IsLocalRing.ResidueField A)))
          (IsLocalRing.residue A)).obj
        ((@DerivedCategory.singleFunctor (ModuleCat.{u} A) _ _
          (HasDerivedCategory.standard (ModuleCat.{u} A))
          (-(localRingDimension A : ℤ))).obj ω) ≅
      (@DerivedCategory.singleFunctor (ModuleCat.{u} (IsLocalRing.ResidueField A)) _ _
          (HasDerivedCategory.standard (ModuleCat.{u} (IsLocalRing.ResidueField A))) 0).obj
        ((ModuleCat.uliftFunctor.{0} (IsLocalRing.ResidueField A)).obj
          (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)))) := by
  obtain ⟨e⟩ := (isNormalizedDualizingComplex_single_neg_localRingDimension hA ω n hn).2
  exact AnyModel.nonempty_derivedHom_locallySmall_iso_of_standard_iso
    (IsLocalRing.residue A) _ _ e

end Dualizing

end
