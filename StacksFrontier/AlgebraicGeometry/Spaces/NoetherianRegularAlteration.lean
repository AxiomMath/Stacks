module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteRegularAlteration

/-!
# Noetherian integral algebraic spaces carrying a regular alteration

A Noetherian integral algebraic space `Y` over `S` which admits an alteration whose source is
regular has a finite normalization and a dense regular open subspace: Stacks 0BHT.

## Main results

* `AlgebraicGeometry.Space.isFinite_normalization_and_exists_isDenseOpenSubspace_isRegular`:
  **Stacks 0BHT**.

## Implementation notes

The two assertions are proved, under weaker hypotheses on `Y`, by
`AlgebraicGeometry.Space.isFinite_normalization_of_regular_alteration` (which uses of the
Noetherian hypothesis only quasi-compactness and local Noetherianity) and
`AlgebraicGeometry.Space.exists_isDenseOpenSubspace_hasEtaleLocalProperty_isRegular` (which uses
no Noetherian hypothesis); this module states them together under the hypotheses of the source.

## References

* [Stacks Project, Tag 0BHT](https://stacks.math.columbia.edu/tag/0BHT)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0BHT.** Let `Y` be a Noetherian integral algebraic space over `S`, and suppose there
is an alteration `f : X ⟶ Y` with `X` regular. Then the normalization `Y^ν ⟶ Y` of `Y` is a
finite morphism of algebraic spaces, and `Y` has a dense open subspace which is regular.

Integrality of `Y` is part of `AlgebraicGeometry.Space.IsAlteration`. Noetherianity is
Stacks 03EA, `AlgebraicGeometry.Space.IsNoetherian`; its local Noetherianity makes the étale
scheme charts of `Y` satisfy the finiteness condition of Stacks 0BB1, so that
`AlgebraicGeometry.Space.normalizationData` is the normalization of `Y`, unique up to a unique
isomorphism over `Y` by `AlgebraicGeometry.Space.NormalizationData.existsUnique_iso_hom`.

The first assertion is `AlgebraicGeometry.Space.isFinite_normalization_of_regular_alteration`
and the second is
`AlgebraicGeometry.Space.exists_isDenseOpenSubspace_hasEtaleLocalProperty_isRegular`. The source
proves finiteness by étale localization to the spectrum of a Noetherian domain followed by
Stacks 08AR; that reduction is not valid for algebraic spaces, whose étale charts need not be
irreducible, and the proof used here goes instead through Chow's lemma (Stacks 089J) over an
affine chart, as the module docstring of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteRegularAlteration` explains. -/
@[stacks 0BHT "both assertions: finiteness of the normalization and the existence of a regular \
dense open. The source's Step 1, etale localization to a Noetherian domain, does not apply to \
algebraic spaces (etale charts of an integral space need not be irreducible); finiteness is \
proved instead through Chow's lemma for spaces over an affine chart"]
theorem isFinite_normalization_and_exists_isDenseOpenSubspace_isRegular
    (hZ : B.Contains (⊤_ Scheme.{u})) (hYnoeth : IsNoetherian B S hS hZ Y)
    (f : X ⟶ Y) (hf : IsAlteration B S hS f)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T)) :
    IsFinite B S hS (normalizationData B S hS hf.1
        (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Y hf.1
          hYnoeth.2.2)).hom ∧
      ∃ V : Subfunctor Y, IsDenseOpenSubspace B S hS hf.1 V ∧
        HasEtaleLocalProperty B S hS V.toFunctor (fun T : Scheme.{u} => IsRegular T) :=
  ⟨isFinite_normalization_of_regular_alteration B S hS f hf hXreg hYnoeth.1 hYnoeth.2.2,
    exists_isDenseOpenSubspace_hasEtaleLocalProperty_isRegular B S hS f hf hXreg⟩

end AlgebraicGeometry.Space

end
