module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ShortExactExtension

/-!
# The bundled statements of Situation 0A52 pass to extensions

Lemma 0A5C: for a short exact sequence `0 → F₁ → F → F₂ → 0` of torsion abelian sheaves on
`X_étale`, if statements (1) -- (8) of Situation 0A52 hold for `F₁` and `F₂`, then they hold for
`F`. This file proves the homological part of that lemma for the bundle
`Stacks.EtaleCohomology.CurveStatements`: all eight statements pass to the middle term of a short
exact sequence as soon as constructibility of the middle term forces constructibility of the two
outer ones.

## Main results

* `Stacks.EtaleCohomology.CurveStatements.of_shortExact_of_constructible`: the eight statements
  for the outer terms of a short exact sequence give the eight statements for the middle term,
  given that the constructibility condition of statements (4) and (5) descends from the middle
  term to the outer ones.

## Implementation notes

Six of the eight statements are the individual transfers of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionSheavesCurves/ShortExactExtension.lean`,
applied for each member of the families the bundle quantifies over: the projection of every
scalar extension for statements (6) and (7) and the inclusion of every open for statement (8).
Statements (4) and (5) are the finiteness half of the long exact sequence,
`Stacks.EtaleCohomology.finite_sheafCohomology_X₂_of_shortExact`, once the side conditions are
moved to the outer terms. The torsion condition moves by
`Stacks.EtaleCohomology.isPrimeToCharacteristicTorsion_of_shortExact`; constructibility moves by
Proposition 09BH in the source, and that is the hypothesis `hc` here, which is discharged on a
Noetherian scheme in `Stacks.EtaleCohomology.CurveStatements.of_shortExact`.

## References

* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} {π : X ⟶ Spec (.of k)}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- **The eight statements of Situation 0A52 pass to the middle term of a short exact sequence**,
granted that constructibility of the middle term gives constructibility of the outer terms (which
on a Noetherian scheme is Proposition 09BH). -/
theorem CurveStatements.of_shortExact_of_constructible (hS : S.ShortExact)
    (h₁ : CurveStatements.{u, v, w} π S.X₁) (h₃ : CurveStatements.{u, v, w} π S.X₃)
    (hc : ∀ (B : BigEtaleSite.{u}) (hX : B.Contains X)
      [∀ (T T' : B.Scheme) (f : T' ⟶ T),
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v}
          (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
          (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
      [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
        HasWeakSheafify
          ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
          AddCommGrpCat.{max (u + 1) v}],
      IsConstructibleEtaleAbelianSheaf.{u, v} B X hX S.X₂ →
        IsConstructibleEtaleAbelianSheaf.{u, v} B X hX S.X₁ ∧
          IsConstructibleEtaleAbelianSheaf.{u, v} B X hX S.X₃) :
    CurveStatements.{u, v, w} π S.X₂ where
  vanishing q hq :=
    subsingleton_etaleCohomology_X₂_of_shortExact hS h₁.vanishing h₃.vanishing q hq
  affineVanishing :=
    subsingleton_etaleCohomology_X₂_of_shortExact_of_isAffine hS h₁.affineVanishing
      h₃.affineVanishing
  primePowerVanishing p _ hp :=
    subsingleton_etaleCohomology_X₂_of_shortExact_of_isPrimePowerTorsion p hS
      (h₁.primePowerVanishing p hp) (h₃.primePowerVanishing p hp)
  finite_of_isPrimeToCharacteristicTorsion B hX _ _ hcon htor q := by
    obtain ⟨hc₁, hc₃⟩ := hc B hX hcon
    obtain ⟨ht₁, ht₃⟩ := isPrimeToCharacteristicTorsion_of_shortExact (ringExpChar k) hS htor
    have := h₁.finite_of_isPrimeToCharacteristicTorsion B hX hc₁ ht₁ q
    have := h₃.finite_of_isPrimeToCharacteristicTorsion B hX hc₃ ht₃ q
    exact finite_sheafCohomology_X₂_of_shortExact hS q
  finite_of_isProper B hX _ _ hπ hcon q := by
    obtain ⟨hc₁, hc₃⟩ := hc B hX hcon
    have := h₁.finite_of_isProper B hX hπ hc₁ q
    have := h₃.finite_of_isProper B hX hπ hc₃ q
    exact finite_sheafCohomology_X₂_of_shortExact hS q
  bijective_of_isPrimeToCharacteristicTorsion htor k' _ _ _ _ _ q :=
    bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion
      (scalarExtensionFst k k' π) (ringExpChar k) hS
      (fun h ↦ h₁.bijective_of_isPrimeToCharacteristicTorsion h k')
      (fun h ↦ h₃.bijective_of_isPrimeToCharacteristicTorsion h k') htor q
  bijective_of_isProper hπ k' _ _ _ _ _ q :=
    etaleCohomologyRestrictionMap_bijective_of_shortExact.{u, v, w}
      (scalarExtensionFst k k' π) hS (h₁.bijective_of_isProper hπ k')
      (h₃.bijective_of_isProper hπ k') q
  surjective U _ :=
    surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_vanishing U.ι hS
      h₁.vanishing (h₁.surjective U) (h₃.surjective U)

end Stacks.EtaleCohomology

end
