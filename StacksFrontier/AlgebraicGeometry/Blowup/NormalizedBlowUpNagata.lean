module

public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata

/-!
# The normalized blowup of a Nagata scheme at a closed point

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components, let `x`
be a closed point of `X`, and assume `X` is Nagata. Then the normalized blowup of `X` at `x` is
a normal Nagata scheme, proper over `X`.

## Main results

* `Stacks.Blowup.isNormal_normalizedBlowUpScheme`: the normalized blowup is normal.
* `Stacks.Blowup.isNagataScheme_normalizedBlowUpScheme`: the normalized blowup is Nagata.
* `Stacks.Blowup.isProper_normalizedBlowUp`: the normalized blowup is proper over `X`.

## Implementation notes

A Nagata scheme is locally Noetherian, so the blowup of `X` at `x` is proper over `X`, hence
locally of finite type over `X`, hence again Nagata; its normalization is therefore finite, and
so the normalized blowup is Nagata and is proper over `X` as a composite of a finite and a
proper morphism. Normality holds for the normalization of any scheme whose quasi-compact opens
have finitely many irreducible components, and needs no Nagata hypothesis.

## References

* [Stacks Project, Tag 0BFT](https://stacks.math.columbia.edu/tag/0BFT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Blowup

/-- The ideal sheaf of the reduced closed subscheme supported at a closed point, which is the
centre of the blowup underlying the normalized blowup at that point. -/
private abbrev pointIdeal {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X)) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)

/-- Quasi-compact opens of the blowup at a closed point have finitely many irreducible
components. -/
private theorem finite_irreducibleComponents_blowUp_pointIdeal {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∀ U : (AlgebraicGeometry.blowUp (pointIdeal x hx)).Opens,
      IsCompact (U : Set (AlgebraicGeometry.blowUp (pointIdeal x hx))) →
      (irreducibleComponents U).Finite :=
  finite_irreducibleComponents_blowUp (pointIdeal x hx) hX

/-- **Stacks Project, Tag 0BFT.** The normalized blowup of `X` at a closed point is a normal
scheme: it is by construction the normalization of the blowup of `X` at that point. -/
@[stacks 0BFT "normal"]
instance isNormal_normalizedBlowUpScheme {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsNormal (normalizedBlowUpScheme X hX x hx) :=
  Scheme.isNormal_normalizationScheme (AlgebraicGeometry.blowUp (pointIdeal x hx))
    (finite_irreducibleComponents_blowUp_pointIdeal hX x hx)

/-- A Nagata scheme is locally Noetherian. -/
private theorem isLocallyNoetherian_of_isNagataScheme {X : Scheme.{u}} (h : IsNagataScheme X) :
    IsLocallyNoetherian X :=
  ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme X).mp h).1

/-- The blowup of a Nagata scheme at a closed point is Nagata: a Nagata scheme is locally
Noetherian, so the blowup is proper and hence locally of finite type over it. -/
private theorem isNagataScheme_blowUp_pointIdeal {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) (hNagata : IsNagataScheme X) :
    IsNagataScheme (AlgebraicGeometry.blowUp (pointIdeal x hx)) := by
  have := isLocallyNoetherian_of_isNagataScheme hNagata
  exact isNagataScheme_of_locallyOfFiniteType
    (AlgebraicGeometry.blowUpToBase (pointIdeal x hx)) hNagata

/-- The normalization of the blowup of a Nagata scheme at a closed point is finite: the blowup is
Nagata, and the normalization of a Nagata scheme is finite. -/
private theorem isFinite_normalization_blowUp_pointIdeal {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) (hNagata : IsNagataScheme X) :
    IsFinite (Scheme.normalization (AlgebraicGeometry.blowUp (pointIdeal x hx))
      (finite_irreducibleComponents_blowUp_pointIdeal hX x hx)) :=
  Scheme.isFinite_normalization (isNagataScheme_blowUp_pointIdeal x hx hNagata)
    (finite_irreducibleComponents_blowUp_pointIdeal hX x hx)

/-- **Stacks Project, Tag 0BFT.** The normalized blowup of a Nagata scheme at a closed point is
Nagata: the blowup is Nagata because it is of finite type over `X`, and the normalization of a
Nagata scheme is finite, hence again of finite type. -/
@[stacks 0BFT "Nagata"]
theorem isNagataScheme_normalizedBlowUpScheme {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) (hNagata : IsNagataScheme X) :
    IsNagataScheme (normalizedBlowUpScheme X hX x hx) :=
  have := isFinite_normalization_blowUp_pointIdeal hX x hx hNagata
  isNagataScheme_of_locallyOfFiniteType
    (Scheme.normalization (AlgebraicGeometry.blowUp (pointIdeal x hx))
      (finite_irreducibleComponents_blowUp_pointIdeal hX x hx))
    (isNagataScheme_blowUp_pointIdeal x hx hNagata)

/-- **Stacks Project, Tag 0BFT.** The normalized blowup of a Nagata scheme at a closed point is
proper over it: the blowup is proper because `X` is locally Noetherian, and the normalization of
the blowup is finite because the blowup is Nagata. -/
@[stacks 0BFT "proper over the base"]
theorem isProper_normalizedBlowUp {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) (hNagata : IsNagataScheme X) :
    IsProper (normalizedBlowUp X hX x hx) :=
  have := isLocallyNoetherian_of_isNagataScheme hNagata
  have := isFinite_normalization_blowUp_pointIdeal hX x hx hNagata
  inferInstanceAs (IsProper
    (Scheme.normalization (AlgebraicGeometry.blowUp (pointIdeal x hx))
        (finite_irreducibleComponents_blowUp_pointIdeal hX x hx) ≫
      AlgebraicGeometry.blowUpToBase (pointIdeal x hx)))

end Stacks.Blowup

end
