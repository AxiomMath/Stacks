module

public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EmptySupport
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProperVanishing

/-!
# Additivity of the degree along a short exact sequence

On a scheme proper over a field and of dimension at most one, the degree of a finite locally
free sheaf of constant rank is additive along a short exact sequence: for
`0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0` with constant ranks `r₁`, `r₂`, `r₃`,

`deg(ℰ₂) = deg(ℰ₁) + deg(ℰ₃)`.

This is the statement of [Stacks, Tag 0AYS]. **No `@[stacks 0AYS]` attribute is attached in this
file**, because the theorem below carries one hypothesis the source does not: finite
dimensionality of the cohomology of the two outer sheaves, which is the content of
[Stacks, Tag 02O6]. Tagging a statement with
an extra hypothesis would record a weaker result as the tag. Everything else that
[Stacks, Tag 0AYS] needs is proved here or already available:

* additivity of the Euler characteristic, [Stacks, Tag 08AA], in the form
  `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional'`, whose own
  vanishing input is discharged;
* additivity of the constant rank,
  `AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact`, which is where the dimension of
  the three sheaves enters and which needs a point of the scheme;
* the degenerate case of the empty scheme, where the rank need not be additive at all and the
  Euler characteristic of the structure sheaf vanishes instead.

So the only thing standing between this file and the tag was [Stacks, Tag 02O6], and that is
now a theorem: `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper` of
`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/OverFieldProper.lean`, the
`cohomologyOverField` spelling of
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`.
Both hypotheses below are therefore discharged, downstream of that proof, by
`AlgebraicGeometry.curveDegree_add_of_shortExact_of_isProper` in
`StacksFrontier/AlgebraicGeometry/Variety/Curve/DegreeAdditivityUnconditional.lean`, which is where
[Stacks, Tag 0AYS] is attached; the same discharge turns
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional'` into
[Stacks, Tag 08AA] in
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/AdditivityUnconditional.lean`. The hypotheses
are kept in this file because the proof of [Stacks, Tag 02O6] cannot be imported into its import
closure: see the implementation notes of that second file.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_eq_zero_of_isEmpty`: the Euler characteristic of a
  sheaf on the empty scheme vanishes.
* `AlgebraicGeometry.curveDegree_add_of_shortExact_of_finiteDimensional`: the statement of
  [Stacks, Tag 0AYS], with finite dimensionality of the cohomology of the outer two sheaves
  assumed below the covering bound.

## Implementation notes

The degree is `AlgebraicGeometry.curveDegree`, which takes the rank as an explicit argument and
the dimension bound as a proof argument used by neither the definition nor this proof; the
dimension bound is carried only so that the statement is about degrees on a curve, as the source
states it.

The case split on whether the scheme is nonempty is the source's own: rank additivity is proved
at a point, so it is unavailable on the empty scheme. There it is also unnecessary, since a
sheaf of modules on a scheme with no points is a zero object and the Euler characteristic of the
structure sheaf is zero, which makes the rank coefficient irrelevant.

The two finite-dimensionality hypotheses are bounded by the affine covering number
`AlgebraicGeometry.Scheme.affineCoverNum` of the scheme, the degree beyond which the cohomology
of every quasi-coherent sheaf vanishes, because that is the shape in which
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional'` consumes them.

## References

* [Stacks Project, Tag 0AYS](https://stacks.math.columbia.edu/tag/0AYS)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open Stacks.AlgebraicGeometry.CurveEulerBridge

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The Euler characteristic of a sheaf on the empty scheme is zero.** A sheaf of modules on a
scheme with no points has every stalk zero, hence is a zero object, and the Euler
characteristic of a zero object vanishes. -/
public theorem eulerCharacteristic_eq_zero_of_isEmpty [IsProper f] [IsEmpty X] (G : X.Modules)
    (hG : SheafOfModules.IsCoherent G) : @eulerCharacteristic k _ X f _ G hG = 0 :=
  eulerCharacteristic_eq_zero_of_isZero k f G hG
    (isZero_of_forall_isZero_stalk G fun x => isEmptyElim x)

/-- **[Stacks, Tag 0AYS] with the finite-dimensionality input of [Stacks, Tag 02O6] assumed for
the outer two sheaves.** For a short exact sequence `0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0` of finite locally
free sheaves of constant ranks `r₁`, `r₂`, `r₃` on a scheme proper over a field and of
dimension at most one, `deg(ℰ₂) = deg(ℰ₁) + deg(ℰ₃)`.

On a nonempty scheme the proof is additivity of the Euler characteristic together with
`r₂ = r₁ + r₃` at any point; on the empty scheme the Euler characteristic of the structure
sheaf is zero, so rank additivity is not needed. -/
public theorem curveDegree_add_of_shortExact_of_finiteDimensional [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (r₁ r₂ r₃ : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r₂]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₃]
    (hfin₁ : ∀ n < X.affineCoverNum ⊤, FiniteDimensional k (cohomologyOverField k f S.X₁ n))
    (hfin₃ : ∀ n < X.affineCoverNum ⊤, FiniteDimensional k (cohomologyOverField k f S.X₃ n)) :
    curveDegree k f hdim S.X₂ r₂ =
      curveDegree k f hdim S.X₁ r₁ + curveDegree k f hdim S.X₃ r₃ := by
  have : S.X₁.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank k f S.X₁ r₁
  have : S.X₂.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank k f S.X₂ r₂
  have : S.X₃.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank k f S.X₃ r₃
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent := isCoherent_unit k f
  simp only [curveDegree_eq_eulerCharacteristic_sub]
  rw [eulerCharacteristic_add_of_shortExact_of_finiteDimensional' k f hS hfin₁ hfin₃]
  rcases isEmpty_or_nonempty X with _ | ⟨⟨x⟩⟩
  · rw [eulerCharacteristic_eq_zero_of_isEmpty k f _ (isCoherent_unit k f)]
    ring
  · rw [SheafOfModules.rank_add_of_shortExact S hS r₁ r₂ r₃ x, Nat.cast_add]
    ring

end AlgebraicGeometry

end
