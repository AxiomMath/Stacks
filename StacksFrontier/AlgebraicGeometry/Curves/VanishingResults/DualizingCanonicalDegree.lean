module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
import StacksCore.Tactic.StacksAttribute

/-!
# The degree of the dualizing sheaf of a proper curve, and Riemann--Roch

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of
[Stacks, Tag 0BS2]. The degree of a finite locally free module of constant rank on such an `X`
is, by [Stacks, Tag 0AYR],

`deg(ℰ) = χ(X, ℰ) - rank(ℰ) · χ(X, 𝒪_X)`,

which is `AlgebraicGeometry.curveDegree`. This file reads clause (2) and the Riemann--Roch
formula of clause (3) of [Stacks, Tag 0BS6] off that definition together with
[Stacks, Tag 0BS5], `χ(X, 𝒪_X) = -χ(X, ω_X)`.

## Main results

The elided prefix is `AlgebraicGeometry.CohenMacaulayCurveSituation`.

* `finsum_alternating_finrank_dualizingSheaf_sub_unit_eq_neg_two_mul`:
  **`χ(X, ω_X) - χ(X, 𝒪_X) = -2 χ(X, 𝒪_X)`**, with nothing carried beyond Situation
  [Stacks, Tag 0B5D] itself.
* `curveDegree_dualizingSheafOverField_eq_neg_two_mul`: **clause (2) of [Stacks, Tag 0BS6]**,
  `deg(ω_X) = -2 χ(X, 𝒪_X)`.
* `two_mul_eulerCharacteristic_eq_two_mul_curveDegree_sub`: **the Riemann--Roch formula of
  clause (3) of [Stacks, Tag 0BS6]**, cleared of its denominator.

## Why the Chow-theoretic route is not needed

[Stacks, Tag 0BS6] proves its clause (2) by applying equation [Stacks, Tag 0BRZ] to `ω_X` and
comparing with [Stacks, Tag 0BS5], and then obtains the Riemann--Roch formula by putting that
back into [Stacks, Tag 0BRZ] for `ℰ`; equation [Stacks, Tag 0BRY] is what lets it write
`deg(c₁(ℰ) ∩ [X]₁)` as `deg(ℰ)`. Since
`AlgebraicGeometry.curveDegree` *is* the degree of [Stacks, Tag 0AYR], namely
`χ(X, ℰ) - rank(ℰ) · χ(X, 𝒪_X)`, equation [Stacks, Tag 0BRZ] at that spelling of the degree is
`AlgebraicGeometry.curveDegree_eq_eulerCharacteristic_sub`, which holds by `rfl`. So neither
[Stacks, Tag 0BRY] nor the first Chern class is used below, and in particular the hypotheses
`hcomponents` and `hintegral` that
`StacksFrontier/AlgebraicGeometry/Variety/Curve/RiemannRoch.lean` carries — the component formula
of [Stacks, Tag 0AYW] and the integral-curve half of [Stacks, Tag 0AZ3] — are not inputs here.

## The two hypotheses that are carried

*That `ω_X` is finite locally free of rank one.* This is clause (1) of [Stacks, Tag 0BS6], and
it is unavoidable for clause (2): the degree of [Stacks, Tag 0AYR] is only defined at a finite
locally free module of constant rank, so without it `deg(ω_X)` is not a term. It is taken as an
instance argument below, so that the statements hold at every curve of Situation
[Stacks, Tag 0B5D] at which `ω_X` is finite locally free of rank one. Under the hypotheses of
[Stacks, Tag 0BS6] — `X` Gorenstein and equidimensional of dimension one — it is proved, not
carried: clause (1) of the tag is
`Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein`, and the rank-one statement
is `Stacks.Duality.isFiniteLocallyFreeOfRank_one_dualizingSheafOverField_of_isGorenstein`, both of
`Curves/VanishingResults/GorensteinDualizingInvertible.lean`. The statements of the tag with that
instance discharged are in `Curves/VanishingResults/GorensteinCurveRiemannRoch.lean`.

*That `H⁰(X, 𝒪_X) = k`.* This is the last field of
`AlgebraicGeometry.CohenMacaulayCurveSituation`, Situation [Stacks, Tag 0B5D], and it is not
part of the setup of [Stacks, Tag 0BS6]: a proper Gorenstein `X` equidimensional of dimension
one may be disconnected, or have a finite extension of `k` as its ring of global sections. It
enters only through [Stacks, Tag 0BS5] as that tag is formalized, in
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.finsum_alternating_finrank_unit_eq_neg_dualizingSheaf`,
whose proof uses `dim_k H⁰(X, 𝒪_X) = 1` to see that the canonical injection of `H¹(X, ω_X)` into
`Hom_D(𝒪_X[0], ω_X^•)` is onto. Dropping it leaves only the inequality
`χ(X, ω_X) ≥ -χ(X, 𝒪_X)`.

*What is not carried.* The Gorenstein hypothesis of [Stacks, Tag 0BS6] is not used anywhere
below, and no dualizing-complex hypothesis is carried: both inputs — [Stacks, Tag 0BS5] and the
definition of the degree — are unconditional in their stated scope.

## Why nothing below carries an attribute of [Stacks, Tag 0BS6]

Each statement below proves strictly less than the tag says, because each takes among its
binders a hypothesis that is not part of the tag's setup, and in one case is a clause of the tag
itself. A registration of that shape would be a weakening, so such a statement is left untagged and
the documentation says exactly what it assumes, which is what the section above does. The two
members of the duality of dimensions at `i = 1` are proved with nothing assumed, in
`Curves/VanishingResults/DualizingDimensionDuality.lean` and
`Curves/VanishingResults/DualizingDimensionDualityBundle.lean`.

## Implementation notes

Euler characteristics appear in two spellings. `AlgebraicGeometry.eulerCharacteristic` needs the
module to be coherent, which for `ω_X` is an unproved part of clause (2) of [Stacks, Tag 0BS2];
so the statement that does not mention `curveDegree` writes both Euler characteristics as the
alternating sums of dimensions that define `AlgebraicGeometry.eulerCharacteristic`, exactly as
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.finsum_alternating_finrank_unit_eq_neg_dualizingSheaf`
does and for the same reason. `AlgebraicGeometry.curveDegree` is written at the same alternating
sums, so it too needs no coherence.

The Riemann--Roch formula of [Stacks, Tag 0BS6] has a factor `½`. It is stated below multiplied
through by two, so that it is an identity of integers rather than of rationals; the two sides of
the tag's formula are `χ(X, ℰ)` and `deg(ℰ) - ½ rank(ℰ) deg(ω_X)`, and the statement below is
twice each of them.

## References

* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0BS5](https://stacks.math.columbia.edu/tag/0BS5)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

/-- **`χ(X, ω_X) - χ(X, 𝒪_X) = -2 χ(X, 𝒪_X)`** in Situation [Stacks, Tag 0B5D], for the
canonical dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))`. This is clause (2) of
[Stacks, Tag 0BS6] with the degree of [Stacks, Tag 0AYR] replaced by its defining formula at
rank one, and it is immediate from [Stacks, Tag 0BS5]: that tag gives
`χ(X, 𝒪_X) = -χ(X, ω_X)`, so `χ(X, ω_X) - χ(X, 𝒪_X) = -χ(X, 𝒪_X) - χ(X, 𝒪_X)`.

Both Euler characteristics are written as the alternating sums of dimensions that define
`AlgebraicGeometry.eulerCharacteristic`, so that no coherence of `ω_X` is needed. -/
public theorem finsum_alternating_finrank_dualizingSheaf_sub_unit_eq_neg_two_mul
    (S : CohenMacaulayCurveSituation.{u}) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank S.k
          (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) n) : ℤ)) -
        (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank S.k
          (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) n) : ℤ)) =
      -2 * (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank S.k
        (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) n) : ℤ)) := by
  have h := finsum_alternating_finrank_unit_eq_neg_dualizingSheaf S
  linarith

/-- **Clause (2) of [Stacks, Tag 0BS6]:** `deg(ω_X) = -2 χ(X, 𝒪_X)` for the canonical dualizing
sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` of a proper curve in Situation [Stacks, Tag 0B5D], with
`deg` the degree of [Stacks, Tag 0AYR].

The degree of [Stacks, Tag 0AYR] at rank one is `χ(X, ω_X) - χ(X, 𝒪_X)` by definition, so this
is `finsum_alternating_finrank_dualizingSheaf_sub_unit_eq_neg_two_mul` above. The instance
argument saying that `ω_X` is finite locally free of rank one is clause (1) of the same tag; it
is what makes `deg(ω_X)` a term at all. It is carried here, and proved for a Gorenstein `X`
equidimensional of dimension one by
`Stacks.Duality.isFiniteLocallyFreeOfRank_one_dualizingSheafOverField_of_isGorenstein`. See the
module documentation for both of the hypotheses that are carried. -/
public theorem curveDegree_dualizingSheafOverField_eq_neg_two_mul
    (S : CohenMacaulayCurveSituation.{u})
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Duality.dualizingSheafOverField S.f) 1] :
    curveDegree S.k S.f (le_of_eq S.dimension_one)
        (Stacks.Duality.dualizingSheafOverField S.f) 1 =
      -2 * (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank S.k
        (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) n) : ℤ)) := by
  unfold curveDegree
  rw [Nat.cast_one, one_mul]
  exact finsum_alternating_finrank_dualizingSheaf_sub_unit_eq_neg_two_mul S

/-- **The Riemann--Roch formula of clause (3) of [Stacks, Tag 0BS6]**, cleared of its
denominator:

`2 χ(X, ℰ) = 2 deg(ℰ) - rank(ℰ) deg(ω_X)`

for a finite locally free `ℰ` of constant rank on a proper curve in Situation
[Stacks, Tag 0B5D], with `deg` the degree of [Stacks, Tag 0AYR] and
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))`. The tag states `χ(X, ℰ) = deg(ℰ) - ½ rank(ℰ) deg(ω_X)`; both
sides are multiplied by two so that the identity is one of integers.

The proof is the definition of the degree, `deg(ℰ) = χ(X, ℰ) - rank(ℰ) χ(X, 𝒪_X)`, together
with clause (2) in the form `deg(ω_X) = -2 χ(X, 𝒪_X)`: the two occurrences of `χ(X, 𝒪_X)`
cancel. The hypotheses that are carried are those of
`curveDegree_dualizingSheafOverField_eq_neg_two_mul`. -/
public theorem two_mul_eulerCharacteristic_eq_two_mul_curveDegree_sub
    (S : CohenMacaulayCurveSituation.{u}) (E : S.X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] [E.IsCoherent]
    [(SheafOfModules.unit S.X.ringCatSheaf).IsCoherent]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Duality.dualizingSheafOverField S.f) 1] :
    2 * eulerCharacteristic S.k S.f E =
      2 * curveDegree S.k S.f (le_of_eq S.dimension_one) E r -
        (r : ℤ) * curveDegree S.k S.f (le_of_eq S.dimension_one)
          (Stacks.Duality.dualizingSheafOverField S.f) 1 := by
  have hu : eulerCharacteristic S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank S.k
        (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) n) : ℤ) := rfl
  rw [curveDegree_eq_eulerCharacteristic_sub S.k S.f (le_of_eq S.dimension_one) E r,
    curveDegree_dualizingSheafOverField_eq_neg_two_mul S, hu]
  ring

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
