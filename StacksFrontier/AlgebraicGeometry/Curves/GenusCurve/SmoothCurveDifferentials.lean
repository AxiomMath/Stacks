module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafSmoothCurve
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.F6Rank136.SmoothIsNodal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension

/-!
# Differentials on a smooth proper curve

Let `X` be a smooth proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`, and let `g` be its genus.
Then `dim_k H⁰(X, Ω_{X/k}) = g` and `deg(Ω_{X/k}) = 2g - 2` ([Stacks, Tag 0C1A]).

## Main results

All in the namespace `AlgebraicGeometry`.

* `isInvertible_dualizingSheafOverField_of_isCurve`: the dualizing sheaf of a smooth proper curve
  is invertible.
* `finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus`: `dim_k H⁰(X, Ω_{X/k}) = g`.
* `curveDegree_relativeDifferentials_eq_two_mul_genus_sub_two`: `deg(Ω_{X/k}) = 2g - 2`.
* `finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus_and_curveDegree`: the two
  together, [Stacks, Tag 0C1A].

## Implementation notes

The proof is that of the source: `Ω_{X/k} ≅ ω_X` by clause (6) of [Stacks, Tag 0BS2]
(`Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials`), so the two formulas
are `dim_k H⁰(X, ω_X) = g` ([Stacks, Tag 0BY8]) and `deg(ω_X) = 2g - 2` ([Stacks, Tag 0C19]).
Invertibility of `ω_X`, which the latter needs, comes from that of `Ω_{X/k}`
([Stacks, Tags 02G1, 0B8M]).

## References

* [Stacks Project, Tag 0C1A](https://stacks.math.columbia.edu/tag/0C1A)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0C19](https://stacks.math.columbia.edu/tag/0C19)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsCurve k pX]
  [Smooth pX] [IsProper pX]

/-- `Ω_{X/k}` of a smooth curve is invertible, being finite locally free of rank one. -/
private theorem isInvertible_relativeDifferentials_of_isCurve {Y : Scheme.{u}}
    (qY : Y ⟶ Spec (.of k)) [IsCurve k qY] [Smooth qY] :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Scheme.Hom.relativeDifferentials qY) := by
  have := smoothOfRelativeDimension_one_of_isCurve k qY
  have := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials qY
  exact Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one Y.toRingedSpace _

/-- **The dualizing sheaf of a smooth proper curve is invertible**: it is isomorphic to
`Ω_{X/k}` (clause (6) of [Stacks, Tag 0BS2]), which is finite locally free of rank one. -/
theorem isInvertible_dualizingSheafOverField_of_isCurve :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField pX) := by
  have := smoothOfRelativeDimension_one_of_isCurve k pX
  have := isInvertible_relativeDifferentials_of_isCurve pX
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _
    (Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials pX).some.symm

/-- **`dim_k H⁰(X, Ω_{X/k}) = g`** for a smooth proper curve `X` over `k` with
`H⁰(X, 𝒪_X) = k`: `Ω_{X/k} ≅ ω_X` and `dim_k H⁰(X, ω_X) = g` ([Stacks, Tag 0BY8]). -/
theorem finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop)] :
    Module.finrank k (cohomologyOverField k pX (Scheme.Hom.relativeDifferentials pX) 0) =
      genus pX := by
  have := smoothOfRelativeDimension_one_of_isCurve k pX
  rw [← finrank_cohomologyOverField_eq_of_iso k pX
    (Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials pX).some 0]
  exact Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField pX
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := pX)))

/-- **`deg(Ω_{X/k}) = 2g - 2`** for a smooth proper curve `X` over `k` with `H⁰(X, 𝒪_X) = k`:
`Ω_{X/k} ≅ ω_X` and `deg(ω_X) = 2g - 2` ([Stacks, Tag 0C19]). -/
theorem curveDegree_relativeDifferentials_eq_two_mul_genus_sub_two
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop)] :
    letI := smoothOfRelativeDimension_one_of_isCurve k pX
    letI := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials pX
    curveDegree k pX (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := pX)))
        (Scheme.Hom.relativeDifferentials pX) 1 = 2 * (genus pX : ℤ) - 2 := by
  let := smoothOfRelativeDimension_one_of_isCurve k pX
  let := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials pX
  have := isInvertible_dualizingSheafOverField_of_isCurve pX
  have := isInvertible_relativeDifferentials_of_isCurve pX
  have hdim : topologicalKrullDim X ≤ 1 := le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := pX))
  rw [← invertibleCurveDegree_eq_curveDegree k pX hdim,
    ← invertibleCurveDegree_eq_of_iso k pX hdim
      (Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials pX).some]
  exact invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k pX hdim

/-- **[Stacks, Tag 0C1A]**: for a smooth proper curve `X` over a field `k` with
`H⁰(X, 𝒪_X) = k` and genus `g`, `dim_k H⁰(X, Ω_{X/k}) = g` and `deg(Ω_{X/k}) = 2g - 2`. -/
@[stacks 0C1A]
theorem finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus_and_curveDegree
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop)] :
    Module.finrank k (cohomologyOverField k pX (Scheme.Hom.relativeDifferentials pX) 0) =
        genus pX ∧
      letI := smoothOfRelativeDimension_one_of_isCurve k pX
      letI := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials pX
      curveDegree k pX (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := pX)))
          (Scheme.Hom.relativeDifferentials pX) 1 = 2 * (genus pX : ℤ) - 2 :=
  ⟨finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus pX,
    curveDegree_relativeDifferentials_eq_two_mul_genus_sub_two pX⟩

end AlgebraicGeometry

end
