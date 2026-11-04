module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SmoothCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafInvertible
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RiemannRochEffective
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing sheaf of a smooth proper curve: sections and degree

Let `k` be a field and `X` a smooth proper curve over `k` with `H⁰(X, 𝒪_X) = k`, and let
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of [Stacks, Tag 0BS2]. This file proves

* `dim_k H⁰(X, ω_X) = g`, the genus of `X`;
* together with `deg(ω_X) = 2g - 2`, that `ω_X` is an invertible module with `g` independent
  global sections and degree `2g - 2`;
* hence, for `g ≥ 1`, that `ω_X` together with all of its global sections is a linear series
  `𝔤^{g-1}_{2g-2}` in the sense of [Stacks, Tag 0CCN].

Invertibility of `ω_X` is `AlgebraicGeometry.isInvertible_dualizingSheafOverField_of_isCurve` and
its degree is `AlgebraicGeometry.invertibleCurveDegree_dualizingSheafOverField_of_isInvertible`.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_zero_dualizingSheafOverField_eq_genus`:
  `dim_k H⁰(X, ω_X) = g`. This holds in Situation [Stacks, Tag 0B5D] at a curve, with no
  smoothness: it is clause (5) of [Stacks, Tag 0BS2] at `ℱ = 𝒪_X` together with
  `Hom(𝒪_X, ω_X) = H⁰(X, ω_X)`.
* `AlgebraicGeometry.finsum_alternating_finrank_unit_eq_one_sub_genus`: `χ(𝒪_X) = 1 - g`.
* `AlgebraicGeometry.exists_isInvertible_finrank_eq_genus_invertibleCurveDegree_eq`: an
  invertible module with `h⁰ = g` and degree `2g - 2`.
* `AlgebraicGeometry.nonempty_linearSeries_dualizingSheafOverField`: for `g ≥ 1`, a linear
  series `𝔤^{g-1}_{2g-2}`.

No Stacks attribute is attached: these are the smooth cases of [Stacks, Tag 0C19] and the
identification of [Stacks, Tag 0BS6], which are stated in the source for Gorenstein curves and
are not these statements.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0C19](https://stacks.math.columbia.edu/tag/0C19)
* [Stacks Project, Tag 0CCN](https://stacks.math.columbia.edu/tag/0CCN)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`dim_k H⁰(X, ω_X) = g`** for a proper curve `X` over `k` with `H⁰(X, 𝒪_X) = k`, where
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))`. Clause (5) of [Stacks, Tag 0BS2] at `ℱ = 𝒪_X` identifies
`H⁰(X, ω_X) = Hom(𝒪_X, ω_X)` with the dual of `H¹(X, 𝒪_X)`. -/
theorem finrank_cohomologyOverField_zero_dualizingSheafOverField_eq_genus [IsCurve k f]
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    Module.finrank k (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0) =
      genus f :=
  (CohenMacaulayCurveSituation.finrank_cohomologyOverField_zero_dualizingSheaf_eq_finrank_unit_one
    (cohenMacaulayCurveSituationOfIsCurve f)).trans
    (genus_eq_finrank_cohomologyOverField_unit_one' k f).symm

/-- **`χ(X, 𝒪_X) = 1 - g`** on a proper curve with `H⁰(X, 𝒪_X) = k`, written as the alternating
sum of dimensions that defines the Euler characteristic. -/
theorem finsum_alternating_finrank_unit_eq_one_sub_genus [IsCurve k f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) : ℤ)) =
      1 - (genus f : ℤ) := by
  have h1 := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f
    (SheafOfModules.unit X.ringCatSheaf) fun m hm =>
      isZero_cohomologyOverField_of_topologicalKrullDim_le k f _ (d := 1)
        (le_of_eq (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f))) (by omega)
  rw [h1, finrank_cohomologyOverField_unit_zero_eq_one f,
    genus_eq_finrank_cohomologyOverField_unit_one' k f]
  push_cast
  ring

/-- **A smooth proper curve with `H⁰(X, 𝒪_X) = k` carries an invertible module with `g`
independent global sections and degree `2g - 2`**: the dualizing sheaf `ω_X`. -/
theorem exists_isInvertible_finrank_eq_genus_invertibleCurveDegree_eq [IsCurve k f] [Smooth f]
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      Module.finrank k (cohomologyOverField k f L 0) = genus f ∧
        invertibleCurveDegree k f hdim L = 2 * (genus f : ℤ) - 2 :=
  have := isInvertible_dualizingSheafOverField_of_isCurve f
  ⟨Stacks.Duality.dualizingSheafOverField f, inferInstance,
    finrank_cohomologyOverField_zero_dualizingSheafOverField_eq_genus f,
    invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k f hdim⟩

/-- **A smooth proper curve of genus `g ≥ 1` with `H⁰(X, 𝒪_X) = k` has a linear series
`𝔤^{g-1}_{2g-2}`** ([Stacks, Tag 0CCN]): the dualizing sheaf `ω_X`, of degree `2g - 2`, with the
whole of its `g`-dimensional space of global sections. -/
theorem nonempty_linearSeries_dualizingSheafOverField [IsCurve k f] [Smooth f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1)
    (hg : 1 ≤ genus f) :
    Nonempty (LinearSeries k f hdim (2 * genus f - 2) (genus f - 1)) :=
  have := isInvertible_dualizingSheafOverField_of_isCurve f
  ⟨{ L := Stacks.Duality.dualizingSheafOverField f
     isInvertible := inferInstance
     degree_eq := by
       rw [invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k f hdim]
       omega
     V := ⊤
     finrank_eq := by
       rw [finrank_top, finrank_cohomologyOverField_zero_dualizingSheafOverField_eq_genus f]
       omega }⟩

end AlgebraicGeometry
