module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochFull
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantTopPower
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0DJ5]: `deg(ℰ) = deg(⋀ⁿ ℰ) = deg(det(ℰ))`

Let `k` be a field, `X` a proper scheme of dimension at most one over `k` and `ℰ` a finite
locally free `𝒪_X`-module of constant rank `n`. This file proves both equalities of
[Stacks, Tag 0DJ5],

`deg(ℰ) = deg(⋀ⁿ ℰ)` and `deg(⋀ⁿ ℰ) = deg(det(ℰ))`,

in one theorem and under exactly those hypotheses. Here `det(ℰ)` is the determinant of
[Stacks, Tag 0FJN] — the annihilator of the degree-one part of the exterior algebra — and its
invertibility, which the degree of an invertible module needs, is *derived* from the rank of `ℰ`
rather than assumed.

## Main definitions

The elided prefix throughout is `AlgebraicGeometry`.

* `Scheme.Modules.determinant`: the determinant `det(ℱ)` of a sheaf of modules on a scheme, the
  [Stacks, Tag 0FJN] determinant `SheafOfModules.TensorExteriorSymmetricAlgebras.determinant` of
  the chosen package of algebras `SheafOfModules.algebras` that
  `AlgebraicGeometry.Scheme.Modules.exteriorPower` is also defined from.

## Main results

* `Scheme.Modules.exteriorPowerIsoDeterminant`: `⋀ⁿ ℰ ≅ det(ℰ)` for `ℰ` of constant rank `n`.
* `Scheme.Modules.isFiniteLocallyFreeOfRank_determinant` and
  `Scheme.Modules.isInvertible_determinant`: `det(ℰ)` is of rank one, hence invertible.
* `curveDegree_eq_curveDegree_exteriorPower_eq_invertibleCurveDegree_determinant`:
  **[Stacks, Tag 0DJ5]**, both equalities at once.

## Implementation notes

**Which determinant.** `det(ℰ)` is read here as the determinant of [Stacks, Tag 0FJN],
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant`: the direct sum over the degrees of
the annihilators of the degree-one part of `⋀(ℰ)`, which is the only object in this repository
called a determinant of a sheaf of modules. That it agrees with the top exterior power at
constant rank is [Stacks, Tag 0B37],
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoExteriorPower`, and that
identification is what carries the second equality. So the second equality is not a restatement
of `deg` at two spellings of one object: the two sheaves of modules are built differently and are
compared by a theorem.

**Nothing about `det(ℰ)` is assumed.** `AlgebraicGeometry.invertibleCurveDegree` takes the
invertibility of its argument as an instance, and Tag 0DJ5 does not assume it, so it is derived:
`det(ℰ)` is of rank one because `⋀ⁿ ℰ` is
(`Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self`) and the two are isomorphic, and a
sheaf of modules of rank one on a ringed space is invertible by clause 1 of [Stacks, Tag 0B8M].
The route through [Stacks, Tag 0FJN] itself —
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant_isInvertible_of_isFlat` — would need
flatness and finite presentation of `ℰ`, which local freeness of course gives, but the rank-one
route needs neither and is the one the source's own proof of this lemma takes.

**Rank zero is covered**, by both halves: at rank zero `ℰ` is a zero object, `⋀⁰ ℰ ≅ 𝒪_X`, both
degrees vanish (`AlgebraicGeometry.curveDegree_eq_curveDegree_exteriorPower_of_isProper` splits
on the rank), and `det(ℰ) ≅ ⋀⁰ ℰ` since the degree-zero annihilator is the whole of `⋀⁰ ℰ` and
the others vanish.

**The two spellings of the structure sheaf of rings.** A scheme's sheaf of modules lives over
`AlgebraicGeometry.Scheme.ringCatSheaf` while the site-level determinant is stated over
`CategoryTheory.Sheaf.toRingCat`; the two are definitionally equal but do not match at reducible
transparency, so the rank hypothesis is restated at the second spelling before
`determinantIsoExteriorPower` is applied, exactly as in
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower`.

## References

* [Stacks Project, Tag 0DJ5](https://stacks.math.columbia.edu/tag/0DJ5)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The determinant `det(ℱ)` of a sheaf of modules on a scheme**: the determinant of
[Stacks, Tag 0FJN], the annihilator of the degree-one part of the exterior algebra, taken for the
chosen package of algebras `SheafOfModules.algebras` — the same package
`AlgebraicGeometry.Scheme.Modules.exteriorAlgebra` is defined from. -/
noncomputable abbrev determinant {X : Scheme.{u}} (F : X.Modules) : X.Modules :=
  (_root_.SheafOfModules.algebras _ F).determinant

/-- **`⋀ⁿ ℱ ≅ det(ℱ)` for `ℱ` finite locally free of constant rank `n`**: [Stacks, Tag 0B37] at
the scheme-level spellings of the exterior power and the determinant. This is
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoExteriorPower` for the package
`SheafOfModules.algebras`, with the rank hypothesis restated over
`CategoryTheory.Sheaf.toRingCat`. -/
@[sga "3 XV 5.7" "special case", sga "6 X 5.1" "special case"]
noncomputable def exteriorPowerIsoDeterminant {X : Scheme.{u}} (F : X.Modules) (n : ℕ)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F n] :
    exteriorPower F (n : ℤ) ≅ determinant F :=
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (_root_.Opens.grothendieckTopology X) X.sheaf) F n := hF
  (_root_.SheafOfModules.algebras _ F).determinantIsoExteriorPower n

/-- **The determinant of a module of constant rank `n` has rank one**, being isomorphic to the
top exterior power `⋀ⁿ ℱ`, whose rank is `binom(n, n) = 1`. -/
@[sga "6 X 5.1" "special case"]
theorem isFiniteLocallyFreeOfRank_determinant {X : Scheme.{u}} (F : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F n] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (determinant F) 1 :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (exteriorPowerIsoDeterminant F n)
    (isFiniteLocallyFreeOfRank_exteriorPower_self F n)

/-- **The determinant of a module of constant rank is invertible.** Its rank is one, and a sheaf
of modules of rank one on a ringed space is invertible by clause 1 of [Stacks, Tag 0B8M]. No
flatness or finite presentation is needed, so this is not the route of [Stacks, Tag 0FJN]. -/
theorem isInvertible_determinant {X : Scheme.{u}} (F : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F n] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (determinant F) :=
  have := isFiniteLocallyFreeOfRank_determinant F n
  Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0DJ5].** Let `k` be a field, `X` a proper scheme of dimension at most one over
`k` and `ℰ` a finite locally free `𝒪_X`-module of constant rank `n`. Then

`deg(ℰ) = deg(⋀ⁿ ℰ) = deg(det(ℰ))`.

Both equalities are asserted, under exactly the source's hypotheses. `det(ℰ)` is the determinant
of [Stacks, Tag 0FJN], `AlgebraicGeometry.Scheme.Modules.determinant`, and its invertibility —
which `AlgebraicGeometry.invertibleCurveDegree` needs and the source does not assume — is derived
from the rank of `ℰ` by `AlgebraicGeometry.Scheme.Modules.isInvertible_determinant`.

The first equality is
`AlgebraicGeometry.curveDegree_eq_curveDegree_exteriorPower_of_isProper`: the source's dévissage
on a proper curve, passed to `X` through the one-dimensional components ([Stacks, Tag 0AYW]). The
second is the identification `⋀ⁿ ℰ ≅ det(ℰ)` of [Stacks, Tag 0B37] together with the agreement of
the invertible degree with the rank-one degree. -/
@[stacks 0DJ5]
theorem curveDegree_eq_curveDegree_exteriorPower_eq_invertibleCurveDegree_determinant
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] :
    curveDegree k f hdim E n =
        @curveDegree k _ X f _ hdim (Scheme.Modules.exteriorPower E (n : ℤ)) 1
          (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E n) ∧
      @curveDegree k _ X f _ hdim (Scheme.Modules.exteriorPower E (n : ℤ)) 1
          (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E n) =
        @invertibleCurveDegree k _ X f _ hdim (Scheme.Modules.determinant E)
          (Scheme.Modules.isInvertible_determinant E n) := by
  have := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E n
  have := Scheme.Modules.isFiniteLocallyFreeOfRank_determinant E n
  have := Scheme.Modules.isInvertible_determinant E n
  refine ⟨curveDegree_eq_curveDegree_exteriorPower_of_isProper k f hdim n E, ?_⟩
  rw [invertibleCurveDegree_eq_curveDegree]
  exact curveDegree_eq_of_iso k f hdim 1 (Scheme.Modules.exteriorPowerIsoDeterminant E n)

end AlgebraicGeometry

end
