module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthPointIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions

/-!
# The length of a quasi-coherent module at a point of the space is unchanged by a closed
immersion

Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over a scheme `S`, let `G` be a
quasi-coherent `𝒪_X`-module, let `x` be a point of `|X|` and let
`d ∈ ℕ∞ = {0, 1, 2, …, ∞}`. Stacks 0EE3 asserts that `G` has length `d` at `x` exactly when
`f_*G` has length `d` at the image of `x` in `|Y|`. This file proves that equivalence at a
point of the point set, which is the form the source states; the source writes the closed
immersion `i : Y → X` with its module on the source `Y`, so its `y ∈ |Y|` is the point `x` of
`|X|` here and its `x ∈ |X|` is the image point.

The phrase "has length `d` at a point of the space" is Stacks 0EE2, and it is a *definition*:
the length of `F` at a geometric point above the point, which Stacks 0EE1 says does not depend
on which geometric point above it is taken. So this file begins by making that value a
declaration. `AlgebraicGeometry.Space.lengthAtPoint` is the length of `F` at the geometric
point above the given point that Stacks 0488, part (1)
(`AlgebraicGeometry.Space.exists_geometricRepresentative`) produces, and
`AlgebraicGeometry.Space.lengthAtPoint_eq_geometricLength` says that for a quasi-coherent `F`
it is the length at *any* geometric point above the point — that is where Stacks 0EE1
(`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`) enters, and it is what makes the
definition well posed. "`F` has length `d` at `x`" is then `lengthAtPoint … F = d`.

Two further facts turn the statement at a geometric point, which is
`AlgebraicGeometry.Space.geometricLength_chartDirectImage` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionGeometricLength.lean`, into the statement
at a point of the space. The first is that `f_*G` is quasi-coherent, so that Stacks 0EE1
applies to it as well and `lengthAtPoint` is well posed on the target: a closed immersion is
affine (`AlgebraicGeometry.Space.isAffineHom_of_isClosedImmersion`) and the direct image of a
quasi-coherent module along an affine morphism is quasi-coherent, which is the first assertion
of Stacks 07U8
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallBaseChangeModulePushforward_of_isAffineHom`).
The second is that a geometric point above `x` is carried by `f` to a geometric point above
the image of `x` (`AlgebraicGeometry.Space.geometricPointMap_image`), so one geometric point
computes both sides at once.

## Main definitions

* `AlgebraicGeometry.Space.lengthAtPoint`: **the length of a module at a point of the space**,
  the value whose being `d` is "has length `d` at that point" in the sense of Stacks 0EE2. It
  is the length at a geometric point above the point, for a choice of such a point; the choice
  is immaterial for a quasi-coherent module by Stacks 0EE1.

## Main results

* `AlgebraicGeometry.Space.lengthAtPoint_eq_geometricLength`: **Stacks 0EE1 read as the
  well-posedness of `AlgebraicGeometry.Space.lengthAtPoint`.** For a quasi-coherent `F` the
  length of `F` at a point of the space is its length at every geometric point above it.
* `AlgebraicGeometry.Space.geometricLength_chartDirectImage_of_liesOver`: for a quasi-coherent
  `G`, the length of `f_*G` at a geometric point above the image of `x` equals the length of
  `G` at a geometric point above `x`, for *any* choice of the two geometric points.
* `AlgebraicGeometry.Space.lengthAtPoint_chartDirectImage`: the length of `f_*G` at the image
  of `x` equals the length of `G` at `x`, as lengths at points of the spaces.
* `AlgebraicGeometry.Space.lengthAtPoint_chartDirectImage_iff`: **Stacks 0EE3 at a point of
  the space.** `G` has length `d` at `x` exactly when `f_*G` has length `d` at the image of
  `x`, for every `d` in `ℕ∞ = {0, 1, 2, …, ∞}`.
* `AlgebraicGeometry.Space.geometricLength_chartDirectImage_iff_liesOver`: the same
  equivalence with each side unfolded into a condition on all geometric points above the
  point, which is how it reads once the definition of Stacks 0EE2 is spelled out.

## Implementation notes

**Why a definition and not a quantifier.** Writing each side of the equivalence as "the length
at every geometric point above the point is `d`" turns Stacks 0EE3 into an equivalence of two
universally quantified conditions, and such an equivalence can be proved without knowing that
either condition is independent of the geometric point: a geometric point above the point of
`|X|` exists, and a geometric point above the point of `|Y|` is handed to the proof. The
source's two conditions are not quantified — they are statements about a single well-defined
number attached to the point — so the number is introduced here and the equivalence is stated
for it. The quantified form is kept as
`AlgebraicGeometry.Space.geometricLength_chartDirectImage_iff_liesOver`, deduced from the
other, where it is a corollary rather than the statement.

**Why this is not in `ClosedImmersionGeometricLength.lean`.** The quasi-coherence of the direct
image is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageCartesian.lean`, which imports
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparison.lean` and so, through
it, the file that proves the statement at a geometric point. The statement at a point of the
space therefore cannot be added there, and is placed here instead.

**The direct image.** It is `AlgebraicGeometry.Space.chartDirectImage`, the direct image of
modules along base change of étale scheme charts, as in the statement at a geometric point. For
a closed immersion that functor is the direct image of Stacks 03LU, by
`AlgebraicGeometry.Space.modulePushforwardIsoChartDirectImage`, so the results here transfer to
that functor as well.

## References

* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The length of a module at a point of the space.** For an algebraic space `X` over a
scheme `S`, a point `p` of `|X|` and an `𝒪_X`-module `F`, this is the length of `F` at a
geometric point of `X` above `p`, a value in `ℕ∞ = {0, 1, 2, …, ∞}`. Such a geometric point
exists by Stacks 0488, part (1)
(`AlgebraicGeometry.Space.exists_geometricRepresentative`), and one of them is chosen here.

For a quasi-coherent `F` the choice does not matter: the value is the length at *every*
geometric point above `p`, by Stacks 0EE1
(`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`). That is
`AlgebraicGeometry.Space.lengthAtPoint_eq_geometricLength`, and it is what makes this number
the one Stacks 0EE2 attaches to a point of `|X|`: "`F` has length `d` at `p`" is
`lengthAtPoint B S hS X p F = d`. -/
def lengthAtPoint (X : AlgebraicSpaces B S hS) (p : points B S hS X.1)
    (F : Modules.{u, m} B S hS X.1 X.2) : ℕ∞ :=
  geometricLength B S hS X (exists_geometricRepresentative B S hS X.1 p).choose F

/-- **Stacks 0EE1 as the well-posedness of the length at a point of the space.** Let `F` be a
quasi-coherent `𝒪_X`-module, let `p` be a point of `|X|` and let `x̄` be *any* geometric point
of `X` above `p`. Then the length of `F` at `p` is the length of `F` at `x̄`.

The geometric point chosen in the definition of `AlgebraicGeometry.Space.lengthAtPoint` lies
above `p` and so has the same image point as `x̄`; the length of a quasi-coherent module at a
geometric point depends only on that image point, which is Stacks 0EE1,
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`. -/
theorem lengthAtPoint_eq_geometricLength (X : AlgebraicSpaces B S hS)
    {p : points B S hS X.1} {x : GeometricPoint B S hS X.1} (hx : x.LiesOver p)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] :
    lengthAtPoint B S hS X p F = geometricLength B S hS X x F :=
  geometricLength_eq_of_image_eq B S hS X.2
    (exists_geometricRepresentative B S hS X.1 p).choose x
    ((exists_geometricRepresentative B S hS X.1 p).choose_spec.trans hx.symm) F

variable {X Y : AlgebraicSpaces B S hS}

/-- The direct image of a quasi-coherent module along a closed immersion is quasi-coherent. -/
private theorem isQuasicoherentOnSite_chartDirectImage (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    [G.IsQuasicoherentOnSite] : (chartDirectImage B S hS f hf G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_smallBaseChangeModulePushforward_of_isAffineHom f hf.rep
    (isAffineHom_of_isClosedImmersion B S hS f.hom hf) ‹G.IsQuasicoherentOnSite›

/-- A quasi-coherent module has length `d` at every geometric point above `p` exactly when it
has length `d` at `p`. -/
private theorem forall_liesOver_geometricLength_eq_iff (Z : AlgebraicSpaces B S hS)
    (p : points B S hS Z.1) (F : Modules.{u, u} B S hS Z.1 Z.2) [F.IsQuasicoherentOnSite]
    (d : ℕ∞) :
    (∀ z : GeometricPoint B S hS Z.1, z.LiesOver p → geometricLength B S hS Z z F = d) ↔
      lengthAtPoint B S hS Z p F = d := by
  refine ⟨fun h => ?_, fun h z hz => ?_⟩
  · obtain ⟨z, hz⟩ := exists_geometricRepresentative B S hS Z.1 p
    exact (lengthAtPoint_eq_geometricLength B S hS Z hz F).trans (h z hz)
  · exact (lengthAtPoint_eq_geometricLength B S hS Z hz F).symm.trans h

/-- **The length of a direct image along a closed immersion, at a point of the space.** Let
`f : X ⟶ Y` be a closed immersion of algebraic spaces over `S` and let `G` be a quasi-coherent
`𝒪_X`-module. For a point `p` of `|X|`, a geometric point `x̄` above `p` and a geometric point
`ȳ` above the image of `p` in `|Y|`, the length of `f_*G` at `ȳ` is the length of `G` at `x̄`.

The length of `f_*G` at `ȳ` is its length at the image `f(x̄)` of `x̄`, because `f_*G` is
quasi-coherent (Stacks 07U8 for the affine morphism `f`) and the length of a quasi-coherent
module at a geometric point depends only on the point of the space underneath it (Stacks 0EE1,
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`); and its length at `f(x̄)` is the
length of `G` at `x̄` by
`AlgebraicGeometry.Space.geometricLength_chartDirectImage`. -/
theorem geometricLength_chartDirectImage_of_liesOver (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    [G.IsQuasicoherentOnSite] {p : points B S hS X.1}
    {x : GeometricPoint B S hS X.1} (hx : x.LiesOver p)
    {y : GeometricPoint B S hS Y.1} (hy : y.LiesOver (pointsMap B S hS X.1 f.hom p)) :
    geometricLength B S hS Y y (chartDirectImage B S hS f hf G) =
      geometricLength B S hS X x G :=
  have := isQuasicoherentOnSite_chartDirectImage B S hS f hf G
  (geometricLength_eq_of_image_eq B S hS Y.2 y (geometricPointMap f.hom x)
      (by rw [hy, geometricPointMap_image, hx]) (chartDirectImage B S hS f hf G)).trans
    (geometricLength_chartDirectImage B S hS f hf x G)

/-- **The length of a direct image along a closed immersion, as lengths at points of the two
spaces.** Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over a scheme `S`, let `G`
be a quasi-coherent `𝒪_X`-module and let `p` be a point of `|X|`. Then the length of `f_*G` at
the image `f(p)` of `p` in `|Y|` is the length of `G` at `p`.

Both numbers are read at one geometric point `x̄` above `p`: the left-hand one at the image
`f(x̄)`, which lies above `f(p)` by
`AlgebraicGeometry.Space.geometricPointMap_image`, and the right-hand one at `x̄`. Reading them
there is `AlgebraicGeometry.Space.lengthAtPoint_eq_geometricLength`, which is Stacks 0EE1 on
`X` for `G` and on `Y` for `f_*G` — the latter is quasi-coherent by Stacks 07U8, a closed
immersion being affine. What is left is the equality at the geometric points, which is
`AlgebraicGeometry.Space.geometricLength_chartDirectImage_of_liesOver`. -/
theorem lengthAtPoint_chartDirectImage (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) [G.IsQuasicoherentOnSite]
    (p : points B S hS X.1) :
    lengthAtPoint B S hS Y (pointsMap B S hS X.1 f.hom p) (chartDirectImage B S hS f hf G) =
      lengthAtPoint B S hS X p G := by
  have := isQuasicoherentOnSite_chartDirectImage B S hS f hf G
  obtain ⟨x, hx⟩ := exists_geometricRepresentative B S hS X.1 p
  have hy : (geometricPointMap f.hom x).LiesOver (pointsMap B S hS X.1 f.hom p) := by
    rw [GeometricPoint.LiesOver, geometricPointMap_image, hx]
  rw [lengthAtPoint_eq_geometricLength B S hS Y hy (chartDirectImage B S hS f hf G),
    lengthAtPoint_eq_geometricLength B S hS X hx G]
  exact geometricLength_chartDirectImage_of_liesOver B S hS f hf G hx hy

/-- **Stacks 0EE3 at a point of the space.** Let `f : X ⟶ Y` be a closed immersion of algebraic
spaces over a scheme `S`, let `G` be a quasi-coherent `𝒪_X`-module, let `p` be a point of `|X|`
with image `f(p)` in `|Y|` and let `d` be an element of `ℕ∞ = {0, 1, 2, …, ∞}`. Then `G` has
length `d` at `p` if and only if `f_*G` has length `d` at `f(p)`.

"Has length `d` at a point" is the condition of Stacks 0EE2: the length of the module at that
point of the space, `AlgebraicGeometry.Space.lengthAtPoint`, is `d`. Both sides are therefore
`= d` for one and the same number, by
`AlgebraicGeometry.Space.lengthAtPoint_chartDirectImage`. -/
@[stacks 0EE3 "at a point of the space, for the direct image of modules along base change of
  étale scheme charts"]
theorem lengthAtPoint_chartDirectImage_iff (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    [G.IsQuasicoherentOnSite] (p : points B S hS X.1) (d : ℕ∞) :
    lengthAtPoint B S hS X p G = d ↔
      lengthAtPoint B S hS Y (pointsMap B S hS X.1 f.hom p)
        (chartDirectImage B S hS f hf G) = d := by
  rw [lengthAtPoint_chartDirectImage B S hS f hf G p]

/-- **Stacks 0EE3 at a point of the space, with both sides unfolded into conditions on
geometric points.** For a quasi-coherent `G` and a point `p` of `|X|`, the length of `G` is `d`
at every geometric point above `p` exactly when the length of `f_*G` is `d` at every geometric
point above the image of `p`.

This is `AlgebraicGeometry.Space.lengthAtPoint_chartDirectImage_iff` with the definition of
Stacks 0EE2 spelled out on both sides: by
`AlgebraicGeometry.Space.lengthAtPoint_eq_geometricLength` the length at the point is the
length at each geometric point above it, so each of the two universally quantified conditions
is equivalent to the corresponding side of that equivalence — the quantifier is harmless
because the quantified value is constant. A geometric point above either point exists by
Stacks 0488, part (1). -/
theorem geometricLength_chartDirectImage_iff_liesOver (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    [G.IsQuasicoherentOnSite] (p : points B S hS X.1) (d : ℕ∞) :
    (∀ x : GeometricPoint B S hS X.1, x.LiesOver p →
        geometricLength B S hS X x G = d) ↔
      ∀ y : GeometricPoint B S hS Y.1, y.LiesOver (pointsMap B S hS X.1 f.hom p) →
        geometricLength B S hS Y y (chartDirectImage B S hS f hf G) = d := by
  have := isQuasicoherentOnSite_chartDirectImage B S hS f hf G
  rw [forall_liesOver_geometricLength_eq_iff B S hS X p G,
    forall_liesOver_geometricLength_eq_iff B S hS Y _ (chartDirectImage B S hS f hf G)]
  exact lengthAtPoint_chartDirectImage_iff B S hS f hf G p d

end AlgebraicGeometry.Space

end
