module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStandardOpenCover
public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A common-degree cover makes the divisible twists invertible

Let `S` be a graded ring and `Y` an open of `Proj(S)` admitting a finite cover by standard opens
`D₊(f)` with every `f` homogeneous of one common positive degree `d`. Then `Y` is contained in
the invertible locus `W_d`, and for every integer `n` the restriction of `𝒪(dn)` to `Y` is
invertible.

The cover is `AlgebraicGeometry.Proj.CommonDegreeCover`, which bundles the common positive
degree, the finite family of homogeneous elements of that degree, and the covering equality;
`AlgebraicGeometry.Proj.commonDegreeCover` produces one from quasi-compactness of `Y`.

## Main results

* `Stacks.AlgebraicGeometry.CommonDegreeTwist.le_whereInvertible` places such a cover inside the
  invertible locus `W_d` of Tag 01MU.
* `Stacks.AlgebraicGeometry.CommonDegreeTwist.isInvertible_restrict_twistingSheaf_mul_degree`:
  the restriction of `𝒪(dn)` to `Y` is invertible.

## The route

Both steps are applications of results about Tag 01MU's open `W_d`.

* `Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_eq_iSup_basicOpen_mul` identifies `W_d`
  with the union of the standard opens `D₊(fg)` for homogeneous `f`, `g` with
  `deg f = deg g + d`. Each member `D₊(f)` of the cover is one of those opens, with `g = 1` of
  degree `0`, so the cover — and hence `Y` — lies in `W_d`.
* `Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_iff_le_whereInvertible` turns that
  containment back into goodness of `Y`, whose first clause is the invertibility assertion.

Positivity of the common degree is therefore not used: it is carried in the bundled cover because
Tag 01MW's statement carries it, and the Tag 01MU results do not need it.

## References

* [Stacks Project, Lemma 27.14.1 (Tag 01MW)](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.CommonDegreeTwist

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Tag 01MW (1).** An open covered by homogeneous standard opens of one common degree `d` is
contained in the invertible locus `W_d`. -/
theorem le_whereInvertible (Y : (AlgebraicGeometry.Proj 𝒜).Opens)
    (c : AlgebraicGeometry.Proj.CommonDegreeCover 𝒜 Y) :
    Y ≤ ProjInvertibleLocus.whereInvertible 𝒜 c.degree := by
  rw [GoodOpenClose.whereInvertible_eq_iSup_basicOpen_mul 𝒜 c.degree]
  calc
    Y = ⨆ f ∈ c.sections, AlgebraicGeometry.Proj.basicOpen 𝒜 f ⊓ Y :=
      c.iSup_basicOpen_inf_eq.symm
    _ ≤ ⨆ (e : ℕ) (x : 𝒜 (e + c.degree)) (y : 𝒜 e),
        AlgebraicGeometry.Proj.basicOpen 𝒜 ((x : A) * (y : A)) := by
      refine iSup_le fun f ↦ iSup_le fun hf ↦ ?_
      let f' : 𝒜 (0 + c.degree) := ⟨f, by simpa using c.sections_mem f hf⟩
      let g : 𝒜 0 := ⟨1, SetLike.one_mem_graded 𝒜⟩
      calc
        AlgebraicGeometry.Proj.basicOpen 𝒜 f ⊓ Y
            ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f := inf_le_left
        _ = AlgebraicGeometry.Proj.basicOpen 𝒜 ((f' : A) * (g : A)) := by simp [f', g]
        _ ≤ ⨆ (e : ℕ) (x : 𝒜 (e + c.degree)) (y : 𝒜 e),
            AlgebraicGeometry.Proj.basicOpen 𝒜 ((x : A) * (y : A)) :=
          le_iSup_of_le 0 <| le_iSup_of_le f' <| le_iSup_of_le g le_rfl

/-- **Tag 01MW (2).** Every integral multiple of a common covering degree gives an invertible
twist on the covered open subscheme of `Proj`. -/
@[ega "II 2.5.8"]
theorem isInvertible_restrict_twistingSheaf_mul_degree
    (Y : (AlgebraicGeometry.Proj 𝒜).Opens)
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒜 Y) (n : ℤ) :
    SheafOfModules.IsInvertible Y.toScheme.presheaf Y.toScheme.ringCatSheaf.2
      ((Scheme.Modules.pullback Y.ι).obj
        (twistingSheaf 𝒜 ((C.degree : ℤ) * n))) :=
  ((GoodOpenClose.isGoodOpen_iff_le_whereInvertible 𝒜 C.degree Y).mpr
    (le_whereInvertible 𝒜 Y C)).1 n

end Stacks.AlgebraicGeometry.CommonDegreeTwist

end
