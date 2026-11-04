module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle
public import StacksFrontier.AlgebraicGeometry.Blowup.TerminalRelativeProj
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent

/-!
# The projectivized normal cone of an immersion

Let `i : Z ⟶ X` be an immersion of schemes with conormal algebra `𝒞_{Z/X,*}`, the quasi-coherent
graded `𝒪_Z`-algebra `⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹` of [Stacks, Tag 0630]. Its relative spectrum over `Z` is
the normal cone `C_ZX` (`Stacks.Conormal.normalCone`); this file forms instead its relative
`Proj`,

  `P_ZX = Proj_Z(𝒞_{Z/X,*})`,

the projectivized normal cone, together with its projection to `Z`.

The conormal algebra is exactly the datum a relative `Proj` asks for: it is a
`SheafOfModules.GradedAlgebra` on `Z` whose pieces are quasi-coherent, which vanishes in negative
degrees, and whose homogeneous multiplication is commutative. Those are the four fields of
`Stacks.RelativeProj.Situation`, supplied by `Stacks.Conormal.ConormalAlgebraData.isQuasicoherent`,
`…negative_isZero` and `…mul_comm_int`.

## Main definitions

* `Stacks.Conormal.conormalProjSituation` — the conormal algebra as a relative `Proj` datum.
* `Stacks.Conormal.projectivizedNormalCone` — `P_ZX = Proj_Z(𝒞_{Z/X,*})`.
* `Stacks.Conormal.projectivizedNormalConeToBase` — its projection `P_ZX ⟶ Z`.
* `Stacks.Conormal.projectivizedNormalConeChart` — the chart of `P_ZX` over an affine open of `Z`,
  an ordinary `Proj` of the graded ring of sections of the conormal algebra.

## Main results

* `Stacks.Conormal.isPullback_projectivizedNormalConeChart` — each chart is the fibre product of
  the affine open with `P_ZX ⟶ Z`, so the charts cover `P_ZX` compatibly with the base.
* `Stacks.Conormal.isSeparated_projectivizedNormalConeToBase` — `P_ZX ⟶ Z` is separated, by
  [Stacks, Tag 01O2] for a relative `Proj`.

## What is not proved here

This file supplies the *scheme* `Proj_Z(𝒞_{Z/X,*})`, which is the object appearing in clause (6)
of [Stacks, Tag 0FBG]; it does not prove that clause, which identifies `P_ZX` with the
intersection `X' ∩ E` inside the blowup at infinity, nor clause (5), whose object is the relative
`Proj` of `𝒞_{Z/X,*}[S]` — the conormal algebra with a degree-one variable adjoined, which the
library does not form. The affine case of the identification, for the exceptional divisor of the
blowup of an affine scheme, is
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivizedNormalConeClosedImmersion.lean`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0636](https://stacks.math.columbia.edu/tag/0636)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O2](https://stacks.math.columbia.edu/tag/01O2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The conormal algebra of an immersion as a relative `Proj` datum.** Its homogeneous pieces
are quasi-coherent, it vanishes in negative degrees, and its homogeneous multiplication is
commutative, which are the three conditions of [Stacks, Tag 01NN]. -/
abbrev conormalProjSituation : Stacks.RelativeProj.Situation.{u} where
  base := Z
  algebra := (conormalAlgebra i).algebra
  mul_comm := (conormalAlgebra i).mul_comm_int
  negative_isZero := (conormalAlgebra i).negative_isZero
  isQuasicoherent := (conormalAlgebra i).isQuasicoherent

/-- **The projectivized normal cone `P_ZX = Proj_Z(𝒞_{Z/X,*})`** of an immersion `i : Z ⟶ X`:
the relative `Proj` over `Z` of the conormal algebra. This is the scheme appearing in clause (6)
of [Stacks, Tag 0FBG]. -/
@[stacks 0FBG "the scheme Proj_Z(C_{Z/X,*}) of clause (6), as a relative Proj over Z"]
def projectivizedNormalCone : Scheme.{u} :=
  (conormalProjSituation i).relativeProj

/-- **The projection `P_ZX ⟶ Z`** of the projectivized normal cone to its base. -/
def projectivizedNormalConeToBase : projectivizedNormalCone i ⟶ Z :=
  (conormalProjSituation i).relativeProjToBase

/-- The chart of `P_ZX` over an affine open `W ⊆ Z`: the ordinary `Proj` of the graded ring
`⨁_{n ≥ 0} 𝒞_{Z/X,n}(W)` of sections of the conormal algebra over `W`. -/
def projectivizedNormalConeChart (W : Z.affineOpens) :
    AlgebraicGeometry.Proj ((conormalProjSituation i).sectionRingGrading W.1) ⟶
      projectivizedNormalCone i :=
  (conormalProjSituation i).relativeProjChart W

/-- **The charts of `P_ZX` are the fibre products of the affine opens of `Z` with `P_ZX ⟶ Z`.**
This is the defining property of a relative `Proj`, [Stacks, Tag 01NQ]. -/
theorem isPullback_projectivizedNormalConeChart (W : Z.affineOpens) :
    IsPullback (projectivizedNormalConeChart i W)
      (Stacks.RelativeProj.Situation.projInclusionToOpen (conormalProjSituation i) W.1 W.2)
      (projectivizedNormalConeToBase i) W.1.ι :=
  (conormalProjSituation i).relativeProjChart_isPullback W

/-- The charts of `P_ZX` are compatible with the inclusions of affine opens of `Z`. -/
theorem projectivizedNormalConeChart_transition {W W' : Z.affineOpens} (h : W ≤ W') :
    Stacks.RelativeProj.Situation.projInclusionMap (conormalProjSituation i) W.1 W'.1 h W.2
          W'.2 ≫
        projectivizedNormalConeChart i W' = projectivizedNormalConeChart i W :=
  (conormalProjSituation i).relativeProjChart_transition h

/-- **`P_ZX ⟶ Z` is separated**, being the structure morphism of a relative `Proj`;
this is [Stacks, Tag 01O2]. -/
instance isSeparated_projectivizedNormalConeToBase :
    IsSeparated (projectivizedNormalConeToBase i) :=
  Stacks.RelativeProj.Data.isSeparated_toBase
    (Stacks.RelativeProj.Situation.chartData (conormalProjSituation i))

end Stacks.Conormal

end
