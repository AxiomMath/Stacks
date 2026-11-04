module

public import StacksFrontier.AlgebraicGeometry.SubmodulePrimitives.CoRestrict
public import StacksFrontier.AlgebraicGeometry.SubmoduleGlueLocality.Basic

/-!
# Glueing submodules given on the members of a family of opens

This file composes the co-restriction of
`StacksFrontier/AlgebraicGeometry/SubmodulePrimitives/CoRestrict.lean` with the glueing step of
`StacksFrontier/AlgebraicGeometry/SubmoduleGlueOpens/Basic.lean` and its restriction identity in
`StacksFrontier/AlgebraicGeometry/SubmoduleGlueLocality/Basic.lean`, and that composition is the
form the affine induction of [Stacks, Tag 01PF] consumes: the induction produces a submodule
`P i` of `F.restrict (W i).ι` on each member of a family of opens, and what it needs is a single
submodule of `F` restricting to `P j` on `W j`.

## Main definitions

* `glueOfRestricted W P`: the submodule of `F` obtained by co-restricting each `P i` to `F` and
  glueing the results.

## Main results

* `restrictTo_glueOfRestricted`: **the restriction identity.** Under the agreement hypothesis,
  `restrictTo (W j).ι (glueOfRestricted W P) = P j`.
* `isQuasicoherent_glueOfRestricted`, `isFiniteType_glueOfRestricted`,
  `isCoherent_glueOfRestricted`: over a covering family, quasi-coherence, finite type and
  coherence transfer from the pieces to the glue.

## Implementation notes

The agreement hypothesis is stated as `Stacks.AlgebraicGeometry.SubmoduleGlueOpens.Agree` of the
co-restricted family, which is where it belongs: it is a condition on how the `P i` behave over
the opens inside two members of the family, and the induction discharges it from the way its
pieces were constructed. Nothing weaker suffices — `glue` without agreement is an intersection,
not a glueing, and `Stacks.AlgebraicGeometry.SubmoduleGlueOpens.glue_obj_of_le` is false
without it.

The three property transfers are the three theorems of `SubmoduleGlueLocality/Basic.lean` with
the restriction identity substituted, so their hypotheses are hypotheses on `P i` directly
rather than on the co-restriction. `isFiniteType_glueOfRestricted` and
`isCoherent_glueOfRestricted` carry `{ι : Type u}` because the two locality theorems of
`StacksFrontier/AlgebraicGeometry/SubmoduleRestrict/Locality.lean` they go through do;
`isQuasicoherent_glueOfRestricted` does not, `Stacks.Modules.isQuasicoherent_of_restrict` being
stated for an arbitrary index universe.

## What this does not do, and no stacks attribute

**No stacks attribute is attached, and none is earned.** Nothing here is an assertion of
[Stacks, Tag 01PF] or of any other tag. The induction itself — the recursion on the number of
affine opens needed to cover `X`, with [Stacks, Tag 01PE] supplying the extension at each step —
is not in this file; what is here is the glueing step in the shape that recursion applies it.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe w u

namespace Stacks.AlgebraicGeometry.SubmodulePrimitives

open Stacks.AlgebraicGeometry.SubmoduleGlueOpens Stacks.AlgebraicGeometry.SubmoduleRestrict
open Stacks.AlgebraicGeometry.SubmoduleGlueLocality

variable {X : Scheme.{u}} {F : X.Modules}

/-- **The glue of submodules given on the members of a family of opens.** Each `P i`, a submodule
of the restriction of `F` to `W i`, is carried back to a submodule of `F` by `coRestrict`, and
the results are glued by `Stacks.AlgebraicGeometry.SubmoduleGlueOpens.glue`. -/
def glueOfRestricted {ι : Type*} (W : ι → X.Opens)
    (P : ∀ i, (F.restrict (W i).ι).Submodule) : F.Submodule :=
  glue W fun i => coRestrict (W i).ι (P i)

/-- **The restriction identity.** Under the agreement hypothesis the glue restricts to `P j` on
`W j`, as an equality of submodules of `F.restrict (W j).ι`. -/
theorem restrictTo_glueOfRestricted {ι : Type*} (W : ι → X.Opens)
    (P : ∀ i, (F.restrict (W i).ι).Submodule)
    (hagree : Agree W fun i => coRestrict (W i).ι (P i)) (j : ι) :
    restrictTo (W j).ι (glueOfRestricted W P) = P j := by
  rw [glueOfRestricted, restrictTo_glue_of_le W _ hagree j, restrictTo_coRestrict]

/-- Over a covering family, the glue of quasi-coherent pieces is quasi-coherent. -/
theorem isQuasicoherent_glueOfRestricted {ι : Type w} (W : ι → X.Opens)
    (P : ∀ i, (F.restrict (W i).ι).Submodule)
    (hagree : Agree W fun i => coRestrict (W i).ι (P i)) (hcov : iSup W = ⊤)
    (h : ∀ i, (P i).toSheafOfModules.IsQuasicoherent) :
    ((glueOfRestricted W P).toSheafOfModules).IsQuasicoherent := by
  refine isQuasicoherent_glue W _ hagree hcov fun i => ?_
  rw [restrictTo_coRestrict]
  exact h i

/-- Over an open cover, the glue of pieces of finite type is of finite type. -/
theorem isFiniteType_glueOfRestricted {ι : Type u} (W : ι → X.Opens)
    (P : ∀ i, (F.restrict (W i).ι).Submodule)
    (hagree : Agree W fun i => coRestrict (W i).ι (P i)) (hcov : IsOpenCover W)
    (h : ∀ i, (P i).toSheafOfModules.IsFiniteType) :
    ((glueOfRestricted W P).toSheafOfModules).IsFiniteType := by
  refine isFiniteType_glue W _ hagree hcov fun i => ?_
  rw [restrictTo_coRestrict]
  exact h i

/-- Over a covering family, the glue of coherent pieces is coherent. -/
theorem isCoherent_glueOfRestricted {ι : Type u} (W : ι → X.Opens)
    (P : ∀ i, (F.restrict (W i).ι).Submodule)
    (hagree : Agree W fun i => coRestrict (W i).ι (P i)) (hcov : iSup W = ⊤)
    (h : ∀ i, (P i).toSheafOfModules.IsCoherent) :
    ((glueOfRestricted W P).toSheafOfModules).IsCoherent := by
  refine isCoherent_glue W _ hagree hcov fun i => ?_
  rw [restrictTo_coRestrict]
  exact h i

end Stacks.AlgebraicGeometry.SubmodulePrimitives

end
