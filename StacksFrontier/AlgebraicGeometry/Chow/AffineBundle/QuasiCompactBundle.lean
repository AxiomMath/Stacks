module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Germ

/-!
# An affine-space bundle is quasi-compact, and the images of a locally finite family

Under a quasi-compact morphism `f : X ⟶ Y`, the closures of the images of a locally finite family
`{W_j}` of subsets of `X` form a locally finite family in `Y`: a quasi-compact open `V ⊆ Y` has
quasi-compact inverse image, which meets only finitely many of the `W_j`, and `V` meets the
closure of `f(W_j)` only if `W_j` meets `f⁻¹(V)`. In particular this holds for an affine-space
bundle.

## Main results

* `Stacks.Chow.isZariskiLocalAtTarget_quasiCompact` — being quasi-compact is Zariski-local on the
  target.
* `Stacks.Chow.locallyFinite_closure_image_of_quasiCompact` — the closures of the images of a
  locally finite family of subsets under a quasi-compact morphism form a locally finite family.
* `Stacks.Chow.locallyFinite_closure_image_of_isAffineSpaceBundle` — the same for an affine-space
  bundle.

## Implementation notes

`AlgebraicGeometry.IsZariskiLocalAtTarget @QuasiCompact` is not found by instance search under
the default `backward.isDefEq.respectTransparency`, so
`Stacks.Chow.isZariskiLocalAtTarget_quasiCompact` is an alias of
`AlgebraicGeometry.GlueingNearPoint.quasiCompact_isZariskiLocal`, which supplies the affine
property of quasi-compactness explicitly.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- Being quasi-compact is Zariski-local on the target. -/
alias isZariskiLocalAtTarget_quasiCompact :=
  AlgebraicGeometry.GlueingNearPoint.quasiCompact_isZariskiLocal

/-- The closures of the images of a locally finite family of subsets under a quasi-compact
morphism form a locally finite family. -/
theorem locallyFinite_closure_image_of_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] {ι : Type*} {W : ι → Set X} (hW : LocallyFinite W) :
    LocallyFinite fun i ↦ closure (f.base '' W i) := by
  intro y
  obtain ⟨V, hV, hyV, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (U := (⊤ : Y.Opens)) (x := y) (by simp)
  refine ⟨(V : Set Y), (V.2.mem_nhds_iff).mpr hyV, Set.Finite.subset
    (hW.finite_nonempty_inter_compact
      (QuasiCompact.isCompact_preimage (f := f) (V : Set Y) V.2 hV.isCompact)) ?_⟩
  intro i hi
  obtain ⟨z, hzclos, hzV⟩ := hi
  obtain ⟨w, hwV, x, hxW, hxw⟩ := mem_closure_iff.mp hzclos (V : Set Y) V.2 hzV
  exact ⟨x, hxW, by simpa only [Set.mem_preimage, hxw] using hwV⟩

/-- If `f` is an affine-space bundle and `{W_j}` is a locally finite family of subsets of its
source, then the closures of the images `f(W_j)` form a locally finite family in the target. -/
theorem locallyFinite_closure_image_of_isAffineSpaceBundle {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (h : IsAffineSpaceBundle f r) {ι : Type*} {W : ι → Set X} (hW : LocallyFinite W) :
    LocallyFinite fun i ↦ closure (f.base '' W i) :=
  let := quasiCompact_of_isAffineSpaceBundle f r h
  locallyFinite_closure_image_of_quasiCompact f hW

end Stacks.Chow

end
