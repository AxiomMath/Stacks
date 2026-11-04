module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.FiniteTypeIdealSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Characterizing modules of finite type by their associated sheaves

On the spectrum of a commutative ring `R`, the quasi-coherent sheaf `M̃` attached to an
`R`-module `M` is of finite type exactly when `M` is a finite module. This module records that
characterization against the Stacks Project; the statement itself is already available in the
library, so nothing is reconstructed here.

The ideal-sheaf consequence of that characterization is proved below: on an *affine* scheme a
sheaf of ideals is of finite type as soon as its global ideal is finitely generated.  Finite
generation on the other affine opens is then automatic, because every point of every affine
open lies in a standard open of the whole scheme, and the ideal of a sheaf of ideals on a
standard open is the image of the global one.

## Main results

* `AlgebraicGeometry.tilde_isFiniteType_iff` states that `M̃` is of finite type if and only if
  `M` is a finite `R`-module.
* `AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_of_fg_ideal_top`: on an affine scheme a
  sheaf of ideals whose global ideal is finitely generated is of finite type.

## References

* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **On an affine scheme a sheaf of ideals whose global ideal is finitely generated is of
finite type.**

The local criterion
`AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_of_forall_exists_basicOpen` asks, around
every point of every affine open, for a standard open of that affine open carrying a finitely
generated ideal.  Two affine opens through a point share a standard open
(`AlgebraicGeometry.exists_basicOpen_le_affine_inter`), applied here to the given affine open
and to the whole scheme; on a standard open of the whole scheme the ideal is the image of the
global one, hence finitely generated. -/
theorem Scheme.IdealSheafData.isFiniteType_of_fg_ideal_top {Z : Scheme.{u}} [IsAffine Z]
    (I : Z.IdealSheafData) (h : (I.ideal ⟨⊤, isAffineOpen_top Z⟩).FG) : I.IsFiniteType := by
  refine Scheme.IdealSheafData.isFiniteType_of_forall_exists_basicOpen I fun U x hx => ?_
  obtain ⟨f, g, hfg, hxf⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter U.2 (isAffineOpen_top Z) x ⟨hx, trivial⟩
  refine ⟨f, hxf, ?_⟩
  have heq : Z.affineBasicOpen f =
      Z.affineBasicOpen (U := ⟨⊤, isAffineOpen_top Z⟩) g := Subtype.ext hfg
  rw [heq, ← I.map_ideal_basicOpen ⟨⊤, isAffineOpen_top Z⟩ g]
  exact h.map _

end AlgebraicGeometry

end
