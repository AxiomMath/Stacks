module

public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.Separated
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A morphism with a relatively ample invertible sheaf is separated

## Main results

* `AlgebraicGeometry.Scheme.Modules.IsRelativelyAmple.isSeparated`: a morphism of schemes
  admitting a relatively ample invertible sheaf is separated.

## Implementation notes

Separatedness is affine-local on the target, and over the inverse image of an affine open of the
base the pullback of the sheaf is ample, so that inverse image is a separated scheme.

The invertible sheaf witnessing the existence hypothesis of the source is supplied explicitly,
so the result applies directly to any such witness.

## References

* [Stacks Project, Tag 01VI](https://stacks.math.columbia.edu/tag/01VI)
* [Stacks Project, Tag 01PY](https://stacks.math.columbia.edu/tag/01PY)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism of schemes admitting a relatively ample invertible sheaf is separated. -/
@[stacks 01VI, ega "II 4.6.3"]
theorem IsRelativelyAmple.isSeparated {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) : IsSeparated f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated)
    (fun V : S.affineOpens => V) (iSup_affineOpens_eq_top S)]
  intro V
  have : IsAffine V.1.toScheme := V.2
  let := Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
    (f ⁻¹ᵁ V.1).ι.toLRSHom.toShHom L
  have hsep : AlgebraicGeometry.Scheme.IsSeparated (f ⁻¹ᵁ V.1).toScheme :=
    IsAmple.isSeparated _
      ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp (hL.isAmple_preimage _ _ V.1 V.2))
  refine (IsSeparated.comp_iff (f := f ∣_ V.1) (g := Limits.terminal.from V.1.toScheme)).mp ?_
  rw [Limits.terminal.comp_from]
  exact hsep.isSeparated_terminal_from

end AlgebraicGeometry.Scheme.Modules
