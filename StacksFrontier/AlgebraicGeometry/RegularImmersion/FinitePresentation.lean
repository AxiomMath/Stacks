module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.RegularIdealSheafFiniteType

/-!
# A quasi-regular immersion is locally of finite presentation

Let `i : Z ⟶ X` be an immersion of schemes.  It factors as the closed immersion
`i.liftCoborder : Z ⟶ i.coborderRange` followed by an open immersion, and `i` is quasi-regular
when the defining ideal sheaf `I` of that closed factor is quasi-regular.  A quasi-regular ideal
sheaf is of finite type and quasi-coherent, so on each affine open its sections form a finite
module over the functions there, i.e. `I` is a finitely generated ideal on each affine open;
that is the hypothesis under which a closed immersion is locally of finite presentation.  Local
finite presentation then passes from the closed factor to `i` because the remaining factor is an
open immersion.

This is condition (1) of the right-hand side of [Stacks, Tag 063M], proved in the direction
that starts from quasi-regularity.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.fg_ker_liftCoborder_of_isQuasiRegularImmersion`:
  for a quasi-regular immersion the kernel ideal sheaf of its canonical closed factor is
  finitely generated over every affine open.
* `…RegularIdealSheaf.locallyOfFinitePresentation_of_isQuasiRegularImmersion`: **a quasi-regular
  immersion is locally of finite presentation**.

## Implementation notes

The two presentations of the ideal sheaf have to be matched up.  Quasi-regularity is a condition
on `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal i`, an ideal subsheaf of the
structure sheaf *module*, whereas the finite-presentation criterion of [Stacks, Tag 01TV] is
stated for `AlgebraicGeometry.Scheme.Hom.ker`, Mathlib's family of ideals indexed by the affine
opens.  `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom_obj_eq_ker` is the bridge,
and it is why the finite generation is extracted affine open by affine open rather than as a
single statement about the ideal sheaf.

Of the three conditions on the right-hand side of Tag 063M, (1) local finite presentation,
(2) the conormal sheaf is finite locally free, and (3) the map of [Stacks, Tag 0632] is an
isomorphism, only (1) is proved here, and only in the direction out of quasi-regularity.
Condition (2) in the same direction is
`…RegularIdealSheaf.isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion` in
`StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalLocallyFree`, condition (3) is
`Stacks.Conormal.isIso_conormalSymmetricHom_app` in
`StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalSymmetricIso`, and the whole iff,
including the converse, is `Stacks.Conormal.isQuasiRegularImmersion_iff` in
`StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalQuasiRegularCriterion`.

## References

* [Stacks Project, Lemma 31.22.5 (Tag 063M)](https://stacks.math.columbia.edu/tag/063M)
* [Stacks Project, Lemma 29.22.7 (Tag 01TV)](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Lemma 31.20.3 (Tag 063F)](https://stacks.math.columbia.edu/tag/063F)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {Z X : Scheme.{u}}

/-- For a quasi-regular immersion `i`, the kernel ideal sheaf of the canonical closed factor
`i.liftCoborder` is finitely generated over every affine open of `i.coborderRange`.

The defining ideal sheaf is of finite type and quasi-coherent by [Stacks, Tag 063F], so its
sections over an affine open form a finite module over the functions there; over an affine open
those sections are the component of `AlgebraicGeometry.Scheme.Hom.ker`. -/
theorem fg_ker_liftCoborder_of_isQuasiRegularImmersion (i : Z ⟶ X) [IsImmersion i]
    (h : IsQuasiRegularImmersion i) (U : i.coborderRange.toScheme.affineOpens) :
    (i.liftCoborder.ker.ideal U).FG := by
  have hqr : IsQuasiRegularIdealSheaf
      i.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace (definingIdeal i) :=
    (isQuasiRegularImmersion_iff i (definingIdeal i) rfl).mp h
  have hft : (definingIdeal i).toSheafOfModules.IsFiniteType :=
    isFiniteType_of_isQuasiRegularIdealSheaf i.coborderRange.toScheme (definingIdeal i) hqr
  have hqc : (definingIdeal i).toSheafOfModules.IsQuasicoherent :=
    isQuasicoherent_of_isQuasiRegularIdealSheaf i.coborderRange.toScheme (definingIdeal i) hqr
  have hfin := _root_.AlgebraicGeometry.moduleFinite_sections_on_affine
    (X := i.coborderRange.toScheme) (definingIdeal i).toSheafOfModules U.1 U.2
  have hfg : ((definingIdeal i).obj (op U.1)).FG := Module.Finite.iff_fg.mp hfin
  rwa [definingIdealOfHom_obj_eq_ker i.liftCoborder U] at hfg

/-- **[Stacks, Tag 063M], condition (1) in the direction out of quasi-regularity.**  A
quasi-regular immersion of schemes is locally of finite presentation.

The canonical closed factor `i.liftCoborder` is locally of finite presentation by
[Stacks, Tag 01TV], since the quasi-regular defining ideal sheaf is finitely generated over
every affine open, and the remaining factor `i.coborderRange.ι` is an open immersion. -/
@[stacks 063M "condition (1) of the statement, in the direction out of quasi-regularity: a \
quasi-regular immersion is locally of finite presentation.  The whole iff is proved at \
Stacks.Conormal.isQuasiRegularImmersion_iff",
  ega "IV 16.9.8" "(i), one direction",
  ega "IV 16.9.9" "l.f.p. is necessary", sga "3 III 4.6.2" "more general"]
theorem locallyOfFinitePresentation_of_isQuasiRegularImmersion (i : Z ⟶ X) [IsImmersion i]
    (h : IsQuasiRegularImmersion i) : LocallyOfFinitePresentation i := by
  have hj : LocallyOfFinitePresentation i.liftCoborder :=
    (locallyOfFinitePresentation_iff_fg_ker i.liftCoborder).2
      (fg_ker_liftCoborder_of_isQuasiRegularImmersion i h)
  have he : i.liftCoborder ≫ i.coborderRange.ι = i := i.liftCoborder_ι
  rw [← he]
  infer_instance

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
