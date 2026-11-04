module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFpqcDescent

/-!
# Finite local freeness is fpqc local on the base once affineness is

Being finite locally free is being finite, flat and locally of finite presentation. Flatness and
local finite presentation are fpqc local on the base, and finiteness is universal closedness
together with affineness and local finite type, of which only affineness is not yet known to be
fpqc local. So the fpqc locality of finite local freeness follows from the fpqc locality of
affineness, and that is the content of this file.

## Main results

* `Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc_of_isAffineHom`: finiteness is fpqc local on
  the base as soon as affineness is.
* `Stacks.Morphisms.isFiniteLocallyFree_isLocalAtTarget_fpqc_of_isAffineHom`: being finite
  locally free is fpqc local on the base as soon as affineness is.
* `Stacks.Morphisms.isFiniteLocallyFree_isLocalAtTarget_fpqc`: being finite locally free is fpqc
  local on the base.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc`: being finite locally free of
  a fixed degree `d` is fpqc local on the base.

## Implementation notes

The hypothesis of both results is the assertion of Stacks Tag 02L5, that
`AlgebraicGeometry.IsAffineHom` is local on the base for the fpqc precoverage. It is taken as a
hypothesis rather than used as an instance because it is not available: it is proved from the
effectivity of quasi-coherent descent data along an fpqc covering, which is Stacks Tag 023T.

Universal closedness is fpqc local by the general criterion
`Stacks.Descent.isLocalAtTarget_fpqcPrecoverage`, every one of whose hypotheses it satisfies.
The criterion's stability hypothesis is `Stacks.Descent.IsStableUnderFlatBaseChange`, and it is
supplied by name from `AlgebraicGeometry.universallyClosed_isStableUnderBaseChange` through
`Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange`: stability under
arbitrary base change gives stability under flat base change a fortiori, and the step cannot be
left to instance search because `@UniversallyClosed` has implicit morphism arguments.
The decompositions used are `AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom`
and `AlgebraicGeometry.IsFinite.eq_inf`, and each infimum is formed with
`CategoryTheory.MorphismProperty.IsLocalAtTarget.inf`, whose precoverage argument is supplied
explicitly because instance search cannot solve for it here.

The second clause of Tag 02VO, for a fixed degree, does not go through this decomposition: the
degree is not visible in any of the three factors. It is instead the general criterion applied to
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property` directly, whose three inputs are
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_isZariskiLocalAtTarget`,
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_isStableUnderBaseChange` and the fpqc descent of
`StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFpqcDescent`.

## References

* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-- Universal closedness of a morphism of schemes is fpqc local on the base. -/
@[sga "4 IV 8.5.5"]
theorem universallyClosed_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@UniversallyClosed : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@UniversallyClosed : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-- The infimum of two morphism properties which are fpqc local on the base is fpqc local. -/
private theorem isLocalAtTarget_inf_fpqc {P Q : MorphismProperty Scheme.{u}}
    (hP : MorphismProperty.IsLocalAtTarget P Scheme.fpqcPrecoverage)
    (hQ : MorphismProperty.IsLocalAtTarget Q Scheme.fpqcPrecoverage) :
    MorphismProperty.IsLocalAtTarget (P ⊓ Q) Scheme.fpqcPrecoverage :=
  @MorphismProperty.IsLocalAtTarget.inf _ _ Scheme.fpqcPrecoverage _ _ hP hQ

/-- Finiteness of a morphism of schemes is fpqc local on the base as soon as affineness is: a
finite morphism is a universally closed affine morphism which is locally of finite type, and the
other two factors are fpqc local on the base already. -/
theorem isFinite_isLocalAtTarget_fpqc_of_isAffineHom
    (h : MorphismProperty.IsLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage) :
    MorphismProperty.IsLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  have hint : MorphismProperty.IsLocalAtTarget (@IsIntegralHom : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
    rw [IsIntegralHom.eq_universallyClosed_inf_isAffineHom]
    exact isLocalAtTarget_inf_fpqc
      universallyClosed_isLocalAtTarget_fpqc.{u} h
  have hft := Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fpqc.{u}
  rw [IsFinite.eq_inf]
  exact isLocalAtTarget_inf_fpqc hint hft

/-- Being finite locally free is fpqc local on the base as soon as affineness is. -/
theorem isFiniteLocallyFree_isLocalAtTarget_fpqc_of_isAffineHom
    (h : MorphismProperty.IsLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage) :
    MorphismProperty.IsLocalAtTarget (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  have hprop : (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) =
      (@IsFinite ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := by
    ext X S f
    rw [isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
    exact ⟨fun ⟨a, b, c⟩ ↦ ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ ↦ ⟨a, b, c⟩⟩
  have hfin := isFinite_isLocalAtTarget_fpqc_of_isAffineHom h
  have hflat := Stacks.Descent.flat_isLocalAtTarget_fpqc.{u}
  have hlfp := Stacks.Descent.locallyOfFinitePresentation_isLocalAtTarget_fpqc.{u}
  rw [hprop]
  exact isLocalAtTarget_inf_fpqc (isLocalAtTarget_inf_fpqc hfin hflat) hlfp

/-- **Stacks Project, Tag 02VO.** Being finite locally free is fpqc local on the base. -/
@[stacks 02VO "finite locally free"]
instance isFiniteLocallyFree_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  isFiniteLocallyFree_isLocalAtTarget_fpqc_of_isAffineHom
    Stacks.Descent.isAffineHom_isLocalAtTarget_fpqc

/-- **Stacks Project, Tag 02VO.** For `d : ℕ`, being finite locally free of degree `d` is fpqc
local on the base. -/
@[stacks 02VO "finite locally free of fixed degree"]
instance isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc (d : ℕ) :
    MorphismProperty.IsLocalAtTarget (IsFiniteLocallyFreeOfRank.property.{u} d)
      Scheme.fpqcPrecoverage :=
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

end Stacks.Morphisms

end
