module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre

/-!
# The morphism induced on scheme-theoretic fibres

Let `S` be a scheme, let `sX : X ⟶ S` and `sY : Y ⟶ S` be two schemes over it and let
`f : X ⟶ Y` be a morphism over `S`. For every point `s` of `S` the universal property of the
fibre product produces a morphism `f_s : X_s ⟶ Y_s` of scheme-theoretic fibres, and the square
formed by `f`, `f_s` and the two inclusions of fibres is cartesian. Consequently `f_s` inherits
every property of `f` stable under base change — properness in particular, which is what makes
proper pushforward of cycles available on the fibres.

This file builds that morphism, records its two defining identities, the cartesian square, and
its functoriality in `f`; and it records the multiplicity with which a point of `X_s` enters the
proper pushforward of a cycle on `X_s` along `f_s`.

## Main definitions

* `Stacks.Chow.inducedFiberMap` — the morphism induced on scheme-theoretic fibres by a morphism
  over the base.
* `Stacks.Chow.fiberPushforwardWeight` — the multiplicity with which a point of a fibre enters
  the proper pushforward of a cycle on that fibre.

## Main results

* `Stacks.Chow.isPullback_inducedFiberMap` — the square of a morphism over the base, the induced
  morphism of fibres and the two fibre inclusions is cartesian.
* `Stacks.Chow.isProper_inducedFiberMap` — the morphism induced on fibres by a proper morphism
  over the base is proper.
* `Stacks.Chow.inducedFiberMap_congr` — the independence of the construction of the chosen proof
  that the morphism lies over the base.  Its functoriality is `Stacks.Chow.inducedFiberMap_comp`
  of `./Compatibilities.lean`.

## Implementation notes

The weight is the one of Stacks 02R4 read on the fibre: the degree of the residue-field
extension at a point where the relative dimension over the residue field of the base point is
preserved, and zero otherwise. It is phrased for the Chow situation on the spectrum of that
residue field, which is the situation the group of cycles on a fibre is formed for.

## References

* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Quasi-compactness of the inclusion of a fibre -/

/-- The inclusion of a scheme-theoretic fibre is quasi-compact, being a base change of the
morphism from the spectrum of a residue field. -/
instance quasiCompact_fiberι {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    QuasiCompact (f.fiberι s) := by
  change QuasiCompact (pullback.fst f (S.fromSpecResidueField s))
  infer_instance

/-! ### The morphism induced on fibres -/

section FiberMap

variable {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ sY = sX) (s : S)

/-- The morphism induced by a morphism `f : X ⟶ Y` over the base on the scheme-theoretic fibres
over a point `s` of the base. -/
def inducedFiberMap : sX.fiber s ⟶ sY.fiber s :=
  pullback.lift (sX.fiberι s ≫ f) (sX.fiberToSpecResidueField s)
    (by rw [Category.assoc, hf]; exact sX.fiber_fac s)

/-- The morphism induced on fibres is compatible with the inclusions of the fibres. -/
@[reassoc]
theorem inducedFiberMap_fiberι : inducedFiberMap sX sY f hf s ≫ sY.fiberι s = sX.fiberι s ≫ f :=
  pullback.lift_fst _ _ _

/-- The morphism induced on fibres is a morphism over the spectrum of the residue field. -/
@[reassoc]
theorem inducedFiberMap_fiberToSpecResidueField :
    inducedFiberMap sX sY f hf s ≫ sY.fiberToSpecResidueField s = sX.fiberToSpecResidueField s :=
  pullback.lift_snd _ _ _

/-- On points, the morphism induced on fibres is the restriction of the given morphism. -/
theorem inducedFiberMap_fiberι_base (x : sX.fiber s) :
    (sY.fiberι s).base ((inducedFiberMap sX sY f hf s).base x) = f.base ((sX.fiberι s).base x) := by
  have h := inducedFiberMap_fiberι sX sY f hf s
  have h' : ((inducedFiberMap sX sY f hf s ≫ sY.fiberι s)).base x = ((sX.fiberι s ≫ f)).base x := by
    rw [h]
  simpa using h'

/-- The square formed by a morphism over the base, the morphism it induces on fibres, and the
two inclusions of fibres is a pullback square. -/
theorem isPullback_inducedFiberMap :
    IsPullback (sX.fiberι s) (inducedFiberMap sX sY f hf s) f (sY.fiberι s) := by
  have h2 : IsPullback (sY.fiberι s) (sY.fiberToSpecResidueField s) sY
      (S.fromSpecResidueField s) := IsPullback.of_hasPullback sY (S.fromSpecResidueField s)
  have h1 : IsPullback (sX.fiberι s)
      (inducedFiberMap sX sY f hf s ≫ sY.fiberToSpecResidueField s) (f ≫ sY)
      (S.fromSpecResidueField s) := by
    rw [inducedFiberMap_fiberToSpecResidueField, hf]
    exact IsPullback.of_hasPullback sX (S.fromSpecResidueField s)
  exact IsPullback.of_bot h1 (inducedFiberMap_fiberι sX sY f hf s).symm h2

/-- The morphism induced on fibres by a proper morphism over the base is proper, being a base
change of it. -/
instance isProper_inducedFiberMap [IsProper f] : IsProper (inducedFiberMap sX sY f hf s) :=
  MorphismProperty.of_isPullback (isPullback_inducedFiberMap sX sY f hf s) inferInstance

/-- The morphism induced on fibres depends on the morphism over the base alone, not on the
chosen proof that it lies over the base. -/
theorem inducedFiberMap_congr {f' : X ⟶ Y} (hff' : f = f') (hf' : f' ≫ sY = sX) :
    inducedFiberMap sX sY f hf s = inducedFiberMap sX sY f' hf' s := by
  subst hff'
  rfl

end FiberMap

/-! ### The pushforward weight on a fibre -/

/-- The multiplicity with which a point of the fibre over `s` enters the proper pushforward of a
cycle on that fibre: the degree of its residue-field extension when the relative dimension is
preserved, and zero otherwise. -/
def fiberPushforwardWeight {S X Y : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) (s : S)
    (x : sX.fiber s) : ℤ :=
  if relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
        (sX.fiberToSpecResidueField s) x =
      relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
        (sY.fiberToSpecResidueField s) ((inducedFiberMap sX sY f hf s).base x)
    then ((inducedFiberMap sX sY f hf s).residueDegree x : ℤ) else 0

end Stacks.Chow

end
