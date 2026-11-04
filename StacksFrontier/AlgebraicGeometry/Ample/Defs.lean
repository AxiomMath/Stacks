module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# Ample invertible sheaves

An invertible sheaf on a scheme is *ample* when the scheme is quasi-compact and every point lies
in an affine nonvanishing locus of a global section of some positive tensor power of the sheaf.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.IsAmple`: ampleness of an invertible sheaf of modules on a
  scheme.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isAmple_iff`: ampleness unfolded to quasi-compactness
  together with the existence of affine nonvanishing loci.
* `AlgebraicGeometry.Scheme.Modules.IsAmple.compactSpace`: the underlying space of a scheme
  carrying an ample invertible sheaf is quasi-compact.
* `AlgebraicGeometry.Scheme.Modules.IsAmple.exists_affine_nonvanishingLocus`: every point has an
  affine nonvanishing locus of a section of a positive tensor power.

## Implementation notes

The nonvanishing open of a global section of an invertible sheaf of modules on a ringed space is
`Stacks.SheafOfModules.nonvanishingOpen` (Tag 01CY); the integer tensor powers are
`Stacks.SheafOfModules.Invertible.tensorPower` (Tag 01CU), each of which is again invertible by
`Stacks.SheafOfModules.Invertible.tensorPower_isInvertible`.

The affineness condition is imposed on the whole nonvanishing locus, not on some smaller
neighbourhood of the point inside it, and the exponent is required to be positive. Quasi-
compactness of the scheme is `CompactSpace` of its underlying space.

Invertibility of a sheaf of modules is recorded by two classes,
`AlgebraicGeometry.SheafOfModules.IsInvertible` and `Stacks.SheafOfModules.IsInvertible`; the
instance `AlgebraicGeometry.Scheme.Modules.isInvertible_tensorPower` passes from the first to the
second for tensor powers.

## References

* [EGA II, Definition 4.5.3]
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Presheaves of abelian groups on the opens of a scheme admit sheafification. -/
noncomputable local instance (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the opens of a scheme, the morphisms of presheaves of abelian groups inverted by
sheafification are exactly the locally bijective ones. -/
noncomputable local instance (X : Scheme.{u}) :
    (Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Every integer tensor power of a sheaf of modules on a scheme that is invertible in the sense
of `AlgebraicGeometry.SheafOfModules.IsInvertible` is invertible in the sense of
`Stacks.SheafOfModules.IsInvertible`. -/
public instance isInvertible_tensorPower (Y : Scheme.{u}) (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property
      (Stacks.SheafOfModules.Invertible.tensorPower Y.toRingedSpace.presheaf
        (structureSheafRing Y.toRingedSpace).property M n) := by
  have h := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible
    Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property M n
  obtain ⟨F, hF, ⟨u⟩⟩ := h.exists_tensorFunctor
  exact ⟨F, hF, ⟨{ ι := u.ι, bijective := u.bijective }⟩⟩

variable (X : Scheme.{u}) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- An invertible sheaf of modules on a scheme is *ample* if the scheme is quasi-compact and
every point has an affine nonvanishing locus for some global section of a tensor power of
positive exponent. -/
@[stacks 01PS, ega "II 4.5.3"]
public def IsAmple : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧
    ∃ s : (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
      x ∈ Stacks.SheafOfModules.nonvanishingOpen
          (X := X.toLocallyRingedSpace.toRingedSpace)
          (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
        IsAffineOpen (Stacks.SheafOfModules.nonvanishingOpen
          (X := X.toLocallyRingedSpace.toRingedSpace)
          (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)

/-- An invertible sheaf is ample precisely when the scheme is quasi-compact and every point
belongs to an affine nonvanishing locus of a section of a positive tensor power. -/
public theorem isAmple_iff :
    IsAmple X L ↔ (CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        x ∈ Stacks.SheafOfModules.nonvanishingOpen
            (X := X.toLocallyRingedSpace.toRingedSpace)
            (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
          IsAffineOpen (Stacks.SheafOfModules.nonvanishingOpen
            (X := X.toLocallyRingedSpace.toRingedSpace)
            (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)) :=
  Iff.rfl

namespace IsAmple

variable {X L}

/-- The underlying space of a scheme carrying an ample invertible sheaf is quasi-compact. -/
public theorem compactSpace (h : IsAmple X L) : CompactSpace X := h.1

/-- Every point has an affine nonvanishing locus of a section of a positive tensor power of an
ample sheaf. -/
public theorem exists_affine_nonvanishingLocus (h : IsAmple X L) (x : X) :
    ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        x ∈ Stacks.SheafOfModules.nonvanishingOpen
            (X := X.toLocallyRingedSpace.toRingedSpace)
            (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
          IsAffineOpen (Stacks.SheafOfModules.nonvanishingOpen
            (X := X.toLocallyRingedSpace.toRingedSpace)
            (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) :=
  h.2 x

end IsAmple

end AlgebraicGeometry.Scheme.Modules
