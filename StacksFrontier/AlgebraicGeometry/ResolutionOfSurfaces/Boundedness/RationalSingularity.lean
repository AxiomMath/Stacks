module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksCore.Tactic.StacksAttribute

/-!
# Rational singularities

An integral domain defines a rational singularity when the first cohomology group of the
structure sheaf vanishes on every normal modification of its spectrum.

## Main definitions

* `AlgebraicGeometry.DefinesRationalSingularity` is the predicate that an integral domain
  defines a rational singularity.

## Implementation notes

The source introduces the predicate for local normal Nagata domains of dimension two. The
vanishing condition itself is meaningful for every integral domain, so the definition is
stated at that generality; later results retain the source's local, normal, Nagata and
dimension hypotheses. Cohomology is Mathlib's `Sheaf.H` applied to the underlying additive
sheaf of the structure sheaf. Its `HasExt` instance is obtained canonically from the fact that
a category of abelian sheaves on a small site is Grothendieck abelian.

## References

* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An integral domain `A` **defines a rational singularity** if the first cohomology of the
structure sheaf of every normal modification of `Spec A` vanishes. -/
@[stacks 0B4N "defines_rational_singularity"]
noncomputable abbrev DefinesRationalSingularity
    (A : Type u) [CommRing A] [IsDomain A] : Prop :=
  ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (CommRingCat.of A)),
    IsModification f →
      letI : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
        IsGrothendieckAbelian.enoughInjectives
      letI : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
        hasExt_of_enoughInjectives _
      Subsingleton (Sheaf.H.{u, u, u, u}
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj X.sheaf) 1)

end AlgebraicGeometry
