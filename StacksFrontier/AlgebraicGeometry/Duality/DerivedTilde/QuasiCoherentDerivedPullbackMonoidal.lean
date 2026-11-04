module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# Derived pullback is monoidal on `D_QCoh`

For a morphism of schemes `f : X ⟶ Y`, the restriction `Lf^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` of
derived pullback ([Stacks, Tag 08DW] part (1)) is a strong monoidal functor for the monoidal
structures `Stacks.Duality.quasiCoherentDerivedMonoidal` of [Stacks, Tag 0FPT] and
[Stacks, Tag 08DX] on each side.

## Main definitions

* `Stacks.Duality.derivedPullbackDerivedMonoidal` — `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` is monoidal for
  `AlgebraicGeometry.Scheme.Modules.derivedMonoidal`.
* `Stacks.Duality.derivedPullbackCanonicalMonoidal` — the same for
  `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal`.
* `Stacks.Duality.quasiCoherentDerivedPullbackMonoidal` — the restriction to `D_QCoh` is monoidal
  for `Stacks.Duality.quasiCoherentDerivedMonoidal`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` is a strong monoidal functor** for the derived tensor products
of [Stacks, Tag 0FPT], at the locally small model. -/
@[instance_reducible]
def derivedPullbackDerivedMonoidal :
    @Functor.Monoidal _ _ (Scheme.Modules.derivedMonoidal Y) _ _
      (Scheme.Modules.derivedMonoidal X) (derivedPullback f) :=
  Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal f.toLRSHom.toShHom

/-- `Lf^*` is monoidal for the re-seated structures whose tensor bifunctor is the derived tensor
product of [Stacks, Tag 06YU] on the nose. -/
@[instance_reducible]
def derivedPullbackCanonicalMonoidal :
    @Functor.Monoidal _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _ _
      (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f) :=
  @Functor.monoidalReseat _ _ (Scheme.Modules.derivedMonoidal Y) _ _ _ _
    (Scheme.Modules.derivedMonoidal X) _ _ (derivedPullback f) (derivedPullbackDerivedMonoidal f)
    _ _ _ _

/-- The restriction of `Lf^*` to `D_QCoh` is monoidal for the full monoidal subcategories of
`(D(𝒪), canonicalDerivedMonoidal)`. -/
@[instance_reducible]
def quasiCoherentDerivedPullbackSubcategoryMonoidal :
    letI := Scheme.Modules.canonicalDerivedMonoidal Y
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    letI := quasiCoherent_isMonoidal Y
    letI := quasiCoherent_isMonoidal X
    (quasiCoherentDerivedPullback' f).Monoidal :=
  letI := Scheme.Modules.canonicalDerivedMonoidal Y
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI := quasiCoherent_isMonoidal Y
  letI := quasiCoherent_isMonoidal X
  letI := derivedPullbackCanonicalMonoidal f
  ObjectProperty.liftMonoidal _ _ _

/-- **`Lf^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` is a strong monoidal functor** for
`Stacks.Duality.quasiCoherentDerivedMonoidal` on each side, whose tensor bifunctors are
`Stacks.Duality.quasiCoherentDerivedTensor` on the nose. -/
@[instance_reducible]
def quasiCoherentDerivedPullbackMonoidal :
    @Functor.Monoidal _ _ (quasiCoherentDerivedMonoidal Y) _ _ (quasiCoherentDerivedMonoidal X)
      (quasiCoherentDerivedPullback' f) :=
  letI := Scheme.Modules.canonicalDerivedMonoidal Y
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI := quasiCoherent_isMonoidal Y
  letI := quasiCoherent_isMonoidal X
  @Functor.monoidalReseat _ _ (ObjectProperty.fullMonoidalSubcategory _) _ _ _ _
    (ObjectProperty.fullMonoidalSubcategory _) _ _ (quasiCoherentDerivedPullback' f)
    (quasiCoherentDerivedPullbackSubcategoryMonoidal f) _ _ _ _

end Stacks.Duality
