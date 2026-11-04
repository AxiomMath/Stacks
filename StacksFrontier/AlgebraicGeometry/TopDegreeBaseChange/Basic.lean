module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# The standing data for base change in top degree

[Stacks, Tag 0EX3] fixes a morphism `f : X ⟶ Y` of quasi-compact quasi-separated schemes and a
bound `d ≥ 0` above which every quasi-coherent module has vanishing higher direct image, and then
considers an arbitrary cartesian base-change square along `g : Y' ⟶ Y`. All three conclusions
(a), (b), (c) of the tag, and Tag 0E7D which invokes them, are statements about that one package
of data, so it is recorded once here.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation`: the morphism, the finiteness
  hypotheses, the vanishing hypothesis and the cartesian square.

## Implementation notes

The bound is a natural number, which is how the source's hypothesis that it is nonnegative is
recorded. Quasi-compactness and quasi-separatedness are properties of the underlying topological
spaces. The higher direct images are
`CategoryTheory.Functor.rightDerivedPlus` of
`AlgebraicGeometry.Scheme.Modules.pushforward`, indexed by `ℤ`, so that the vanishing hypothesis
can be stated for all degrees above `d` without a coercion in the quantifier.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The standing situation for top-degree base change: a morphism `f : X ⟶ Y` of quasi-compact
quasi-separated schemes whose higher direct images of quasi-coherent modules vanish above the
degree `d`, together with a cartesian base-change square. -/
public structure TopDegreeBaseChangeSituation where
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The target scheme. -/
  Y : Scheme.{u}
  /-- The original morphism. -/
  f : X ⟶ Y
  /-- The degree above which all higher direct images vanish. -/
  d : ℕ
  /-- The source is quasi-compact. -/
  isCompact_X : CompactSpace X
  /-- The source is quasi-separated. -/
  isQuasiSeparated_X : QuasiSeparatedSpace X
  /-- The target is quasi-compact. -/
  isCompact_Y : CompactSpace Y
  /-- The target is quasi-separated. -/
  isQuasiSeparated_Y : QuasiSeparatedSpace Y
  /-- Above `d`, every quasi-coherent module has zero higher direct image. -/
  vanishes_above : ∀ (i : ℤ), (d : ℤ) < i → ∀ (F : X.Modules),
    F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F)
  /-- The source of the base-changed morphism. -/
  X' : Scheme.{u}
  /-- The target of the base-changed morphism. -/
  Y' : Scheme.{u}
  /-- The upper horizontal morphism in the base-change square. -/
  g' : X' ⟶ X
  /-- The base-changed morphism. -/
  f' : X' ⟶ Y'
  /-- The lower horizontal morphism in the base-change square. -/
  g : Y' ⟶ Y
  /-- The displayed base-change square is cartesian. -/
  isPullback : IsPullback g' f' f g

end

end Stacks.AlgebraicGeometry
