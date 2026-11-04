module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Torsion sheaves on schemes of dimension at most one: the standing situation

Let `k` be an algebraically closed field, let `X` be a separated scheme of finite type over `k`
whose underlying space has Krull dimension at most one, and let `F` be a torsion abelian sheaf on
the small étale site of `X`. This file bundles these data into a single structure.

## Main definitions

* `Stacks.EtaleCohomology.TorsionSheafSituation`: the algebraically closed base field, the
  separated finite-type scheme of dimension at most one over it together with its structure
  morphism, and the torsion abelian sheaf on its small étale site, with coefficients in
  `AddCommGrpCat.{max (u + 1) v}`.

## References

* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- An algebraically closed field `k`, a separated scheme `X` of finite type over `k` whose
underlying space has Krull dimension at most one, and a torsion abelian sheaf `F` on the small
étale site of `X`. -/
@[stacks_fixed 0A52]
public structure TorsionSheafSituation where
  /-- The base field. -/
  k : Type u
  /-- The base field is a field. -/
  [field : Field k]
  /-- The base field is algebraically closed. -/
  [isAlgClosed : IsAlgClosed k]
  /-- The scheme over the base field. -/
  X : Scheme.{u}
  /-- The structure morphism from `X` to the spectrum of the base field. -/
  structureMorphism : X ⟶ Spec (.of k)
  /-- The structure morphism is separated. -/
  [isSeparated : IsSeparated structureMorphism]
  /-- The structure morphism is locally of finite type. -/
  [locallyOfFiniteType : LocallyOfFiniteType structureMorphism]
  /-- The structure morphism is quasi-compact, which with the previous field is finite type. -/
  [quasiCompact : QuasiCompact structureMorphism]
  /-- The underlying space of `X` has Krull dimension at most one. -/
  dimension_le_one : topologicalKrullDim X ≤ 1
  /-- The abelian sheaf on the small étale site of `X`. -/
  F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}
  /-- Every section of `F` is annihilated by a positive integer after restriction along each
  member of some covering sieve. -/
  isTorsion : Stacks.Torsion.torsionSheafProperty (smallEtaleTopology X) F

attribute [instance] TorsionSheafSituation.field TorsionSheafSituation.isAlgClosed
  TorsionSheafSituation.isSeparated TorsionSheafSituation.locallyOfFiniteType
  TorsionSheafSituation.quasiCompact

end Stacks.EtaleCohomology

end
