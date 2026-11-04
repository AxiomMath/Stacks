module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# The open subspace on which a perfect complex is locally free of a given rank in one degree

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `E` be an object of
`D(𝒪_X)`.  Stacks 0D20 asserts, for integers `i` and `r`, the existence of an open subspace
`U ⊆ X` *characterised by* two clauses: on `U` the object `E` is a locally free module of rank
`r` placed in degree `i`, and a morphism `f : Y → X` factors through `U` exactly when `Lf^*E`
is such a module.

The second clause is a universal property, and a universal property has three separate pieces
of content: that some open subspace has it, that an open subspace which has it also satisfies
the first clause, and that at most one open subspace has it.  The last two are what this module
proves.  Existence is not proved here, and nothing below asserts it; see "What is not here".

## Main definitions

* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank`: finite local freeness of a
  rank prescribed as an *integer*, the form in which the source states it.
* `AlgebraicGeometry.Space.openSubspaceAsSpace` and
  `AlgebraicGeometry.Space.openSubspaceImmersion`: an open subspace of an algebraic space read
  as an algebraic space together with its inclusion.
* `AlgebraicGeometry.Space.IsFiniteLocallyFreeOfIntRankInDegree`: an object of `D(𝒪_X)` is a
  finite locally free module of rank `r` placed in degree `i`.
* `AlgebraicGeometry.Space.IsSingleDegreeRankLocus`: clause (2) of the source, the universal
  property an open subspace of `X` may have with respect to `E`, `i` and `r`.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfIntRankInDegree_of_isSingleDegreeRankLocus`:
  **clause (1) of Stacks 0D20.**  An open subspace with the universal property of clause (2)
  carries `E` as a finite locally free module of rank `r` placed in degree `i`.  This is the
  universal property applied to the inclusion of the open subspace itself, which factors
  through it by way of the identity.
* `AlgebraicGeometry.Space.eq_of_isSingleDegreeRankLocus`: **the uniqueness half of "there
  exists an open subspace characterised by" in Stacks 0D20.**  Two open subspaces with the
  universal property of clause (2) are equal: each inclusion factors through the other, and a
  subfunctor through which another subfunctor's inclusion factors contains it.

## What is not here

Existence of the open subspace is not proved, and no declaration below asserts it.  In
particular nothing here is a `Classical.choose` of an existence statement: the open subspace is
a *hypothesis* of both results, so both are statements about whatever open subspaces happen to
have the universal property, and they are vacuous if none does.  The source obtains existence
from the case of schemes by étale localization, Stacks 0BDK; the scheme case is proved as
`AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen`, where the open subscheme is
constructed as the union of the opens carrying `E` in degree `i` with rank `r`.  Transporting
that to an algebraic space needs the restriction of a derived `𝒪_X`-module to an open subspace
and the locality of the two constituent conditions on the small étale site, neither of which
exists in this development.

Perfectness of `E` is not a hypothesis of either result, exactly as in the scheme case: it is
what the source needs for existence, and both clauses proved here hold for an arbitrary object
of `D(𝒪_X)`.  Stating them without it is therefore a generalization and not a weakening.

## Implementation notes

The rank is an integer, as in the source, and not a natural number as in the scheme case
`AlgebraicGeometry.Scheme.Modules.IsSingleDegreeRank`.  A negative rank is not vacuous in the
source: the empty algebraic space is locally free of every rank, because the condition is
tested on the members of a covering and the empty space is covered by the empty family.
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank` therefore asks of each member
of a local free presentation that its basis have cardinality `r`, which for a negative `r`
forces the presentation to have no members at all; `isFiniteLocallyFreeOfIntRank_natCast_iff`
records that for a non-negative rank it is Mathlib's condition.

`Lf^*` is `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, which carries the
existence of the left derived functor as an instance argument, since the resolving datum of
Stacks 06YS is available in this tree only for a site which is
`CategoryTheory.SmallCategory`.  That argument is quantified over inside
`AlgebraicGeometry.Space.IsSingleDegreeRankLocus`, so the universal property is stated for
every morphism for which `Lf^*` exists, and the two results carry it for the inclusions of the
open subspaces they speak about.

## References

* [Stacks Project, Tag 0D20](https://stacks.math.columbia.edu/tag/0D20)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u₁

namespace AlgebraicGeometry

/-! ### Finite local freeness of an integer rank -/

namespace SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules is finite locally free of the *integer* rank `r` when it has a local free
presentation each of whose basis-indexing types has cardinality `r`.

For a non-negative `r` this is `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` at
`r.toNat`.  For a negative `r` no basis-indexing type can have cardinality `r`, so the
presentation is forced to be indexed by the empty type; the condition is then satisfied exactly
when the empty family covers the final object, which is how the source's "locally free of rank
`r`" for an integer `r` reads on the empty space. -/
def IsFiniteLocallyFreeOfIntRank (M : _root_.SheafOfModules.{u} R) (r : ℤ) : Prop :=
  ∃ q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M, q.IsLocallyFreeData ∧
    ∀ i, ∃ n : ℕ, (n : ℤ) = r ∧ Nonempty ((q.generators i).I ≃ Fin n)

/-- At a rank which is a natural number, finite local freeness of an integer rank is Mathlib's
finite local freeness of that rank. -/
theorem isFiniteLocallyFreeOfIntRank_natCast_iff (M : _root_.SheafOfModules.{u} R) (n : ℕ) :
    IsFiniteLocallyFreeOfIntRank.{u, v, u₁} M (n : ℤ) ↔
      IsFiniteLocallyFreeOfRank.{u, v, u₁} M n := by
  constructor
  · rintro ⟨q, hq, h⟩
    refine ⟨q, hq, fun i => ?_⟩
    obtain ⟨m, hm, he⟩ := h i
    obtain rfl : m = n := Nat.cast_injective hm
    exact he
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, fun i => ⟨n, rfl, h i⟩⟩

end SheafOfModules

/-! ### The open subspace -/

namespace Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The algebraic space underlying an open subspace of an algebraic space: an open subspace is
an algebraic space by the first half of `AlgebraicGeometry.Space.IsOpenSubspace`. -/
abbrev openSubspaceAsSpace {X : AlgebraicSpaces B S hS} (U : OpenSubspaces B S hS X.1) :
    AlgebraicSpaces B S hS :=
  ⟨U.1.toFunctor, U.2.1⟩

/-- The inclusion of an open subspace into the ambient algebraic space, as a morphism of
algebraic spaces. -/
abbrev openSubspaceImmersion {X : AlgebraicSpaces B S hS} (U : OpenSubspaces B S hS X.1) :
    openSubspaceAsSpace B S hS U ⟶ X :=
  ObjectProperty.homMk U.1.ι

/-- A subfunctor whose inclusion factors through a second subfunctor is contained in it: a
section of the first is the image of its own preimage under the factorization, hence lies in
the second. -/
private theorem le_of_factorsThrough {X : AlgebraicSpaces B S hS}
    {U U' : OpenSubspaces B S hS X.1}
    (g : openSubspaceAsSpace B S hS U ⟶ openSubspaceAsSpace B S hS U')
    (hg : g ≫ openSubspaceImmersion B S hS U' = openSubspaceImmersion B S hS U) :
    U.1 ≤ U'.1 := by
  have hg' : g.hom ≫ U'.1.ι = U.1.ι := by
    simpa using congrArg (fun t : openSubspaceAsSpace B S hS U ⟶ X =>
      ObjectProperty.ι _ |>.map t) hg
  intro c x hx
  have hx' : (g.hom.app c ⟨x, hx⟩).1 = x :=
    congrFun (congrArg (fun t => t.app c) hg') ⟨x, hx⟩
  exact hx' ▸ (g.hom.app c ⟨x, hx⟩).2

variable (X : AlgebraicSpaces B S hS)

/-- An object of `D(𝒪_X)` is a finite locally free module of rank `r` placed in degree `i`.

This is the shape the source's two clauses ask of `E` on the open subspace and of `Lf^*E` along
a morphism into it; the module placed in degree `i` is then the `i`-th cohomology sheaf, and the
source writes the condition as `E|_U ≅ H^i(E|_U)[-i]` with `H^i(E|_U)` locally free of
rank `r`. -/
def IsFiniteLocallyFreeOfIntRankInDegree
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (i r : ℤ) : Prop :=
  ∃ M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank M r ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor _ i).obj M)

variable (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (i r : ℤ)

/-- **Clause (2) of Stacks 0D20**, the universal property an open subspace `U ⊆ X` may have: a
morphism `f : Y ⟶ X` of algebraic spaces factors through `U` exactly when `Lf^*E` is a finite
locally free module of rank `r` placed in degree `i`.

The morphisms quantified over are those for which the derived pullback exists, that existence
being an instance argument of `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
def IsSingleDegreeRankLocus (U : OpenSubspaces B S hS X.1) : Prop :=
  ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X)
      [(smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
        (smallEtaleModuleQuasiIso B S hS X)],
    (∃ g : Y ⟶ openSubspaceAsSpace B S hS U, g ≫ openSubspaceImmersion B S hS U = f) ↔
      IsFiniteLocallyFreeOfIntRankInDegree B S hS Y
        ((smallEtaleDerivedModulePullback B S hS f).obj E) i r

/-- **Clause (1) of Stacks 0D20.**  On an open subspace with the universal property of clause
(2), the object `E` is a finite locally free module of rank `r` placed in degree `i`: the
inclusion of the open subspace factors through it by way of the identity, so the universal
property applies to it. -/
@[stacks 0D20 "clause (1), for an open subspace with the characterising universal property of \
  clause (2); existence of such an open subspace is not proved"]
theorem isFiniteLocallyFreeOfIntRankInDegree_of_isSingleDegreeRankLocus
    (U : OpenSubspaces B S hS X.1)
    [(smallEtaleModulePullbackOnHomotopy B S hS
        (openSubspaceImmersion B S hS U)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS X)]
    (hU : IsSingleDegreeRankLocus B S hS X E i r U) :
    IsFiniteLocallyFreeOfIntRankInDegree B S hS (openSubspaceAsSpace B S hS U)
      ((smallEtaleDerivedModulePullback B S hS (openSubspaceImmersion B S hS U)).obj E) i r :=
  (hU _ (openSubspaceImmersion B S hS U)).1 ⟨𝟙 _, Category.id_comp _⟩

/-- If `U'` has the universal property of clause (2) and `U` satisfies clause (1), then `U ≤ U'`:
the inclusion of `U` factors through `U'`. -/
private theorem le_of_isSingleDegreeRankLocus (U U' : OpenSubspaces B S hS X.1)
    [(smallEtaleModulePullbackOnHomotopy B S hS
        (openSubspaceImmersion B S hS U)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS X)]
    (hU : IsSingleDegreeRankLocus B S hS X E i r U)
    (hU' : IsSingleDegreeRankLocus B S hS X E i r U') :
    U.1 ≤ U'.1 := by
  obtain ⟨g, hg⟩ := (hU' _ (openSubspaceImmersion B S hS U)).2
    (isFiniteLocallyFreeOfIntRankInDegree_of_isSingleDegreeRankLocus B S hS X E i r U hU)
  exact le_of_factorsThrough B S hS g hg

/-- **The uniqueness half of "there exists an open subspace characterised by" in Stacks
0D20.**  At most one open subspace of `X` has the universal property of clause (2).

Each of the two inclusions factors through the other open subspace, because by clause (1) the
restriction of `E` along it has the required shape and the other open subspace's universal
property turns that into a factorization; and a subfunctor through which another's inclusion
factors contains it. -/
@[stacks 0D20 "uniqueness of an open subspace with the characterising universal property of \
  clause (2); existence of such an open subspace is not proved"]
theorem eq_of_isSingleDegreeRankLocus (U U' : OpenSubspaces B S hS X.1)
    [(smallEtaleModulePullbackOnHomotopy B S hS
        (openSubspaceImmersion B S hS U)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS X)]
    [(smallEtaleModulePullbackOnHomotopy B S hS
        (openSubspaceImmersion B S hS U')).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS X)]
    (hU : IsSingleDegreeRankLocus B S hS X E i r U)
    (hU' : IsSingleDegreeRankLocus B S hS X E i r U') :
    U = U' := by
  exact Subtype.ext (le_antisymm (le_of_isSingleDegreeRankLocus B S hS X E i r U U' hU hU')
    (le_of_isSingleDegreeRankLocus B S hS X E i r U' U hU' hU))

end Space

end AlgebraicGeometry

end
