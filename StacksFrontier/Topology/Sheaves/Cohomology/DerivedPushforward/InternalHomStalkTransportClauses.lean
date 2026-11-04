module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomEquivalenceTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDinaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkOnePointTarget

/-!
# The three clauses of a tensor--hom bijection, on a ringed space and over a ring

`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomEquivalenceTransport`
consumes, for each of the two internal homs it compares, the three naturality clauses of its
tensor--hom bijection.  This file supplies all six: three for the derived internal hom of a ringed
space (Tag 08DI, whose clauses are Tag 08J8) and three for a derived tensor--hom adjunction over a
commutative ring (Tag 0A63, whose clauses are fields of the bundle).

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.curriedSourceNatural_ringedSpace`,
  `…curriedHomDinatural_ringedSpace`, `…curriedTargetNatural_ringedSpace`: the three clauses of
  Tag 08DI on a ringed space.
* `Stacks.Cohomology.DerivedInternalHomPullback.derivedCurryHomEquiv_naturality_target_ringedSpace`
  and `…_toEquiv`: the target clause of Tag 08J8 read on a ringed space, and then with the
  additive equivalence read as a bijection.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.sourceNatural`, `…homDinatural`,
  `…targetNatural`: the three clauses of Tag 0A63 over a commutative ring.
* `Stacks.Cohomology.DerivedInternalHomStalk.pointStalkInternalHomComparisonOfTensorIso`: with all
  six clauses in hand, `PointStalkInternalHomComparison X x` follows from an isomorphism of tensor
  bifunctors.

## Implementation notes

*Nothing is crossed here.*  The three clauses on the ringed space are stated against the
*curried* derived internal hom, which is the shape all three of Tag 08J8's clauses are proved at,
and the three over the ring are stated against the *uncurried* one, which is the shape the fields
of `StacksDraft.DerivedHom.DerivedHomAdjunction` are stated at.  The crossing between the two
spellings is paid inside `InternalHomEquivalenceTransport`, over arbitrary categories, by
`Stacks.Cohomology.DerivedInternalHomPullback.EquivalenceTranspose.uncurryObj_map_mkHom_id` and
its companion; paying it here instead makes each of the three declarations exceed the
elaborator's recursion depth.

*Why each clause is closed by `convert … using 1` and not by `exact`.*  Each clause of the library is
stated at a predicate of its own — `Transpose.TensorHomEquivNaturalLeft` against
`EquivalenceTranspose.CurriedSourceNatural`, and likewise for the other two — and at the
*unapplied* family `fun A B C => (RingedSite.derivedCurryHomEquiv _ A B C).toEquiv` rather than at
`tensorHomBijection`.  Either difference alone is free: swapping the predicate at a literally
identical bijection costs nothing, and swapping `tensorHomBijection Z` for the lambda costs
nothing *while the family is unapplied*, which is the observation already recorded on
`tensorHomEquivNaturalLeft_ringedSpace`.  Both at once is not free: unfolding the two predicates
puts the two spellings of the bijection under an applied `DFunLike` coercion, whose instance
argument carries the spelling of the derived tensor product, and one `isDefEq` on that equation
exhausts the elaborator's recursion depth — which is what the three declarations below used to do.
`intro` first and then `convert … using 1` settles the coercion's arguments one at a time, and
each clause goes through in seconds.  No `set_option` is involved.

*Why the structure ring is made `instance_reducible` here.*  The residual each of those `convert`
calls has to discharge is an equation between the two spellings of the bijection under a
`DFunLike` coercion whose instance argument is indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf`, an ordinary definition — see the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUniverseLift`.  An ordinary definition does
not unfold at `TransparencyMode.instances`, which is the transparency at which instance search and
`convert`'s own congruence closing both run, so the two readings of the index never meet there and
all three residuals are left open.  The `attribute [local instance_reducible]` below declares
nothing and changes no statement; it lets that one definition unfold where the residuals are
discharged, and the three `convert` calls then close by themselves.

*Which spelling of the bijection.*  Tag 08DI is registered on
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv`, which is *defined* as
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` at the opens site and equal to it by `rfl` as
a family.  Under an applied coercion the two are not interchangeable within the elaborator's
budget, so the clauses below are stated at the site-level spelling, which is the one Tag 08J8 is
proved at; see the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility`.

No `@[stacks …]` attribute is attached: each clause below is one already in the library, restated at the
predicate the transport consumes, and the tags stay where they are.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedInternalHomPullback

open Stacks.Cohomology.DerivedInternalHomPullback.EquivalenceTranspose

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

-- This file-local attribute is needed because `Stacks.SheafOfModules.Tensor.ringSheaf`
-- carries no declaration-site `@[reducible]`; its reducibility is granted file by file
-- through local attribute entries, as here.
-- Without it the three transport clauses below are left
-- with an open `Iff` between the two spellings of the bijection.
-- Two of the three *can* be closed by restatement -- pinning
-- `(D := DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules Z))` on
-- `CurriedSourceNatural` for the source clause, and `convert … using 2` then `rfl` for
-- `derivedCurryHomEquiv_naturality_target_ringedSpace` -- but the target clause cannot be, and
-- the reason is structural rather than a missing trick: it has no predicate-shaped
-- counterpart to `convert` against, so this file is where the crossing between the two
-- spellings is paid, and its statement is not free to respell because
-- `InternalHomPullbackLocality`, `InternalHomPullbackStrictlyPerfect` and
-- `InternalHomPullbackModels` all consume it.  `convert` at depths 2, 3 and 4 leaves
-- the same single `Iff`: it cannot decompose `@Eq α a b` against `@Eq α' c d` while
-- `α` and `α'` are not syntactically equal.
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable (Z : RingedSpace.{u, u})

/-- The bijection of Tag 08DI on a ringed space, at the spelling Tag 08J8 is proved at and read
as a bijection rather than as an isomorphism of abelian groups. -/
abbrev tensorHomBijection
    (A B C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (A ⟶ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).obj C) ≃
      ((internalHomTensorUncurried Z).obj (A, B) ⟶ C) :=
  (RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).toEquiv

/-- **Tag 08J8 in the source variable.**  This is
`Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivNaturalLeft_ringedSpace`, whose
predicate `Transpose.TensorHomEquivNaturalLeft` is the same statement. -/
theorem curriedSourceNatural_ringedSpace :
    CurriedSourceNatural (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
      (internalHomTensorUncurried Z) (tensorHomBijection Z) := by
  intro A A' B C φ ψ
  convert tensorHomEquivNaturalLeft_ringedSpace Z A A' B C φ ψ using 1

/-- **Tag 08J8 in the internal-hom variable.**  This is
`Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivDinatural_ringedSpace`, whose
predicate `Transpose.TensorHomEquivDinatural` is the same statement. -/
theorem curriedHomDinatural_ringedSpace :
    CurriedHomDinatural (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
      (internalHomTensorUncurried Z) (tensorHomBijection Z) := by
  intro A B B' C φ ψ
  convert tensorHomEquivDinatural_ringedSpace Z A B B' C φ ψ using 1

/-- **Tag 08J8 in the target variable, read on a ringed space.**  This is
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_target` at
`Stacks.SheafOfModules.ringedSite Z.sheaf`, with the derived internal hom written as
`Stacks.SheafOfModules.derivedSheafHom Z.sheaf` rather than as the site's own
`derivedSheafHomBifunctor`.  The two are the same bifunctor, and `convert … using 1` settles the
difference argument by argument; see the implementation notes of this file. -/
theorem derivedCurryHomEquiv_naturality_target_ringedSpace
    (A B : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    {C C' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)}
    (φ : C ⟶ C')
    (ψ : A ⟶ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).obj C) :
    RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C'
        (ψ ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).map φ) =
      RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C ψ ≫ φ := by
  convert RingedSite.derivedCurryHomEquiv_naturality_target
    (Stacks.SheafOfModules.ringedSite Z.sheaf) φ ψ using 1

/-- `derivedCurryHomEquiv_naturality_target_ringedSpace` with the additive equivalence of Tag 08DI
read as a bijection, which is the shape `CurriedTargetNatural` is stated at.

The coercion is traded at each end by `AddEquiv.coe_toEquiv` applied at its argument, exactly as
on `derivedCurryHomEquiv_dinaturality_uncurried_toEquiv`: the unapplied equality of the two
coercions costs nothing, whereas asking for the applied equality by `rfl` exceeds the elaborator's
recursion depth. -/
theorem derivedCurryHomEquiv_naturality_target_ringedSpace_toEquiv
    (A B : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    {C C' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)}
    (φ : C ⟶ C')
    (ψ : A ⟶ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).obj C) :
    (RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C').toEquiv
        (ψ ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).map φ) =
      (RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).toEquiv ψ ≫ φ :=
  (congrFun (AddEquiv.coe_toEquiv (RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C'))
      (ψ ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).map φ)).trans
    ((derivedCurryHomEquiv_naturality_target_ringedSpace Z A B φ ψ).trans
      (congrArg (· ≫ φ)
        (congrFun (AddEquiv.coe_toEquiv (RingedSite.derivedCurryHomEquiv
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C)) ψ).symm))

/-- **Tag 08J8 in the target variable.**  This is
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_target` read at the opens site; no
tensor product occurs in the identity, only in the type of its two sides. -/
theorem curriedTargetNatural_ringedSpace :
    CurriedTargetNatural (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
      (internalHomTensorUncurried Z) (tensorHomBijection Z) := by
  intro A B C C' φ ψ
  convert derivedCurryHomEquiv_naturality_target_ringedSpace_toEquiv Z A B φ ψ using 1

end Stacks.Cohomology.DerivedInternalHomPullback

/-! ### The clauses over a commutative ring -/

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

open Stacks.Cohomology.DerivedInternalHomPullback.EquivalenceTranspose

universe v w

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R)

/-- The bijection of Tag 0A63 read as a bijection rather than as an isomorphism of abelian
groups. -/
abbrev homBijection (A B C : DerivedCategory (ModuleCat.{v} R)) :
    (A ⟶ d.hom.obj (op B, C)) ≃ (d.tensor.obj (A, B) ⟶ C) :=
  (d.homEquiv A B C).toEquiv

/-- **Tag 0A63 in the source variable**: the field `homEquiv_naturality_left`. -/
theorem sourceNatural : SourceNatural d.hom d.tensor d.homBijection :=
  fun _ _ _ _ φ ψ => d.homEquiv_naturality_left φ ψ

/-- **Tag 0A63 in the internal-hom variable**: the field `homEquiv_dinaturality`. -/
theorem homDinatural : HomDinatural d.hom d.tensor d.homBijection :=
  fun _ _ _ _ φ ψ => d.homEquiv_dinaturality φ ψ

/-- **Tag 0A63 in the target variable**: the field `homEquiv_naturality_right`. -/
theorem targetNatural : TargetNatural d.hom d.tensor d.homBijection :=
  fun _ _ _ _ φ ψ => d.homEquiv_naturality_right φ ψ

end StacksDraft.DerivedHom.DerivedHomAdjunction

/-! ### The internal-hom compatibility from a tensor compatibility -/

namespace Stacks.Cohomology.DerivedInternalHomStalk

open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedInternalHomPullback
open Stacks.Cohomology.DerivedInternalHomPullback.EquivalenceTranspose
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (X : RingedSpace.{u, u}) (x : X.carrier)

attribute [local instance] stalkCommRing

/-- **The derived tensor--hom adjunction on `D(𝒪_{X,x})`.**  Its `hom` field is
`Stacks.Cohomology.DerivedInternalHomStalk.stalkDerivedHom`, which is *defined* as that field, and
its `tensor` field is the derived tensor product the comparison below is stated against. -/
abbrev stalkDerivedAdjunction : StacksDraft.DerivedHom.DerivedHomAdjunction (stalkRing X x) :=
  StacksDraft.DerivedHom.derivedHomAdjunctionOverRing (stalkRing X x)

/-- **`PointStalkInternalHomComparison X x` from the bifunctor isomorphism alone.**  For a ringed
space `X` and a point `x`, an isomorphism of bifunctors

`(− ⊗^L_{𝒪_Y} −) ⋙ E ≅ (E × E) ⋙ (− ⊗^L_{𝒪_{X,x}} −)`,

where `Y = {x}` is the one-point ringed space of `pointSpace` and `E` is the equivalence
`pointStalkDerivedEquiv X x`, carries the derived internal hom of `Y` to `RHom` over `𝒪_{X,x}`.

This is `EquivalenceTranspose.internalHomTransportIsoCurried` with every other input supplied:
the three clauses of Tag 08J8 on the ringed space `Y` by `curriedSourceNatural_ringedSpace`,
`curriedHomDinatural_ringedSpace` and `curriedTargetNatural_ringedSpace` above, and the three
clauses of Tag 0A63 over `𝒪_{X,x}` by the fields of `stalkDerivedAdjunction X x`, which
`derivedHomAdjunctionOverRing` produces with no hypothesis.  No associator or unitor
compatibility is asked of `m`.

The isomorphism `m` is constructed as
`Stacks.Cohomology.DerivedInternalHomStalk.stalkDerivedTensorIso`, which gives
`Stacks.Cohomology.DerivedInternalHomStalk.pointStalkInternalHomComparison`. -/
def pointStalkInternalHomComparisonOfTensorIso
    (m : internalHomTensorUncurried (pointSpace X x) ⋙ (pointStalkDerivedEquiv X x).functor ≅
      (pointStalkDerivedEquiv X x).functor.prod (pointStalkDerivedEquiv X x).functor ⋙
        (stalkDerivedAdjunction X x).tensor) :
    PointStalkInternalHomComparison X x :=
  internalHomTransportIsoCurried (pointStalkDerivedEquiv X x)
    (internalHomTensorUncurried (pointSpace X x))
    (stalkDerivedAdjunction X x).tensor m
    (Stacks.SheafOfModules.derivedSheafHom (pointSpace X x).sheaf)
    (stalkDerivedAdjunction X x).hom
    (tensorHomBijection (pointSpace X x))
    (stalkDerivedAdjunction X x).homBijection
    (curriedSourceNatural_ringedSpace (pointSpace X x))
    (StacksDraft.DerivedHom.DerivedHomAdjunction.sourceNatural _)
    (curriedHomDinatural_ringedSpace (pointSpace X x))
    (StacksDraft.DerivedHom.DerivedHomAdjunction.homDinatural _)
    (curriedTargetNatural_ringedSpace (pointSpace X x))
    (StacksDraft.DerivedHom.DerivedHomAdjunction.targetNatural _)

end Stacks.Cohomology.DerivedInternalHomStalk

end
