module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening

/-!
# Vanishing of the conormal module map of a square whose lower edge factors

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `Z` a closed subspace of `X` and `Z'` a closed subspace of `X'`.  Suppose that the lower
edge `g : X ⟶ X'` factors through the subspace `Z'`, that is `g = r ≫ i'` for some
`r : X ⟶ Z'`.  Then the map `g^*𝓘' ⟶ 𝓘` of defining ideal sheaves of Stacks 04CP is **zero**,
and so is the canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of conormal modules.

This is the vanishing behind the first half of the exactness of the conormal sequence of
Stacks 06BD: in a chain of closed subspaces `Z ⊆ Y ⊆ X` the composite
`i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` is, by the composition law of part (3) of Stacks 04G2, the
map of Stacks 04CP of the outer rectangle, whose lower edge is the inclusion `Y ⟶ X` followed by
the identity and therefore factors through `Y`.

## Main results

* `AlgebraicGeometry.Space.definingIdealSheaf_top_ι`: the inclusion into the structure sheaf of
  the defining ideal sheaf of the whole space is zero.  The defining ideal of `⊤` vanishes on
  every chart by `AlgebraicGeometry.Space.definingIdealAt_eq_bot_of_retraction`, the retraction
  being the inverse of the isomorphism `⊤.ι`.
* `AlgebraicGeometry.Space.idealSheafMap_eq_zero_of_factorization`: **the map of defining ideal
  sheaves of such a square is zero.**
* `AlgebraicGeometry.Space.conormalMap_eq_zero_of_factorization`: **the canonical map of
  conormal modules of such a square is zero.**
* `AlgebraicGeometry.Space.subspaceInclusion_homOfLe_square`: the square of Stacks 04CP formed
  by a pair of closed subspaces `Z ⊆ Y` of `X` and the identity of `X`.
* `AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero`: **the vanishing of the
  composite in [Stacks Project, Tag 06BD]**, the clause of that tag which says that the two
  arrows of the conormal sequence of a pair of closed subspaces form a complex.  Its companion,
  exactness at the right term, is
  `AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces`.

## Implementation notes

**How the vanishing is read off the square at `⊤`.**  By
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` the map `g^*𝓘' ⟶ 𝓘`, followed
by the inclusion `𝓘 ⊆ 𝒪_X`, is the inverse image along `g` of the inclusion `𝓘' ⊆ 𝒪_{X'}` read
through the comparison `g^*𝒪_{X'} ⟶ 𝒪_X`, and that right-hand side does not mention the upper
subspace at all.  So it may be computed at *another* upper subspace over the same `g`: the whole
of `X`, for which the factorization `g = r ≫ i'` supplies the commutative square.  There the
left-hand side is a map into the defining ideal sheaf of `⊤`, whose inclusion into `𝒪_X` is
zero; hence the common right-hand side vanishes, hence so does `g^*𝓘' ⟶ 𝓘`, the inclusion
`𝓘 ⊆ 𝒪_X` being a monomorphism.  Nothing about the upper subspace `Z` is used, and in
particular `Z` is not required to be the inverse image of `Z'`.

**Why the chain statement makes the inverse image locally irreducible.**  The vanishing of the
composite is read off the composition law by cancelling an isomorphism, and the two sides of
that cancellation are built from the same data by two different declarations.  Comparing them
is a structural comparison of equal terms, but the elaborator will not see that until it is
stopped from unfolding `AlgebraicGeometry.Space.modulePullback` and
`AlgebraicGeometry.Space.conormalModule` to their constructions by sheafification, which the
heartbeat budget does not survive; the attribute is the same device
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleComposition.lean` uses for the same reason.

**Why the ideal-sheaf statement carries a type ascription.**  Its target is written
`(definingIdealSheaf B S hS X Z).toSheafOfModules`, whose type is
`SheafOfModules (structureRingSheaf B S hS X)`, while its source is an inverse image, whose type
is `AlgebraicGeometry.Space.Modules`.  Those are the same category, but the instance of
`Zero` on the morphisms is not found through the mixed spelling, so the target is ascribed at
`AlgebraicGeometry.Space.Modules` and the zero morphism is then available.  No bridge or
reducibility attribute is introduced: the object is named once, at the spelling the statement
needs.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
-/
@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion into the structure sheaf of the defining ideal sheaf of the whole space is
zero. -/
theorem definingIdealSheaf_top_ι (X : AlgebraicSpaces B S hS) :
    (definingIdealSheaf B S hS X ⟨⊤, isClosedSubspace_top B S hS X⟩).ι = 0 := by
  have hret : (ObjectProperty.homMk (inv (⊤ : Subfunctor X.1).ι) :
      X ⟶ (⟨(⊤ : Subfunctor X.1).toFunctor, (isClosedSubspace_top B S hS X).1⟩ :
        AlgebraicSpaces B S hS)) ≫ ObjectProperty.homMk (⊤ : Subfunctor X.1).ι = 𝟙 X :=
    ObjectProperty.hom_ext _ (IsIso.inv_hom_id _)
  ext U x
  have h1 : (definingIdealSheaf B S hS X ⟨⊤, isClosedSubspace_top B S hS X⟩).obj U ≤ ⊥ :=
    (definingIdealAt_eq_bot_of_retraction B S hS X
      ⟨⊤, isClosedSubspace_top B S hS X⟩ _ hret U).le
  exact (Submodule.mem_bot _).mp (h1 x.2)

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The map of defining ideal sheaves of a square whose lower edge factors through the lower
subspace vanishes.**  If `g : X ⟶ X'` factors as `r ≫ i'` through the closed subspace `Z'` of
`X'`, then the map `g^*𝓘' ⟶ 𝓘` of [Stacks Project, Tag 04CP] attached to any commutative square
over `g` is zero: the pullback of a regular function vanishing on `Z'` vanishes on `X`.

The implementation notes of this file record how the computation is made at the upper subspace
`⊤`, where the target of the map is the zero ideal sheaf. -/
theorem idealSheafMap_eq_zero_of_factorization
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (r : X ⟶ (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hr : r ≫ subspaceInclusion B S hS X' Z' = g) :
    (show (modulePullback B S hS g).obj
          (definingIdealSheaf B S hS X' Z').toSheafOfModules ⟶
        (show Modules.{u, u} B S hS X.1 X.2 from
          (definingIdealSheaf B S hS X Z).toSheafOfModules) from
      idealSheafMap B S hS Z Z' g f hsq) = 0 := by
  have hsqT : subspaceInclusion B S hS X ⟨⊤, isClosedSubspace_top B S hS X⟩ ≫ g =
      (subspaceInclusion B S hS X ⟨⊤, isClosedSubspace_top B S hS X⟩ ≫ r) ≫
        subspaceInclusion B S hS X' Z' := by
    rw [Category.assoc, hr]
  have keyT := idealSheafMap_comp_definingIdealSheaf_ι B S hS
    (⟨⊤, isClosedSubspace_top B S hS X⟩ : ClosedSubspaces B S hS X.1) Z' g
    (subspaceInclusion B S hS X ⟨⊤, isClosedSubspace_top B S hS X⟩ ≫ r) hsqT
  rw [definingIdealSheaf_top_ι] at keyT
  have key := (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z' g f hsq).trans
    (keyT.symm.trans comp_zero)
  exact (cancel_mono (definingIdealSheaf B S hS X Z).ι).mp (key.trans zero_comp.symm)

/-- **The canonical map of conormal modules of a square whose lower edge factors through the
lower subspace vanishes.**  The map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] is
the comparison isomorphism followed by the inverse image along the inclusion of `Z` of the map
`g^*𝓘' ⟶ 𝓘` of defining ideal sheaves, and that map is zero by
`AlgebraicGeometry.Space.idealSheafMap_eq_zero_of_factorization`; the inverse image is a left
adjoint, hence annihilates the zero morphism. -/
theorem conormalMap_eq_zero_of_factorization
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (r : X ⟶ (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hr : r ≫ subspaceInclusion B S hS X' Z' = g) :
    conormalMap B S hS Z Z' g f hsq = 0 := by
  have hadj : (modulePullback B S hS (subspaceInclusion B S hS X Z)).IsLeftAdjoint :=
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).isLeftAdjoint
  have hmz : (show (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          ((modulePullback B S hS g).obj
            (definingIdealSheaf B S hS X' Z').toSheafOfModules) ⟶
        conormalModule B S hS X Z from
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
        (idealSheafMap B S hS Z Z' g f hsq)) = 0 :=
    (congrArg (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
      (idealSheafMap_eq_zero_of_factorization B S hS Z Z' g f hsq r hr)).trans
      (Functor.map_zero _ _ _)
  rw [conormalMap_eq B S hS Z Z' g f hsq, hmz, comp_zero]


/-! ### The vanishing clause of Stacks 06BD -/

section Chain

-- Comparing two spellings of a single inverse image forces `modulePullback` open to its
-- construction by sheafification, which the heartbeat budget does not survive; the comparisons
-- below do not need it unfolded.
attribute [local irreducible] modulePullback conormalModule

/-- The inclusion of a smaller closed subspace into a larger one, as a morphism of algebraic
spaces, together with the commutative square of Stacks 04CP it forms with the identity of the
ambient space. -/
theorem subspaceInclusion_homOfLe_square {X : AlgebraicSpaces B S hS}
    (Y Z : ClosedSubspaces B S hS X.1) (hZY : Z.1 ≤ Y.1) :
    subspaceInclusion B S hS X Z ≫ 𝟙 X =
      (ObjectProperty.homMk (Subfunctor.homOfLe hZY) :
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)) ≫
        subspaceInclusion B S hS X Y :=
  ObjectProperty.hom_ext _ (by
    show Z.1.ι ≫ 𝟙 X.obj = Subfunctor.homOfLe hZY ≫ Y.1.ι
    rw [Category.comp_id]
    exact (Subfunctor.homOfLe_ι hZY).symm)

/-- **The vanishing of the composite in Stacks 06BD.**  Let `Y` and `Z` be closed subspaces of
an algebraic space `X` with `Z ⊆ Y`, let `j : Y ⟶ X` be the inclusion and let `p : j⁻¹(Z) ⟶ Z`
be the projection.  The two arrows of the conormal sequence of the pair,

`p^*(i^*𝒞_{Y/X}) ⟶ p^*𝒞_{Z/X} ⟶ 𝒞_{j⁻¹(Z)/Y}`,

compose to zero.  The first is the inverse image along `p` of the map of [Stacks Project,
Tag 04CP] at the square of `AlgebraicGeometry.Space.subspaceInclusion_homOfLe_square`, the
second is the map of [Stacks Project, Tag 04CP] at the inverse-image square, whose surjectivity
is `AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces`.

By the composition law of part (3) of [Stacks Project, Tag 04G2],
`AlgebraicGeometry.Space.conormalMap_comp`, the composite is the map of [Stacks Project,
Tag 04CP] attached to the outer rectangle, read through the composition comparison of
[Stacks Project, Tag 03LU], which is an isomorphism.  The lower edge of that rectangle is
`j ≫ 𝟙 X = j`, which factors through `Y` by the identity of `Y`, so the map of the outer
rectangle vanishes by
`AlgebraicGeometry.Space.conormalMap_eq_zero_of_factorization`. -/
@[stacks 06BD "the vanishing of the composite of the two maps of the sequence"]
theorem conormalMap_comp_conormalMap_eq_zero {X : AlgebraicSpaces B S hS}
    (Y Z : ClosedSubspaces B S hS X.1) (hZY : Z.1 ≤ Y.1) :
    (modulePullback B S hS
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)).map
        (conormalMap B S hS Z Y (𝟙 X)
          (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
          (subspaceInclusion_homOfLe_square B S hS Y Z hZY)) ≫
      conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
        (subspaceInclusion B S hS X Y)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z) = 0 := by
  have houter : subspaceInclusion B S hS
          (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
          (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) ≫
        subspaceInclusion B S hS X Y ≫ 𝟙 X =
      (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z ≫
          (ObjectProperty.homMk (Subfunctor.homOfLe hZY) :
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))) ≫
        subspaceInclusion B S hS X Y := by
    rw [← Category.assoc,
      conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z, Category.assoc,
      subspaceInclusion_homOfLe_square B S hS Y Z hZY, Category.assoc]
  have hcomp := conormalMap_comp B S hS (subspaceInclusion B S hS X Y) (𝟙 X)
    (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z Y
    (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
    (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
    (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)
    (subspaceInclusion_homOfLe_square B S hS Y Z hZY) houter
  have hvanish := conormalMap_eq_zero_of_factorization B S hS
    (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Y
    (subspaceInclusion B S hS X Y ≫ 𝟙 X)
    (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z ≫
      ObjectProperty.homMk (Subfunctor.homOfLe hZY))
    houter (𝟙 (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
    (by rw [Category.id_comp, Category.comp_id])
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).mp (hcomp.symm.trans hvanish)

end Chain

end AlgebraicGeometry.Space

end
