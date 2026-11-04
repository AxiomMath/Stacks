module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.Locus
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The open `U(ψ)` attached to an invertible sheaf on an algebraic space

[Stacks, Tag 0D2Y] is a situation, not a lemma.  It fixes a scheme `S`, an algebraic space `Y`
over `S`, a quasi-coherent graded `𝒪_Y`-algebra `𝒜`, the relative Proj
`π : Proj_Y(𝒜) ⟶ Y`, a morphism `f : X ⟶ Y` of algebraic spaces over `S`, an invertible
`𝒪_X`-module `ℒ`, and a homomorphism of graded `𝒪_X`-algebras
`ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}`.  Out of that data it *sets* `U(ψ) ⊆ X` to be the open subspace
with

  `|U(ψ)| = ⋃_{d ≥ 1} {locus where f^*𝒜_d ⟶ ℒ^{⊗ d} is surjective}`

and records that **formation of `U(ψ) ⊆ X` commutes with pullback by any morphism `X' ⟶ X`**.

This file carries that out in the form the relative Proj of an algebraic space is available at in
this library: through the scheme points of `X`.  An algebraic space is a sheaf on the big fppf
site (`AlgebraicGeometry.IsAlgebraicSpace`, [Stacks, Tag 025Y]), and
`AlgebraicGeometry.Space.GradedAlgebraPoints` presents a graded algebra on it by its restriction
`x^*𝒜` to each scheme point `x`, which is how
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjQuadruples.lean` builds the functor of
quadruples of [Stacks, Tag 084A] and how
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjBaseChange.lean` reads `g^*𝒜`.  `U(ψ)` is
presented the same way: by the open it cuts on each scheme point of `X`, computed there by the
scheme-level construction of [Stacks, Tag 01O8] in
`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/Locus.lean`.  In that presentation
the pullback of `U(ψ)` along `g : X' ⟶ X` is the family reindexed along `g`, so the tag's
compatibility assertion is the equality `GradedPowerMapPoints.locus_comap` below — the same
phenomenon that makes `AlgebraicGeometry.Space.GradedAlgebraPoints.comap_algebra` an equality
rather than a comparison isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.GradedPowerMapPoints`: the data of [Stacks, Tag 0D2Y], localised at
  the scheme points of `X` — for every scheme point `x` of `X` the restriction of `f^*𝒜` to it,
  together with the restrictions of `ℒ` and of the homogeneous components of `ψ` as the datum
  `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap` of
  [Stacks, Tag 01O8].
* `AlgebraicGeometry.Space.GradedPowerMapPoints.comap`: the pullback of that data along a
  morphism `g : X' ⟶ X` of algebraic spaces, the reindexing along `g`.
* `AlgebraicGeometry.Space.GradedPowerMapPoints.locus`: **the open `U(ψ) ⊆ X` of
  [Stacks, Tag 0D2Y]**, as the open it cuts on each scheme point of `X`.

## Main results

* `…GradedPowerMapPoints.mem_locus_iff`: **membership in `U(ψ)`.**  A point of a scheme point of
  `X` lies in `U(ψ)` exactly when the value of `ψ` at some homogeneous section of positive degree
  of `f^*𝒜` over some affine open does not vanish there.
* `…GradedPowerMapPoints.locus_comap`: **formation of `U(ψ) ⊆ X` commutes with pullback by a
  morphism `X' ⟶ X`.**  The open that `U(g^*ψ)` cuts on a scheme point `x'` of `X'` is the open
  that `U(ψ)` cuts on `x' ∘ g`.
* `…GradedPowerMapPoints.openOfPositiveSection_le_locus` and
  `…GradedPowerMapPoints.nonvanishingOpenAt_le_locus`: each member of the family lies in
  `U(ψ)`, so with `mem_locus_iff` the open is the union of the tag and not merely one containing
  it.

## Implementation notes

**The union is the one of [Stacks, Tag 01O8], not the literal surjectivity locus.**  On a scheme
point the open is `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap`'s
`coveringOpen`: the union, over the homogeneous sections `a` of positive degree of `f^*𝒜` over
the affine opens, of the open on which the section `ψ(a)` of `ℒ^{⊗ deg a}` does not vanish
([Stacks, Tag 01CY]).  Mathematically that union *is* the union of the surjectivity loci the tag
writes down, but the identification is not proved in this library: see "Not done here" in
`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/Locus.lean`, where the two
containments are shown to need the germ of a section over an open to generate a stalk and the
stalk of a pullback to be computed as a tensor product.  So the open below is defined by the
Tag 01O8 description and the clause of the attribute says so.

**`ψ` enters through its homogeneous components only.**  `GradedPowerMap` is items (5) and (6) of
the source with (6) weakened from a homomorphism of graded algebras to its family of homogeneous
components, for the reasons set out in the implementation notes of the Tag 01O8 file: the open
uses `ψ` only degreewise, and no multiplication of two sections of tensor powers over a common
open is available at this spelling.

**The graded algebra is carried at the `SheafGradedAlgebra` spelling.**  The field `algebra`
below takes values in `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, the
structure of [Stacks, Tag 01NN] that the Tag 01O8 construction consumes, and not in the
`SheafOfModules.GradedAlgebra` over `structureRingSheaf` of
`AlgebraicGeometry.Space.GradedAlgebraPoints`.  The two are different structures and neither is
obtained from the other: `SheafGradedAlgebra` also demands commutativity, the vanishing of the
negative pieces and quasi-coherence, which are exactly the hypotheses of [Stacks, Tag 0D2Y] on
`𝒜` and which `SheafOfModules.GradedAlgebra` does not record.  The same choice is made by the
Tag 085D datum `AlgebraicGeometry.Space.RelativeProjPoints`, whose `algebra` field has
the same type as the one here.

**`f`, `Y` and `𝒜` enter only through `f^*𝒜`.**  The open `U(ψ)` depends on the data only through
the pulled-back algebra, `ℒ` and `ψ`, so the datum below is indexed by the scheme points of `X`
and carries the restriction of `f^*𝒜` to them; a datum `𝒜` on `Y` together with `f : X ⟶ Y`
produces one by reindexing a Y-point datum along `f`, which is
`AlgebraicGeometry.Space.GradedAlgebraPoints.comap` at the other spelling.  The relative Proj
`π : Proj_Y(𝒜) ⟶ Y` of item (3) is not restated: it is
`AlgebraicGeometry.Space.RelativeProjGlueingData.relativeProj` with its `toBase` ([Stacks,
Tag 084C]), or on test objects `AlgebraicGeometry.Space.GradedAlgebraPoints.F` with `F.point`
([Stacks, Tag 084A]).

## Not done here

* **No open-subspace subfunctor is constructed.**  An open subspace in this library is a
  `CategoryTheory.Subfunctor` satisfying `AlgebraicGeometry.Space.IsOpenSubspace`, and
  `AlgebraicGeometry.Space.openSubspaceOfPoints` builds one from an open subset of
  `AlgebraicGeometry.Space.points`.  Assembling the family below into such a subset needs the
  opens on two scheme points to agree over a common refinement, i.e. the compatibility of the
  family under pullback along a *morphism of test objects*.  That compatibility cannot be stated
  for this datum: `GradedAlgebraPoints` and `RelativeProjPoints` carry no comparison between the
  restrictions of `𝒜` to two scheme points, which is the same gap
  `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjBaseChange.lean` records under "Not done
  here" when it observes that Tag 084A gives the values `F(T)` and not the functor `F`.  Proving
  it, once such a comparison were available, would also need the nonvanishing open of
  [Stacks, Tag 01CY] to pull back for a section over an open; `Stacks.NonvanishingPullback`'s
  `preimage_nonvanishingLocus` ([Stacks, Tag 0H78]) gives this only for a global section.
* **The morphism `r_{ℒ,ψ}` out of `U(ψ)` is [Stacks, Tag 0D2Z]** and is not built here; its
  ingredients at a scheme point are
  `AlgebraicGeometry.Space.RelativeProjPoints.pointOfPair` and its base-change compatibility in
  `StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/Spaces.lean`.

## References

* [Stacks Project, Tag 0D2Y](https://stacks.math.columbia.edu/tag/0D2Y)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The data -/

/-- **The data of [Stacks, Tag 0D2Y], localised at the scheme points of `X`.**

For every object `T` of the big fppf site and every `T`-point `x` of the algebraic space `X`: the
restriction `x^*(f^*𝒜)` of the pulled-back graded algebra to the scheme underlying `T`, together
with the restrictions of the invertible module `ℒ` and of the homogeneous components of
`ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}`, packaged as the datum of [Stacks, Tag 01O8] over the identity of
that scheme.

The base `Y`, the morphism `f : X ⟶ Y` and `𝒜` enter only through `f^*𝒜`, on which alone the
open `U(ψ)` depends; the algebra field is the analogue for `f^*𝒜` of
`AlgebraicGeometry.Space.GradedAlgebraPoints.algebra`, at the `SheafGradedAlgebra` spelling of
[Stacks, Tag 01NN] that the Tag 01O8 construction consumes. -/
public structure GradedPowerMapPoints (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The restriction of `f^*𝒜` to a scheme point of `X`. -/
  algebra (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X) :
    SheafGradedAlgebra.{u} ((BigFppfOver.toScheme B S hS).obj T)
  /-- The restrictions of `ℒ` and of the homogeneous components of `ψ` to that scheme point. -/
  pow (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X) :
    GradedPowerMap (algebra T x) (𝟙 ((BigFppfOver.toScheme B S hS).obj T))

namespace GradedPowerMapPoints

variable {B S hS} {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The pullback of the data along a morphism `g : X' ⟶ X` of algebraic spaces.**  A scheme
point `x'` of `X'` is a scheme point `x' ∘ g` of `X`, and the data at `x'` is the data there;
this is `AlgebraicGeometry.Space.GradedAlgebraPoints.comap` for the present datum. -/
public def comap (P : GradedPowerMapPoints B S hS X) (g : X' ⟶ X) :
    GradedPowerMapPoints B S hS X' where
  algebra T x := P.algebra T (x ≫ g)
  pow T x := P.pow T (x ≫ g)

/-- The algebra of the pullback at a scheme point `x'` of `X'` is the algebra at `x' ∘ g`. -/
@[simp] public theorem comap_algebra (P : GradedPowerMapPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X') :
    (P.comap g).algebra T x = P.algebra T (x ≫ g) :=
  rfl

/-- The invertible module and the components of `ψ` of the pullback at a scheme point `x'` of
`X'` are those at `x' ∘ g`. -/
@[simp] public theorem comap_pow (P : GradedPowerMapPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X') :
    (P.comap g).pow T x = P.pow T (x ≫ g) :=
  rfl

/-! ### The open `U(ψ)` -/

/-- **The open subspace `U(ψ) ⊆ X` of [Stacks, Tag 0D2Y]**, presented by the open it cuts on each
scheme point of `X`: on a `T`-point `x`, the open `U(ψ)` of [Stacks, Tag 01O8] of the restricted
data, that is the union of the opens on which the values of `ψ` at the homogeneous sections of
positive degree of `f^*𝒜` over the affine opens of the scheme of `T` do not vanish.

This is the source of the morphism `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)` of [Stacks, Tag 0D2Z].  On each
scheme point it is an abbreviation of
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.coveringOpen` of the
restricted data (it is reducible), and it is reasoned about through that open's characterising
lemmas.

Two things the present tag asks for are absent, and both are recorded here rather than in the
attribute.  Tag 0D2Y describes the same open as the union of the loci where `f^*𝒜_d ⟶ ℒ^{⊗ d}`
is surjective; identifying the two descriptions still needs the stalk of the pullback `f^*𝒜_d`
computed as a tensor product, for which see the "Not done here" section of
`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/Locus.lean`.  And the family of
opens below is not assembled into an open-subspace subfunctor object. -/
@[stacks 0D2Y "the open U(psi) of the situation, presented by the opens it cuts on the scheme \
points of X; on a scheme point it is the union, over the homogeneous sections of positive degree \
of f^*A over the affine opens, of the opens where the value of psi does not vanish, which is the \
description of Tag 01O8"]
public def locus (P : GradedPowerMapPoints B S hS X) (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X) : ((BigFppfOver.toScheme B S hS).obj T).Opens :=
  (P.pow T x).coveringOpen

attribute [reducible] locus

/-- Each member of the family lies in `U(ψ)`. -/
public theorem openOfPositiveSection_le_locus (P : GradedPowerMapPoints B S hS X)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X) (p : PositiveSection (P.algebra T x)) :
    (P.pow T x).openOfPositiveSection p ≤ P.locus T x :=
  (P.pow T x).openOfPositiveSection_le_coveringOpen p

/-- Each member of the family, written out on a triple `(V, d, a)` of an affine open of the
scheme of `T`, a positive degree and a homogeneous section of that degree over it, lies in
`U(ψ)`. -/
public theorem nonvanishingOpenAt_le_locus (P : GradedPowerMapPoints B S hS X)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X) (n : ℕ)
    (V : ((BigFppfOver.toScheme B S hS).obj T).Opens) (hV : IsAffineOpen V)
    (a : Γ((P.algebra T x).piece ((n + 1 : ℕ) : ℤ), V)) :
    (P.pow T x).nonvanishingOpenAt (n + 1) V a ≤ P.locus T x :=
  (P.pow T x).nonvanishingOpenAt_le_coveringOpen n V hV a

/-- A point of `U(ψ)` lies in a member of the family, so `U(ψ)` is the union of the tag and not
merely an open containing it. -/
public theorem exists_mem_openOfPositiveSection_of_mem_locus
    (P : GradedPowerMapPoints B S hS X) (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X)
    {z : (BigFppfOver.toScheme B S hS).obj T} (hz : z ∈ P.locus T x) :
    ∃ p : PositiveSection (P.algebra T x), z ∈ (P.pow T x).openOfPositiveSection p :=
  (P.pow T x).exists_mem_openOfPositiveSection_of_mem_coveringOpen hz

/-- **Membership in `U(ψ)`.**  A point of the scheme of `T` lies in the open that `U(ψ)` cuts on
a `T`-point `x` of `X` exactly when the value of `ψ` at some homogeneous section of positive
degree of `f^*𝒜` over some affine open does not vanish there. -/
@[stacks 0D2Y "membership in U(psi): a point of a scheme point of X lies in U(psi) exactly when \
the value of psi at some homogeneous section of f^*A of positive degree over some affine open \
does not vanish there"]
public theorem mem_locus_iff (P : GradedPowerMapPoints B S hS X) (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X) {z : (BigFppfOver.toScheme B S hS).obj T} :
    z ∈ P.locus T x ↔
      ∃ p : PositiveSection (P.algebra T x), z ∈ (P.pow T x).openOfPositiveSection p :=
  (P.pow T x).mem_coveringOpen_iff

/-! ### Compatibility with pullback -/

/-- **Formation of `U(ψ) ⊆ X` commutes with pullback by a morphism `g : X' ⟶ X` of algebraic
spaces**, the final assertion of [Stacks, Tag 0D2Y].  The open that `U(g^*ψ)` cuts on a scheme
point `x'` of `X'` is the open that `U(ψ)` cuts on the scheme point `x' ∘ g` of `X`, which is the
open that the pullback of `U(ψ)` along `g` cuts on `x'`. -/
@[simp, stacks 0D2Y "formation of U(psi) commutes with pullback by a morphism of algebraic \
spaces X' -> X: the open cut by U(g^*psi) on a scheme point x' of X' is the open cut by U(psi) \
on x' composed with g"]
public theorem locus_comap (P : GradedPowerMapPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X') :
    (P.comap g).locus T x = P.locus T (x ≫ g) :=
  rfl

/-- Pullback compatibility, pointwise: a point of the scheme of `T` lies in the open cut by
`U(g^*ψ)` on `x'` exactly when it lies in the open cut by `U(ψ)` on `x' ∘ g`. -/
public theorem mem_locus_comap_iff (P : GradedPowerMapPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X')
    {z : (BigFppfOver.toScheme B S hS).obj T} :
    z ∈ (P.comap g).locus T x ↔ z ∈ P.locus T (x ≫ g) :=
  Iff.rfl

/-- Pulling the data back twice is pulling it back along the composite, so the opens of the two
iterated pullbacks of `U(ψ)` agree. -/
public theorem locus_comap_comap (P : GradedPowerMapPoints B S hS X)
    {X'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ X) (g' : X'' ⟶ X')
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'') :
    ((P.comap g).comap g').locus T x = P.locus T (x ≫ g' ≫ g) := by
  rw [locus_comap, locus_comap, Category.assoc]

end GradedPowerMapPoints

end AlgebraicGeometry.Space

end
