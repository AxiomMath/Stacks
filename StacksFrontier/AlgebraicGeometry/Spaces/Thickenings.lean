module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Thickenings of algebraic spaces (Stacks 05ZK)

An algebraic space `X'` over a scheme `S` is a *thickening* of a closed subspace `X ⊂ X'`
when the two have the same associated topological space. Here a closed subspace is a
subfunctor `G` of the presheaf underlying `X'` which is itself an algebraic space and whose
inclusion is a closed immersion (`AlgebraicGeometry.Space.IsClosedSubspace`), and "the same
topological space" is recorded as surjectivity of the induced map on points
`AlgebraicGeometry.Space.pointsMap`: a closed immersion is already injective on points, so
surjectivity is exactly the assertion that no point is added.

Parts (2), (3) and (4) of the source definition — first-order, finite-order and `n`th-order
thickenings — measure the order of a thickening by powers of the sheaf of ideals defining
the closed subspace. They are defined in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Order.lean`, through the chartwise
defining ideal `definingIdealAt`; see the implementation notes.

Parts (5) and (6) are defined here. A morphism of thickenings `(X ⊂ X') → (Y ⊂ Y')` is a
morphism `f' : X' ⟶ Y'` carrying `X` into `Y`; the restriction `f = f'|_X : X ⟶ Y` is then
the factorisation of `f'|_X` through the closed subspace `Y`. Over a base algebraic space
all four spaces carry a structure morphism, and `X ⟶ X'`, `Y ⟶ Y'` and `f'` are required to
commute with them.

## Main definitions

* `AlgebraicGeometry.Space.IsThickening`: **Stacks 05ZK**, part (1).
* `AlgebraicGeometry.Space.IsMorphismOfThickenings`: **Stacks 05ZK**, part (5), with the
  restriction `AlgebraicGeometry.Space.IsMorphismOfThickenings.restrict` playing the role of
  `f = f'|_X`.
* `AlgebraicGeometry.Space.IsThickeningOver` and
  `AlgebraicGeometry.Space.IsMorphismOfThickeningsOver`: **Stacks 05ZK**, part (6).

## Implementation notes

The name `IsThickening` is already taken twice at the level of **schemes** — Stacks 04EX,
`Stacks.Thickenings.IsThickening` in `StacksFrontier/AlgebraicGeometry/Thickenings.lean` and in
`StacksFrontier/AlgebraicGeometry/Thickenings.lean` — and once for
**ringed spaces**, as `AlgebraicGeometry.RingedSpaceThickening.IsThickening`. The notion
here is none of those: it is a predicate on a subfunctor of an algebraic space over a base
scheme. It therefore lives in the namespace `AlgebraicGeometry.Space`, alongside the other
subspace predicates `AlgebraicGeometry.Space.IsClosedSubspace` and
`AlgebraicGeometry.Space.IsOpenSubspace` that it is built from. Inside a context that opens
`AlgebraicGeometry`, the scheme-level notion must be written with its full prefix, exactly
as for `AlgebraicGeometry.IsClosedImmersion` versus
`AlgebraicGeometry.Space.IsClosedImmersion`.

Parts (2) to (4) of Stacks 05ZK are stated through the canonical defining ideal sheaf of a
closed subspace, which is Stacks 03MB. In this library neither 03MB nor the morphism of
small étale ringed topoi of Stacks 03G8 that 03MB is phrased through exists, so there is no
quasi-coherent ideal sheaf to take powers of, so a definition of the `n`th-order condition
phrased through Stacks 03MB would have to project data out of an object this library does
not construct. The order conditions do not need it: `definingIdealAt`, the defining ideal
read off an étale scheme chart, is enough to say that a power of the ideal vanishes, and
`AlgebraicGeometry.Space.IsNthOrderThickening` and its first- and finite-order variants are
defined that way in `Thickenings/Order.lean`, which also proves that the order descends to
every chart. Part (1) remains self-contained here, and is the only part used topologically.

Parts (5) and (6) are stated with the closed subspaces kept as subfunctors, matching part
(1): "`f'(X) ⊂ Y`" becomes `G.image f'.hom ≤ H` for the subfunctor image of
`CategoryTheory.Subfunctor.image`, and `f = f'|_X` is the factorisation
`CategoryTheory.Subfunctor.lift` of `G.ι ≫ f'.hom` through `H`. A thickening is in
particular a closed subspace, hence an algebraic space, so its subfunctor is an object of
`AlgebraicGeometry.AlgebraicSpaces` through
`AlgebraicGeometry.Space.IsThickening.subspace`, and `f` is a morphism of algebraic spaces
over `S`; that is `AlgebraicGeometry.Space.IsMorphismOfThickenings.restrictSpace`. In part
(6) the structure morphisms of the two subspaces are carried as separate data, as the source
does, and the requirement that `X ⟶ X'` and `Y ⟶ Y'` be morphisms over the base is the
equation identifying them with the composites.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

/-- **Stacks 05ZK, part (1).** A closed subspace `G` of an algebraic space `X` over `S` is a
*thickening* of `X` when the two have the same associated topological space, i.e. when the
map on points induced by the closed immersion `G.ι` is surjective. -/
@[stacks 05ZK "part (1): thickening"]
abbrev IsThickening (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (G : Subfunctor X.1) : Prop :=
  IsClosedSubspace B S hS G ∧
    Function.Surjective (pointsMap B S hS G.toFunctor G.ι)

add_to_stacks 05ZK "parts (5) and (6): morphisms of thickenings, also over a base"
  CategoryTheory.Arrow.Hom

/-! ### Morphisms of thickenings -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The closed subspace of a thickening, as an algebraic space over `S`.

A thickening is in particular a closed subspace, hence an algebraic space over `S`, so the
subfunctor `G` is an object of `AlgebraicGeometry.AlgebraicSpaces` in its own right. For a
thickening `X ⊂ X'` this is the space the source calls `X`. -/
abbrev IsThickening.subspace {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
    (hG : IsThickening B S hS X G) : AlgebraicSpaces B S hS :=
  ⟨G.toFunctor, hG.1.1⟩

variable (B S hS)

/-- **Stacks 05ZK, part (5).** Given two thickenings `G ⊂ X'` and `H ⊂ Y'` of algebraic spaces
over `S`, a *morphism of thickenings* is a morphism `f' : X' ⟶ Y'` with `f'(G) ⊂ H`, i.e. one
whose restriction to `G` factors through the closed subspace `H`.

The restriction `f = f'|_G : G ⟶ H` is
`AlgebraicGeometry.Space.IsMorphismOfThickenings.restrict`, and the pair `(f, f')` is what the
source calls the morphism of thickenings `(G ⊂ X') → (H ⊂ Y')`. -/
@[stacks 05ZK "part (5): morphism of thickenings"]
abbrev IsMorphismOfThickenings {X' Y' : AlgebraicSpaces B S hS} (G : Subfunctor X'.1)
    (H : Subfunctor Y'.1) (f' : X' ⟶ Y') : Prop :=
  IsThickening B S hS X' G ∧ IsThickening B S hS Y' H ∧ G.image f'.hom ≤ H

variable {B S hS}

/-- The image of a subfunctor `G` under `f'` is the range of `G.ι ≫ f'`. -/
private theorem image_eq_range_ι_comp {C : Type*} [Category C] {F F' : C ⥤ Type _}
    (G : Subfunctor F) (f' : F ⟶ F') :
    G.image f' = Subfunctor.range (G.ι ≫ f') := by
  rw [Subfunctor.range_comp, Subfunctor.range_ι]

/-- The restriction of `f'` to the closed subspace `G` has range inside `H`. -/
theorem IsMorphismOfThickenings.range_le {X' Y' : AlgebraicSpaces B S hS}
    {G : Subfunctor X'.1} {H : Subfunctor Y'.1} {f' : X' ⟶ Y'}
    (h : IsMorphismOfThickenings B S hS G H f') :
    Subfunctor.range (G.ι ≫ f'.hom) ≤ H := by
  exact (image_eq_range_ι_comp _ _).ge.trans h.2.2

/-- **Stacks 05ZK, part (5).** The morphism `f = f'|_X : X ⟶ Y` attached to a morphism of
thickenings: the factorisation of `f'|_G` through the closed subspace `H`. -/
def IsMorphismOfThickenings.restrict {X' Y' : AlgebraicSpaces B S hS}
    {G : Subfunctor X'.1} {H : Subfunctor Y'.1} {f' : X' ⟶ Y'}
    (h : IsMorphismOfThickenings B S hS G H f') : G.toFunctor ⟶ H.toFunctor :=
  Subfunctor.lift (G.ι ≫ f'.hom) h.range_le

/-- The restriction `f = f'|_X` of a morphism of thickenings makes the square with the two
closed immersions commute: `f` followed by `Y ⟶ Y'` is `X ⟶ X'` followed by `f'`. -/
theorem IsMorphismOfThickenings.restrict_ι {X' Y' : AlgebraicSpaces B S hS}
    {G : Subfunctor X'.1} {H : Subfunctor Y'.1} {f' : X' ⟶ Y'}
    (h : IsMorphismOfThickenings B S hS G H f') : h.restrict ≫ H.ι = G.ι ≫ f'.hom :=
  Subfunctor.lift_ι _ _

/-- **Stacks 05ZK, part (5).** The morphism `f = f'|_X : X ⟶ Y` attached to a morphism of
thickenings, read as a morphism of algebraic spaces over `S`. -/
def IsMorphismOfThickenings.restrictSpace {X' Y' : AlgebraicSpaces B S hS}
    {G : Subfunctor X'.1} {H : Subfunctor Y'.1} {f' : X' ⟶ Y'}
    (h : IsMorphismOfThickenings B S hS G H f') : h.1.subspace ⟶ h.2.1.subspace :=
  ObjectProperty.homMk h.restrict

/-- **Stacks 05ZK, part (5).** Carrying `G` into `H` is exactly the condition that the
restriction of `f'` to `G` factor through the closed subspace `H`. This is the "i.e." of the
source definition. -/
theorem isMorphismOfThickenings_iff_exists_restriction {X' Y' : AlgebraicSpaces B S hS}
    (G : Subfunctor X'.1) (H : Subfunctor Y'.1) (f' : X' ⟶ Y') :
    IsMorphismOfThickenings B S hS G H f' ↔
      IsThickening B S hS X' G ∧ IsThickening B S hS Y' H ∧
        ∃ f : G.toFunctor ⟶ H.toFunctor, f ≫ H.ι = G.ι ≫ f'.hom := by
  refine and_congr_right fun hG => and_congr_right fun hH => ⟨fun h => ?_, fun h => ?_⟩
  · have hm : IsMorphismOfThickenings B S hS G H f' := ⟨hG, hH, h⟩
    exact ⟨hm.restrict, hm.restrict_ι⟩
  · obtain ⟨f, hf⟩ := h
    rw [image_eq_range_ι_comp, ← hf]
    exact (Subfunctor.range_comp_le f H.ι).trans (Subfunctor.range_ι H).le

/-! ### Thickenings over a base -/

variable (B S hS)

/-- **Stacks 05ZK, part (6).** A *thickening over* an algebraic space `Z`: a thickening
`G ⊂ X'` of algebraic spaces over `S` together with structure morphisms `a' : X' ⟶ Z` of the
ambient space and `a : G ⟶ Z` of the subspace, such that the closed immersion `G ⟶ X'` is a
morphism over `Z`. -/
@[stacks 05ZK "part (6): thickening over a base"]
abbrev IsThickeningOver (Z : AlgebraicSpaces B S hS) {X' : AlgebraicSpaces B S hS}
    (G : Subfunctor X'.1) (a : G.toFunctor ⟶ Z.1) (a' : X' ⟶ Z) : Prop :=
  IsThickening B S hS X' G ∧ G.ι ≫ a'.hom = a

/-- **Stacks 05ZK, part (6).** A *morphism of thickenings over* an algebraic space `Z`: two
thickenings over `Z` and a morphism of thickenings between them which is a morphism over
`Z`. -/
@[stacks 05ZK "part (6): morphism of thickenings over a base"]
abbrev IsMorphismOfThickeningsOver (Z : AlgebraicSpaces B S hS)
    {X' Y' : AlgebraicSpaces B S hS} (G : Subfunctor X'.1) (H : Subfunctor Y'.1)
    (a : G.toFunctor ⟶ Z.1) (a' : X' ⟶ Z) (b : H.toFunctor ⟶ Z.1) (b' : Y' ⟶ Z)
    (f' : X' ⟶ Y') : Prop :=
  IsThickeningOver B S hS Z G a a' ∧ IsThickeningOver B S hS Z H b b' ∧
    G.image f'.hom ≤ H ∧ f' ≫ b' = a'

variable {B S hS}

/-- A morphism of thickenings over a base is in particular a morphism of thickenings. -/
theorem IsMorphismOfThickeningsOver.isMorphismOfThickenings {Z : AlgebraicSpaces B S hS}
    {X' Y' : AlgebraicSpaces B S hS} {G : Subfunctor X'.1} {H : Subfunctor Y'.1}
    {a : G.toFunctor ⟶ Z.1} {a' : X' ⟶ Z} {b : H.toFunctor ⟶ Z.1} {b' : Y' ⟶ Z}
    {f' : X' ⟶ Y'} (h : IsMorphismOfThickeningsOver B S hS Z G H a a' b b' f') :
    IsMorphismOfThickenings B S hS G H f' :=
  ⟨h.1.1, h.2.1.1, h.2.2.1⟩

/-- The restriction `f = f'|_X` of a morphism of thickenings over a base is itself a morphism
over that base. -/
theorem IsMorphismOfThickeningsOver.restrict_comp {Z : AlgebraicSpaces B S hS}
    {X' Y' : AlgebraicSpaces B S hS} {G : Subfunctor X'.1} {H : Subfunctor Y'.1}
    {a : G.toFunctor ⟶ Z.1} {a' : X' ⟶ Z} {b : H.toFunctor ⟶ Z.1} {b' : Y' ⟶ Z}
    {f' : X' ⟶ Y'} (h : IsMorphismOfThickeningsOver B S hS Z G H a a' b b' f') :
    h.isMorphismOfThickenings.restrict ≫ b = a :=
  calc h.isMorphismOfThickenings.restrict ≫ b
      = (G.ι ≫ f'.hom) ≫ b'.hom := by
        rw [← h.isMorphismOfThickenings.restrict_ι, Category.assoc, h.2.1.2]
    _ = a := by rw [Category.assoc, ← h.1.2, ← h.2.2.2]; rfl

end AlgebraicGeometry.Space

end
