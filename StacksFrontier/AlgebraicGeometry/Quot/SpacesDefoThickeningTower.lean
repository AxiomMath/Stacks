module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderThickeningSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The morphism of first order thickenings attached to a square-zero base extension

Let `B` be a big fppf site, `S` a scheme contained in it, and let `i : T ⟶ T'` be a closed
immersion of objects of the site defined by a square-zero ideal — in the application below,
`T = Spec(R₁)` and `T' = Spec(Rₙ)` for a surjection `Rₙ → R₁` whose kernel `Iₙ` satisfies
`Iₙ² = 0`.  Let `g : X' ⟶ T'` be a morphism of algebraic spaces into the algebraic space
represented by `T'`, and let `X = g⁻¹(T)` be the inverse image of [Stacks Project, Tag 083Q].

This file records that
```
X  --⊆--→  X'
|          |
|          g
↓          ↓
T  --⊆--→  T'
```
is then a *morphism of first order thickenings* of algebraic spaces whose square of ambient
spaces is a fibre product square by construction, and that when `g` is flat the canonical map
of conormal modules of that square is an isomorphism.

## Context

This is the opening of the body of [Stacks Project, Tag 0D3X], the proof that the stack
`Spaces'_{fp, flat, proper}` satisfies openness of versality by Artin's criterion
[Stacks Project, Tag 0CXU]. It begins: *"Let `Iₙ = Ker(Rₙ → R₁)`.  We may think of
`(X₁ ⊂ Xₙ) → (Spec(R₁) ⊂ Spec(Rₙ))` as a morphism of first order thickenings"*, and then invokes
[Stacks Project, Tag 06BH] at that morphism to read the structure sheaf of `Xₙ` as an extension
of `𝒪_{X₁}` by `𝒪_{X₁} ⊗_{R₁} Iₙ`. The first order thickening upstairs is the order clause of
[Stacks Project, Tag 09ZX], and the conormal comparison is the direction (1) ⟹ (2) of
[Stacks Project, Tag 06BH], with both first order thickening hypotheses discharged.

## Main definitions

* `AlgebraicGeometry.Space.squareZeroSubspace`: the closed subspace of the algebraic space
  represented by `T'` cut out by a square-zero closed immersion `i : T ⟶ T'` of the site.
* `AlgebraicGeometry.Space.definingIdealSheafPullbackConormalIso`: the identification of the
  defining ideal of `g⁻¹(T) ⊆ X'` with the inverse image of `𝒞_{T/T'}`, pinned by
  `AlgebraicGeometry.Space.definingIdealSheafPullbackConormalIso_inv`.

## Main results

* `AlgebraicGeometry.Space.isFirstOrderThickening_squareZeroSubspace`: `T ⊆ T'` is a first order
  thickening of algebraic spaces.
* `AlgebraicGeometry.Space.isFirstOrderThickening_preimage_squareZeroSubspace`: so is its inverse
  image `g⁻¹(T) ⊆ X'`, along an arbitrary `g`.
* `AlgebraicGeometry.Space.isIso_conormalMap_preimage_squareZeroSubspace`: for flat `g`, the
  canonical map `f^*𝒞_{T/T'} ⟶ 𝒞_{g⁻¹(T)/X'}` of [Stacks Project, Tag 04CP] is an isomorphism.
  Both first order thickening hypotheses are discharged, so flatness of `g` is the only
  hypothesis.
* `AlgebraicGeometry.Space.definingIdealSheafPullbackConormalIso_inv`: the equation pinning that
  identification, so that it is about the kernel of `𝒪_{X'} ⟶ 𝒪_{g⁻¹(T)}` itself.

## Scope

Only the first stage of the source's argument is carried. Not covered: the identification of
`𝒞_{T/T'}` with `Iₙ` and of its inverse image with `𝒪_{X₁} ⊗_{R₁} Iₙ`
([Stacks Project, Tag 0D3F]), the unique extension of [Stacks Project, Tag 0D3Q] on the small
étale site of an algebraic space, the realization of the resulting sheaf as a first order
thickening ([Stacks Project, Tag 05ZT]), and the converse (2) ⟹ (1) of Tag 06BH used at the
limit. The index `n` is fixed throughout: the statements are about a single stage of the tower.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The closed subspace cut out by a square-zero closed immersion of the site.**  For a closed
immersion `i : T ⟶ T'` of objects of the big fppf site whose kernel ideal squares to zero, the
range of `yoneda.map i` is a closed subspace of the algebraic space represented by `T'`.

In the body of [Stacks Project, Tag 0D3X] this is `Spec(R₁) ⊆ Spec(Rₙ)`, cut out by
`Iₙ = Ker(Rₙ → R₁)`. -/
abbrev squareZeroSubspace {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) :
    ClosedSubspaces B S hS ((schemeSpaceFunctor B S hS).obj T').1 :=
  ⟨Subfunctor.range (yoneda.map i), isClosedSubspace_range_yoneda_map B S hS i hi.1⟩

/-- **A square-zero closed immersion of the site is a first order thickening of algebraic
spaces.**  This is `AlgebraicGeometry.Space.isFirstOrderThickening_range_yoneda_map`, the case
`n = 1` of the order clause of [Stacks Project, Tag 05ZK] for a represented closed subspace,
read at `AlgebraicGeometry.Space.squareZeroSubspace`. -/
theorem isFirstOrderThickening_squareZeroSubspace {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) :
    IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj T')
      (squareZeroSubspace B S hS i hi).1 :=
  isFirstOrderThickening_range_yoneda_map B S hS i hi

/-- **The inverse image of a square-zero base extension is a first order thickening.**  Let
`i : T ⟶ T'` be a closed immersion of objects of the site with square-zero kernel and let
`g : X' ⟶ T'` be an arbitrary morphism of algebraic spaces into the algebraic space represented
by `T'`.  Then the inverse image `g⁻¹(T)` of [Stacks Project, Tag 083Q] is a first order
thickening of `X'`.

In the body of [Stacks Project, Tag 0D3X] this is the thickening `X₁ ⊂ Xₙ`, where
`X₁ = Xₙ ×_{Spec(Rₙ)} Spec(R₁)`.  It is the order clause of [Stacks Project, Tag 09ZX],
`AlgebraicGeometry.Space.isFirstOrderThickening_preimage`, applied to
`AlgebraicGeometry.Space.isFirstOrderThickening_squareZeroSubspace`; no flatness of `g` is
needed. -/
theorem isFirstOrderThickening_preimage_squareZeroSubspace {T T' : BigFppfOver B S hS}
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
    {X' : AlgebraicSpaces B S hS} (g : X' ⟶ (schemeSpaceFunctor B S hS).obj T') :
    IsFirstOrderThickening B S hS X'
      (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi)).1 :=
  isFirstOrderThickening_preimage B S hS (squareZeroSubspace B S hS i hi).1 g
    (isFirstOrderThickening_squareZeroSubspace B S hS i hi)

/-- **The conormal comparison of the morphism of first order thickenings of
[Stacks Project, Tag 0D3X].**  Let `i : T ⟶ T'` be a closed immersion of objects of the site
with square-zero kernel, and let `g : X' ⟶ T'` be a *flat* morphism of algebraic spaces into the
algebraic space represented by `T'`.  Then the canonical map of conormal modules
`f^*𝒞_{T/T'} ⟶ 𝒞_{g⁻¹(T)/X'}` of [Stacks Project, Tag 04CP] is an isomorphism, `f` being the
projection `g⁻¹(T) ⟶ T`.

This is the direction (1) ⟹ (2) of [Stacks Project, Tag 06BH],
`AlgebraicGeometry.Space.isIso_conormalMap_firstOrderThickening_of_isFlat`, at the configuration
the body of [Stacks Project, Tag 0D3X] puts it in — and with *both* of its first order
thickening hypotheses discharged, by
`AlgebraicGeometry.Space.isFirstOrderThickening_squareZeroSubspace` downstairs and
`AlgebraicGeometry.Space.isFirstOrderThickening_preimage_squareZeroSubspace` upstairs.  So
flatness of `g` is the only hypothesis left, as it is in the source, where the thickenings are
part of the configuration rather than assumptions about it.

Flatness is the chartwise flatness of [Stacks Project, Tag 03ML] part (1),
`AlgebraicGeometry.Space.IsFlat`, which is what the source's `Xₙ → Spec(Rₙ)` satisfies; it is
carried to flatness of the induced morphism of small étale ringed topoi by
[Stacks Project, Tag 073C]. -/
theorem isIso_conormalMap_preimage_squareZeroSubspace {T T' : BigFppfOver B S hS}
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
    {X' : AlgebraicSpaces B S hS} (g : X' ⟶ (schemeSpaceFunctor B S hS).obj T')
    (hg : IsFlat B S hS g.hom) :
    IsIso (conormalMap B S hS (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi))
      (squareZeroSubspace B S hS i hi) g
      (preimageProjection B S hS g (squareZeroSubspace B S hS i hi))
      (conormalEtaleRestrictionSquare B S hS g (squareZeroSubspace B S hS i hi))) :=
  isIso_conormalMap_firstOrderThickening_of_isFlat B S hS g (squareZeroSubspace B S hS i hi)
    (isFirstOrderThickening_squareZeroSubspace B S hS i hi)
    (isFirstOrderThickening_preimage_squareZeroSubspace B S hS i hi g)
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS g).1 hg)

/-- **The defining ideal of `X₁ ⊂ Xₙ` is the pullback of the defining ideal of
`Spec(R₁) ⊂ Spec(Rₙ)`.**  In the configuration of
`AlgebraicGeometry.Space.isIso_conormalMap_preimage_squareZeroSubspace`, the defining ideal sheaf
of `g⁻¹(T) ⊆ X'` is isomorphic, as a module on the small étale site of `X'`, to the direct image
along the inclusion of `g⁻¹(T)` of the inverse image along the projection `g⁻¹(T) ⟶ T` of the
conormal module `𝒞_{T/T'}`.

This is the source's reading of [Stacks Project, Tag 06BH] in the body of
[Stacks Project, Tag 0D3X]: the kernel of `𝒪_{Xₙ} ⟶ 𝒪_{X₁}` is `𝒪_{X₁} ⊗_{R₁} Iₙ`.  Two
identifications compose to give it.  First, for a *first order* thickening the defining ideal
sheaf already is its own pushed-forward conormal module, `𝓘 ≅ i_*i^*𝓘`, which is
`AlgebraicGeometry.Space.firstOrderConormalModuleIso` — the map `𝓘 ⟶ 𝓘/𝓘²` of the source, an
isomorphism because `𝓘² = 0`.  Second, that conormal module is the inverse image of `𝒞_{T/T'}`,
which is `AlgebraicGeometry.Space.isIso_conormalMap_preimage_squareZeroSubspace` above, i.e.
Tag 06BH and the flatness of `g`.

What is *not* here, and is what separates this from the source's displayed sequence, is the
identification of `𝒞_{T/T'}` with `Iₙ` as an `R₁`-module and of its inverse image with the base
ring tensor product `𝒪_{X₁} ⊗_{R₁} Iₙ` of [Stacks Project, Tag 0D3F].

Composed with the conormal comparison and with
`AlgebraicGeometry.Space.firstOrderConormalModuleι` this isomorphism is the inclusion of the
ideal into `𝒪_{X'}`; the equation pinning it is
`AlgebraicGeometry.Space.definingIdealSheafPullbackConormalIso_inv` below. -/
@[sga "3 III 0.14" "partial"]
def definingIdealSheafPullbackConormalIso {T T' : BigFppfOver B S hS}
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} (g : W ⟶ (schemeSpaceFunctor B S hS).obj T')
    (hg : IsFlat B S hS g.hom) :
    (definingIdealSheaf B S hS W
          (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi))).toSheafOfModules ≅
      (modulePushforward B S hS (subspaceInclusion B S hS W
          (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi)))).obj
        ((modulePullback B S hS
            (preimageProjection B S hS g (squareZeroSubspace B S hS i hi))).obj
          (conormalModule B S hS ((schemeSpaceFunctor B S hS).obj T')
            (squareZeroSubspace B S hS i hi))) :=
  firstOrderConormalModuleIso B S hS
      (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi))
      (isFirstOrderThickening_preimage_squareZeroSubspace B S hS i hi g) ≪≫
    (modulePushforward B S hS (subspaceInclusion B S hS W
      (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi)))).mapIso
      (@asIso _ _ _ _ _
        (isIso_conormalMap_preimage_squareZeroSubspace B S hS i hi g hg)).symm

/-- **The characterising property of
`AlgebraicGeometry.Space.definingIdealSheafPullbackConormalIso`.**  Its inverse is the direct
image of the conormal comparison of
`AlgebraicGeometry.Space.isIso_conormalMap_preimage_squareZeroSubspace`, followed by the inverse
of the unit `𝓘 ≅ i_*i^*𝓘` of
`AlgebraicGeometry.Space.firstOrderConormalModuleIso`.

So the isomorphism really does identify the kernel of `𝒪_{X'} ⟶ 𝒪_{g⁻¹(T)}` — and not merely
some abstractly isomorphic module — with the inverse image of `𝒞_{T/T'}`: composing this
equation with `AlgebraicGeometry.Space.firstOrderConormalModuleIso` and then with
`AlgebraicGeometry.Space.firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι`
exhibits the inclusion of the ideal into `𝒪_{X'}` through it. -/
theorem definingIdealSheafPullbackConormalIso_inv
    {T T' : BigFppfOver B S hS} (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} (g : W ⟶ (schemeSpaceFunctor B S hS).obj T')
    (hg : IsFlat B S hS g.hom) :
    (definingIdealSheafPullbackConormalIso B S hS i hi g hg).inv =
      (modulePushforward B S hS (subspaceInclusion B S hS W
          (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi)))).map
          (conormalMap B S hS
            (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi))
            (squareZeroSubspace B S hS i hi) g
            (preimageProjection B S hS g (squareZeroSubspace B S hS i hi))
            (conormalEtaleRestrictionSquare B S hS g (squareZeroSubspace B S hS i hi))) ≫
        (firstOrderConormalModuleIso B S hS
          (preimageSubspace B S hS g (squareZeroSubspace B S hS i hi))
          (isFirstOrderThickening_preimage_squareZeroSubspace B S hS i hi g)).inv :=
  rfl

end AlgebraicGeometry.Space

end
