module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMap
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# The global Künneth map of the box product is an isomorphism

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes with `S` affine, let `W = X ×_S Y` with
projections `p` and `q`, write `f = p ∘ a = q ∘ b` and set `A = Γ(S, 𝒪_S)`.  Let `𝓕^•` on `X/S`
and `𝓖^•` on `Y/S` be complexes of quasi-coherent modules whose differentials are differential
operators of finite order.  [Stacks, Tag 0FLT] asserts that the cup product of
[Stacks, Tag 0FLR]

`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`

is an isomorphism in `D(A)` when `X` and `Y` are quasi-compact with affine diagonal, `𝓕^•` is
bounded, `𝓖^•` is bounded below, and every `𝓕^n` and every `𝓖^m` is `S`-flat.

`Stacks.Cohomology.BoxKunneth.globalBoxKunnethMap` is that map, and by
`Stacks.Cohomology.BoxKunneth.globalBoxKunnethMap_eq` it is the global Künneth map of
[Stacks, Tag 0G7V] for the inverse-image ringed spaces followed by derived global sections of
steps (4) and (5).  So the assertion splits into the invertibility of the derived map — which is
[Stacks, Tag 0FLQ], stated as
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` on
hypotheses of its own — and the invertibility of steps (4) and (5).  Both are carried here as
explicit hypotheses, together with the invertibility of the `A`-linear global cup product on the
base; what is proved is that the three suffice.

## Main results

* `Stacks.Cohomology.BoxKunneth.isIso_boxTotalDerivedComparison`: steps (4) and (5) are invertible
  as soon as their four factors are.  Unlike the sheaf case none of the four is free, the last
  being `DerivedCategory.Q` of the step-(5) comparison.
* `Stacks.Cohomology.BoxKunneth.isIso_globalBoxKunnethMap`: **[Stacks, Tag 0FLT]**, granted those
  three inputs.

## Implementation notes

*What is carried and why.*  Three hypotheses.

* `hκ`, the invertibility of the global cup product `κ` at the pair of inverse-image complexes.
  `Stacks.Cohomology.GlobalKunneth.GlobalCupProduct` is a bare morphism of bifunctors, with no
  laws: the zero morphism inhabits it, and for that choice the Künneth map is zero and the
  assertion false.  So some hypothesis pinning `κ` is unavoidable, and affineness of `S` is what
  the source uses to supply this one.
* `hrel`, the invertibility of the relative Künneth map of [Stacks, Tag 0FLP] at the two
  inverse-image complexes.  This is the conclusion of [Stacks, Tag 0FLQ], which is
  `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` on four
  named inputs: the projection formula of [Stacks, Tag 08EU] for `a` and for `p`, the base-change
  comparison of [Stacks, Tag 08IB] for the square, and the [Stacks, Tag 079U]/[Stacks, Tag 0D5S]
  monoidality coherence.  That carrier is stated for the
  structure morphism `p ≫ a` of the product, whereas the map here is formed at
  `inverseImageBaseProjection (pullback.fst a b ≫ a)`, which
  `Stacks.Cohomology.BoxKunneth.fstProjection_comp` identifies with
  `fstProjection a b ≫ inverseImageBaseProjection a` by a proof and not definitionally; so the
  carrier applies only after transport along that identification, and `hrel` is carried whole.
* `hstep`, the invertibility of steps (4) and (5),
  `Stacks.Cohomology.BoxKunneth.boxTotalDerivedComparison`.  Mathematically this is where the
  flatness of the terms enters: it makes the two derived inverse images underived and kills the
  higher Tor of their tensor product.  `isIso_boxTotalDerivedComparison` reduces it to the four
  comparisons that carry that content.

*Why the termwise relative flatness does not discharge `hstep`.*  Every criterion in this library
for the first three of those four factors is stated at K-flatness over the *structure sheaf*:
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` and
`Stacks.SheafOfModules.isIso_toTensor_of_kFlat_left`/`_right`.  What [Stacks, Tag 0FLT] supplies
instead is `AlgebraicGeometry.IsFlatOver` of each term, flatness of the stalks over the stalks of
`𝒪_S`, and the two conditions are incomparable.  The bridge that would be needed is the stalk
computation identifying `Lp^*𝓕^• ⊗^𝐋 Lq^*𝓖^•` with `𝓕^• ⊗^𝐋_{𝒪_S} 𝓖^•` on the fibre product.
For a cartesian square that stalk check is the `Prop`
`AlgebraicGeometry.PointwiseBaseChangeOfFlatOver`, which is carried as a hypothesis wherever it is
used.  The fourth factor asks the step-(5) comparison to be a quasi-isomorphism, which no flatness
hypothesis bears on.

*Why the source's own proof is not followed.*  [Stacks, Tag 0FLT] is proved by dévissage: the
termwise split truncation `σ_{≥ i+1}𝓕^• ⟶ 𝓕^• ⟶ 𝓕^i[-i]` gives a distinguished triangle in the
homotopy category of the category of finite-order differential operators, functoriality of the
cup product turns it into a map of triangles, and induction on the number of nonzero terms reduces
to complexes concentrated in one degree, which is [Stacks, Tag 0FU4]; a tor-amplitude bound from
[Stacks, Tag 0FML] is what allows the bounded-below `𝓖^•` to be replaced by a bounded one in each
fixed degree.  That route needs three inputs.  First, the Künneth maps of [Stacks, Tag 0FLR]
and [Stacks, Tag 0G4B] must be natural in `𝓕^•`, that is,
`Stacks.Cohomology.BoxKunneth.BoxTotalComparison` must be natural in a *morphism of complexes*;
its degreewise ingredient is the naturality of
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison` in the two
differential operators,
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison_naturality`.
Second, the truncation triangles must exist in the homotopy category of
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory`.  Third, the base case
[Stacks, Tag 0FU4], `Stacks.Cohomology.GlobalKunneth.isIso_kunnethMapOfSheavesScheme`, is stated
under the same three carried inputs as here.

*The geometric hypotheses are stated but not consumed.*  They are carried as underscore-prefixed
binders and instance arguments so that the statement is the source's, following
`Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_cartesian` for [Stacks, Tag 0FXZ].
Affineness of the diagonal is spelled as affineness of `pullback.diagonal (terminal.from X)`;
flatness over the base is
`AlgebraicGeometry.IsFlatOver` of the underlying quasi-coherent module of each term, the flatness
of every stalk over the corresponding stalk of `𝒪_S`, which by the discussion following
[Stacks, Tag 08KT] is flatness as an `a^{-1}𝒪_S`-module.

*Boundedness.*  `𝓖^•` bounded below is `[L.IsStrictlyGE n₂]`, which the map of
[Stacks, Tag 0FLR] already carries.  `𝓕^•` bounded is `[K.IsStrictlyGE n₁]` together with
`[K.IsStrictlyLE n₃]`; the first of those is likewise already carried by the map, because — as
`Stacks.Cohomology.BoxKunneth.boxTotal` records — `Tot(𝓕^• ⊠ 𝓖^•)` does not exist in the category
of finite-order differential operators without it.

## References

* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.BoxKunneth

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
  (n₁ n₂ n₃ : ℤ) [K.IsStrictlyGE n₁] [K.IsStrictlyLE n₃] [L.IsStrictlyGE n₂]

/-- **Steps (4) and (5) are invertible as soon as their four factors are.**  By
`Stacks.Cohomology.BoxKunneth.boxTotalDerivedComparison_eq` the map
`Lp^*𝓕^• ⊗^𝐋_{f^{-1}𝒪_S} Lq^*𝓖^• ⟶ Tot(𝓕^• ⊠ 𝓖^•)` is a composite of four maps: the two
derived-to-degreewise inverse image comparisons
`Stacks.Cohomology.BoxKunneth.pullbackComplexComparison`, the derived-to-nonderived tensor
comparison `toTensor` of [Stacks, Tag 06YU], and `DerivedCategory.Q` of the step-(5)
comparison.  Unlike the sheaf case, none of the four is invertible for free: the fourth is the
image of `c.hom`, a morphism of complexes and not an isomorphism of them.  This is stated for an
arbitrary step-(5) datum `c`, of which `Stacks.Cohomology.BoxKunneth.boxTotalComparison` is the
one; `isIso_globalBoxKunnethMap` below consumes it at that one.

The first three are each the conclusion of a criterion the library has, but only at *absolute*
K-flatness over the structure sheaf:
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` for the
first two and `Stacks.SheafOfModules.isIso_toTensor_of_kFlat_left` or `_right` for the third.
Flatness of the terms over the base `S`, which is what [Stacks, Tag 0FLT] assumes, neither
implies nor is implied by that — see the implementation notes. -/
theorem isIso_boxTotalDerivedComparison (c : BoxTotalComparison a b K L n₁ n₂)
    (hfst : IsIso (pullbackComplexComparison (fstProjection a b) (leftComplex a K)))
    (hsnd : IsIso (pullbackComplexComparison (sndProjection a b) (rightComplex b L)))
    (htensor : IsIso ((canonicalDerivedTensorProduct
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor
      (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)))
    (hstep5 : IsIso (DerivedCategory.Q.map c.hom)) :
    IsIso (boxTotalDerivedComparison a b K L n₁ n₂ c) := by
  rw [boxTotalDerivedComparison_eq]
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_))
  · exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ hfst) _
  · exact @Functor.map_isIso _ _ _ _ _ _ _ _ hsnd
  · exact htensor
  · exact hstep5

/-- **[Stacks, Tag 0FLT].**  Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes with `S`
affine, let `A = Γ(S, 𝒪_S)`, and let `𝓕^•` on `X/S` and `𝓖^•` on `Y/S` be complexes of
quasi-coherent modules with differentials differential operators of finite order.  If `X` and `Y`
are quasi-compact with affine diagonal, `𝓕^•` is bounded, `𝓖^•` is bounded below, and every term
of `𝓕^•` and of `𝓖^•` is flat over `S`, then the cup product of [Stacks, Tag 0FLR]

`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`

is an isomorphism in `D(A)`.

The three inputs of the proof are carried as the hypotheses `hκ`, `hrel` and `hstep`, and the
geometric hypotheses are therefore not consumed; the implementation notes of this file say what
each of the three is and what the source's own dévissage would need in addition.  `hκ` is the
invertibility of the `A`-linear global cup product on the affine base, `hrel` is
[Stacks, Tag 0FLQ] at the two inverse-image complexes, and `hstep` is the invertibility of steps
(4) and (5), in which the source consumes the flatness of the terms.  What is proved here is that
the three suffice. -/
@[stacks 0FLT "the isomorphism; three inputs are carried, so the geometric hypotheses are not \
consumed: hκ, invertibility of the global cup product on the affine base, which no bare \
GlobalCupProduct has; hrel, Tag 0FLQ at the two inverse-image complexes; hstep, steps (4) and \
(5), which the tag's termwise relative S-flatness cannot discharge in this library"]
theorem isIso_globalBoxKunnethMap [IsAffine S] [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (_hK : ∀ n, IsFlatOver a.toLRSHom.toShHom (K.X n).module)
    (_hL : ∀ n, IsFlatOver b.toLRSHom.toShHom (L.X n).module)
    (κ : GlobalCupProduct S.toRingedSpace)
    (hκ : IsIso (κ.app
      ((derivedPushforward (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)),
        (derivedPushforward (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))))
    (hrel : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (DerivedCategory.Q.obj (leftComplex a K))
      (DerivedCategory.Q.obj (rightComplex b L))))
    (hstep : IsIso (boxTotalDerivedComparison a b K L n₁ n₂
      (boxTotalComparison a b K L n₁ n₂))) :
    IsIso (globalBoxKunnethMap a b K L n₁ n₂ κ) := by
  have hglob := isIso_kunnethGlobalMap (inverseImageBaseProjection a)
    (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
    (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
    (sndProjection_comp a b) κ (DerivedCategory.Q.obj (leftComplex a K))
    (DerivedCategory.Q.obj (rightComplex b L)) hκ hrel
  rw [globalBoxKunnethMap_eq]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hglob (@Functor.map_isIso _ _ _ _ _ _ _ _ hstep)

end Stacks.Cohomology.BoxKunneth

end
