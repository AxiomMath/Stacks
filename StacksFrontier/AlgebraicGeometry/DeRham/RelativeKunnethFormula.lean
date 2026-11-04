module

public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethFormula
import StacksCore.Tactic.StacksAttribute

/-!
# The relative de Rham Künneth formula

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections `p`
and `q` and structure morphism `f = p ∘ a = q ∘ b`. The relative cup product of
[Stacks, Tag 0G4B] at the two relative de Rham complexes, followed by `Rf_*` of the isomorphism
`Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{X ×_S Y/S}` of [Stacks, Tag 0FMA], is the map

`Ra_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} Rb_*Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X ×_S Y/S}`

in `D(𝒪_S)` whose invertibility is [Stacks, Tag 0FMC]. This file builds that map and proves it
invertible on the two inputs of [Stacks, Tag 0G4B]; it is the sheaf-level counterpart of
`StacksFrontier/AlgebraicGeometry/DeRham/KunnethFormula.lean`, which does the same over an affine
base for derived global sections.

## Main definitions

* `Stacks.Cohomology.BoxKunneth.deRhamRelativeKunnethMap`: **the relative cup product**
  `Ra_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} Rb_*Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X ×_S Y/S}` of [Stacks, Tag 0FMC].

## Main results

* `Stacks.Cohomology.BoxKunneth.isIso_relativeBoxKunnethMap`: the relative Künneth map of the box
  product of two complexes of finite-order differential operators is invertible as soon as the
  Künneth map of [Stacks, Tag 0FLP] and steps (4) and (5) are. This is the relative counterpart
  of `Stacks.Cohomology.BoxKunneth.isIso_globalBoxKunnethMap`, and needs no global cup product:
  on the relative side steps (1) to (3) are a constructed map and not a carried datum.

## Implementation notes

*What the relative map adds to the global one.* By
`Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMap_eq` the map of [Stacks, Tag 0G4B] is the
Künneth map of [Stacks, Tag 0FLP] followed by `Rf_*` of steps (4) and (5), so its invertibility
splits into exactly two assertions. Over an affine base the corresponding splitting of
[Stacks, Tag 0FLR] has a third factor, the `Γ(S, 𝒪_S)`-linear global cup product of
[Stacks, Section 0FKU], which this repository carries as a bare morphism of bifunctors; the
relative cup product of [Stacks, Tag 0FLP] is constructed, so no such parameter occurs here and
the invertibility of the global cup product is not among the inputs below.

*What is carried, and what each input stands for.* Two hypotheses, neither implied by the
conclusion.

* `hrel`, the invertibility of the Künneth map of [Stacks, Tag 0FLP] at the two inverse-image
  complexes. This is the conclusion of [Stacks, Tag 0FLQ], carried in this repository by
  `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` and
  itself only on four named inputs: the projection formula of [Stacks, Tag 08EU] for `a` and for
  `p`, the base-change comparison of [Stacks, Tag 08IB] for the square, and the
  [Stacks, Tag 079U]/[Stacks, Tag 0D5S] monoidality coherence. As the notes of
  `StacksFrontier/AlgebraicGeometry/DeRham/BoxTotalKunnethIsomorphism.lean` record, that carrier is
  stated for the structure morphism `p ≫ a` of the product while the map here is formed at
  `inverseImageBaseProjection (pullback.fst a b ≫ a)`, which
  `Stacks.Cohomology.BoxKunneth.fstProjection_comp` identifies with
  `fstProjection a b ≫ inverseImageBaseProjection a` by a proof and not definitionally, so the
  carrier applies only after transport along that identification.
* `hstep`, the invertibility of steps (4) and (5),
  `Stacks.Cohomology.BoxKunneth.boxTotalDerivedComparison`, which
  `Stacks.Cohomology.BoxKunneth.isIso_boxTotalDerivedComparison` reduces to its four factors.
  Mathematically this is where the flatness of the terms of the two complexes enters: it makes
  the two derived inverse images underived and kills the higher Tor of their tensor product. For
  the de Rham complex of a smooth morphism that flatness holds because each `Ω^i_{X/S}` is finite
  locally free by [Stacks, Tag 02G1] and a finite locally free module over a flat morphism is
  flat over the base, [Stacks, Tag 01V9] supplying the flatness of a smooth morphism; but every
  criterion this library has for the first three factors of `hstep` is stated at K-flatness over
  the *structure* sheaf, which neither implies nor is implied by flatness over `S`, so the
  termwise flatness does not discharge it. Because `hstep` is carried, the termwise flatness of
  `Ω^•_{X/S}` is not stated below either: [Stacks, Tag 0FMC] does not state it, deriving it from
  smoothness instead.

*Neither input follows from the conclusion.* The conclusion is the invertibility of the composite
of the `hrel` map with `Rf_*` of the `hstep` map and with the invertible `Rf_*` of
[Stacks, Tag 0FMA]; so it implies `hrel` only together with `hstep` and `hstep` only together
with `hrel`, and the pair is strictly stronger than the conclusion.

*The de Rham identification is unconditional.* The one de Rham-specific ingredient,
`AlgebraicGeometry.Scheme.Hom.deRhamBoxTotalExtendIso`, is an isomorphism of complexes with no
hypotheses, [Stacks, Tag 0FMA] transported across the extension by zero; its `Rf_*` is what
identifies the target of the box-product Künneth map with `Rf_*Ω^•_{X ×_S Y/S}`.

*Quasi-compactness and the diagonal.* [Stacks, Tag 0FMC] asks the two *morphisms* to be
quasi-compact and the two relative diagonals `X ⟶ X ×_S X` and `Y ⟶ Y ×_S Y` to be affine, so
these are `[QuasiCompact a]`, `[QuasiCompact b]`, `[IsAffineHom (pullback.diagonal a)]` and
`[IsAffineHom (pullback.diagonal b)]`; over the affine base of [Stacks, Tag 0FMB] the same
hypotheses read as quasi-compactness of the spaces and affineness of the absolute diagonal.

## References

* [Stacks Project, Tag 0FMC](https://stacks.math.columbia.edu/tag/0FMC)
* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 0G4B](https://stacks.math.columbia.edu/tag/0G4B)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.BoxKunneth

open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-! ### The relative Künneth map of a box product -/

section

variable (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
  (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]

/-- **The relative Künneth map of the box product is invertible as soon as its two factors are.**
By `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMap_eq` the map

`Ra_*(𝓕^•) ⊗^𝐋_{𝒪_S} Rb_*(𝓖^•) ⟶ Rf_*(Tot(𝓕^• ⊠ 𝓖^•))`

of [Stacks, Tag 0G4B] is the Künneth map of [Stacks, Tag 0FLP] at the two inverse-image
complexes, whose invertibility is [Stacks, Tag 0FLQ], followed by `Rf_*` of steps (4) and (5).
Unlike the global map of [Stacks, Tag 0FLR] it carries no global cup product, steps (1) to (3)
being constructed on the relative side, so these two factors are all of it. -/
theorem isIso_relativeBoxKunnethMap
    (hrel : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (DerivedCategory.Q.obj (leftComplex a K))
      (DerivedCategory.Q.obj (rightComplex b L))))
    (hstep : IsIso (boxTotalDerivedComparison a b K L n₁ n₂
      (boxTotalComparison a b K L n₁ n₂))) :
    IsIso (relativeBoxKunnethMap a b K L n₁ n₂) := by
  have hpush : IsIso ((derivedPushforward
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (boxTotalDerivedComparison a b K L n₁ n₂ (boxTotalComparison a b K L n₁ n₂))) :=
    ((derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).mapIso
      (@asIso _ _ _ _ (boxTotalDerivedComparison a b K L n₁ n₂
        (boxTotalComparison a b K L n₁ n₂)) hstep)).isIso_hom
  rw [relativeBoxKunnethMap_eq]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hrel hpush

end

/-! ### The relative de Rham Künneth formula -/

/-- **The relative cup product of [Stacks, Tag 0FMC]**

`Ra_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} Rb_*Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X ×_S Y/S}`

in `D(𝒪_S)`: the relative Künneth map of [Stacks, Tag 0G4B] at the two relative de Rham
complexes, read as `ℤ`-indexed complexes by extension by zero, followed by `Rf_*` of the
isomorphism `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{X ×_S Y/S}` of [Stacks, Tag 0FMA]. The complexes
pushed forward are the complexes of inverse-image modules underlying the de Rham complexes. The
map of [Stacks, Tag 0G4B] carries no parameter: its step-(5) comparison is constructed, as
`Stacks.Cohomology.BoxKunneth.boxTotalComparison`, and is unique by
`Stacks.Cohomology.BoxKunneth.BoxTotalComparison.hom_unique`. -/
@[stacks 0FMC "the relative cup product whose invertibility the tag asserts"]
def deRhamRelativeKunnethMap :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
          ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a (deRhamDiffOpCochainComplex a))))).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b (deRhamDiffOpCochainComplex b)))) ⟶
      (derivedPushforward.{u, u + 1, u + 1}
          (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
        (DerivedCategory.Q.obj
          (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((deRhamDiffOpComplex (pullback.fst a b ≫ a)).extend
              ComplexShape.embeddingUpNat))) :=
  relativeBoxKunnethMap a b (deRhamDiffOpCochainComplex a) (deRhamDiffOpCochainComplex b) 0 0 ≫
    (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (DerivedCategory.Q.map
        (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom))

/-- **The relative cup product does not depend on which step-(5) comparison it is built from**,
that datum being unique: a morphism out of a total complex is determined by its components on
the summands, and those are prescribed to be the degreewise comparisons. The map itself carries
no such parameter, being built from the constructed
`Stacks.Cohomology.BoxKunneth.boxTotalComparison`. -/
theorem deRhamRelativeKunnethMap_unique
    (c : BoxTotalComparison a b (deRhamDiffOpCochainComplex a)
      (deRhamDiffOpCochainComplex b) 0 0) :
    deRhamRelativeKunnethMap a b =
      (relativeBoxKunnethMap a b (deRhamDiffOpCochainComplex a)
            (deRhamDiffOpCochainComplex b) 0 0 ≫
          (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
            (DerivedCategory.Q.map
              (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom))) :=
  congrArg (fun _c : BoxTotalComparison a b (deRhamDiffOpCochainComplex a)
      (deRhamDiffOpCochainComplex b) 0 0 => deRhamRelativeKunnethMap a b) (Subsingleton.elim c c)

end Stacks.Cohomology.BoxKunneth

end
