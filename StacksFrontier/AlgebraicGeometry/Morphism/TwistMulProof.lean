module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistMulChart
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistMulLeg

/-!
# Tag 07ZG: the graded-algebra clause of `θ`, proved

`StacksFrontier/AlgebraicGeometry/Morphism/TwistMul.lean` states the graded-algebra clause of Tag
07ZG — that the family `θ_n` of comparison maps on the twists respects the products
`𝒪(m) ⊗ 𝒪(n) ⟶ 𝒪(m + n)` — and reduces it to the pieces of `U(ψ)`;
`StacksFrontier/AlgebraicGeometry/Morphism/TwistMulChart.lean` supplies the two multiplicativity
facts about the absolute data that the reduction needs. **This file discharges the clause.**

## The argument

Over the piece of `U(ψ)` above an affine open `U` of the base, `θ_n` is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart` — Tag 01MY's comparison map for the
induced homomorphism `Γ(U, A) ⟶ Γ(U, B)`, conjugated by `chartSourceIso` and `chartTargetIso`.
Each of those two is a *leg*: a four-factor identification
`k^*h^*M ≅ ρ^*hU^*N` built from a factorisation `k ≫ h = ρ ≫ hU ≫ c` and an identification of
`c^*M` with `N`. The two legs conjugate by the same isomorphism `ρ` and differ only in which of
`r_ψ` and the inclusion of `U(ψ)` plays `h`, so one lemma about a single leg —
`Stacks.AlgebraicGeometry.TwistMulLeg.leg_mul` — serves for both, and the clause at the chart is

`chartSourceIso` leg ∘ `ρ^*` of Tag 01MY's clause ∘ (`chartTargetIso` leg)⁻¹,

three multiplicative families joined by `mul_comp` and `mul_inv`. That composite is
`relativeTwistChart` on the nose, by `rfl`. Rewriting the three occurrences by Tag 07ZG's own
characterising property `relativeTwistMap_chart` turns it into the hypothesis of
`relativeTwistMap_mul_of_forall_chart_pullback`, and that yields the clause.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso_mul`: Tag 01NR's chart identification of
  the relative twists is multiplicative, in the normal form of
  `Stacks.AlgebraicGeometry.TwistMulLeg`. This is `pullback_chart_relativeTwistMul` with the
  leading Tag 01CD comparison cancelled.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.legA_mul` and `legB_mul`: **the two legs are
  multiplicative.** `leg_mul` at `r_ψ` along the chart of `Proj_S(A)`, and at the inclusion of
  `U(ψ)` along the chart of `Proj_S(B)`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.midMul` and `mid_mul`: Tag 01MY's multiplicativity clause
  at the chart in the normal form, and its inverse image along the chart identification of the
  domains of definition.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chart_mul`: **the clause over one piece**, for
  `relativeTwistChart`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.pieceIncl_mul` and `chart_pullback_mul`: the same with
  `relativeTwistChart` traded for the inverse image of `θ`, in the two shapes the locality
  reduction consumes.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_mul`: **the graded-algebra clause of Tag
  07ZG, unconditionally.** The hypothesis of
  `relativeTwistMap_mul_of_forall_chart_pullback` is discharged for every affine open of the base.

## Implementation notes

**One instantiation per declaration.** Each of `chartTwistIso_mul`, `legA_mul`, `legB_mul`,
`midMul`, `mid_mul`, `chart_mul` and `pieceIncl_mul` is a single application of a lemma whose
statement is at the level of variables, to arguments that are themselves named theorems. That is
the discipline `StacksFrontier/AlgebraicGeometry/TwistMultCompat/Generic.lean` records, and the reason
is the same: heartbeats are counted cumulatively over a declaration, and the elaborator's
decomposition of one of these composites against the free morphisms of the generic lemma is a
sizeable fraction of the budget on its own.

**The two legs are `legIso` by `rfl`, and that is what makes this affordable.** `chartSourceIso`
and `chartTargetIso` are *defined* as the four-factor composite that
`Stacks.AlgebraicGeometry.TwistMulLeg.legIso` is, so `leg_mul`'s conclusion is this file's
statement after one delta-step on each side. The implementation notes of
`StacksFrontier/AlgebraicGeometry/Morphism/TwistMulChart.lean` record the missing input as "the
factor-by-factor identification `relativeTwistChart ψ n U = <its four factors>`, the analogue of
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq`"; written out as an equation
between a composite of four named components and `chartSourceIso.hom`, that identification is a
`(kernel) deterministic timeout`, and as a definition in the right generality it is free. Tag 01NO
needed the equation because its comparison is a `def` with a declared type that is *not* the
composite; Tag 07ZG's is.

**No retraction is used.** The same notes record that Tag 07ZG needs "a sibling of `transport_six`
for two legs over one isomorphism", because `transport_six`'s retraction `k ≫ j = 𝟙` does not
exist for a general `ψ`. No such sibling is needed: see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Morphism/TwistMulLeg.lean`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}}

/-! ### Tag 01NR's chart identification is multiplicative, in the normal form -/

/-- **The chart identification of the relative twists is multiplicative**, with the leading Tag
01CD comparison cancelled off the source. This is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.pullback_chart_relativeTwistMul` in the normal form of
`Stacks.AlgebraicGeometry.TwistMulLeg`: the inverse image along the chart over `U` of the product
of the relative twists, followed by the chart identification on the `(m + n)`-th twist, is the
tensor product of the chart identifications followed by Tag 01MU's multiplication map. -/
public theorem chartTwistIso_mul (A : SheafGradedAlgebra S) (m n : ℤ) (U : S.affineOpens) :
    TwistMulLeg.pbMul ((relativeProj A).chart U.1 U.2) (relativeTwistMul A m n) ≫
        (chartTwistIso A (m + n) U).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace).presheaf,
            ((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace).IsSheaf⟩)).map
          (((chartTwistIso A m U).hom, (chartTwistIso A n U).hom) : (_, _) ⟶ (_, _))) ≫
        twistMultiplicationMap (A.grading U.1) m n :=
  TwistMulLeg.mul_of_comparison_gen
    ((Stacks.PullbackTensorIso.pullbackTensorIso
      ((relativeProj A).chart U.1 U.2).toLRSHom.toShHom).app
        (relativeTwist A m, relativeTwist A n))
    (TwistMulLeg.pbMul_eq ((relativeProj A).chart U.1 U.2) (relativeTwistMul A m n))
    (pullback_chart_relativeTwistMul A m n U)

variable {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-! ### The two legs

Each leg is three declarations rather than one: the identification of the chart isomorphism with
`Stacks.AlgebraicGeometry.TwistMulLeg.legIso` (a `rfl`), the transport in `legIso` form (one
application of `leg_mul`, with nothing to convert), and the passage between the two spellings by
`congrArg`. Stated as one declaration -- the transport proved directly at the `chartSourceIso`
spelling, so that the elaborator must convert `chartSourceIso` against `legIso` three times inside
the unification -- both legs report `(deterministic) timeout at whnf` at the declaration header.
Heartbeats are cumulative over a declaration and the three conversions do not fit beside the
twelve-argument application; separated, each fits with room to spare. -/

/-- **The source identification of `θ` over a piece is the generic leg identification.** True by
`rfl`: `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso` is *defined* as the four-factor
composite that `Stacks.AlgebraicGeometry.TwistMulLeg.legIso` is, at the factorisation
`pieceIncl ≫ r_ψ = (chartDomainIso)⁻¹ ≫ r_{ψ_U} ≫ chart_A` and Tag 01NR's chart identification of
the relative twists of `A`. -/
public theorem chartSourceIso_eq_legIso (x : ℤ) (U : S.affineOpens) :
    chartSourceIso ψ x U =
      TwistMulLeg.legIso (pieceIncl ψ U) (relativeMapHom ψ) (chartDomainIso ψ U).inv
        (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
        ((relativeProj A).chart U.1 U.2) (pieceIncl_comp_relativeMapHom ψ U)
        (chartTwistIso A x U) := rfl

/-- **The target identification of `θ` over a piece is the generic leg identification**, at the
factorisation `pieceIncl ≫ ι = (chartDomainIso)⁻¹ ≫ ι_{U(ψ_U)} ≫ chart_B` and Tag 01NR's chart
identification of the relative twists of `B`. True by `rfl`, for the same reason. -/
public theorem chartTargetIso_eq_legIso (x : ℤ) (U : S.affineOpens) :
    chartTargetIso ψ x U =
      TwistMulLeg.legIso (pieceIncl ψ U) ψ.relativeMapDomain.ι (chartDomainIso ψ U).inv
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
        ((relativeProj B).chart U.1 U.2) (pieceIncl_comp_ι ψ U)
        (chartTwistIso B x U) := rfl

/-- **The source leg of `θ` is multiplicative**, in the `legIso` spelling. `leg_mul` at the
factorisation of `Stacks.AlgebraicGeometry.Tag07ZGTwist.pieceIncl_comp_relativeMapHom`, with Tag
01NR's chart identification of the relative twists of `A` as the identification `χ` and
`chartTwistIso_mul` as its multiplicativity. -/
public theorem legA_mul_leg (m n : ℤ) (U : S.affineOpens) :
    TwistMulLeg.pbMul (pieceIncl ψ U)
          (TwistMulLeg.pbMul (relativeMapHom ψ) (relativeTwistMul A m n)) ≫
        (TwistMulLeg.legIso (pieceIncl ψ U) (relativeMapHom ψ) (chartDomainIso ψ U).inv
          (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
          ((relativeProj A).chart U.1 U.2) (pieceIncl_comp_relativeMapHom ψ U)
          (chartTwistIso A (m + n) U)).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map
          (((TwistMulLeg.legIso (pieceIncl ψ U) (relativeMapHom ψ) (chartDomainIso ψ U).inv
            (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
            ((relativeProj A).chart U.1 U.2) (pieceIncl_comp_relativeMapHom ψ U)
            (chartTwistIso A m U)).hom,
          (TwistMulLeg.legIso (pieceIncl ψ U) (relativeMapHom ψ) (chartDomainIso ψ U).inv
            (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
            ((relativeProj A).chart U.1 U.2) (pieceIncl_comp_relativeMapHom ψ U)
            (chartTwistIso A n U)).hom) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul (chartDomainIso ψ U).inv
          (TwistMulLeg.pbMul (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
            (twistMultiplicationMap (A.grading U.1) m n)) :=
  TwistMulLeg.leg_mul (pieceIncl ψ U) (relativeMapHom ψ) (chartDomainIso ψ U).inv
    (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
    ((relativeProj A).chart U.1 U.2) (pieceIncl_comp_relativeMapHom ψ U)
    (relativeTwistMul A m n) (twistMultiplicationMap (A.grading U.1) m n)
    (chartTwistIso A m U) (chartTwistIso A n U) (chartTwistIso A (m + n) U)
    (chartTwistIso_mul A m n U)

/-- **The target leg of `θ` is multiplicative**, in the `legIso` spelling. `leg_mul` at the
factorisation of `Stacks.AlgebraicGeometry.Tag07ZGTwist.pieceIncl_comp_ι`. The conjugating
isomorphism is the *same* `chartDomainIso` as in `legA_mul_leg`; only the morphism being
factorised and the chart differ, which is why one single-leg lemma serves for both. -/
public theorem legB_mul_leg (m n : ℤ) (U : S.affineOpens) :
    TwistMulLeg.pbMul (pieceIncl ψ U)
          (TwistMulLeg.pbMul ψ.relativeMapDomain.ι (relativeTwistMul B m n)) ≫
        (TwistMulLeg.legIso (pieceIncl ψ U) ψ.relativeMapDomain.ι (chartDomainIso ψ U).inv
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
          ((relativeProj B).chart U.1 U.2) (pieceIncl_comp_ι ψ U)
          (chartTwistIso B (m + n) U)).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map
          (((TwistMulLeg.legIso (pieceIncl ψ U) ψ.relativeMapDomain.ι (chartDomainIso ψ U).inv
            (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
            ((relativeProj B).chart U.1 U.2) (pieceIncl_comp_ι ψ U)
            (chartTwistIso B m U)).hom,
          (TwistMulLeg.legIso (pieceIncl ψ U) ψ.relativeMapDomain.ι (chartDomainIso ψ U).inv
            (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
            ((relativeProj B).chart U.1 U.2) (pieceIncl_comp_ι ψ U)
            (chartTwistIso B n U)).hom) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul (chartDomainIso ψ U).inv
          (TwistMulLeg.pbMul (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
            (twistMultiplicationMap (B.grading U.1) m n)) :=
  TwistMulLeg.leg_mul (pieceIncl ψ U) ψ.relativeMapDomain.ι (chartDomainIso ψ U).inv
    (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
    ((relativeProj B).chart U.1 U.2) (pieceIncl_comp_ι ψ U)
    (relativeTwistMul B m n) (twistMultiplicationMap (B.grading U.1) m n)
    (chartTwistIso B m U) (chartTwistIso B n U) (chartTwistIso B (m + n) U)
    (chartTwistIso_mul B m n U)

/-- **The source leg of `θ` is multiplicative**, at the spelling `relativeTwistChart` is built
from. `legA_mul_leg` with `chartSourceIso_eq_legIso` applied in the three places the
identification occurs, by whiskering rather than by conversion.

The two steps are `CategoryTheory.whisker_eq` and `CategoryTheory.eq_whisker`, not `congrArg` at
a lambda, and that is a budget matter. The factor left alone by each step is a composite over the
uncurried `Stacks.SheafOfModules.Tensor.sheafTensor`; `congrArg (fun k => that ≫ k) h` elaborates
it a second time and hands the goal a beta-redex to reduce against it, which since
`Stacks.SheafOfModules.Tensor.ringSheaf` became an ordinary `def` is a `whnf` across
`sheafCompose`. That step alone exhausts the 200000-heartbeat budget, even in a declaration carrying one
`congrArg` and nothing else. The
whisker lemmas take the factor from the goal and build no redex. -/
public theorem legA_mul (m n : ℤ) (U : S.affineOpens) :
    TwistMulLeg.pbMul (pieceIncl ψ U)
          (TwistMulLeg.pbMul (relativeMapHom ψ) (relativeTwistMul A m n)) ≫
        (chartSourceIso ψ (m + n) U).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map
          (((chartSourceIso ψ m U).hom, (chartSourceIso ψ n U).hom) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul (chartDomainIso ψ U).inv
          (TwistMulLeg.pbMul (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
            (twistMultiplicationMap (A.grading U.1) m n)) := by
  refine Eq.trans
    (whisker_eq _ (congrArg Iso.hom (chartSourceIso_eq_legIso ψ (m + n) U))) ?_
  exact Eq.trans (legA_mul_leg ψ m n U)
    (eq_whisker
      (congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map)
        (Prod.ext (congrArg Iso.hom (chartSourceIso_eq_legIso ψ m U)).symm
          (congrArg Iso.hom (chartSourceIso_eq_legIso ψ n U)).symm)) _)

/-- **The target leg of `θ` is multiplicative**, at the spelling `relativeTwistChart` is built
from. `legB_mul_leg` with `chartTargetIso_eq_legIso` applied in the three places the
identification occurs, by whiskering for the reason recorded on `legA_mul`. -/
public theorem legB_mul (m n : ℤ) (U : S.affineOpens) :
    TwistMulLeg.pbMul (pieceIncl ψ U)
          (TwistMulLeg.pbMul ψ.relativeMapDomain.ι (relativeTwistMul B m n)) ≫
        (chartTargetIso ψ (m + n) U).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map
          (((chartTargetIso ψ m U).hom, (chartTargetIso ψ n U).hom) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul (chartDomainIso ψ U).inv
          (TwistMulLeg.pbMul (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
            (twistMultiplicationMap (B.grading U.1) m n)) := by
  refine Eq.trans
    (whisker_eq _ (congrArg Iso.hom (chartTargetIso_eq_legIso ψ (m + n) U))) ?_
  exact Eq.trans (legB_mul_leg ψ m n U)
    (eq_whisker
      (congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map)
        (Prod.ext (congrArg Iso.hom (chartTargetIso_eq_legIso ψ m U)).symm
          (congrArg Iso.hom (chartTargetIso_eq_legIso ψ n U)).symm)) _)

/-! ### Tag 01MY's clause at the chart, and its inverse image -/

/-- **Tag 01MY's multiplicativity clause at the chart, in the normal form.** This is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.bundle_mult_twistMap_chart` with the two Tag 01CD
comparisons that conjugate the tensor product of the comparison maps cancelled, one off each
side. -/
public theorem midMul (m n : ℤ) (U : S.affineOpens) :
    TwistMulLeg.pbMul (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
          (twistMultiplicationMap (A.grading U.1) m n) ≫
        twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) (m + n) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((mapDomain (A.grading U.1) (B.grading U.1)
            (ψ.sectionHom U.1)).toScheme.toRingedSpace).presheaf,
            ((mapDomain (A.grading U.1) (B.grading U.1)
            (ψ.sectionHom U.1)).toScheme.toRingedSpace).IsSheaf⟩)).map
          (((twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) m),
            (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n)) :
            (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
          (twistMultiplicationMap (B.grading U.1) m n) :=
  TwistMulLeg.mul_of_comparison_split_gen
    ((Stacks.PullbackTensorIso.pullbackTensorIso
      (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).toLRSHom.toShHom).app
        (twistingSheaf (A.grading U.1) m, twistingSheaf (A.grading U.1) n))
    ((Stacks.PullbackTensorIso.pullbackTensorIso
      (mapDomain (A.grading U.1) (B.grading U.1)
        (ψ.sectionHom U.1)).ι.toLRSHom.toShHom).app
        (twistingSheaf (B.grading U.1) m, twistingSheaf (B.grading U.1) n))
    (TwistMulLeg.pbMul_eq (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
      (twistMultiplicationMap (A.grading U.1) m n))
    (TwistMulLeg.pbMul_eq (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
      (twistMultiplicationMap (B.grading U.1) m n))
    (bundle_mult_twistMap_chart ψ m n U)

/-- **The inverse image of Tag 01MY's clause along the chart identification of the domains of
definition.** The middle factor of `relativeTwistChart` is the inverse image along
`(chartDomainIso)⁻¹` of Tag 01MY's comparison map, and the inverse image of a multiplicative
family is multiplicative. -/
public theorem mid_mul (m n : ℤ) (U : S.affineOpens) :
    TwistMulLeg.pbMul (chartDomainIso ψ U).inv
          (TwistMulLeg.pbMul (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
            (twistMultiplicationMap (A.grading U.1) m n)) ≫
        (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
          (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) (m + n)) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map
          ((((Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
            (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) m)),
          ((Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
            (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n))) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul (chartDomainIso ψ U).inv
          (TwistMulLeg.pbMul (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
            (twistMultiplicationMap (B.grading U.1) m n)) :=
  TwistMulLeg.mul_pullback (chartDomainIso ψ U).inv (midMul ψ m n U)

/-! ### The clause over one piece

`relativeTwistChart` is unfolded into its three factors in a `rfl` declaration of its own, and the
transport is stated at the unfolded spelling. Stated at the folded one, so that the kernel must
delta-unfold `relativeTwistChart` three times inside the composed term, the declaration reports
`(kernel) deterministic timeout`. -/

/-- **The affine-local comparison map, unfolded into its three factors.** True by `rfl`:
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart` is *defined* as Tag 01MY's comparison
map for the induced homomorphism, conjugated by the source and target identifications. -/
public theorem relativeTwistChart_eq_comp (x : ℤ) (U : S.affineOpens) :
    relativeTwistChart ψ x U =
      (chartSourceIso ψ x U).hom ≫
        (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
            (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) x) ≫
          (chartTargetIso ψ x U).inv := rfl

/-- **The inverse image of `θ_x` along the inclusion of a piece, unfolded into the three factors of
the affine-local comparison map.** Tag 07ZG's characterising property
`relativeTwistMap_chart` followed by `relativeTwistChart_eq_comp`. -/
public theorem pullback_relativeTwistMap_eq_comp (x : ℤ) (U : S.affineOpens) :
    (Scheme.Modules.pullback (pieceIncl ψ U)).map (relativeTwistMap ψ x) =
      (chartSourceIso ψ x U).hom ≫
        (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
            (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) x) ≫
          (chartTargetIso ψ x U).inv :=
  (relativeTwistMap_chart ψ x U).trans (relativeTwistChart_eq_comp ψ x U)

/-- **A transport across three squares, the last one inverted, is multiplicative**, with every
scheme, module and morphism free: two factorisations `k ≫ h` and `ρ ≫ g` of the inverse images, a
square between them, a second square over `ρ`, and a third square over `k ≫ h'` read backwards.
This is the shape of the affine-local comparison map — a source identification, the inverse image
of Tag 01MY's comparison map, and the inverse of a target identification — and nothing here is
specific to `relativeTwistChart`: it is `mul_comp` twice over `mul_inv` once, which at free
objects is one line.

**The three transports are variables and their factorisations are hypotheses.** That keeps the
tensor arguments of the conclusion *atomic*, so the application below unifies `tm` against
`relativeTwistChart ψ m U` instead of decomposing a three-factor composite under
`Stacks.SheafOfModules.Tensor.sheafTensor`, and it confines the functoriality of the tensor
product to this declaration, where the objects are free: `mul_comp` and `mul_inv` carry
`Stacks.AlgebraicGeometry.TwistMultTransport.tensorSheafMap_comp`, which is stated for a
`CategoryTheory.RingedSpace` and exhausts the budget when it is converted against
`AlgebraicGeometry.Scheme.Modules` at the concrete objects below. Here there is nothing to
convert, and the delta-unfolding this section's note warns about does not arise.

**The four products are built by `pbMul` here rather than taken as variables of the tensor type**,
and that is what makes the application affordable. Stated with `mulP ... mulS` free of type
`((sheafTensor ⟨X⟩).obj Pm).obj Pn ⟶ Pmn` -- the shape of `mul_comp`'s own hypotheses -- every one
of the nine arguments reaches the kernel with its type spelled through `pbMul` instead, and the
kernel, which honours no reducibility attribute, converts the two spellings once per argument:
`(kernel) deterministic timeout`. Applying `pbMul` inside, as
`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.legTail_mul` does, makes each argument's
type *syntactically* the statement of `legA_mul`, `mid_mul` and `legB_mul`, and the whole module
checks in four seconds. -/
theorem mul_of_three_split_gen {W Z Y Y' D V V' : Scheme.{u}} (k : W ⟶ Z) (h : Z ⟶ Y)
    (h' : Z ⟶ Y') (ρ : W ⟶ D) (g : D ⟶ V) (g' : D ⟶ V')
    {Am An Amn : Y.Modules} {Bm Bn Bmn : Y'.Modules} {Cm Cn Cmn : V.Modules}
    {Dm Dn Dmn : V'.Modules}
    (mulA : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩).obj (Am)).obj (An)) ⟶ Amn)
    (mulB : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(Y'.toRingedSpace).presheaf, (Y'.toRingedSpace).IsSheaf⟩).obj (Bm)).obj (Bn)) ⟶ Bmn)
    (mulC : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(V.toRingedSpace).presheaf, (V.toRingedSpace).IsSheaf⟩).obj (Cm)).obj (Cn)) ⟶ Cmn)
    (mulD : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(V'.toRingedSpace).presheaf, (V'.toRingedSpace).IsSheaf⟩).obj (Dm)).obj (Dn)) ⟶ Dmn)
    {am : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h).obj Am) ⟶
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g).obj Cm)}
    {an : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h).obj An) ⟶
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g).obj Cn)}
    {amn : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h).obj Amn) ⟶
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g).obj Cmn)}
    {bm : (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g).obj Cm) ⟶
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g').obj Dm)}
    {bn : (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g).obj Cn) ⟶
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g').obj Dn)}
    {bmn : (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g).obj Cmn) ⟶
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g').obj Dmn)}
    (cm : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h').obj Bm) ≅
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g').obj Dm))
    (cn : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h').obj Bn) ≅
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g').obj Dn))
    (cmn : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h').obj Bmn) ≅
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback g').obj Dmn))
    {tm : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h).obj Am) ⟶
      (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h').obj Bm)}
    {tn : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h).obj An) ⟶
      (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h').obj Bn)}
    {tmn : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h).obj Amn) ⟶
      (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h').obj Bmn)}
    (htm : tm = am ≫ bm ≫ cm.inv) (htn : tn = an ≫ bn ≫ cn.inv)
    (htmn : tmn = amn ≫ bmn ≫ cmn.inv)
    (ha : TwistMulLeg.pbMul k (TwistMulLeg.pbMul h mulA) ≫ amn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
          ((am, an) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul ρ (TwistMulLeg.pbMul g mulC))
    (hb : TwistMulLeg.pbMul ρ (TwistMulLeg.pbMul g mulC) ≫ bmn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
          ((bm, bn) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul ρ (TwistMulLeg.pbMul g' mulD))
    (hc : TwistMulLeg.pbMul k (TwistMulLeg.pbMul h' mulB) ≫ cmn.hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
          ((cm.hom, cn.hom) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul ρ (TwistMulLeg.pbMul g' mulD)) :
    TwistMulLeg.pbMul k (TwistMulLeg.pbMul h mulA) ≫ tmn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
          ((tm, tn) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul k (TwistMulLeg.pbMul h' mulB) := by
  subst htm htn htmn
  exact TwistMulLeg.mul_comp ha
    (TwistMulLeg.mul_comp hb (TwistMulLeg.mul_inv cm cn cmn hc))

/-- **The graded-algebra clause of Tag 07ZG over the piece of `U(ψ)` above an affine open of the
base**, at `relativeTwistChart`.

`mul_of_three_split_gen` at the three factorisations of `relativeTwistChart_eq_comp`, with
`legA_mul`, `mid_mul` and `legB_mul` as the three squares. The target identification enters as the
isomorphism to be inverted, which is why `chartTargetIso` is passed explicitly: `cmn.inv` cannot be
solved for `cmn` by unification. -/
public theorem chart_mul (m n : ℤ) (U : S.affineOpens) :
    TwistMulLeg.pbMul (pieceIncl ψ U)
          (TwistMulLeg.pbMul (relativeMapHom ψ) (relativeTwistMul A m n)) ≫
        relativeTwistChart ψ (m + n) U =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map
          ((relativeTwistChart ψ m U, relativeTwistChart ψ n U) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul (pieceIncl ψ U)
          (TwistMulLeg.pbMul ψ.relativeMapDomain.ι (relativeTwistMul B m n)) :=
  mul_of_three_split_gen (pieceIncl ψ U) (relativeMapHom ψ) ψ.relativeMapDomain.ι
    (chartDomainIso ψ U).inv (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
    (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
    (relativeTwistMul A m n) (relativeTwistMul B m n)
    (twistMultiplicationMap (A.grading U.1) m n) (twistMultiplicationMap (B.grading U.1) m n)
    (chartTargetIso ψ m U) (chartTargetIso ψ n U) (chartTargetIso ψ (m + n) U)
    (relativeTwistChart_eq_comp ψ m U) (relativeTwistChart_eq_comp ψ n U)
    (relativeTwistChart_eq_comp ψ (m + n) U)
    (legA_mul ψ m n U) (mid_mul ψ m n U) (legB_mul ψ m n U)

/-- **The graded-algebra clause of Tag 07ZG over the piece of `U(ψ)` above an affine open of the
base**, with the affine-local comparison map written out as its three factors.

`chart_mul` with `relativeTwistChart_eq_comp` applied in the three places the comparison map
occurs, by whiskering for the reason recorded on `legA_mul`. -/
public theorem chart_mul_comp (m n : ℤ) (U : S.affineOpens) :
    TwistMulLeg.pbMul (pieceIncl ψ U)
          (TwistMulLeg.pbMul (relativeMapHom ψ) (relativeTwistMul A m n)) ≫
        ((chartSourceIso ψ (m + n) U).hom ≫
          (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
              (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) (m + n)) ≫
            (chartTargetIso ψ (m + n) U).inv) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map
          ((((chartSourceIso ψ m U).hom ≫
            (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
                (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) m) ≫
              (chartTargetIso ψ m U).inv), ((chartSourceIso ψ n U).hom ≫
            (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
                (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n) ≫
              (chartTargetIso ψ n U).inv)) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul (pieceIncl ψ U)
          (TwistMulLeg.pbMul ψ.relativeMapDomain.ι (relativeTwistMul B m n)) := by
  refine Eq.trans
    (whisker_eq _ (relativeTwistChart_eq_comp ψ (m + n) U).symm) ?_
  exact Eq.trans (chart_mul ψ m n U)
    (eq_whisker
      (congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map)
        (Prod.ext (relativeTwistChart_eq_comp ψ m U)
          (relativeTwistChart_eq_comp ψ n U))) _)

/-- **The clause over one piece, with the three factors folded back into the inverse image of
`θ`.** `chart_mul_comp` with `pullback_relativeTwistMap_eq_comp` applied in the three places the
comparison map occurs, by whiskering for the reason recorded on `legA_mul`. -/
public theorem pieceIncl_mul (m n : ℤ) (U : S.affineOpens) :
    TwistMulLeg.pbMul (pieceIncl ψ U)
          (pullbackRelativeTwistMul A (relativeMapHom ψ) m n) ≫
        (Scheme.Modules.pullback (pieceIncl ψ U)).map (relativeTwistMap ψ (m + n)) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map
          ((((Scheme.Modules.pullback (pieceIncl ψ U)).map (relativeTwistMap ψ m)),
            ((Scheme.Modules.pullback (pieceIncl ψ U)).map (relativeTwistMap ψ n))) :
            (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul (pieceIncl ψ U)
          (pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n) := by
  refine Eq.trans
    (whisker_eq _ (pullback_relativeTwistMap_eq_comp ψ (m + n) U)) ?_
  exact Eq.trans (chart_mul_comp ψ m n U)
    (eq_whisker
      (congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((chartImage ψ U).toScheme.toRingedSpace).presheaf,
            ((chartImage ψ U).toScheme.toRingedSpace).IsSheaf⟩)).map)
        (Prod.ext (pullback_relativeTwistMap_eq_comp ψ m U).symm
          (pullback_relativeTwistMap_eq_comp ψ n U).symm)) _)

/-- **The hypothesis of the locality reduction, discharged.** `pieceIncl_mul` read back as an
equation between two inverse images along the inclusion of the piece, which is the shape
`relativeTwistMap_mul_of_forall_chart_pullback` consumes. -/
public theorem chart_pullback_mul (m n : ℤ) (U : S.affineOpens) :
    (Scheme.Modules.pullback (pieceIncl ψ U)).map
        (pullbackRelativeTwistMul A (relativeMapHom ψ) m n ≫ relativeTwistMap ψ (m + n)) =
      (Scheme.Modules.pullback (pieceIncl ψ U)).map
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(ψ.relativeMapDomain.toScheme.toRingedSpace).presheaf,
              (ψ.relativeMapDomain.toScheme.toRingedSpace).IsSheaf⟩)).map
            (((relativeTwistMap ψ m), (relativeTwistMap ψ n)) : (_, _) ⟶ (_, _))) ≫
          pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n) :=
  TwistMulLeg.map_eq_of_mul_pullback (pieceIncl ψ U)
    (pullbackRelativeTwistMul A (relativeMapHom ψ) m n)
    (pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n)
    (relativeTwistMap ψ m) (relativeTwistMap ψ n) (relativeTwistMap ψ (m + n))
    (pieceIncl_mul ψ m n U)

/-! ### The clause -/

/-- **The graded-algebra clause of Tag 07ZG.** The family `θ_n` of comparison maps on the twists
respects the products: the inverse image along `r_ψ` of the product of the relative twists of `A`,
followed by `θ_{m+n}`, is the tensor product of `θ_m` and `θ_n` followed by the inverse image along
the inclusion of `U(ψ)` of the product of the relative twists of `B`, both pulled-back products
formed with the Tag 01CD comparison.

The clause is local on the pieces of `U(ψ)`
(`relativeTwistMap_mul_of_forall_chart_pullback`) and `chart_pullback_mul` discharges its
hypothesis over every affine open of the base. -/
public theorem relativeTwistMap_mul (m n : ℤ) :
    pullbackRelativeTwistMul A (relativeMapHom ψ) m n ≫ relativeTwistMap ψ (m + n) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((ψ.relativeMapDomain.toScheme.toRingedSpace)).presheaf,
            ((ψ.relativeMapDomain.toScheme.toRingedSpace)).IsSheaf⟩)).map
          (((relativeTwistMap ψ m), (relativeTwistMap ψ n)) : (_, _) ⟶ (_, _))) ≫
        pullbackRelativeTwistMul B ψ.relativeMapDomain.ι m n :=
  relativeTwistMap_mul_of_forall_chart_pullback ψ m n (chart_pullback_mul ψ m n)

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
