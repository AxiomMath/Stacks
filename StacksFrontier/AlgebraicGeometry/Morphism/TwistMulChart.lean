module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistMul
public import StacksFrontier.AlgebraicGeometry.TwistMultCompat.Generic

/-!
# Tag 07ZG: the two multiplicative inputs of the graded-algebra clause, on a chart

`StacksFrontier/AlgebraicGeometry/Morphism/TwistMul.lean` states the graded-algebra clause of Tag
07ZG and reduces it, in two ways; the reduction that survives is the one to the pieces of `U(ψ)`
(`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_mul_of_forall_chart_pullback`), whose
hypothesis is the clause restricted to the piece over each affine open `U` of the base. Over such
a piece, `θ_n` is `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart` — Tag 01MY's
comparison map for the induced homomorphism `Γ(U, A) ⟶ Γ(U, B)`, conjugated by the chart
identifications of Tag 01NR — so discharging that hypothesis needs two multiplicativity facts
about the *absolute* data, and this file supplies both.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.pullback_chart_relativeTwistMul`: **the chart
  identification of the relative twists is multiplicative, in pullback form.** The inverse image
  along the chart over `U` of the product of the relative twists, followed by the chart
  identification on the `(m + n)`-th twist, is the Tag 01CD comparison followed by the tensor
  product of the chart identifications followed by Tag 01MU's multiplication map on `Proj Γ(U, A)`.

  `Stacks.AlgebraicGeometry.TwistMapsInvertible.restrict_chart_mulSheaf_eq` is this square in
  *restriction* form, with `Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso` where
  the Tag 01CD comparison stands here. It is the only input with mathematical content; the passage
  between the two forms is `conj_mul_of_restrict` below.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.bundle_mult_twistMap_chart`: **Tag 01MY's
  multiplicativity clause at the chart, with its leading Tag 01CD comparison cancelled.** This is
  `Stacks.AlgebraicGeometry.ProjMapCard.twistMap_comp_pullbackTwistMultiplication` for the induced
  homomorphism of graded section rings, in the shape a transport consumes — the exact analogue, for
  Tag 07ZG's chart, of `Stacks.AlgebraicGeometry.TwistMultTransport.bundle_mult_twistMap` for Tag
  01NO's inclusion of affine opens.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.conj_mul_of_restrict`: the re-association that turns a
  multiplication square written with a conjugated comparison into one written with the comparison
  itself. Stated with every object and morphism free, in an arbitrary category, and applied by
  `exact`: at the concrete types neither `rw` nor `simp` can match `CategoryTheory.Category.assoc`,
  the category instance on sheaves of modules on a scheme being reached through a `def`.

## Three inputs that are already available

The implementation notes of `StacksFrontier/AlgebraicGeometry/Morphism/TwistMul.lean` list three
inputs as open. Each of them is available.

1. **"The brick is `Stacks.PullbackCompMonoidal.comparison_tensor`, and what is owed on top of it
   is the bridge to the spelling used here."** No bridge is owed and that brick is not needed. The
   compatibility of the Tag 01CD comparison with the contraction of an iterated inverse image is
   already proved **at the scheme-level spelling this area uses**, in both directions, as
   `Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackComp` and
   `comparison_pullbackComp_hom`
   (`StacksFrontier/AlgebraicGeometry/TwistMultTransport/Structural.lean:209` and `:348`) — stated for
   `AlgebraicGeometry.Scheme.Modules.pullbackComp`, `Stacks.PullbackTensorIso.pullbackTensorIso`
   and `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap`, which are the three spellings
   `TwistMul.lean` is written in. It is not obtained from `comparison_tensor`: it is proved
   directly, by `Stacks.AlgebraicGeometry.ProjMapCard.pullbackTensor_hom_ext` and the pullback-unit
   formulas. The same file also has the congruence factor
   (`comparison_pullbackCongr_inv`, `comparison_pullbackCongr_hom`) and the identity factor
   (`comparison_pullbackId`), and
   `Stacks.AlgebraicGeometry.TwistMultCompat.comparison_tensorSheafMap_nat` has naturality in the
   two module arguments.

2. **"A tensor analogue of `chartSourceIso` is owed."** The generic form of it is available:
   `Stacks.AlgebraicGeometry.TwistMultCompat.transport_six`
   (`StacksFrontier/AlgebraicGeometry/TwistMultCompat/Generic.lean:571`) transports a multiplication
   identity along a six-factor composite of `pullbackCongr`, `pullbackComp`, a functor image,
   `pullbackComp`, `pullbackCongr` and `pullbackId`, at the level of variables, with no `Proj` in
   sight. What is genuinely missing is narrower, and is stated under "What is not done" below.

3. **"Identifying the transported composite with the named comparison is the obstruction."**
   `StacksFrontier/AlgebraicGeometry/TwistMultTransport/Basic.lean` records this under "What is NOT
   here", but it is not an obstruction:
   `Stacks.AlgebraicGeometry.TwistMultCompat.projInclusionTwistIso_preserves_products`
   (`StacksFrontier/AlgebraicGeometry/TwistMultCompat/Basic.lean:147`) carries `@[stacks 01NO]` for
   exactly that assertion. The method is to run the transport at the level of variables and to pass
   to the named comparison by one `congrArg` per twist index.

## The two chart inputs, and two further inputs that are not needed

The two results above are the chart inputs of the clause, and the clause is **proved**:
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_mul` in
`StacksFrontier/AlgebraicGeometry/Morphism/TwistMulProof.lean` consumes exactly
`pullback_chart_relativeTwistMul` and `bundle_mult_twistMap_chart` and nothing else with
mathematical content. No declaration in this file carries the project tag, because the tag belongs
on the declaration stating the whole of Tag 07ZG,
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeProjMapTriple` in
`StacksFrontier/AlgebraicGeometry/Morphism/TwistAlgebra.lean`.

Two further things might seem to stand between those inputs and the hypothesis of
`relativeTwistMap_mul_of_forall_chart_pullback`. **Neither is needed.**

1. **"A sibling of `transport_six` for two legs over one isomorphism is owed."** It is not. The
   observation that `transport_six` does not instantiate at Tag 07ZG is correct — for a general
   `ψ` there is no retraction `k ≫ j = 𝟙`, because `U(ψ_U)` is a proper open of `Proj Γ(U, B)` —
   but the conclusion drawn from it does not follow. `transport_six` needs that retraction because
   it lands on modules living on the *outer* scheme, which it reaches by identifying an inverse
   image with the identity. `Stacks.AlgebraicGeometry.TwistMulLeg.leg_mul` lands on `ρ^*hU^*N` and
   identifies nothing, so it applies to **one leg at a time**, with no hypothesis beyond the
   factorisation, and `ρ`'s invertibility is never used. The two legs of Tag 07ZG are then two
   instances of it, joined afterwards by `mul_comp` and `mul_inv`. Nothing about "two legs over one
   isomorphism" has to be built.

2. **"The factor-by-factor identification `relativeTwistChart ψ n U = <its four factors>` ...
   nothing of the kind exists."** It is not a theorem to be proved but a definition to be stated in
   the right generality. `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso` and
   `chartTargetIso` are both `Stacks.AlgebraicGeometry.TwistMulLeg.legIso` **by `rfl`**, cheaply,
   and `relativeTwistChart` is their conjugate by `rfl` too. The analogy with
   `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq` is misleading: Tag 01NO
   needed that equation because its comparison is a `def` whose declared type is *not* the
   composite, whereas Tag 07ZG's is. Written out instead as an equation between
   `chartSourceIso.hom` and a composite of four named components, the identification is a
   `(kernel) deterministic timeout`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
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
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RestrictionSections
open Stacks.AlgebraicGeometry.TwistMultTransport
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}}

/-- **A multiplication square written with a conjugated comparison is one written with the
comparison itself.** Given an isomorphism `R` factored as `rT ≫ cmp ≫ w`, with `cmp` the Tag 01CD
comparison and `rT`, `w` the conjugating identifications, a multiplication square for `R.inv` is a
multiplication square for `cmp`.

Every object and morphism is free and the category is arbitrary, and the lemma is applied by
`exact`: at the concrete types below neither `rw` nor `simp` can match
`CategoryTheory.Category.assoc`, because `AlgebraicGeometry.Scheme.Modules` is a `def` and the
category instance is therefore invisible at the transparency a rewrite builds its motive at. This
is the device `StacksFrontier/AlgebraicGeometry/TwistMultTransport/Structural.lean` records for the
same reason. -/
public theorem conj_mul_of_restrict {C : Type*} [Category C]
    {Y₁ Y₂ X₁ X₂ Z₁ Z₂ Tw TT : C}
    {R : Y₁ ≅ X₁} {rT : Y₁ ⟶ Y₂} {rT' : Y₂ ⟶ Y₁} {cmp : Y₂ ⟶ X₂} {w : X₂ ⟶ X₁}
    {MR : Y₁ ⟶ Z₁} {MP : Y₂ ⟶ Z₂} {rZ' : Z₂ ⟶ Z₁} {χ : Z₂ ⟶ Tw}
    {γZ : Z₁ ⟶ Tw} {γZ' : Tw ⟶ Z₁} {tsm : X₂ ⟶ TT} {tsmγ : X₁ ⟶ TT} {mult : TT ⟶ Tw}
    (hR : R.hom = rT ≫ cmp ≫ w)
    (hrT : rT' ≫ rT = 𝟙 Y₂) (hγ : γZ' ≫ γZ = 𝟙 Tw) (hχ : χ = rZ' ≫ γZ)
    (htsm : tsm = w ≫ tsmγ)
    (hnat : MP ≫ rZ' = rT' ≫ MR)
    (hkey : R.inv ≫ MR = tsmγ ≫ mult ≫ γZ') :
    MP ≫ χ = cmp ≫ tsm ≫ mult := by
  subst hχ htsm
  rw [← Category.assoc, hnat, Category.assoc, (Iso.inv_comp_eq R).mp hkey, hR]
  simp only [Category.assoc, hγ, Category.comp_id, reassoc_of% hrT]

/-! ### The spelling facts, each in its own declaration

Each of the five hypotheses `pullback_chart_relativeTwistMul` feeds to `conj_mul_of_restrict` is
stated here, written out, in its own declaration. Supplied inline instead — as one `exact` with
seven arguments — the declaration reports `(deterministic) timeout at whnf, maximum number of
heartbeats (200000) has been reached` at its header, and the limit cannot be raised in this
library. The cost is the elaborator's decomposition of the two conjugated comparisons against the
free morphisms of `conj_mul_of_restrict`, and heartbeats are counted cumulatively over a
declaration; one such decomposition fits in the budget and five do not. This is the discipline
`StacksFrontier/AlgebraicGeometry/TwistMultCompat/Generic.lean` records for the same reason. -/

variable (A : SheafGradedAlgebra S) (m n : ℤ) (U : S.affineOpens)

/-- **The restriction of a tensor product to a chart, factored.** The comparison of
`Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso` is, on the nose, the
identification of restriction with inverse image, then the Tag 01CD comparison, then the tensor
product of the two identifications read backwards.

True by `rfl`: `restrictTensorIso` is *defined* as that composite, and the Tag 01CD factor in its
definition — `Stacks.AlgebraicGeometry.RestrictionSections.comparisonIsoApp`, over a morphism of
ringed spaces — is the same term as `Stacks.PullbackTensorIso.pullbackTensorIso`'s component over
the underlying morphism of schemes. So the ringed-space/scheme spelling crossing that the
implementation notes of `StacksFrontier/AlgebraicGeometry/PullbackTensorIso/Composite.lean` report as
unaffordable *at the level of morphisms* is, for this pair of spellings, free. -/
public theorem restrictTensorIso_hom_chart :
    (restrictTensorIso ((relativeProj A).chart U.1 U.2)
          (relativeTwist A m) (relativeTwist A n)).hom =
      (Scheme.Modules.restrictFunctorIsoPullback ((relativeProj A).chart U.1 U.2)).hom.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(((relativeProj A).scheme.toRingedSpace)).presheaf,
                (((relativeProj A).scheme.toRingedSpace)).IsSheaf⟩))).obj
            (relativeTwist A m, relativeTwist A n)) ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso
            ((relativeProj A).chart U.1 U.2).toLRSHom.toShHom).hom.app
              (relativeTwist A m, relativeTwist A n) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).presheaf,
                (((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).IsSheaf⟩)).map
            ((((Scheme.Modules.restrictFunctorIsoPullback
                ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A m)),
              ((Scheme.Modules.restrictFunctorIsoPullback
                ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A n))) :
              (_, _) ⟶ (_, _))) := rfl

/-- **The chart identification on the `n`-th relative twist, factored** into the identification of
restriction with inverse image and Tag 01NR's chart identification. True by `rfl`:
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso` is defined as that composite. -/
public theorem chartTwistIso_hom_factor :
    (chartTwistIso A n U).hom =
      (Scheme.Modules.restrictFunctorIsoPullback
          ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A n) ≫
        ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 n).hom := rfl

/-- **The tensor product of the chart identifications on the `m`-th and the `n`-th twist, split**
into the tensor product of the two restriction-to-inverse-image identifications followed by the
tensor product of Tag 01NR's two chart identifications. Both morphism arguments of
`Stacks.AlgebraicGeometry.TwistMultTransport.tensorSheafMap_comp` are written out rather than
inferred, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/TwistMultCompat/Generic.lean`. -/
public theorem tensorSheafMap_chartTwistIso :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).presheaf,
          (((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).IsSheaf⟩)).map
      (((chartTwistIso A m U).hom, (chartTwistIso A n U).hom) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).presheaf,
            (((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.restrictFunctorIsoPullback
            ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A m)),
          ((Scheme.Modules.restrictFunctorIsoPullback
            ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A n))) :
          (_, _) ⟶ (_, _))) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).presheaf,
              (((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).IsSheaf⟩)).map
          ((((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 m).hom,
            ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 n).hom) :
            (_, _) ⟶ (_, _))) :=
  tensorSheafMap_comp (AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace
    ((Scheme.Modules.restrictFunctorIsoPullback
      ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A m))
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 m).hom
    ((Scheme.Modules.restrictFunctorIsoPullback
      ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A n))
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 n).hom

/-- **Naturality of the restriction-to-inverse-image identification at the product of the relative
twists**, read backwards: the inverse image of the product followed by the identification on the
`(m + n)`-th twist is the identification at the tensor product sheaf followed by the restriction of
the product. -/
public theorem restrictFunctorIsoPullback_inv_naturality_mul :
    (Scheme.Modules.pullback ((relativeProj A).chart U.1 U.2)).map (relativeTwistMul A m n) ≫
        (Scheme.Modules.restrictFunctorIsoPullback
          ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A (m + n)) =
      (Scheme.Modules.restrictFunctorIsoPullback ((relativeProj A).chart U.1 U.2)).inv.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(((relativeProj A).scheme.toRingedSpace)).presheaf,
                (((relativeProj A).scheme.toRingedSpace)).IsSheaf⟩))).obj
            (relativeTwist A m, relativeTwist A n)) ≫
        (Scheme.Modules.restrictFunctor ((relativeProj A).chart U.1 U.2)).map
          (relativeTwistMul A m n) :=
  (Scheme.Modules.restrictFunctorIsoPullback
    ((relativeProj A).chart U.1 U.2)).inv.naturality (relativeTwistMul A m n)

/-- **The chart's multiplication square in restriction form, at the canonical twist datum.** This
is `Stacks.AlgebraicGeometry.TwistMapsInvertible.restrict_chart_mulSheaf_eq` — the only input below
with mathematical content, whose own content is the chart condition
`Stacks.AlgebraicGeometry.RelativeProjTwists.IsGradedChartIso` read on local sections — specialised
to `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, so that no twist datum is
carried as a hypothesis, and with the twist indices in this file's order. -/
public theorem restrict_chart_mul_eq_chart :
    (restrictTensorIso ((relativeProj A).chart U.1 U.2)
            (relativeTwist A m) (relativeTwist A n)).inv ≫
        (Scheme.Modules.restrictFunctor ((relativeProj A).chart U.1 U.2)).map
          (relativeTwistMul A m n) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).presheaf,
            (((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).IsSheaf⟩)).map
        ((((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 m).hom,
          ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 n).hom) :
          (_, _) ⟶ (_, _))) ≫
        twistMultiplicationMap (A.grading U.1) m n ≫
          ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso
            U.1 U.2 (m + n)).inv :=
  TwistMapsInvertible.restrict_chart_mulSheaf_eq
    (GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData
    (GluedTwistAlgebra.twistDataOfGradedAlgebra A).isGradedChartIso U.1 U.2 m n

/-- **The chart identification of the relative twists is multiplicative, in pullback form.** The
inverse image along the chart over an affine open `U` of the base of the product of the relative
twists, followed by Tag 01NR's chart identification on the `(m + n)`-th twist, is the Tag 01CD
comparison followed by the tensor product of the chart identifications followed by Tag 01MU's
multiplication map of the absolute twists on `Proj Γ(U, A)`.

This is `Stacks.AlgebraicGeometry.TwistMapsInvertible.restrict_chart_mulSheaf_eq` with the
restriction of a tensor product traded for the Tag 01CD comparison, which is the form the chart
transport of Tag 07ZG's graded-algebra clause needs: the clause is stated with
`Stacks.AlgebraicGeometry.Tag07ZGTwist.pullbackRelativeTwistMul`, whose leading factor is the
inverse Tag 01CD comparison. No mathematics is added — the trade is `conj_mul_of_restrict`, and the
two comparisons are the same term (`restrictTensorIso_hom_chart`). -/
public theorem pullback_chart_relativeTwistMul :
    (Scheme.Modules.pullback ((relativeProj A).chart U.1 U.2)).map (relativeTwistMul A m n) ≫
        (chartTwistIso A (m + n) U).hom =
      (Stacks.PullbackTensorIso.pullbackTensorIso
            ((relativeProj A).chart U.1 U.2).toLRSHom.toShHom).hom.app
          (relativeTwist A m, relativeTwist A n) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).presheaf,
              (((AlgebraicGeometry.Proj (A.grading U.1)).toRingedSpace)).IsSheaf⟩)).map
          (((chartTwistIso A m U).hom, (chartTwistIso A n U).hom) : (_, _) ⟶ (_, _))) ≫
          twistMultiplicationMap (A.grading U.1) m n :=
  conj_mul_of_restrict (restrictTensorIso_hom_chart A m n U)
    (Iso.inv_hom_id_app
      (Scheme.Modules.restrictFunctorIsoPullback ((relativeProj A).chart U.1 U.2))
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((relativeProj A).scheme.toRingedSpace)).presheaf,
            (((relativeProj A).scheme.toRingedSpace)).IsSheaf⟩))).obj
        (relativeTwist A m, relativeTwist A n)))
    (Iso.inv_hom_id
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 (m + n)))
    (chartTwistIso_hom_factor A (m + n) U)
    (tensorSheafMap_chartTwistIso A m n U)
    (restrictFunctorIsoPullback_inv_naturality_mul A m n U)
    (restrict_chart_mul_eq_chart A m n U)

/-! ### Tag 01MY's clause at the chart, in cancelled form -/

variable {A B : SheafGradedAlgebra S}

/-- **Tag 01MY's multiplicativity clause at the chart over an affine open of the base, with its
leading Tag 01CD comparison cancelled.** For the homomorphism `Γ(U, A) ⟶ Γ(U, B)` of graded
section rings that `ψ` induces, the inverse image along `r_{ψ_U}` of Tag 01MU's multiplication map
followed by Tag 01MY's comparison on the `(m + n)`-th twist is the tensor product of the
comparisons on the `m`-th and `n`-th twists, conjugated by the Tag 01CD comparisons of the two
legs, followed by the inverse image of the multiplication map downstairs.

This is `Stacks.AlgebraicGeometry.ProjMapCard.twistMap_comp_pullbackTwistMultiplication` with the
leading inverse comparison of
`Stacks.AlgebraicGeometry.ProjTwistTheta.pullbackTwistMultiplication` cancelled against its `hom`;
no new mathematics. It is the exact analogue, at Tag 07ZG's chart, of
`Stacks.AlgebraicGeometry.TwistMultTransport.bundle_mult_twistMap` at Tag 01NO's inclusion of
affine opens, and in this shape the identity is what a transport along the factors of
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso` and `chartTargetIso` consumes. -/
public theorem bundle_mult_twistMap_chart (ψ : SheafGradedAlgebraHom A B) (m n : ℤ)
    (U : S.affineOpens) :
    (Scheme.Modules.pullback
            (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).map
          (twistMultiplicationMap (A.grading U.1) m n) ≫
        twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) (m + n) =
      ((Stacks.PullbackTensorIso.pullbackTensorIso
              (mapHom (A.grading U.1) (B.grading U.1)
                (ψ.sectionHom U.1)).toLRSHom.toShHom).hom.app
            (twistingSheaf (A.grading U.1) m, twistingSheaf (A.grading U.1) n) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(((mapDomain (A.grading U.1) (B.grading U.1)
                (ψ.sectionHom U.1)).toScheme.toRingedSpace)).presheaf,
                (((mapDomain (A.grading U.1) (B.grading U.1)
                  (ψ.sectionHom U.1)).toScheme.toRingedSpace)).IsSheaf⟩)).map
            (((twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) m),
              (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n)) :
              (_, _) ⟶ (_, _))) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso
                (mapDomain (A.grading U.1) (B.grading U.1)
                  (ψ.sectionHom U.1)).ι.toLRSHom.toShHom).inv.app
              (twistingSheaf (B.grading U.1) m, twistingSheaf (B.grading U.1) n)) ≫
        (Scheme.Modules.pullback
            (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).map
          (twistMultiplicationMap (B.grading U.1) m n) :=
  transport_middle _ _ _ _ _ _ _
    (Iso.hom_inv_id_app
      (Stacks.PullbackTensorIso.pullbackTensorIso
        (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).toLRSHom.toShHom)
      (twistingSheaf (A.grading U.1) m, twistingSheaf (A.grading U.1) n))
    (ProjMapCard.twistMap_comp_pullbackTwistMultiplication
      (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) m n)

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
