module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforward
import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional

/-!
# The direct image of quotients along an affine morphism

For an affine morphism `π : X ⟶ Y` over `B` and a quasi-coherent module `F` on `X`, the direct
image `G = π_*F` is quasi-coherent, and sending a quotient `F_T ⟶ Q` to `G_T ⟶ π_{T,*}Q` defines
a morphism of Quot functors `Quot_{F/X/B} ⟶ Quot_{G/Y/B}`.

## Main definitions

* `QuotPushforwardSituation.targetSituation'`: The quotient situation `G/Y/B`.
* `QuotPushforwardSituation.pushforwardQuotient'`: The direct image of a quotient, recorded by
  its kernel.
* `QuotPushforwardSituation.quotFunctorMap'`: The morphism of Quot functors induced by the
  direct image.

## Main results

* `QuotPushforwardSituation.isQuasicoherentOnSite_pushforwardModule'`: The direct image `π_*F`
  is quasi-coherent.
* `QuotPushforwardSituation.pushforwardQuotient_mem'`: The direct image of a quotient in
  `Quot_{F/X/B}(T)` lies in `Quot_{G/Y/B}(T)`.
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotPushforwardSituation

variable (D : QuotPushforwardSituation B S hS)

/-- **Stacks 07U8 for the morphism of the situation**: the direct image `G = π_*F` along the
affine morphism `π` is quasi-coherent.

This is the form of Stacks 07U8 with no hypothesis,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional`. -/
theorem isQuasicoherentOnSite_pushforwardModule' :
    D.pushforwardModule.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS D.π D.affine
    D.F D.quasicoherent

/-- The quotient situation `G/Y/B` of Stacks 09TR for the direct image `G = π_*F`, whose Quot
functor is the target of the morphism of Stacks 0DP1. -/
def targetSituation' : QuotSituation B S hS where
  X := D.Y
  Y := D.base
  f := D.structureY
  F := D.pushforwardModule
  quasicoherent := D.isQuasicoherentOnSite_pushforwardModule'
  finitePresentation := D.finitePresentationY

/-- **Stacks 0DP1, the direct image of a quotient.**  The quotient `G_T ⟶ π_{T,*}(F_T/K)` of
`G_T` obtained from a quotient `F_T ⟶ F_T/K` by applying `π_{T,*}` and reading the result through
the comparison `G_T ≅ π_{T,*}F_T`, recorded — as the quotients themselves are — by its kernel. -/
@[stacks 0DP1 "the direct image of a quotient, recorded by its kernel"]
def pushforwardQuotient' (c : PushforwardComparison D) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    Subobject (D.targetSituation'.baseChangeModule T) :=
  Functor.conjSubobject (c.iso T) K

/-- **The quotient of `G_T` by the direct image of a quotient is the direct image of that
quotient**: the quotient of `G_T` by `pushforwardQuotient c T K` is `π_{T,*}(F_T/K)`. -/
def pushforwardQuotientCokernelIso' (c : PushforwardComparison D) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    D.targetSituation'.quotientModule T (D.pushforwardQuotient' c T K) ≅
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj
        (D.sourceSituation.quotientModule T K) :=
  letI := c.preservesEpimorphisms T
  Functor.conjSubobjectCokernelIso (c.iso T) K

/-- **The inputs the morphism of Stacks 0DP1 is built from**, bundled: the base-change assertion
of Stacks 07U8 with the exactness of the direct image along an affine morphism, the morphism of
stacks `Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9, and the compatibility of the direct image with
base change of the test scheme, which is part (b) of the proof of Stacks 0DN9. -/
structure AffinePushforwardQuotInputs' (D : QuotPushforwardSituation B S hS) where
  /-- The comparison of the direct image with its base change, and its exactness. -/
  comparison : PushforwardComparison D
  /-- **Stacks 0DN9 for the situation**: the direct image along `π_T` of a module satisfying the
  four conditions of Stacks 09TR over `T` again satisfies them.  This is the content of the
  morphism of stacks `Coh_{X/B} ⟶ Coh_{Y/B}` on objects. -/
  pushforwardMem : ∀ (T : SchemesOver D.base)
      (Q : Modules.{u, u} B S hS (D.sourceSituation.space T).1 (D.sourceSituation.space T).2),
    D.sourceSituation.IsQuotModule T Q →
      D.targetSituation'.IsQuotModule T
        ((modulePushforward B S hS (D.baseChangeOfMap T)).obj Q)
  /-- **Part (b) of the proof of Stacks 0DN9 for the situation**: forming the direct image
  commutes with pullback along a morphism of test schemes, read on the kernels of the
  quotients. -/
  pushforwardQuotient_quotientPullback : ∀ {T' T : SchemesOver D.base} (m : T' ⟶ T)
      (K : Subobject (D.sourceSituation.baseChangeModule T)),
    D.pushforwardQuotient' comparison T' (D.sourceSituation.quotientPullback m K) =
      D.targetSituation'.quotientPullback m (D.pushforwardQuotient' comparison T K)

/-- **Stacks 0DP1.**  The direct image of a quotient in `Quot_{F/X/B}(T)` lies in
`Quot_{G/Y/B}(T)`: the quotient of `G_T` by it is `π_{T,*}(F_T/K)`, which is quasi-coherent, of
finite presentation, flat over `T` and has support proper over `T` because `F_T/K` is, this being
the morphism of stacks `Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9. -/
@[stacks 0DP1 "the direct image of a quotient of the Quot functor is one"]
theorem pushforwardQuotient_mem' (I : AffinePushforwardQuotInputs' D) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    D.pushforwardQuotient' I.comparison T K ∈
      D.targetSituation'.properlySupportedQuotients T :=
  (D.targetSituation'.mem_properlySupportedQuotients_iff T
      (D.pushforwardQuotient' I.comparison T K)).mpr
    (QuotSituation.IsQuotModule.of_iso
      (D.pushforwardQuotientCokernelIso' I.comparison T K).symm
      (I.pushforwardMem T (D.sourceSituation.quotientModule T K)
        ((D.sourceSituation.mem_properlySupportedQuotients_iff T K).mp hK)))

/-- **Stacks 0DP1.**  The morphism of Quot functors `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` induced by
the direct image: over a test scheme it sends a quotient `F_T ⟶ Q` to `G_T ⟶ π_{T,*}Q`.

Naturality is the compatibility of the direct image with pullback along a morphism of test
schemes, part (b) of the proof of Stacks 0DN9. -/
@[stacks 0DP1 "the induced morphism of Quot functors"]
def quotFunctorMap' (I : AffinePushforwardQuotInputs' D) :
    D.sourceSituation.quotFunctor ⟶ D.targetSituation'.quotFunctor where
  app T := ↾fun K ↦
    ⟨D.pushforwardQuotient' I.comparison T.unop K.1,
      D.pushforwardQuotient_mem' I T.unop K.1 K.2⟩
  naturality _ _ m := ConcreteCategory.hom_ext _ _ fun K ↦
    Subtype.ext (I.pushforwardQuotient_quotientPullback m.unop K.1)

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
