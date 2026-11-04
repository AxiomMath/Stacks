module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.FiniteDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NagataFormalism

/-!
# The normalized dualizing complex along a finite morphism, for Nagata compactifications

In Situation [Stacks, Tag 0AU4], for the upper shriek functors of Nagata compactifications
(`Stacks.Duality.UpperShriek.nagata`), let `f : X ⟶ Y` be a finite morphism of schemes of finite
type over `S` and `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to `ω_S^•`. Then
`f_* ω_X^• = R𝓗om(f_* 𝒪_X, ω_Y^•)` in `D⁺_QCoh(f_* 𝒪_X)`, and through it the trace map `Tr_f` is
evaluation at `1` ([Stacks, Tag 0AX4]).

## Main results

* `Stacks.Duality.NormalizedOnOpens.exists_finitePushforwardIso_trace_nagata`:
  [Stacks, Tag 0AX4], both assertions.

## References

* [Stacks Project, Tag 0AX4](https://stacks.math.columbia.edu/tag/0AX4)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.DerivedAffinePushforward
open Stacks.AlgebraicGeometry.AffineQcohPushforward

universe u

namespace Stacks.Duality.NormalizedOnOpens

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **[Stacks, Tag 0AX4]** Let `S` be Noetherian with a dualizing complex `ω_S^•`, `f : X ⟶ Y` a
finite morphism of schemes of finite type over `S`, and `ω_X^•`, `ω_Y^•` the dualizing complexes
normalized relative to `ω_S^•`. Then `R𝓗om(f_* 𝒪_X, ω_Y^•)` lies in `D⁺_QCoh(f_* 𝒪_X)` and
`f_* ω_X^• ≅ R𝓗om(f_* 𝒪_X, ω_Y^•)` there, by an isomorphism through which the trace map
`Tr_f : Rf_* ω_X^• ⟶ ω_Y^•` of [Stacks, Tag 0B6X] is
`Rf_* ω_X^• = f_* ω_X^• = R𝓗om(f_* 𝒪_X, ω_Y^•) ⟶ ω_Y^•`, evaluation at `1` (the counit of
`res ⊣ R𝓗om(f_* 𝒪_X, -)`). -/
@[stacks 0AX4]
theorem exists_finitePushforwardIso_trace_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsFinite f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    DerivedCategoryB.derivedCategoryBPlus
        (SheafOfModules.isQuasicoherent (pushforwardRing f.base X.ringCatSheaf))
        (((structureSheafModelEquiv Y).inverse ⋙ derivedHomSheaf f ⋙
          (pushforwardRingModelEquiv f).functor).obj 𝒦Y.complex.obj.obj) ∧
      ∃ e : ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.obj
          𝒦X.complex.obj).obj ≅ ((structureSheafModelEquiv Y).inverse ⋙ derivedHomSheaf f ⋙
            (pushforwardRingModelEquiv f).functor).obj 𝒦Y.complex.obj.obj,
        (ObjectProperty.ι _).map (traceOfCompactifications nagataCompactification hpe hωS 𝒦X 𝒦Y) =
          (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app
              𝒦X.complex.obj.obj ≫
            (scalarRestriction f).mapDerivedCategory.map e.hom ≫
            (scalarRestrictionAdjunctionLS f).counit.app 𝒦Y.complex.obj.obj :=
  exists_finitePushforwardIso_trace nagataCompactification hpe hωS 𝒦X 𝒦Y

end Stacks.Duality.NormalizedOnOpens
