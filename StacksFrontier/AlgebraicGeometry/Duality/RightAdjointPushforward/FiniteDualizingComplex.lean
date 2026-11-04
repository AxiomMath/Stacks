module

public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.FiniteTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedProper
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Noetherian

/-!
# The normalized dualizing complex along a finite morphism

Let `S` be Noetherian with a dualizing complex `ω_S^•`, let `f : X ⟶ Y` be a finite morphism of
schemes of finite type over `S`, and let `ω_X^•`, `ω_Y^•` be the dualizing complexes normalized
relative to `ω_S^•`, for the upper shriek functors of a choice of compactifications. Then
`f₊ ω_X^• = R ℰom(f₊ 𝒪_X, ω_Y^•)` in `D⁺_QCoh(f₊ 𝒪_X)` (Stacks, Remark 0AX4): `a(ω_Y^•) ≅ ω_X^•`
by Tag 0AUD and `Φ ∘ a = R ℰom(f₊ 𝒪_X, -)` on `D⁺_QCoh(𝒪_Y)` by Tag 0AX2. Through it the trace
`Tr_f` is the counit of `res ⊣ R ℰom(f₊ 𝒪_X, -)`, evaluation at `1`: the counit of `Rf_* ⊣ a`
and that counit correspond under the uniqueness of right adjoints.

The statement depends on the choice of compactifications `c`, which is a parameter, so nothing
here is registered.

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.finitePushforwardIso`: `f₊ ω_X^• ≅ R ℰom(f₊ 𝒪_X, ω_Y^•)`.

## Main results

* `Stacks.Duality.NormalizedOnOpens.ι_map_traceOfCompactifications`: `Tr_f` is evaluation at `1`.
* `Stacks.Duality.NormalizedOnOpens.exists_finitePushforwardIso_trace`: Remark 0AX4, both
  assertions.
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

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- A finite morphism of schemes of finite type over a Noetherian base is pseudo-coherent
(Stacks, Tag 0684). -/
theorem pseudoCoherent_of_isFinite (hq : IsFiniteTypeOverNoetherian q) [IsFinite f] :
    PseudoCoherent f :=
  have := hq.source_noetherian
  (pseudoCoherent_iff_locallyOfFiniteType f).2 inferInstance

/-- **Stacks, Remark 0AX4, first assertion**, for the upper shriek functors of compactifications.
For a finite morphism `f : X ⟶ Y` of schemes of finite type over `S` and the dualizing complexes
`ω_X^•`, `ω_Y^•` normalized relative to `ω_S^•`, `f₊ ω_X^• ≅ R ℰom(f₊ 𝒪_X, ω_Y^•)` in
`D⁺_QCoh(f₊ 𝒪_X)`: here `f₊` is the equivalence `Φ` of Stacks, Tag 0AVW, and
`R ℰom(f₊ 𝒪_X, -)` is read at the locally small model. -/
def finitePushforwardIso (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    [IsFinite f] (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.obj 𝒦X.complex.obj).obj ≅
      ((structureSheafModelEquiv Y).inverse ⋙ derivedHomSheaf f ⋙
        (pushforwardRingModelEquiv f).functor).obj 𝒦Y.complex.obj.obj :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  haveI := pseudoCoherent_of_isFinite hq (f := f)
  (ObjectProperty.ι _).mapIso ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.mapIso
      (twistedInverseImageObjIso c hpe hωS 𝒦X 𝒦Y).symm) ≪≫
    (derivedPushforwardOverRingCompTwistedInverseImageIso f).app 𝒦Y.complex

/-- **Stacks, Remark 0AX4, second assertion**, for the upper shriek functors of compactifications:
the trace map `Tr_f : Rf_* ω_X^• ⟶ ω_Y^•` of the finite morphism `f` is
`Rf_* ω_X^• = f_* ω_X^• = R ℰom(f₊ 𝒪_X, ω_Y^•) ⟶ ω_Y^•`, where the first identification is
`Rf_* = res ∘ Φ` (Stacks, Tag 0AVW), the second is `finitePushforwardIso`, and the last map is the
counit of `res ⊣ R ℰom(f₊ 𝒪_X, -)` (Stacks, Tag 0BV0), "evaluation at `1`". -/
theorem ι_map_traceOfCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsFinite f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (ObjectProperty.ι _).map (traceOfCompactifications c hpe hωS 𝒦X 𝒦Y) =
      (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app 𝒦X.complex.obj.obj ≫
        (scalarRestriction f).mapDerivedCategory.map
          (finitePushforwardIso c hpe hωS 𝒦X 𝒦Y).hom ≫
        (scalarRestrictionAdjunctionLS f).counit.app 𝒦Y.complex.obj.obj := by
  have := hq.source_noetherian
  have := hp.source_noetherian
  have := pseudoCoherent_of_isFinite hq (f := f)
  have h := (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.naturality
    ((ObjectProperty.ι _).map (twistedInverseImageObjIso c hpe hωS 𝒦X 𝒦Y).inv)
  rw [traceOfCompactifications, relativeDualizingComplexTrace, Functor.map_comp,
    ι_map_twistedInverseImageAdjunction_counit_app_eq f 𝒦Y.complex]
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker h _).trans ((Category.assoc _ _ _).trans
    (congrArg ((derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app
        𝒦X.complex.obj.obj ≫ ·) ((Category.assoc _ _ _).symm.trans
      (eq_whisker ((scalarRestriction f).mapDerivedCategory.map_comp _ _).symm _)))))

/-- **Stacks, Remark 0AX4**, for the upper shriek functors of compactifications. Let `f : X ⟶ Y`
be a finite morphism of schemes of finite type over a Noetherian `S` with a dualizing complex
`ω_S^•`, and `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to `ω_S^•`. Then
`R ℰom(f₊ 𝒪_X, ω_Y^•)` lies in `D⁺_QCoh(f₊ 𝒪_X)` and `f₊ ω_X^• ≅ R ℰom(f₊ 𝒪_X, ω_Y^•)`, by an
isomorphism through which the trace `Tr_f : Rf_* ω_X^• ⟶ ω_Y^•` is
`Rf_* ω_X^• = f_* ω_X^• = R ℰom(f₊ 𝒪_X, ω_Y^•) ⟶ ω_Y^•`, the last map being the counit of
`res ⊣ R ℰom(f₊ 𝒪_X, -)`, evaluation at `1`
(`AlgebraicGeometry.scalarRestrictionAdjunctionLS_counit_app`,
`AlgebraicGeometry.derivedRestrictScalarsHomAdjunction_counit_fac`). -/
theorem exists_finitePushforwardIso_trace
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsFinite f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    DerivedCategoryB.derivedCategoryBPlus
        (SheafOfModules.isQuasicoherent (pushforwardRing f.base X.ringCatSheaf))
        (((structureSheafModelEquiv Y).inverse ⋙ derivedHomSheaf f ⋙
          (pushforwardRingModelEquiv f).functor).obj 𝒦Y.complex.obj.obj) ∧
      ∃ e : ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.obj
          𝒦X.complex.obj).obj ≅ ((structureSheafModelEquiv Y).inverse ⋙ derivedHomSheaf f ⋙
            (pushforwardRingModelEquiv f).functor).obj 𝒦Y.complex.obj.obj,
        (ObjectProperty.ι _).map (traceOfCompactifications c hpe hωS 𝒦X 𝒦Y) =
          (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app
              𝒦X.complex.obj.obj ≫
            (scalarRestriction f).mapDerivedCategory.map e.hom ≫
            (scalarRestrictionAdjunctionLS f).counit.app 𝒦Y.complex.obj.obj :=
  have := hq.source_noetherian
  have := hp.source_noetherian
  have := pseudoCoherent_of_isFinite hq (f := f)
  ⟨derivedCategoryBPlus_derivedHomSheafLS_obj f 𝒦Y.complex,
    finitePushforwardIso c hpe hωS 𝒦X 𝒦Y, ι_map_traceOfCompactifications c hpe hωS 𝒦X 𝒦Y⟩

end Stacks.Duality.NormalizedOnOpens
