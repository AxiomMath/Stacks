module

public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceDevissage
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekProper

/-!
# Duality for a proper morphism on all of `D_QCoh`

In Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a proper morphism of schemes of finite type
over `S` and `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to `ω_S^•`. The second
isomorphism of [Stacks, Tag 0B6X] is

`Rf_*R𝓗om(L, ω_X^•) ≅ R𝓗om(Rf_*L, ω_Y^•)`, `L ∈ D_QCoh(𝒪_X)`,

the sheafy trace map of [Stacks, Tag 0B6H] at `K = ω_Y^•` composed with `a(ω_Y^•) ≅ ω_X^•`
([Stacks, Tag 0AUD]); the trace map is an isomorphism on all of `D_QCoh(𝒪_X)` by
`Stacks.Duality.isIso_sheafyTrace_of_isProper_of_isBoundedBelow`.

## Main definitions

* `Stacks.Duality.sheafyTraceIsoStdOfQCoh` — `Rf_*R𝓗om(L, a(M)) ≅ R𝓗om(Rf_*L, M)` for
  `L ∈ D_QCoh(𝒪_X)` and `M ∈ D^+_QCoh(𝒪_Y)`, at the standard model.
* `Stacks.Duality.NormalizedOnOpens.sheafHomDualizingIsoOfQCoh` — [Stacks, Tag 0B6X], the second
  isomorphism, for every `L ∈ D_QCoh(𝒪_X)`.

## References

* [Stacks Project, Tag 0B6X](https://stacks.math.columbia.edu/tag/0B6X)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std sheafHom pull push comparison plusCoh qcoh
  rightAdjointStd plusCoh_le_qcoh qcoh_iff_isDQCoh)
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

section Trace

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] [IsProper f]

/-- **The sheafy trace of a proper morphism on all of `D_QCoh`, at the standard model.** For a
proper morphism `f : X ⟶ Y` of Noetherian schemes, `L ∈ D_QCoh(𝒪_X)` and `M ∈ D_QCoh(𝒪_Y)`
bounded below, the sheafy trace of [Stacks, Tag 0B6H] is an isomorphism
`Rf_*R𝓗om(L, a(M)) ≅ R𝓗om(Rf_*L, M)`. -/
def sheafyTraceIsoStdOfQCoh (L : Std X) (hL : qcoh X L) (M : (qcoh Y).FullSubcategory)
    (hM : DerivedCategoryB.IsBoundedBelow M.obj) :
    (push f).obj (((sheafHom X).obj (op L)).obj ((rightAdjointStd f).obj M)) ≅
      ((sheafHom Y).obj (op ((push f).obj L))).obj M.obj :=
  @asIso _ _ _ _ (sheafyTrace f
    (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
    (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (StandardModel.isQuasicoherent_homology_derivedPushforward f)
    (rightAdjointQCohStdAdjunction f)
    ⟨L, (qcoh_iff_isDQCoh L).1 hL⟩
    ⟨M.obj, (qcoh_iff_isDQCoh M.obj).1 M.property⟩)
    (isIso_sheafyTrace_of_isProper_of_isBoundedBelow f (rightAdjointQCohStdAdjunction f) _ _ hM)

end Trace

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **[Stacks, Tag 0B6X], the second isomorphism.** For a proper morphism `f : X ⟶ Y` of schemes
of finite type over `S`, the dualizing complexes `ω_X^•`, `ω_Y^•` normalized relative to `ω_S^•`
and every `L ∈ D_QCoh(𝒪_X)`, `Rf_*R𝓗om(L, ω_X^•) ≅ R𝓗om(Rf_*L, ω_Y^•)`: the sheafy trace map at
`ω_Y^•`, composed with `a(ω_Y^•) ≅ ω_X^•` ([Stacks, Tag 0AUD]). -/
def sheafHomDualizingIsoOfQCoh
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    (L : Std X) (hL : qcoh X L) :
    (push f).obj (((sheafHom X).obj (op L)).obj (stdComplex c 𝒦X)) ≅
      ((sheafHom Y).obj (op ((push f).obj L))).obj (stdComplex c 𝒦Y) :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  (push f).mapIso (((sheafHom X).obj (op L)).mapIso
      (rightAdjointStdDualizingIso c hpe hωS 𝒦X 𝒦Y).symm) ≪≫
    sheafyTraceIsoStdOfQCoh f L hL _
      (isBoundedBelow_of_isDualizing_std (isDualizing_stdComplex c hωS 𝒦Y))

end NormalizedOnOpens

end Stacks.Duality
