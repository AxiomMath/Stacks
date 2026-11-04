module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDualTriangleFirstMapSections
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.UnitSourceTrivialisationSections

/-!
# Tag 0B4B: the identity of sections, and the isomorphism assertion

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces.
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDualTriangleFirstMapSections.lean`
reduces the isomorphism assertion of [Stacks, Tag 0B4B] for an effective Cartier divisor to the
single identity of sections
`…ClosedQuotientMorphismOfRingedSpaces.SheafHomPushforwardSectionsCore`.

**This file proves that identity**, hence [Stacks, Tag 0B4B]: the canonical comparison morphism
`𝒩_{D/X}[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` in `D(𝒪_D)` of an effective Cartier divisor is an
isomorphism.

## The argument

The underived core
`…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_comp_unitIso_comp_counit` is
the identity of natural transformations `ℰom_{𝒪_X}(i_* 𝒪_Z, -) ⟶ 𝟭`

`0E2I at 𝒪_Z ≫ i_*(trivialisation of ℰom_{𝒪_Z}(𝒪_Z, -)) ≫ (trace of 0A75)`
`= (restriction along u) ≫ (trivialisation of ℰom_{𝒪_X}(𝒪_X, -))`.

Reading it at a sheaf of `𝒪_X`-modules `F`, on sections over an open `U ⊆ X`, at the section
attached to `z` by `…PushforwardInternalHom.sliceEquiv`, turns each factor into something the
tree computes:

* the underived [Stacks, Tag 0E2I] isomorphism on sections *is*
  `…PushforwardInternalHom.sliceEquiv`, by construction, so the first factor returns `z`;
* the two trivialisations of `ℰom(𝒪, -)` on sections are evaluation at the unit section, by
  `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso_hom_val_app` — the only
  input that was missing, and the reason this file exists;
* restriction along the unit `u : 𝒪_X ⟶ i_* 𝒪_Z` on sections is precomposition with `u|_U`, by
  `Stacks.SheafOfModules.InternalHom.internalHomPrecomp_val_app`, and a pushforward is read on
  sections over the preimage, both by definition.

## Main results

* `…ClosedQuotientMorphismOfRingedSpaces.trivialisation_val_app_X` and `…_Z`: the trivialisation
  of `ℰom(𝒪, -)` on sections, at the ringed sites of `X` and of `Z` — the generic
  `…internalHomSecondFunctorUnitIso_hom_val_app` in the spellings the underived core is stated
  in.
* `…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardSectionsCore`: **the identity of
  sections holds.**
* `Stacks.Divisors.dualTriangleFirstMapCochainCore`: the cochain-level core of
  [Stacks, Tag 0B4B] holds, unconditionally.
* `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport`: **[Stacks, Tag 0B4B]**
  — the canonical comparison morphism `𝒩_{D/X}[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` of an effective Cartier
  divisor is an isomorphism.

## Implementation notes

The two trivialisation wrappers are proved through the ringed-space identification
`Stacks.SheafOfModules.internalHomSecondFunctorUnitIso_hom_app_eq_internalHomSheafUnitIso`
followed by `Stacks.SheafOfModules.internalHomSheafUnitIso_hom_val_app`, and *not* by
instantiating the generic sections formula at `S.siteX` directly: the generic statement is
written over `Stacks.SheafOfModules.Tensor.ringSheaf S.X.sheaf` and the core over
`structureSheafRing S.X`, and crossing those two inside a statement that
already mentions sections of an internal Hom sheaf exhausts the recursion depth.
Going through the identification crosses them in a statement about a morphism only, which is
cheap, and the sections formula on the far side is already stated at the space.

`structureSheafRing` is `@[instance_reducible]` everywhere, which the surrounding files need;
no further transparency change is made here.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

open Stacks.SheafOfModules Stacks.SheafOfModules.InternalHom

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The trivialisation of `ℰom(𝒪_Y, -)` on sections is evaluation at the unit section, for any
ringed space `Y`. -/
private theorem trivialisation_val_app_aux (Y : RingedSpace.{u})
    (A : SheafOfModules.{u} (structureSheafRing Y)) (U : Opens Y)
    (s : ((internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
      (SheafOfModules.unit (Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
        Y.sheaf))).obj A).val.obj (op U)) :
    ((internalHomSecondFunctorUnitIso Y.sheaf).hom.app A).val.app (op U) s =
      (s.app (op (Over.mk (𝟙 U)))) (RingedSite.structureSheafOne (ringedSite Y.sheaf) U) :=
  (congrArg (fun t : _ ⟶ A => (t.val.app (op U)) s)
    (internalHomSecondFunctorUnitIso_hom_app_eq_internalHomSheafUnitIso Y.sheaf A)).trans
    (internalHomSheafUnitIso_hom_val_app Y.sheaf A U s)

/-- **The trivialisation of `ℰom_{𝒪_X}(𝒪_X, -)` on sections is evaluation at the unit
section**, at the ringed site of the ambient space `X` of a closed quotient morphism.

This is the ringed-space identification
`Stacks.SheafOfModules.internalHomSecondFunctorUnitIso_hom_app_eq_internalHomSheafUnitIso`
followed by `Stacks.SheafOfModules.internalHomSheafUnitIso_hom_val_app`. -/
theorem trivialisation_val_app_X (A : SheafOfModules.{u} (structureSheafRing S.X)) (U : Opens S.X)
    (s : ((internalHomSecondFunctor.{u, u, u, u} S.siteX S.X.sheaf
      S.structureSheafModuleX).obj A).val.obj (op U)) :
    ((internalHomSecondFunctorUnitIso S.X.sheaf).hom.app A).val.app (op U) s =
      (s.app (op (Over.mk (𝟙 U)))) (RingedSite.structureSheafOne (ringedSite S.X.sheaf) U) :=
  trivialisation_val_app_aux S.X A U s

/-- **The trivialisation of `ℰom_{𝒪_Z}(𝒪_Z, -)` on sections is evaluation at the unit
section** — `trivialisation_val_app_X` at the ringed site of the source `Z`. -/
theorem trivialisation_val_app_Z (A : SheafOfModules.{u} (structureSheafRing S.Z)) (U : Opens S.Z)
    (s : ((internalHomSecondFunctor.{u, u, u, u} S.siteZ S.Z.sheaf
      S.structureSheafModuleZ).obj A).val.obj (op U)) :
    ((internalHomSecondFunctorUnitIso S.Z.sheaf).hom.app A).val.app (op U) s =
      (s.app (op (Over.mk (𝟙 U)))) (RingedSite.structureSheafOne (ringedSite S.Z.sheaf) U) :=
  trivialisation_val_app_aux S.Z A U s

/-- **The underived core of [Stacks, Tag 0E2I] at the source `𝒪_Z`, read on sections, holds.**
For a sheaf of `𝒪_X`-modules `F`, an open `U ⊆ X` and a morphism
`z : 𝒪_Z|_{i^{-1}U} ⟶ ℰom(𝒪_Z, F)|_{i^{-1}U}`, the morphism `(i_* 𝒪_Z)|_U ⟶ F|_U` that the
underived identification of [Stacks, Tag 0E2I] attaches to `z` takes the unit section of
`i_* 𝒪_Z` to the value at the unit section of the trace of [Stacks, Tag 0A75] on `z` evaluated
at the unit section of `𝒪_Z`.

This is the underived core
`…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_comp_unitIso_comp_counit` read
at `F` on sections over `U`, with both trivialisations of `ℰom(𝒪, -)` computed by
`trivialisation_val_app_X` and `trivialisation_val_app_Z`; every other factor is read on
sections by definition. -/
theorem sheafHomPushforwardSectionsCore : S.SheafHomPushforwardSectionsCore := by
  intro F U z
  let e := S.pushforwardInternalHom.sliceEquiv
    ((RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)).X 0) F U
  have hcore := NatTrans.congr_app S.sheafHomPushforwardNatIso_comp_unitIso_comp_counit F
  have hcw := congrArg (fun (t : _ ⟶ F) => (ConcreteCategory.hom (t.val.app (op U)))
    (e.symm z).val) hcore
  have hz : ((((S.sheafHomPushforwardNatIso S.structureSheafModuleZ).hom.app F).val.app (op U)))
      (e.symm z).val = z.val := congrArg SheafOfModules.Hom.val (e.apply_symm_apply z)
  refine Eq.trans ?_ (Eq.trans hcw.symm ?_)
  · exact (trivialisation_val_app_X S F U
      (((internalHomPrecompNatTrans S.siteX S.X.sheaf (structureSheafModuleHom S.i)).app F).val.app
        (op U) (e.symm z).val)).symm
  · refine Eq.trans (congrArg (fun y =>
      ((S.modulePushforwardSheafHomExactSupportAdjunction.counit.app F).val.app (op U))
        (((internalHomSecondFunctorUnitIso S.Z.sheaf).hom.app
          (S.sheafHomExactSupport.obj F)).val.app (op (S.openPreimage U)) y)) hz) ?_
    exact congrArg
      (fun y => ((S.modulePushforwardSheafHomExactSupportAdjunction.counit.app F).val.app (op U)) y)
      (trivialisation_val_app_Z S (S.sheafHomExactSupport.obj F) (S.openPreimage U) z.val)

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

namespace Stacks.Divisors

open RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

omit [IsEffectiveCartierDivisor D] in
/-- **The cochain-level core of [Stacks, Tag 0B4B] holds.** This is
`Stacks.Divisors.dualTriangleFirstMapCochainCore_of_sectionsCore` with its hypothesis supplied
by `…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardSectionsCore`. -/
theorem dualTriangleFirstMapCochainCore : DualTriangleFirstMapCochainCore D :=
  dualTriangleFirstMapCochainCore_of_sectionsCore D
    (ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardSectionsCore (closedQuotient D))

/-- **[Stacks, Tag 0B4B].** For an effective Cartier divisor `D ⊆ X` the canonical comparison
morphism

`𝒩_{D/X}[-1] ⟶ R ℰom_{𝒪_X}(𝒪_D, 𝒪_X)`

in `D(𝒪_D)` is an isomorphism.

This is `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_sectionsCore`
with its hypothesis supplied by
`…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardSectionsCore`. -/
@[stacks 0B4B]
theorem isIso_normalSheafShiftToDerivedSheafHomExactSupport :
    IsIso (normalSheafShiftToDerivedSheafHomExactSupport D) :=
  isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_sectionsCore D
    (ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardSectionsCore (closedQuotient D))

end Stacks.Divisors

end
