/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.TwistingReading
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedCohomologyAlongRingMap
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.QuasicoherentIdeal

/-!
# Hilbert polynomials with respect to the pullback of `𝒪(1)`, read on projective spaces

Let `F/X/B` be a Quot situation over `Spec ℤ` with a projective frame `X = B × ℙⁿ_ℤ`, and let
`𝓛` be the pullback of `𝒪_{ℙⁿ}(1)` to `X`.  For an object `(T, 𝒬)` of `Coh_{X/B}`, a point
`t ∈ T` and `m ∈ ℤ`, the twisted Euler characteristic of Stacks 0DNF,
`χ(X_t, 𝒬_t ⊗ 𝓛_t^{⊗ m})`, computed on the small étale site of the algebraic space `X_t`, is the
value at `m` of the Hilbert polynomial (Stacks 08AD) of the fibre over `t` of the reading of `𝒬`
on `ℙⁿ_T`.  So `Quot^P_{F/X/B}` with respect to `𝓛`
(`AlgebraicGeometry.Space.QuotSituation.hilbertPolynomialQuot`) is the subfunctor of quotients
with fibrewise Hilbert polynomial `P` on projective spaces
(`AlgebraicGeometry.ProjectiveQuotOverSpace.hilbertSubfunctor`).

The comparison runs along `X_t ≅ h_{ℙⁿ_{κ(t)}}`: the Euler characteristic is invariant under that
isomorphism; the module `𝒬_t ⊗ 𝓛_t^{⊗ m}` becomes the associated module of
`G ⊗ 𝒪(1)^{⊗ m}` with `G` the fibre of the reading of `𝒬` (Stacks 03DX, 03EL, 01CU and the reading
of `𝓛`); its étale cohomology is the Zariski cohomology of `G ⊗ 𝒪(1)^{⊗ m}` (Stacks 03DW); and
`𝒪(1)^{⊗ m} ≅ 𝒪(m)`.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 08AD](https://stacks.math.columbia.edu/tag/08AD)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-! ### Quasi-coherence of a twisting step -/

/-- A twisting step `M ⊗ N^{⊗ m}` of a quasi-coherent module by an invertible module is
quasi-coherent. -/
theorem isQuasicoherentOnSite_twistStep (Z : AlgebraicSpaces B integerBase B.contains_integerBase)
    (N : Space.Modules.{u, u} B integerBase B.contains_integerBase Z.1 Z.2)
    [hN : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase
      B.contains_integerBase Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase
        B.contains_integerBase Z.1 Z.2).O).property N]
    (m : ℤ) (M : Space.Modules.{u, u} B integerBase B.contains_integerBase Z.1 Z.2)
    (hM : M.IsQuasicoherentOnSite) :
    (Space.twistStep B integerBase B.contains_integerBase Z.1 Z.2 N m M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_sheafTensor
    (X := Space.smallEtaleRingedSite B integerBase B.contains_integerBase Z.1 Z.2) M _ hM
    (Space.isQuasicoherentOnSite_of_isInvertible B integerBase B.contains_integerBase Z _
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
        (Space.isInvertible_invertibleTensorPower B integerBase B.contains_integerBase Z.1 Z.2
          N m)))

/-! ### The twisted module on a fibre, read on `ℙⁿ_{κ(t)}` -/

section Fibre

variable {D : Space.QuotSituation B integerBase B.contains_integerBase} (E : ProjectiveFrame B n D)
  (A : Space.CoherentObject D.toCoherentSituation) (t : A.testScheme)

/-- `ℙⁿ_{κ(t)}`, as an object of the site, for a point `t` of the test scheme of `A`. -/
abbrev fibreSite : BigFppfOver B integerBase B.contains_integerBase :=
  projectiveSite B n (A.pointScheme t)

/-- The associated module of Stacks 03DX on the algebraic space of `ℙⁿ_{κ(t)}`. -/
abbrev fibreAssociated :
    ((𝒯).obj (fibreSite (n := n) A t)).Modules ⥤
      SheafOfModules.{u} (Space.representedStructureRingSheaf B integerBase B.contains_integerBase
        (fibreSite (n := n) A t)) :=
  _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((𝒯).obj (fibreSite (n := n) A t)) (fibreSite (n := n) A t).left.property ⋙
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (fibreSite (n := n) A t)).functor

/-- The fibre `𝒬_t` of the module of `A` is quasi-coherent. -/
theorem isQuasicoherentOnSite_fibreModule : (A.fibreModule t).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
    B.contains_integerBase _ _ A.quasicoherent

/-- `𝓛_t`, the pullback of `𝓛` to the fibre `X_t`. -/
abbrev fibreTwisting : Space.Modules.{u, u} B integerBase B.contains_integerBase
    (A.fibreSpace t).1 (A.fibreSpace t).2 :=
  (Space.modulePullback B integerBase B.contains_integerBase
    (D.sourceProjection (A.pointTest t))).obj (twistingModule E)

/-- `𝓛_t` is an invertible module on the fibre `X_t`. -/
instance isInvertible_fibreTwisting :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase
      B.contains_integerBase (D.space (A.pointTest t)).1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase
        B.contains_integerBase (D.space (A.pointTest t)).1 (D.space (A.pointTest t)).2).O).property
      (fibreTwisting E A t) :=
  Space.stacksIsInvertible_modulePullback_obj B integerBase B.contains_integerBase _ _

/-- `𝓛_t` is invertible, in the spelling of `AlgebraicGeometry.Space.CoherentObject.fibreSpace`. -/
instance isInvertible_fibreTwisting' :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase
      B.contains_integerBase (A.fibreSpace t).1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase
        B.contains_integerBase (A.fibreSpace t).1 (A.fibreSpace t).2).O).property
      (fibreTwisting E A t) :=
  isInvertible_fibreTwisting E A t

/-- `𝓛` is invertible, in the spelling of the coherent situation underlying `D`. -/
instance isInvertible_twistingModule' :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase
      B.contains_integerBase D.toCoherentSituation.X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase
        B.contains_integerBase D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O).property
      (twistingModule E) :=
  isInvertible_twistingModule E

/-- `𝒪(1)` on `ℙⁿ_{κ(t)}` is invertible. -/
instance isInvertible_fibreTwistingSheaf :
    SheafOfModules.IsInvertible ((𝒯).obj (fibreSite (n := n) A t)).presheaf
      ((𝒯).obj (fibreSite (n := n) A t)).ringCatSheaf.2
      (twistingSheaf n ((𝒯).obj (A.pointScheme t)) 1) :=
  Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n _ 1

/-- `𝒪(1)` on `ℙⁿ_{κ(t)}` is invertible, in the spelling of Stacks 01CU. -/
instance stacksIsInvertible_fibreTwistingSheaf :
    Stacks.SheafOfModules.IsInvertible ((𝒯).obj (fibreSite (n := n) A t)).presheaf
      ((𝒯).obj (fibreSite (n := n) A t)).ringCatSheaf.2
      (twistingSheaf n ((𝒯).obj (A.pointScheme t)) 1) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (isInvertible_fibreTwistingSheaf A t)

/-- `𝓛_t` read on the algebraic space of `ℙⁿ_{κ(t)}`. -/
abbrev fibreTwistingRead : Space.Modules.{u, u} B integerBase B.contains_integerBase
    (schemeSpace (fibreSite (n := n) A t)).1 (schemeSpace (fibreSite (n := n) A t)).2 :=
  (Space.modulePullback B integerBase B.contains_integerBase
    (spaceIso E (A.pointTest t)).hom).obj (fibreTwisting E A t)

/-- `𝓛_t` read on the algebraic space of `ℙⁿ_{κ(t)}` is an invertible module. -/
instance isInvertible_fibreTwistingRead :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase
      B.contains_integerBase (schemeSpace (fibreSite (n := n) A t)).1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase
        B.contains_integerBase (schemeSpace (fibreSite (n := n) A t)).1
          (schemeSpace (fibreSite (n := n) A t)).2).O).property
      (fibreTwistingRead E A t) :=
  Space.stacksIsInvertible_modulePullback_obj B integerBase B.contains_integerBase _ _
    (hM := isInvertible_fibreTwisting E A t)

/-- `𝓛_t` read on `h_{ℙⁿ_{κ(t)}}` is invertible, in the spelling of the represented space. -/
instance isInvertible_fibreTwistingRead' :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase
      B.contains_integerBase (yoneda.obj (fibreSite (n := n) A t)))
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase
        B.contains_integerBase (yoneda.obj (fibreSite (n := n) A t))
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase
            (fibreSite (n := n) A t))).O).property
      (fibreTwistingRead E A t) :=
  isInvertible_fibreTwistingRead E A t

/-- `𝒬_t` on the algebraic space of `ℙⁿ_{κ(t)}` is the associated module of its reading. -/
def fibreModuleReadIso :
    (Space.modulePullback B integerBase B.contains_integerBase
        (spaceIso E (A.pointTest t)).hom).obj (A.fibreModule t) ≅
      (fibreAssociated A t).obj ((reading E (A.pointTest t)).obj (A.fibreModule t)) :=
  haveI := isIso_zariskiAdjunction_counit_app (fibreSite (n := n) A t)
    ((Space.modulePullback B integerBase B.contains_integerBase
        (spaceIso E (A.pointTest t)).hom).obj (A.fibreModule t))
    (isQuasicoherentOnSite_modulePullback_spaceIso E _ _ (isQuasicoherentOnSite_fibreModule A t))
  (asIso ((zariskiAdjunction B (fibreSite (n := n) A t)).counit.app
    ((Space.modulePullback B integerBase B.contains_integerBase
        (spaceIso E (A.pointTest t)).hom).obj (A.fibreModule t)))).symm

/-- `𝓛_t` on the algebraic space of `ℙⁿ_{κ(t)}` is the associated module of `𝒪(1)`. -/
def fibreTwistingReadIso :
    (fibreAssociated A t).obj (twistingSheaf n ((𝒯).obj (A.pointScheme t)) 1) ≅
      fibreTwistingRead E A t :=
  (fibreAssociated A t).mapIso (readingTwistingModuleIso E (A.pointTest t)).symm ≪≫
    @asIso _ _ _ _ ((zariskiAdjunction B (fibreSite (n := n) A t)).counit.app
      (fibreTwistingRead E A t))
      (isIso_zariskiAdjunction_counit_app (fibreSite (n := n) A t) (fibreTwistingRead E A t)
        (Space.isQuasicoherentOnSite_of_isInvertible B integerBase B.contains_integerBase _ _
          (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
            (isInvertible_fibreTwistingRead E A t))))

/-- The reading `G` of `𝒬_t` on `ℙⁿ_{κ(t)}`. -/
abbrev fibreReading : ((𝒯).obj (fibreSite (n := n) A t)).Modules :=
  (reading E (A.pointTest t)).obj (A.fibreModule t)

/-- `G ⊗ 𝒪(1)^{⊗ m}` on `ℙⁿ_{κ(t)}`. -/
abbrev fibreReadingTwist (m : ℤ) : ((𝒯).obj (fibreSite (n := n) A t)).Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨((𝒯).obj (fibreSite (n := n) A t)).presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ ((𝒯).obj (fibreSite (n := n) A t)).presheaf
        (forget₂ CommRingCat RingCat) ((𝒯).obj (fibreSite (n := n) A t)).ringCatSheaf.2⟩).obj
      (fibreReading E A t)).obj
    (Stacks.SheafOfModules.Invertible.tensorPower ((𝒯).obj (fibreSite (n := n) A t)).presheaf
      ((𝒯).obj (fibreSite (n := n) A t)).ringCatSheaf.2
      (twistingSheaf n ((𝒯).obj (A.pointScheme t)) 1) m)

/-- **`𝒬_t ⊗ 𝓛_t^{⊗ m}`, carried to the algebraic space of `ℙⁿ_{κ(t)}`, is the associated module
of `G ⊗ 𝒪(1)^{⊗ m}`** (Stacks 03EL, 01CU, 03DX). -/
def fibreTwistStepIso (m : ℤ) :
    (Space.modulePullback B integerBase B.contains_integerBase
        (spaceIso E (A.pointTest t)).hom).obj
        (Space.twistStep B integerBase B.contains_integerBase (A.fibreSpace t).1
          (A.fibreSpace t).2 (fibreTwisting E A t) m (A.fibreModule t)) ≅
      (fibreAssociated A t).obj (fibreReadingTwist E A t m) :=
  Space.modulePullbackSheafTensorIso B integerBase B.contains_integerBase
      (spaceIso E (A.pointTest t)).hom (A.fibreModule t)
      (Space.invertibleTensorPower B integerBase B.contains_integerBase (A.fibreSpace t).1
        (A.fibreSpace t).2 (fibreTwisting E A t) m) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (Space.smallEtaleRingedSite B integerBase B.contains_integerBase
        (schemeSpace (fibreSite (n := n) A t)).1 (schemeSpace (fibreSite (n := n) A t)).2).O).obj
        ((Space.modulePullback B integerBase B.contains_integerBase
          (spaceIso E (A.pointTest t)).hom).obj (A.fibreModule t))).mapIso
      (Space.modulePullbackInvertibleTensorPowerIso B integerBase B.contains_integerBase
        (spaceIso E (A.pointTest t)).hom (fibreTwisting E A t) m) ≪≫
    Space.twistStepIso B integerBase B.contains_integerBase
      (schemeSpace (fibreSite (n := n) A t)).1 (schemeSpace (fibreSite (n := n) A t)).2
      (fibreTwistingRead E A t) m (fibreModuleReadIso E A t) ≪≫
    (Space.representedAssociatedModuleTwistStepIso B integerBase B.contains_integerBase
      (fibreSite (n := n) A t) (twistingSheaf n ((𝒯).obj (A.pointScheme t)) 1)
      (fibreTwistingRead E A t) (fibreTwistingReadIso E A t) m (fibreReading E A t)).symm

/-- **`𝒪(1)^{⊗ m} ≅ 𝒪(m)` on `ℙⁿ_{κ(t)}`** (Stacks 01CU and 01MN), in the spelling of the
twists of `AlgebraicGeometry.ProjectiveQuot.twist`. -/
def fibreTensorPowerIso (m : ℤ) :
    Stacks.SheafOfModules.Invertible.tensorPower ((𝒯).obj (fibreSite (n := n) A t)).presheaf
        ((𝒯).obj (fibreSite (n := n) A t)).ringCatSheaf.2
        (twistingSheaf n ((𝒯).obj (A.pointScheme t)) 1) m ≅
      twistingSheaf n ((𝒯).obj (A.pointScheme t)) m :=
  Stacks.PowerFamilyBridge.tensorPowerModuleIso (projectiveSpaceOver n ((𝒯).obj (A.pointScheme t)))
      (twistingSheaf n ((𝒯).obj (A.pointScheme t)) 1) m ≪≫
    Stacks.AlgebraicGeometry.ProjTwistTensorPow.tensorPowModuleProjectiveTwistIso n _ m

/-- **`G ⊗ 𝒪(1)^{⊗ m}` is the twist `F_t(m)` of the fibre `F_t` of the reading `F` of the module of
`A` on `ℙⁿ_T`**: the reading of `𝒬_t` is the fibre of the reading of `𝒬`. -/
def fibreReadingTwistIso (m : ℤ) :
    fibreReadingTwist E A t m ≅ projectiveTwist n (fibre t ((reading E A.T).obj A.F)) m :=
  Stacks.SheafOfModules.Invertible.tensorProductIso ((𝒯).obj (fibreSite (n := n) A t)).presheaf
    ((𝒯).obj (fibreSite (n := n) A t)).ringCatSheaf.2
    (readingPullbackIso E (A.pointTestHom t) A.F A.quasicoherent) (fibreTensorPowerIso A t m)

/-! ### Euler characteristics -/

/-- The ring map `κ(t) ⟶ Γ(ℙⁿ_{κ(t)}, 𝒪)` read on the algebraic space of `ℙⁿ_{κ(t)}`: through the
structure morphism to `Spec κ(t)`. -/
abbrev fibreSpaceFieldHom : A.testScheme.residueField t →+*
    Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase
        B.contains_integerBase (schemeSpace (fibreSite (n := n) A t)).1
          (schemeSpace (fibreSite (n := n) A t)).2).O)) :=
  (Space.globalSectionsRingHom B integerBase B.contains_integerBase _ _
      (schemeSpaceMap (projectiveSiteStructure B n (A.pointScheme t))).hom).comp
    (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom

/-- **The twisted Euler characteristic with respect to `𝓛` is an Euler characteristic on the
algebraic space of `ℙⁿ_{κ(t)}`**: move along `h_{ℙⁿ_{κ(t)}} ≅ X_t`. -/
theorem twistedEuler_twistingModule_eq (m : ℤ) :
    A.twistedEuler (twistingModule E) t m =
      Space.eulerCharacteristicAlong B integerBase B.contains_integerBase
        (schemeSpace (fibreSite (n := n) A t)).1 (schemeSpace (fibreSite (n := n) A t)).2
        (A.testScheme.residueField t) (fibreSpaceFieldHom A t)
        ((Space.modulePullback B integerBase B.contains_integerBase
          (spaceIso E (A.pointTest t)).hom).obj
          (Space.twistStep B integerBase B.contains_integerBase (A.fibreSpace t).1
            (A.fibreSpace t).2 (fibreTwisting E A t) m (A.fibreModule t))) := by
  have hproj : (spaceIso E (A.pointTest t)).inv.hom ≫
      (schemeSpaceMap (projectiveSiteStructure B n (A.pointScheme t))).hom =
        (D.toCoherentSituation.projection (A.pointTest t)).hom :=
    have h : (spaceIso E (A.pointTest t)).inv ≫
        schemeSpaceMap (projectiveSiteStructure B n (A.pointScheme t)) =
          D.projection (A.pointTest t) :=
      (Iso.inv_comp_eq _).mpr (spaceIso_hom_projection E (A.pointTest t)).symm
    congrArg (fun k => k.hom) h
  have hc : Space.GlobalSectionRingHomsCompatible B integerBase B.contains_integerBase
      (spaceIso E (A.pointTest t)).inv
      (Space.relativelyRepresentable_of_isAffineHom B integerBase B.contains_integerBase _
        (Space.isAffineHom_of_isIso (spaceIso E (A.pointTest t)).inv.hom))
      (fibreSpaceFieldHom A t) (A.fibreFieldHom t) := by
    unfold Space.CoherentObject.fibreFieldHom
    rw [← hproj]
    exact Space.globalSectionRingHomsCompatible_globalSectionsRingHom B integerBase
      B.contains_integerBase (spaceIso E (A.pointTest t)).inv _ _ _
  have h0 := Space.CoherentObject.twistedEuler_eq_fibreTensorPower (twistingModule E) A t m
  have h3 : ((Stacks.SheafOfModules.Tensor.sheafTensor
      (Space.smallEtaleRingedSite B integerBase B.contains_integerBase (A.fibreSpace t).1
        (A.fibreSpace t).2).O).obj (A.fibreModule t)).obj
      (Space.invertibleTensorPower B integerBase B.contains_integerBase (A.fibreSpace t).1
        (A.fibreSpace t).2 (fibreTwisting E A t) m) =
      Space.twistStep B integerBase B.contains_integerBase (A.fibreSpace t).1
            (A.fibreSpace t).2 (fibreTwisting E A t) m (A.fibreModule t) := rfl
  have h4 : A.twistedEuler (twistingModule E) t m =
      Space.eulerCharacteristicAlong B integerBase B.contains_integerBase
        (A.fibreSpace t).1 (A.fibreSpace t).2 (A.testScheme.residueField t) (A.fibreFieldHom t)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
      (Space.smallEtaleRingedSite B integerBase B.contains_integerBase (A.fibreSpace t).1
        (A.fibreSpace t).2).O).obj (A.fibreModule t)).obj
      (Space.invertibleTensorPower B integerBase B.contains_integerBase (A.fibreSpace t).1
        (A.fibreSpace t).2 (fibreTwisting E A t) m)) := h0
  rw [h3] at h4
  exact h4.trans (Space.eulerCharacteristicAlong_modulePullback_of_iso
    (spaceIso E (A.pointTest t)) _ _ _ hc _
    (isQuasicoherentOnSite_twistStep _ _ m _ (isQuasicoherentOnSite_fibreModule A t))).symm

/-- The twisted Euler characteristic with respect to `𝓛` is the Euler characteristic of the
associated module of `G ⊗ 𝒪(1)^{⊗ m}` on the algebraic space of `ℙⁿ_{κ(t)}`. -/
theorem twistedEuler_twistingModule_eq_associated (m : ℤ) :
    A.twistedEuler (twistingModule E) t m =
      Space.eulerCharacteristicAlong B integerBase B.contains_integerBase
        (schemeSpace (fibreSite (n := n) A t)).1 (schemeSpace (fibreSite (n := n) A t)).2
        (A.testScheme.residueField t) (fibreSpaceFieldHom A t)
        ((fibreAssociated A t).obj (fibreReadingTwist E A t m)) :=
  (twistedEuler_twistingModule_eq E A t m).trans
    (Space.eulerCharacteristicAlong_congr B integerBase B.contains_integerBase _ _ _ _
      (fibreTwistStepIso E A t m))

/-- The ring map `κ(t) ⟶ Γ(ℙⁿ_{κ(t)}, 𝒪)` of `AlgebraicGeometry.cohomologyOverField`. -/
abbrev fibreZariskiFieldHom : A.testScheme.residueField t →+*
    ((𝒯).obj (fibreSite (n := n) A t)).ringCatSheaf.obj.obj (Opposite.op ⊤) :=
  ((Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv ≫
    (projectiveSpaceOverRing n (.of (A.testScheme.residueField t)) ↘
      Spec (.of (A.testScheme.residueField t))).appLE ⊤ ⊤ (by simp)).hom

/-- The structure morphism of `ℙⁿ_{κ(t)}`, through the identity chart, is the structure
morphism. -/
theorem chartToScheme_idChart_projectiveSiteStructure :
    Space.chartToScheme B integerBase B.contains_integerBase
        (schemeSpace (fibreSite (n := n) A t)).1
        (schemeSpaceMap (projectiveSiteStructure B n (A.pointScheme t))).hom
        (Space.idChart B integerBase B.contains_integerBase (fibreSite (n := n) A t)) =
      projectiveSiteStructure B n (A.pointScheme t) := by
  apply Yoneda.fullyFaithful.map_injective
  simp only [Space.chartToScheme, Functor.FullyFaithful.map_preimage]
  exact Category.id_comp _

/-- **The two readings of a scalar of `κ(t)` agree on the open `⊤`**, the compatibility through
which Stacks 03DW is read over `κ(t)`. -/
theorem fibreFieldHom_compatible (a : A.testScheme.residueField t) :
    (Space.representedSchemeStructureSheaf B integerBase B.contains_integerBase
        (fibreSite (n := n) A t)).obj.map
        (Space.representedTopToIdChartAlong B integerBase B.contains_integerBase
          (fibreSite (n := n) A t)).op
        ((Stacks.Cohomology.SiteModules.globalSectionEval
          (Space.representedStructureRingSheaf B integerBase B.contains_integerBase
            (fibreSite (n := n) A t))
          (Opposite.op (Space.idChart B integerBase B.contains_integerBase
            (fibreSite (n := n) A t)))) (fibreSpaceFieldHom A t a)) =
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((𝒯).obj (fibreSite (n := n) A t)) (fibreSite (n := n) A t).left.property).hom.app
          (Opposite.op ⊤) (fibreZariskiFieldHom A t a) := by
  have key : ∀ x, (Space.representedSchemeStructureSheaf B integerBase B.contains_integerBase
      (fibreSite (n := n) A t)).obj.map
      (Space.representedTopToIdChartAlong B integerBase B.contains_integerBase
        (fibreSite (n := n) A t)).op x =
        (Scheme.Γ.map ((associatedBigEtaleSite B).inclusion.map
          (Space.representedTopToIdChartAlong B integerBase B.contains_integerBase
            (fibreSite (n := n) A t)).hom.left).op).hom x := fun _ => rfl
  refine (key _).trans ?_
  rw [Space.representedTopToIdChartAlong_hom_left]
  have hev : (Stacks.Cohomology.SiteModules.globalSectionEval
          (Space.representedStructureRingSheaf B integerBase B.contains_integerBase
            (fibreSite (n := n) A t))
          (Opposite.op (Space.idChart B integerBase B.contains_integerBase
            (fibreSite (n := n) A t)))) (fibreSpaceFieldHom A t a) =
      (Scheme.Γ.map ((𝒯).map (Space.chartToScheme B integerBase B.contains_integerBase
        (schemeSpace (fibreSite (n := n) A t)).1
        (schemeSpaceMap (projectiveSiteStructure B n (A.pointScheme t))).hom
        (Space.idChart B integerBase B.contains_integerBase (fibreSite (n := n) A t)))).op).hom
        ((Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom a) := rfl
  rw [hev, chartToScheme_idChart_projectiveSiteStructure]
  have hcomp : Scheme.Γ.map ((𝒯).map (projectiveSiteStructure B n (A.pointScheme t))).op ≫
      Scheme.Γ.map ((⊤ : ((𝒯).obj (fibreSite (n := n) A t)).Opens).ι).op =
      (projectiveSpaceOverRing n (.of (A.testScheme.residueField t)) ↘
        Spec (.of (A.testScheme.residueField t))).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.Opens.topIso (⊤ : ((𝒯).obj (fibreSite (n := n) A t)).Opens)).inv := by
    simp only [Scheme.Γ_map_op, Scheme.Hom.appLE, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv,
      Scheme.Hom.appTop]
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg (_ ≫ ·) ?_
    refine Eq.trans ?_ (((𝒯).obj (fibreSite (n := n) A t)).presheaf.map_comp _ _)
    exact congrArg ((𝒯).obj (fibreSite (n := n) A t)).presheaf.map (Subsingleton.elim _ _)
  exact congrArg (fun f => ((Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv ≫ f).hom a)
    hcomp

/-- **The Euler characteristic of an associated module on the algebraic space of `ℙⁿ_{κ(t)}` is
the Euler characteristic of the module on the scheme** (Stacks 03DW over `κ(t)`). -/
theorem eulerCharacteristicAlong_fibreAssociated (H : ((𝒯).obj (fibreSite (n := n) A t)).Modules)
    (hH : SheafOfModules.IsQuasicoherent H) :
    Space.eulerCharacteristicAlong B integerBase B.contains_integerBase
        (schemeSpace (fibreSite (n := n) A t)).1 (schemeSpace (fibreSite (n := n) A t)).2
        (A.testScheme.residueField t) (fibreSpaceFieldHom A t) ((fibreAssociated A t).obj H) =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank (A.testScheme.residueField t)
        (cohomologyOverField (A.testScheme.residueField t)
          (projectiveSpaceOverRing n (.of (A.testScheme.residueField t)) ↘
            Spec (.of (A.testScheme.residueField t))) H i) : ℤ) := by
  refine (Space.eulerCharacteristicAlong_eq_finsum_rightDerived B integerBase
    B.contains_integerBase _ _ _ _ _).trans ?_
  congr 1
  funext i
  congr 2
  exact ((Space.representedCohomologyAssociatedModuleIsoAlong B integerBase B.contains_integerBase
    (fibreSite (n := n) A t) (A.testScheme.residueField t) (fibreSpaceFieldHom A t)
    (fibreZariskiFieldHom A t) (fibreFieldHom_compatible A t) H hH i).toLinearEquiv.trans
      ULift.moduleEquiv).finrank_eq

/-- The reading of the module of `A` on `ℙⁿ_T` is of finite presentation. -/
theorem isFinitePresentation_reading_F : ((reading E A.T).obj A.F).IsFinitePresentation :=
  isFinitePresentation_reading E A.T A.F A.quasicoherent A.finitePresentation

/-- `G ⊗ 𝒪(1)^{⊗ m}` is quasi-coherent. -/
theorem isQuasicoherent_fibreReadingTwist (m : ℤ) :
    SheafOfModules.IsQuasicoherent (fibreReadingTwist E A t m) :=
  _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_tensorSheaf_of_isQuasicoherent _ _ _
    (isQuasicoherent_isoReading_obj (spaceIso E (A.pointTest t)) _
      (isQuasicoherentOnSite_fibreModule A t))
    (Scheme.Modules.isQuasicoherent_tensorPower_of_isInvertible _ m)

/-- **The twisted Euler characteristic with respect to the pullback `𝓛` of `𝒪(1)` is the Hilbert
polynomial on the fibre**: for an object `(T, 𝒬)` of `Coh_{X/B}`, a point `t ∈ T` and `m ∈ ℤ`,
`χ(X_t, 𝒬_t ⊗ 𝓛_t^{⊗ m})` is the value at `m` of the Hilbert polynomial of the fibre over `t` of
the reading of `𝒬` on `ℙⁿ_T`. -/
theorem twistedEuler_twistingModule_eq_hilbertPolynomial (m : ℤ) :
    A.twistedEuler (twistingModule E) t m =
      @hilbertPolynomial (A.testScheme.residueField t) _ n (fibre t ((reading E A.T).obj A.F))
        (@isCoherent_fibre n _ t _ (isFinitePresentation_reading_F E A)) m := by
  refine (twistedEuler_twistingModule_eq_associated E A t m).trans
    ((eulerCharacteristicAlong_fibreAssociated A t _
      (isQuasicoherent_fibreReadingTwist E A t m)).trans ?_)
  unfold hilbertPolynomial
  congr 1
  funext i
  congr 2
  exact finrank_cohomologyOverField_eq_of_iso _ _ (fibreReadingTwistIso E A t m) i

end Fibre

/-! ### `Quot^P` with respect to `𝓛` -/

section Subfunctor

variable {D : Space.QuotSituation B integerBase B.contains_integerBase} (E : ProjectiveFrame B n D)

/-- **`Quot^P_{F/X/B}` with respect to the pullback `𝓛` of `𝒪(1)` is the subfunctor of quotients
with fibrewise Hilbert polynomial `P` on projective spaces** (Stacks 0DP6 and 0DNF at
`E_m = 𝓛^{⊗ m}`), for `P` the function of a rational polynomial `p`. -/
theorem hilbertPolynomialQuot_twistingModule_eq {P : ℤ → ℤ} {p : Polynomial ℚ}
    (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    D.hilbertPolynomialQuot (twistingModule E) P = hilbertSubfunctor E p := by
  ext T x
  change (∀ (t : x.cohObject.testScheme) (m : ℤ),
      P m = x.cohObject.twistedEuler (twistingModule E) t m) ↔
    x.subobject ∈ D.properlySupportedQuotients _ ∧
      HasFibreHilbertPolynomial p ((reading E (CostructuredArrow.mk x.toBase)).obj
        (D.quotientModule _ x.subobject))
  constructor
  · intro h
    refine ⟨x.mem, fun t => ⟨@isCoherent_fibre n _ t _
      (isFinitePresentation_reading_F E x.cohObject), fun d => ?_⟩⟩
    rw [hP d, h t d, twistedEuler_twistingModule_eq_hilbertPolynomial E x.cohObject t d]
    rfl
  · rintro ⟨-, hfib⟩ t m
    obtain ⟨_, hd⟩ := hfib t
    have h : (x.cohObject.twistedEuler (twistingModule E) t m : ℚ) = p.eval (m : ℚ) := by
      rw [twistedEuler_twistingModule_eq_hilbertPolynomial E x.cohObject t m]
      exact hd m
    exact_mod_cast (h.trans (hP m)).symm

end Subfunctor

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
