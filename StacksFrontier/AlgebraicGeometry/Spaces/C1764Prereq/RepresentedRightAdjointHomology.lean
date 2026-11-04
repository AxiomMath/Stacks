module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedRightAdjointDuality
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplex

/-!
# Cohomology sheaves of the right adjoint of `Rf_*` for a represented morphism

Let `g : T' ⟶ T` be a morphism of quasi-compact quasi-separated schemes of the big fppf site,
`f : X ⟶ Y` the represented morphism of algebraic spaces, and `ε : X ⟶ X_0` the comparison of
the small étale topos of `X` with the Zariski topos of the scheme `X_0`. This file reads the
cohomology sheaves of `a(𝒪_Y)`, for `a` the right adjoint of `Rf_*` (Stacks 0E55), on the scheme:
`H^i(a(𝒪_Y)) ≅ ε^* H^i(a_0(𝒪_{Y_0}))` for the twisted inverse image `a_0` of the morphism of
schemes (Stacks 0A9E), by Stacks 0E6E and the equivalence of Stacks 071Q.

## Main definitions

* `AlgebraicGeometry.C1764Prereq.representedDualityStructureSheafIso`: the equivalence of
  Stacks 071Q carries `𝒪_{X_0}` to `𝒪_X`.
* `AlgebraicGeometry.C1764Prereq.representedDualityHomologyIso`: the equivalence of Stacks 071Q
  carries `H^i` to `ε^* H^i`.
* `AlgebraicGeometry.C1764Prereq.homologyRightAdjointStructureSheafIso`:
  `H^i(a(𝒪_Y)) ≅ ε^* H^i(a_0(𝒪_{Y_0}))`.

## References

* [Stacks Project, Tag 0E6E](https://stacks.math.columbia.edu/tag/0E6E)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.C1764Prereq

open Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  SheafOfModules.instAbelian

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- The equivalence `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` of Stacks 071Q carries the structure sheaf
`𝒪_{X_0}` in degree zero to the structure sheaf `𝒪_X` in degree zero. -/
def representedDualityStructureSheafIso (T : BigFppfOver B S hS) :
    (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor.obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) ≅
      Space.derivedStructureSheaf B S hS (representedSpace T).1 (representedSpace T).2 := by
  refine ObjectProperty.isoMk _ ?_
  let O₀ := SheafOfModules.unit
    (representedSchemeRepresentedZariskiRingedToposHom B S hS T).ringCatSheaf
  let e₁ := (representedZariskiDerivedPullbackIso B S hS T).app
    ((DerivedCategory.singleFunctor _ 0).obj O₀)
  let e₂ := ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS
    T).mapDerivedCategorySingleFunctor 0).app O₀
  let e₃ := (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
      B S hS T).app O₀ ≪≫
    representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T)
  exact e₁ ≪≫ e₂ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e₃

end

/-- The equivalence `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` of Stacks 071Q carries the `i`-th cohomology
sheaf of an object to the pullback along `ε : X ⟶ X_0` of its `i`-th cohomology sheaf. -/
def representedDualityHomologyIso (T : BigFppfOver B S hS)
    (M : Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) (i : ℤ) :
    (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
        ((representedDualityQuasicoherentDerivedEquivalence B S hS T).functor.obj M).obj ≅
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj
        ((DerivedCategory.homologyFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules i).obj M.obj) := by
  letI := HasDerivedCategory.standard
    (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules
  letI := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS (representedSpace T).1 (representedSpace T).2).O))
  let C := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules
  let N := (Stacks.Injectives.grothendieckModelEquiv C).inverse.obj M.obj
  let e₀ : (DerivedCategory.homologyFunctor C i).obj N ≅
      (@DerivedCategory.homologyFunctor C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian C) i).obj M.obj :=
    ((StacksDraft.DerivedModel.grothendieckModelEquivHomologyIso C i).app N).symm ≪≫
      (@DerivedCategory.homologyFunctor C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian C) i).mapIso
        ((Stacks.Injectives.grothendieckModelEquiv C).counitIso.app M.obj)
  exact (representedZariskiDerivedPullbackHomologyIso B S hS T i).app N ≪≫
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).mapIso e₀

/-- **Cohomology sheaves of `a(𝒪_Y)` for a represented morphism** (Stacks 0E6E, 071Q). For a
morphism `g : T' ⟶ T` of the big fppf site between quasi-compact quasi-separated schemes, the
`i`-th cohomology sheaf of the right adjoint `a(𝒪_Y)` of `Rf_*` for the represented morphism `f`
of algebraic spaces is the pullback along `ε : X ⟶ X_0` of the `i`-th cohomology sheaf of the
twisted inverse image `a_0(𝒪_{Y_0})` of the morphism of schemes. -/
def homologyRightAdjointStructureSheafIso
    (hZ : B.Contains (⊤_ Scheme.{u})) {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hXqc : IsQuasiCompactSpace B S hS (yoneda.obj T'))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T'))
    (hYqc : IsQuasiCompactSpace B S hS (yoneda.obj T))
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T)) (i : ℤ) :
    haveI : CompactSpace (B.inclusion.obj T'.left) :=
      compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hXqc
    haveI : QuasiSeparatedSpace (B.inclusion.obj T'.left) :=
      (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T').1 hXqs
    haveI : CompactSpace (B.inclusion.obj T.left) :=
      compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hYqc
    haveI : QuasiSeparatedSpace (B.inclusion.obj T.left) :=
      (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T).1 hYqs
    haveI :=
      Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
        (B.inclusion.map g.left)
    (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
        ((Space.quasicoherentDerivedRightAdjoint hZ (representedSpaceMap B S hS g) hXqc hXqs
            hYqs).obj
          (Space.derivedStructureSheaf B S hS (representedSpace T).1 (representedSpace T).2)).obj ≅
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T').obj
        ((DerivedCategory.homologyFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T').Modules i).obj
          ((Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward
            (B.inclusion.map g.left)).rightAdjoint.obj
            (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
              (representedSchemeRepresentedZariskiRingedToposHom B S hS T))).obj) := by
  haveI : CompactSpace (B.inclusion.obj T'.left) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hXqc
  haveI : QuasiSeparatedSpace (B.inclusion.obj T'.left) :=
    (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T').1 hXqs
  haveI : CompactSpace (B.inclusion.obj T.left) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hYqc
  haveI : QuasiSeparatedSpace (B.inclusion.obj T.left) :=
    (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T).1 hYqs
  haveI := Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
    (B.inclusion.map g.left)
  let e := (Space.quasicoherentDerivedRightAdjoint hZ (representedSpaceMap B S hS g) hXqc hXqs
      hYqs).mapIso (representedDualityStructureSheafIso T).symm ≪≫
    ((Space.representedRightAdjointIso hZ g hXqc hXqs hYqc hYqs).app
      (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T))).symm
  exact (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).mapIso
      ((ObjectProperty.ι _).mapIso e) ≪≫
    representedDualityHomologyIso T' _ i

end AlgebraicGeometry.C1764Prereq

end
