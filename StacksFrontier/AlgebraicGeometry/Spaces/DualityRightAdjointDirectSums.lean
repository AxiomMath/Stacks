module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompactQcqs
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts

/-!
# The right adjoint of `Rf_*` commutes with direct sums

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated algebraic spaces and let `a`
be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` (Stacks 0E55). If `Rf_*` carries
perfect objects to perfect objects, then `a` commutes with direct sums. This applies when `f` is
proper, flat and of finite presentation, which is Stacks 0E5T.

## Main results

* `preservesCoproducts_rightAdjoint_quasicoherentDerivedPushforward`: `a` commutes with direct
  sums when `Rf_*` preserves perfect objects.
* `preservesCoproducts_rightAdjoint_quasicoherentDerivedPushforward_of_isProper`: `a` commutes
  with direct sums when `f` is proper, flat and of finite presentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The right adjoint of `Rf_*` commutes with direct sums when `Rf_*` preserves perfect
objects.** Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated algebraic spaces
such that `Rf_*` carries every perfect object of `D_QCoh(𝒪_X)` to a perfect object. Then the
right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with direct sums. -/
theorem preservesCoproducts_rightAdjoint_quasicoherentDerivedPushforward
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hperf : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E.obj →
        (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
          ((derivedModulePushforward B S hS f).obj E.obj)) :
    haveI := isLeftAdjoint_quasicoherentDerivedPushforward hZ f hXqc hXqs hYqs
    ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (quasicoherentDerivedPushforward B S hS f
        (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
        (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs
          f.hom)).rightAdjoint := by
  have := isLeftAdjoint_quasicoherentDerivedPushforward hZ f hXqc hXqs hYqs
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X.1 X.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS Y.1 Y.2
  obtain ⟨G, hGc, hG⟩ := exists_isCompactObject_isWeakTriangulatedGenerator_of_qcqs B S hS hZ X
    hXqc hXqs
  let adj := Adjunction.ofIsLeftAdjoint (quasicoherentDerivedPushforward B S hS f
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom))
  have := adj.right_adjoint_additive
  exact preservesCoproducts_of_isCompactObject_map adj G hG hGc
    ((isCompactObject_iff_isPerfect Y hYqc hYqs _).2
      (hperf G ((isCompactObject_iff_isPerfect X hXqc hXqs G).1 hGc)))

/-- Let `Y` be a quasi-compact and quasi-separated algebraic space and
`f : X ⟶ Y` a proper, flat morphism of finite presentation. Then the right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` (Stacks 0E55) commutes with direct sums. -/
@[stacks 0E5T]
theorem preservesCoproducts_rightAdjoint_quasicoherentDerivedPushforward_of_isProper
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom) :
    haveI := isLeftAdjoint_quasicoherentDerivedPushforward hZ f
      (isQuasiCompactSpace_of_isQuasiCompact B S hS Y.2 hYqc f.hom hfp.2.1)
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X.2 hYqs hfp.2.2) hYqs
    ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (quasicoherentDerivedPushforward B S hS f hfp.2.1 hfp.2.2).rightAdjoint :=
  preservesCoproducts_rightAdjoint_quasicoherentDerivedPushforward hZ f
    (isQuasiCompactSpace_of_isQuasiCompact B S hS Y.2 hYqc f.hom hfp.2.1)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X.2 hYqs hfp.2.2) hYqc hYqs
    fun E hE => (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp
      E.obj hE).1

end AlgebraicGeometry.Space

end
