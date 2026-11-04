module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkCompact
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BoundedLocalApproximation

/-!
# Objects perfect relative to an isomorphism

An object of `D(𝒪_X)` which is perfect relative to an isomorphism `X ⟶ S` in the sense of
[Stacks, Tag 0DI0], with `X` quasi-compact, is perfect.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfect_of_isPerfectRelativeTo_of_isIso`: an object perfect
  relative to an isomorphism is perfect.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **An object perfect relative to an isomorphism is perfect.** For an isomorphism of schemes
`f : X ⟶ S` with `X` quasi-compact, an object of `D(𝒪_X)` perfect relative to `S` at the
canonical certificates is perfect. -/
theorem isPerfect_of_isPerfectRelativeTo_of_isIso [IsIso f] [CompactSpace X]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : f.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _) E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E := by
  obtain ⟨a, b, h⟩ := exists_stalkTorAmplitude_of_isPerfectRelativeTo_of_compactSpace f _
    (isGenuineRelativeTensorFamily_canonical f) E hE
  have h₂ : ∀ x : X, HasTorAmplitudeCanonical
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafOfRings.{u} X.toRingedSpace).obj x))
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj E) a b := fun x ↦
    (hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff
      ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.trans
        (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm) _ a b).1
      ((hasTorAmplitudeCanonical_derivedStalk_relative_iff f x E a b).1 (h x))
  have hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b :=
    (Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeCanonical_forall_stalk_iff
      X.toRingedSpace.sheaf E a b).2 h₂
  have hamp' : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E (min a b)
      (max a b) := fun F j hj ↦
    hamp F j fun hmem ↦ hj ⟨(min_le_left a b).trans hmem.1, hmem.2.trans (le_max_right a b)⟩
  exact
    Stacks.Cohomology.PerfectFromTorAmplitude.isPerfect_of_hasTorAmplitude_of_isPseudoCoherentFrom
      E (min a b) (max a b) min_le_max hamp'
      ((AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall E).1 hE.1 (min a b - 1))

end AlgebraicGeometry.Scheme.Hom

end
