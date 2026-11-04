module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedTensorTorAmplitudeOver
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedTensorProduct

/-!
# Perfect objects are perfect relative to the base, at the derived tensor product of Stacks 06YU

Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite presentation. We
prove the two assertions of [Stacks, Tag 0DI4], relative perfectness being read at the canonical
certificate family `AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`,
the derived tensor product of each open subspace of `(X, f⁻¹𝒪_S)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_base_of_flat`: for `f` flat,
  Tor amplitude of a derived stalk over the local ring of `X` gives the same Tor amplitude over
  the local ring of `S`.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_canonical_of_isPerfect`: a perfect object
  of `D(𝒪_X)` is perfect relative to `S`.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_canonical_derivedTensor`: the derived tensor
  product of a perfect object with an `S`-perfect object is perfect relative to `S`.

## References

* [Stacks Project, Tag 0DI4](https://stacks.math.columbia.edu/tag/0DI4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
  StrictlyPerfect

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

section Faithful

attribute [local instance 10000] HasDerivedCategory.standard

/-- Restriction of scalars along a ring homomorphism is additive. -/
local instance (priority := 10000) additive_restrictScalars_0DI4
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u} φ).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along a ring homomorphism preserves finite limits. -/
local instance (priority := 10000) preservesFiniteLimits_restrictScalars_0DI4
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits φ

/-- Restriction of scalars along a ring homomorphism preserves finite colimits. -/
local instance (priority := 10000) preservesFiniteColimits_restrictScalars_0DI4
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits φ

attribute [local instance] commRing_stalk_structure_at

/-- For `f` flat, if the derived stalk of `E` at `y` has Tor amplitude in `[a, b]` over the stalk
ring of `𝒪_X`, then its restriction of scalars along `𝒪_{S, f y} ⟶ 𝒪_{X, y}` has Tor amplitude in
`[a, b]` over `𝒪_{S, f y}`. -/
theorem hasTorAmplitudeCanonical_derivedStalk_base_of_flat [Flat f]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (y : X) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafOfRings.{u} X.toRingedSpace).obj y))
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} X.toRingedSpace) y).mapDerivedCategory.obj E) a b) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base y)))
      ((ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv X.presheaf y).symm.toRingHom.comp
            (f.stalkMap y).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) y).mapDerivedCategory.obj E)) a b := by
  have hφ : ((SemilinearStalk.commStalkRingEquiv X.presheaf y).symm.toRingHom.comp
      (f.stalkMap y).hom).Flat :=
    RingHom.Flat.comp (Flat.stalkMap f y)
      (RingHom.Flat.of_bijective (SemilinearStalk.commStalkRingEquiv X.presheaf y).symm.bijective)
  have key : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ M : ModuleCat.{u} B, Module.Flat B M →
        Module.Flat A ((ModuleCat.restrictScalars.{u} φ).obj M) := by
    intro A B _ _ φ hφ M hM
    let := φ.toAlgebra
    have : Module.Flat A B := hφ
    have : Module.Flat B ((ModuleCat.restrictScalars.{u} φ).obj M) := hM
    have : IsScalarTower A B ((ModuleCat.restrictScalars.{u} φ).obj M) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact Module.Flat.trans A B ((ModuleCat.restrictScalars.{u} φ).obj M)
  exact BaseChangeTorAmplitude.hasTorAmplitudeCanonical_map_of_preservesFlat _ (key _ hφ) _ a b h

/-- Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite presentation. A
perfect object of `D(𝒪_X)` is `S`-perfect, relative perfectness being read at the derived tensor
product of Stacks 06YU on each open subspace of `(X, f⁻¹𝒪_S)`. -/
theorem isPerfectRelativeTo_canonical_of_isPerfect [Flat f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (hE : RingedSpace.IsPerfect E) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E := by
  refine ⟨hE.isPseudoCoherent, ?_⟩
  obtain ⟨I, U, hU, h⟩ :=
    Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect E hE
  refine (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover f _
    (isGenuineRelativeTensorFamily_canonical f) E).2 ⟨I, U, hU, fun i => ?_⟩
  obtain ⟨a, b, hab⟩ := h i
  refine ⟨a, b, fun y hy => (hasTorAmplitudeCanonical_derivedStalk_relative_iff f y E a b).2 ?_⟩
  exact hasTorAmplitudeCanonical_derivedStalk_base_of_flat f E y a b
    ((Stacks.Thickenings.hasTorAmplitude_restrictModules_iff_forall_stalk X.toRingedSpace (U i) E
      a b).1 hab y hy)

/-- Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite presentation,
and let `K, M ∈ D(𝒪_X)`. If `K` is perfect and `M` is `S`-perfect, then `K ⊗^{L}_{𝒪_X} M` is
`S`-perfect. The derived tensor product is the one of Stacks 06YU, and relative perfectness is
read at the derived tensor product of Stacks 06YU on each open subspace of `(X, f⁻¹𝒪_S)`. -/
theorem isPerfectRelativeTo_canonical_derivedTensor [Flat f] [LocallyOfFinitePresentation f]
    (K M : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (hK : RingedSpace.IsPerfect K)
    (hM : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) M) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      (((Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct
        X.toRingedSpace).tensor.obj K).obj M) := by
  refine ⟨RingedSpace.isPseudoCoherent_derivedTensorProduct X.toRingedSpace
    (Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct X.toRingedSpace) K M
    hK.isPseudoCoherent hM.1, ?_⟩
  obtain ⟨I, U, hU, hKU⟩ :=
    Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect K hK
  obtain ⟨J, V, hV, hMV⟩ := (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover
    f _ (isGenuineRelativeTensorFamily_canonical f) M).1 hM.2
  refine (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover f _
    (isGenuineRelativeTensorFamily_canonical f) _).2
    ⟨I × J, fun ij => U ij.1 ⊓ V ij.2, ?_, fun ij => ?_⟩
  · refine top_unique fun x _ => ?_
    have hxU : x ∈ iSup U := by rw [hU]; trivial
    have hxV : x ∈ iSup V := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxV
    exact Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩
  · obtain ⟨a, b, hab⟩ := hKU ij.1
    obtain ⟨c, d, hcd⟩ := hMV ij.2
    refine ⟨a + c, b + d, fun y hy =>
      (hasTorAmplitudeCanonical_derivedStalk_relative_iff f y _ _ _).2 ?_⟩
    exact hasTorAmplitudeCanonical_derivedStalk_derivedTensor f
      (Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct X.toRingedSpace) K M y a b c d
      ((Stacks.Thickenings.hasTorAmplitude_restrictModules_iff_forall_stalk X.toRingedSpace
        (U ij.1) K a b).1 hab y hy.1)
      ((hasTorAmplitudeCanonical_derivedStalk_relative_iff f y M c d).1 (hcd y hy.2))

end Faithful

end Scheme.Hom

end AlgebraicGeometry

end
