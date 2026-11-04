module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ScalarRestrictionFlatOver
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.RestrictionFreeModuleUniverse

/-!
# Flatness and Tor amplitude over `f⁻¹𝒪_Y` along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  By Stacks 03LV the inverse-image form `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map
of the morphism of small étale ringed topoi of Stacks 03G8 is an *isomorphism*, so restriction
of scalars along it changes nothing but the name of the acting sheaf of rings.  This file draws
the two consequences that the Tor-dimension vocabulary of Stacks 08FZ needs: a flat
`𝒪_X`-module is flat over `f⁻¹𝒪_Y`, and Tor amplitude and finite Tor dimension pass from `𝒪_X`
to `f⁻¹𝒪_Y`.

## Main results

* `AlgebraicGeometry.Space.isFlat_scalarRestriction_of_isEtale`: a flat `𝒪_X`-module read over
  `f⁻¹𝒪_Y` is flat.
* `AlgebraicGeometry.Space.hasTorAmplitude_derivedScalarRestriction_of_isEtale_of_le` and
  `hasFiniteTorDimension_derivedScalarRestriction_of_isEtale`: Tor amplitude in a nonempty
  interval, and finite Tor dimension, pass from `𝒪_X` to `f⁻¹𝒪_Y`.

## The proof

Flatness is the only input.  Extension of scalars along the inverse of `f♯` and restriction of
scalars along `f♯` are both left adjoint to restriction of scalars along the inverse of `f♯`:
the first by the change-of-rings adjunction of Stacks 03CZ, the second because restriction of
scalars along an isomorphism is half of the equivalence
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`.  So they agree, by uniqueness of
left adjoints, and Stacks 05V4 — extension of scalars preserves flatness — transports along that
agreement.  Tor amplitude then moves by Stacks 08G1 in both directions: a bounded complex of
flat `𝒪_X`-modules representing the object has flat terms over `f⁻¹𝒪_Y`, and a complex of that
shape has the same Tor amplitude.

## Implementation notes

The two derived tensor product data are unrelated parameters.  Only the vanishing of cohomology
sheaves is transported, by the direction of Stacks 08G1 which takes no input, so no comparison
of them is needed and none is made — the same device as
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedRestriction`.

No `@[stacks ...]` attribute is placed here.  Nothing below is an assertion of a numbered result
that is not registered where it is proved: the invertibility of the structure map at an étale
morphism is Stacks 03LV, registered in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleStructureSheafInverseImage.lean`, and the two
Tor-theoretic inputs are Stacks 05V4 and Stacks 08G1, registered where they are proved.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u d e

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-! ### Flatness over `f⁻¹𝒪_Y` -/

include hf in
/-- **A flat `𝒪_X`-module is flat over `f⁻¹𝒪_Y` when `f` is étale.**  By Stacks 03LV the
structure map `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` is an isomorphism, so restriction of scalars along it is
isomorphic to extension of scalars along its inverse, both being left adjoint to restriction of
scalars along the inverse; and extension of scalars preserves flatness, which is Stacks 05V4.

Unlike `AlgebraicGeometry.Space.isFlat_scalarRestriction_of_isFlatOver`, which reaches the same
conclusion for an arbitrary `f` from flatness of the module over the base, this needs no
quasi-coherence and nothing about the module beyond flatness over `𝒪_X`. -/
theorem isFlat_scalarRestriction_of_isEtale (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (smallEtaleRingedTopos B S hS X).O) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := (inverseImageRingedSite B S hS f).O)
      ((scalarRestriction B S hS f).obj M) :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
    (((Stacks.FlatChangeOfRings.extendScalarsAdjunction
      (etaleStructureSheafIso B S hS f hf).inv).leftAdjointUniq
        (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
          (etaleStructureRingSheafIso B S hS f hf).symm).toAdjunction).app M)
    (Stacks.FlatChangeOfRings.isFlat_extendScalars _ M hM)

/-! ### Tor amplitude over `f⁻¹𝒪_Y` -/

include hf in
/-- **Tor amplitude in a nonempty interval passes from `𝒪_X` to `f⁻¹𝒪_Y` along an étale
morphism.**  Stacks 08G1 represents an object of Tor amplitude in `[a, b]`, with `a ≤ b`, by a
complex of flat `𝒪_X`-modules concentrated in `[a, b]`; restriction of scalars along `f♯` keeps
the terms flat, by `AlgebraicGeometry.Space.isFlat_scalarRestriction_of_isEtale`, and keeps the
complex concentrated in `[a, b]`, being additive; and a complex of that shape has Tor amplitude
in `[a, b]` by the direction of Stacks 08G1 which takes no input. -/
theorem hasTorAmplitude_derivedScalarRestriction_of_isEtale_of_le
    [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2).O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).Additive]
    [∀ (M N : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ),
      HomologicalComplex.HasMapBifunctor M N
        (Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O)
        (ComplexShape.up ℤ)]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (inverseImageRingedSite B S hS f).O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (inverseImageRingedSite B S hS f).O).obj M).Additive]
    [∀ (M N : CochainComplex (RingedSite.Modules.{u + 1, u, u}
        (inverseImageRingedSite B S hS f)) ℤ),
      HomologicalComplex.HasMapBifunctor M N
        (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageRingedSite B S hS f).O)
        (ComplexShape.up ℤ)]
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, d}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (T' : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
      (inverseImageRingedSite B S hS f))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a b : ℤ) (hab : a ≤ b)
    (hamp : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude T K a b) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude T'
      ((derivedScalarRestriction B S hS f).obj K) a b := by
  obtain ⟨P, hflat, hzero, ⟨eP⟩⟩ :=
    Stacks.SheafOfModules.DerivedTensorProduct.exists_flatRepresentative_of_hasTorAmplitude
      T K a b hab hamp
  have : (scalarRestriction B S hS f).Additive := ⟨by intros; ext; rfl⟩
  refine Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative
    T' _ a b (((scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (fun i => isFlat_scalarRestriction_of_isEtale B S hS f hf (P.X i) (hflat i))
    (fun i hi => (scalarRestriction B S hS f).map_isZero (hzero i hi)) ?_
  exact ((scalarRestriction B S hS f).mapDerivedCategoryFactors.app P).symm ≪≫
    (scalarRestriction B S hS f).mapDerivedCategory.mapIso eP

include hf in
/-- **Finite Tor dimension passes from `𝒪_X` to `f⁻¹𝒪_Y` along an étale morphism**: an interval
containing the Tor amplitude may be taken nonempty, by
`Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_iff`. -/
theorem hasFiniteTorDimension_derivedScalarRestriction_of_isEtale
    [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2).O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).Additive]
    [∀ (M N : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ),
      HomologicalComplex.HasMapBifunctor M N
        (Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O)
        (ComplexShape.up ℤ)]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (inverseImageRingedSite B S hS f).O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (inverseImageRingedSite B S hS f).O).obj M).Additive]
    [∀ (M N : CochainComplex (RingedSite.Modules.{u + 1, u, u}
        (inverseImageRingedSite B S hS f)) ℤ),
      HomologicalComplex.HasMapBifunctor M N
        (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageRingedSite B S hS f).O)
        (ComplexShape.up ℤ)]
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, d}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (T' : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
      (inverseImageRingedSite B S hS f))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (h : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T K) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T'
      ((derivedScalarRestriction B S hS f).obj K) := by
  obtain ⟨a, b, hab, hamp⟩ :=
    (Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_iff T K).1 h
  exact ⟨a, b, hasTorAmplitude_derivedScalarRestriction_of_isEtale_of_le B S hS f hf T T' K a b
    hab hamp⟩

end AlgebraicGeometry.Space

end
