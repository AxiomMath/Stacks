module

public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundednessGenerator
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.PseudoCoherentByPerfectTwists
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectTwistsDetectIsomorphisms
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.IsPerfectComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace

/-!
# Perfect twists of an object right orthogonal to `D_QCoh` have no cohomology

Let `A` be a ring, let `X` be a scheme over `A` and let `C` be an object of `D(𝒪_X)` which is
right orthogonal to `D_QCoh(𝒪_X)`: every morphism `Q ⟶ C` from an object `Q` with quasi-coherent
cohomology sheaves is zero. Then for every perfect object `E` of `D(𝒪_X)`

`RΓ(X, C ⊗^𝐋 E) = 0`.

## Main results

* `AlgebraicGeometry.isZero_derivedModuleGlobalSections_derivedTensor_of_forall_hom_eq_zero`: the
  vanishing of `RΓ(X, E ⊗^𝐋 C)` in `D(ℤ)`, on the ringed site of opens.
* `AlgebraicGeometry.isZero_derivedGlobalSectionsOver_sheafDerivedTensor_of_forall_hom_eq_zero`:
  the vanishing of the `A`-linear `RΓ(X, C ⊗^𝐋 E)`, for `Stacks.SheafOfModules.derivedTensor`.
* `AlgebraicGeometry.isZero_derivedGlobalSectionsOver_derivedTensor_of_forall_hom_eq_zero`: the
  same for the derived tensor product of the projection formula, with perfectness that of the
  ringed space.

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules Stacks.Cohomology.ModuleSections

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance_reducible] CategoryTheory.sheafCompose

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- **Perfect twists of an object right orthogonal to `D_QCoh(𝒪_X)` have no cohomology**, on the
ringed site of opens. Let `E` be a perfect object of `D(𝒪_X)` and let `C` be an object of `D(𝒪_X)`
such that every morphism `Q ⟶ C` from an object `Q` with quasi-coherent cohomology sheaves is
zero. Then `RΓ(X, E ⊗^𝐋 C) = 0` in `D(ℤ)`. -/
theorem isZero_derivedModuleGlobalSections_derivedTensor_of_forall_hom_eq_zero
    (E C : DerivedCategory (StructureSheafModules X.sheaf))
    (hE : (ringedSite X.sheaf).IsPerfect E)
    (hC : ∀ Q : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
        (StructureSheafModules X.sheaf) i).obj Q).IsQuasicoherent) →
        ∀ φ : Q ⟶ C, φ = 0) :
    IsZero ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
      (((derivedTensor X.sheaf).obj E).obj C)) := by
  have hDqc := isQuasicoherent_homology_of_isPerfect (derivedDual X.sheaf E)
    (Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace _
      (isPerfect_derivedDual X.sheaf E hE))
  refine Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj _ fun i ↦ ?_
  refine (isZero_homology_tensor_iff_subsingleton_ext_dual E C hE i).2
    ((subsingleton_shiftedHom_iff_ext _ C i).1 ⟨fun a b ↦ ?_⟩)
  have hq : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) j).obj ((derivedDual X.sheaf E)⟦-i⟧)).IsQuasicoherent :=
    fun j ↦ (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((((DerivedCategory.homologyFunctor _ 0).shiftIso (-i) j (-i + j) rfl).app
        (derivedDual X.sheaf E)).symm) (hDqc (-i + j))
  exact (hC _ hq a).trans (hC _ hq b).symm

/-- **The same vanishing in `D(A)`, with the factors exchanged.** Under the hypotheses of
`isZero_derivedModuleGlobalSections_derivedTensor_of_forall_hom_eq_zero`, for `f : X ⟶ Spec A`
the `A`-linear `RΓ(X, C ⊗^𝐋 E)` vanishes. -/
theorem isZero_derivedGlobalSectionsOver_sheafDerivedTensor_of_forall_hom_eq_zero
    (f : X ⟶ Spec (CommRingCat.of A)) (C E : DerivedCategory (StructureSheafModules X.sheaf))
    (hE : (ringedSite X.sheaf).IsPerfect E)
    (hC : ∀ Q : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
        (StructureSheafModules X.sheaf) i).obj Q).IsQuasicoherent) →
        ∀ φ : Q ⟶ C, φ = 0) :
    IsZero ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj C).obj E)) :=
  (isZero_of_isZero_forget₂_mapDerivedCategory_obj
    ((isZero_derivedModuleGlobalSections_derivedTensor_of_forall_hom_eq_zero E C hE hC).of_iso
      ((Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedGlobalSectionsOverForgetIso f).app
        (((derivedTensor X.sheaf).obj E).obj C)))).of_iso
    ((derivedGlobalSectionsOver f).mapIso (derivedTensorBraidingIso C E))

/-- **Perfect twists of an object right orthogonal to `D_QCoh(𝒪_X)` have no derived global
sections.** Let `f : X ⟶ Spec A`, let `E` be a perfect object of `D(𝒪_X)` and let `C` be an
object of `D(𝒪_X)` such that every morphism `Q ⟶ C` from an object `Q` with quasi-coherent
cohomology sheaves is zero. Then `RΓ(X, C ⊗^𝐋 E) = 0` in `D(A)`, the derived tensor product being
the one of the projection formula. -/
theorem isZero_derivedGlobalSectionsOver_derivedTensor_of_forall_hom_eq_zero
    (f : X ⟶ Spec (CommRingCat.of A))
    (E C : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hC : ∀ Q : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj Q).IsQuasicoherent) →
        ∀ φ : Q ⟶ C, φ = 0) :
    IsZero ((derivedGlobalSectionsOver f).obj
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj C).obj E)) :=
  ((derivedGlobalSectionsOver f).mapIso
    (RingedSite.derivedTensorObjIso (ringedSite X.sheaf) _ E)).isZero_iff.1
      (isZero_derivedGlobalSectionsOver_sheafDerivedTensor_of_forall_hom_eq_zero f C E
        (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X.toRingedSpace E
          ((RingedSpace.isPerfect_iff_perfectComplexes_isPerfect E).1 hE)) hC)

end AlgebraicGeometry

end
