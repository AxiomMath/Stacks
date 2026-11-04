module

public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentDetectedByGlobalSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.PseudoCoherentByPseudoCoherentTwists
public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundednessGenerator
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.AlgebraicGeometry.Perfect.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.DerivedSectionsTensorPseudoCoherence

/-!
# Relative pseudo-coherence from perfect twists of the derived global sections

Let `A` be a ring, let `X` be a scheme separated and of finite presentation over `A` and let
`K ∈ D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent in `D(A)` for every perfect `E` in
`D(𝒪_X)`, then `K` is pseudo-coherent relative to `A` ([Stacks, Tag 0GES]).

## The proof

The source's, in three steps.

* `K ∈ D^-_QCoh(𝒪_X)`: with a perfect generator `G` of `D_QCoh(𝒪_X)` ([Stacks, Tag 09IS],
  `Stacks.SheafOfModules.exists_isPerfect_generator`), the hypothesis at the perfect object `G^∨`
  makes `H^i(X, G^∨ ⊗^𝐋 K)` vanish for `i ≫ 0`, and [Stacks, Tag 0GEN] concludes
  (`AlgebraicGeometry.exists_isZero_homology_of_derivedGlobalSectionsOver_isPseudoCoherent`).
* [Stacks, Tag 0CSH] upgrades the hypothesis from perfect to pseudo-coherent `E`.
* [Stacks, Tag 0CSL] concludes
  (`AlgebraicGeometry.isPseudoCoherent_of_derivedGlobalSectionsOver_tensor_isPseudoCoherent`).

## Implementation notes

"Perfect" is the ringed-space notion `Stacks.Cohomology.PerfectComplexes.IsPerfect` of
[Stacks, Tag 08CM], which is the source's; the ringed-site notion used by Stacks 0GEN and 09IS is
equivalent to it (`Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite`).

## References

* [Stacks Project, Lemma 37.69.5 (Tag 0GES)](https://stacks.math.columbia.edu/tag/0GES)
* [Stacks Project, Tag 0CSL](https://stacks.math.columbia.edu/tag/0CSL)
* [Stacks Project, Tag 0CSH](https://stacks.math.columbia.edu/tag/0CSH)
* [Stacks Project, Tag 0GEN](https://stacks.math.columbia.edu/tag/0GEN)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The derived tensor product of `D(𝒪_X)` in the spelling of `Stacks.SheafOfModules.derivedTensor`
is symmetric. -/
def derivedTensorBraidingIso (E K : DerivedCategory (StructureSheafModules X.sheaf)) :
    ((derivedTensor X.sheaf).obj E).obj K ≅ ((derivedTensor X.sheaf).obj K).obj E :=
  RingedSite.derivedTensorObjIso (Stacks.SheafOfModules.ringedSite X.sheaf) E K ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).braidingIso
      (Stacks.RingedSpace.toRingedSite X.toRingedSpace) E K ≪≫
    Iso.symm (C := DerivedCategory (StructureSheafModules X.sheaf))
      (RingedSite.derivedTensorObjIso (Stacks.SheafOfModules.ringedSite X.sheaf) K E)

/-- **Boundedness above from the perfect twists.** Let `f : X ⟶ Spec A` be quasi-compact and
quasi-separated, let `G` be a perfect generator of `D_QCoh(𝒪_X)` and let `K ∈ D_QCoh(𝒪_X)`. If
`RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent in `D(A)` for every perfect `E`, then `K ∈ D^-_QCoh(𝒪_X)`.
This is the second step of the source proof of Stacks 0GES: the hypothesis makes
`H^i(X, G^∨ ⊗^𝐋 K)` vanish for `i ≫ 0`, which is condition (5) of Stacks 0GEN, and that
proposition's implication to condition (1) concludes. -/
theorem exists_isZero_homology_of_derivedGlobalSectionsOver_isPseudoCoherent
    (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [QuasiSeparated f]
    (G K : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (hgen : ∀ L : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj L).IsQuasicoherent) →
        (∀ (n : ℤ) (g : G⟦n⟧ ⟶ L), g = 0) → IsZero L)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent)
    (hpc : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj E).obj K))) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj K) := by
  have hqc : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hqs : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hpc' : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      (ringedSite X.sheaf).IsPerfect E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj K).obj E)) :=
    fun E hE => StacksDraft.PseudoCoherence.IsPseudoCoherent.of_iso
      (hpc E (Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace E hE))
      ((derivedGlobalSectionsOver f).mapIso (derivedTensorBraidingIso E K))
  obtain ⟨-, hhom⟩ := eventually_subsingleton_ext_of_derivedGlobalSections_isPseudoCoherent
    f hqc hqs G K hG hgen hK hpc'
  have hmin := minus_of_eventually_subsingleton_shiftedHom hqc hqs G K hG hgen hK hhom
  obtain ⟨b, hb⟩ := (DerivedCategory.minus_iff K).1 hmin
  exact ⟨b, fun i hi => hb i hi.le⟩

/-- **[Stacks, Tag 0GES].** Let `A` be a ring, let `X` be a scheme separated and of finite
presentation over `A`, with structure morphism `f : X ⟶ Spec A`, and let `K ∈ D_QCoh(𝒪_X)`. If
`RΓ(X, E ⊗^𝐋 K)` is a pseudo-coherent object of `D(A)` for every perfect object `E` of
`D(𝒪_X)`, then `K` is pseudo-coherent relative to `A`. -/
@[stacks 0GES]
theorem isPseudoCoherent_of_derivedGlobalSectionsOver_tensor_isPerfect
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [QuasiCompact f]
    [LocallyOfFinitePresentation f]
    (K : DerivedCategory (StructureSheafModules X.sheaf))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent)
    (hpc : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj E).obj K))) :
    f.IsPseudoCoherent K := by
  have hqc : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hqs : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨G, hG, hgen⟩ := exists_isPerfect_generator hqc hqs
  have hKb := exists_isZero_homology_of_derivedGlobalSectionsOver_isPseudoCoherent f G K hG hgen
    hK hpc
  have h0CSH : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj E).obj K)) :=
    fun E hE => by
      have := hqc
      have := hqs
      exact isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent f K hK hKb hpc E
        hE
  exact isPseudoCoherent_of_derivedGlobalSectionsOver_tensor_isPseudoCoherent f K hK h0CSH

end AlgebraicGeometry

end
