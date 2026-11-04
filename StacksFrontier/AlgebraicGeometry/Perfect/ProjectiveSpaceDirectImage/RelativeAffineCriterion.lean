module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeCounit
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence
public import StacksFrontier.Homology.PseudoCoherentRelative.TildePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative

/-!
# Pseudo-coherence on an affine scheme from the derived global sections

Let `R` be a ring and let `E` be an object of `D_QCoh(𝒪_{Spec R})`. If the `R`-linear derived
global sections `RΓ(Spec R, E)` form a pseudo-coherent object of `D(R)`, then `E` is a
pseudo-coherent object of `D(𝒪_{Spec R})`.

This is the direction from modules to sheaves of [Stacks, Tag 08E7], read through the
equivalence `D(R) ≌ D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 06Z0]: the counit of the derived
sheafification–sections adjunction identifies `E` with the derived sheafification of
`RΓ(Spec R, E)`, and the derived sheafification of a complex of `R`-modules is the termwise
sheafification of that complex.

## Main results

* `AlgebraicGeometry.isPseudoCoherent_of_isPseudoCoherent_derivedGlobalSectionsOver_spec`.

## References

* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **Pseudo-coherence on `Spec R` is detected by the derived global sections.** An object `E`
of `D(𝒪_{Spec R})` with quasi-coherent cohomology whose `R`-linear derived global sections are
pseudo-coherent in `D(R)` is pseudo-coherent.

By [Stacks, Tag 06Z0] (`derivedTildeGlobalSectionsAdjunction_counit_isIso`) `E` is the derived
sheafification of `RΓ(Spec R, E)`; representing the latter by a bounded above complex `N` of
finite free modules, `E` is isomorphic to the termwise sheafification of `N`, which is
pseudo-coherent by [Stacks, Tag 08E7]. -/
theorem isPseudoCoherent_of_isPseudoCoherent_derivedGlobalSectionsOver_spec
    (R : CommRingCat.{u}) (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).IsQuasicoherent)
    (h : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj E)) :
    RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace) E := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  have hcounit := derivedTildeGlobalSectionsAdjunction_counit_isIso R ⟨E, hE⟩
  have hpc : RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace)
      (DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex N)) :=
    Stacks.AffineTilde.isPseudoCoherent_tildeComplex N ⟨N, hN, ⟨Iso.refl _⟩⟩
  refine RingedSpace.IsPseudoCoherent.of_iso (X := (Spec R).toRingedSpace) hpc ?_
  exact ((derivedTildeFactors R).app N).symm ≪≫
    (derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι).mapIso e ≪≫
    @asIso _ _ _ _ ((derivedTildeGlobalSectionsAdjunction R).val.counit.app E) hcounit

end AlgebraicGeometry

end
