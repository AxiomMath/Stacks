module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatLocusAdicThickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport

/-!
# Flatness over a local base from flatness over its thickenings

Let `A` be a Noetherian local ring, `I ⊆ 𝔪` an ideal, `X ⟶ Spec A` a morphism of algebraic spaces
locally of finite presentation and `F` a coherent `𝒪_X`-module with support proper over
`Spec A`.  If the restrictions of `F` to the adic fibres `Spec(A/I^{n+1}) ×_{Spec A} X` are flat
over `Spec(A/I^{n+1})`, then `F` is flat over `Spec A`
(`AlgebraicGeometry.Space.isFlatOver_of_isFlatOver_adicFibres`).

This is the step of the proof of Stacks 08W9 after Stacks 08VP: the latter makes the flat locus
open and puts the points over the closed point in it; its complement is closed and contained in
the support, so its image in `Spec A` is closed (Stacks 0CZG), and a nonempty closed subset of
the spectrum of a local ring contains the closed point.

## References

* [Stacks Project, Tag 08VP](https://stacks.math.columbia.edu/tag/08VP)
* [Stacks Project, Tag 08W9](https://stacks.math.columbia.edu/tag/08W9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-- **Flatness over a local base from flatness over its thickenings.** -/
theorem isFlatOver_of_isFlatOver_adicFibres [IsNoetherianRing A] [IsLocalRing A] (I : Ideal A)
    (hI : I ≤ maximalIdeal A) (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFinitePresentation B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [hF : IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (hflat : ∀ n : ℕ, IsFlatOver B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f n).2
      (adicFibreProjection A I B hA X f n).hom
      ((modulePullback B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f n)).obj F))
    (hp : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (Spec (.of A)) hA hf)
      ((SheafOfModules.toSheaf _).obj F)) :
    IsFlatOver B (Spec (.of A)) hA X.2 f.hom F := by
  have hqc : F.IsQuasicoherentOnSite := hF.toIsQuasicoherentOnSite
  have hlft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (Spec (.of A)) hA hf
  obtain ⟨hopen, hsub⟩ := isOpen_flatLocus_and_preimage_subset_flatLocus A I B hA X f hf F hflat
  suffices hall : ∀ x, x ∈ flatLocus B (Spec (.of A)) hA X.2 f.hom F by
    exact (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B (Spec (.of A)) hA f F).mpr fun xbar =>
      (mem_flatLocus_iff_isFlatOverAtGeometricPoint B (Spec (.of A)) hA f F xbar).1 (hall _)
  by_contra! hne
  obtain ⟨x₀, hx₀⟩ := hne
  let C := (flatLocus B (Spec (.of A)) hA X.2 f.hom F)ᶜ
  have hCcl : IsClosed C := hopen.isClosed_compl
  obtain ⟨hScl, hSp⟩ := hp
  have hCsupp : C ⊆ supportOfSheaf B (Spec (.of A)) hA X.1 ((SheafOfModules.toSheaf _).obj F) := by
    intro y hy
    by_contra hys
    apply hy
    obtain ⟨ybar, rfl⟩ := exists_geometricRepresentative B (Spec (.of A)) hA X.1 y
    exact (mem_flatLocus_iff_isFlatOverAtGeometricPoint B (Spec (.of A)) hA f F ybar).2
      (isFlatOverAtGeometricPoint_of_subsingleton_geometricModuleStalk B (Spec (.of A)) hA f F ybar
        (not_nontrivial_iff_subsingleton.mp fun hn => hys
          ((mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver
            B (Spec (.of A)) hA X F ybar _ rfl).2 hn)))
  have hCp := isProperOver_of_subset B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
    f.hom hlft C _ hCcl hScl hCsupp hSp
  have hid : IsLocallyOfFiniteType B (Spec (.of A)) hA (𝟙 (schemeSpace (baseObject A B hA)).1) :=
    isLocallyOfFiniteType_of_isClosedImmersion B (Spec (.of A)) hA _
      (isClosedImmersion_of_isIso B (Spec (.of A)) hA _)
  have himg := isClosed_image_of_isProperOver B (Spec (.of A)) hA X.2
    (schemeSpace (baseObject A B hA)).2 (schemeSpace (baseObject A B hA)).2 f.hom f.hom (𝟙 _)
    (Category.comp_id _) hlft hid (isSeparated_of_isIso B (Spec (.of A)) hA _) C hCcl hCp
  have hZ := (schemePointsHomeomorph B (Spec (.of A)) hA (baseObject A B hA)).isClosedMap _ himg
  obtain ⟨_, ⟨c, hc, rfl⟩, hcc⟩ :=
    (specializes_closedPoint _).mem_closed hZ ⟨_, ⟨x₀, hx₀, rfl⟩, rfl⟩
  obtain ⟨q, hq⟩ : closedPoint A ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (I ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact fun a ha => hI (by simpa using ha)
  obtain ⟨w, hw⟩ := (bijective_pointsToScheme B (Spec (.of A)) hA
    (adicThickeningObject A I B hA (contains_adicThickening A I B hA) 0)).2 q
  have hmem : pointsMap B (Spec (.of A)) hA X.1 f.hom c ∈ Set.range (pointsMap B (Spec (.of A)) hA
      (yoneda.obj (adicThickeningObject A I B hA (contains_adicThickening A I B hA) 0))
      (yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) 0))) := by
    refine ⟨w, (bijective_pointsToScheme B (Spec (.of A)) hA (baseObject A B hA)).1 ?_⟩
    rw [pointsToScheme_pointsMap_yoneda, hw]
    refine Eq.trans ?_ hcc.symm
    rw [← hq]
    rfl
  exact hc (hsub hmem)

end AlgebraicGeometry.Space

end
