module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleMonoClosedFibre
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPairDepthFree
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTorsionFreeTensor
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.UnitHom

/-!
# Nonvanishing of section pairs at global sections

For a section pair `(x, x₀)` of an invertible triple `L`, given by global sections
`x : Γ(L.F, ⊤)` and `x₀ : Γ(L.F₀, ⊤)` corresponding under
`Stacks.Algebraization.globalSectionsMap`, the monicity and `f`-torsion-freeness of
multiplication by the section pair, with the nonvanishing of `x` expressed through the open
`Stacks.NonvanishingOpen.nonvanishingOpen` on the punctured spectrum, or through associated
points and inverse images on the punctured closed fibre.

## Main results

* `CoherentTriple.mono_onPunctured_mulSectionTwistZOfGlobalSections`: the punctured-spectrum
  member of multiplication by a section pair is a monomorphism when `x` does not vanish on
  `Ass(T.F)`.
* `CoherentTriple.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZOfGlobalSections`: its
  cokernel is `f`-torsion-free when `x` does not vanish on `Ass(T.F / f T.F)`.
* `exists_sectionPair_mono_onPunctured_and_isFTorsionFree`: for a Noetherian local ring, an
  `f ∈ 𝔪` and any triple `T`, there is a section pair whose multiplication map on the punctured
  spectrum is a monomorphism with `f`-torsion-free cokernel.
* `preimage_nonvanishingLocus_of_eq_globalSectionsMap`: the two sections of a section pair have
  the same nonvanishing locus over the punctured closed fibre.
* `forall_exists_opens_nonvanishingLocus_closedFibre_of_preimage`: points of the closed fibre
  other than the closed point lying over points where `x` does not vanish have open
  neighbourhoods in the nonvanishing locus of `x₀`.
* `CoherentTriple.mono_onClosedFibre_mulSectionTwistZOfGlobalSections_quotientTriple`: the
  closed-fibre member of multiplication by a section pair on the quotient triple is a
  monomorphism when every associated point of its closed-fibre member in the punctured closed
  fibre lies over a point where `x` does not vanish.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.AlgebraicGeometry.PrincipalIdealExtension (smulPowHom)
open Stacks.RelativeVeryAmple (tensorModules)

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}

/-! ### Monicity and torsion-freeness on the punctured spectrum -/

/-- The punctured-spectrum member of multiplication by a section pair `(x, x₀)` is a
monomorphism, provided `Ass(T.F)` is contained in the nonvanishing open
`Stacks.NonvanishingOpen.nonvanishingOpen` of `x`. -/
public theorem CoherentTriple.mono_onPunctured_mulSectionTwistZOfGlobalSections
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
    (hx : globalSectionsMap A f L x =
      pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀)
    (n : ℤ) {N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    (hq : ((T.twistZ L hL n).F).IsQuasicoherent)
    (hq' : (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
      ((T.twistZ L hL n).F) L.F).IsQuasicoherent)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).presheaf,
          (((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).IsSheaf⟩).obj
        (L.F)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (hnv : letI := hL.invertible_F
      Stacks.Divisors.associatedPoints T.F ⊆
        (Stacks.NonvanishingOpen.nonvanishingOpen
          (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x : Set _)) :
    Mono (T.mulSectionTwistZOfGlobalSections L hL x x₀ hx n).onPunctured :=
  have := hL.invertible_F
  T.mono_onPunctured_mulSectionTwistZ L hL (Scheme.Modules.unitHomEquivTop L.F x)
    (Scheme.Modules.unitHomEquivTop L.F₀ x₀) (hcompat_of_eq_globalSectionsMap x x₀ hx) n hq hq' ψ
    (Stacks.NonvanishingSpelling.forall_exists_opens_mem_stalkNonvanishingLocus_unitHomEquivTop
      (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x hnv)

/-- The cokernel of the punctured-spectrum member of multiplication by a section pair `(x, x₀)`
is `f`-torsion-free, provided that member is a monomorphism and `Ass(T.F / f T.F)` is contained
in the nonvanishing open `Stacks.NonvanishingOpen.nonvanishingOpen` of `x`. -/
public theorem CoherentTriple.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZOfGlobalSections
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
    (hx : globalSectionsMap A f L x =
      pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀)
    (n : ℤ) (hmonoφ : Mono (T.mulSectionTwistZOfGlobalSections L hL x x₀ hx n).onPunctured)
    {N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    (hq : letI := hL.invertible_F
      (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (cokernel (smulPowHom T.F (scalarGlobal A f) 1))
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).IsQuasicoherent)
    (hq' : letI := hL.invertible_F
      (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
          (cokernel (smulPowHom T.F (scalarGlobal A f) 1))
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n))
        L.F).IsQuasicoherent)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).presheaf,
          (((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).IsSheaf⟩).obj
        (L.F)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (hnv : letI := hL.invertible_F
      Stacks.Divisors.associatedPoints (cokernel (smulPowHom T.F (scalarGlobal A f) 1)) ⊆
        (Stacks.NonvanishingOpen.nonvanishingOpen
          (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x : Set _)) :
    IsFTorsionFree A f
      (cokernel (T.mulSectionTwistZOfGlobalSections L hL x x₀ hx n).onPunctured) :=
  have := hL.invertible_F
  T.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZ_of_nonvanishing L hL
    (Scheme.Modules.unitHomEquivTop L.F x) (Scheme.Modules.unitHomEquivTop L.F₀ x₀)
    (hcompat_of_eq_globalSectionsMap x x₀ hx) n hmonoφ hq hq' ψ
    (Stacks.NonvanishingSpelling.forall_exists_opens_mem_stalkNonvanishingLocus_unitHomEquivTop
      (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x hnv)

/-! ### Existence of a section pair -/

/-- For a Noetherian local ring `A`, an `f ∈ 𝔪`, an invertible triple `L` and any triple `T`,
there is a section pair of `L` whose multiplication map on the punctured spectrum is a
monomorphism with `f`-torsion-free cokernel, given quasi-coherence of the tensor products
involved and a trivialization `ψ` of `L.F`. -/
public theorem exists_sectionPair_mono_onPunctured_and_isFTorsionFree
    (hf : f ∈ maximalIdeal A) {L : CoherentTriple A f} (hL : IsInvertibleTriple L)
    (T : CoherentTriple A f) (n : ℤ)
    {N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).presheaf,
          (((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).IsSheaf⟩).obj
        (L.F)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (hq : ((T.twistZ L hL n).F).IsQuasicoherent)
    (hq' : (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
      ((T.twistZ L hL n).F) L.F).IsQuasicoherent)
    (hqc : letI := hL.invertible_F
      (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (cokernel (smulPowHom T.F (scalarGlobal A f) 1))
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).IsQuasicoherent)
    (hqc' : letI := hL.invertible_F
      (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
          (cokernel (smulPowHom T.F (scalarGlobal A f) 1))
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n))
        L.F).IsQuasicoherent) :
    ∃ (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
      (hx : globalSectionsMap A f L x =
        pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀),
      Mono (T.mulSectionTwistZOfGlobalSections L hL x x₀ hx n).onPunctured ∧
        IsFTorsionFree A f
          (cokernel (T.mulSectionTwistZOfGlobalSections L hL x x₀ hx n).onPunctured) := by
  let := hL.invertible_F
  obtain ⟨x, x₀, hx, hnv⟩ :=
    exists_sectionPair_nonvanishing_on_associatedPoints_depthFree hf hL T
  obtain ⟨hnvF, hnvQ⟩ := Set.union_subset_iff.mp hnv
  have hmono := T.mono_onPunctured_mulSectionTwistZOfGlobalSections L hL x x₀ hx n hq hq' ψ hnvF
  exact ⟨x, x₀, hx, hmono,
    T.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZOfGlobalSections L hL x x₀ hx n hmono
      hqc hqc' ψ hnvQ⟩

/-! ### Nonvanishing over the closed fibre -/

omit [IsNoetherianRing A] in
/-- If `x` and `x₀` correspond under `Stacks.Algebraization.globalSectionsMap`, then a point of
the punctured closed fibre lies over a point of the punctured spectrum where `x` does not vanish
exactly when `x₀` does not vanish at its image in the closed fibre. -/
public theorem preimage_nonvanishingLocus_of_eq_globalSectionsMap (L : CoherentTriple A f)
    (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
    (hx : globalSectionsMap A f L x =
      pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀) :
    (puncturedClosedFibreRestriction A f).base ⁻¹' Stacks.Ample.nonvanishingLocus L.F x =
      (puncturedClosedFibre A f).ι.base ⁻¹' Stacks.Ample.nonvanishingLocus L.F₀ x₀ := by
  rw [Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections,
    Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections,
    ← Stacks.Ample.nonvanishingLocus_congr L.alpha
      (pullbackGlobalSections (puncturedClosedFibreRestriction A f) L.F x)]
  exact congrArg (Stacks.Ample.nonvanishingLocus _) hx

omit [IsNoetherianRing A] in
/-- Let `x` and `x₀` correspond under `Stacks.Algebraization.globalSectionsMap`, and let `S` be
a set of points of the closed fibre such that every point of `S` in the punctured closed fibre
lies over a point of the punctured spectrum where `x` does not vanish. Then every point of `S`
other than the closed point has an open neighbourhood contained in the nonvanishing locus of the
section of `L.F₀` given by `x₀`. -/
public theorem forall_exists_opens_nonvanishingLocus_closedFibre_of_preimage
    [IsLocalRing (A ⧸ Ideal.span {f})] {L : CoherentTriple A f} (hL : IsInvertibleTriple L)
    (hf : f ∈ maximalIdeal A) (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
    (hx : globalSectionsMap A f L x =
      pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀)
    (S : Set (closedFibre A f))
    (hS : letI := hL.invertible_F
      ∀ p ∈ S, ∀ hp : p ∈ puncturedClosedFibre A f,
        (puncturedClosedFibreRestriction A f).base ⟨p, hp⟩ ∈
          Stacks.Ample.nonvanishingLocus L.F x) :
    letI := hL.invertible_F₀
    ∀ p ∈ S, p ≠ IsLocalRing.closedPoint (A ⧸ Ideal.span {f}) →
      ∃ W : (closedFibre A f).Opens, p ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (closedFibre A f).toRingedSpace) L.F₀
          (L.F₀.unitHomEquiv (Scheme.Modules.unitHomEquivTop L.F₀ x₀)) := by
  let := hL.invertible_F
  let := hL.invertible_F₀
  intro p hp hpc
  have hmem : p ∈ puncturedClosedFibre A f := by
    rw [puncturedClosedFibre_eq_puncturedSpectrum A f hf]
    exact hpc
  have hnv : (⟨p, hmem⟩ : (puncturedClosedFibre A f).toScheme) ∈
      (puncturedClosedFibre A f).ι.base ⁻¹' Stacks.Ample.nonvanishingLocus L.F₀ x₀ := by
    rw [← preimage_nonvanishingLocus_of_eq_globalSectionsMap L x x₀ hx]
    exact hS p hp hmem
  refine Stacks.NonvanishingSpelling.forall_exists_opens_mem_stalkNonvanishingLocus_unitHomEquivTop
    (closedFibre A f) L.F₀ x₀ (S := {p}) ?_ p rfl
  exact Set.singleton_subset_iff.mpr hnv

/-- For the quotient triple `T.quotientTriple hf`, the closed-fibre member of multiplication by a
section pair `(x, x₀)` is a monomorphism, provided every associated point of
`(T.quotientTriple hf).F₀` in the punctured closed fibre lies over a point of the punctured
spectrum where `x` does not vanish. -/
public theorem CoherentTriple.mono_onClosedFibre_mulSectionTwistZOfGlobalSections_quotientTriple
    [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A) (T L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
    (hx : globalSectionsMap A f L x =
      pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀)
    (n : ℤ) {N₀ : (closedFibre A f).Modules}
    (hq : (((T.quotientTriple hf).twistZ L hL n).F₀).IsQuasicoherent)
    (hq' : (tensorModules (closedFibre A f)
      (((T.quotientTriple hf).twistZ L hL n).F₀) L.F₀).IsQuasicoherent)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((closedFibre A f).toRingedSpace)).presheaf,
          (((closedFibre A f).toRingedSpace)).IsSheaf⟩).obj (L.F₀)).obj (N₀)) ≅
      _root_.SheafOfModules.unit _)
    (hass : letI := hL.invertible_F
      ∀ p ∈ Stacks.Divisors.associatedPoints (T.quotientTriple hf).F₀,
        ∀ hp : p ∈ puncturedClosedFibre A f,
          (puncturedClosedFibreRestriction A f).base ⟨p, hp⟩ ∈
            Stacks.Ample.nonvanishingLocus L.F x) :
    Mono ((T.quotientTriple hf).mulSectionTwistZOfGlobalSections L hL x x₀ hx n).onClosedFibre :=
  T.mono_onClosedFibre_mulSectionTwistZ_quotientTriple hf L hL
    (Scheme.Modules.unitHomEquivTop L.F x) (Scheme.Modules.unitHomEquivTop L.F₀ x₀)
    (hcompat_of_eq_globalSectionsMap x x₀ hx) n hq hq' ψ
    (forall_exists_opens_nonvanishingLocus_closedFibre_of_preimage hL hf x x₀ hx
      (Stacks.Divisors.associatedPoints (T.quotientTriple hf).F₀) hass)

end Stacks.Algebraization

end
