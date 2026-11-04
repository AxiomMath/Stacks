module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChartPunctured
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistLocalMap

/-!
# The degreewise inclusion `𝒪_P(m) ⟶ (π|_U)_* 𝒪_U` over a standard open

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`, and let `U ⊆ L` be the punctured cone.
For `f ∈ 𝒜 d` homogeneous of positive degree the part of `U` lying over the standard open `D₊(f)`
is the standard open `D₊(σ f · ψ f)` of `L`, so the sections of `(π|_U)_* 𝒪_U` over `D₊(f)` are the
degree-zero localization `(B[1/σ f · ψ f])₀`, and
`Stacks.Truncation.puncturedGradingEquivSectionsTwist` identifies its degree-`m` summand with the
sections of the twisting sheaf `𝒪_P(m)` over `D₊(f)`, for every integer `m`.

This file turns that identification into **a map of `Γ(P, D₊(f))`-modules**

  `Γ(D₊(f), 𝒪_P(m)) ⟶ Γ(D₊(f), (π|_U)_* 𝒪_U)`,

for every `m ∈ ℤ`, which is the local datum the gluing principle of [Stacks, Tag 009U] needs for
the punctured half `(π|_U)_* 𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)` of [Stacks, Tag 0EKG]. It is the punctured
analogue of `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedChartRestrict`: the restriction of the
  functions on `D₊(σ f · ψ f)` to the chart of `U` over `D₊(f)`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistAwayHom`: the degreewise inclusion
  `Γ(D₊(f), 𝒪_P(m)) →+ (B[1/σ f · ψ f])₀`, as an additive map.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistApp`: **the same map read into the
  sections of `(π|_U)_* 𝒪_U` over `D₊(f)`, as a morphism of modules over the sections of `𝒪_P`
  there.**

## Main results

* `Stacks.Truncation.puncturedToLocalization_degreeZeroRingMap`: the comparison maps
  `(B[1/σ f · ψ f])₀ → A[1/f]` and `(B[1/ψ f])₀ → A[1/f]` agree across the restriction map of `B`
  attached to `D₊(σ f · ψ f) ⊆ D₊(ψ f)`.
* `Stacks.Truncation.puncturedGradingEquivSectionsTwist_symm_smul`: **the degreewise inclusion is
  semilinear** for the chart description of `π|_U` on functions.
* `Stacks.Truncation.puncturedGradingEquivSectionsTwist_symm_degree_indep`: **it depends only on
  the standard open**, not on the degree in which `f` is homogeneous.
* `Stacks.AlgebraicGeometry.ProjConeTwist.openUInL_image_puncturedPi_preimage_basicOpen` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedPi_preimage_basicOpen`: the chart of `U` over
  `D₊(f)` is the inverse image of `D₊(σ f · ψ f)`, and its image in `L` is `D₊(σ f · ψ f)`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.awayToSection_puncturedPi_app`: **`π|_U` on functions
  over `D₊(f)`, in the form the direct image needs.**

## Implementation notes

The semilinearity is proved inside `A[1/f]`, where
`Stacks.Truncation.puncturedToLocalization` is a ring *isomorphism*
(`Stacks.Truncation.puncturedRingEquiv`) rather than merely injective as in the nonnegative case,
so every identity can be checked on fractions. The restriction map of `B` is handled exactly as in
`Stacks.Truncation.awayToLocalization_degreeZeroRingMap`: both composites into `A[1/f]` are ring
maps out of a localization of `B` at a power-submonoid, so `IsLocalization.ringHom_ext` reduces
the identity to the image of `B`, where each side is the structure map of `A[1/f]` applied to the
degree-forgetting image of the element.

The element cutting out the chart has two spellings, `Stacks.Truncation.sigmaMulPsi` and the
product `σ f · ψ f` of the fields of
`Stacks.AlgebraicGeometry.ProjAndSpec.ConeData`, and the chart description
`Stacks.AlgebraicGeometry.ProjAndSpec.puncturedAwayMap` is stated at the second. The two are
definitionally equal, which `puncturedAwayMap_eq_degreeZeroRingMap` records; every statement here
uses the first spelling, and the bridge is crossed once, by `exact` rather than by `rw`, inside
the proof of `awayToSection_puncturedPi_app`.

Two pieces of bookkeeping replace the transport of the nonnegative case. The chart of `U` over
`D₊(f)` is the inverse image of `D₊(σ f · ψ f)`, and the sections of `𝒪_U` over an open are by
definition the sections of `𝒪_L` over its image, so the restriction along the open immersion is a
morphism between the sections of `𝒪_L` over two opens that `Subsingleton.elim` identifies;
`openUInL_ι_appLE_eq_eqToHom` is that identification, and `puncturedPi_app_eq` says the transport
undoes the inequality of opens carried by `AlgebraicGeometry.Scheme.Hom.appLE`.

The restriction map is named, as `puncturedChartRestrict`, rather than written out: the local map
mentions it four times, and with it written out the elaborated definition is large enough that
`abstract nested proofs` exhausts the heartbeat budget. For the same reason the morphism of
modules is packaged with `CategoryTheory.ConcreteCategory.ofHom` at the two objects themselves
rather than with `ModuleCat.ofHom`, which asks instead for a definitional equality between those
objects and `ModuleCat.of` of their carriers, and whose check does not terminate here.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

namespace Stacks.Truncation

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

/-- `D₊(σ f · ψ f) ⊆ D₊(ψ f)`: the standard open of a product is contained in each factor's. -/
theorem basicOpen_sigmaMulPsi_le_psi :
    ProjectiveSpectrum.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f) ≤
      ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 f) := by
  rw [sigmaMulPsi]
  exact ProjectiveSpectrum.basicOpen_mul_le_right (grading 𝒜) _ _

/-- The comparison maps `(B[1/σ f · ψ f])₀ → A[1/f]` and `(B[1/ψ f])₀ → A[1/f]` agree across the
restriction map of `B` attached to `D₊(σ f · ψ f) ⊆ D₊(ψ f)`. -/
@[stacks 0EKG "the comparison maps (B[1/sigma f * psi f])_0 to A[1/f] and (B[1/psi f])_0 to \
A[1/f] agree across the degree-zero restriction map of B attached to D+(sigma f * psi f) <= \
D+(psi f)"]
theorem puncturedToLocalization_degreeZeroRingMap
    (hψf : ∃ e : ℕ, 0 < e ∧ psi 𝒜 f ∈ grading 𝒜 e)
    (hσψf : ∃ e : ℕ, 0 < e ∧ sigmaMulPsi 𝒜 f ∈ grading 𝒜 e)
    (hle : ProjectiveSpectrum.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f) ≤
      ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 f))
    (z : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) :
    puncturedToLocalization 𝒜
        (ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (psi 𝒜 f) (sigmaMulPsi 𝒜 f)
          hψf hσψf hle z) =
      awayToLocalization 𝒜 z := by
  set Lf : Localization.Away (psi 𝒜 f) →+* Localization.Away f :=
    Localization.awayLift ((algebraMap A (Localization.Away f)).comp (forgetDegree 𝒜))
      (psi 𝒜 f) (isUnit_iff_exists_inv.mpr ⟨awayFrac f 1 1, comp_psi_mul_awayFrac 𝒜⟩) with hLf
  set Lg : Localization.Away (sigmaMulPsi 𝒜 f) →+* Localization.Away f :=
    Localization.awayLift ((algebraMap A (Localization.Away f)).comp (forgetDegree 𝒜))
      (sigmaMulPsi 𝒜 f)
      (isUnit_iff_exists_inv.mpr ⟨awayFrac f 2 1, comp_sigmaMulPsi_mul_awayFrac 𝒜⟩) with hLg
  have hkey : Lg.comp
      (ProjectiveSpectrum.localizedRingMap (grading 𝒜) (psi 𝒜 f) (sigmaMulPsi 𝒜 f)
        hψf hσψf hle).toRingHom = Lf := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (psi 𝒜 f)) ?_
    refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [AlgHom.commutes, hLg, hLf, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
  have h := congrArg (fun φ : Localization.Away (psi 𝒜 f) →+* Localization.Away f => φ z.val) hkey
  simpa only [awayToLocalization, puncturedToLocalization, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, ProjectiveSpectrum.val_degreeZeroRingMap,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h

/-- The comparison map `(B[1/σ f · ψ f])₀ → A[1/f]` undoes the chart description of the punctured
cone projection, the map `A₍f₎ → B₍σ f · ψ f₎` of degree-zero localizations attached to `ψ`
followed by restriction. -/
@[stacks 0EKG "the comparison map (B[1/sigma f * psi f])_0 to A[1/f] undoes the chart \
description of the punctured cone projection on a standard open"]
theorem puncturedToLocalization_degreeZeroRingMap_map_psi (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (r : HomogeneousLocalization.Away 𝒜 f) :
    puncturedToLocalization 𝒜
        (ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (psi 𝒜 f) (sigmaMulPsi 𝒜 f)
          ⟨d, hd, GradedRingHom.map_mem (psi 𝒜) hf⟩ ⟨d, hd, sigmaMulPsi_mem_grading 𝒜 d hf⟩
          (basicOpen_sigmaMulPsi_le_psi 𝒜)
          (HomogeneousLocalization.Away.map (psi 𝒜) f r)) =
      r.val :=
  (puncturedToLocalization_degreeZeroRingMap 𝒜 ⟨d, hd, GradedRingHom.map_mem (psi 𝒜) hf⟩
        ⟨d, hd, sigmaMulPsi_mem_grading 𝒜 d hf⟩ (basicOpen_sigmaMulPsi_le_psi 𝒜)
        (HomogeneousLocalization.Away.map (psi 𝒜) f r)).trans
    (awayToLocalization_map_psi 𝒜 d hf r)

/-- The degreewise inclusion of `Γ(D₊(f), 𝒪_P(m))` into `(B[1/σ f · ψ f])₀`, read in `A[1/f]`, is
the standard-open description of the section it starts from. -/
theorem puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm (d : ℕ) (hf : f ∈ 𝒜 d)
    (hd : 0 < d) (m : ℤ)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    puncturedToLocalization 𝒜
        (((puncturedGradingEquivSectionsTwist 𝒜 d hf hd m).symm s :
          HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f))) =
      ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd m s :
        LocalizedModule.Away f A)) :=
  puncturedToLocalization_symm_apply 𝒜 d hf _

/-- **The degreewise inclusion `Γ(D₊(f), 𝒪_P(m)) → (B[1/σ f · ψ f])₀` is semilinear for the chart
description of the punctured cone projection**, the map `A₍f₎ → B₍σ f · ψ f₎` of degree-zero
localizations attached to `ψ` followed by restriction. Scaling a section of `𝒪_P(m)` by a
degree-zero fraction `r` multiplies its image by the image of `r`. -/
@[stacks 0EKG "the degreewise inclusion of the sections of O_P(m) over D+(f) into the \
degree-zero localization of the truncation algebra at sigma f * psi f is semilinear for the \
chart description of the punctured cone projection, for every integer m"]
theorem puncturedGradingEquivSectionsTwist_symm_smul (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (m : ℤ)
    (r : HomogeneousLocalization.Away 𝒜 f)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (((puncturedGradingEquivSectionsTwist 𝒜 d hf hd m).symm
          ((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).hom r • s) :
        HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f))) =
      ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (psi 𝒜 f) (sigmaMulPsi 𝒜 f)
          ⟨d, hd, GradedRingHom.map_mem (psi 𝒜) hf⟩ ⟨d, hd, sigmaMulPsi_mem_grading 𝒜 d hf⟩
          (basicOpen_sigmaMulPsi_le_psi 𝒜) (HomogeneousLocalization.Away.map (psi 𝒜) f r) *
        (((puncturedGradingEquivSectionsTwist 𝒜 d hf hd m).symm s :
          HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f))) := by
  refine puncturedToLocalization_injective 𝒜 d hf ?_
  rw [map_mul, puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm,
    puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm,
    puncturedToLocalization_degreeZeroRingMap_map_psi 𝒜 d hf hd,
    Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_smul]
  rfl

/-- **The punctured degreewise inclusion depends only on the standard open**, not on the degree
in which `f` is homogeneous. -/
@[stacks 0EKG "the punctured degreewise inclusion over one standard open depends only on that \
open, not on the degree of the element cutting it out"]
theorem puncturedGradingEquivSectionsTwist_symm_degree_indep {d d' : ℕ} (hf : f ∈ 𝒜 d)
    (hd : 0 < d) (hf' : f ∈ 𝒜 d') (hd' : 0 < d') (m : ℤ)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (((puncturedGradingEquivSectionsTwist 𝒜 d hf hd m).symm s :
        HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f))) =
      (((puncturedGradingEquivSectionsTwist 𝒜 d' hf' hd' m).symm s :
        HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f))) := by
  refine puncturedToLocalization_injective 𝒜 d hf ?_
  rw [puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm,
    puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm,
    Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading,
    Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading,
    associatedModuleSheafStandardOpenEquiv_degree_indep 𝒜 (twistGrading 𝒜 m) hf hd hf' hd' s]

end Stacks.Truncation

namespace Stacks.AlgebraicGeometry.ProjConeTwist

open Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjAndSpec (puncturedAwayMap)

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

attribute [local instance] Stacks.AlgebraicGeometry.ProjConeTwist.instTwistSectionsModule

alias instPuncturedTwistSectionsModule :=
  Stacks.AlgebraicGeometry.ProjConeTwist.instTwistSectionsModule

/-- The chart description of the punctured cone projection for the truncation algebra, with the
element `σ f · ψ f` named by `Stacks.Truncation.sigmaMulPsi`. -/
theorem puncturedAwayMap_eq_degreeZeroRingMap (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (r : HomogeneousLocalization.Away 𝒜 f) :
    (puncturedAwayMap (truncationConeData 𝒜) hd hf r :
        HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f)) =
      ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (psi 𝒜 f) (sigmaMulPsi 𝒜 f)
        ⟨d, hd, GradedRingHom.map_mem (psi 𝒜) hf⟩ ⟨d, hd, sigmaMulPsi_mem_grading 𝒜 d hf⟩
        (basicOpen_sigmaMulPsi_le_psi 𝒜) (HomogeneousLocalization.Away.map (psi 𝒜) f r) := rfl

/-- The inverse image of an open under the inclusion of an open subscheme recovers an open of the
subscheme from its image. -/
private theorem ι_preimage_ι_image {X : Scheme.{u}} (U : X.Opens) (W : U.toScheme.Opens) :
    U.ι ⁻¹ᵁ (U.ι ''ᵁ W) = W :=
  TopologicalSpace.Opens.ext (Set.ext fun _ => Scheme.Opens.mem_ι_image_iff U)

/-- **The image in `L` of the chart of `U` over `D₊(f)` is the standard open `D₊(σ f · ψ f)`.** -/
@[stacks 0EKG "the image in L of the chart of U over a standard open D+(f) is the standard \
open D+(sigma f * psi f), for the truncation cone"]
theorem openUInL_image_puncturedPi_preimage_basicOpen (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (openUInL 𝒜).ι ''ᵁ (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f) =
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f) := by
  rw [Scheme.Hom.comp_preimage, pi_preimage_basicOpen 𝒜 f d hf hd,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    openUInL_inf_basicOpen 𝒜 f d hf hd, sigmaMulPsi]

/-- **The chart of `U` over `D₊(f)` is the inverse image of `D₊(σ f · ψ f)`.** -/
@[stacks 0EKG "the chart of U over a standard open D+(f) is the inverse image of D+(sigma f * \
psi f) under the open immersion of U, for the truncation cone"]
theorem puncturedPi_preimage_basicOpen (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f =
      (openUInL 𝒜).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f) := by
  rw [← openUInL_image_puncturedPi_preimage_basicOpen 𝒜 d hf hd,
    ι_preimage_ι_image (openUInL 𝒜)]

/-- Transporting the sections over the chart back along
`(π|_U)⁻¹(D₊(f)) = U ∩ D₊(σ f · ψ f)` undoes the inequality of opens that
`AlgebraicGeometry.Scheme.Hom.appLE` carries. -/
theorem puncturedPi_app_eq (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    ((openUInL 𝒜).ι ≫ pi 𝒜).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
        ((openUInL 𝒜).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f))
        (puncturedPi_preimage_basicOpen 𝒜 d hf hd).ge ≫
      (openUInL 𝒜).toScheme.presheaf.map
        (eqToHom (puncturedPi_preimage_basicOpen 𝒜 d hf hd)).op =
      ((openUInL 𝒜).ι ≫ pi 𝒜).app (AlgebraicGeometry.Proj.basicOpen 𝒜 f) := by
  rw [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp,
    show ((homOfLE (puncturedPi_preimage_basicOpen 𝒜 d hf hd).ge).op ≫
        (eqToHom (puncturedPi_preimage_basicOpen 𝒜 d hf hd)).op) =
      CategoryStruct.id _ from Subsingleton.elim _ _]
  exact Category.comp_id _

/-- **The restriction of the functions on `D₊(σ f · ψ f)` to the chart of `U` over `D₊(f)`**,
along the open immersion of the punctured cone. The source is the whole standard open because
`D₊(σ f · ψ f)` already lies inside `U`, and the target is the sections of `(π|_U)_* 𝒪_U` over
`D₊(f)`. -/
def puncturedChartRestrict (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Γ(AlgebraicGeometry.Proj (grading 𝒜),
        AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f)) ⟶
      Γ((openUInL 𝒜).toScheme,
        ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f) :=
  (openUInL 𝒜).ι.appLE
    (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f))
    (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (puncturedPi_preimage_basicOpen 𝒜 d hf hd).le

/-- **The restriction along the open immersion of `U` from `D₊(σ f · ψ f)` to the chart of `U`
over `D₊(f)` is the identification of the sections of `(π|_U)_* 𝒪_U` over `D₊(f)` with the
functions on `D₊(σ f · ψ f)`.** Both are morphisms between the sections of `𝒪_L` over two opens
that the image identity of
`Stacks.AlgebraicGeometry.ProjConeTwist.openUInL_image_puncturedPi_preimage_basicOpen` shows to
be equal, and the opens of a space have at most one morphism between two of them. -/
theorem openUInL_ι_appLE_eq_eqToHom (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    puncturedChartRestrict 𝒜 d hf hd =
      eqToHom (puncturedConeAlgebra_sections_basicOpen 𝒜 d hf hd).symm := by
  rw [puncturedChartRestrict, Scheme.Opens.ι_appLE]
  refine Eq.trans (congrArg (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
    (Subsingleton.elim _
      (eqToHom (openUInL_image_puncturedPi_preimage_basicOpen 𝒜 d hf hd)).op)) ?_
  rw [CategoryTheory.eqToHom_op, CategoryTheory.eqToHom_map]
  rfl

/-- **The punctured cone projection on functions over a standard open, in the form the direct
image needs:** the image of a degree-zero fraction of `A` under the chart description
`puncturedAwayMap`, read as a function on `D₊(σ f · ψ f)` and restricted to the chart of `U` over
`D₊(f)`, is the pullback of that fraction along `π|_U`. -/
@[stacks 0EKG "the punctured cone projection on functions over a standard open, with the \
sections over D+(sigma f * psi f) restricted to the chart of U over D+(f)"]
theorem awayToSection_puncturedPi_app (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (r : HomogeneousLocalization.Away 𝒜 f) :
    (puncturedChartRestrict 𝒜 d hf hd).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom
          (ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (psi 𝒜 f) (sigmaMulPsi 𝒜 f)
            ⟨d, hd, GradedRingHom.map_mem (psi 𝒜) hf⟩
            ⟨d, hd, sigmaMulPsi_mem_grading 𝒜 d hf⟩ (basicOpen_sigmaMulPsi_le_psi 𝒜)
            (HomogeneousLocalization.Away.map (psi 𝒜) f r))) =
      (((openUInL 𝒜).ι ≫ pi 𝒜).app (AlgebraicGeometry.Proj.basicOpen 𝒜 f)).hom
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom r) := by
  rw [puncturedChartRestrict]
  have h2 := ConcreteCategory.congr_hom
    (Stacks.AlgebraicGeometry.ProjAndSpec.awayToSection_comp_puncturedPi_appLE
      (truncationConeData 𝒜) hd hf) r
  simp only at h2
  have h3 := ConcreteCategory.congr_hom (puncturedPi_app_eq 𝒜 d hf hd)
    ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom r)
  simp only [CommRingCat.comp_apply] at h3
  have h4 := fun x => ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_map (openUInL 𝒜).ι
      (U := AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f))
      (V := (openUInL 𝒜).ι ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f))
      le_rfl (eqToHom (puncturedPi_preimage_basicOpen 𝒜 d hf hd)).op) x
  simp only [CommRingCat.comp_apply] at h4
  exact (h4 _).symm.trans ((congrArg ((openUInL 𝒜).toScheme.presheaf.map
    (eqToHom (puncturedPi_preimage_basicOpen 𝒜 d hf hd)).op).hom h2.symm).trans h3)

/-- **The degreewise inclusion `Γ(D₊(f), 𝒪_P(m)) → (B[1/σ f · ψ f])₀`, as an additive map**, for
every integer `m`. It is the inverse of
`Stacks.Truncation.puncturedGradingEquivSectionsTwist` followed by the inclusion of the
degree-`m` summand. -/
@[stacks 0EKG "the degreewise inclusion of the sections of O_P(m) over D+(f) into the \
degree-zero localization of the truncation algebra at sigma f * psi f, as an additive map, for \
every integer m"]
def puncturedConeTwistAwayHom (m : ℤ) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    ((twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) →+
      HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f) :=
  (AddSubgroup.subtype (puncturedGrading 𝒜 d hf m)).comp
    (puncturedGradingEquivSectionsTwist 𝒜 d hf hd m).symm.toAddMonoidHom

/-- The degreewise inclusion sends a section to its preimage in the degree-`m` summand. -/
@[simp] theorem puncturedConeTwistAwayHom_apply (m : ℤ) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    puncturedConeTwistAwayHom 𝒜 m d hf hd s =
      (((puncturedGradingEquivSectionsTwist 𝒜 d hf hd m).symm s :
        HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f))) :=
  rfl

/-- **The local degreewise inclusion `Γ(D₊(f), 𝒪_P(m)) ⟶ Γ(D₊(f), (π|_U)_* 𝒪_U)`, as a morphism
of modules over the sections of `𝒪_P` on `D₊(f)`**, for every integer `m`. This is the local
datum from which the global morphism `𝒪_P(m) ⟶ (π|_U)_* 𝒪_U` is glued. -/
@[stacks 0EKG "the degreewise inclusion O_P(m) to (pi|_U)_* O_U over one standard open D+(f), \
as a map of modules over the sections of O_P there, for every integer m"]
def puncturedConeTwistApp (m : ℤ) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.obj
        (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f)) := by
  letI iN : Module (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
      ((Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.obj
        (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :=
    ((Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.obj
      (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))).isModule
  let L : ((twistingSheaf 𝒜 m).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f))) →ₗ[
      (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))]
      ((Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.obj
        (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :=
    { toFun := fun s =>
        (puncturedChartRestrict 𝒜 d hf hd).hom
          ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom
            (puncturedConeTwistAwayHom 𝒜 m d hf hd s))
      map_add' := by
        intro s t
        refine Eq.trans (congrArg (fun z =>
        (puncturedChartRestrict 𝒜 d hf hd).hom
            ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom z))
          (map_add (puncturedConeTwistAwayHom 𝒜 m d hf hd) s t)) ?_
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro r s
        obtain ⟨a, rfl⟩ := awayToSection_surjective 𝒜 hf hd r
        refine Eq.trans (congrArg (fun z =>
            (puncturedChartRestrict 𝒜 d hf hd).hom
            ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom z))
          (puncturedGradingEquivSectionsTwist_symm_smul 𝒜 d hf hd m a s)) ?_
        rw [map_mul, map_mul, awayToSection_puncturedPi_app 𝒜 d hf hd]
        rfl }
  exact ConcreteCategory.ofHom (C := ModuleCat _) L

/-- The components of the local punctured map. -/
theorem puncturedConeTwistApp_apply (m : ℤ) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (puncturedConeTwistApp 𝒜 m d hf hd).hom s =
        (puncturedChartRestrict 𝒜 d hf hd).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom
          (puncturedConeTwistAwayHom 𝒜 m d hf hd s)) :=
  rfl

end Stacks.AlgebraicGeometry.ProjConeTwist

end
