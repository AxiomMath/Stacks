module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceDirectImage.RelativeAffineCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceDirectImage.PseudoCoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceDirectImage.RelativeProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.Homology.PseudoCoherent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived direct image along a projective bundle preserves pseudo-coherence

Let `A` be a ring, let `X` be a scheme over `A` and let `p : X ×_A ℙᵐ_A ⟶ X` be the first
projection. For every pseudo-coherent object `F` of `D(𝒪_{X ×_A ℙᵐ_A})` the derived direct
image `Rp_*F` is pseudo-coherent. This is the pseudo-coherence half of [Stacks, Tag 0CSD] for the
flat proper morphism `p`, which is what the proof of [Stacks, Tag 0CSL] uses.

## Main results

* `AlgebraicGeometry.isPseudoCoherent_derivedPushforward_projectiveSpaceOver_spec`: the case of
  `ℙᵐ_R ⟶ Spec R`.
* `AlgebraicGeometry.isPseudoCoherent_derivedPushforward_fst_projectiveSpaceOver`: the general
  case.

## Proof

Over an affine base `Spec R`, `Rπ_*F` has quasi-coherent cohomology, its derived global sections
are `RΓ(ℙᵐ_R, F)` (Leray, [Stacks, Tag 0D5W]), which is a pseudo-coherent complex of `R`-modules
(`ProjectiveSpaceDirectImage.isPseudoCoherent_derivedGlobalSectionsOver_of_isPseudoCoherent`), and
an object of `D_QCoh(𝒪_{Spec R})` with pseudo-coherent derived global sections is pseudo-coherent
([Stacks, Tags 06Z0 and 08E7]). In general the statement is local on `X` ([Stacks, Tag 08FE]), and
over an affine open `W ≅ Spec R` of `X` the restriction of `p` is identified with `ℙᵐ_R ⟶ Spec R`
by the base change of projective space.

## References

* [Stacks Project, Tag 0CSD](https://stacks.math.columbia.edu/tag/0CSD)
* [Stacks Project, Tag 0CSL](https://stacks.math.columbia.edu/tag/0CSL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

open DerivedChow

variable (m : ℕ)

/-- **Derived direct image along `ℙᵐ_R ⟶ Spec R` preserves pseudo-coherence.** -/
@[sga "6 III 2.2.2" "more general"]
theorem isPseudoCoherent_derivedPushforward_projectiveSpaceOver_spec
    (R : CommRingCat.{u}) (F : DerivedCategory (projectiveSpaceOver m (Spec R)).Modules)
    (hF : RingedSpace.IsPseudoCoherent (X := (projectiveSpaceOver m (Spec R)).toRingedSpace) F) :
    RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace)
      ((derivedPushforward (ofScheme (projectiveSpaceOver m (Spec R) ↘ Spec R))).obj F) := by
  have hFq : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (projectiveSpaceOver m (Spec R)).Modules i).obj F).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent _ F hF
  have hq : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      ((derivedPushforward (ofScheme (projectiveSpaceOver m (Spec R) ↘ Spec R))).obj
        F)).IsQuasicoherent :=
    isQuasicoherent_homologyFunctor_derivedPushforward _ F hFq
  refine isPseudoCoherent_of_isPseudoCoherent_derivedGlobalSectionsOver_spec R _ hq ?_
  exact StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso
    (ProjectiveSpaceDirectImage.isPseudoCoherent_derivedGlobalSectionsOver_of_isPseudoCoherent
      (A := R) m F hF)
    ((derivedGlobalSectionsOverPushforwardIso (projectiveSpaceOver m (Spec R) ↘ Spec R)).app F)

/-- **[Stacks, Tag 0CSD], pseudo-coherence half, for a projective bundle over a scheme over
`A`.** For `f : X ⟶ Spec A` and a pseudo-coherent object `F` of `D(𝒪_{X ×_A ℙᵐ_A})`, the
derived direct image of `F` along the first projection `X ×_A ℙᵐ_A ⟶ X` is pseudo-coherent. No
hypothesis on `f` is needed. -/
@[sga "6 III 2.2.2" "more general"]
theorem isPseudoCoherent_derivedPushforward_fst_projectiveSpaceOver
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (F : DerivedCategory (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).Modules)
    (hF : RingedSpace.IsPseudoCoherent
      (X := (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).toRingedSpace) F) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace)
      ((derivedPushforward (ofScheme (pullback.fst f
        (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))))).obj F) := by
  refine isPseudoCoherent_derivedPushforward_of_local _ (fun x => ?_) F hF
  set πA := projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)
  set p := pullback.fst f πA
  set q := pullback.snd f πA
  obtain ⟨⟨W, hW⟩, hxW⟩ : ∃ W : X.affineOpens, x ∈ (W : X.Opens) := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨W, hW⟩, hxW⟩
  refine ⟨W, hxW, fun F' hF' => ?_⟩
  set R : CommRingCat.{u} := Γ(X, W)
  set h : W.toScheme ≅ Spec R := hW.isoSpec
  set g : Spec R ⟶ Spec (.of A) := h.inv ≫ W.ι ≫ f
  set e' := projectiveSpaceOverBaseChangeIso m g
  have H1 : IsPullback ((p ⁻¹ᵁ W).ι ≫ q) (p ∣_ W) πA (W.ι ≫ f) :=
    (isPullback_morphismRestrict p W).flip.paste_horiz
      (IsPullback.of_hasPullback f πA).flip
  have H2 : IsPullback (e'.inv ≫ pullback.fst πA g)
      ((projectiveSpaceOver m (Spec R) ↘ Spec R) ≫ h.inv) πA (W.ι ≫ f) :=
    (IsPullback.of_hasPullback πA g).of_iso e' (Iso.refl _) h.symm (Iso.refl _)
      (by simp) (by rw [← Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over]; rfl) (by simp)
      (by simp [g])
  set e := H1.isoIsPullback _ _ H2
  have he : e.hom ≫ ((projectiveSpaceOver m (Spec R) ↘ Spec R) ≫ h.inv) = p ∣_ W :=
    H1.isoIsPullback_hom_snd _ _ H2
  refine isPseudoCoherent_derivedPushforward_of_iso (p ∣_ W)
    (projectiveSpaceOver m (Spec R) ↘ Spec R) e h ?_
    (isPseudoCoherent_derivedPushforward_projectiveSpaceOver_spec m R) F' hF'
  rw [← he]
  simp

end AlgebraicGeometry

end
