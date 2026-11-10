module

public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.ClosedImmersionPushforwardExact

/-!
# Closed subschemes of affine schemes with w-contractible global sections

A closed subscheme with quasi-compact open complement of an affine scheme with w-contractible
global sections has w-contractible global sections.

## Main results

* `AlgebraicGeometry.ProEtale.isWContractible_of_isClosedImmersion_of_isCompact_compl_range`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe u

namespace AlgebraicGeometry.ProEtale

/-- **A closed subscheme of an affine scheme with w-contractible ring of global sections whose
open complement is quasi-compact has w-contractible ring of global sections.**

Let `p : P ⟶ W` be a closed immersion into an affine scheme whose ring of global sections `R` is
w-contractible. Read on `Spec R`, `p` is the closed subscheme cut out by an ideal `I` of `R`, whose
zero locus is the image of `p`. If the complement of that image is quasi-compact, `R ⧸ I` is
w-contractible (`isWContractible_quotient_of_isCompact_compl_zeroLocus`), and it is the ring of
global sections of `P`. For instance a clopen subscheme of an affine scheme with w-contractible
global sections has w-contractible global sections. -/
theorem isWContractible_of_isClosedImmersion_of_isCompact_compl_range {P W : Scheme.{u}}
    (p : P ⟶ W) [IsClosedImmersion p] [IsAffine W] (hW : IsWContractible.{u, u} Γ(W, ⊤))
    (hcpt : IsCompact ((Set.range p.base)ᶜ)) : IsWContractible.{u, u} Γ(P, ⊤) := by
  -- Read the closed immersion off on `Spec Γ(W, ⊤)`.
  let eW : ↥W ≃ₜ ↥(Spec Γ(W, ⊤)) := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso W.isoSpec)
  obtain ⟨I, eP, hfac⟩ := (IsClosedImmersion.Spec_iff (f := p ≫ W.isoSpec.hom)).mp inferInstance
  have hrq : Set.range (p ≫ W.isoSpec.hom).base =
      (PrimeSpectrum.zeroLocus (I : Set ↥Γ(W, ⊤)) : Set ↥(Spec Γ(W, ⊤))) := by
    rw [hfac, Scheme.Hom.comp_base]
    change Set.range ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base ∘
      eP.hom.base) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr (by
      have _ : IsIso eP.hom.base := Scheme.forgetToTop.map_isIso eP.hom
      exact ((TopCat.isIso_iff_isHomeomorph _).mp inferInstance).surjective),
      Set.image_univ]
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    simp [Ideal.mk_ker]
  have himage : Set.range (p ≫ W.isoSpec.hom).base = eW '' Set.range p.base := by
    rw [Scheme.Hom.comp_base]
    change Set.range (eW ∘ p.base) = _
    rw [Set.range_comp]
  have hcptI : IsCompact ((PrimeSpectrum.zeroLocus (I : Set ↥Γ(W, ⊤)))ᶜ) := by
    have h : IsCompact (eW '' ((Set.range p.base)ᶜ)) := hcpt.image eW.continuous
    rwa [Homeomorph.image_compl, ← himage, hrq] at h
  -- The quotient of a w-contractible ring by such an ideal is w-contractible.
  let eRing : CommRingCat.of (↥Γ(W, ⊤) ⧸ I) ≅ Γ(P, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (↥Γ(W, ⊤) ⧸ I))).symm ≪≫ Scheme.Γ.mapIso eP.op
  exact isWContractible_of_ringEquiv eRing.commRingCatIsoToRingEquiv.symm
    (isWContractible_quotient_of_isCompact_compl_zeroLocus _ hW I hcptI)

end AlgebraicGeometry.ProEtale

end
