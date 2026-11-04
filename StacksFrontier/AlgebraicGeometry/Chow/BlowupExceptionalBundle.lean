module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.SituationTower
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic

/-!
# The exceptional divisor of a blowup in a smooth centre is a projective tower, with `𝒪(-E)|_E`

Let `i : Z ⟶ X` be a closed immersion of schemes smooth over a base `S`, `b : X' ⟶ X` the blowing
up of `X` in the ideal sheaf of `i` (`Stacks.Blowup.blowUp`, the presentation the blow up formula
of Stacks 0FVA is stated for), `E = X' ×_X Z` with `j : E ⟶ X'` and `π : E ⟶ Z`. If the conormal
sheaf `ℐ/ℐ²` of the centre is finite locally free of rank `n + 1`, then

  `(π, j^*ℐ_E)` is a projective tower of fibre dimension `n` locally on `Z`,

where `ℐ_E = 𝒪_{X'}(-E)` is the ideal sheaf of `E`. This is the input the projective space bundle
formula of Stacks 02TW needs on `E`, and so the input of the degree computation in the proof of
Stacks 0FIH.

## The route

Stacks 0FUT (`Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectiveBundle`,
`exceptionalTwistOneIso`) identifies the exceptional divisor of `AlgebraicGeometry.blowUp` with the
projective bundle `𝐏(ℐ/ℐ²)` of the situation model, over the centre, and `𝒪(1)` with the
restriction of the ideal sheaf of the exceptional divisor; that bundle with its `𝒪(1)` is a
locally projective tower (`Stacks.ProjectiveBundle.isLocallyProjectiveTower_projectiveBundle`).
The exceptional divisor of `AlgebraicGeometry.blowUp` is `E` up to the comparison
`AlgebraicGeometry.blowUpIso` of the two presentations of the blowup and the identification
`Z ≅ V(ℐ)`, both over `X`; the restricted ideal sheaves correspond by the transports of ideal
sheaves along isomorphisms of source and target
(`Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSourceOfCompEq`,
`Stacks.Conormal.AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget`).

## Main results

* `Stacks.AlgebraicGeometry.isLocallyProjectiveTower_exceptionalDivisor`: the tower on the
  exceptional divisor of `AlgebraicGeometry.blowUp`, over `V(ℐ)`.
* `Stacks.AlgebraicGeometry.isLocallyProjectiveTower_pullbackSnd_blowUpToBase`: **the tower on
  `E = X' ×_X Z`, over `Z`.**

## References

* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry

variable {S X Z : Scheme.{u}} (f : X ⟶ S) [Smooth f]

/-- **The exceptional divisor of the blowup in a smooth centre of codimension `n + 1`, over the
centre, with the restriction of its ideal sheaf, is a projective tower of fibre dimension `n`
locally on the centre** (Stacks 0FUT and the projective-bundle tower). -/
theorem isLocallyProjectiveTower_exceptionalDivisor (ℐ : X.IdealSheafData)
    [Smooth (ℐ.subschemeι ≫ f)] (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) (n + 1)] :
    Stacks.Chow.IsLocallyProjectiveTower n
      (Scheme.IdealSheafData.subschemeMap (exceptionalIdeal ℐ) ℐ (blowUpToBase ℐ)
        (ℐ.le_map_comap (blowUpToBase ℐ)))
      ((Scheme.Modules.pullback (exceptionalIdeal ℐ).subschemeι).obj
        (exceptionalIdealModule ℐ)) :=
  (Stacks.ProjectiveBundle.isLocallyProjectiveTower_projectiveBundle
      (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) n).of_isPullback
    (IsPullback.of_horiz_isIso (fst := (exceptionalDivisorIsoProjectiveBundle f ℐ).hom)
      (g := 𝟙 _) ⟨by rw [exceptionalDivisorIsoProjectiveBundle_hom_toCentre, Category.comp_id]⟩)
    (exceptionalTwistOneIso f ℐ).symm

/-- **The exceptional divisor `E = X' ×_X Z` of the blowup `Stacks.Blowup.blowUp` of `X` along a
closed immersion `i : Z ⟶ X` of schemes smooth over `S`, over `Z`, with the restriction `j^*ℐ_E`
of its ideal sheaf, is a projective tower of fibre dimension `n` locally on `Z`**, when the
conormal sheaf of the centre has rank `n + 1`. -/
theorem isLocallyProjectiveTower_pullbackSnd_blowUpToBase (i : Z ⟶ X) [IsClosedImmersion i]
    [Smooth (i ≫ f)] (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι) (n + 1)] :
    Stacks.Chow.IsLocallyProjectiveTower n (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i)
      ((modulePullback (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i).toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf
          (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i).toLRSHom.toShHom)) := by
  have hinv : inv i.toImage ≫ i = i.ker.subschemeι :=
    (IsIso.inv_comp_eq _).mpr (Scheme.Hom.toImage_imageι i).symm
  have : Smooth (i.ker.subschemeι ≫ f) := by
    rw [← hinv, Category.assoc]
    infer_instance
  have htD := isLocallyProjectiveTower_exceptionalDivisor f i.ker n
  have h' : IsPullback
      ((exceptionalIdeal i.ker).subschemeι ≫ (AlgebraicGeometry.blowUpIso i.ker).hom)
      (Scheme.IdealSheafData.subschemeMap (exceptionalIdeal i.ker) i.ker (blowUpToBase i.ker)
        (i.ker.le_map_comap (blowUpToBase i.ker)) ≫ inv i.toImage)
      (Stacks.Blowup.blowUpToBase i.ker) i :=
    (isPullback_exceptionalDivisor_toCentre i.ker).of_iso (Iso.refl _)
      (AlgebraicGeometry.blowUpIso i.ker) (asIso (inv i.toImage)) (Iso.refl X)
      (by simp) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id, AlgebraicGeometry.blowUpIso_hom_blowUpToBase])
      (by rw [Iso.refl_hom, Category.comp_id, asIso_hom, hinv])
  have hφ₁ := h'.isoPullback_hom_fst
  have hφ₂ := h'.isoPullback_hom_snd
  refine htD.of_isPullback (IsPullback.of_horiz_isIso (fst := h'.isoPullback.inv)
    (g := i.toImage) ⟨?_⟩) ?_
  · rw [← cancel_epi h'.isoPullback.hom, Iso.hom_inv_id_assoc, reassoc_of% hφ₂,
      IsIso.inv_hom_id, Category.comp_id]
  · have hfst : h'.isoPullback.symm.hom ≫
        ((exceptionalIdeal i.ker).subschemeι ≫ (AlgebraicGeometry.blowUpIso i.ker).hom) =
          pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i :=
      (Iso.inv_comp_eq _).mpr hφ₁.symm
    exact
      Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSourceOfCompEq
        h'.isoPullback.symm _ _ hfst ≪≫
      (modulePullback h'.isoPullback.inv.toLRSHom.toShHom).mapIso
        (Stacks.Conormal.AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget
          (exceptionalIdeal i.ker).subschemeι (AlgebraicGeometry.blowUpIso i.ker) _ rfl)

end Stacks.AlgebraicGeometry

end
