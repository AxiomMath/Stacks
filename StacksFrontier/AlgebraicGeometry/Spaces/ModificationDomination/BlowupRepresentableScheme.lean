module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.BlowupRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCentreCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.SchemeNormalizedBlowupBridge

/-!
# The blowup of a scheme is the blowup of the algebraic space it represents

Let `T` be an object of the big fppf site over `S` and let `K` be a quasi-coherent sheaf of
ideals on its underlying scheme with `V(K) ⟶ T` of finite presentation. The blowup
`blowUp K ⟶ T` of the scheme, regarded as a morphism of algebraic spaces, is the blowup of the
algebraic space represented by `T` along the closed subspace `Z_K` cut out by `K`: it is a final
object of the category of Stacks 085U. No affineness of `T` is needed.

The proof reads a blowup of the algebraic space, which exists because `Z_K` is of finite
presentation (`AlgebraicGeometry.Space.exists_isBlowupAlong_of_isFinitePresentation`), on the
identity chart of `T`: by Stacks 085R in the form
`AlgebraicGeometry.Space.exists_iso_schemeSpace_reesProjChart_of_isEtale` it is the relative `Proj`
of the Rees algebra of the sheaf of ideals that `Z_K` induces on that chart, which is `K` itself
(`AlgebraicGeometry.Space.reesChartIdeal_selfPresentation_closedSubspaceOfIdeal`), and that
relative `Proj` is the scheme blowup of `T` in `K`
(`AlgebraicGeometry.Space.exists_iso_relativeProj_reesSituation_blowUp`).

## Main results

* `AlgebraicGeometry.Space.reesChartIdeal_selfPresentation_closedSubspaceOfIdeal`.
* `AlgebraicGeometry.Space.isBlowupAlong_closedSubspaceOfIdeal_schemeSpaceMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The identity of the space represented by `T` pulls `Z_K` back to itself. -/
theorem preimageClosedSubspace_id_closedSubspaceOfIdeal (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) :
    preimageClosedSubspace (𝟙 (schemeSpace T)) (closedSubspaceOfIdeal T K) =
      closedSubspaceOfIdeal T K :=
  Subtype.ext (Subfunctor.preimage_id _)

/-- **On the self-presentation of a scheme the ideal induced by `Z_K` is `K`.** -/
theorem reesChartIdeal_selfPresentation_closedSubspaceOfIdeal (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) :
    reesChartIdeal (centreIdeal (closedSubspaceOfIdeal T K))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS T) = K := by
  rw [← ker_rep_snd_eq_reesChartIdeal B S hS (schemeSpace T) (closedSubspaceOfIdeal T K)
    (selfPresentation B S hS T)]
  exact ker_rep_snd_closedSubspaceOfIdeal T K

/-- A site object `R` over `T` whose scheme is identified, over `T`, with the scheme blowup of
`T` in `K` represents that blowup, compatibly with any identification of an algebraic space with
it. -/
theorem exists_iso_schemeSpace_blowUpObj_of_iso (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) {T' : AlgebraicSpaces B S hS}
    {b : T' ⟶ schemeSpace T} {R : BigFppfOver B S hS} (r : R ⟶ T) (e : T' ≅ schemeSpace R)
    (he : e.hom ≫ schemeSpaceMap r = b)
    (ψ : (BigFppfOver.toScheme B S hS).obj R ≅ AlgebraicGeometry.blowUp K)
    (hψ : ψ.hom ≫ AlgebraicGeometry.blowUpToBase K = (BigFppfOver.toScheme B S hS).map r) :
    ∃ e' : T' ≅ schemeSpace (blowUpObj T K), e'.hom ≫ schemeSpaceMap (blowUpObjHom T K) = b := by
  have hw : ψ.hom ≫ (AlgebraicGeometry.blowUpToBase K ≫ B.inclusion.map T.hom) =
      B.inclusion.map R.hom := by
    rw [← Category.assoc, hψ]
    exact congrArg B.inclusion.map (Over.w r)
  let εh : R ⟶ blowUpObj T K := BigFppfOver.homMk B S hS _ _ ψ.hom hw
  have hεr : εh ≫ blowUpObjHom T K = r :=
    (BigFppfOver.toScheme B S hS).map_injective ((Functor.map_comp _ _ _).trans hψ)
  have : IsIso ((BigFppfOver.toScheme B S hS).map εh) := inferInstanceAs (IsIso ψ.hom)
  have : IsIso εh := isIso_of_reflects_iso εh (BigFppfOver.toScheme B S hS)
  refine ⟨e ≪≫ (schemeSpaceFunctor B S hS).mapIso (asIso εh), ?_⟩
  rw [← he, ← hεr]
  exact (Category.assoc _ _ _).trans
    (congrArg (e.hom ≫ ·) ((schemeSpaceFunctor B S hS).map_comp _ _).symm)

/-- **A blowup of the algebraic space represented by `T` along `Z_K` is the scheme blowup of `T`
in `K`**, up to an isomorphism over `T`, when `V(K) ⟶ T` is of finite presentation. -/
theorem exists_iso_schemeSpace_blowUpObj_of_finitePresentation (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData)
    (hK : FinitePresentation K.subschemeι) {T' : AlgebraicSpaces B S hS}
    {b : T' ⟶ schemeSpace T} (hb : IsBlowupAlong B S hS (closedSubspaceOfIdeal T K) b) :
    ∃ e : T' ≅ schemeSpace (blowUpObj T K), e.hom ≫ schemeSpaceMap (blowUpObjHom T K) = b := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  have hpre := preimageClosedSubspace_id_closedSubspaceOfIdeal T K
  have hZfp' : IsFinitePresentation B S hS
      (preimageClosedSubspace (𝟙 (schemeSpace T)) (closedSubspaceOfIdeal T K)).1.ι := by
    rw [hpre]
    exact isFinitePresentation_closedSubspaceOfIdeal T K hK
  have hcU := contains_reesChartSituation_centreIdeal _ hZfp' (selfPresentation B S hS T)
  have hcR := contains_reesRelationSituation_centreIdeal _ hZfp' (selfPresentation B S hS T)
  have hcRR := contains_reesDoubleSituation_centreIdeal _ hZfp' (selfPresentation B S hS T)
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale hb T
    (a := 𝟙 (schemeSpace T)) (isEtale_id B S hS _) hcU hcR hcRR (IsPullback.of_id_snd (f := b))
  have hI : reesChartIdeal (centreIdeal (preimageClosedSubspace (𝟙 (schemeSpace T))
      (closedSubspaceOfIdeal T K))) (isCartesianOnAffineCharts_centreIdeal _)
      (selfPresentation B S hS T) = K := by
    rw [hpre]
    exact reesChartIdeal_selfPresentation_closedSubspaceOfIdeal T K
  obtain ⟨ψ, hψ⟩ := exists_iso_relativeProj_reesSituation_blowUp _ _ hI
  exact exists_iso_schemeSpace_blowUpObj_of_iso T K _ e he ψ hψ

/-- **The scheme blowup of `T` in `K` is the blowup of the algebraic space represented by `T`
along `Z_K`**, in the sense of the universal property of Stacks 085U, when `V(K) ⟶ T` is of
finite presentation. -/
theorem isBlowupAlong_closedSubspaceOfIdeal_schemeSpaceMap (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData)
    (hK : FinitePresentation K.subschemeι) :
    IsBlowupAlong B S hS (closedSubspaceOfIdeal T K) (schemeSpaceMap (blowUpObjHom T K)) := by
  obtain ⟨T', b, hb⟩ := exists_isBlowupAlong_of_isFinitePresentation
    (closedSubspaceOfIdeal T K) (isFinitePresentation_closedSubspaceOfIdeal T K hK)
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_blowUpObj_of_finitePresentation T K hK hb
  have h := hb.of_iso_over e.symm
  rwa [← he, Iso.symm_hom, Iso.inv_hom_id_assoc] at h

end AlgebraicGeometry.Space

end
