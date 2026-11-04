module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartRees
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupSecondCentreChart
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.BlowupRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.BlowupOfRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated

/-!
# Blowups of algebraic spaces represented by schemes

Every closed subspace of the algebraic space of a scheme `T` of the site is cut out by an ideal
sheaf on `T`, and a blowup of that space in the closed subspace cut out by a finitely presented
ideal sheaf `I` is, over `T`, the space of the scheme blowup `Bl_I T`.  For an affine algebraic
space this makes every blowup in a finitely presented centre the space of a quasi-compact and
quasi-separated scheme.

## Main results

* `AlgebraicGeometry.Space.exists_eq_closedSubspaceOfIdeal`: closed subspaces of the space of a
  scheme come from ideal sheaves.
* `AlgebraicGeometry.Space.exists_iso_schemeSpace_blowUpObj_of_isBlowupAlong`: a blowup of the
  space of a scheme is the space of the scheme blowup (Stacks 085R on the identity chart).
* `AlgebraicGeometry.Space.exists_iso_schemeSpace_of_isBlowupAlong_of_isAffineSpace`: a blowup
  of an affine algebraic space in a finitely presented centre is the space of a qcqs scheme.

## References

* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every closed subspace of the algebraic space of a scheme of the site is the closed subspace
cut out by an ideal sheaf on the scheme: the kernel of its base change to the identity chart. -/
theorem exists_eq_closedSubspaceOfIdeal (T : BigFppfOver B S hS)
    (W : ClosedSubspaces B S hS (schemeSpace T).1) :
    ∃ K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData, W = closedSubspaceOfIdeal T K := by
  obtain ⟨j, hj⟩ : ∃ j, j = W.2.2.rep.snd (𝟙 (yoneda.obj T)) := ⟨_, rfl⟩
  have hjc : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) := by
    rw [hj]; exact W.2.2.property_snd _
  obtain ⟨K, hK⟩ : ∃ K, K = ((BigFppfOver.toScheme B S hS).map j).ker := ⟨_, rfl⟩
  refine ⟨K, Subtype.ext ?_⟩
  have hr : Subfunctor.range (yoneda.map j) = W.1 := by
    have h := range_yoneda_snd_eq_preimage B S hS (𝟙 (yoneda.obj T)) W.2.2.rep
    rw [hj]; exact h.trans (Subfunctor.preimage_id (W.1 : Subfunctor (yoneda.obj T)))
  have hq : ((BigFppfOver.toScheme B S hS).map (closedSubschemeOverι B S hS T K)).ker = K := by
    rw [toScheme_map_closedSubschemeOverι]
    exact Scheme.IdealSheafData.ker_subschemeι K
  have hqc : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (closedSubschemeOverι B S hS T K)) := by
    rw [toScheme_map_closedSubschemeOverι]
    exact inferInstanceAs (AlgebraicGeometry.IsClosedImmersion K.subschemeι)
  obtain ⟨l₁, hl₁⟩ := exists_comp_eq_of_ker_le_of_isClosedImmersion j
    (closedSubschemeOverι B S hS T K) (by rw [hq, hK])
  obtain ⟨l₂, hl₂⟩ := exists_comp_eq_of_ker_le_of_isClosedImmersion
    (closedSubschemeOverι B S hS T K) j (by rw [hq, hK])
  rw [← hr]
  show Subfunctor.range (yoneda.map j) =
    Subfunctor.range (yoneda.map (closedSubschemeOverι B S hS T K))
  refine le_antisymm ?_ ?_
  · rw [← hl₂, Functor.map_comp]
    exact Subfunctor.range_comp_le _ _
  · rw [← hl₁, Functor.map_comp]
    exact Subfunctor.range_comp_le _ _

/-- **A blowup of an affine algebraic space in a finitely presented closed subspace is the
algebraic space of a quasi-compact and quasi-separated scheme.** -/
theorem exists_iso_schemeSpace_of_isBlowupAlong_of_isAffineSpace {V V₁ : AlgebraicSpaces B S hS}
    (hV : IsAffineSpace B S hS V.1) (Z : ClosedSubspaces B S hS V.1)
    (hZ : IsFinitePresentation B S hS Z.1.ι) {c : V₁ ⟶ V} (hc : IsBlowupAlong B S hS Z c) :
    ∃ Q : BigFppfOver B S hS, CompactSpace ((BigFppfOver.toScheme B S hS).obj Q) ∧
      QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Q) ∧
        Nonempty (V₁ ≅ schemeSpace Q) := by
  obtain ⟨T, hTa, ⟨eV⟩⟩ := id hV
  let e : V ≅ schemeSpace T := ObjectProperty.isoMk _ eV
  have hp := isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Z c hZ hc
  have hqc : IsQuasiCompactSpace B S hS V₁.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS c hp.2.1.2 hV
  have hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal V₁.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS
      B.contains_terminal c (isQuasiSeparated_of_isSeparated B S hS hp.1) hV
  have hsq : IsPullback (c ≫ e.hom) (𝟙 V₁) e.inv c :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hc' := isBlowupAlong_preimage_of_isPullback_of_isFlat
    (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS e.inv.hom)) hc hsq
  obtain ⟨K, hK⟩ := exists_eq_closedSubspaceOfIdeal T (preimageClosedSubspace e.inv Z)
  rw [hK] at hc'
  obtain ⟨eQ, -⟩ := exists_iso_schemeSpace_blowUpObj T K hc'
  have eF : V₁.1 ≅ yoneda.obj (blowUpObj T K) := (ObjectProperty.ι _).mapIso eQ
  refine ⟨blowUpObj T K, compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    (IsQuasiCompactSpace.of_iso B S hS hqc eF), ?_, ⟨eQ⟩⟩
  exact (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS B.contains_terminal
    _).1 (isAbsolutelyQuasiSeparated_of_mono B S hS B.contains_terminal
      (isAlgebraicSpace_yoneda B S hS _) eF.inv inferInstance hqs)

/-- **A blowup of the algebraic space of a scheme in the closed subspace cut out by a finitely
presented ideal sheaf is the space of the scheme blowup**, over the base. -/
theorem exists_iso_schemeSpace_blowUpObj_of_isBlowupAlong (V : BigFppfOver B S hS)
    (I : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
    (hI : FinitePresentation I.subschemeι) {W' : AlgebraicSpaces B S hS}
    {b : W' ⟶ schemeSpace V} (hb : IsBlowupAlong B S hS (closedSubspaceOfIdeal V I) b) :
    ∃ e : W' ≅ schemeSpace (blowUpObj V I), e.hom ≫ schemeSpaceMap (blowUpObjHom V I) = b := by
  obtain ⟨e, he⟩ := exists_iso_yoneda_blowUpObj_of_isBlowupAlong V I hI hb
  refine ⟨(ObjectProperty.isoMk _ e).symm, ObjectProperty.hom_ext _ ?_⟩
  show e.inv ≫ yoneda.map (blowUpObjHom V I) = b.hom
  rw [← he]
  exact Iso.inv_hom_id_assoc e _

end AlgebraicGeometry.Space

end
