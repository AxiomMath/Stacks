module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.AffineCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartReesUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Size.Blowup

/-!
# The blowup of an affine scheme is the blowup of the algebraic space it represents

Let `T` be an object of the big fppf site over `S` whose underlying scheme is affine and let `K`
be a quasi-coherent sheaf of ideals on it. The blowup `blowUp K ⟶ T` of the scheme, regarded as a
morphism of algebraic spaces, is the blowup of the algebraic space represented by `T` along the
closed subspace `Z_K` cut out by `K`, when `V(K) ⟶ T` is of finite presentation: it is a final
object of the category of Stacks 085U.

## Main definitions

* `AlgebraicGeometry.Space.blowUpObj`, `AlgebraicGeometry.Space.blowUpObjHom`: the scheme blowup
  `blowUp K ⟶ T` as a morphism of the site.

## Main results

* `AlgebraicGeometry.Space.exists_iso_schemeSpace_blowUpObj`: a blowup of the algebraic space
  represented by an affine `T` along `Z_K` is isomorphic over `T` to the scheme blowup.
* `AlgebraicGeometry.Space.isBlowupAlong_schemeSpaceMap_blowUpObjHom`: the scheme blowup of an
  affine `T` in `K` is the blowup of the algebraic space represented by `T` along `Z_K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The blowup `blowUp K` of the scheme underlying a site object `T` in a sheaf of ideals `K`, as
an object of the site over `S`. -/
def blowUpObj (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (lt_of_le_of_lt (Scheme.size_blowUp_le K) T.left.property)
    (_root_.AlgebraicGeometry.blowUpToBase K ≫ B.inclusion.map T.hom)

/-- The blowup morphism `blowUp K ⟶ T`, as a morphism of the site. -/
def blowUpObjHom (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) : blowUpObj T K ⟶ T :=
  Over.homMk (ObjectProperty.homMk (_root_.AlgebraicGeometry.blowUpToBase K)) rfl

/-- The underlying morphism of schemes of `blowUpObjHom T K` is the blowup morphism
`blowUpToBase K`. -/
theorem toScheme_map_blowUpObjHom (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) :
    (BigFppfOver.toScheme B S hS).map (blowUpObjHom T K) =
      _root_.AlgebraicGeometry.blowUpToBase K :=
  rfl

/-- On the identity chart of an affine site object, the sheaf of ideals whose Rees algebra the
blowup of `Z_K` is built from is `K` itself. -/
theorem reesChartIdeal_closedSubspaceOfIdeal (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) :
    reesChartIdeal (centreIdeal (preimageClosedSubspace (𝟙 (schemeSpace T))
        (closedSubspaceOfIdeal T K)))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS T) = K := by
  have hpre : preimageClosedSubspace (𝟙 (schemeSpace T)) (closedSubspaceOfIdeal T K) =
      closedSubspaceOfIdeal T K :=
    Subtype.ext (Subfunctor.preimage_id _)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (presentationChart (selfPresentation B S hS T)).obj.left) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  rw [hpre, reesChartIdeal_selfPresentation_eq_ofIdealTop,
    ← ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS (schemeSpace T) (closedSubspaceOfIdeal T K)
      (presentationChart (selfPresentation B S hS T))]
  exact ker_rep_snd_closedSubspaceOfIdeal T K

/-- A site object over `T` presented, over `T`, as `Proj` of the Rees algebra of the ideal of
global sections of `K` is the scheme blowup of `T` in `K`, compatibly with any identification of
an algebraic space with it. -/
theorem exists_iso_schemeSpace_blowUpObj_of_iso_proj (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) {T' : AlgebraicSpaces B S hS}
    {b : T' ⟶ schemeSpace T} {R : BigFppfOver B S hS} (r : R ⟶ T) (e : T' ≅ schemeSpace R)
    (he : e.hom ≫ schemeSpaceMap r = b)
    (f : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading
      (K.ideal (Stacks.Blowup.topAffineOpen _))) ≅ (BigFppfOver.toScheme B S hS).obj R)
    (hf : f.hom ≫ (BigFppfOver.toScheme B S hS).map r =
      Stacks.Blowup.toSpec (K.ideal (Stacks.Blowup.topAffineOpen _)) ≫
        (Stacks.RelativeProj.isAffineOpen (Stacks.Blowup.topAffineOpen _)).isoSpec.inv ≫
          (Stacks.Blowup.topAffineOpen _).1.ι) :
    ∃ e' : T' ≅ schemeSpace (blowUpObj T K), e'.hom ≫ schemeSpaceMap (blowUpObjHom T K) = b := by
  let ψ := Stacks.Blowup.reesRelativeProjIsoProj K ≪≫ Stacks.Blowup.reesSituationBlowUpIso K
  have hψ : ψ.hom ≫ _root_.AlgebraicGeometry.blowUpToBase K =
      Stacks.Blowup.toSpec (K.ideal (Stacks.Blowup.topAffineOpen _)) ≫
        (Stacks.RelativeProj.isAffineOpen (Stacks.Blowup.topAffineOpen _)).isoSpec.inv ≫
          (Stacks.Blowup.topAffineOpen _).1.ι := by
    simp only [ψ, Iso.trans_hom, Category.assoc,
      Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase]
    exact Stacks.Blowup.reesRelativeProjIsoProj_hom_comp K
  have hφ : (f.inv ≫ ψ.hom) ≫ _root_.AlgebraicGeometry.blowUpToBase K =
      (BigFppfOver.toScheme B S hS).map r := by
    rw [Category.assoc, hψ, ← hf, Iso.inv_hom_id_assoc]
  have hw : (f.inv ≫ ψ.hom) ≫ (_root_.AlgebraicGeometry.blowUpToBase K ≫
      B.inclusion.map T.hom) = B.inclusion.map R.hom := by
    rw [← Category.assoc, hφ]
    exact congrArg B.inclusion.map (Over.w r)
  let εh : R ⟶ blowUpObj T K := BigFppfOver.homMk B S hS _ _ (f.inv ≫ ψ.hom) hw
  have hεr : εh ≫ blowUpObjHom T K = r :=
    (BigFppfOver.toScheme B S hS).map_injective (by rwa [Functor.map_comp])
  have : IsIso ((BigFppfOver.toScheme B S hS).map εh) :=
    inferInstanceAs (IsIso (f.inv ≫ ψ.hom))
  have : IsIso εh := isIso_of_reflects_iso εh (BigFppfOver.toScheme B S hS)
  refine ⟨e ≪≫ (schemeSpaceFunctor B S hS).mapIso (asIso εh), ?_⟩
  rw [← he, ← hεr]
  exact (Category.assoc _ _ _).trans
    (congrArg (e.hom ≫ ·) ((schemeSpaceFunctor B S hS).map_comp _ _).symm)

/-- **A blowup of the algebraic space represented by an affine `T` along `Z_K` is the scheme
blowup of `T` in `K`**, up to an isomorphism over `T`. -/
theorem exists_iso_schemeSpace_blowUpObj (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) {T' : AlgebraicSpaces B S hS}
    {b : T' ⟶ schemeSpace T} (hb : IsBlowupAlong B S hS (closedSubspaceOfIdeal T K) b) :
    ∃ e : T' ≅ schemeSpace (blowUpObj T K), e.hom ≫ schemeSpaceMap (blowUpObjHom T K) = b := by
  have ha : IsEtale B S hS (𝟙 (schemeSpace T) : schemeSpace T ⟶ schemeSpace T).hom :=
    isEtale_of_isIso B S hS _
  obtain ⟨e, he, f, hf⟩ := exists_iso_proj_reesGrading_affineChart_unconditional hb T ha
    (IsPullback.id_vert b) (K.ideal (Stacks.Blowup.topAffineOpen _))
    (by rw [reesChartIdeal_closedSubspaceOfIdeal])
  exact exists_iso_schemeSpace_blowUpObj_of_iso_proj T K _ e he f hf

/-- **The scheme blowup of an affine `T` in `K` is the blowup of the algebraic space represented
by `T` along `Z_K`**, in the sense of the universal property of Stacks 085U, when `V(K) ⟶ T` is
of finite presentation. -/
theorem isBlowupAlong_schemeSpaceMap_blowUpObjHom (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData)
    (hK : FinitePresentation K.subschemeι) :
    IsBlowupAlong B S hS (closedSubspaceOfIdeal T K) (schemeSpaceMap (blowUpObjHom T K)) := by
  obtain ⟨T', b, hb⟩ := exists_isBlowupAlong_of_isFinitePresentation
    (closedSubspaceOfIdeal T K) (isFinitePresentation_closedSubspaceOfIdeal T K hK)
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_blowUpObj T K hb
  have h := hb.of_iso_over e.symm
  rwa [← he, Iso.symm_hom, Iso.inv_hom_id_assoc] at h

end AlgebraicGeometry.Space

end
