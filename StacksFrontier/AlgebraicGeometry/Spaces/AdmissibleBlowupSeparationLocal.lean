module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleSeparation
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartRees
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# The blowup in a sum of two ideals with nilpotent product splits, étale locally

Let `X` be an algebraic space over a scheme `S`, let `Z₁, Z₂ ⊆ X` be closed subspaces whose sets
of points cover `|X|`, and let `b : X' ⟶ X` be the blowup of `X` in their scheme-theoretic
intersection `Z₁ ∩ Z₂`.  On an étale scheme chart `V ⟶ X` the two closed subspaces are cut out
by sheaves of ideals `ℐ₁`, `ℐ₂` whose product is locally nilpotent, the intersection by
`ℐ₁ + ℐ₂`, and the base change `V ×_X X'` is the scheme blowup of `V` in `ℐ₁ + ℐ₂`, which splits
into two disjoint open pieces by the scheme case of Stacks 080P.

## Main results

* `AlgebraicGeometry.Space.ker_rep_snd_inf`: on a scheme chart the sheaf of ideals cut out by
  the intersection of two closed subspaces is the sum of the two sheaves of ideals.
* `AlgebraicGeometry.Space.subspacePointSet_inf`: the points of the intersection of two closed
  subspaces are the common points.
* `AlgebraicGeometry.Space.isFinitePresentation_inf`: the intersection of two finitely
  presented closed subspaces is finitely presented.
* `AlgebraicGeometry.Space.exists_open_partition_of_isPullback`: on the base change of the blowup
  to an étale scheme chart the inverse images of two open sets of points avoiding `Z₁`, resp.
  `Z₂`, are separated by a partition into two open sets.
* `AlgebraicGeometry.Space.isOpen_closure_subspacePointSet_preimage_of_isBlowupAlong_inf`: the
  closure in `|X'|` of the points of the inverse image of an open subspace avoiding `Z₁` is open.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_openComplement_of_isFinitePresentation`: the
  complement of a finitely presented closed subspace of a quasi-compact algebraic space is
  quasi-compact.
* `exists_isAdmissibleBlowup_disjoint_openSubspace_decomposition_of_closedSubspaces`: given
  finitely presented closed subspaces `Z₁, Z₂` covering `|X|` and open subspaces `U, V` avoiding
  `Z₁`, resp. `Z₂`, some `U ∪ V`-admissible blowup of `X` is the disjoint union of two open
  subspaces containing the inverse images of `U`, resp. `V`.

## References

* [Stacks Project, Tag 086F](https://stacks.math.columbia.edu/tag/086F)
* [Stacks Project, Tag 080P](https://stacks.math.columbia.edu/tag/080P)
* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Closed subschemes cut out by ideal sheaves -/

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- A morphism factors through the closed subscheme cut out by `I` exactly when `I` lies in its
kernel. -/
theorem factors_mk_subschemeι_iff (I : X.IdealSheafData) {T : Scheme.{u}} (f : T ⟶ X) :
    (Subobject.mk I.subschemeι).Factors f ↔ I ≤ f.ker := by
  constructor
  · intro h
    have hf : (Subobject.mk I.subschemeι).factorThru f h ≫
        (Subobject.mk I.subschemeι).arrow = f := Subobject.factorThru_arrow _ _ _
    have hk : (Subobject.mk I.subschemeι).arrow.ker = I := by
      rw [← Subobject.underlyingIso_hom_comp_eq_mk, Hom.ker_comp_of_isIso, I.ker_subschemeι]
    calc I = (Subobject.mk I.subschemeι).arrow.ker := hk.symm
      _ ≤ f.ker := hf ▸ Hom.le_ker_comp _ _
  · intro h
    have hI : I.subschemeι.ker ≤ f.ker := I.ker_subschemeι.le.trans h
    rw [← _root_.AlgebraicGeometry.IsClosedImmersion.lift_fac I.subschemeι f hI]
    exact Subobject.factors_of_factors_right _ (Subobject.mk_factors_self _)

/-- Two ideal sheaves cutting out the same subobject are equal. -/
theorem eq_of_mk_subschemeι_eq {I J : X.IdealSheafData}
    (h : Subobject.mk I.subschemeι = Subobject.mk J.subschemeι) : I = J := by
  refine le_antisymm ?_ ?_
  · rw [← J.ker_subschemeι, ← factors_mk_subschemeι_iff, h]
    exact Subobject.mk_factors_self _
  · rw [← I.ker_subschemeι, ← factors_mk_subschemeι_iff, ← h]
    exact Subobject.mk_factors_self _

/-- A closed immersion and the closed subscheme cut out by its kernel are the same subobject. -/
theorem mk_ker_subschemeι {Y : Scheme.{u}} (f : Y ⟶ X)
    [_root_.AlgebraicGeometry.IsClosedImmersion f] :
    Subobject.mk f.ker.subschemeι = Subobject.mk f :=
  Subobject.mk_eq_mk_of_comm _ _ (asIso f.toImage).symm (by
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
    exact (Scheme.Hom.toImage_imageι f).symm)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The blowup in a sum splits, read on the relative `Proj` -/

/-- **The relative `Proj` of the Rees algebra of a sum `ℐ + 𝒥` of two sheaves of ideals with
nilpotent product is partitioned by two open sets** containing the inverse images of any opens
disjoint from the support of `ℐ`, resp. `𝒥`. -/
theorem exists_open_partition_reesSituation_relativeProj {Y : Scheme.{u}}
    (K I J : Y.IdealSheafData) (hK : K = I ⊔ J) (hIJ : I * J ≤ Y.nilradical) (O₁ O₂ : Y.Opens)
    (h₁ : Disjoint (O₁ : Set Y) (I.support : Set Y))
    (h₂ : Disjoint (O₂ : Set Y) (J.support : Set Y)) :
    ∃ G₁ G₂ : Set (Stacks.Blowup.reesSituation K).relativeProj, IsOpen G₁ ∧ IsOpen G₂ ∧
      Disjoint G₁ G₂ ∧ G₁ ∪ G₂ = Set.univ ∧
        (∀ x, (Stacks.Blowup.reesSituation K).relativeProjToBase x ∈ O₁ → x ∈ G₁) ∧
          ∀ x, (Stacks.Blowup.reesSituation K).relativeProjToBase x ∈ O₂ → x ∈ G₂ := by
  subst hK
  obtain ⟨U₁, U₂, hd, hc, hU₁, hU₂⟩ :=
    Stacks.Blowup.exists_disjoint_open_cover_blowUp_sup I J hIJ O₁ O₂ h₁ h₂
  let ψ := Stacks.Blowup.reesSituationBlowUpIso (I ⊔ J) ≪≫ AlgebraicGeometry.blowUpIso (I ⊔ J)
  have hψ : ψ.hom ≫ Stacks.Blowup.blowUpToBase (I ⊔ J) =
      (Stacks.Blowup.reesSituation (I ⊔ J)).relativeProjToBase := by
    change (Stacks.Blowup.reesSituationBlowUpIso (I ⊔ J)).hom ≫
      (AlgebraicGeometry.blowUpIso (I ⊔ J)).hom ≫ Stacks.Blowup.blowUpToBase (I ⊔ J) = _
    rw [AlgebraicGeometry.blowUpIso_hom_blowUpToBase]
    exact Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase _
  have hpt : ∀ x, Stacks.Blowup.blowUpToBase (I ⊔ J) (ψ.hom x) =
      (Stacks.Blowup.reesSituation (I ⊔ J)).relativeProjToBase x := fun x => by
    rw [← hψ]
    rfl
  refine ⟨ψ.hom ⁻¹' (U₁ : Set _), ψ.hom ⁻¹' (U₂ : Set _),
    U₁.isOpen.preimage ψ.hom.continuous, U₂.isOpen.preimage ψ.hom.continuous,
    Set.disjoint_left.2 fun x hx₁ hx₂ => ?_, Set.eq_univ_of_forall fun x => ?_,
    fun x hx => hU₁ ?_, fun x hx => hU₂ ?_⟩
  · exact hd.le_bot (⟨hx₁, hx₂⟩ : ψ.hom x ∈ U₁ ⊓ U₂)
  · exact hc.ge trivial
  · rwa [Scheme.Hom.mem_preimage, hpt]
  · rwa [Scheme.Hom.mem_preimage, hpt]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed subspaces read on a scheme chart -/

/-- The functor of points of a subscheme cut out by the sum of two ideal sheaves is the
intersection of the two functors of points. -/
theorem subschemePoints_mk_sup_subschemeι {U : BigFppfOver B S hS}
    (I J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) :
    subschemePoints B S hS (Subobject.mk (I ⊔ J).subschemeι) =
      subschemePoints B S hS (Subobject.mk I.subschemeι) ⊓
        subschemePoints B S hS (Subobject.mk J.subschemeι) := by
  refine le_antisymm (fun T f hf => ?_) (fun T f hf => ?_)
  · rw [mem_subschemePoints_iff, Scheme.IdealSheafData.factors_mk_subschemeι_iff,
      sup_le_iff] at hf
    exact ⟨(mem_subschemePoints_iff B S hS f).2
        ((Scheme.IdealSheafData.factors_mk_subschemeι_iff _ _).2 hf.1),
      (mem_subschemePoints_iff B S hS f).2
        ((Scheme.IdealSheafData.factors_mk_subschemeι_iff _ _).2 hf.2)⟩
  · obtain ⟨h₁, h₂⟩ := hf
    rw [mem_subschemePoints_iff, Scheme.IdealSheafData.factors_mk_subschemeι_iff] at h₁ h₂ ⊢
    exact sup_le h₁ h₂

/-- The functor of points of the closed subscheme of a scheme chart `b : V ⟶ X` cut out by the
kernel of the base change of a closed immersion `Z ⟶ X` is the inverse image of `Z`. -/
theorem subschemePoints_mk_ker_rep_snd {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor X)
    (hZ : IsClosedImmersion B S hS Z.ι) {V : BigFppfOver B S hS} (b : yoneda.obj V ⟶ X) :
    subschemePoints B S hS (Subobject.mk
        ((BigFppfOver.toScheme B S hS).map (hZ.rep.snd b)).ker.subschemeι) = Z.preimage b := by
  have : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hZ.rep.snd b)) := hZ.property_snd b
  rw [Scheme.IdealSheafData.mk_ker_subschemeι,
    subschemePoints_eq_range B S hS (hZ.rep.snd b) (Subobject.underlyingIso _).symm
      (Subobject.underlyingIso_arrow _),
    range_yoneda_snd_eq_preimage]

/-- The arrow of the subobject cut out by an ideal sheaf is an immersion. -/
private theorem isImmersion_arrow_mk_subschemeι {Y : Scheme.{u}} (K : Y.IdealSheafData) :
    AlgebraicGeometry.IsImmersion (Subobject.mk K.subschemeι).arrow := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

/-- **On a scheme chart, the intersection of two closed subspaces is cut out by the sum of the
two sheaves of ideals.**  For closed subspaces `Z₁, Z₂ ⊆ X` and a morphism `b : V ⟶ X` from a
scheme of the site, the kernel of the base change of `Z₁ ∩ Z₂ ⟶ X` along `b` is the sum of the
kernels of the base changes of `Z₁ ⟶ X` and `Z₂ ⟶ X`. -/
theorem ker_rep_snd_inf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z₁ Z₂ : Subfunctor X)
    (h₁ : IsClosedImmersion B S hS Z₁.ι) (h₂ : IsClosedImmersion B S hS Z₂.ι)
    (h : IsClosedImmersion B S hS (Z₁ ⊓ Z₂).ι) {V : BigFppfOver B S hS}
    (b : yoneda.obj V ⟶ X) :
    ((BigFppfOver.toScheme B S hS).map (h.rep.snd b)).ker =
      ((BigFppfOver.toScheme B S hS).map (h₁.rep.snd b)).ker ⊔
        ((BigFppfOver.toScheme B S hS).map (h₂.rep.snd b)).ker := by
  refine Scheme.IdealSheafData.eq_of_mk_subschemeι_eq (subschemePoints_injective B S hS
    (isImmersion_arrow_mk_subschemeι _) (isImmersion_arrow_mk_subschemeι _) ?_)
  rw [subschemePoints_mk_ker_rep_snd B S hS (Z₁ ⊓ Z₂) h b, subschemePoints_mk_sup_subschemeι,
    subschemePoints_mk_ker_rep_snd B S hS Z₁ h₁ b, subschemePoints_mk_ker_rep_snd B S hS Z₂ h₂ b]
  rfl

/-- **The support of the kernel of a closed subspace on a scheme chart is the inverse image of
its points.**  For a closed immersion `Z ⟶ X` and a morphism `b : V ⟶ X` from a scheme of the
site, a point of `V` lies in the support of the kernel of the base change of `Z ⟶ X` exactly
when its image in `|X|` is a point of `Z`. -/
theorem mem_support_ker_rep_snd_iff {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor X)
    (hZ : IsClosedImmersion B S hS Z.ι) {V : BigFppfOver B S hS} (b : yoneda.obj V ⟶ X)
    (v : points B S hS (yoneda.obj V)) :
    pointsToScheme B S hS V v ∈
        ((BigFppfOver.toScheme B S hS).map (hZ.rep.snd b)).ker.support ↔
      pointsMap B S hS _ b v ∈ subspacePointSet B S hS X Z := by
  have : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hZ.rep.snd b)) := hZ.property_snd b
  have hsupp : (((BigFppfOver.toScheme B S hS).map (hZ.rep.snd b)).ker.support : Set _) =
      Set.range ((BigFppfOver.toScheme B S hS).map (hZ.rep.snd b)) := by
    rw [Scheme.Hom.support_ker]
    exact (Scheme.Hom.isClosedEmbedding _).isClosed_range.closure_eq
  have hsq := hZ.rep.isPullback b
  rw [← SetLike.mem_coe, hsupp]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := (bijective_pointsToScheme B S hS _).2 y
    rw [← pointsToScheme_pointsMap_yoneda] at hy
    rw [← (bijective_pointsToScheme B S hS V).1 hy, ← pointsMap_comp_apply, ← hsq.w,
      pointsMap_comp_apply]
    exact Set.mem_range_self _
  · rintro ⟨c, hc⟩
    obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS hsq c v hc
    refine ⟨pointsToScheme B S hS _ w, ?_⟩
    rw [← pointsToScheme_pointsMap_yoneda, hw₂]

/-! ### The intersection of two closed subspaces -/

/-- **The points of the intersection of two subfunctors are the common points.** -/
theorem subspacePointSet_inf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z₁ Z₂ : Subfunctor X) :
    subspacePointSet B S hS X (Z₁ ⊓ Z₂) =
      subspacePointSet B S hS X Z₁ ∩ subspacePointSet B S hS X Z₂ := by
  refine Set.Subset.antisymm (fun x hx => ⟨range_pointsMap_ι_le B S hS inf_le_left hx,
    range_pointsMap_ι_le B S hS inf_le_right hx⟩) ?_
  rintro x ⟨⟨p₁, rfl⟩, ⟨p₂, hp₂⟩⟩
  have hsq := Subfunctor.isPullback_inf Z₁ Z₂
  obtain ⟨w, -, hw₁⟩ := exists_points_of_isPullback B S hS hsq p₂ p₁ hp₂
  refine ⟨w, ?_⟩
  rw [← Subfunctor.homOfLe_ι (inf_le_left : Z₁ ⊓ Z₂ ≤ Z₁), pointsMap_comp_apply, hw₁]

/-- **The intersection of two closed subspaces, the second of which is finitely presented, is
finitely presented over the first.**  Its inclusion into the first is a base change of the
inclusion of the second. -/
theorem isFinitePresentation_homOfLe_inf_left {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (Z₁ Z₂ : Subfunctor X) (h₁ : IsClosedSubspace B S hS Z₁)
    (h₂ : IsClosedSubspace B S hS Z₂) (h : IsClosedSubspace B S hS (Z₁ ⊓ Z₂))
    (hf₂ : IsFinitePresentation B S hS Z₂.ι) :
    IsFinitePresentation B S hS (Subfunctor.homOfLe (inf_le_left : Z₁ ⊓ Z₂ ≤ Z₁)) :=
  isFinitePresentation_of_isPullback B S hS h.1 h₂.1 h₁.1 hX (Subfunctor.isPullback_inf Z₁ Z₂)
    hf₂

/-- **The intersection of two finitely presented closed subspaces is finitely presented.** -/
theorem isFinitePresentation_inf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (Z₁ Z₂ : Subfunctor X) (h₁ : IsClosedSubspace B S hS Z₁)
    (h₂ : IsClosedSubspace B S hS Z₂) (h : IsClosedSubspace B S hS (Z₁ ⊓ Z₂))
    (hf₁ : IsFinitePresentation B S hS Z₁.ι) (hf₂ : IsFinitePresentation B S hS Z₂.ι) :
    IsFinitePresentation B S hS (Z₁ ⊓ Z₂).ι := by
  rw [← Subfunctor.homOfLe_ι (inf_le_left : Z₁ ⊓ Z₂ ≤ Z₁)]
  exact isFinitePresentation_comp B S hS h.1 h₁.1 hX _ _
    (isFinitePresentation_homOfLe_inf_left B S hS hX Z₁ Z₂ h₁ h₂ h hf₂) hf₁

/-! ### The splitting on an étale scheme chart -/

variable {B S hS}

/-- **On the base change of the blowup to an étale scheme chart, the inverse images of two open
sets of points avoiding `Z₁`, resp. `Z₂`, are separated by a partition into two open sets.**

Let `Z₁, Z₂ ⊆ X` be closed subspaces whose points cover `|X|`, with finitely presented
intersection, let `b : X' ⟶ X` be the blowup of `X` in `Z₁ ∩ Z₂`, let `a : V ⟶ X` be étale
with `V` a scheme of the site and let `W = V ×_X X'`.  If `P₁, P₂ ⊆ |X|` are open and disjoint
from the points of `Z₁`, resp. `Z₂`, there is a partition `|W| = G₁ ⊔ G₂` into open sets with
the points of `W` over `P₁` in `G₁` and those over `P₂` in `G₂`. -/
theorem exists_open_partition_of_isPullback {X X' W : AlgebraicSpaces B S hS}
    (Z₁ Z₂ : ClosedSubspaces B S hS X.1)
    (hfp : IsFinitePresentation B S hS (Z₁.1 ⊓ Z₂.1).ι) {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS ⟨Z₁.1 ⊓ Z₂.1, inf_isClosedSubspace B S hS X.1 X.2 Z₁ Z₂⟩ b)
    (hcov : subspacePointSet B S hS X.1 Z₁.1 ∪ subspacePointSet B S hS X.1 Z₂.1 = Set.univ)
    (P₁ P₂ : Set (points B S hS X.1)) (hP₁ : IsOpen P₁) (hP₂ : IsOpen P₂)
    (h₁ : Disjoint P₁ (subspacePointSet B S hS X.1 Z₁.1))
    (h₂ : Disjoint P₂ (subspacePointSet B S hS X.1 Z₂.1))
    (V : BigFppfOver B S hS) {a : schemeSpace V ⟶ X} (ha : IsEtale B S hS a.hom)
    {q : W ⟶ schemeSpace V} {r : W ⟶ X'} (sq : IsPullback q r a b) :
    ∃ G₁ G₂ : Set (points B S hS W.1), IsOpen G₁ ∧ IsOpen G₂ ∧ Disjoint G₁ G₂ ∧
      G₁ ∪ G₂ = Set.univ ∧
        pointsMap B S hS W.1 (q ≫ a).hom ⁻¹' P₁ ⊆ G₁ ∧
          pointsMap B S hS W.1 (q ≫ a).hom ⁻¹' P₂ ⊆ G₂ := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  set Z : ClosedSubspaces B S hS X.1 :=
    ⟨Z₁.1 ⊓ Z₂.1, inf_isClosedSubspace B S hS X.1 X.2 Z₁ Z₂⟩ with hZdef
  set ZV := preimageClosedSubspace a Z with hZV
  have hfpV : IsFinitePresentation B S hS ZV.1.ι :=
    isFinitePresentation_of_isPullback B S hS ZV.2.1 Z.2.1 (schemeSpace V).2 X.2
      (Subfunctor.isPullback_preimage a.hom Z.1) hfp
  have hcU := contains_reesChartSituation_centreIdeal ZV hfpV (selfPresentation B S hS V)
  have hcR := contains_reesRelationSituation_centreIdeal ZV hfpV (selfPresentation B S hS V)
  have hcRR := contains_reesDoubleSituation_centreIdeal ZV hfpV (selfPresentation B S hS V)
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale hb V ha hcU hcR hcRR sq
  set b₀ : yoneda.obj V ⟶ (schemeSpace V).1 :=
    (presentationChart (selfPresentation B S hS V)).1.hom with hb₀
  set Z₁' := preimageClosedSubspace a Z₁ with hZ₁'
  set Z₂' := preimageClosedSubspace a Z₂ with hZ₂'
  set K₁ := ((BigFppfOver.toScheme B S hS).map (Z₁'.2.2.rep.snd b₀)).ker with hK₁
  set K₂ := ((BigFppfOver.toScheme B S hS).map (Z₂'.2.2.rep.snd b₀)).ker with hK₂
  have hK : reesChartIdeal (centreIdeal ZV) (isCartesianOnAffineCharts_centreIdeal ZV)
      (selfPresentation B S hS V) = K₁ ⊔ K₂ := by
    rw [hK₁, hK₂, ← ker_rep_snd_inf B S hS Z₁'.1 Z₂'.1 Z₁'.2.2 Z₂'.2.2 ZV.2.2 b₀]
    exact (ker_rep_snd_eq_idealSheafDataOfChart B S hS (schemeSpace V) ZV
      (presentationChart (selfPresentation B S hS V))).symm
  have hsupp : ∀ (Zi : ClosedSubspaces B S hS X.1) (v : points B S hS (yoneda.obj V)),
      pointsToScheme B S hS V v ∈ ((BigFppfOver.toScheme B S hS).map
          ((preimageClosedSubspace a Zi).2.2.rep.snd b₀)).ker.support ↔
        pointsMap B S hS (schemeSpace V).1 a.hom v ∈ subspacePointSet B S hS X.1 Zi.1 := by
    intro Zi v
    rw [mem_support_ker_rep_snd_iff B S hS _ (preimageClosedSubspace a Zi).2.2 b₀ v]
    change pointsMap B S hS _ (𝟙 _) v ∈ subspacePointSet B S hS _ (Zi.1.preimage a.hom) ↔ _
    rw [subspacePointSet_preimage, pointsMap_id]
    rfl
  let O : Set (points B S hS X.1) → Set ((BigFppfOver.toScheme B S hS).obj V) :=
    fun P => pointsToScheme B S hS V '' (pointsMap B S hS (schemeSpace V).1 a.hom ⁻¹' P)
  have hO : ∀ P, IsOpen P → IsOpen (O P) := fun P hP =>
    (schemePointsHomeomorph B S hS V).isOpenMap _ (hP.preimage (continuous_pointsMap B S hS a.hom))
  have hdisj : ∀ (Zi : ClosedSubspaces B S hS X.1) (P : Set (points B S hS X.1)),
      Disjoint P (subspacePointSet B S hS X.1 Zi.1) →
        Disjoint (O P) (((BigFppfOver.toScheme B S hS).map
          ((preimageClosedSubspace a Zi).2.2.rep.snd b₀)).ker.support : Set _) := by
    intro Zi P hPZ
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨v, hv, rfl⟩ hs
    exact Set.disjoint_left.1 hPZ hv ((hsupp Zi v).1 hs)
  have hIJ : K₁ * K₂ ≤ ((BigFppfOver.toScheme B S hS).obj V).nilradical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_top,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
      Scheme.IdealSheafData.support_mul]
    intro y _
    obtain ⟨v, rfl⟩ := (bijective_pointsToScheme B S hS V).2 y
    have hv : pointsMap B S hS (schemeSpace V).1 a.hom v ∈
        subspacePointSet B S hS X.1 Z₁.1 ∪ subspacePointSet B S hS X.1 Z₂.1 := by
      rw [hcov]; trivial
    rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_sup]
    rcases hv with hv | hv
    · exact Or.inl ((hsupp Z₁ v).2 hv)
    · exact Or.inr ((hsupp Z₂ v).2 hv)
  obtain ⟨G₁, G₂, hG₁, hG₂, hGd, hGc, hGU₁, hGU₂⟩ :=
    exists_open_partition_reesSituation_relativeProj _ K₁ K₂ hK hIJ ⟨O P₁, hO P₁ hP₁⟩
      ⟨O P₂, hO P₂ hP₂⟩ (hdisj Z₁ P₁ h₁) (hdisj Z₂ P₂ h₂)
  let Φ : points B S hS W.1 → (Stacks.Blowup.reesSituation (reesChartIdeal (centreIdeal ZV)
      (isCartesianOnAffineCharts_centreIdeal ZV) (selfPresentation B S hS V))).relativeProj :=
    fun w => pointsToScheme B S hS _ (pointsMap B S hS W.1 e.hom.hom w)
  have hΦc : Continuous Φ :=
    (schemePointsHomeomorph B S hS _).continuous.comp (continuous_pointsMap B S hS e.hom.hom)
  have hq : e.hom.hom ≫ yoneda.map (reesProjChartHom (centreIdeal ZV)
      (isCartesianOnAffineCharts_centreIdeal ZV) (selfPresentation B S hS V) hcU) = q.hom :=
    congrArg (fun m => m.hom) he
  have hΦ : ∀ w, (Stacks.Blowup.reesSituation (reesChartIdeal (centreIdeal ZV)
      (isCartesianOnAffineCharts_centreIdeal ZV)
      (selfPresentation B S hS V))).relativeProjToBase (Φ w) =
      pointsToScheme B S hS V (pointsMap B S hS W.1 q.hom w) := by
    intro w
    have h1 := pointsToScheme_pointsMap_yoneda B S hS (reesProjChartHom (centreIdeal ZV)
      (isCartesianOnAffineCharts_centreIdeal ZV) (selfPresentation B S hS V) hcU)
      (pointsMap B S hS W.1 e.hom.hom w)
    have h2 := pointsMap_comp_apply B S hS (F := W.1) e.hom.hom (yoneda.map (reesProjChartHom
      (centreIdeal ZV) (isCartesianOnAffineCharts_centreIdeal ZV) (selfPresentation B S hS V)
        hcU)) w
    rw [← hq, h2]
    exact h1.symm
  have hmem : ∀ (P : Set (points B S hS X.1)) (w : points B S hS W.1),
      pointsMap B S hS W.1 (q ≫ a).hom w ∈ P →
        (Stacks.Blowup.reesSituation (reesChartIdeal (centreIdeal ZV)
          (isCartesianOnAffineCharts_centreIdeal ZV)
          (selfPresentation B S hS V))).relativeProjToBase (Φ w) ∈ O P := fun P w hw => by
    rw [hΦ]
    refine ⟨pointsMap B S hS W.1 q.hom w, ?_, rfl⟩
    have hw' : pointsMap B S hS W.1 (q.hom ≫ a.hom) w ∈ P := hw
    rwa [pointsMap_comp_apply] at hw'
  refine ⟨Φ ⁻¹' G₁, Φ ⁻¹' G₂, hG₁.preimage hΦc, hG₂.preimage hΦc, hGd.preimage Φ, ?_,
    fun w hw => hGU₁ (Φ w) (hmem P₁ w hw), fun w hw => hGU₂ (Φ w) (hmem P₂ w hw)⟩
  rw [← Set.preimage_union, hGc, Set.preimage_univ]

/-- **The closure of the inverse image of `U` is open.**
Let `U, V ⊆ X` be disjoint open subspaces, let `Z₁, Z₂ ⊆ X` be closed subspaces with
`|Z₁| = |X| ∖ |U|` and `|Z₂| = |X| ∖ |V|` and finitely presented intersection, and let
`b : X' ⟶ X` be the blowup of `X` in `Z₁ ∩ Z₂`.  Then the closure of the points of `b⁻¹(U)` in
`|X'|` is open. -/
theorem isOpen_closure_subspacePointSet_preimage_of_isBlowupAlong_inf
    {X X' : AlgebraicSpaces B S hS} (Z₁ Z₂ : ClosedSubspaces B S hS X.1)
    (hfp : IsFinitePresentation B S hS (Z₁.1 ⊓ Z₂.1).ι) {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS ⟨Z₁.1 ⊓ Z₂.1, inf_isClosedSubspace B S hS X.1 X.2 Z₁ Z₂⟩ b)
    (U V : OpenSubspaces B S hS X.1)
    (hU : subspacePointSet B S hS X.1 Z₁.1 = (subspacePointSet B S hS X.1 U.1)ᶜ)
    (hV : subspacePointSet B S hS X.1 Z₂.1 = (subspacePointSet B S hS X.1 V.1)ᶜ)
    (hUV : Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 V.1)) :
    IsOpen (closure (subspacePointSet B S hS X'.1 (U.1.preimage b.hom))) := by
  have hcov : subspacePointSet B S hS X.1 Z₁.1 ∪ subspacePointSet B S hS X.1 Z₂.1 =
      Set.univ := by
    rw [hU, hV, ← Set.compl_inter, hUV.inter_eq, Set.compl_empty]
  have hpts : subspacePointSet B S hS X.1 (Z₁.1 ⊓ Z₂.1) =
      (subspacePointSet B S hS X.1 (openSubspaceUnion B S hS X U V).1)ᶜ := by
    rw [subspacePointSet_inf, hU, hV, subspacePointSet_openSubspaceUnion, Set.compl_union]
  have hdense : Dense (subspacePointSet B S hS X'.1 (U.1.preimage b.hom) ∪
      subspacePointSet B S hS X'.1 (V.1.preimage b.hom)) := by
    rw [← subspacePointSet_preimage_openSubspaceUnion B S hS U V b]
    exact dense_subspacePointSet_preimage_of_isBlowupAlong (openSubspaceUnion B S hS X U V)
      ⟨Z₁.1 ⊓ Z₂.1, inf_isClosedSubspace B S hS X.1 X.2 Z₁ Z₂⟩ hb hpts
  let P := presentationOfIsAlgebraicSpace B S hS X.1 X.2
  let a : schemeSpace P.U ⟶ X := ObjectProperty.homMk P.toSpace
  have ha : IsEtale B S hS a.hom := (isEtale_iff_presheaf_of_yoneda B S hS P.toSpace).2 P.etale
  have haS : IsSurjective B S hS a.hom :=
    surjective_pointsMap_of_presheaf_surjective B S hS P.toSpace P.surjective
  have sq := IsPullback.of_hasPullback a b
  have hr : IsEtale B S hS (pullback.snd a b).hom :=
    isEtale_of_isPullback B S hS _ _ a b sq ha
  have hrS : IsSurjective B S hS (pullback.snd a b).hom := isSurjective_of_isPullback B S hS sq haS
  have hro := isOpenMap_pointsMap_of_isEtale B S hS (pullback.snd a b).hom (pullback a b).2
    X'.2 hr
  have hrc := continuous_pointsMap B S hS (pullback.snd a b).hom
  have hw : (pullback.snd a b).hom ≫ b.hom = (pullback.fst a b).hom ≫ a.hom :=
    congrArg (fun m => m.hom) sq.w.symm
  have hpre : ∀ O : OpenSubspaces B S hS X.1,
      pointsMap B S hS _ (pullback.snd a b).hom ⁻¹'
          subspacePointSet B S hS X'.1 (O.1.preimage b.hom) =
        pointsMap B S hS _ (pullback.fst a b ≫ a).hom ⁻¹' subspacePointSet B S hS X.1 O.1 := by
    intro O
    ext w
    rw [Set.mem_preimage, subspacePointSet_preimage, Set.mem_preimage, Set.mem_preimage,
      ← pointsMap_comp_apply, hw]
    rfl
  obtain ⟨G₁, G₂, hG₁, hG₂, hGd, hGc, hGU, hGV⟩ := exists_open_partition_of_isPullback Z₁ Z₂ hfp hb
    hcov (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 V.1)
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS U.1.ι U.2.2)
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS V.1.ι V.2.2)
    (by rw [hU]; exact disjoint_compl_right) (by rw [hV]; exact disjoint_compl_right) P.U ha sq
  rw [← hpre U] at hGU
  rw [← hpre V] at hGV
  set A := pointsMap B S hS _ (pullback.snd a b).hom ⁻¹'
    subspacePointSet B S hS X'.1 (U.1.preimage b.hom) with hA
  set A' := pointsMap B S hS _ (pullback.snd a b).hom ⁻¹'
    subspacePointSet B S hS X'.1 (V.1.preimage b.hom) with hA'
  have hdense' : Dense (A ∪ A') := by
    rw [hA, hA', ← Set.preimage_union]
    exact hdense.preimage hro
  have hcompl : IsCompl G₁ G₂ := .of_eq hGd.eq_bot hGc
  have hG₁c : IsClosed G₁ := by rw [← isOpen_compl_iff, hcompl.compl_eq]; exact hG₂
  have hG₂c : IsClosed G₂ := by rw [← isOpen_compl_iff, hcompl.symm.compl_eq]; exact hG₁
  have hclA : closure A = G₁ := by
    refine Set.Subset.antisymm (closure_minimal hGU hG₁c) fun x hx => ?_
    have hx' : x ∈ closure A ∪ closure A' := by
      rw [← closure_union, hdense'.closure_eq]; trivial
    exact hx'.resolve_right fun hx'' => Set.disjoint_left.1 hGd hx (closure_minimal hGV hG₂c hx'')
  have hT : pointsMap B S hS _ (pullback.snd a b).hom ⁻¹'
      closure (subspacePointSet B S hS X'.1 (U.1.preimage b.hom)) = G₁ := by
    rw [hro.preimage_closure_eq_closure_preimage hrc, ← hA, hclA]
  rw [← Set.image_preimage_eq (closure (subspacePointSet B S hS X'.1 (U.1.preimage b.hom))) hrS,
    hT]
  exact hro _ hG₁

/-! ### Separating two disjoint open subspaces, given two closed subspaces -/

/-- **The complement of a finitely presented closed subspace of a quasi-compact algebraic space
is quasi-compact.** -/
theorem isQuasiCompactSpace_openComplement_of_isFinitePresentation
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (Z : Subfunctor X) (hZ : IsClosedSubspace B S hS Z)
    (hfp : IsFinitePresentation B S hS Z.ι) :
    IsQuasiCompactSpace B S hS (openComplement B S hS Z).toFunctor := by
  have hO := isOpenSubspace_openComplement B S hS hX Z hZ
  refine (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hO.1).2 ?_
  have hemb : Topology.IsOpenEmbedding
      (pointsMap B S hS _ (openComplement B S hS Z).ι) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS _) (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hO.2)
  refine ⟨hemb.isEmbedding.isCompact_iff.2 ?_⟩
  rw [Set.image_univ, range_pointsMap_ι_openComplement]
  obtain ⟨T, f, hTc, hfs, hfe⟩ := hXqc
  have := hTc
  have hfe' := (isEtale_iff_presheaf_of_yoneda B S hS f).1 hfe
  have hKft : ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd f)).ker.IsFiniteType := fun A =>
    fg_ideal_ker_rep_snd_of_isFinitePresentation B S hS (Z := ⟨Z.toFunctor, hZ.1⟩)
      (X := ⟨X, hX⟩) (ObjectProperty.homMk Z.ι) hZ.2 hfp hfe' A
  have hcpt := isCompact_of_isFiniteType_of_support_eq_compl
    ⟨((((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd f)).ker.support : Set _))ᶜ,
      (((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd f)).ker.support.isClosed.isOpen_compl)⟩
    _ hKft (compl_compl _).symm
  have hsurj := surjective_pointsMap_of_presheaf_surjective B S hS f hfs
  have heq : (subspacePointSet B S hS X Z)ᶜ = pointsMap B S hS _ f ''
      (pointsToScheme B S hS T ⁻¹'
        ((((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd f)).ker.support : Set _))ᶜ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := hsurj x
      exact ⟨v, fun hv => hx ((mem_support_ker_rep_snd_iff B S hS Z hZ.2 f v).1 hv), rfl⟩
    · rintro ⟨v, hv, rfl⟩ hx
      exact hv ((mem_support_ker_rep_snd_iff B S hS Z hZ.2 f v).2 hx)
  rw [heq]
  exact ((schemePointsHomeomorph B S hS T).isCompact_preimage.2 hcpt).image
    (continuous_pointsMap B S hS f)

/-- **Separating two open subspaces by an admissible blowup, given two finitely presented closed
subspaces.**  Let `X` be an algebraic space over `S`, let `U, V ⊆ X` be open subspaces and let
`Z₁, Z₂ ⊆ X` be finitely presented closed subspaces with `|Z₁| ∪ |Z₂| = |X|`, `|Z₁|` disjoint
from `|U|` and `|Z₂|` disjoint from `|V|`.  Then there is a `U ∪ V`-admissible blowup
`b : X' ⟶ X` such that `X'` is the disjoint union of two open subspaces `X' = X'₁ ⊔ X'₂` with
`b⁻¹(U) ⊆ X'₁` and `b⁻¹(V) ⊆ X'₂`. -/
theorem exists_isAdmissibleBlowup_disjoint_openSubspace_decomposition_of_closedSubspaces
    {X : AlgebraicSpaces B S hS} (U V : OpenSubspaces B S hS X.1)
    (Z₁ Z₂ : ClosedSubspaces B S hS X.1) (hfp₁ : IsFinitePresentation B S hS Z₁.1.ι)
    (hfp₂ : IsFinitePresentation B S hS Z₂.1.ι)
    (hcov : subspacePointSet B S hS X.1 Z₁.1 ∪ subspacePointSet B S hS X.1 Z₂.1 = Set.univ)
    (hU : Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Z₁.1))
    (hV : Disjoint (subspacePointSet B S hS X.1 V.1) (subspacePointSet B S hS X.1 Z₂.1)) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (X'₁ X'₂ : OpenSubspaces B S hS X'.1),
      IsAdmissibleBlowup B S hS (openSubspaceUnion B S hS X U V) b ∧
        IsClosedSubspace B S hS X'₁.1 ∧ IsClosedSubspace B S hS X'₂.1 ∧
          Disjoint (subspacePointSet B S hS X'.1 X'₁.1)
            (subspacePointSet B S hS X'.1 X'₂.1) ∧
            subspacePointSet B S hS X'.1 X'₁.1 ∪ subspacePointSet B S hS X'.1 X'₂.1
                = Set.univ ∧
              (X'₁.1 ⊔ X'₂.1).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
                X'₁.1 ⊓ X'₂.1
                    = (⊥ : Subfunctor X'.1).sheafify (BigFppfOver.topology B S hS) ∧
                  U.1.preimage b.hom ≤ X'₁.1 ∧ V.1.preimage b.hom ≤ X'₂.1 := by
  let Z : ClosedSubspaces B S hS X.1 := ⟨Z₁.1 ⊓ Z₂.1, inf_isClosedSubspace B S hS X.1 X.2 Z₁ Z₂⟩
  have hZfp : IsFinitePresentation B S hS Z.1.ι :=
    isFinitePresentation_inf B S hS X.2 Z₁.1 Z₂.1 Z₁.2 Z₂.2 Z.2 hfp₁ hfp₂
  have hZdisj : Disjoint (subspacePointSet B S hS X.1 (openSubspaceUnion B S hS X U V).1)
      (subspacePointSet B S hS X.1 Z.1) := by
    rw [subspacePointSet_openSubspaceUnion, subspacePointSet_inf]
    exact Disjoint.union_left (hU.mono_right Set.inter_subset_left)
      (hV.mono_right Set.inter_subset_right)
  let O₁ : OpenSubspaces B S hS X.1 :=
    ⟨openComplement B S hS Z₁.1, isOpenSubspace_openComplement B S hS X.2 Z₁.1 Z₁.2⟩
  let O₂ : OpenSubspaces B S hS X.1 :=
    ⟨openComplement B S hS Z₂.1, isOpenSubspace_openComplement B S hS X.2 Z₂.1 Z₂.2⟩
  have hO₁ : subspacePointSet B S hS X.1 O₁.1 = (subspacePointSet B S hS X.1 Z₁.1)ᶜ :=
    range_pointsMap_ι_openComplement B S hS Z₁.1
  have hO₂ : subspacePointSet B S hS X.1 O₂.1 = (subspacePointSet B S hS X.1 Z₂.1)ᶜ :=
    range_pointsMap_ι_openComplement B S hS Z₂.1
  have hO₁₂ : Disjoint (subspacePointSet B S hS X.1 O₁.1) (subspacePointSet B S hS X.1 O₂.1) := by
    rw [hO₁, hO₂, Set.disjoint_compl_left_iff_subset]
    exact fun x hx => (hcov.ge (Set.mem_univ x)).resolve_right hx
  obtain ⟨X', b, hb⟩ := exists_isBlowupAlong_of_isFinitePresentation Z hZfp
  set T := closure (subspacePointSet B S hS X'.1 (O₁.1.preimage b.hom)) with hT
  have hTo : IsOpen T :=
    isOpen_closure_subspacePointSet_preimage_of_isBlowupAlong_inf Z₁ Z₂ hZfp hb O₁ O₂
      (by rw [hO₁, compl_compl]) (by rw [hO₂, compl_compl]) hO₁₂
  have hTc : IsClosed T := isClosed_closure
  have hopen₁ : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X'.1 T) :=
    isOpenSubspace_openSubspaceOfPoints B S hS X'.2 _ hTo
  have hopen₂ : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X'.1 Tᶜ) :=
    isOpenSubspace_openSubspaceOfPoints B S hS X'.2 _ hTc.isOpen_compl
  have hpts₁ : subspacePointSet B S hS X'.1 (openSubspaceOfPoints B S hS X'.1 T) = T :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hpts₂ : subspacePointSet B S hS X'.1 (openSubspaceOfPoints B S hS X'.1 Tᶜ) = Tᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hadm : IsAdmissibleBlowup B S hS (openSubspaceUnion B S hS X U V) b :=
    isAdmissibleBlowup_of_isBlowupAlong hZfp hZdisj hb
  have hdisj : Disjoint (subspacePointSet B S hS X'.1 (openSubspaceOfPoints B S hS X'.1 T))
      (subspacePointSet B S hS X'.1 (openSubspaceOfPoints B S hS X'.1 Tᶜ)) := by
    rw [hpts₁, hpts₂]
    exact disjoint_compl_right
  have hcover : subspacePointSet B S hS X'.1 (openSubspaceOfPoints B S hS X'.1 T)
      ∪ subspacePointSet B S hS X'.1 (openSubspaceOfPoints B S hS X'.1 Tᶜ) = Set.univ := by
    rw [hpts₁, hpts₂, Set.union_compl_self]
  have hsup : (openSubspaceOfPoints B S hS X'.1 T ⊔ openSubspaceOfPoints B S hS X'.1 Tᶜ).sheafify
      (BigFppfOver.topology B S hS) = ⊤ := by
    rw [sup_comm]
    exact sheafify_sup_openSubspaceOfPoints_eq_top B S hS _ hTo hTc
  have hinf : openSubspaceOfPoints B S hS X'.1 T ⊓ openSubspaceOfPoints B S hS X'.1 Tᶜ
      = (⊥ : Subfunctor X'.1).sheafify (BigFppfOver.topology B S hS) := by
    rw [inf_comm]
    exact inf_openSubspaceOfPoints_eq_sheafify_bot B S hS _
  have hsub₁ : subspacePointSet B S hS X'.1 (U.1.preimage b.hom)
      ⊆ subspacePointSet B S hS X'.1 (openSubspaceOfPoints B S hS X'.1 T) := by
    rw [hpts₁]
    refine subset_trans ?_ subset_closure
    rw [subspacePointSet_preimage, subspacePointSet_preimage, hO₁]
    exact Set.preimage_mono fun x hx => Set.disjoint_left.1 hU hx
  have hsub₂ : subspacePointSet B S hS X'.1 (V.1.preimage b.hom)
      ⊆ subspacePointSet B S hS X'.1 (openSubspaceOfPoints B S hS X'.1 Tᶜ) := by
    rw [hpts₂]
    refine subset_trans ?_ (Set.subset_compl_iff_disjoint_left.mpr
      (Disjoint.closure_left (t := subspacePointSet B S hS X'.1 (O₂.1.preimage b.hom)) ?_ ?_))
    · rw [subspacePointSet_preimage, subspacePointSet_preimage, hO₂]
      exact Set.preimage_mono fun x hx => Set.disjoint_left.1 hV hx
    · rw [subspacePointSet_preimage, subspacePointSet_preimage]
      exact hO₁₂.preimage (pointsMap B S hS X'.1 b.hom)
    · exact isOpen_range_pointsMap_of_isOpenImmersion B S hS (O₂.1.preimage b.hom).ι
        (isOpenSubspace_preimage B S hS b.hom O₂.1 X.2 X'.2 O₂.2).2
  exact ⟨X', b, ⟨_, hopen₁⟩, ⟨_, hopen₂⟩, hadm,
    isClosedSubspace_openSubspaceOfPoints B S hS X'.2 _ hTo hTc,
    isClosedSubspace_openSubspaceOfPoints B S hS X'.2 _ hTc.isOpen_compl hTo.isClosed_compl,
    hdisj, hcover, hsup, hinf, le_of_range_pointsMap_ι_subset B S hS hopen₁ hsub₁,
    le_of_range_pointsMap_ι_subset B S hS hopen₂ hsub₂⟩

end AlgebraicGeometry.Space

end
