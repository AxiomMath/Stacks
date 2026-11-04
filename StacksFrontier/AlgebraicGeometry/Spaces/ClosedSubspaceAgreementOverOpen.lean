module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent

/-!
# Two closed subspaces agreeing over an open subspace

Let `C ⊆ T` be closed subspaces of an algebraic space `P` and `Ω ⊆ P` an open subspace. If the
two closed subspaces have the same base change to an étale chart of `P` covering `Ω`, they agree
over `Ω`; in the situation of Stacks 0GUN this is how the closed subspace of finite presentation
`T` produced from a closed subspace `C` keeps the finite étale locus of `C ⟶ X`.

The chart condition is the one that
`AlgebraicGeometry.Space.exists_isFinitePresentation_disjoint_le_chartKer` can impose: the ideal
of `C` on a quasi-compact étale chart is contained in the ideal of `T`, and that ideal is of finite
type when `C` is finite étale and `P` is finite and of finite presentation over the open subspace
of the base the chart covers.

## Main results

* `AlgebraicGeometry.Space.inf_le_of_preimage_le`: agreement over `Ω`.
* `AlgebraicGeometry.Space.isFinite_isEtale_pullback_fst_of_inf_le`: the finite étale locus
  passes from `C` to `T`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Closed subspaces with the same base change to a chart covering `Ω` agree over `Ω`.** If
`φ : h_U ⟶ P` lands in the subfunctor `Ω` and is locally surjective onto it, and the base change
of `T` to `U` is contained in that of `C`, then `T ∩ Ω ⊆ C`. A section of `T ∩ Ω` is locally the
image of a section of `U`, which then lies in the base change of `T`, hence of `C`; and `C` is a
sheaf. -/
theorem inf_le_of_preimage_le (P : AlgebraicSpaces B S hS) (T C : ClosedSubspaces B S hS P.1)
    (Ω : Subfunctor P.1) {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ P.1)
    (hφΩ : Subfunctor.range φ ≤ Ω)
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Subfunctor.lift φ hφΩ))
    (h : T.1.preimage φ ≤ C.1.preimage φ) : T.1 ⊓ Ω ≤ C.1 := by
  have hPsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) P.1 :=
    (isSheaf_iff_isSheaf_of_type _ _).1 P.2.isSheaf
  have hCsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) C.1.toFunctor :=
    (isSheaf_iff_isSheaf_of_type _ _).1 C.2.1.isSheaf
  have hGC : (C.1.preimage φ).image φ ≤ C.1 := (Subfunctor.image_le_iff _ _ _).2 le_rfl
  refine le_trans ?_ (Subfunctor.sheafify_le _ _ hGC hPsh hCsh)
  rintro Z x ⟨hxT, hxΩ⟩
  show ((C.1.preimage φ).image φ).sieveOfSection x ∈ BigFppfOver.topology B S hS Z.unop
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) (Subfunctor.lift φ hφΩ)
      (⟨x, hxΩ⟩ : Ω.toFunctor.obj Z))
  rintro Z' f ⟨y, hy⟩
  have hφy : φ.app _ y = P.1.map f.op x := congrArg Subtype.val hy
  refine ⟨y, h _ ?_, hφy⟩
  show φ.app _ y ∈ T.1.obj _
  rw [hφy]
  exact T.1.map f.op hxT

/-- **The finite étale locus passes to a larger closed subspace agreeing over it.** If `C ⊆ T`
are closed subspaces of `P`, `q : P ⟶ X`, and `T ∩ q⁻¹U ⊆ C` for an open subspace `U ⊆ X`, then
`T ⟶ X` is finite and étale over `U` as soon as `C ⟶ X` is. -/
theorem isFinite_isEtale_pullback_fst_of_inf_le {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : P ⟶ X) (U : Subfunctor X)
    (T C : Subfunctor P) (hCT : C ≤ T) (h : T ⊓ U.preimage q ≤ C)
    (hfin : IsFinite B S hS (pullback.fst U.ι (C.ι ≫ q)))
    (het : IsEtale B S hS (pullback.fst U.ι (C.ι ≫ q))) :
    IsFinite B S hS (pullback.fst U.ι (T.ι ≫ q)) ∧
      IsEtale B S hS (pullback.fst U.ι (T.ι ≫ q)) := by
  have hrange : Subfunctor.range (pullback.snd U.ι (T.ι ≫ q) ≫ T.ι) ≤ C := by
    rintro Z _ ⟨w, rfl⟩
    refine h Z ⟨((pullback.snd U.ι (T.ι ≫ q)).app Z w).2, ?_⟩
    show (pullback.snd U.ι (T.ι ≫ q) ≫ T.ι ≫ q).app Z w ∈ U.obj Z
    rw [← pullback.condition]
    exact ((pullback.fst U.ι (T.ι ≫ q)).app Z w).2
  let s : pullback U.ι (T.ι ≫ q) ⟶ C.toFunctor :=
    Subfunctor.lift (pullback.snd U.ι (T.ι ≫ q) ≫ T.ι) hrange
  have hs : s ≫ C.ι = pullback.snd U.ι (T.ι ≫ q) ≫ T.ι := Subfunctor.lift_ι _ _
  let inv' : pullback U.ι (T.ι ≫ q) ⟶ pullback U.ι (C.ι ≫ q) :=
    pullback.lift (pullback.fst U.ι (T.ι ≫ q)) s (by
      rw [pullback.condition, ← Category.assoc, ← hs, Category.assoc])
  let m : pullback U.ι (C.ι ≫ q) ⟶ pullback U.ι (T.ι ≫ q) :=
    pullback.lift (pullback.fst U.ι (C.ι ≫ q))
      (pullback.snd U.ι (C.ι ≫ q) ≫ Subfunctor.homOfLe hCT) (by
        rw [pullback.condition, Category.assoc, ← Category.assoc (Subfunctor.homOfLe hCT),
          Subfunctor.homOfLe_ι])
  have hinv : IsIso inv' := by
    refine ⟨⟨m, ?_, ?_⟩⟩
    · apply pullback.hom_ext
      · simp only [m, inv', Category.assoc, pullback.lift_fst, Category.id_comp]
      · rw [← cancel_mono T.ι]
        simp only [m, inv', Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Subfunctor.homOfLe_ι, Category.id_comp]
        rw [hs]
    · apply pullback.hom_ext
      · simp only [m, inv', Category.assoc, pullback.lift_fst, Category.id_comp]
      · rw [← cancel_mono C.ι]
        simp only [m, inv', Category.assoc, pullback.lift_snd, Category.id_comp]
        rw [hs, pullback.lift_snd_assoc, Category.assoc, Subfunctor.homOfLe_ι]
  have hfac : pullback.fst U.ι (T.ι ≫ q) = inv' ≫ pullback.fst U.ι (C.ι ≫ q) :=
    (pullback.lift_fst _ _ _).symm
  rw [hfac]
  exact ⟨isFinite_comp B S hS (isFinite_of_isIso B S hS inv') hfin,
    isEtale_comp B S hS (isEtale_of_isIso B S hS inv') het⟩

/-- **An affine étale chart of `P` covering the part over a quasi-compact open subspace of the
base.** For an affine `q : P ⟶ X` locally of finite presentation and a quasi-compact open subspace
`U ⊆ X`, the base change of an
affine étale surjective chart `U₀ ⟶ U` is an affine étale chart `φ : Ũ ⟶ P` which lands in
`q⁻¹U` and is locally surjective onto it. -/
theorem exists_chart_over_openSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (P : AlgebraicSpaces B S hS) (q : P.1 ⟶ X)
    (hqa : IsAffineHom B S hS q) (hqlfp : IsLocallyOfFinitePresentation B S hS q)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (U₀ Ũ : BigFppfOver B S hS) (u₀ : yoneda.obj U₀ ⟶ U.toFunctor) (π : Ũ ⟶ U₀)
      (φ : yoneda.obj Ũ ⟶ P.1) (hφΩ : Subfunctor.range φ ≤ U.preimage q),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Ũ) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map π) ∧
      IsEtale B S hS u₀ ∧ IsPullback φ (yoneda.map π) q (u₀ ≫ U.ι) ∧ IsEtale B S hS φ ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Subfunctor.lift φ hφΩ) := by
  obtain ⟨U₀, u₀, hU₀aff, hu₀s, hu₀e⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS U.toFunctor hU.1).1 hUqc
  have hqaff := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS q P.2 hX).out 2 1).mp hqa
  have hqrep : yoneda.relativelyRepresentable q := hqaff.2.rep
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) := hU₀aff
  let Ũ := hqrep.pullback (u₀ ≫ U.ι)
  let π := hqrep.snd (u₀ ≫ U.ι)
  let φ := hqrep.fst (u₀ ≫ U.ι)
  have hsq : IsPullback φ (yoneda.map π) q (u₀ ≫ U.ι) := hqrep.isPullback _
  have hŨaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Ũ) :=
    @isAffine_of_isAffineHom _ _ ((BigFppfOver.toScheme B S hS).map π)
      (hqaff.2.property (u₀ ≫ U.ι) φ π hsq) hU₀aff
  have hŨalg := isAlgebraicSpace_yoneda B S hS Ũ
  have hue := isEtale_comp B S hS hu₀e (isEtale_ι_of_isOpenSubspace hU)
  have hφ : IsEtale B S hS φ :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsq hŨalg P.2
      (isAlgebraicSpace_yoneda B S hS U₀) hX hue
  have hπfin : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map π) := by
    have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map π) :=
      hqlfp Ũ U₀ φ (u₀ ≫ U.ι) π ((isEtale_iff_presheaf_of_yoneda B S hS φ).1 hφ)
        ((isEtale_iff_presheaf_of_yoneda B S hS _).1 hue) hsq.w.symm
    infer_instance
  have hφΩ : Subfunctor.range φ ≤ U.preimage q := by
    rintro Z _ ⟨x, rfl⟩
    show (φ ≫ q).app Z x ∈ U.obj Z
    rw [hsq.w]
    exact ((u₀.app Z) ((yoneda.map π).app Z x)).2
  have hΩ : IsOpenSubspace B S hS (U.preimage q) :=
    isOpenSubspace_preimage B S hS q U hX P.2 hU
  have hlift : Subfunctor.lift φ hφΩ ≫ (U.preimage q).ι = φ := Subfunctor.lift_ι _ _
  have hlet : IsEtale B S hS (Subfunctor.lift φ hφΩ) :=
    isEtale_of_isEtale_over B S hS hŨalg hΩ.1 P.2 _ φ _ hφ (isEtale_ι_of_isOpenSubspace hΩ) hlift
  have hlsurj : IsSurjective B S hS (Subfunctor.lift φ hφΩ) := by
    intro p
    obtain ⟨uU, x, hux⟩ : ∃ (uU : points B S hS U.toFunctor) (x : points B S hS P.1),
        pointsMap B S hS _ U.ι uU = pointsMap B S hS _ q x ∧
          pointsMap B S hS _ (U.preimage q).ι p = x := by
      refine ⟨pointsMap B S hS _ (U.fromPreimage q) p, _, ?_, rfl⟩
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
    obtain ⟨u, hu⟩ := isSurjective_of_presheafSurjective B S hS u₀ hu₀s uU
    obtain ⟨ũ, hũ, -⟩ := exists_points_of_isPullback B S hS hsq x u
      (by rw [pointsMap_comp_apply, hu, hux.1])
    refine ⟨ũ, pointsMap_injective_of_mono B S hS (U.preimage q).ι ?_⟩
    rw [← pointsMap_comp_apply, hlift, hũ, hux.2]
  exact ⟨U₀, Ũ, u₀, π, φ, hφΩ, hU₀aff, hŨaff, hπfin, hu₀e, hsq, hφ,
    isLocallySurjective_of_surjective_flat_locallyOfFinitePresentation B S hS hŨalg hΩ.1 _
      hlsurj (isFlat_of_isEtale B S hS hlet) (isLocallyOfFinitePresentation_of_isEtale B S hS hlet)⟩

/-- **The ideal of a closed subspace finite étale over `U` is of finite type on a chart over
`U`.** In the situation of `AlgebraicGeometry.Space.exists_chart_over_openSubspace`, if
`C ⟶ X` is finite étale over `U` then the base change of `C` to the chart `Ũ` is étale over the
affine `U₀`, while `Ũ` is finite over `U₀`; so the closed immersion into `Ũ` is of finite
presentation and its ideal is of finite type. -/
theorem isFiniteType_chartKer_of_isEtale_pullback_fst {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (P : AlgebraicSpaces B S hS) (q : P.1 ⟶ X)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U) {U₀ Ũ : BigFppfOver B S hS}
    (u₀ : yoneda.obj U₀ ⟶ U.toFunctor) (π : Ũ ⟶ U₀) (φ : yoneda.obj Ũ ⟶ P.1)
    (hπ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map π))
    (hsq : IsPullback φ (yoneda.map π) q (u₀ ≫ U.ι)) (C : ClosedSubspaces B S hS P.1)
    (het : IsEtale B S hS (pullback.fst U.ι (C.1.ι ≫ q))) :
    (chartKer B S hS P C φ).IsFiniteType := by
  let Z := C.2.2.rep.pullback φ
  let i := C.2.2.rep.snd φ
  have big : IsPullback (C.2.2.rep.fst φ) (yoneda.map i ≫ yoneda.map π) (C.1.ι ≫ q)
      (u₀ ≫ U.ι) := (C.2.2.rep.isPullback φ).paste_vert hsq
  have hcond : (yoneda.map i ≫ yoneda.map π ≫ u₀) ≫ U.ι = C.2.2.rep.fst φ ≫ C.1.ι ≫ q := by
    simpa only [Category.assoc] using big.w.symm
  let k : yoneda.obj Z ⟶ pullback U.ι (C.1.ι ≫ q) :=
    pullback.lift (yoneda.map i ≫ yoneda.map π ≫ u₀) (C.2.2.rep.fst φ) hcond
  have hk : k ≫ pullback.snd U.ι (C.1.ι ≫ q) = C.2.2.rep.fst φ := pullback.lift_snd _ _ _
  have hleft : IsPullback k (yoneda.map i ≫ yoneda.map π) (pullback.fst U.ι (C.1.ι ≫ q)) u₀ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd U.ι (C.1.ι ≫ q)) (h₂₂ := U.ι) ?_ ?_
      (IsPullback.of_hasPullback U.ι (C.1.ι ≫ q)).flip
    · rwa [hk]
    · rw [pullback.lift_fst, Category.assoc]
  have hCalg : IsAlgebraicSpace B S hS (pullback U.ι (C.1.ι ≫ q)) :=
    isAlgebraicSpace_pullback B S hS _ _ hU.1 C.2.1 hX
  have hv : IsEtale B S hS (yoneda.map (i ≫ π)) := by
    rw [Functor.map_comp]
    exact isEtale_of_isPullback_of_isAlgebraicSpace B S hS hleft.flip
      (isAlgebraicSpace_yoneda B S hS Z) (isAlgebraicSpace_yoneda B S hS U₀) hCalg hU.1 het
  have hEt : Etale ((BigFppfOver.toScheme B S hS).map (i ≫ π)) :=
    etale_of_isEtale_yoneda_map B S hS hv
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) :=
    C.2.2.property_snd φ
  have _ : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map i ≫ (BigFppfOver.toScheme B S hS).map π) := by
    rw [← Functor.map_comp]
    infer_instance
  have _ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map i) :=
    locallyOfFinitePresentation_of_comp _ ((BigFppfOver.toScheme B S hS).map π)
  exact isFiniteType_ker_of_finitePresentation _ ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Space

end
