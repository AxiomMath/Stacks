module

public import StacksFrontier.AlgebraicGeometry.Blowup.CentreFromGlobalIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteEtaleCoverChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings

/-!
# Spreading a finite étale cover of a closed subspace to a closed subspace of finite presentation

Let `X` be a quasi-compact and quasi-separated algebraic space, `C ⊆ X` a closed subspace,
`W' ⊆ X` a closed subspace of finite presentation and `g : T ⟶ X` a finite morphism of finite
presentation from a scheme. Suppose the base change `T ×_X C ⟶ C` is étale over `C ∖ W'` and
that every point of `C ∖ W'` lies in the image of `g`. Then there is a closed subspace `W ⊇ C` of
finite presentation such that `T ×_X W ⟶ W` is étale over `W ∖ W'` and every point of `W ∖ W'`
lies in the image of `g`.

This is the spreading-out step of Stacks 0GUP. The source obtains it from Noetherian
approximation (Stacks 07SU); here it is read on one affine étale chart `V ⟶ X` with image
`X ∖ W'`: the ideal of `C` on `V` is the union of the ideals of the closed subspaces of finite
presentation containing `C` (Stacks 0829 in the ideal form
`AlgebraicGeometry.Space.exists_isFinitePresentation_le_chartKer`), and étaleness and
surjectivity of the chart of `g` over the ideal of `C` descend to a finitely generated subideal
(`Ideal.exists_fg_le_etale_tensor`, `Ideal.exists_fg_le_surjective_comap_tensor`).

## Main results

* `AlgebraicGeometry.Space.exists_isFinitePresentation_spread`: the statement above.

## References

* [Stacks Project, Tag 0GUP](https://stacks.math.columbia.edu/tag/0GUP)
* [Stacks Project, Tag 07RI](https://stacks.math.columbia.edu/tag/07RI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An étale chart with image the complement of a closed subspace of finite presentation.** -/
theorem exists_affine_chart_openComplement (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) {W' : Subfunctor X} (hW' : IsClosedSubspace B S hS W')
    (hW'fp : IsFinitePresentation B S hS W'.ι) :
    ∃ (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ IsEtale B S hS q ∧
        Set.range (pointsMap B S hS _ q) = (subspacePointSet B S hS X W')ᶜ := by
  have hO := isOpenSubspace_openComplement B S hS hX W' hW'
  obtain ⟨V, f, hV, hfs, hfe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hO.1).1
      (isQuasiCompactSpace_openComplement_of_isFinitePresentation hX hXqc W' hW' hW'fp)
  refine ⟨V, f ≫ (openComplement B S hS W').ι, hV,
    isEtale_comp B S hS hfe (isEtale_ι_of_isOpenSubspace hO), ?_⟩
  have hfs' : Function.Surjective (pointsMap B S hS _ f) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ hO.1 V f).1 hfs
  rw [pointsMap_comp, Set.range_comp, hfs'.range_eq, Set.image_univ,
    range_pointsMap_ι_openComplement]

section Chart

variable {W' : Subfunctor X} {V T Tq : BigFppfOver B S hS} {q : yoneda.obj V ⟶ X}
  {g : yoneda.obj T ⟶ X} {pT : Tq ⟶ V} {iT : yoneda.obj Tq ⟶ yoneda.obj T}

/-- **The condition on a closed subspace, read on the chart.** For an affine étale chart
`q : V ⟶ X` with image `X ∖ W'` and the affine chart `T_q ⟶ V` of `g`, the base change of `g` to a
closed subspace `Z` is étale over `Z ∖ W'`, resp. has every point of `Z ∖ W'` in its image, exactly
when `Γ(V) ⧸ K_Z ⟶ (Γ(V) ⧸ K_Z) ⊗ Γ(T_q)` is étale, resp. surjective on spectra, `K_Z` being the
ideal of the chart of `Z`. -/
theorem etale_and_surjective_iff_chart (hX : IsAlgebraicSpace B S hS X) (hq : IsEtale B S hS q)
    (hqr : Set.range (pointsMap B S hS _ q) = (subspacePointSet B S hS X W')ᶜ)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Tq)]
    (sqT : IsPullback iT (yoneda.map pT) g q)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ((BigFppfOver.toScheme B S hS).obj Tq, ⊤)]
    (hA : algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Tq, ⊤) =
        ((BigFppfOver.toScheme B S hS).map pT).appTop.hom)
    {Z : Subfunctor X} (hZ : IsClosedSubspace B S hS Z) :
    ((∀ t : points B S hS (pullback Z.ι g),
        pointsMap B S hS _ (pullback.fst Z.ι g ≫ Z.ι) t ∉ subspacePointSet B S hS X W' →
          IsEtaleAt B S hS (pullback.fst Z.ι g) t) ↔
      (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
          RingHom.ker ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd q)).appTop.hom)
        (TensorProduct Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
            RingHom.ker ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd q)).appTop.hom)
          Γ((BigFppfOver.toScheme B S hS).obj Tq, ⊤))).Etale) ∧
    (subspacePointSet B S hS X Z \ subspacePointSet B S hS X W' ⊆
        Set.range (pointsMap B S hS _ g) ↔
      Function.Surjective (PrimeSpectrum.comap
        (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
          RingHom.ker ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd q)).appTop.hom)
        (TensorProduct Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
            RingHom.ker ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd q)).appTop.hom)
          Γ((BigFppfOver.toScheme B S hS).obj Tq, ⊤))))) := by
  have hsq := exists_chartSquare (Z := Z) sqT hZ
  obtain ⟨Zq, hsq⟩ := hsq
  obtain ⟨Pq, z, a, b, ζ, k, hsq⟩ := hsq
  obtain ⟨hK, sqZ, hz, sqPZ, sqk⟩ := hsq
  have hring := etale_and_surjective_toScheme_iff (hz := hz) hA sqPZ
  rw [hK] at hring
  have hP : IsAlgebraicSpace B S hS (pullback Z.ι g) :=
    isAlgebraicSpace_pullback B S hS _ _ hZ.1 (isAlgebraicSpace_yoneda B S hS T) hX
  have hζ : IsEtale B S hS ζ :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS sqZ (isAlgebraicSpace_yoneda B S hS Zq) hZ.1
      (isAlgebraicSpace_yoneda B S hS V) hX hq
  -- the points of `Z` over the image of `q` are those in the image of `ζ`
  have hrange : ∀ x : points B S hS Z.toFunctor,
      x ∈ Set.range (pointsMap B S hS _ ζ) ↔
        pointsMap B S hS _ Z.ι x ∉ subspacePointSet B S hS X W' := by
    intro x
    rw [← Set.mem_compl_iff, ← hqr]
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨pointsMap B S hS _ (yoneda.map z) w, ?_⟩
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, sqZ.w]
    · rintro ⟨v, hv⟩
      obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS sqZ x v hv.symm
      exact ⟨w, hw⟩
  refine ⟨?_, ?_⟩
  · rw [← hring.1]
    constructor
    · intro h
      refine etale_toScheme_of_forall_isEtaleAt sqk hZ.1 hP fun t ht => h t ?_
      rw [pointsMap_comp_apply]
      exact (hrange _).1 ht
    · intro hb t ht
      refine isEtaleAt_of_etale_toScheme sqk hZ.1 hP hζ hb t ((hrange _).2 ?_)
      rwa [← pointsMap_comp_apply]
  · rw [← hring.2, ← surjective_toScheme_iff sqk]
    constructor
    · intro h w
      have hx : pointsMap B S hS _ Z.ι (pointsMap B S hS _ ζ w) ∈
          subspacePointSet B S hS X Z \ subspacePointSet B S hS X W' :=
        ⟨⟨_, rfl⟩, (hrange _).1 ⟨w, rfl⟩⟩
      obtain ⟨y, hy⟩ := h hx
      obtain ⟨t, ht, -⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback Z.ι g)
        (pointsMap B S hS _ ζ w) y hy.symm
      exact ⟨t, ht⟩
    · rintro h _ ⟨⟨x, rfl⟩, hx⟩
      obtain ⟨w, rfl⟩ := (hrange x).2 hx
      obtain ⟨t, ht⟩ := h w
      refine ⟨pointsMap B S hS _ (pullback.snd Z.ι g) t, ?_⟩
      rw [← pointsMap_comp_apply, ← pullback.condition, pointsMap_comp_apply, ht]


end Chart

/-- The chart ideal sheaf of a closed subspace on an affine chart, read on global functions, is the
kernel of the global functions of the chart of the closed subspace. -/
theorem chartKer_ideal_top (hX : IsAlgebraicSpace B S hS X) {Z : Subfunctor X}
    (hZ : IsClosedSubspace B S hS Z) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (q : yoneda.obj V ⟶ X) :
    (chartKer B S hS ⟨X, hX⟩ ⟨Z, hZ⟩ q).ideal ⟨⊤, isAffineOpen_top _⟩ =
      RingHom.ker ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd q)).appTop.hom := by
  rw [chartKer, Scheme.Hom.ker_apply]
  rfl

/-- The ideal sheaf `ofIdealTop J` lies below the chart ideal sheaf of a closed
subspace exactly when `J` lies in the kernel of the global functions of its chart. -/
private theorem ofIdealTop_le_chartKer_iff (hX : IsAlgebraicSpace B S hS X) {Z : Subfunctor X}
    (hZ : IsClosedSubspace B S hS Z) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (q : yoneda.obj V ⟶ X)
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop J ≤ chartKer B S hS ⟨X, hX⟩ ⟨Z, hZ⟩ q ↔
      J ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd q)).appTop.hom := by
  rw [← chartKer_ideal_top hX hZ q]
  refine ⟨fun h => by simpa using h ⟨⊤, isAffineOpen_top _⟩, fun h => ?_⟩
  exact Scheme.IdealSheafData.le_of_isAffine (by simpa using h)

/-- **Spreading a finite étale cover of a closed subspace.** Let `X` be quasi-compact and
quasi-separated, `C ⊆ X` closed, `W' ⊆ X` closed of finite presentation and `g : T ⟶ X` finite of
finite presentation from a scheme, such that the base change of `g` to `C` is étale over `C ∖ W'`
and every point of `C ∖ W'` is in the image of `g`. Then there is a closed subspace `W ⊇ C` of
finite presentation with the same two properties. -/
theorem exists_isFinitePresentation_spread (hZ : B.Contains (⊤_ Scheme.{u}))
    (hX : IsAlgebraicSpace B S hS X) (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) {C₀ W' : Subfunctor X}
    (hC₀ : IsClosedSubspace B S hS C₀) (hW' : IsClosedSubspace B S hS W')
    (hW'fp : IsFinitePresentation B S hS W'.ι) {T : BigFppfOver B S hS}
    {g : yoneda.obj T ⟶ X} (hg : IsFinite B S hS g) (hgfp : IsFinitePresentation B S hS g)
    (hét : ∀ t : points B S hS (pullback C₀.ι g),
      pointsMap B S hS _ (pullback.fst C₀.ι g ≫ C₀.ι) t ∉ subspacePointSet B S hS X W' →
        IsEtaleAt B S hS (pullback.fst C₀.ι g) t)
    (hsurj : subspacePointSet B S hS X C₀ \ subspacePointSet B S hS X W' ⊆
      Set.range (pointsMap B S hS _ g)) :
    ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
      C₀ ≤ W ∧
      (∀ t : points B S hS (pullback W.ι g),
        pointsMap B S hS _ (pullback.fst W.ι g ≫ W.ι) t ∉ subspacePointSet B S hS X W' →
          IsEtaleAt B S hS (pullback.fst W.ι g) t) ∧
      subspacePointSet B S hS X W \ subspacePointSet B S hS X W' ⊆
        Set.range (pointsMap B S hS _ g) := by
  obtain ⟨V, q, hV, hq, hqr⟩ := exists_affine_chart_openComplement hX hXqc hW' hW'fp
  have := hV
  obtain ⟨Tq, pT, iT, hTq, hpT, sqT⟩ := hg V hV q
  have := hTq
  let Tsch := BigFppfOver.toScheme B S hS
  let : Algebra Γ(Tsch.obj V, ⊤) Γ(Tsch.obj Tq, ⊤) := (Tsch.map pT).appTop.hom.toAlgebra
  have hA : algebraMap Γ(Tsch.obj V, ⊤) Γ(Tsch.obj Tq, ⊤) = (Tsch.map pT).appTop.hom := rfl
  -- the chart algebra is of finite presentation
  have hfp : Algebra.FinitePresentation Γ(Tsch.obj V, ⊤) Γ(Tsch.obj Tq, ⊤) := by
    have hfpT : IsFinitePresentation B S hS (yoneda.map pT) :=
      IsFinitePresentation.of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS Tq)
        (isAlgebraicSpace_yoneda B S hS T) (isAlgebraicSpace_yoneda B S hS V) hX sqT hgfp
    have hid : ∀ W : BigFppfOver B S hS, (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) Tsch).presheaf
          (𝟙 (yoneda.obj W)) := fun W =>
      (isEtale_iff_presheaf_of_yoneda B S hS (𝟙 (yoneda.obj W))).1 (isEtale_id B S hS _)
    have hlfp : LocallyOfFinitePresentation (Tsch.map pT) :=
      hfpT.1 Tq V (𝟙 _) (𝟙 _) pT (hid Tq) (hid V) (by simp)
    rw [← RingHom.finitePresentation_algebraMap, hA]
    exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1 hlfp
  -- the conditions on `C₀`, read on rings
  have hC := etale_and_surjective_iff_chart hX hq hqr sqT hA hC₀
  obtain ⟨J₁, hJ₁⟩ := Ideal.exists_fg_le_etale_tensor _ hfp (hC.1.1 hét)
  obtain ⟨J₂, hJ₂⟩ := Ideal.exists_fg_le_surjective_comap_tensor _ hfp (hC.2.1 hsurj)
  let J : Ideal Γ(Tsch.obj V, ⊤) := J₁.1 ⊔ J₂.1
  have hJ₀C := (ofIdealTop_le_chartKer_iff hX hC₀ q J).2 (sup_le J₁.2.2 J₂.2.2)
  obtain ⟨W, hWfp, hC₀W, hJW⟩ := exists_isFinitePresentation_le_chartKer B S hS hZ ⟨X, hX⟩ hXqc hXqs
    ⟨C₀, hC₀⟩ q ((isEtale_iff_presheaf_of_yoneda B S hS q).1 hq) _
    (Scheme.IdealSheafData.isFiniteType_ofIdealTop (Submodule.FG.sup J₁.2.1 J₂.2.1)) hJ₀C
  have hJW' := (ofIdealTop_le_chartKer_iff hX W.2 q J).1 hJW
  have hW := etale_and_surjective_iff_chart hX hq hqr sqT hA W.2
  exact ⟨W.1, W.2, hWfp, hC₀W, hW.1.2 (Ideal.etale_tensor_of_le (le_sup_left.trans hJW') hJ₁),
    hW.2.2 (Ideal.surjective_comap_tensor_of_le (le_sup_right.trans hJW') hJ₂)⟩

end AlgebraicGeometry.Space

end
