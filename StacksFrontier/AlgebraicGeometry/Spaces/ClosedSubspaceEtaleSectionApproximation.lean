module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationClosedAvoidance
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedUnionPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion

/-!
# Étale charts which become open immersions on a closed subspace of finite presentation

Let `P` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, let
`g_j : h_{Γ_j} ⟶ P` be finitely many étale morphisms from quasi-compact schemes, and let `C ⊆ P`
be a closed subspace such that

1. over `C` each `g_j` is a monomorphism: a pair of points of `Γ_j` with the same image in `C`
   lies on the diagonal of `Γ_j ×_P Γ_j`, and
2. the images of the `g_j` cover `|C|`.

Then a closed subspace `T ⊇ C` of finite presentation can be chosen with the same two properties,
and on such a `T` the restrictions `g_j^{-1}(T) ⟶ T` are open immersions from schemes covering
`T`. In particular `T` is a scheme.

This is the step of Stacks 0GUN that replaces the source's appeal to Stacks 07SR, 0827 and 04AK
along a limit of algebraic spaces: the diagonal of an étale morphism is an open immersion, so the
pairs off the diagonal form a closed, hence quasi-compact, set whose image in `|P|` misses `|C|`;
a closed subspace of finite presentation containing `C` and missing that image exists by
`AlgebraicGeometry.Space.exists_isFinitePresentation_disjoint_le_chartKer`.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleSectionClosed`: the two properties above.

## Main results

* `AlgebraicGeometry.Space.exists_isFinitePresentation_isEtaleSectionClosed`: the approximation.
* `AlgebraicGeometry.Space.isOpenImmersion_fromPreimage_of_isEtaleSectionClosed`: the
  restrictions are open immersions.
* `AlgebraicGeometry.Space.isRepresentable_of_isEtaleSectionClosed`: `T` is a scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

section

variable {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n : ℕ} {Γ : Fin n → BigFppfOver B S hS}
  (g : ∀ j, yoneda.obj (Γ j) ⟶ P)

/-- **A closed subspace on which finitely many étale charts are monomorphisms covering it.**
For every `j` the pairs of points of `Γ_j` with the same image in `T` lie on the diagonal of
`Γ_j ×_P Γ_j`, and the images of the `g_j` cover the points of `T`. -/
def IsEtaleSectionClosed (T : Subfunctor P) : Prop :=
  (∀ j, T.preimage (pullback.fst (g j) (g j) ≫ g j) ≤
      Subfunctor.range (pullback.diagonal (g j))) ∧
    Set.range (pointsMap B S hS T.toFunctor T.ι) ⊆
      ⋃ j, Set.range (pointsMap B S hS (yoneda.obj (Γ j)) (g j))

end

/-- **The approximation.** If a closed subspace `C` of a quasi-compact quasi-separated algebraic
space `P` has the two properties of `IsEtaleSectionClosed` for finitely many étale charts with
quasi-compact sources, so has some closed subspace `T ⊇ C` of finite presentation, which can in
addition be asked to satisfy a chart condition satisfied by `C`. -/
theorem exists_isFinitePresentation_isEtaleSectionClosed (P : AlgebraicSpaces B S hS)
    (hPqc : IsQuasiCompactSpace B S hS P.1) (hPqs : IsAbsolutelyQuasiSeparated B S hS hZ P.1)
    {n : ℕ} {Γ : Fin n → BigFppfOver B S hS}
    (hΓ : ∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (Γ j)))
    (g : ∀ j, yoneda.obj (Γ j) ⟶ P.1) (hg : ∀ j, IsEtale B S hS (g j))
    (C : ClosedSubspaces B S hS P.1) (hC : IsEtaleSectionClosed B S hS g C.1)
    {m : ℕ} {U : Fin m → BigFppfOver B S hS}
    [∀ i, CompactSpace ((BigFppfOver.toScheme B S hS).obj (U i))]
    (φ : ∀ i, yoneda.obj (U i) ⟶ P.1)
    (hφ : ∀ i, MorphismProperty.presheaf (MorphismProperty.inverseImage @Etale
      (BigFppfOver.toScheme B S hS)) (φ i))
    (J₀ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (U i)).IdealSheafData)
    (hJ₀ : ∀ i, (J₀ i).IsFiniteType) (hJ₀C : ∀ i, J₀ i ≤ chartKer B S hS P C (φ i)) :
    ∃ T : ClosedSubspaces B S hS P.1, IsFinitePresentation B S hS T.1.ι ∧ C.1 ≤ T.1 ∧
      IsEtaleSectionClosed B S hS g T.1 ∧ ∀ i, J₀ i ≤ chartKer B S hS P T (φ i) := by
  classical
  have hΓalg : ∀ j, IsAlgebraicSpace B S hS (yoneda.obj (Γ j)) := fun j =>
    isAlgebraicSpace_yoneda B S hS _
  have hQalg : ∀ j, IsAlgebraicSpace B S hS (pullback (g j) (g j)) := fun j =>
    isAlgebraicSpace_pullback B S hS _ _ (hΓalg j) (hΓalg j) P.2
  have hD : ∀ j, IsOpenImmersion B S hS (pullback.diagonal (g j)) := fun j =>
    isOpenImmersion_diagonal_of_isUnramified B S hS (hΓalg j) P.2 (g j)
      (isUnramified_of_isEtale B S hS (hg j))
  have hQcpt : ∀ j, CompactSpace (points B S hS (pullback (g j) (g j))) := fun j =>
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ (hQalg j)).1
      (isQuasiCompactSpace_pullback B S hS hZ (g j) (g j) (hΓalg j) P.2
        (isQuasiCompactSpace_yoneda B S hS _ (hΓ j))
        (isQuasiCompactSpace_yoneda B S hS _ (hΓ j)) hPqs)
  -- The pairs off the diagonal, and their images in `|P|`.
  let ρ : ∀ j, pullback (g j) (g j) ⟶ P.1 := fun j => pullback.fst (g j) (g j) ≫ g j
  let Bad : ∀ j, Set (points B S hS (pullback (g j) (g j))) := fun j =>
    (Set.range (pointsMap B S hS _ (pullback.diagonal (g j))))ᶜ
  have hBad : ∀ j, IsCompact (Bad j) := fun j =>
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hD j)).isClosed_compl.isCompact
  let K₁ : Set (points B S hS P.1) := ⋃ j, pointsMap B S hS _ (ρ j) '' Bad j
  let K₂ : Set (points B S hS P.1) := (⋃ j, Set.range (pointsMap B S hS _ (g j)))ᶜ
  have hPcpt : CompactSpace (points B S hS P.1) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ P.2).1 hPqc
  have hK₁ : IsCompact K₁ :=
    isCompact_iUnion fun j => (hBad j).image (continuous_pointsMap B S hS (ρ j))
  have hK₂ : IsCompact K₂ :=
    (isOpen_iUnion fun j => isOpen_range_pointsMap_of_isEtale B S hS (g j) (hΓalg j) P.2
      (hg j)).isClosed_compl.isCompact
  -- A point of `|P|` coming from a pair off the diagonal lies off a closed subspace with
  -- property (1).
  have hoff : ∀ (T : Subfunctor P.1),
      (∀ j, T.preimage (ρ j) ≤ Subfunctor.range (pullback.diagonal (g j))) →
      Disjoint K₁ (Set.range (pointsMap B S hS T.toFunctor T.ι)) := by
    intro T hT
    rw [Set.disjoint_left]
    rintro x hx hxT
    obtain ⟨j, β, hβ, rfl⟩ := Set.mem_iUnion.1 hx
    have hβ' : β ∈ Set.range (pointsMap B S hS (T.preimage (ρ j)).toFunctor
        (T.preimage (ρ j)).ι) := by
      rwa [range_pointsMap_preimage_ι]
    have := range_pointsMap_ι_le B S hS (hT j) hβ'
    rw [range_pointsMap_ι_range] at this
    exact hβ this
  have hKC : Disjoint (K₁ ∪ K₂) (Set.range (pointsMap B S hS C.1.toFunctor C.1.ι)) :=
    (hoff C.1 hC.1).union_left (Set.disjoint_left.2 fun _ hx hxC => hx (hC.2 hxC))
  obtain ⟨T, hTfp, hCT, hKT, hJT⟩ := exists_isFinitePresentation_disjoint_le_chartKer B S hS hZ P
    hPqc hPqs C (K₁ ∪ K₂) (hK₁.union hK₂) hKC φ hφ J₀ hJ₀ hJ₀C
  refine ⟨T, hTfp, hCT, ⟨fun j => ?_, ?_⟩, hJT⟩
  · refine le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_range_of_isAlgebraicSpace B S hS (hΓalg j) _ (hD j)) ?_
    rw [range_pointsMap_preimage_ι, range_pointsMap_ι_range]
    intro β hβ
    by_contra hβD
    exact Set.disjoint_left.1 hKT (Or.inl (Set.mem_iUnion.2 ⟨j, β, hβD, rfl⟩)) hβ
  · intro x hxT
    by_contra hx
    exact Set.disjoint_left.1 hKT (Or.inr hx) hxT

/-! ### The restrictions are open immersions -/

/-- **Over a closed subspace with property (1), the restriction of an étale chart is a
monomorphism.** Two sections of `g^{-1}(T)` with the same image in `T` form a section of
`Γ ×_P Γ` lying over `T`, hence on the diagonal. -/
theorem mono_fromPreimage_of_preimage_le_range_diagonal {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Γ : BigFppfOver B S hS} (g : yoneda.obj Γ ⟶ P) (T : Subfunctor P)
    (h : T.preimage (pullback.fst g g ≫ g) ≤ Subfunctor.range (pullback.diagonal g)) :
    Mono (T.fromPreimage g) := by
  rw [NatTrans.mono_iff_mono_app]
  intro Z
  rw [mono_iff_injective]
  intro x y hxy
  have hval : g.app Z x.1 = g.app Z y.1 := congrArg Subtype.val hxy
  let s : yoneda.obj Z.unop ⟶ yoneda.obj Γ := yoneda.map x.1
  let t : yoneda.obj Z.unop ⟶ yoneda.obj Γ := yoneda.map y.1
  have hst : s ≫ g = t ≫ g := by
    apply yonedaEquiv.injective
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
  let w := yonedaEquiv (pullback.lift s t hst)
  have hw : w ∈ (T.preimage (pullback.fst g g ≫ g)).obj Z := by
    show (pullback.fst g g ≫ g).app Z w ∈ T.obj Z
    rw [← yonedaEquiv_comp, pullback.lift_fst_assoc, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact x.2
  obtain ⟨v, hv⟩ := h Z hw
  have h1 : (pullback.fst g g).app Z w = x.1 := by
    rw [← yonedaEquiv_comp, pullback.lift_fst, yonedaEquiv_yoneda_map]
  have h2 : (pullback.snd g g).app Z w = y.1 := by
    rw [← yonedaEquiv_comp, pullback.lift_snd, yonedaEquiv_yoneda_map]
  have h3 : (pullback.fst g g).app Z w = (pullback.snd g g).app Z w := by
    rw [← hv]
    show (pullback.diagonal g ≫ pullback.fst g g).app Z v =
      (pullback.diagonal g ≫ pullback.snd g g).app Z v
    rw [pullback.diagonal_fst, pullback.diagonal_snd]
  exact Subtype.ext (h1.symm.trans (h3.trans h2))

/-- **Over a closed subspace with property (1), the restriction of an étale chart is an open
immersion**: it is étale, being a base change of the chart, and a monomorphism. -/
theorem isOpenImmersion_fromPreimage_of_preimage_le_range_diagonal (P : AlgebraicSpaces B S hS)
    {Γ : BigFppfOver B S hS} (g : yoneda.obj Γ ⟶ P.1) (hg : IsEtale B S hS g)
    (T : ClosedSubspaces B S hS P.1)
    (h : T.1.preimage (pullback.fst g g ≫ g) ≤ Subfunctor.range (pullback.diagonal g)) :
    IsOpenImmersion B S hS (T.1.fromPreimage g) := by
  have hA : IsAlgebraicSpace B S hS (T.1.preimage g).toFunctor :=
    (isClosedSubspace_preimage_yoneda B S hS P g T).1
  exact isOpenImmersion_of_isEtale_of_mono B S hS _ hA T.2.1
    (isEtale_of_isPullback_of_isAlgebraicSpace B S hS (Subfunctor.isPullback_preimage g T.1) hA
      T.2.1 (isAlgebraicSpace_yoneda B S hS Γ) P.2 hg)
    (mono_fromPreimage_of_preimage_le_range_diagonal B S hS g T.1 h)

/-- The preimage of a closed subspace along a morphism from a scheme is a scheme. -/
theorem isRepresentable_preimage_yoneda {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Γ : BigFppfOver B S hS} (g : yoneda.obj Γ ⟶ P) (T : Subfunctor P)
    (hT : IsClosedImmersion B S hS T.ι) :
    (T.preimage g).toFunctor.IsRepresentable := by
  have _ : Mono (yoneda.map (hT.rep.snd g)) := (hT.rep.isPullback g).mono_snd_of_mono
  exact Functor.IsRepresentable.mk' ((asIso (Subfunctor.toRange (yoneda.map (hT.rep.snd g)))) ≪≫
    eqToIso (congrArg Subfunctor.toFunctor (range_yoneda_snd_eq_preimage B S hS g hT.rep)))

/-- The points of a closed subspace with property (2) are covered by the restrictions of the
charts. -/
theorem exists_fromPreimage_point_of_isEtaleSectionClosed {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {n : ℕ} {Γ : Fin n → BigFppfOver B S hS} (g : ∀ j, yoneda.obj (Γ j) ⟶ P) (T : Subfunctor P)
    (hT : IsEtaleSectionClosed B S hS g T) (t : points B S hS T.toFunctor) :
    ∃ j, ∃ w : points B S hS (T.preimage (g j)).toFunctor,
      pointsMap B S hS _ (T.fromPreimage (g j)) w = t := by
  obtain ⟨j, γ, hγ⟩ := Set.mem_iUnion.1 (hT.2 ⟨t, rfl⟩)
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
    (Subfunctor.isPullback_preimage (g j) T) t γ hγ.symm
  exact ⟨j, w, hw⟩

/-- **A closed subspace with the two properties is a scheme**: it is covered by the open
immersions `g_j^{-1}(T) ⟶ T` from schemes. -/
theorem isRepresentable_of_isEtaleSectionClosed (P : AlgebraicSpaces B S hS) {n : ℕ}
    {Γ : Fin n → BigFppfOver B S hS} (g : ∀ j, yoneda.obj (Γ j) ⟶ P.1)
    (hg : ∀ j, IsEtale B S hS (g j)) (T : ClosedSubspaces B S hS P.1)
    (hT : IsEtaleSectionClosed B S hS g T.1) :
    T.1.toFunctor.IsRepresentable := by
  have _ : ∀ j, (T.1.preimage (g j)).toFunctor.IsRepresentable := fun j =>
    isRepresentable_preimage_yoneda B S hS (g j) T.1 T.2.2
  let W : ULift.{u} (Fin n) → BigFppfOver B S hS := fun j =>
    (T.1.preimage (g j.down)).toFunctor.reprX
  let k : ∀ j, yoneda.obj (W j) ⟶ T.1.toFunctor := fun j =>
    (T.1.preimage (g j.down)).toFunctor.reprW.hom ≫ T.1.fromPreimage (g j.down)
  have hk : ∀ j, IsOpenImmersion B S hS (k j) := fun j =>
    isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _)
      (isOpenImmersion_fromPreimage_of_preimage_le_range_diagonal B S hS P (g j.down) (hg j.down)
        T (hT.1 j.down))
  refine isRepresentable_of_isOpenImmersion_cover B S hS T.2.1.isSheaf
    (μ := Finset.univ.sup fun j => ((BigFppfOver.toScheme B S hS).obj (W j)).size) ?_ ?_
    (fun j => Finset.le_sup (f := fun j => ((BigFppfOver.toScheme B S hS).obj (W j)).size)
      (Finset.mem_univ j)) k hk ?_
  · rw [Cardinal.mk_uLift, Cardinal.mk_fin, Cardinal.lift_natCast]
    exact Cardinal.natCast_lt_aleph0.trans B.aleph0_lt_cutoff
  · rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.2 (ne_of_gt
      ((Cardinal.aleph0_pos).trans B.aleph0_lt_cutoff)))]
    exact fun j _ => (W j).left.property
  · refine Set.eq_univ_of_forall fun t => ?_
    obtain ⟨j, w, hw⟩ := exists_fromPreimage_point_of_isEtaleSectionClosed B S hS g T.1 hT t
    obtain ⟨v, hv⟩ := (bijective_pointsMap_of_isIso B S hS
      (T.1.preimage (g j)).toFunctor.reprW.hom).2 w
    refine Set.mem_iUnion.2 ⟨ULift.up j, v, ?_⟩
    show pointsMap B S hS _ (_ ≫ _) v = t
    rw [pointsMap_comp_apply, hv, hw]

/-- **A closed subspace with the two properties is a scheme, covered by open subschemes over
which it factors through the charts.** -/
theorem exists_iso_yoneda_of_isEtaleSectionClosed (P : AlgebraicSpaces B S hS) {n : ℕ}
    {Γ : Fin n → BigFppfOver B S hS} (g : ∀ j, yoneda.obj (Γ j) ⟶ P.1)
    (hg : ∀ j, IsEtale B S hS (g j)) (T : ClosedSubspaces B S hS P.1)
    (hT : IsEtaleSectionClosed B S hS g T.1) :
    ∃ (Y : BigFppfOver B S hS) (e : yoneda.obj Y ≅ T.1.toFunctor),
      ∀ y : points B S hS (yoneda.obj Y), ∃ (j : Fin n) (W : Subfunctor (yoneda.obj Y)),
        IsOpenSubspace B S hS W ∧ W.toFunctor.IsRepresentable ∧
        y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        ∃ c : W.toFunctor ⟶ yoneda.obj (Γ j), W.ι ≫ e.hom ≫ T.1.ι = c ≫ g j := by
  classical
  have hTrep := isRepresentable_of_isEtaleSectionClosed B S hS P g hg T hT
  refine ⟨T.1.toFunctor.reprX, T.1.toFunctor.reprW, fun y => ?_⟩
  set e := T.1.toFunctor.reprW
  obtain ⟨j, w, hw⟩ := exists_fromPreimage_point_of_isEtaleSectionClosed B S hS g T.1 hT
    (pointsMap B S hS _ e.hom y)
  let m : (T.1.preimage (g j)).toFunctor ⟶ yoneda.obj T.1.toFunctor.reprX :=
    T.1.fromPreimage (g j) ≫ e.inv
  have hm : IsOpenImmersion B S hS m :=
    isOpenImmersion_comp B S hS _ _
      (isOpenImmersion_fromPreimage_of_preimage_le_range_diagonal B S hS P (g j) (hg j) T (hT.1 j))
      (isOpenImmersion_of_isIso B S hS _)
  have _ : Mono m := mono_of_isOpenImmersion B S hS m hm
  have _ := isRepresentable_preimage_yoneda B S hS (g j) T.1 T.2.2
  refine ⟨j, Subfunctor.range m, isOpenSubspace_range_of_isAlgebraicSpace B S hS
    (isClosedSubspace_preimage_yoneda B S hS P (g j) T).1 m hm,
    isRepresentable_of_natIso _ (asIso (Subfunctor.toRange m)), ?_,
    inv (Subfunctor.toRange m) ≫ (T.1.preimage (g j)).ι, ?_⟩
  · rw [range_pointsMap_ι_range]
    refine ⟨w, ?_⟩
    show pointsMap B S hS _ (_ ≫ _) w = y
    rw [pointsMap_comp_apply, hw, ← pointsMap_comp_apply, Iso.hom_inv_id, pointsMap_id, id_eq]
  · have hinv : inv (Subfunctor.toRange m) ≫ m = (Subfunctor.range m).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι m).symm
    rw [← hinv, Category.assoc, Category.assoc]
    show inv (Subfunctor.toRange m) ≫ T.1.fromPreimage (g j) ≫ e.inv ≫ e.hom ≫ T.1.ι = _
    rw [Iso.inv_hom_id_assoc, Subfunctor.fromPreimage_ι, Category.assoc]

end AlgebraicGeometry.Space

end
