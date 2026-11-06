module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericRankDecomposition
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.AffineTestReduction
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatInDimensionsGEOn
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme

/-!
# Flatness in dimensions at least the fibre dimension as a finite coproduct of strata

Let `f : X ⟶ S` be a smooth morphism, quasi-compact and quasi-separated, whose fibres are
geometrically irreducible of dimension `d`, let `F` be an `𝒪_X`-module of finite presentation, and
let `S` be affine. Stacks 05UE says that the functor `F_d` of flatness in dimensions `≥ d`
is the union of the functors `H_p` of freeness of rank `p` at the generic points of the fibres,
and that only finitely many `H_p` are nonempty; Stacks 05UC represents each `H_p` by an immersion
`S_p ⟶ S`, of finite presentation. This file assembles the two: `F_d` is represented by the
coproduct `∐_{p ≤ B} S_p ⟶ S`, a monomorphism of finite presentation. That is the case `d₁ = d`
of the proof of Stacks 05UF.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.exists_rankBound`: over a quasi-compact base the
  ranks at the points of the base are bounded.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.baseChangeFlatInDimensionsGE_iff`: Stacks 05UE
  after an arbitrary base change, in the form `F_d(T)` holds exactly when every point of `T` lies
  in the image of the locus where the pulled-back module is free of some rank.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.exists_mono_baseChangeFlatInDimensionsGE`: the
  representation of `F_d` by a monomorphism of finite presentation.

## Implementation notes

A morphism into the coproduct is glued from local factorizations through the summands
(`Stacks.Flatness.ModuleMapBaseChangeSituation.exists_comp_eq_of_openCover`), which is possible
because the coproduct is a monomorphism into the base: two morphisms into it agreeing over the base
land, near each point, in summands of the same rank, since the ranks at a point are determined
(`AlgebraicGeometry.FreeAtGenericPointsSituation.eq_of_condition_of_condition`), and each summand
is a monomorphism into the base.

## References

* [Stacks Project, Tag 05UE](https://stacks.math.columbia.edu/tag/05UE)
* [Stacks Project, Tag 05UC](https://stacks.math.columbia.edu/tag/05UC)
* [Stacks Project, Tag 05UF](https://stacks.math.columbia.edu/tag/05UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u})

/-- **The ranks are bounded over a quasi-compact base.** Every point of the base lies in the base
of a chart (Stacks 05UC), the ranks over the base of a chart are at most its number of
generators, and finitely many chart bases cover the base. -/
theorem exists_rankBound [CompactSpace D.S] : ∃ B : ℕ, ∀ s q, D.RankAt q s → q ≤ B := by
  have hc : ∀ s : D.S, ∃ c : D.Chart, s ∈ c.V := fun s ↦ by
    obtain ⟨q, hq⟩ := D.exists_condition_residueField s
    obtain ⟨c, hsc, -, -⟩ := D.exists_chart ⊤ trivial hq
    exact ⟨c, hsc⟩
  choose c hsc using hc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s ↦ ((c s).V : Set D.S))
    (fun s ↦ (c s).V.isOpen) fun s _ ↦ Set.mem_iUnion.mpr ⟨s, hsc s⟩
  refine ⟨t.sup fun s ↦ (c s).n, fun s q hq ↦ ?_⟩
  obtain ⟨s', hs't, hs⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ s))
  exact ((c s').rankBound s hs q hq).trans (Finset.le_sup (f := fun s ↦ (c s).n) hs't)

/-- The image of the free-rank locus, as an open subscheme of the base change. -/
abbrev baseRankLocusOpens (p : ℕ) (T : Over D.S) : T.left.Opens :=
  ⟨D.baseRankLocus p T, D.isOpen_baseRankLocus p T⟩

/-- Freeness of rank `p` at the generic points of the fibres over an open `O` of `T` gives, at a
point of `O`, freeness of rank `p` at the generic point of the fibre over that point of `T`: the
base change to `O` is an open subscheme of the base change to `T`. -/
theorem mem_baseRankLocus_of_condition_opens {p : ℕ} (T : Over D.S) (O : T.left.Opens)
    (h : D.Condition p (Over.mk (O.ι ≫ T.hom))) {t : T.left} (ht : t ∈ O) :
    t ∈ D.baseRankLocus p T := by
  let g : Over.mk (O.ι ≫ T.hom) ⟶ T := Over.homMk O.ι
  have hpb := D.isPullback_transitionHom g
  have : IsOpenImmersion (D.transitionHom g) :=
    MorphismProperty.of_isPullback hpb.flip (inferInstanceAs (IsOpenImmersion O.ι))
  have hall := (D.condition_iff_baseRankLocus_eq_univ p _).mp h
  obtain ⟨y, hy, hyt⟩ := (Set.eq_univ_iff_forall.mp hall) ⟨t, ht⟩
  refine ⟨D.transitionHom g y, ?_, ?_⟩
  · exact freeAtPointOfRank_of_isOpenImmersion (D.transitionHom g) _ y p
      (freeAtPointOfRank_of_moduleIso (D.transitionModuleIso g).symm hy)
  · have hw := congrArg (fun k : _ ⟶ T.left ↦ k.base y) (D.transitionHom_comp_snd g)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hw
    show (D.baseChangeMap T).base (D.transitionHom g y) = t
    rw [hw]
    show O.ι.base ((D.baseChangeMap _).base y) = t
    rw [hyt]
    rfl

/-- Conversely, freeness of rank `p` at the generic points of the fibres over the image of the
free-rank locus is the generic-rank condition of rank `p` over that open. -/
theorem condition_baseRankLocus {p : ℕ} (T : Over D.S) :
    D.Condition p (Over.mk ((D.baseRankLocusOpens p T).ι ≫ T.hom)) := by
  set O := D.baseRankLocusOpens p T
  rw [D.condition_iff_baseRankLocus_eq_univ, Set.eq_univ_iff_forall]
  intro t
  exact D.preimage_baseRankLocus_subset p (Over.homMk O.ι : Over.mk (O.ι ≫ T.hom) ⟶ T) t.2

/-- **The rank at a point of a base change is bounded by a bound for the ranks at the points of
the base.** The rank is read off the fibre over the image point. -/
theorem le_of_mem_baseRankLocus {B : ℕ} (hB : ∀ s q, D.RankAt q s → q ≤ B) {p : ℕ}
    (T : Over D.S) {t : T.left} (ht : t ∈ D.baseRankLocus p T) : p ≤ B := by
  obtain ⟨q, hq⟩ := D.exists_condition_residueField (T.hom.base t)
  rw [D.eq_of_condition_of_condition_residueField (D.condition_baseRankLocus (p := p) T)
    (⟨t, ht⟩ : D.baseRankLocusOpens p T) hq]
  exact hB _ q hq

/-- **Stacks Project, Tag 05UE**, after an arbitrary base change. If the fibres of the family are
of dimension `d`, the morphism is quasi-compact and quasi-separated and the module is of finite
presentation, then the base change of the module to a scheme `T` over the base is flat over `T` in
dimensions `≥ d` exactly when every point of `T` lies in the image of the locus where the
pulled-back module is free of some rank. -/
theorem baseChangeFlatInDimensionsGE_iff [QuasiCompact D.f] [QuasiSeparated D.f]
    [D.F.IsFinitePresentation] {d : ℕ} (hd : ∀ s, topologicalKrullDim (D.f.fiber s) = d)
    (T : Over D.S) :
    BaseChangeFlatInDimensionsGE D.f D.F d T ↔ ∀ t, ∃ r, t ∈ D.baseRankLocus r T := by
  have hirr : ∀ t, GeometricallyIrreducible ((D.baseChangeMap T).fiberToSpecResidueField t) :=
    (GeometricallyIrreducible.iff_geometricallyIrreducible_fiber _).mp
      (D.geometricallyIrreducible_baseChangeMap T)
  have hdim : RelativeDimension (D.baseChangeMap T) d := by
    intro t _
    have := D.irreducibleSpace_fiber_baseChangeMap T t
    refine ⟨TopologicalSpace.Equidimensional.of_preirreducibleSpace _, ?_⟩
    have hsq := isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback D.f T.hom) t
    have hlft : LocallyOfFiniteType (D.f.fiberToSpecResidueField (T.hom t)) := by
      show LocallyOfFiniteType (pullback.snd D.f (D.S.fromSpecResidueField (T.hom t)))
      infer_instance
    exact (@topologicalKrullDim_eq_of_isPullback_of_subsingleton _ _ _ _ _ _ _ _ hsq hlft _ _
      _).trans (hd _)
  have hfp : FinitePresentation (D.baseChangeMap T) :=
    FinitePresentation.mk inferInstance inferInstance inferInstance
  rw [BaseChangeFlatInDimensionsGE,
    ← isFlatOverInDimensionsGE_iff_isFlatOverInDimensionsGEOn_univ]
  refine ⟨fun hflat t ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨ξ, hξ⟩ := D.exists_isGenericPoint_fiber_baseChangeMap T t
    obtain ⟨r, hr⟩ := exists_freeAtPointOfRank_of_isFlatOverInDimensionsGE (D.baseChangeMap T) hfp
      hirr hdim (D.baseChangeModule T) hflat t ξ hξ
    refine ⟨r, (D.mem_baseRankLocus_iff r T t).mpr fun ξ' hξ' ↦ ?_⟩
    rwa [hξ'.eq hξ]
  · refine isFlatOverInDimensionsGE_of_forall_exists_freeAtPointOfRank (D.baseChangeMap T) hirr
      hdim (D.baseChangeModule T) fun t ξ hξ ↦ ?_
    obtain ⟨r, hr⟩ := h t
    exact ⟨r, (D.mem_baseRankLocus_iff r T t).mp hr ξ hξ⟩

/-- A morphism into a coproduct of schemes factors, near each point, through one summand. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_opens_lift_sigmaι {ι : Type u}
    (X : ι → Scheme.{u}) {T : Scheme.{u}} (a : T ⟶ ∐ X) (t : T) :
    ∃ (p : ι) (O : T.Opens) (_ : t ∈ O) (b : O.toScheme ⟶ X p), b ≫ Sigma.ι X p = O.ι ≫ a := by
  obtain ⟨⟨p, w⟩, hw⟩ := (sigmaMk X).surjective (a t)
  have hp : a t ∈ (Sigma.ι X p).opensRange := ⟨w, (sigmaMk_mk X p w).symm.trans hw⟩
  let O : T.Opens := a ⁻¹ᵁ (Sigma.ι X p).opensRange
  refine ⟨p, O, hp, IsOpenImmersion.lift (Sigma.ι X p) (O.ι ≫ a) ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨o, rfl⟩
  exact o.2

/-- **The coproduct of the strata is a monomorphism into the base.** Two morphisms into the
coproduct agreeing over the base land, near each point, in summands of the same rank, since the
rank at a point is determined, and each summand is a monomorphism into the base. -/
theorem mono_sigmaDesc_of_factorizationCriterion {B : ℕ} (W : ULift.{u} (Fin (B + 1)) → Over D.S)
    [∀ p, Mono (W p).hom] (hW : ∀ p, D.FactorizationCriterion p.down.val (W p).hom) :
    Mono (Sigma.desc fun p ↦ (W p).hom) := by
  set i : (∐ fun p ↦ (W p).left) ⟶ D.S := Sigma.desc fun p ↦ (W p).hom
  have hιi : ∀ p, Sigma.ι (fun p ↦ (W p).left) p ≫ i = (W p).hom := fun p ↦
    Sigma.ι_desc _ p
  refine ⟨fun {T} a b hab ↦ ?_⟩
  have key : ∀ t : T, ∃ O : T.Opens, t ∈ O ∧ O.ι ≫ a = O.ι ≫ b := by
    intro t
    obtain ⟨p, O₁, ht₁, a₁, ha₁⟩ := Scheme.exists_opens_lift_sigmaι _ a t
    obtain ⟨q, O₂, ht₂, b₂, hb₂⟩ := Scheme.exists_opens_lift_sigmaι _ b t
    let O : T.Opens := O₁ ⊓ O₂
    let j₁ : O.toScheme ⟶ O₁.toScheme := T.homOfLE inf_le_left
    let j₂ : O.toScheme ⟶ O₂.toScheme := T.homOfLE inf_le_right
    have hj₁ : j₁ ≫ O₁.ι = O.ι := T.homOfLE_ι _
    have hj₂ : j₂ ≫ O₂.ι = O.ι := T.homOfLE_ι _
    have lift : ∀ (c : T ⟶ ∐ fun p ↦ (W p).left) (r) (O' : T.Opens) (j : O.toScheme ⟶ O'.toScheme)
        (c' : O'.toScheme ⟶ (W r).left), c' ≫ Sigma.ι (fun p ↦ (W p).left) r = O'.ι ≫ c →
        j ≫ O'.ι = O.ι → (j ≫ c') ≫ (W r).hom = O.ι ≫ c ≫ i := by
      intro c r O' j c' hc hj
      rw [← hιi r, ← hj]
      simp only [Category.assoc, ← Category.assoc c', hc]
    have hA := lift a p O₁ j₁ a₁ ha₁ hj₁
    have hB := (lift b q O₂ j₂ b₂ hb₂ hj₂).trans (congrArg (O.ι ≫ ·) hab.symm)
    have hpq : p = q := ULift.ext <| Fin.ext <| D.eq_of_condition_of_condition
      ((hW p (Over.mk (O.ι ≫ a ≫ i))).mpr ⟨j₁ ≫ a₁, hA⟩)
      ((hW q (Over.mk (O.ι ≫ a ≫ i))).mpr ⟨j₂ ≫ b₂, hB⟩) ⟨t, ht₁, ht₂⟩
    subst hpq
    have hab' : j₁ ≫ a₁ = j₂ ≫ b₂ := (cancel_mono (W p).hom).mp (hA.trans hB.symm)
    refine ⟨O, ⟨ht₁, ht₂⟩, ?_⟩
    calc O.ι ≫ a = j₁ ≫ a₁ ≫ Sigma.ι (fun p ↦ (W p).left) p := by
          rw [ha₁, ← Category.assoc, hj₁]
      _ = j₂ ≫ b₂ ≫ Sigma.ι (fun p ↦ (W p).left) p := by
          rw [← Category.assoc, hab', Category.assoc]
      _ = O.ι ≫ b := by rw [hb₂, ← Category.assoc, hj₂]
  choose O hO hOab using key
  let 𝒰 := T.openCoverOfIsOpenCover O (IsOpenCover.of_sets (fun t ↦ (O t).isOpen)
    (Set.eq_univ_of_forall fun t ↦ Set.mem_iUnion.mpr ⟨t, hO t⟩))
  exact Scheme.Cover.hom_ext 𝒰 _ _ fun t ↦ hOab t

/-- **Stacks 05UE and Stacks 05UC assembled: the case `d₁ = d` of Stacks 05UF.** Over an
affine base, for a quasi-compact and quasi-separated family whose fibres have dimension
`d` and a module of finite presentation, the functor `F_d` is represented by a monomorphism of
finite presentation: the coproduct of the immersions representing the functors `H_p` for the
finitely many ranks `p` that occur. -/
theorem exists_mono_baseChangeFlatInDimensionsGE [IsAffine D.S] [QuasiCompact D.f]
    [QuasiSeparated D.f] [D.F.IsFinitePresentation] {d : ℕ}
    (hd : ∀ s, topologicalKrullDim (D.f.fiber s) = d) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ D.S), Mono i ∧ FinitePresentation i ∧
      ∀ T : Over D.S, BaseChangeFlatInDimensionsGE D.f D.F d T ↔
        ∃ g : T.left ⟶ Z, g ≫ i = T.hom := by
  obtain ⟨B, hB⟩ := D.exists_rankBound
  choose W hWimm hWrep using fun p : ULift.{u} (Fin (B + 1)) ↦
    D.exists_immersion_representableBy p.down.val
  have hWmono : ∀ p, Mono (W p).hom := fun p ↦
    Stacks.Flatness.mono_hom_of_representableBy (hWrep p).some
  have hWcrit : ∀ p, D.FactorizationCriterion p.down.val (W p).hom := fun p ↦
    D.factorizationCriterion_of_representableBy p.down.val (hWrep p).some
  have hWfp : ∀ p, FinitePresentation (W p).hom := fun p ↦
    D.finitePresentation_hom_of_representableBy p.down.val (hWrep p).some
  let Z : Scheme.{u} := ∐ fun p ↦ (W p).left
  let i : Z ⟶ D.S := Sigma.desc fun p ↦ (W p).hom
  have hιi : ∀ p, Sigma.ι (fun p ↦ (W p).left) p ≫ i = (W p).hom := fun p ↦
    Sigma.ι_desc _ p
  have hmono : Mono i := D.mono_sigmaDesc_of_factorizationCriterion W hWcrit
  have hcompact : CompactSpace Z := by
    have : ∀ p, CompactSpace (W p).left := fun p ↦
      have := (hWfp p).2.1
      QuasiCompact.compactSpace_of_compactSpace (W p).hom
    exact (sigmaMk fun p ↦ (W p).left).compactSpace
  refine ⟨Z, i, hmono, ?_, fun T ↦ ?_⟩
  · refine FinitePresentation.mk ?_ ?_ inferInstance
    · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
        (Q := RingHom.FinitePresentation)
      exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation) fun p ↦
        (hWfp p).1
    · exact quasiCompact_of_compactSpace i
  rw [D.baseChangeFlatInDimensionsGE_iff hd]
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ t ↦ ?_⟩
  · have hr : ∀ t, ∃ p : ULift.{u} (Fin (B + 1)), t ∈ D.baseRankLocus p.down.val T := fun t ↦ by
      obtain ⟨r, hr⟩ := h t
      exact ⟨⟨r, Nat.lt_succ_of_le (D.le_of_mem_baseRankLocus hB T hr)⟩, hr⟩
    choose p hp using hr
    let O : T.left → T.left.Opens := fun t ↦ D.baseRankLocusOpens (p t).down.val T
    let 𝒰 := T.left.openCoverOfIsOpenCover O (IsOpenCover.of_sets (fun t ↦ (O t).isOpen)
      (Set.eq_univ_of_forall fun t ↦ Set.mem_iUnion.mpr ⟨t, hp t⟩))
    refine Stacks.Flatness.ModuleMapBaseChangeSituation.exists_comp_eq_of_openCover T
      (Over.mk i) hmono 𝒰 fun t ↦ ?_
    obtain ⟨b, hb⟩ := (hWcrit (p t) _).mp (D.condition_baseRankLocus (p := (p t).down.val) T)
    refine ⟨b ≫ Sigma.ι (fun p ↦ (W p).left) (p t), ?_⟩
    show (b ≫ Sigma.ι (fun p ↦ (W p).left) (p t)) ≫ i = (O t).ι ≫ T.hom
    rw [Category.assoc, hιi]
    exact hb
  · obtain ⟨p, O, ht, b, hb⟩ := Scheme.exists_opens_lift_sigmaι (fun p ↦ (W p).left) g t
    refine ⟨p.down.val, D.mem_baseRankLocus_of_condition_opens T O ?_ ht⟩
    refine (hWcrit p _).mpr ⟨b, ?_⟩
    show b ≫ (W p).hom = O.ι ≫ T.hom
    rw [← hιi p, ← Category.assoc, hb, Category.assoc, hg]

end FreeAtGenericPointsSituation

end AlgebraicGeometry

end
