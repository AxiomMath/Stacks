module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Existence
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatDimensionFunctorRepresentability
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.EtaleLocalRepresentability
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionSheafAndLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.MonoFinitePresentationLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.QuasiFinitePointedBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.ContainmentConstructible

/-!
# The functor of flatness in dimensions at least `n` for a pure module

In Situation 05MT, assume that `f : X ⟶ S` is of finite presentation and that `F` is an
`𝒪_X`-module of finite presentation which is pure relative to `S`. Stacks 05UG asserts that the
functor `F_n` of Stacks 05MU is representable by a monomorphism `Z_n ⟶ S` of finite presentation.

This file carries out the proof of the source. Stacks 05UF is
`AlgebraicGeometry.FlatDimensionSituation.exists_mono_finitePresentation_representableBy`, and the
second assertion of Stacks 05UD, through Stacks 05UA, is
`AlgebraicGeometry.FlatDimensionSituation.isFlat_of_forall_etaleChart`.

## The proof

The functor `F_n` is an fpqc sheaf (Stacks 05MV) and a monomorphism of finite presentation is
separated and quasi-finite, so representability by a monomorphism of finite presentation is
local on `S` for the étale topology; this is
`Stacks.Flatness.IsCutOutByMonoFP.of_etale_local`. Over an affine base the fibre dimensions are
bounded, so `F_n` is everything for `n` large, and a descending induction on `n` reduces the
statement to the case where `F` is flat over `S` in dimensions `≥ n + 1`: the representing
monomorphism `Z_{n+1} ⟶ S` is quasi-finite, so purity passes to `X ×_S Z_{n+1}` (Stacks 05J7),
over which `F` is flat in dimensions `≥ n + 1`.

In that case, around a point `s` of `S`, Stacks 05HU gives an elementary étale neighbourhood
`(S', s')` and finitely many étale charts `hᵢ : Yᵢ ⟶ X ×_S S'` covering the fibre over `s'`,
each with a complete dévissage over `s'`. Purity and Stacks 05KR, 05LW give an open neighbourhood
of `s'` over which the relative assassin lies in the union of the images of the charts, and over
it `F_n` is the intersection of the functors of the charts (Stacks 05UD, which uses Stacks 05UA).
Each of those is representable near `s'` by Stacks 05UF.

## Main results

* `FlatDimensionSituation.exists_mono_finitePresentation_representableBy_of_isPure`: if `f` is
  of finite presentation and `F` is of finite presentation and pure relative to `S`, then the
  functor `F_n` is representable by a monomorphism of finite presentation.

## References

* [Stacks Project, Tag 05UG](https://stacks.math.columbia.edu/tag/05UG)
* [Stacks Project, Tag 05UF](https://stacks.math.columbia.edu/tag/05UF)
* [Stacks Project, Tag 05UD](https://stacks.math.columbia.edu/tag/05UD)
* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
* [Stacks Project, Tag 05HU](https://stacks.math.columbia.edu/tag/05HU)
* [Stacks Project, Tag 05J7](https://stacks.math.columbia.edu/tag/05J7)
* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
* [Stacks Project, Tag 05LW](https://stacks.math.columbia.edu/tag/05LW)
* [Stacks Project, Tag 05MV](https://stacks.math.columbia.edu/tag/05MV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Stacks.Flatness

universe u

namespace AlgebraicGeometry

attribute [local instance] isQuasicoherent_pullback_obj' isFiniteType_pullback_obj'

attribute [local instance] isFinitePresentation_pullback_obj

/-- A zero module is flat in dimensions `≥ n` over any base. -/
theorem isFlatOverInDimensionsGE_of_isZero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (hF : IsZero F)
    (n : ℕ) : IsFlatOverInDimensionsGE f F n := by
  intro s
  have : IsEmpty ↥{y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)} :=
    ⟨fun y ↦ y.2 (isFlatOver_of_isZero f F hF _)⟩
  rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).mpr inferInstance]
  exact WithBot.bot_lt_coe _

/-- If the fibres of `f` have dimension at most `N`, then every module is flat in dimensions
`≥ N + 1`. -/
theorem isFlatOverInDimensionsGE_of_fiber_le {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] {N : ℕ}
    (hN : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ N) :
    IsFlatOverInDimensionsGE f F (N + 1) := fun s ↦
  (topologicalKrullDim_subspace_le _ _).trans_lt
    ((hN s).trans_lt (by exact_mod_cast Nat.lt_succ_self N))

/-- **Purity along an associated point.** If `F` is pure along the fibre over `s`, then for
every generalization `t` of `s` and every open `W` of `X` containing the fibre over `s`, the
associated points of the fibre `F_t` lie in `W`. -/
theorem associatedPoints_fiber_subset_of_isPureAlong {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] {s t : S}
    (hPure : IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}))
    (hst : t ⤳ s) (W : Set X) (hW : IsOpen W) (hWs : Set.range (f.fiberι s) ⊆ W) :
    Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (f.fiberι t)).obj F) ⊆
      f.fiberι t ⁻¹' W := by
  intro y hy
  by_contra hyW
  let x : X := f.fiberι t y
  let P : PrePureSituation.{u} := { S := S, X := X, f := f, F := F, s := s }
  let D : ImpurityDiagram P :=
    { T := S
      g := 𝟙 S
      t' := t
      t := s
      specializes := hst
      mapsToChosenPoint := rfl
      X_T := X
      toX := 𝟙 X
      toT := f
      isPullback := IsPullback.of_id_fst
      xi := x
      xi_liesOver := by
        have hxmem : x ∈ Set.range (f.fiberι t) := ⟨y, rfl⟩
        simpa only [f.range_fiberι, Set.mem_preimage, Set.mem_singleton_iff] using hxmem }
  have hAss : x ∈ Stacks.Divisors.relativeAssassin f
      ((Scheme.Modules.pullback (𝟙 X)).obj F) := by
    rw [Stacks.Divisors.mem_relativeAssassin]
    refine ⟨t, y, ?_, rfl⟩
    rwa [Stacks.Divisors.associatedPoints_congr
      ((Scheme.Modules.pullback (f.fiberι t)).mapIso ((Scheme.Modules.pullbackId X).app F))]
  refine hPure D inferInstance (EtaleNeighborhood.isElementary_self S s) ⟨hAss, ?_⟩
  refine Set.eq_empty_iff_forall_notMem.mpr fun z hz ↦ ?_
  obtain ⟨hzcl, ⟨z₀, rfl⟩⟩ := hz
  exact closure_minimal (by simpa [Set.subset_def] using hyW) hW.isClosed_compl hzcl
    (hWs ⟨z₀, rfl⟩)

/-- **Spreading out the containment of the relative assassin.** Let `f` be of finite
presentation with affine target, `F` of finite presentation and pure along the fibre over `s`,
and let `O ⊆ X` be an open containing that fibre. Then over some open neighbourhood of `s` every
point of the relative assassin of `F` lies in `O`. -/
theorem exists_open_relativeAssassin_subset {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] [F.IsFiniteType] (s : S)
    (hPure : IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}))
    (O : Set X) (hO : IsOpen O) (hsO : f ⁻¹' {s} ⊆ O) :
    ∃ V : S.Opens, s ∈ V ∧ ∀ x ∈ Stacks.Divisors.relativeAssassin f F, f x ∈ V → x ∈ O := by
  have hKO : Set.range (f.fiberι s) ⊆ O := by rwa [f.range_fiberι]
  obtain ⟨W, hWc, hWo, hKW, hWO⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (isCompact_range (f.fiberι s).continuous) hO hKO
  let W' : X.Opens := ⟨W, hWo⟩
  have : CompactSpace W' := isCompact_iff_compactSpace.mp hWc
  have : QuasiCompact (W'.ι ≫ f) := inferInstance
  let E : Set S := Stacks.RelativeAssassin.fibrewiseContainment f F W'
  have hE : IsLocallyConstructible E :=
    Stacks.RelativeAssassin.isLocallyConstructible_fibrewiseContainment f
      (FinitePresentation.mk inferInstance inferInstance inferInstance) F W'
  have hgen : {t : S | t ⤳ s} ⊆ E := fun t ht ↦
    associatedPoints_fiber_subset_of_isPureAlong f F hPure ht W hWo hKW
  obtain ⟨V, hVE, hVo, hsV⟩ :=
    mem_nhds_iff.mp (mem_nhds_of_isLocallyConstructible_of_specializes_subset hE hgen)
  refine ⟨⟨V, hVo⟩, hsV, fun x hx hxV ↦ ?_⟩
  obtain ⟨t, y, hy, rfl⟩ := (Stacks.Divisors.mem_relativeAssassin f F x).mp hx
  exact hWO (hVE (f.apply_fiberι t y ▸ hxV) hy)

/-- Being cut out by a monomorphism of finite presentation respects equivalence of properties. -/
private theorem isCutOutByMonoFP_congr {S : Scheme.{u}} {P Q : Over S → Prop}
    (h : ∀ T, P T ↔ Q T) : IsCutOutByMonoFP P ↔ IsCutOutByMonoFP Q :=
  ⟨fun hP ↦ hP.of_iff h, fun hQ ↦ hQ.of_iff fun T ↦ (h T).symm⟩

namespace FlatDimensionSituation

variable (D : FlatDimensionSituation.{u})

/-- `F_n` is cut out by a monomorphism of finite presentation. -/
abbrev Rep : Prop := IsCutOutByMonoFP D.IsFlatInDimensionsGEAfterBaseChange

/-- `Rep` is representability of `F_n` by a monomorphism of finite presentation. -/
theorem rep_iff : D.Rep ↔ ∃ Z : Over D.S, Mono Z.hom ∧ FinitePresentation Z.hom ∧
    Nonempty (D.flatDimensionFunctor.RepresentableBy Z) := by
  rw [← isCutOutByMonoFP_iff_exists_representableBy]
  exact isCutOutByMonoFP_congr fun T ↦ (D.flatDimensionFunctor_obj_nonempty_iff T).symm

/-- The functor of the property `IsFlatInDimensionsGEAfterBaseChange` is `F_n`, an fpqc
sheaf. -/
theorem isSheaf_propertyFunctor :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over D.S)
      (propertyFunctor D.IsFlatInDimensionsGEAfterBaseChange
        fun g h ↦ D.isFlatInDimensionsGEAfterBaseChange_of_hom g h) :=
  D.flatDimensionFunctor_isSheaf_fpqc

/-- The condition at a scheme over the base depends only on its structure morphism. -/
theorem isFlat_mk_congr {Y : Scheme.{u}} {a b : Y ⟶ D.S} (h : a = b) :
    D.IsFlatInDimensionsGEAfterBaseChange (Over.mk a) ↔
      D.IsFlatInDimensionsGEAfterBaseChange (Over.mk b) := by
  subst h
  rfl

/-- Restriction along a composite is iterated restriction. -/
theorem isCutOutByMonoFP_comp_iff {U V : Scheme.{u}} (q : U ⟶ D.S) (r : V ⟶ U) :
    IsCutOutByMonoFP (fun T : Over V ↦ D.IsFlatInDimensionsGEAfterBaseChange
      ((Over.map (r ≫ q)).obj T)) ↔
    IsCutOutByMonoFP (fun T : Over V ↦ D.IsFlatInDimensionsGEAfterBaseChange
      ((Over.map q).obj ((Over.map r).obj T))) :=
  isCutOutByMonoFP_congr fun _ ↦ D.isFlat_mk_congr (Category.assoc _ _ _).symm

/-- Restriction to schemes over `U` is the functor of the base-changed situation. -/
theorem isCutOutByMonoFP_iff_baseChange {U : Scheme.{u}} (q : U ⟶ D.S) :
    IsCutOutByMonoFP (fun T : Over U ↦ D.IsFlatInDimensionsGEAfterBaseChange
      ((Over.map q).obj T)) ↔ (D.baseChange q).Rep :=
  isCutOutByMonoFP_congr fun T ↦ (D.baseChange_isFlat_iff q T).symm

/-- The output of Stacks 05UF, read as a property cut out over the open. -/
theorem isCutOutByMonoFP_of_representableBy (U : D.S.Opens) {Z : Over U.toScheme}
    (hm : Mono Z.hom) (hfp : FinitePresentation Z.hom)
    (e : (D.openFlatDimensionFunctor U).RepresentableBy Z) :
    IsCutOutByMonoFP (fun T : Over U.toScheme ↦ D.IsFlatInDimensionsGEAfterBaseChange
      ((Over.map U.ι).obj T)) :=
  ((isCutOutByMonoFP_iff_exists_representableBy (D.openFlatDimensionFunctor U)).mpr
    ⟨Z, hm, hfp, ⟨e⟩⟩).of_iff fun T ↦ D.nonempty_openFlatDimensionFunctor_obj_iff U T

/-- Changing the module by an isomorphism does not change the condition. -/
theorem isFlat_iff_of_moduleIso (G : D.X.Modules) [hq : G.IsQuasicoherent] [ht : G.IsFiniteType]
    (e : D.F ≅ G) (T : Over D.S) :
    D.IsFlatInDimensionsGEAfterBaseChange T ↔
      ({ D with F := G, isQuasicoherent := hq, isFiniteType := ht } :
        FlatDimensionSituation.{u}).IsFlatInDimensionsGEAfterBaseChange T :=
  isFlatOverInDimensionsGE_iff_of_moduleIso _
    ((Scheme.Modules.pullback (pullback.fst D.f T.hom)).mapIso e) D.n

/-- The base change of a morphism of finite presentation is of finite presentation. -/
instance [LocallyOfFinitePresentation D.f] {U : Scheme.{u}} (q : U ⟶ D.S) :
    LocallyOfFinitePresentation (D.baseChange q).f :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd D.f q))

/-- The base change of a quasi-compact morphism is quasi-compact. -/
instance [QuasiCompact D.f] {U : Scheme.{u}} (q : U ⟶ D.S) :
    QuasiCompact (D.baseChange q).f :=
  inferInstanceAs (QuasiCompact (pullback.snd D.f q))

/-- The base change of a quasi-separated morphism is quasi-separated. -/
instance [QuasiSeparated D.f] {U : Scheme.{u}} (q : U ⟶ D.S) :
    QuasiSeparated (D.baseChange q).f :=
  inferInstanceAs (QuasiSeparated (pullback.snd D.f q))

/-- The pullback of a module of finite presentation is of finite presentation. -/
instance [D.F.IsFinitePresentation] {U : Scheme.{u}} (q : U ⟶ D.S) :
    (D.baseChange q).F.IsFinitePresentation :=
  isFinitePresentation_pullback_obj _ _

/-- **Stacks 05J7.** Purity relative to the base passes to the base change along a morphism
locally quasi-finite and locally of finite type. -/
theorem isPureRelative_baseChange [QuasiCompact D.f] (hpure : IsPureRelative D.f D.F)
    {U : Scheme.{u}} (q : U ⟶ D.S) [LocallyOfFiniteType q] [LocallyQuasiFinite q] :
    IsPureRelative (D.baseChange q).f (D.baseChange q).F := fun t ↦
  isPureAlong_of_quasiFiniteAt_of_isPureAlong
    (P := { S := D.S, X := D.X, f := D.f, F := D.F, s := q t })
    (Q := { S := U, X := pullback D.f q, f := pullback.snd D.f q
            F := (Scheme.Modules.pullback (pullback.fst D.f q)).obj D.F, s := t })
    q rfl (pullback.fst D.f q) (IsPullback.of_hasPullback D.f q) (Iso.refl _)
    ((forall_quasiFiniteAt_iff q).2 ⟨inferInstance, inferInstance⟩ t) (hpure (q t))

/-- Changing the dimension bound commutes with base change. -/
theorem baseChange_withN {U : Scheme.{u}} (q : U ⟶ D.S) (m : ℕ) :
    (D.withN m).baseChange q = (D.baseChange q).withN m := rfl

/-! ### The descending induction -/

/-- The case of Stacks 05UG in which `F` is already flat in dimensions `≥ n + 1`, for every
situation, as a proposition. -/
abbrev KeyCase : Prop :=
  ∀ (E : FlatDimensionSituation.{u}) [LocallyOfFinitePresentation E.f] [QuasiCompact E.f]
    [QuasiSeparated E.f] [E.F.IsFinitePresentation], IsPureRelative E.f E.F →
    IsFlatOverInDimensionsGE E.f E.F (E.n + 1) → E.Rep

/-- **The induction step.** If `F_{m+1}` is cut out by `Z ⟶ S`, then `F_m` is cut out by a
monomorphism of finite presentation over `Z`, by the key case applied to `X ×_S Z`, and hence
over `S`. -/
theorem rep_withN_of_rep_withN_succ (hkey : KeyCase.{u}) [LocallyOfFinitePresentation D.f]
    [QuasiCompact D.f] [QuasiSeparated D.f] [D.F.IsFinitePresentation]
    (hpure : IsPureRelative D.f D.F) (m : ℕ) (h : (D.withN (m + 1)).Rep) :
    (D.withN m).Rep := by
  obtain ⟨Z, hZm, hZfp, hZ⟩ := h
  have := hZm
  obtain ⟨h1, h2, h3⟩ := hZfp
  refine IsCutOutByMonoFP.comp
    (fun g h ↦ (D.withN m).isFlatInDimensionsGEAfterBaseChange_of_hom g h)
    (fun T ↦ D.isFlat_withN_mono (Nat.le_succ m) T) hZm ⟨h1, h2, h3⟩ hZ ?_
  rw [(D.withN m).isCutOutByMonoFP_iff_baseChange Z.hom]
  have : LocallyQuasiFinite Z.hom := (isSeparated_and_locallyQuasiFinite_of_mono Z.hom).2
  refine hkey _ ((D.withN m).isPureRelative_baseChange hpure Z.hom) ?_
  have hQZ : (D.withN (m + 1)).IsFlatInDimensionsGEAfterBaseChange Z := (hZ Z).mpr ⟨𝟙 Z⟩
  have h' : ((D.withN (m + 1)).baseChange Z.hom).IsFlatInDimensionsGEAfterBaseChange
      (Over.mk (𝟙 Z.left)) :=
    ((D.withN (m + 1)).baseChange_isFlat_iff Z.hom _).mpr
      ((D.withN (m + 1)).isFlatInDimensionsGEAfterBaseChange_of_hom
        (Over.homMk (𝟙 _) (by simp) : (Over.map Z.hom).obj (Over.mk (𝟙 Z.left)) ⟶ Z) hQZ)
  exact ((D.withN (m + 1)).baseChange Z.hom).isFlat_id_iff.mp h'

/-- **Over a quasi-compact base**, the key case implies the theorem: the fibre dimensions are
bounded, so `F_n` is everything for `n` large, and the induction step descends from there. -/
theorem rep_of_compactSpace (hkey : KeyCase.{u}) [CompactSpace D.S]
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f]
    [D.F.IsFinitePresentation] (hpure : IsPureRelative D.f D.F) : D.Rep := by
  obtain ⟨N, hN⟩ := exists_topologicalKrullDim_fiber_le D.f
  have hbig (m : ℕ) (hm : N + 1 ≤ m) : (D.withN m).Rep :=
    IsCutOutByMonoFP.of_forall fun T ↦ (D.withN m).isFlat_of_isFlatOverInDimensionsGE
      ((isFlatOverInDimensionsGE_of_fiber_le D.f D.F hN).mono hm) T
  have hind : ∀ k m, m + k = N + 1 → (D.withN m).Rep := by
    intro k
    induction k with
    | zero => exact fun m hm ↦ hbig m (by omega)
    | succ k ih =>
      exact fun m hm ↦ D.rep_withN_of_rep_withN_succ hkey hpure m (ih (m + 1) (by omega))
  by_cases hn : N + 1 ≤ D.n
  · exact hbig D.n hn
  · exact hind (N + 1 - D.n) D.n (by omega)

/-- **The key case implies the theorem.** Representability by a monomorphism of finite
presentation is Zariski local on the base, and over an affine open the previous result
applies. -/
theorem rep_of_keyCase (hkey : KeyCase.{u}) [LocallyOfFinitePresentation D.f]
    [QuasiCompact D.f] [QuasiSeparated D.f] [D.F.IsFinitePresentation]
    (hpure : IsPureRelative D.f D.F) : D.Rep := by
  refine IsCutOutByMonoFP.of_etale_local _ _ D.isSheaf_propertyFunctor fun s ↦ ?_
  obtain ⟨a, t, ht⟩ := D.S.affineCover.exists_eq s
  let q := D.S.affineCover.f a
  refine ⟨_, q, inferInstance, ⟨t, ht⟩, ?_⟩
  rw [D.isCutOutByMonoFP_iff_baseChange]
  have : CompactSpace (D.baseChange q).S :=
    inferInstanceAs (CompactSpace (D.S.affineCover.X a))
  exact (D.baseChange q).rep_of_compactSpace hkey (D.isPureRelative_baseChange hpure q)

/-! ### The key case -/

/-- **Finitely many charts.** Over an affine base, let `hᵢ : Yᵢ ⟶ X` be finitely many étale
charts covering the fibre over `s`, and assume that the functor of each chart is cut out by a
monomorphism of finite presentation over some open neighbourhood of `s`. Then the same holds for
`F_n`, by purity and the second assertion of Stacks 05UD. -/
theorem exists_open_of_charts (E : FlatDimensionSituation.{u}) [IsAffine E.S]
    [LocallyOfFinitePresentation E.f] [QuasiCompact E.f] [QuasiSeparated E.f]
    [E.F.IsFinitePresentation]
    (hpure : IsPureRelative E.f E.F) (s : E.S) {m : ℕ} {Y : Fin m → Scheme.{u}}
    (h : ∀ i, Y i ⟶ E.X) [∀ i, Etale (h i)] (hcov : E.f ⁻¹' {s} ⊆ ⋃ i, Set.range (h i))
    (hloc : ∀ i, ∃ W : E.S.Opens, s ∈ W ∧ IsCutOutByMonoFP (fun T : Over W.toScheme ↦
      (E.etaleChart (h i)).IsFlatInDimensionsGEAfterBaseChange ((Over.map W.ι).obj T))) :
    ∃ V : E.S.Opens, s ∈ V ∧ IsCutOutByMonoFP (fun T : Over V.toScheme ↦
      E.IsFlatInDimensionsGEAfterBaseChange ((Over.map V.ι).obj T)) := by
  classical
  choose W hsW hW using hloc
  obtain ⟨V₀, hsV₀, hV₀⟩ := exists_open_relativeAssassin_subset E.f E.F s (hpure s)
    (⋃ i, Set.range (h i)) (isOpen_iUnion fun i ↦ (h i).isOpenMap.isOpen_range) hcov
  let V : E.S.Opens := V₀ ⊓ ⨅ i, W i
  have hVW (i : Fin m) : V ≤ W i := inf_le_right.trans (iInf_le _ i)
  have hVV₀ : V ≤ V₀ := inf_le_left
  have hsV : s ∈ V := by
    refine ⟨hsV₀, ?_⟩
    show s ∈ ((⨅ i, W i : E.S.Opens) : Set E.S)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hsW
  refine ⟨V, hsV, ?_⟩
  have hchart (i : Fin m) : IsCutOutByMonoFP (fun T : Over V.toScheme ↦
      (E.etaleChart (h i)).IsFlatInDimensionsGEAfterBaseChange ((Over.map V.ι).obj T)) := by
    refine ((hW i).baseChange (E.S.homOfLE (hVW i))).of_iff fun T ↦ ?_
    refine (E.etaleChart (h i)).isFlat_mk_congr ?_
    show (T.hom ≫ E.S.homOfLE (hVW i)) ≫ (W i).ι = T.hom ≫ V.ι
    rw [Category.assoc, Scheme.homOfLE_ι]
  refine (IsCutOutByMonoFP.finite_inf hchart).of_iff fun T ↦
    ⟨fun hT ↦ E.isFlat_of_forall_etaleChart h _ ?_ hT,
      fun hT i ↦ E.isFlat_etaleChart_of_isFlat (h i) _ hT⟩
  rintro x hx ⟨t, ht⟩
  have hxV : E.f x ∈ V₀ := by
    rw [← ht]
    exact hVV₀ (T.hom t).2
  exact Set.mem_iUnion.mp (hV₀ x hx hxV)

/-- **The key case of Stacks 05UG**: if `F` is flat in dimensions
`≥ n + 1`, then `F_n` is cut out by a monomorphism of finite presentation. Around each point, the
charts of Stacks 05HU are handled by Stacks 05UF. -/
theorem keyCase : KeyCase.{u} := by
  intro D _ _ _ _ hpure hflat
  refine IsCutOutByMonoFP.of_etale_local _ _ D.isSheaf_propertyFunctor fun s ↦ ?_
  obtain ⟨U, -, hUaff, m, Y, h, het, hl, hq, ht, hdev, hcov⟩ :=
    exists_isAffine_etaleNeighborhood_completeDevissage_cover D.f D.F s
  have := hUaff
  have := het
  let E := D.baseChange U.toBase
  have hpE : IsPureRelative E.f E.F := D.isPureRelative_baseChange hpure U.toBase
  have hflatE : IsFlatOverInDimensionsGE E.f E.F (D.n + 1) :=
    IsFlatOverInDimensionsGE.of_isPullback (IsPullback.of_hasPullback D.f U.toBase) D.F _ hflat
  have hloc (i : Fin m) : ∃ W : E.S.Opens, U.point ∈ W ∧
      IsCutOutByMonoFP (fun T : Over W.toScheme ↦
        (E.etaleChart (h i)).IsFlatInDimensionsGEAfterBaseChange ((Over.map W.ι).obj T)) := by
    let G := (Scheme.Modules.pullback (h i ≫ pullback.fst D.f U.toBase)).obj D.F
    let eC : (E.etaleChart (h i)).F ≅ G :=
      (Scheme.Modules.pullbackComp (h i) (pullback.fst D.f U.toBase)).app D.F
    let C : FlatDimensionSituation.{u} :=
      { E.etaleChart (h i) with F := G, isQuasicoherent := hq i, isFiniteType := ht i }
    have hiff (T : Over E.S) : (E.etaleChart (h i)).IsFlatInDimensionsGEAfterBaseChange T ↔
        C.IsFlatInDimensionsGEAfterBaseChange T :=
      (E.etaleChart (h i)).isFlat_iff_of_moduleIso G eC T
    obtain ⟨d⟩ := hdev i
    cases d with
    | empty hz =>
      refine ⟨⊤, trivial, IsCutOutByMonoFP.of_forall fun T ↦ (hiff _).mpr ?_⟩
      exact C.isFlat_of_isFlatOverInDimensionsGE
        (isFlatOverInDimensionsGE_of_isZero C.f C.F hz C.n) _
    | nonempty data =>
      have : IsAffine (Y i) := isAffine_source_of_devissageChain data.chain
      have hfpC : FinitePresentation C.f :=
        FinitePresentation.mk inferInstance inferInstance inferInstance
      have hflatC : IsFlatOverInDimensionsGE C.f C.F (C.n + 1) :=
        (isFlatOverInDimensionsGE_iff_of_moduleIso _ eC _).mp
          (hflatE.etale_comp (h i) E.f E.F)
      obtain ⟨W, hsW, Z, hm, hfp, ⟨e⟩⟩ :=
        C.exists_mono_finitePresentation_representableBy U.point ⟨.nonempty data⟩ hfpC hflatC
      exact ⟨W, hsW, (C.isCutOutByMonoFP_of_representableBy W hm hfp e).of_iff
        fun T ↦ (hiff _).symm⟩
  obtain ⟨V, hsV, hV⟩ := exists_open_of_charts E hpE U.point h hcov hloc
  refine ⟨V.toScheme, V.ι ≫ U.toBase, inferInstance, ⟨⟨U.point, hsV⟩, U.map_point⟩, ?_⟩
  rw [D.isCutOutByMonoFP_comp_iff]
  exact hV.of_iff fun T ↦ D.baseChange_isFlat_iff U.toBase _

/-- **Stacks Project, Tag 05UG.** In Situation 05MT, assume moreover that `f` is of finite
presentation, that `F` is an `𝒪_X`-module of finite presentation, and that `F` is pure relative
to `S`. Then `F_n` is representable by a monomorphism `Z_n ⟶ S` of finite presentation.

`f` of finite presentation is spelled out as locally of finite presentation, quasi-compact and
quasi-separated. -/
@[stacks 05UG]
theorem exists_mono_finitePresentation_representableBy_of_isPure [LocallyOfFinitePresentation D.f]
    [QuasiCompact D.f] [QuasiSeparated D.f] [D.F.IsFinitePresentation]
    (hpure : IsPureRelative D.f D.F) :
    ∃ Z : Over D.S, Mono Z.hom ∧ FinitePresentation Z.hom ∧
      Nonempty (D.flatDimensionFunctor.RepresentableBy Z) :=
  D.rep_iff.mp (D.rep_of_keyCase keyCase hpure)

end FlatDimensionSituation

end AlgebraicGeometry

end
