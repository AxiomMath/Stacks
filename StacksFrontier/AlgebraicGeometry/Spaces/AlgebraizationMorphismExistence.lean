module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphismGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.Statements
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AffineExtensionSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange

/-!
# Algebraization of morphisms of algebraic spaces: existence from Stacks 08BG

This is the graph argument of the proof of Stacks 0A4Z. The graphs of a compatible system
`gₙ : X ×_V Spec (A / Iⁿ) ⟶ T` are closed subspaces of a quasi-compact open subspace `W₀` of
`X ×_Q T` forming a cartesian system; Stacks 08BG (taken as the hypothesis `h08BG`, the
proposition `AlgebraicGeometry.Space.ClosedSubspaceTowerAlgebraizes`) algebraizes them to a
closed subspace `Z ⊆ W₀` proper over `V`. The projection `Z ⟶ X` is a closed immersion by
Stacks 05XA, because it is one over `Spec (A / I)` and `I` lies in the Jacobson radical of `A`;
its image contains every infinitesimal fibre, so it is an isomorphism by rigidity
(`AlgebraicGeometry.Space.eq_top_of_forall_fibreThickening_le`).

## Main results

* `AlgebraicGeometry.Space.isIso_baseChangeOverBase_of`: a criterion for a base change to be an
  isomorphism, on sections.
* `AlgebraicGeometry.Space.exists_comp_eq_of_closedSubspaceTowerAlgebraizes`: existence of the
  algebraization, given Stacks 08BG.

## References

* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
* [Stacks Project, Tag 05XA](https://stacks.math.columbia.edu/tag/05XA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

section BaseChange

/-- A morphism of presheaves is an isomorphism as soon as composing with it is bijective on
morphisms out of every representable presheaf. -/
theorem isIso_of_forall_bijective_comp {C : Type*} [Category C] {F G : Cᵒᵖ ⥤ Type u}
    (φ : F ⟶ G)
    (h : ∀ U : C, Function.Bijective fun s : (yoneda.obj U ⟶ F) => s ≫ φ) : IsIso φ := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [isIso_iff_bijective]
  have e : (φ.app U : F.obj U → G.obj U) =
      yonedaEquiv ∘ (fun s : (yoneda.obj U.unop ⟶ F) => s ≫ φ) ∘ yonedaEquiv.symm := by
    funext x
    change _ = yonedaEquiv (yonedaEquiv.symm x ≫ φ)
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [e]
  exact yonedaEquiv.bijective.comp ((h U.unop).comp yonedaEquiv.symm.bijective)

/-- A monomorphism of functors to types whose range is everything is an isomorphism. -/
theorem isIso_of_mono_of_range_eq_top {C : Type*} [Category C] {F G : C ⥤ Type u} (f : F ⟶ G)
    [Mono f] (h : Subfunctor.range f = ⊤) : IsIso f := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f).1 ‹Mono f› U), fun x => ?_⟩
  obtain ⟨z, hz⟩ : x ∈ (Subfunctor.range f).obj U := by
    rw [h]
    trivial
  exact ⟨z, hz⟩

/-- The image under `a` of the first projection of a section of `pullback a b` lies in the range
of `b`. -/
theorem app_yonedaEquiv_comp_pullback_fst_mem_range {C : Type*} [Category C]
    {F G H : Cᵒᵖ ⥤ Type u} (a : F ⟶ H) (b : G ⟶ H) {U : C} (s : yoneda.obj U ⟶ pullback a b) :
    a.app _ (yonedaEquiv (s ≫ pullback.fst a b)) ∈ Set.range (b.app _) := by
  refine ⟨yonedaEquiv (s ≫ pullback.snd a b), ?_⟩
  simp only [← yonedaEquiv_comp, Category.assoc]
  rw [pullback.condition]

variable {X Y Z Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A base change of `f : Z ⟶ X` over `Y` is an isomorphism** as soon as `f` is injective on
the sections lying over `Y'` and every section of `X` over `Y'` comes from `Z`. -/
theorem isIso_baseChangeOverBase_of (f : Z ⟶ X) (p : Z ⟶ Y) (q : X ⟶ Y) (hfq : f ≫ q = p)
    (g : Y' ⟶ Y)
    (hinj : ∀ U (z z' : Z.obj U), p.app U z ∈ Set.range (g.app U) →
      p.app U z' ∈ Set.range (g.app U) → f.app U z = f.app U z' → z = z')
    (hsurj : ∀ U (x : X.obj U), q.app U x ∈ Set.range (g.app U) → ∃ z, f.app U z = x) :
    IsIso (baseChangeOverBase B S hS f p q hfq g) := by
  have hb : baseChangeOverBase B S hS f p q hfq g ≫ pullback.fst q g = pullback.fst p g ≫ f :=
    pullback.lift_fst _ _ _
  have hb' : baseChangeOverBase B S hS f p q hfq g ≫ pullback.snd q g = pullback.snd p g :=
    pullback.lift_snd _ _ _
  refine isIso_of_forall_bijective_comp _ fun U => ⟨fun s s' hss' => ?_, fun σ => ?_⟩
  · have hss'' : s ≫ baseChangeOverBase B S hS f p q hfq g =
        s' ≫ baseChangeOverBase B S hS f p q hfq g := hss'
    have hsnd : s ≫ pullback.snd p g = s' ≫ pullback.snd p g := by
      rw [← hb', ← Category.assoc, hss'', Category.assoc]
    refine pullback.hom_ext (yonedaEquiv.injective (hinj _ _ _
      (app_yonedaEquiv_comp_pullback_fst_mem_range p g s)
      (app_yonedaEquiv_comp_pullback_fst_mem_range p g s') ?_)) hsnd
    simp only [← yonedaEquiv_comp, Category.assoc]
    rw [← hb, ← Category.assoc, hss'', Category.assoc]
  · obtain ⟨z, hz⟩ := hsurj _ _ (app_yonedaEquiv_comp_pullback_fst_mem_range q g σ)
    have hcond : yonedaEquiv.symm z ≫ p = (σ ≫ pullback.snd q g) ≫ g := by
      refine yonedaEquiv.injective ?_
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← hfq, NatTrans.comp_app, types_comp_apply,
        hz]
      simp only [← yonedaEquiv_comp, Category.assoc]
      rw [pullback.condition]
    refine ⟨pullback.lift (yonedaEquiv.symm z) (σ ≫ pullback.snd q g) hcond, ?_⟩
    refine pullback.hom_ext ?_ ?_
    · refine yonedaEquiv.injective ?_
      change yonedaEquiv ((pullback.lift (yonedaEquiv.symm z) (σ ≫ pullback.snd q g) hcond ≫
        baseChangeOverBase B S hS f p q hfq g) ≫ pullback.fst q g) = _
      rw [Category.assoc, hb, pullback.lift_fst_assoc, yonedaEquiv_comp, Equiv.apply_symm_apply,
        hz]
    · change (pullback.lift (yonedaEquiv.symm z) (σ ≫ pullback.snd q g) hcond ≫
        baseChangeOverBase B S hS f p q hfq g) ≫ pullback.snd q g = _
      rw [Category.assoc, hb', pullback.lift_snd]

/-- A morphism `f : Z ⟶ X` over `Y` is a closed immersion as soon as its base change along the
identity of `Y` is one. -/
theorem isClosedImmersion_of_isClosedImmersion_baseChangeOverBase_id (f : Z ⟶ X) (q : X ⟶ Y)
    (h : IsClosedImmersion B S hS (baseChangeOverBase B S hS f (f ≫ q) q rfl (𝟙 Y))) :
    IsClosedImmersion B S hS f := by
  have : IsIso (pullback.fst (f ≫ q) (𝟙 Y)) :=
    (IsPullback.of_hasPullback (f ≫ q) (𝟙 Y)).isIso_fst_of_isIso
  have : IsIso (pullback.fst q (𝟙 Y)) := (IsPullback.of_hasPullback q (𝟙 Y)).isIso_fst_of_isIso
  have e : f = inv (pullback.fst (f ≫ q) (𝟙 Y)) ≫
      baseChangeOverBase B S hS f (f ≫ q) q rfl (𝟙 Y) ≫ pullback.fst q (𝟙 Y) := by
    rw [show baseChangeOverBase B S hS f (f ≫ q) q rfl (𝟙 Y) ≫ pullback.fst q (𝟙 Y) =
        pullback.fst (f ≫ q) (𝟙 Y) ≫ f from pullback.lift_fst _ _ _, IsIso.inv_hom_id_assoc]
  rw [e]
  exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _)
    (isClosedImmersion_comp B S hS _ _ h (isClosedImmersion_of_isIso B S hS _))

end BaseChange

section Existence

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  {X : AlgebraicSpaces B S hS} {fX : X ⟶ schemeSpace V}
  {Q T : AlgebraicSpaces B S hS} {q : X ⟶ Q} {t : T ⟶ Q}
  {g : ∀ n, fibreSpace V I fX n ⟶ T}

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- **A quasi-compact open subspace of `X ×_Q T` through which every graph factors.** -/
theorem exists_quasiCompact_openSubspace_range_fibreGraph_le (hX : IsProper B S hS fX.hom)
    (hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q)
    (hc : ∀ n, fibreTransition V I fX (Nat.le_succ n) ≫ g (n + 1) = g n) :
    ∃ W₀ : Subfunctor (pullback q.hom t.hom), IsOpenSubspace B S hS W₀ ∧
      IsQuasiCompactSpace B S hS W₀.toFunctor ∧
      ∀ n, Subfunctor.range (fibreGraph hg n) ≤ W₀ := by
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hWp : IsAlgebraicSpace B S hS (pullback q.hom t.hom) :=
    isAlgebraicSpace_pullback B S hS q.hom t.hom X.2 T.2 Q.2
  have hX₁ : IsQuasiCompactSpace B S hS (fibreSpace V I fX 1).1 :=
    isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS V inferInstance
      (fibreSpace V I fX 1).2 hV _ (universallyClosed_comp B S hS X.2 hV _ _
        (universallyClosed_of_isClosedImmersion B S hS (fibreSpace V I fX 1).2 X.2 _
          (fibreThickening V I fX 1).2.2) hX.2.2)
  have := compactSpace_points_of_isQuasiCompactSpace B S hS (fibreSpace V I fX 1).2 hX₁
  have hK : IsCompact (Set.range (pointsMap B S hS _ (fibreGraph hg 1))) :=
    isCompact_range (continuous_pointsMap B S hS _)
  obtain ⟨Zc, c, hZc, hc_et, hKc⟩ := exists_affine_etale_chart_of_isCompact B S hS _ hWp hK
  obtain ⟨hopen, hψet, -, hψsurj⟩ :=
    isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range_yoneda B S hS hWp Zc c hc_et
  refine ⟨_, hopen, ?_, range_fibreGraph_le_openSubspaceOfPoints hg hc hKc⟩
  exact (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hopen.1).2
    ⟨Zc, _, hZc, hψsurj, isEtale_of_presheaf_etale B S hS hψet⟩

/-- The structure morphism to `V` of an open subspace of `X ×_Q T`, through the first factor. -/
abbrev graphChartToBase (W₀ : Subfunctor (pullback q.hom t.hom)) (hW₀ : IsOpenSubspace B S hS W₀) :
    (⟨W₀.toFunctor, hW₀.1⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace V :=
  ObjectProperty.homMk (W₀.ι ≫ pullback.fst q.hom t.hom ≫ fX.hom)

/-- If a section `w` of `W₀` is the image of a section `x` of the `m`-th graph's source, then `w`
lies in the `n`-th infinitesimal fibre of `W₀` iff `x` does. -/
private theorem mem_fibreThickening_graphChartToBase_iff {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} {X : AlgebraicSpaces B S hS}
    {fX : X ⟶ schemeSpace V} {Q T : AlgebraicSpaces B S hS} {q : X ⟶ Q} {t : T ⟶ Q}
    {g : ∀ n, fibreSpace V I fX n ⟶ T} (hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q)
    {W₀ : Subfunctor (pullback q.hom t.hom)} (hW₀ : IsOpenSubspace B S hS W₀) (m n : ℕ) {U}
    {x : (fibreSpace V I fX m).1.obj U} {w : W₀.toFunctor.obj U}
    (hx : (fibreGraph hg m).app U x = W₀.ι.app U w) :
    w ∈ (fibreThickening V I (graphChartToBase (fX := fX) W₀ hW₀) n).1.obj U ↔
      fX.hom.app U x.1 ∈ (adicQuotientSubspace V I n).1.obj U := by
  have e : (pullback.fst q.hom t.hom).app U ((fibreGraph hg m).app U x) = x.1 :=
    congrArg (fun k => k.app U x) (fibreGraph_fst hg m)
  change fX.hom.app U ((pullback.fst q.hom t.hom).app U (W₀.ι.app U w)) ∈
    (adicQuotientSubspace V I n).1.obj U ↔ _
  rw [← hx, e]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- The `n`-th graph lies in the `n`-th infinitesimal fibre of `W₀`. -/
theorem preimage_range_fibreGraph_le_fibreThickening
    (hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q) {W₀ : Subfunctor (pullback q.hom t.hom)}
    (hW₀ : IsOpenSubspace B S hS W₀) (n : ℕ) :
    (Subfunctor.range (fibreGraph hg n)).preimage W₀.ι ≤
      (fibreThickening V I (graphChartToBase (fX := fX) W₀ hW₀) n).1 := by
  rintro U w ⟨x, hx⟩
  exact (mem_fibreThickening_graphChartToBase_iff hg hW₀ n n hx).2 x.2

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- The graphs form a cartesian system: the `n`-th graph is the `(n + 1)`-st one cut down to the
`n`-th infinitesimal fibre of `W₀`. -/
theorem preimage_range_fibreGraph_eq_inf_fibreThickening
    (hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q)
    (hc : ∀ n, fibreTransition V I fX (Nat.le_succ n) ≫ g (n + 1) = g n)
    {W₀ : Subfunctor (pullback q.hom t.hom)} (hW₀ : IsOpenSubspace B S hS W₀) (n : ℕ) :
    (Subfunctor.range (fibreGraph hg n)).preimage W₀.ι =
      (Subfunctor.range (fibreGraph hg (n + 1))).preimage W₀.ι ⊓
        (fibreThickening V I (graphChartToBase (fX := fX) W₀ hW₀) n).1 := by
  refine le_antisymm ?_ ?_
  · intro U w hw
    refine ⟨?_, preimage_range_fibreGraph_le_fibreThickening hg hW₀ n U hw⟩
    obtain ⟨x, hx⟩ := hw
    refine ⟨(fibreTransition V I fX (Nat.le_succ n)).hom.app U x, ?_⟩
    rw [← hx]
    exact congrArg (fun k => k.app U x)
      (fibreTransition_comp_fibreGraph hg hc (Nat.le_succ n))
  · rintro U w ⟨⟨x, hx⟩, hthick⟩
    have hmem := (mem_fibreThickening_graphChartToBase_iff hg hW₀ (n + 1) n hx).1 hthick
    refine ⟨⟨x.1, hmem⟩, ?_⟩
    rw [← hx]
    exact (congrArg (fun k => k.app U ⟨x.1, hmem⟩)
      (fibreTransition_comp_fibreGraph hg hc (Nat.le_succ n))).symm

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- The first graph, as a closed subspace of `W₀`, is proper over `V`. -/
theorem isProper_subspaceInclusion_preimage_range_fibreGraph_one (hX : IsProper B S hS fX.hom)
    (hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q) {W₀ : Subfunctor (pullback q.hom t.hom)}
    (hW₀ : IsOpenSubspace B S hS W₀) (hΓ : Subfunctor.range (fibreGraph hg 1) ≤ W₀)
    (hγ : IsClosedSubspace B S hS ((Subfunctor.range (fibreGraph hg 1)).preimage W₀.ι)) :
    IsProper B S hS (subspaceInclusion B S hS ⟨W₀.toFunctor, hW₀.1⟩ ⟨_, hγ⟩ ≫
      graphChartToBase (fX := fX) W₀ hW₀).hom := by
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  let Γ₁ : ClosedSubspaces B S hS W₀.toFunctor := ⟨_, hγ⟩
  change IsProper B S hS (subspaceInclusion B S hS ⟨W₀.toFunctor, hW₀.1⟩ Γ₁ ≫
    graphChartToBase (fX := fX) W₀ hW₀).hom
  let γ₀ : (fibreSpace V I fX 1).1 ⟶ W₀.toFunctor := Subfunctor.lift (fibreGraph hg 1) hΓ
  let e : (fibreSpace V I fX 1).1 ⟶ Γ₁.1.toFunctor :=
    Subfunctor.lift γ₀ (by
      rintro U _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩)
  have he : e ≫ Γ₁.1.ι ≫ W₀.ι ≫ pullback.fst q.hom t.hom = (fibreInclusion V I fX 1).hom := by
    change γ₀ ≫ W₀.ι ≫ pullback.fst q.hom t.hom = _
    rw [Subfunctor.lift_ι_assoc, fibreGraph_fst]
  have : IsIso e := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [isIso_iff_bijective]
    refine ⟨fun x x' hxx' => ?_, fun w => ?_⟩
    · have e1 := congrArg (fun k => k.app U x) he
      have e2 := congrArg (fun k => k.app U x') he
      simp only [NatTrans.comp_app, types_comp_apply] at e1 e2
      rw [hxx'] at e1
      exact Subtype.ext (e1.symm.trans e2)
    · obtain ⟨x, hx⟩ := w.2
      exact ⟨x, Subtype.ext (Subtype.ext hx)⟩
  have hcomp : (subspaceInclusion B S hS ⟨W₀.toFunctor, hW₀.1⟩ Γ₁ ≫
      graphChartToBase (fX := fX) W₀ hW₀).hom =
        inv e ≫ (fibreInclusion V I fX 1).hom ≫ fX.hom := by
    rw [IsIso.eq_inv_comp, ← he]
    rfl
  rw [hcomp]
  exact isProper_comp' B S hS _ _ (fibreSpace V I fX 1).2 hV (isProper_of_isIso B S hS _)
    (isProper_comp' B S hS _ _ X.2 hV (isProper_of_isClosedImmersion B S hS
      (fibreSpace V I fX 1).2 X.2 _ (fibreThickening V I fX 1).2.2) hX)

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- **The graphs algebraize** (Stacks 08BG applied to the graphs): inside a quasi-compact open
subspace `W₀` of `X ×_Q T` containing all graphs there is a closed subspace `Z`, proper over `V`,
whose intersection with each infinitesimal fibre of `W₀` is the `n`-th graph. -/
theorem exists_closedSubspace_inf_eq_range_fibreGraph (hX : IsProper B S hS fX.hom)
    (htsep : IsSeparated B S hS t.hom) (htlft : IsLocallyOfFiniteType B S hS t.hom)
    (hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q)
    (hc : ∀ n, fibreTransition V I fX (Nat.le_succ n) ≫ g (n + 1) = g n)
    (W₀ : Subfunctor (pullback q.hom t.hom)) (hW₀ : IsOpenSubspace B S hS W₀)
    (hW₀qc : IsQuasiCompactSpace B S hS W₀.toFunctor)
    (hΓ : ∀ n, Subfunctor.range (fibreGraph hg n) ≤ W₀)
    (h08BG : ClosedSubspaceTowerAlgebraizes V I (graphChartToBase (fX := fX) W₀ hW₀)) :
    ∃ Z' : ClosedSubspaces B S hS W₀.toFunctor,
      IsProper B S hS (Z'.1.ι ≫ W₀.ι ≫ pullback.fst q.hom t.hom ≫ fX.hom) ∧
      ∀ n, 1 ≤ n → Z'.1 ⊓ (fibreThickening V I (graphChartToBase (fX := fX) W₀ hW₀) n).1 =
        (Subfunctor.range (fibreGraph hg n)).preimage W₀.ι := by
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hWp : IsAlgebraicSpace B S hS (pullback q.hom t.hom) :=
    isAlgebraicSpace_pullback B S hS q.hom t.hom X.2 T.2 Q.2
  have hγ : ∀ n, IsClosedSubspace B S hS (Subfunctor.range (fibreGraph hg n)) := fun n =>
    isClosedSubspace_range_of_isClosedImmersion B S hS _ (fibreSpace V I fX n).2
      (isClosedImmersion_fibreGraph hg htsep n)
  let Γ' : ℕ → ClosedSubspaces B S hS W₀.toFunctor := fun n =>
    ⟨(Subfunctor.range (fibreGraph hg n)).preimage W₀.ι,
      isClosedSubspace_preimage B S hS W₀.ι _ hWp hW₀.1 (hγ n)⟩
  have hsep : IsSeparated B S hS (graphChartToBase (fX := fX) W₀ hW₀).hom :=
    isSeparated_comp B S hS _ _
      (isSeparated_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hW₀.2))
      (isSeparated_comp B S hS _ _ (isSeparated_pullbackFst B S hS q.hom htsep) hX.1)
  have hlft : IsLocallyOfFiniteType B S hS (graphChartToBase (fX := fX) W₀ hW₀).hom :=
    isLocallyOfFiniteType_comp' B S hS _ _ hWp hV
      (isLocallyOfFiniteType_of_isImmersion B S hS _
        (isImmersion_of_isOpenImmersion B S hS hW₀.2))
      (isLocallyOfFiniteType_comp' B S hS _ _ X.2 hV
        (isLocallyOfFiniteType_pullback_fst' B S hS T.2 Q.2 X.2 t.hom q.hom htlft) hX.2.1.1)
  have hqc : IsQuasiCompact B S hS (graphChartToBase (fX := fX) W₀ hW₀).hom :=
    AffineExtension.isQuasiCompact_to_yoneda B S hS hW₀.1 hW₀qc inferInstance _
  exact h08BG inferInstance hsep ⟨hlft, hqc⟩ Γ'
    (fun n _ => preimage_range_fibreGraph_le_fibreThickening hg hW₀ n)
    (fun n _ => preimage_range_fibreGraph_eq_inf_fibreThickening hg hc hW₀ n)
    (isProper_subspaceInclusion_preimage_range_fibreGraph_one hX hg hW₀ (hΓ 1) (Γ' 1).2)

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- The `n`-th graph factors through any closed subspace `Z'` of `W₀` whose intersection with the
`n`-th infinitesimal fibre of `W₀` is that graph. -/
theorem exists_comp_eq_fibreGraph_of_inf_eq {hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q}
    {W₀ : Subfunctor (pullback q.hom t.hom)} {hW₀ : IsOpenSubspace B S hS W₀}
    (hΓ : ∀ n, Subfunctor.range (fibreGraph hg n) ≤ W₀)
    {Z' : ClosedSubspaces B S hS W₀.toFunctor} {n : ℕ}
    (hZ' : Z'.1 ⊓ (fibreThickening V I (graphChartToBase (fX := fX) W₀ hW₀) n).1 =
      (Subfunctor.range (fibreGraph hg n)).preimage W₀.ι) :
    ∃ s : (fibreSpace V I fX n).1 ⟶ Z'.1.toFunctor, s ≫ Z'.1.ι ≫ W₀.ι = fibreGraph hg n := by
  let γ₀ : (fibreSpace V I fX n).1 ⟶ W₀.toFunctor := Subfunctor.lift (fibreGraph hg n) (hΓ n)
  have hle : Subfunctor.range γ₀ ≤ Z'.1 := by
    rintro U _ ⟨x, rfl⟩
    have hmem : γ₀.app U x ∈ ((Subfunctor.range (fibreGraph hg n)).preimage W₀.ι).obj U :=
      ⟨x, rfl⟩
    rw [← hZ'] at hmem
    exact hmem.1
  exact ⟨Subfunctor.lift γ₀ hle, rfl⟩

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- An open subspace of `V` through which `Spec (A / I) ⟶ V` factors is surjective on points. -/
theorem surjective_pointsMap_of_comp_eq_adicCompletionQuotientObjHom
    {W' : Subfunctor (schemeSpace V).obj} (hW' : IsOpenSubspace B S hS W')
    {r : yoneda.obj (adicCompletionQuotientObj B S hS V I 1) ⟶ W'.toFunctor}
    (hr : r ≫ W'.ι = (yoneda.map (adicCompletionQuotientObjHom B S hS V I 1) :
      yoneda.obj (adicCompletionQuotientObj B S hS V I 1) ⟶ (schemeSpace V).obj)) :
    Function.Surjective (pointsMap B S hS _ W'.ι) := by
  have hopen := isOpen_range_pointsMap_of_isOpenImmersion B S hS W'.ι hW'.2
  have hempty := eq_empty_of_isClosed_of_disjoint_range_adicCompletionQuotientObjHom V I
    hopen.isClosed_compl (Set.disjoint_left.2 ?_)
  · intro v
    by_contra hv
    exact Set.eq_empty_iff_forall_notMem.1 hempty v hv
  · rintro v hv ⟨y, rfl⟩
    apply hv
    refine ⟨pointsMap B S hS _ r y, ?_⟩
    rw [← pointsMap_comp_apply, hr]
    rfl

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- **The projection to `X` of the algebraized graph is a closed immersion** (Stacks 05XA): over
`Spec (A / I)` it is an isomorphism, and `I` lies in the Jacobson radical of `A`. -/
theorem isClosedImmersion_closedSubspace_comp_pullbackFst (hX : IsProper B S hS fX.hom)
    {hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q}
    {W₀ : Subfunctor (pullback q.hom t.hom)} {hW₀ : IsOpenSubspace B S hS W₀}
    {Z' : ClosedSubspaces B S hS W₀.toFunctor}
    (hZ'p : IsProper B S hS (Z'.1.ι ≫ W₀.ι ≫ pullback.fst q.hom t.hom ≫ fX.hom))
    (hZ' : Z'.1 ⊓ (fibreThickening V I (graphChartToBase (fX := fX) W₀ hW₀) 1).1 =
      (Subfunctor.range (fibreGraph hg 1)).preimage W₀.ι)
    (hle : (fibreThickening V I fX 1).1 ≤
      Subfunctor.range ((Z'.1.ι ≫ W₀.ι) ≫ pullback.fst q.hom t.hom)) :
    IsClosedImmersion B S hS ((Z'.1.ι ≫ W₀.ι) ≫ pullback.fst q.hom t.hom) := by
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  let π : Z'.1.toFunctor ⟶ pullback q.hom t.hom := Z'.1.ι ≫ W₀.ι
  let p : Z'.1.toFunctor ⟶ X.1 := π ≫ pullback.fst q.hom t.hom
  have hpX : IsProper B S hS (p ≫ fX.hom) := by simpa only [p, π, Category.assoc] using hZ'p
  obtain ⟨W', hW'open, hW'⟩ := exists_isOpenSubspace_iff_isClosedImmersion_baseChange B S hS
    Z'.2.1 X.2 hV p (p ≫ fX.hom) fX.hom rfl hpX.2.1.1 hpX.2.2 hX.1
  let j₁ : yoneda.obj (adicCompletionQuotientObj B S hS V I 1) ⟶ (schemeSpace V).obj :=
    yoneda.map (adicCompletionQuotientObjHom B S hS V I 1)
  have hpre : ∀ U (z : Z'.1.toFunctor.obj U), (p ≫ fX.hom).app U z ∈ Set.range (j₁.app U) →
      ∃ x : (fibreSpace V I fX 1).1.obj U, (fibreGraph hg 1).app U x = π.app U z := by
    intro U z hz
    have hw : Z'.1.ι.app U z ∈
        (Z'.1 ⊓ (fibreThickening V I (graphChartToBase (fX := fX) W₀ hW₀) 1).1).obj U :=
      ⟨z.2, hz⟩
    rw [hZ'] at hw
    exact hw
  have hpx : ∀ U (z : Z'.1.toFunctor.obj U) (x : (fibreSpace V I fX 1).1.obj U),
      (fibreGraph hg 1).app U x = π.app U z → p.app U z = x.1 := by
    intro U z x hx
    change (pullback.fst q.hom t.hom).app U (π.app U z) = x.1
    rw [← hx]
    exact congrArg (fun k => k.app U x) (fibreGraph_fst hg 1)
  have hbc : IsIso (baseChangeOverBase B S hS p (p ≫ fX.hom) fX.hom rfl j₁) := by
    refine isIso_baseChangeOverBase_of p (p ≫ fX.hom) fX.hom rfl _ ?_ ?_
    · intro U z z' hz hz' hzz'
      obtain ⟨x, hx⟩ := hpre U z hz
      obtain ⟨x', hx'⟩ := hpre U z' hz'
      obtain rfl : x = x' :=
        Subtype.ext ((hpx U z x hx).symm.trans (hzz'.trans (hpx U z' x' hx')))
      exact Subtype.ext (Subtype.ext (hx.symm.trans hx'))
    · intro U x hx
      have hx1 : x ∈ (fibreThickening V I fX 1).1.obj U := hx
      exact hle U hx1
  obtain ⟨r, hr⟩ := (hW' _ (isAlgebraicSpace_yoneda B S hS _) j₁).2
    (@isClosedImmersion_of_isIso B S hS _ _ _ hbc)
  have : IsIso W'.ι := isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS W'.ι hW'open.2
    (surjective_pointsMap_of_comp_eq_adicCompletionQuotientObjHom hW'open hr)
  exact isClosedImmersion_of_isClosedImmersion_baseChangeOverBase_id p fX.hom
    ((hW' _ hV (𝟙 _)).1 ⟨inv W'.ι, IsIso.inv_hom_id _⟩)

/-- **Existence of the algebraization, given Stacks 08BG.** Let `A = Γ(V, 𝒪_V)` be Noetherian and
`I`-adically complete, `X` proper over `V`, and `t : T ⟶ Q` separated and locally of finite type.
A system of morphisms `gₙ : X ×_V Spec (A / Iⁿ) ⟶ T` over `Q`, compatible with the inclusions of
the infinitesimal fibres, is the restriction of a morphism `X ⟶ T` over `Q`.

The graphs of the `gₙ` are closed subspaces of `X ×_Q T` forming a cartesian system inside a
quasi-compact open subspace `W₀`; by Stacks 08BG (the hypothesis `h08BG`) they are the
infinitesimal fibres of a closed subspace `Z ⊆ W₀` proper over `V`. The projection `p : Z ⟶ X`
restricts over `Spec (A / I)` to an isomorphism, so by Stacks 05XA it is a closed immersion over
an open subspace of `V` containing `V(I)`, which is all of `V` since `I` lies in the Jacobson
radical. Its image contains every infinitesimal fibre, so `p` is an isomorphism by rigidity, and
the algebraization is `p⁻¹` followed by the second projection. -/
theorem exists_comp_eq_of_closedSubspaceTowerAlgebraizes
    (h08BG : ∀ (W : AlgebraicSpaces B S hS) (f : W ⟶ schemeSpace V),
      ClosedSubspaceTowerAlgebraizes V I f)
    (hX : IsProper B S hS fX.hom)
    (htsep : IsSeparated B S hS t.hom) (htlft : IsLocallyOfFiniteType B S hS t.hom)
    (hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q)
    (hc : ∀ n, fibreTransition V I fX (Nat.le_succ n) ≫ g (n + 1) = g n) :
    ∃ h : X ⟶ T, h ≫ t = q ∧ ∀ n, fibreInclusion V I fX n ≫ h = g n := by
  classical
  obtain ⟨W₀, hW₀, hW₀qc, hΓ⟩ := exists_quasiCompact_openSubspace_range_fibreGraph_le hX hg hc
  obtain ⟨Z', hZ'p, hZ'⟩ := exists_closedSubspace_inf_eq_range_fibreGraph hX htsep htlft hg hc
    W₀ hW₀ hW₀qc hΓ (h08BG _ _)
  let π : Z'.1.toFunctor ⟶ pullback q.hom t.hom := Z'.1.ι ≫ W₀.ι
  let p : Z'.1.toFunctor ⟶ X.1 := π ≫ pullback.fst q.hom t.hom
  have hs : ∀ n, 1 ≤ n → ∃ s : (fibreSpace V I fX n).1 ⟶ Z'.1.toFunctor,
      s ≫ π = fibreGraph hg n := fun n hn => exists_comp_eq_fibreGraph_of_inf_eq hΓ (hZ' n hn)
  choose s hsπ using hs
  have hsp : ∀ n hn, s n hn ≫ p = (fibreInclusion V I fX n).hom := fun n hn => by
    change s n hn ≫ π ≫ pullback.fst q.hom t.hom = _
    rw [← Category.assoc, hsπ, fibreGraph_fst]
  have hle : ∀ n, 1 ≤ n → (fibreThickening V I fX n).1 ≤ Subfunctor.range p := fun n hn => by
    rintro U x hx
    exact ⟨(s n hn).app U ⟨x, hx⟩, congrArg (fun k => k.app U ⟨x, hx⟩) (hsp n hn)⟩
  have hpci : IsClosedImmersion B S hS p :=
    isClosedImmersion_closedSubspace_comp_pullbackFst hX hZ'p (hZ' 1 le_rfl) (hle 1 le_rfl)
  have hR : IsClosedSubspace B S hS (Subfunctor.range p) :=
    isClosedSubspace_range_of_isClosedImmersion B S hS p Z'.2.1 hpci
  have hRtop : Subfunctor.range p = ⊤ := by
    refine eq_top_of_forall_fibreThickening_le V I fX hX ⟨_, hR⟩ fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (fibreThickening_le V I fX (Nat.zero_le 1)).trans (hle 1 le_rfl)
    · exact hle n hn
  have := mono_of_isClosedImmersion B S hS p hpci
  have : IsIso p := isIso_of_mono_of_range_eq_top p hRtop
  refine ⟨ObjectProperty.homMk (inv p ≫ π ≫ pullback.snd q.hom t.hom), ?_, fun n => ?_⟩
  · refine ObjectProperty.hom_ext _ ?_
    change (inv p ≫ π ≫ pullback.snd q.hom t.hom) ≫ t.hom = q.hom
    rw [Category.assoc, Category.assoc, ← pullback.condition, IsIso.inv_comp_eq]
    rfl
  · have key : ∀ m, 1 ≤ m → (fibreInclusion V I fX m).hom ≫ inv p ≫ π ≫
        pullback.snd q.hom t.hom = (g m).hom := fun m hm => by
      rw [← hsp m hm, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, hsπ,
        fibreGraph_snd]
    refine ObjectProperty.hom_ext _ ?_
    change (fibreInclusion V I fX n).hom ≫ inv p ≫ π ≫ pullback.snd q.hom t.hom = (g n).hom
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e₁ := congrArg (fun k => k.hom) (fibreTransition_comp V I fX (Nat.zero_le 1))
      have e₂ := congrArg (fun k => k.hom) (hc 0)
      simp only [ObjectProperty.FullSubcategory.comp_hom] at e₁ e₂
      rw [← e₁, ← e₂, Category.assoc, key 1 le_rfl]
    · exact key n hn

end Existence

end AlgebraicGeometry.Space
