module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceIso
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitOpenPart
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluing

/-!
# An isomorphism over the complement of `Z` in the limit holds at a stage

Let `V = lim V_i` be a cofiltered limit of affine Noetherian objects of the big fppf site,
`Z ⊆ |V_i|` closed, and `p_i : Y_i ⟶ V_i` a proper morphism of finite presentation from an
algebraic space whose base change `p : Y ⟶ V` is an isomorphism over `V ∖ Z`. Then the base
change of `p_i` to some later stage `V_j` is an isomorphism over `V_j ∖ Z`.

The complement of `Z` is covered by finitely many basic opens `D(f)`; over each the isomorphism
holds at a stage (`AlgebraicGeometry.Space.exists_stage_isIso_of_isLimit_baseChange`); at a
common stage lifts over `V_j ∖ Z` exist locally and are unique, so they glue.

This is the step "we may assume `V'_λ ⟶ V_λ` is an isomorphism over `V_λ ∖ Z_λ`" of the proof of
Stacks 0GI5.

## Main results

* `AlgebraicGeometry.Space.isIso_pullback_fst_iff_existsUnique`,
  `AlgebraicGeometry.Space.isIso_pullback_snd_ι_iff_existsUnique`: isomorphisms of base changes
  as unique lifting.
* `AlgebraicGeometry.Space.exists_stage_isIso_openSubspace_of_isLimit`: the descent.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If the second projection of a pullback square is an isomorphism, maps into its base factor
lift uniquely through the first leg. -/
private theorem existsUnique_lift_of_isPullback_of_isIso {C : Type*} [Category C]
    {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [IsIso snd] {W : C} (w : W ⟶ Y) :
    ∃! y : W ⟶ X, y ≫ f = w ≫ g := by
  refine ⟨w ≫ inv snd ≫ fst, by simp [h.w], fun y hy => ?_⟩
  have e : h.lift y w hy = w ≫ inv snd := by rw [IsIso.eq_comp_inv, h.lift_snd]
  simpa [h.lift_fst] using congrArg (· ≫ fst) e

/-- The base change of `q` along `φ : h_O ⟶ h_V` is an isomorphism exactly when every morphism
from a representable presheaf to `h_O` lifts uniquely through `q`. -/
theorem isIso_pullback_fst_iff_existsUnique {O V : BigFppfOver B S hS} (φ : O ⟶ V)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : Y ⟶ yoneda.obj V) :
    IsIso (pullback.fst (yoneda.map φ) q) ↔
      ∀ (W : BigFppfOver B S hS) (w : yoneda.obj W ⟶ yoneda.obj O),
        ∃! y : yoneda.obj W ⟶ Y, y ≫ q = w ≫ yoneda.map φ := by
  refine ⟨fun h W w => ?_, fun h => ?_⟩
  · have := h
    exact existsUnique_lift_of_isPullback_of_isIso
      (IsPullback.of_hasPullback (yoneda.map φ) q).flip w
  · obtain ⟨y₀, hy₀, -⟩ := h O (𝟙 _)
    let s := pullback.lift (𝟙 _) y₀ (by rw [hy₀])
    have hs : s ≫ pullback.fst (yoneda.map φ) q = 𝟙 _ := pullback.lift_fst _ _ _
    have hs' : s ≫ pullback.snd (yoneda.map φ) q = y₀ := pullback.lift_snd _ _ _
    refine ⟨s, ?_, hs⟩
    refine hom_ext_yoneda fun W z => ?_
    rw [Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hs, Category.comp_id]
    · rw [Category.assoc, Category.assoc, hs']
      obtain ⟨y, -, hy⟩ := h W (z ≫ pullback.fst _ q)
      refine (hy _ ?_).trans (hy _ ?_).symm
      · dsimp only
        simp only [Category.assoc, hy₀, Category.id_comp]
      · dsimp only
        simp only [Category.assoc, pullback.condition]

/-- The base change of `q` to a subfunctor `U` of `h_V` is an isomorphism exactly when every
morphism from a representable presheaf to `U` lifts uniquely through `q`. -/
theorem isIso_pullback_snd_ι_iff_existsUnique {V : BigFppfOver B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : Y ⟶ yoneda.obj V) (U : Subfunctor (yoneda.obj V)) :
    IsIso (pullback.snd q U.ι) ↔
      ∀ (W : BigFppfOver B S hS) (w : yoneda.obj W ⟶ U.toFunctor),
        ∃! y : yoneda.obj W ⟶ Y, y ≫ q = w ≫ U.ι := by
  refine ⟨fun h W w => ?_, fun h => ?_⟩
  · have := h
    exact existsUnique_lift_of_isPullback_of_isIso (IsPullback.of_hasPullback q U.ι) w
  · have hW : ∀ W : (BigFppfOver B S hS)ᵒᵖ, IsIso ((pullback.snd q U.ι).app W) := by
      intro W
      rw [isIso_iff_bijective]
      constructor
      · intro e₁ e₂ he
        have h₁ : yonedaEquiv.symm e₁ ≫ pullback.snd q U.ι =
            yonedaEquiv.symm e₂ ≫ pullback.snd q U.ι := by
          apply yonedaEquiv.injective
          rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        obtain ⟨y, -, hy⟩ := h W.unop (yonedaEquiv.symm e₁ ≫ pullback.snd q U.ι)
        have k₁ := hy (yonedaEquiv.symm e₁ ≫ pullback.fst q U.ι) (by
          dsimp only
          simp only [Category.assoc, pullback.condition])
        have k₂ := hy (yonedaEquiv.symm e₂ ≫ pullback.fst q U.ι) (by
          dsimp only
          simp only [Category.assoc, pullback.condition]
          rw [← Category.assoc, ← h₁, Category.assoc])
        exact yonedaEquiv.symm.injective (pullback.hom_ext (k₁.trans k₂.symm) h₁)
      · intro x
        obtain ⟨y, hy, -⟩ := h W.unop (yonedaEquiv.symm x)
        refine ⟨yonedaEquiv (pullback.lift y (yonedaEquiv.symm x) hy), ?_⟩
        rw [← yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]
    exact NatIso.isIso_of_isIso_app _

/-- A morphism from a representable presheaf whose points land in `A` factors through the open
subspace cut out by `A`. -/
theorem exists_comp_ι_openSubspaceOfPoints {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : BigFppfOver B S hS} (g : yoneda.obj W ⟶ F) {A : Set (points B S hS F)}
    (hg : Set.range (pointsMap B S hS _ g) ⊆ A) :
    ∃ w : yoneda.obj W ⟶ (openSubspaceOfPoints B S hS F A).toFunctor,
      w ≫ (openSubspaceOfPoints B S hS F A).ι = g := by
  refine ⟨Subfunctor.lift g ?_, Subfunctor.lift_ι _ _⟩
  rintro U _ ⟨y, rfl⟩
  rw [mem_openSubspaceOfPoints_iff]
  have e : yonedaEquiv.symm (g.app U y) = yoneda.map y ≫ g := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [e]
  rintro _ ⟨x, rfl⟩
  rw [pointsMap_comp_apply]
  exact hg ⟨_, rfl⟩

/-- **An isomorphism over the complement of `Z` in the limit holds at a stage**, in the form of
unique lifting: for some `F : j ⟶ i`, every morphism `t : W ⟶ V_j` landing in `V_j ∖ Z` lifts
uniquely through `p_i` along `V_j ⟶ V_i`. -/
theorem exists_stage_existsUnique_lift_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS} {c : Cone E}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)) (i : I)
    (hNoeth : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj (E.obj i), ⊤))
    {Z : Set (points B S hS (yoneda.obj (E.obj i)))} (hZ : IsClosed Z)
    {Yk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hYk : IsAlgebraicSpace B S hS Yk)
    (pk : Yk ⟶ yoneda.obj (E.obj i)) (hpk : IsProper B S hS pk)
    (hpkf : IsLocallyOfFinitePresentation B S hS pk)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ yoneda.obj c.pt) (a : Y ⟶ Yk)
    (hpb : IsPullback p a (yoneda.map (c.π.app i)) pk)
    (hU : IsIso (pullback.snd p (openSubspaceOfPoints B S hS (yoneda.obj c.pt)
      (pointsMap B S hS _ (yoneda.map (c.π.app i)) ⁻¹' Z)ᶜ).ι)) :
    ∃ (j : I) (F : j ⟶ i), ∀ (W : BigFppfOver B S hS) (t : W ⟶ E.obj j),
      Set.range (pointsMap B S hS _ (yoneda.map (t ≫ E.map F))) ⊆ Zᶜ →
      ∃! y : yoneda.obj W ⟶ Yk, y ≫ pk = yoneda.map (t ≫ E.map F) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let V := E.obj i
  let X := T.obj V
  have : IsAffine X := hE i
  obtain ⟨Iid, hI⟩ := exists_ideal_mem_iff_mem_zeroLocus B S hS V hZ
  obtain ⟨gens, hgens⟩ := (IsNoetherian.noetherian Iid : Iid.FG)
  have hmem : ∀ f ∈ gens, f ∈ Iid := fun f hf => hgens ▸ Ideal.subset_span hf
  let O : gens → BigFppfOver B S hS := fun f => opensObject B S hS V (X.basicOpen f.1)
  let ι : ∀ f, O f ⟶ V := fun f => opensObjectι B S hS V (X.basicOpen f.1)
  have hO : ∀ f, IsAffine (T.obj (O f)) := fun f => (isAffineOpen_top X).basicOpen f.1
  have hιo : ∀ f, AlgebraicGeometry.IsOpenImmersion (T.map (ι f)) := fun f => by
    rw [toScheme_map_opensObjectι]
    exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (X.basicOpen f.1).ι)
  have hιf : ∀ f, LocallyOfFinitePresentation (T.map (ι f)) := fun f => by
    have := hιo f
    infer_instance
  have hιZ : ∀ f, Set.range (pointsMap B S hS _ (yoneda.map (ι f))) ⊆ Zᶜ := fun f =>
    Artin.ContractionSituation.range_pointsMap_opensObjectι_basicOpen_subset V hI (hmem f.1 f.2)
  -- at the limit, unique lifts over `V ×_{V_i} D(f)`
  have hlim : ∀ f, IsIso (pullback.fst (yoneda.map (pullback.snd (c.π.app i) (ι f) ≫ ι f)) pk) := by
    intro f
    rw [isIso_pullback_fst_iff_existsUnique]
    intro W w
    let U := openSubspaceOfPoints B S hS (yoneda.obj c.pt)
      (pointsMap B S hS _ (yoneda.map (c.π.app i)) ⁻¹' Z)ᶜ
    obtain ⟨w', hw'⟩ := exists_comp_ι_openSubspaceOfPoints
      (A := (pointsMap B S hS _ (yoneda.map (c.π.app i)) ⁻¹' Z)ᶜ)
      (w ≫ yoneda.map (pullback.fst (c.π.app i) (ι f))) (by
        rintro _ ⟨x, rfl⟩ hx
        apply hιZ f ⟨pointsMap B S hS _ (w ≫ yoneda.map (pullback.snd (c.π.app i) (ι f))) x, ?_⟩ hx
        rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Category.assoc, Category.assoc,
          ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
    have hw'' : w' ≫ U.ι = w ≫ yoneda.map (pullback.fst (c.π.app i) (ι f)) := hw'
    obtain ⟨y, hy, huniq⟩ := (isIso_pullback_snd_ι_iff_existsUnique p U).1 hU W w'
    have hw : w ≫ yoneda.map (pullback.snd (c.π.app i) (ι f) ≫ ι f) =
        w ≫ yoneda.map (pullback.fst (c.π.app i) (ι f)) ≫ yoneda.map (c.π.app i) := by
      rw [← Functor.map_comp, pullback.condition]
    refine ⟨y ≫ a, ?_, fun y' hy' => ?_⟩
    · dsimp only
      rw [Category.assoc, ← hpb.w, ← Category.assoc, hy, hw'', hw, Category.assoc]
    · have hc' : (w ≫ yoneda.map (pullback.fst (c.π.app i) (ι f))) ≫ yoneda.map (c.π.app i) =
          y' ≫ pk := by rw [hy', hw, Category.assoc]
      rw [← huniq (hpb.lift _ _ hc') ((hpb.lift_fst _ _ hc').trans hw''.symm)]
      exact (hpb.lift_snd _ _ hc').symm
  -- at a stage, for each `f`
  have hst : ∀ f, ∃ k : Over i,
      IsIso (pullback.fst (yoneda.map (pullback.snd (E.map k.hom) (ι f) ≫ ι f)) pk) := fun f =>
    exists_stage_isIso_of_isLimit_baseChange hc hE hpt i (hO f) (ι f) (hιf f) hYk pk hpk hpkf
      (hlim f)
  choose kf hkf using hst
  -- a common later stage
  let Os : Finset I := insert i (Finset.univ.image fun f => (kf f).left)
  have hiO : i ∈ Os := Finset.mem_insert_self i _
  have hjO : ∀ f, (kf f).left ∈ Os := fun f =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ f))
  let Hs : Finset (Σ' (X Y : I) (_ : X ∈ Os) (_ : Y ∈ Os), X ⟶ Y) :=
    Finset.univ.image fun f => ⟨(kf f).left, i, hjO f, hiO, (kf f).hom⟩
  obtain ⟨j, Tm, hTm⟩ := IsCofiltered.inf_exists Os Hs
  have htf : ∀ f, Tm (hjO f) ≫ (kf f).hom = Tm hiO := fun f =>
    hTm (hjO f) hiO (Finset.mem_image_of_mem _ (Finset.mem_univ f))
  let F := Tm hiO
  -- unique lifts over `V_j ×_{V_i} D(f)`
  have hstage : ∀ f (W : BigFppfOver B S hS)
      (w : yoneda.obj W ⟶ yoneda.obj (pullback (E.map F) (ι f))),
      ∃! y : yoneda.obj W ⟶ Yk, y ≫ pk = w ≫ yoneda.map (pullback.snd (E.map F) (ι f) ≫ ι f) := by
    intro f W w
    let m : pullback (E.map F) (ι f) ⟶ pullback (E.map (kf f).hom) (ι f) :=
      pullback.lift (pullback.fst _ _ ≫ E.map (Tm (hjO f))) (pullback.snd _ _) (by
        rw [Category.assoc, ← E.map_comp, htf f]
        exact pullback.condition)
    have hm : m ≫ pullback.snd (E.map (kf f).hom) (ι f) = pullback.snd (E.map F) (ι f) :=
      pullback.lift_snd _ _ _
    have e : w ≫ yoneda.map (pullback.snd (E.map F) (ι f) ≫ ι f) =
        (w ≫ yoneda.map m) ≫ yoneda.map (pullback.snd (E.map (kf f).hom) (ι f) ≫ ι f) := by
      rw [Category.assoc, ← Functor.map_comp, ← Category.assoc m, hm]
    rw [e]
    exact (isIso_pullback_fst_iff_existsUnique _ pk).1 (hkf f) W (w ≫ yoneda.map m)
  refine ⟨j, F, fun W t ht => ?_⟩
  let φ := t ≫ E.map F
  let Tf : gens → BigFppfOver B S hS := fun f => pullback φ (ι f)
  let pf : ∀ f, Tf f ⟶ W := fun f => pullback.fst φ (ι f)
  -- the basic opens cover `W`
  have hcov : Sieve.ofArrows Tf pf ∈ BigFppfOver.topology B S hS W := by
    refine BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS Tf W pf
      (fun f => ?_) (fun y => ?_)
    · show AlgebraicGeometry.IsOpenImmersion (T.map (pullback.fst φ (ι f)))
      rw [← PreservesPullback.iso_hom_fst T φ (ι f)]
      have := hιo f
      infer_instance
    · have hy : T.map φ y ∉ X.zeroLocus (Iid : Set Γ(X, ⊤)) := by
        intro hy
        let w := (schemePointsHomeomorph B S hS W).symm y
        apply ht ⟨w, rfl⟩
        show pointsMap B S hS _ (yoneda.map φ) w ∈ Z
        rwa [hI, pointsToScheme_pointsMap_yoneda, ← schemePointsHomeomorph_apply,
          Homeomorph.apply_symm_apply]
      have hy2 : T.map φ y ∉ X.zeroLocus ((gens : Set Γ(X, ⊤))) := by
        have hg' : Ideal.span (gens : Set Γ(X, ⊤)) = Iid := hgens
        rwa [← Scheme.zeroLocus_span, hg']
      rw [Scheme.mem_zeroLocus_iff] at hy2
      push Not at hy2
      obtain ⟨f, hf, hyf⟩ := hy2
      obtain ⟨z, hz⟩ : T.map φ y ∈ Set.range (X.basicOpen f).ι := by rwa [Scheme.Opens.range_ι]
      obtain ⟨w, hw⟩ := Artin.ContractionSituation.exists_toScheme_map_pullback_fst_eq φ
        (ι ⟨f, hf⟩) (y := y) (z := z) hz.symm
      exact ⟨⟨f, hf⟩, w, hw⟩
  -- unique lifts over each member of the cover
  have huniqf : ∀ f (W' : BigFppfOver B S hS) (r : W' ⟶ Tf f),
      ∃! y : yoneda.obj W' ⟶ Yk, y ≫ pk = yoneda.map (r ≫ pf f ≫ φ) := by
    intro f W' r
    let wf : Tf f ⟶ pullback (E.map F) (ι f) :=
      pullback.lift (pullback.fst φ (ι f) ≫ t) (pullback.snd φ (ι f)) (by
        rw [Category.assoc]
        exact pullback.condition)
    have e : yoneda.map (r ≫ pf f ≫ φ) =
        yoneda.map (r ≫ wf) ≫ yoneda.map (pullback.snd (E.map F) (ι f) ≫ ι f) := by
      rw [← Functor.map_comp]
      congr 1
      simp only [pf, wf, Category.assoc, pullback.lift_snd_assoc, pullback.condition]
    rw [e]
    exact hstage f W' (yoneda.map (r ≫ wf))
  choose yf hyf huf using fun f => huniqf f (Tf f) (𝟙 _)
  have hYs : (Presieve.ofArrows Tf pf).IsSheafFor Yk :=
    (Presieve.isSheafFor_iff_generate _).2
      ((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) Yk).1 hYk.isSheaf _ hcov)
  obtain ⟨s, hs, hsu⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks Yk pf).1 hYs)
    (fun f => yonedaEquiv (yf f)) (fun f g => by
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
      congr 1
      obtain ⟨_, -, hu⟩ := huniqf f _ (pullback.fst (pf f) (pf g))
      refine (hu _ ?_).trans (hu _ ?_).symm
      · dsimp only
        rw [Category.assoc, hyf, Category.id_comp, ← Functor.map_comp]
      · dsimp only
        rw [Category.assoc, hyf, Category.id_comp, ← Functor.map_comp, ← Category.assoc,
          ← pullback.condition, Category.assoc])
  have hV := (isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) (yoneda.obj V)).1
    (isSheaf_yoneda_obj B S hS V) _ hcov
  refine ⟨yonedaEquiv.symm s, ?_, fun y hy => ?_⟩
  · apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    refine hV.isSeparatedFor.ext fun Y g hg => ?_
    obtain ⟨_, h', _, ⟨f⟩, rfl⟩ := hg
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    congr 1
    rw [← NatTrans.naturality_apply, hs f, ← yonedaEquiv_comp, hyf, Category.id_comp,
      yonedaEquiv_yoneda_map]
    rfl
  · apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    refine hsu _ fun f => ?_
    rw [yonedaEquiv_naturality]
    congr 1
    refine huf f _ ?_
    dsimp only
    rw [Category.assoc, hy, ← Functor.map_comp, Category.id_comp]

/-- **An isomorphism over the complement of `Z` in the limit is an isomorphism over the
complement of `Z` at a stage**: for some `F : j ⟶ i` the base change of `p_i` to `V_j` is an
isomorphism over `V_j ∖ Z`. -/
theorem exists_stage_isIso_openSubspace_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS} {c : Cone E}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)) (i : I)
    (hNoeth : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj (E.obj i), ⊤))
    {Z : Set (points B S hS (yoneda.obj (E.obj i)))} (hZ : IsClosed Z)
    {Yk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hYk : IsAlgebraicSpace B S hS Yk)
    (pk : Yk ⟶ yoneda.obj (E.obj i)) (hpk : IsProper B S hS pk)
    (hpkf : IsLocallyOfFinitePresentation B S hS pk)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ yoneda.obj c.pt) (a : Y ⟶ Yk)
    (hpb : IsPullback p a (yoneda.map (c.π.app i)) pk)
    (hU : IsIso (pullback.snd p (openSubspaceOfPoints B S hS (yoneda.obj c.pt)
      (pointsMap B S hS _ (yoneda.map (c.π.app i)) ⁻¹' Z)ᶜ).ι)) :
    ∃ (j : I) (F : j ⟶ i), IsIso (pullback.snd (pullback.snd pk (yoneda.map (E.map F)))
      (openSubspaceOfPoints B S hS (yoneda.obj (E.obj j))
        (pointsMap B S hS _ (yoneda.map (E.map F)) ⁻¹' Z)ᶜ).ι) := by
  obtain ⟨j, F, h⟩ := exists_stage_existsUnique_lift_of_isLimit hc hE hpt i hNoeth hZ hYk pk hpk
    hpkf p a hpb hU
  refine ⟨j, F, (isIso_pullback_snd_ι_iff_existsUnique _ _).2 fun W w => ?_⟩
  let U := openSubspaceOfPoints B S hS (yoneda.obj (E.obj j))
    (pointsMap B S hS _ (yoneda.map (E.map F)) ⁻¹' Z)ᶜ
  let t := yoneda.preimage (w ≫ U.ι)
  have ht' : yoneda.map t = w ≫ U.ι := yoneda.map_preimage _
  have ht : Set.range (pointsMap B S hS _ (yoneda.map (t ≫ E.map F))) ⊆ Zᶜ := by
    rintro _ ⟨x, rfl⟩
    rw [Functor.map_comp, pointsMap_comp_apply, ht', pointsMap_comp_apply]
    exact (range_pointsMap_ι_openSubspaceOfPoints B S hS
      (pointsMap B S hS _ (yoneda.map (E.map F)) ⁻¹' Z)ᶜ).le ⟨_, rfl⟩
  obtain ⟨y, hy, hyu⟩ := h W t ht
  refine ⟨pullback.lift y (yoneda.map t) (by rw [hy, Functor.map_comp]), ?_, fun y' hy' => ?_⟩
  · dsimp only
    rw [pullback.lift_snd, ht']
  · have e₁ : y' ≫ pullback.fst pk (yoneda.map (E.map F)) = y := hyu _ (by
      dsimp only
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy', ← ht', ← Functor.map_comp])
    apply pullback.hom_ext
    · rw [e₁, pullback.lift_fst]
    · rw [pullback.lift_snd, ht', hy']

end AlgebraicGeometry.Space

end
