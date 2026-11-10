module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluing

/-!
# Morphisms out of the open complement agreeing in a limit agree at a finite stage

Let `V = lim Vᵢ` be a cofiltered limit of affine locally Noetherian schemes over `S` and let
`Z ⊆ |Vᵢ|` be closed. Two morphisms `Vᵢ ∖ Z ⟶ G` into a limit preserving fppf sheaf `G` (for
instance an algebraic space locally of finite type over the locally Noetherian base) whose
restrictions to `V ∖ Z` agree already agree on `Vⱼ ∖ Z` for some `j ⟶ i`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.range_pointsMap_opensObjectι_basicOpen_subset`:
  a basic open `D(f)`, `f` in an ideal cutting out `Z`, avoids `Z`.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_restrict_eq_of_isLimit`: the agreement
  at a finite stage.

## References

* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 05N0](https://stacks.math.columbia.edu/tag/05N0)
* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ LocallyNoetherianOver B S hS}
  {κ : Cone D}

/-- The basic open `D(f)` of an affine object `V` of the site avoids the vanishing locus of an
ideal containing `f`: the points of `D(f)` map into the complement of a closed set `Z` presented
as that vanishing locus. -/
theorem range_pointsMap_opensObjectι_basicOpen_subset (V : BigFppfOver B S hS)
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {Iid : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (Iid : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    {f : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (hf : f ∈ Iid) :
    Set.range (Space.pointsMap B S hS _ (yoneda.map
      (Space.opensObjectι B S hS V (((BigFppfOver.toScheme B S hS).obj V).basicOpen f)))) ⊆
        Zᶜ := by
  rintro _ ⟨w, rfl⟩ hw
  rw [hI, Space.pointsToScheme_pointsMap_yoneda, Space.toScheme_map_opensObjectι] at hw
  refine (Scheme.mem_zeroLocus_iff _ _ _).mp hw f hf ?_
  have : (((BigFppfOver.toScheme B S hS).obj V).basicOpen f).ι
      (Space.pointsToScheme B S hS _ w) ∈ Set.range
        (((BigFppfOver.toScheme B S hS).obj V).basicOpen f).ι := ⟨_, rfl⟩
  rwa [Scheme.Opens.range_ι] at this

/-- A section `t` of `V` lies in the open subspace cut out by `W` iff its points land in `W`. -/
private lemma mem_openSubspaceOfPoints_yoneda_iff {U V : BigFppfOver B S hS}
    {W : Set (Space.points B S hS (yoneda.obj V))} (t : U ⟶ V) :
    t ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) W).obj (op U) ↔
      Set.range (Space.pointsMap B S hS _ (yoneda.map t)) ⊆ W :=
  Iff.rfl

/-- The inclusion of a basic open `D(f)`, `f` in an ideal cutting out `Z`, is a section of the
open subspace complementary to `Z`. -/
theorem opensObjectι_basicOpen_mem_openSubspaceOfPoints (V : BigFppfOver B S hS)
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {Iid : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (Iid : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    {f : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (hf : f ∈ Iid) :
    Space.opensObjectι B S hS V (((BigFppfOver.toScheme B S hS).obj V).basicOpen f) ∈
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).obj
        (op (Space.opensObject B S hS V (((BigFppfOver.toScheme B S hS).obj V).basicOpen f))) := by
  rw [mem_openSubspaceOfPoints_yoneda_iff]
  exact range_pointsMap_opensObjectι_basicOpen_subset V hI hf

/-- A morphism `t : W ⟶ V'` whose composite with `φ : V' ⟶ V` factors through a basic open `D(f)`,
`f` in an ideal cutting out `Z`, is a section of the open subspace complementary to the preimage
of `Z`. -/
theorem mem_openSubspaceOfPoints_of_comp_eq_opensObjectι (V : BigFppfOver B S hS)
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {Iid : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (Iid : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    {f : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (hf : f ∈ Iid)
    {W V' : BigFppfOver B S hS} (φ : V' ⟶ V) (t : W ⟶ V')
    (r : W ⟶ Space.opensObject B S hS V (((BigFppfOver.toScheme B S hS).obj V).basicOpen f))
    (htr : t ≫ φ = r ≫ Space.opensObjectι B S hS V
      (((BigFppfOver.toScheme B S hS).obj V).basicOpen f)) :
    t ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V')
      (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z)ᶜ).obj (op W) := by
  rw [mem_openSubspaceOfPoints_yoneda_iff]
  rintro _ ⟨w, rfl⟩ hw
  simp only [Set.mem_preimage] at hw
  rw [← Space.pointsMap_comp_apply, ← Functor.map_comp, htr, Functor.map_comp,
    Space.pointsMap_comp_apply] at hw
  exact range_pointsMap_opensObjectι_basicOpen_subset V hI hf ⟨_, rfl⟩ hw

/-- Evaluating a restriction of `γ` at a section `t` with `t ≫ φ = r ≫ ι` gives the restriction
along `r` of the value of `γ` at `ι`. -/
theorem openSubspaceOfPointsRestrict_comp_app_of_comp_eq {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : BigFppfOver B S hS} {Z : Set (Space.points B S hS (yoneda.obj V))}
    (γ : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ G)
    {W V' O : BigFppfOver B S hS} (φ : V' ⟶ V) (ι : O ⟶ V)
    (hι : ι ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).obj (op O))
    (t : W ⟶ V') (r : W ⟶ O) (htr : t ≫ φ = r ≫ ι)
    (ht : t ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V')
      (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z)ᶜ).obj (op W)) :
    (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
        (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ γ).app (op W)
        ⟨t, ht⟩ = G.map r.op (γ.app (op O) ⟨ι, hι⟩) := by
  refine Eq.trans ?_ (NatTrans.naturality_apply γ r.op ⟨ι, hι⟩)
  change γ.app (op W) _ = γ.app (op W) _
  congr 1
  exact Subtype.ext htr

/-- For a section `t : U ⟶ V'` avoiding the preimage of `Z` under `φ : V' ⟶ V`, the pullbacks
along `t ≫ φ` of the basic opens `D(f)`, `f` running over generators of an ideal cutting out `Z`,
cover `U`. -/
theorem sieve_ofArrows_pullback_opensObjectι_mem_topology (V : BigFppfOver B S hS)
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {Iid : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (Iid : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    {gens : Finset Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hgens : Ideal.span (gens : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) = Iid)
    {U V' : BigFppfOver B S hS} (φ : V' ⟶ V) {t : U ⟶ V'}
    (ht : t ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V')
      (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z)ᶜ).obj (op U)) :
    Sieve.ofArrows (fun f : gens => pullback (t ≫ φ) (Space.opensObjectι B S hS V
        (((BigFppfOver.toScheme B S hS).obj V).basicOpen f.1)))
      (fun f => pullback.fst (t ≫ φ) (Space.opensObjectι B S hS V
        (((BigFppfOver.toScheme B S hS).obj V).basicOpen f.1))) ∈
        BigFppfOver.topology B S hS U := by
  let X := (BigFppfOver.toScheme B S hS).obj V
  refine BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS _ U _
    (fun f => ?_) (fun y => ?_)
  · change IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (pullback.fst (t ≫ φ) (Space.opensObjectι B S hS V (X.basicOpen f.1))))
    rw [← PreservesPullback.iso_hom_fst (BigFppfOver.toScheme B S hS) (t ≫ φ)]
    have : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
        (Space.opensObjectι B S hS V (X.basicOpen f.1))) := by
      rw [Space.toScheme_map_opensObjectι]
      exact inferInstanceAs (IsOpenImmersion (X.basicOpen f.1).ι)
    infer_instance
  · have hy : (BigFppfOver.toScheme B S hS).map (t ≫ φ) y ∉
        X.zeroLocus (Iid : Set Γ(X, ⊤)) := by
      intro hy
      let w := (Space.schemePointsHomeomorph B S hS U).symm y
      have htw := (mem_openSubspaceOfPoints_yoneda_iff t).1 ht ⟨w, rfl⟩
      apply htw
      change Space.pointsMap B S hS _ (yoneda.map φ)
        (Space.pointsMap B S hS _ (yoneda.map t) w) ∈ Z
      rwa [hI, Space.pointsToScheme_pointsMap_yoneda, Space.pointsToScheme_pointsMap_yoneda,
        ← Space.schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply,
        ← Scheme.Hom.comp_apply, ← Functor.map_comp]
    rw [← hgens, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff] at hy
    push Not at hy
    obtain ⟨f, hf, hyf⟩ := hy
    obtain ⟨z, hz⟩ : _ ∈ Set.range (X.basicOpen f).ι := by rwa [Scheme.Opens.range_ι]
    obtain ⟨w, hw⟩ := exists_toScheme_map_pullback_fst_eq (t ≫ φ)
      (Space.opensObjectι B S hS V (X.basicOpen f)) (y := y) (z := z) hz.symm
    exact ⟨⟨f, hf⟩, w, hw⟩

/-- Two morphisms `α, β` out of the complement of `Z` have equal restrictions along `φ : V' ⟶ V`
once their values at the basic opens `D(f)`, `f` running over generators of an ideal cutting out
`Z`, agree after pulling back along `φ`. -/
theorem openSubspaceOfPointsRestrict_comp_eq_of_forall_pullback_snd
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hGs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) (V : BigFppfOver B S hS)
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {Iid : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (Iid : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    {gens : Finset Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hgens : Ideal.span (gens : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) = Iid)
    (α β : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ G)
    {V' : BigFppfOver B S hS} (φ : V' ⟶ V)
    (hF : ∀ (f : gens) (hf : f.1 ∈ Iid),
      G.map (pullback.snd φ (Space.opensObjectι B S hS V
          (((BigFppfOver.toScheme B S hS).obj V).basicOpen f.1))).op
        (α.app _ ⟨_, opensObjectι_basicOpen_mem_openSubspaceOfPoints V hI hf⟩) =
      G.map (pullback.snd φ (Space.opensObjectι B S hS V
          (((BigFppfOver.toScheme B S hS).obj V).basicOpen f.1))).op
        (β.app _ ⟨_, opensObjectι_basicOpen_mem_openSubspaceOfPoints V hI hf⟩)) :
    Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
        (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ α =
      Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
        (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ β := by
  let X := (BigFppfOver.toScheme B S hS).obj V
  let ι : ∀ f : gens, Space.opensObject B S hS V (X.basicOpen f.1) ⟶ V :=
    fun f => Space.opensObjectι B S hS V (X.basicOpen f.1)
  refine NatTrans.ext (funext fun U => ?_)
  ext s
  obtain ⟨t, ht⟩ := s
  have hsheaf := (isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) G).1 hGs _
    (sieve_ofArrows_pullback_opensObjectι_mem_topology V hI hgens φ ht)
  refine hsheaf.isSeparatedFor.ext fun Y g hg => ?_
  obtain ⟨_, h', _, ⟨f⟩, rfl⟩ := hg
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  congr 1
  have hf : f.1 ∈ Iid := hgens ▸ Ideal.subset_span f.2
  have hc : (pullback.fst (t ≫ φ) (ι f) ≫ t) ≫ φ = pullback.snd (t ≫ φ) (ι f) ≫ ι f :=
    (Category.assoc _ _ _).trans pullback.condition
  have hmt := mem_openSubspaceOfPoints_of_comp_eq_opensObjectι V hI hf φ _ _ hc
  have hres : ∀ γ : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ G,
      G.map (pullback.fst (t ≫ φ) (ι f)).op
        ((Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
          (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ γ).app U
          ⟨t, ht⟩) =
        G.map (pullback.lift _ _ hc).op (G.map (pullback.snd φ (ι f)).op
          (γ.app _ ⟨ι f, opensObjectι_basicOpen_mem_openSubspaceOfPoints V hI hf⟩)) := by
    intro γ
    rw [← NatTrans.naturality_apply (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
      (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ γ)
      (pullback.fst (t ≫ φ) (ι f)).op ⟨t, ht⟩]
    have e1 : (Space.openSubspaceOfPoints B S hS (yoneda.obj V')
        (Space.pointsMap B S hS _ (yoneda.map φ) ⁻¹' Z)ᶜ).toFunctor.map
          (pullback.fst (t ≫ φ) (ι f)).op ⟨t, ht⟩ = ⟨pullback.fst (t ≫ φ) (ι f) ≫ t, hmt⟩ := rfl
    rw [e1, openSubspaceOfPointsRestrict_comp_app_of_comp_eq γ φ (ι f) _ _ _ hc hmt,
      ← Functor.map_comp_apply, ← op_comp, pullback.lift_snd]
  exact (hres α).trans ((congrArg (G.map (pullback.lift _ _ hc).op) (hF f hf)).trans
    (hres β).symm)

/-- In a cofiltered category, finitely many morphisms `gf f : jf f ⟶ i` with common target are
dominated by a single morphism `F : j ⟶ i` factoring through each of them. -/
theorem exists_comp_eq_of_finite {J : Type*} [Category J] [IsCofiltered J] {ι : Type*}
    [Finite ι] (i : J) (jf : ι → J) (gf : ∀ f, jf f ⟶ i) :
    ∃ (j : J) (F : j ⟶ i) (T : ∀ f, j ⟶ jf f), ∀ f, T f ≫ gf f = F := by
  classical
  have := Fintype.ofFinite ι
  let Os : Finset J := insert i (Finset.univ.image jf)
  have hiO : i ∈ Os := Finset.mem_insert_self i _
  have hjO : ∀ f, jf f ∈ Os := fun f =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ f))
  let Hs : Finset (Σ' (X Y : J) (_ : X ∈ Os) (_ : Y ∈ Os), X ⟶ Y) :=
    Finset.univ.image fun f => ⟨jf f, i, hjO f, hiO, gf f⟩
  obtain ⟨j, T, hT⟩ := IsCofiltered.inf_exists Os Hs
  exact ⟨j, T hiO, fun f => T (hjO f), fun f =>
    hT (hjO f) hiO (Finset.mem_image_of_mem _ (Finset.mem_univ f))⟩

/-- **Two morphisms out of `Vᵢ ∖ Z` into a limit preserving fppf sheaf that agree on `V ∖ Z` agree
at a later stage.** For a cofiltered limit `V = lim Vᵢ` of affine locally Noetherian schemes over
`S` and a closed `Z ⊆ |Vᵢ|`, two morphisms `α, β : Vᵢ ∖ Z ⟶ G` into a limit preserving fppf sheaf
`G` whose restrictions to `V ∖ Z` agree have the same restriction to `Vⱼ ∖ Z` for some `j ⟶ i`. -/
theorem exists_restrict_eq_of_isLimit (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hGs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hG : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G)
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt)) (i : I)
    {Z : Set (Space.points B S hS (yoneda.obj (D.obj i).obj))} (hZ : IsClosed Z)
    (α β : (Space.openSubspaceOfPoints B S hS (yoneda.obj (D.obj i).obj) Zᶜ).toFunctor ⟶ G)
    (h : Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (κ.π.app i).hom)
          (Space.pointsMap B S hS _ (yoneda.map (κ.π.app i).hom) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ α =
        Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (κ.π.app i).hom)
          (Space.pointsMap B S hS _ (yoneda.map (κ.π.app i).hom) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ β) :
    ∃ (j : I) (f : j ⟶ i),
      Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (D.map f).hom)
          (Space.pointsMap B S hS _ (yoneda.map (D.map f).hom) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ α =
        Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (D.map f).hom)
          (Space.pointsMap B S hS _ (yoneda.map (D.map f).hom) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ β := by
  classical
  let V := (D.obj i).obj
  let X := (BigFppfOver.toScheme B S hS).obj V
  have : IsAffine X := hD i
  have : IsLocallyNoetherian X := (D.obj i).property
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  obtain ⟨Iid, hI⟩ := Space.exists_ideal_mem_iff_mem_zeroLocus B S hS V hZ
  obtain ⟨gens, hgens⟩ := (IsNoetherian.noetherian Iid : Iid.FG)
  have hmem : ∀ f ∈ gens, f ∈ Iid := fun f hf => hgens ▸ Ideal.subset_span hf
  let O : gens → BigFppfOver B S hS := fun f => Space.opensObject B S hS V (X.basicOpen f.1)
  let ι : ∀ f, O f ⟶ V := fun f => Space.opensObjectι B S hS V (X.basicOpen f.1)
  let σ : ∀ f, (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor.obj (op (O f)) :=
    fun f => ⟨ι f, opensObjectι_basicOpen_mem_openSubspaceOfPoints V hI (hmem f.1 f.2)⟩
  have hstage : ∀ f : gens, ∃ (j : I) (g : j ⟶ i),
      G.map (pullback.snd (D.map g).hom (ι f)).op (α.app _ (σ f)) =
        G.map (pullback.snd (D.map g).hom (ι f)).op (β.app _ (σ f)) := by
    intro f
    refine exists_map_eq_of_isLimit_baseChange G hG hκ hD hpt i (ι f)
      ((isAffineOpen_top X).basicOpen f.1) _ _ ?_
    have hc := pullback.condition (f := (κ.π.app i).hom) (g := ι f)
    have ht := mem_openSubspaceOfPoints_of_comp_eq_opensObjectι V hI (hmem f.1 f.2) _ _ _ hc
    have e := congrArg (fun γ => γ.app (op (pullback (κ.π.app i).hom (ι f))) ⟨_, ht⟩) h
    simp only at e
    rwa [openSubspaceOfPointsRestrict_comp_app_of_comp_eq α _ (ι f) (σ f).2 _ _ hc ht,
      openSubspaceOfPointsRestrict_comp_app_of_comp_eq β _ (ι f) (σ f).2 _ _ hc ht] at e
  choose jf gf hgf using hstage
  obtain ⟨j, F, T, htf⟩ := exists_comp_eq_of_finite i jf gf
  refine ⟨j, F, ?_⟩
  let φ := (D.map F).hom
  have hF : ∀ f : gens, G.map (pullback.snd φ (ι f)).op (α.app _ (σ f)) =
      G.map (pullback.snd φ (ι f)).op (β.app _ (σ f)) := by
    intro f
    let m : pullback φ (ι f) ⟶ pullback (D.map (gf f)).hom (ι f) :=
      pullback.lift (pullback.fst _ _ ≫ (D.map (T f)).hom) (pullback.snd _ _) (by
        rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, ← D.map_comp, htf f]
        exact pullback.condition)
    have hm : pullback.snd φ (ι f) = m ≫ pullback.snd (D.map (gf f)).hom (ι f) :=
      (pullback.lift_snd _ _ _).symm
    rw [hm, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hgf f]
  exact openSubspaceOfPointsRestrict_comp_eq_of_forall_pullback_snd hGs V hI hgens α β φ
    fun f _ => hF f

end AlgebraicGeometry.Artin.ContractionSituation

end
