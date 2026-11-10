module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical

/-!
# The schematic locus is an open subspace and a scheme

Let `F` be an algebraic space over `S` whose representable open subspaces are all contained in
the union of a family of them indexed by a nonempty type of cardinality below the cofinality of
the cutoff of the site. Then the schematic locus `AlgebraicGeometry.Space.schematicLocus` of
`F`, the supremum of its representable open subspaces, is the sheafification of that union; it
is an open subspace of `F` and it is representable (Stacks 03JH).

## Main results

* `CategoryTheory.Subfunctor.isPullback_lift`: a subfunctor of the source of a morphism of
  presheaves which is cut out by a subfunctor of the target is the fibre product of the two
  inclusions.
* `CategoryTheory.Subfunctor.eq_of_isLocallySurjective`: a subfunctor of a sheaf which is
  itself a sheaf is determined by the sections it contains in the image of a locally
  surjective morphism.
* `AlgebraicGeometry.Space.isOpenImmersion_sheafify_iSup_ι`: the inclusion into `F` of the
  sheafified union of a family of open subspaces is an open immersion.
* `AlgebraicGeometry.Space.isRepresentable_sheafify_iSup` and
  `AlgebraicGeometry.Space.isOpenSubspace_sheafify_iSup`: the sheafified union of a small
  family of representable open subspaces is representable, and is an open subspace.
* `AlgebraicGeometry.Space.schematicLocus_eq_sheafify_iSup`: if the representable open
  subspaces are all contained in the union of a small family of them, the schematic locus
  is that union, sheafified.
* `AlgebraicGeometry.Space.isOpenSubspace_schematicLocus` and
  `AlgebraicGeometry.Space.isRepresentable_schematicLocus`: under the same hypothesis, the
  schematic locus is an open subspace and is representable.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F F' : Cᵒᵖ ⥤ Type w}

/-- If a subfunctor `N` of `F'` consists exactly of the sections which `g : F' ⟶ F` carries
into a subfunctor `G` of `F`, then the image of `N` in `G` is contained in `G`. -/
theorem range_comp_ι_le (G : Subfunctor F) (g : F' ⟶ F) (N : Subfunctor F')
    (hN : ∀ (W : Cᵒᵖ) (x : F'.obj W), x ∈ N.obj W → g.app W x ∈ G.obj W) :
    range (N.ι ≫ g) ≤ G := by
  rintro W _ ⟨x, rfl⟩
  exact hN W x.1 x.2

/-- A subfunctor `N` of `F'` which consists exactly of the sections that a morphism
`g : F' ⟶ F` carries into a subfunctor `G` of `F` is the fibre product of `G.ι` and `g`. -/
theorem isPullback_lift (G : Subfunctor F) (g : F' ⟶ F) (N : Subfunctor F')
    (hN : ∀ (W : Cᵒᵖ) (x : F'.obj W), x ∈ N.obj W ↔ g.app W x ∈ G.obj W) :
    IsPullback (lift (N.ι ≫ g) (range_comp_ι_le G g N fun W x hx => (hN W x).1 hx))
      N.ι G.ι g := by
  have hfac : lift (N.ι ≫ g) (range_comp_ι_le G g N fun W x hx => (hN W x).1 hx) ≫ G.ι
      = N.ι ≫ g := lift_ι _ _
  have key : ∀ c : PullbackCone G.ι g, range c.snd ≤ N := by
    rintro c W _ ⟨z, rfl⟩
    refine (hN W _).2 ?_
    have h : (c.fst ≫ G.ι).app W z = (c.snd ≫ g).app W z := by rw [c.condition]
    simp only [NatTrans.comp_app, types_comp_apply, ι_app] at h
    exact h ▸ (c.fst.app W z).2
  refine IsPullback.of_isLimit' (CommSq.mk hfac)
    (PullbackCone.IsLimit.mk hfac (fun c => lift c.snd (key c)) (fun c => ?_)
      (fun c => rfl) (fun c m _ h₂ => ?_))
  · rw [← cancel_mono G.ι, Category.assoc, hfac]
    exact c.condition.symm ▸ rfl
  · rw [← cancel_mono N.ι]
    exact h₂.trans (lift_ι _ _).symm

/-- Two subfunctors of a sheaf which are themselves sheaves and contain the same sections
in the image of a locally surjective morphism are equal. -/
theorem eq_of_isLocallySurjective {J : GrothendieckTopology C}
    (hF : Presieve.IsSheaf J F) {g : F' ⟶ F}
    (hg : Presheaf.IsLocallySurjective J g) (G₁ G₂ : Subfunctor F)
    (h₁ : Presieve.IsSheaf J G₁.toFunctor) (h₂ : Presieve.IsSheaf J G₂.toFunctor)
    (h : ∀ (W : Cᵒᵖ) (x : F'.obj W), g.app W x ∈ G₁.obj W ↔ g.app W x ∈ G₂.obj W) :
    G₁ = G₂ := by
  have key : ∀ (H₁ H₂ : Subfunctor F), Presieve.IsSheaf J H₂.toFunctor →
      (∀ (W : Cᵒᵖ) (x : F'.obj W), g.app W x ∈ H₁.obj W → g.app W x ∈ H₂.obj W) →
      H₁ ≤ H₂ := by
    intro H₁ H₂ hH₂ hH W s hs
    rw [H₂.eq_sheafify hF hH₂]
    refine J.superset_covering ?_ (hg.imageSieve_mem s)
    rintro W' k ⟨t, ht⟩
    have hmem : g.app (Opposite.op W') t ∈ H₁.obj (Opposite.op W') := by
      rw [ht]
      exact H₁.map k.op hs
    have := hH (Opposite.op W') t hmem
    rwa [ht] at this
  exact le_antisymm (key G₁ G₂ h₂ fun W x hx => (h W x).1 hx)
    (key G₂ G₁ h₁ fun W x hx => (h W x).2 hx)

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of the sheafification of a union of open subspaces is an open immersion. -/
theorem isOpenImmersion_sheafify_iSup_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} (X : ι → Subfunctor F) (hX : ∀ i, IsOpenImmersion B S hS (X i).ι) :
    IsOpenImmersion B S hS
      ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).ι := by
  have hFt : Presieve.IsSheaf (BigFppfOver.topology B S hS) F :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hF
  refine MorphismProperty.relative.of_exists fun a g => ?_
  have hgnat : ∀ {W W' : BigFppfOver B S hS} (k : W ⟶ W') (x : W' ⟶ a),
      F.map k.op (g.app (Opposite.op W') x) = g.app (Opposite.op W) (k ≫ x) := fun k x => by
    rw [← NatTrans.naturality_apply g k.op x]
    rfl
  obtain ⟨Pi, si, fsti, hpb, hoi⟩ :
      ∃ (Pi : ι → BigFppfOver B S hS) (si : ∀ i, Pi i ⟶ a)
        (fsti : ∀ i, yoneda.obj (Pi i) ⟶ (X i).toFunctor),
        (∀ i, IsPullback (fsti i) (yoneda.map (si i)) (X i).ι g) ∧
        ∀ i, AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B S hS).map (si i)) :=
    ⟨_, _, _, fun i => (hX i).rep.isPullback g, fun i => (hX i).property_snd g⟩
  set V : ((BigFppfOver.toScheme B S hS).obj a).Opens :=
    ⨆ i, ((BigFppfOver.toScheme B S hS).map (si i)).opensRange with hVdef
  have hVmem : B.Contains (↑V : Scheme.{u}) := B.contains_coe_opens a.left.property V
  set Pobj : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (X := B.obj hVmem) (Y := B.obj hS)
      (V.ι ≫ B.inclusion.map a.hom)) with hPobjdef
  set sn : Pobj ⟶ a :=
    Over.homMk (ObjectProperty.homMk (X := B.obj hVmem) (Y := a.left) V.ι)
      (by apply ObjectProperty.hom_ext; rfl) with hsndef
  have hsnmap : (BigFppfOver.toScheme B S hS).map sn = V.ι := rfl
  have hrange : ∀ i, Set.range ((BigFppfOver.toScheme B S hS).map (si i)) ⊆
      Set.range V.ι := by
    intro i x hx
    rw [Scheme.Opens.range_ι]
    exact le_iSup
      (fun j => ((BigFppfOver.toScheme B S hS).map (si j)).opensRange) i hx
  have hlf : ∀ i, AlgebraicGeometry.IsOpenImmersion.lift V.ι
      ((BigFppfOver.toScheme B S hS).map (si i)) (hrange i) ≫ V.ι =
      (BigFppfOver.toScheme B S hS).map (si i) :=
    fun i => AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hlfoi : ∀ i, AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.IsOpenImmersion.lift V.ι
        ((BigFppfOver.toScheme B S hS).map (si i)) (hrange i)) := by
    intro i
    have hc : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.IsOpenImmersion.lift V.ι
          ((BigFppfOver.toScheme B S hS).map (si i)) (hrange i) ≫ V.ι) := by
      rw [hlf i]; exact hoi i
    exact AlgebraicGeometry.IsOpenImmersion.of_comp _ V.ι
  set ti : ∀ i, Pi i ⟶ Pobj := fun i =>
    Over.homMk (ObjectProperty.homMk (X := (Pi i).left) (Y := B.obj hVmem)
      (AlgebraicGeometry.IsOpenImmersion.lift V.ι
        ((BigFppfOver.toScheme B S hS).map (si i)) (hrange i)))
      (by
        apply ObjectProperty.hom_ext
        change AlgebraicGeometry.IsOpenImmersion.lift V.ι
            ((BigFppfOver.toScheme B S hS).map (si i)) (hrange i) ≫
            V.ι ≫ B.inclusion.map a.hom = B.inclusion.map (Pi i).hom
        rw [← Category.assoc, hlf i]
        change B.inclusion.map (si i).left ≫ B.inclusion.map a.hom = _
        rw [← B.inclusion.map_comp, Over.w (si i)]) with htidef
  have htimap : ∀ i, (BigFppfOver.toScheme B S hS).map (ti i) =
      AlgebraicGeometry.IsOpenImmersion.lift V.ι
        ((BigFppfOver.toScheme B S hS).map (si i)) (hrange i) := fun _ => rfl
  have hti : ∀ i, ti i ≫ sn = si i := fun i =>
    (BigFppfOver.toScheme B S hS).map_injective (by rw [Functor.map_comp, htimap, hsnmap, hlf i])
  have hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj Pobj,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ti i)) := by
    intro x
    have hxV : V.ι x ∈ V := by
      have hmr : V.ι x ∈ Set.range V.ι := ⟨x, rfl⟩
      rwa [Scheme.Opens.range_ι] at hmr
    obtain ⟨i, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.1 hxV
    refine ⟨i, y, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    rw [htimap, ← Scheme.Hom.comp_apply, hlf i, hy]
  have hgen : Sieve.ofArrows Pi ti ∈ BigFppfOver.topology B S hS Pobj :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS ti
      (fun i => (htimap i) ▸ hlfoi i) hcov
  have hs₀ : g.app (Opposite.op Pobj) sn ∈
      ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).obj (Opposite.op Pobj) := by
    refine (BigFppfOver.topology B S hS).superset_covering ?_ hgen
    rw [Sieve.generate_le_iff]
    rintro Z z ⟨i⟩
    change F.map (ti i).op (g.app (Opposite.op Pobj) sn) ∈ (⨆ i, X i).obj _
    have hmem : g.app (Opposite.op (Pi i)) (si i) ∈ (X i).obj (Opposite.op (Pi i)) := by
      have hw : (fsti i ≫ (X i).ι).app (Opposite.op (Pi i)) (𝟙 (Pi i)) =
          (yoneda.map (si i) ≫ g).app (Opposite.op (Pi i)) (𝟙 (Pi i)) := by
        rw [(hpb i).w]
      simp only [NatTrans.comp_app, types_comp_apply, Subfunctor.ι_app, yoneda_map_app] at hw
      exact hw ▸ ((fsti i).app (Opposite.op (Pi i)) (𝟙 (Pi i))).2
    rw [hgnat, hti i]
    exact le_iSup X i (Opposite.op (Pi i)) hmem
  have hmono : Mono sn := by
    refine (BigFppfOver.toScheme B S hS).mono_of_mono_map ?_
    rw [hsnmap]
    infer_instance
  have hmonoY : Mono (yoneda.map sn) := ⟨fun α β hab => by
    ext W s
    have h1 : (α ≫ yoneda.map sn).app W s = (β ≫ yoneda.map sn).app W s := by rw [hab]
    simp only [NatTrans.comp_app, types_comp_apply, yoneda_map_app] at h1
    exact (cancel_mono sn).1 h1⟩
  obtain ⟨e, he⟩ : ∃ e : yoneda.obj Pobj ≅ (Subfunctor.range (yoneda.map sn)).toFunctor,
      e.hom ≫ (Subfunctor.range (yoneda.map sn)).ι = yoneda.map sn :=
    ⟨asIso (Subfunctor.toRange (yoneda.map sn)), Subfunctor.toRange_ι _⟩
  have hNsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS)
      (Subfunctor.range (yoneda.map sn)).toFunctor :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_of_iso_iff e).1 (BigFppfOver.isSheaf_yoneda_obj B S hS Pobj))
  have hNeq : Subfunctor.range (yoneda.map sn) =
      (Subfunctor.range (yoneda.map sn)).sheafify (BigFppfOver.topology B S hS) :=
    (Subfunctor.range (yoneda.map sn)).eq_sheafify
      ((isSheaf_iff_isSheaf_of_type _ _).1 (BigFppfOver.isSheaf_yoneda_obj B S hS a)) hNsheaf
  have hNiff : ∀ (W : BigFppfOver B S hS) (x : W ⟶ a),
      x ∈ (Subfunctor.range (yoneda.map sn)).obj (Opposite.op W) ↔
        g.app (Opposite.op W) x ∈
          ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).obj (Opposite.op W) := by
    refine fun W x => ⟨?_, fun hx => ?_⟩
    · rintro ⟨k, rfl⟩
      rw [show g.app (Opposite.op W) ((yoneda.map sn).app (Opposite.op W) k) = _ from
        (hgnat k sn).symm]
      exact ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).map k.op hs₀
    · have hle : (⨆ i, X i).sieveOfSection (g.app (Opposite.op W) x) ≤
          (Subfunctor.range (yoneda.map sn)).sieveOfSection x := by
        intro W' h hh
        obtain ⟨y, hy⟩ : ∃ y : W' ⟶ a, y = h ≫ x := ⟨_, rfl⟩
        have hnat : F.map h.op (g.app (Opposite.op W) x) = g.app (Opposite.op W') y := by
          rw [hgnat, hy]
        simp only [Subfunctor.sieveOfSection_apply, Subfunctor.iSup_obj,
          Set.mem_iUnion] at hh
        obtain ⟨i, hi⟩ := hh
        rw [hnat] at hi
        have hαle : Subfunctor.range (yoneda.map y ≫ g) ≤ X i := by
          intro W'' w hw
          obtain ⟨z, rfl⟩ := hw
          rw [show (yoneda.map y ≫ g).app W'' z = _ from (hgnat z y).symm]
          exact (X i).map z.op hi
        have hαw : Subfunctor.lift (yoneda.map y ≫ g) hαle ≫ (X i).ι =
            yoneda.map y ≫ g := Subfunctor.lift_ι _ _
        have hk : yoneda.preimage ((hpb i).lift _ (yoneda.map y) hαw) ≫ si i = y := by
          refine yoneda.map_injective ?_
          rw [Functor.map_comp, yoneda.map_preimage,
            (hpb i).lift_snd (Subfunctor.lift (yoneda.map y ≫ g) hαle) (yoneda.map y) hαw]
        refine ⟨yoneda.preimage ((hpb i).lift _ (yoneda.map y) hαw) ≫ ti i, ?_⟩
        change (yoneda.preimage ((hpb i).lift _ (yoneda.map y) hαw) ≫ ti i) ≫ sn = h ≫ x
        rw [Category.assoc, hti i, hk, hy]
      rw [hNeq]
      exact (BigFppfOver.topology B S hS).superset_covering hle hx
  obtain ⟨fstN, hpbN⟩ : ∃ fstN, IsPullback fstN (Subfunctor.range (yoneda.map sn)).ι
      ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).ι g :=
    ⟨_, Subfunctor.isPullback_lift _ g _ fun W x => hNiff W.unop x⟩
  refine ⟨Pobj, e.hom ≫ fstN, sn, hpbN.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using he) (by simp) (by simp), ?_⟩
  exact (inferInstance : AlgebraicGeometry.IsOpenImmersion V.ι)

/-- The sheafification of the union of a family of representable open subspaces, indexed by a
nonempty type of cardinality below the cofinality of the cutoff of the site, is
representable. -/
theorem isRepresentable_sheafify_iSup
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} [Nonempty ι] (hι : Cardinal.mk ι < B.cutoff.ord.cof)
    (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable) :
    ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor.IsRepresentable := by
  have hFt : Presieve.IsSheaf (BigFppfOver.topology B S hS) F :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hF
  have hle : ∀ i, X i ≤ (⨆ j, X j).sheafify (BigFppfOver.topology B S hS) :=
    fun i => (le_iSup X i).trans ((⨆ j, X j).le_sheafify _)
  obtain ⟨T, w, f, hfL⟩ : ∃ (T : ι → BigFppfOver B S hS)
      (w : ∀ i, yoneda.obj (T i) ≅ (X i).toFunctor)
      (f : ∀ i, yoneda.obj (T i) ⟶
        ((⨆ j, X j).sheafify (BigFppfOver.topology B S hS)).toFunctor),
      ∀ i, f i ≫ ((⨆ j, X j).sheafify (BigFppfOver.topology B S hS)).ι =
        (w i).hom ≫ (X i).ι :=
    ⟨fun i => (X i).toFunctor.reprX, fun i => (X i).toFunctor.reprW,
      fun i => (X i).toFunctor.reprW.hom ≫ Subfunctor.homOfLe (hle i),
      fun i => by rw [Category.assoc, Subfunctor.homOfLe_ι]⟩
  have hfi : ∀ i, IsOpenImmersion B S hS (f i) := by
    intro i
    refine MorphismProperty.presheaf_of_comp_mono _
      (m := ((⨆ j, X j).sheafify (BigFppfOver.topology B S hS)).ι) ?_
    rw [hfL i]
    exact MorphismProperty.RespectsIso.precomp _ (w i).hom (X i).ι (hXopen i)
  have hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc f) := by
    refine ⟨fun {W} s => (BigFppfOver.topology B S hS).superset_covering ?_ s.2⟩
    intro W' h hh
    simp only [Subfunctor.sieveOfSection_apply, Subfunctor.iSup_obj, Set.mem_iUnion] at hh
    obtain ⟨i, hi⟩ := hh
    obtain ⟨v, hv⟩ : ∃ v : (X i).toFunctor.obj (Opposite.op W'), v.1 = F.map h.op s.1 :=
      ⟨⟨F.map h.op s.1, hi⟩, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : (yoneda.obj (T i)).obj (Opposite.op W'),
        (w i).hom.app (Opposite.op W') t = v :=
      ⟨(w i).inv.app (Opposite.op W') v, by rw [← NatTrans.comp_app_apply, Iso.inv_hom_id]; rfl⟩
    refine ⟨(Sigma.ι (fun j => yoneda.obj (T j)) i).app (Opposite.op W') t, Subtype.ext ?_⟩
    rw [← NatTrans.comp_app_apply, Sigma.ι_comp_desc]
    have h2 : (((f i).app (Opposite.op W') t).1 : F.obj (Opposite.op W')) =
        ((w i).hom ≫ (X i).ι).app (Opposite.op W') t := by
      rw [← hfL i]
      rfl
    rw [h2]
    simp only [NatTrans.comp_app, types_comp_apply, Subfunctor.ι_app, ht]
    exact hv
  exact isRepresentable_of_zariskiCover_of_lt_cof B S hS
    ((isSheaf_iff_isSheaf_of_type _ _).2 ((⨆ i, X i).sheafify_isSheaf hFt)) hι T f hfi hsurj

/-- The sheafification of the union of a family of representable open subspaces, indexed by a
nonempty type of cardinality below the cofinality of the cutoff of the site, is an open
subspace. -/
theorem isOpenSubspace_sheafify_iSup
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} [Nonempty ι] (hι : Cardinal.mk ι < B.cutoff.ord.cof)
    (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable) :
    IsOpenSubspace B S hS ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)) := by
  have hrep := isRepresentable_sheafify_iSup B S hS hF hι X hXopen hXrep
  exact ⟨(isAlgebraicSpace_yoneda B S hS _).of_iso
      ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor.reprW,
    isOpenImmersion_sheafify_iSup_ι B S hS hF X hXopen⟩

/-- If the representable open subspaces of an algebraic space are all contained in the
union of a small family of them, then the schematic locus is that union, sheafified. -/
theorem schematicLocus_eq_sheafify_iSup
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {ι : Type u} [Nonempty ι] (hι : Cardinal.mk ι < B.cutoff.ord.cof)
    (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenSubspace B S hS (X i))
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable)
    (hcof : ∀ G : Subfunctor F, IsOpenSubspace B S hS G → G.toFunctor.IsRepresentable →
      G ≤ ⨆ i, X i) :
    schematicLocus B S hS F = (⨆ i, X i).sheafify (BigFppfOver.topology B S hS) :=
  le_antisymm
    (sSup_le fun G hG => (hcof G hG.1 hG.2).trans ((⨆ i, X i).le_sheafify _))
    (le_schematicLocus B S hS F _
      (isOpenSubspace_sheafify_iSup B S hS hF.isSheaf hι X
        (fun i => (hXopen i).2) hXrep)
      (isRepresentable_sheafify_iSup B S hS hF.isSheaf hι X
        (fun i => (hXopen i).2) hXrep))

/-- If the representable open subspaces of an algebraic space over `S` are all contained in
the union of a small family of them, then its schematic locus is an open subspace. -/
theorem isOpenSubspace_schematicLocus
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {ι : Type u} [Nonempty ι] (hι : Cardinal.mk ι < B.cutoff.ord.cof)
    (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenSubspace B S hS (X i))
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable)
    (hcof : ∀ G : Subfunctor F, IsOpenSubspace B S hS G → G.toFunctor.IsRepresentable →
      G ≤ ⨆ i, X i) :
    IsOpenSubspace B S hS (schematicLocus B S hS F) := by
  rw [schematicLocus_eq_sheafify_iSup B S hS hF hι X hXopen hXrep hcof]
  exact isOpenSubspace_sheafify_iSup B S hS hF.isSheaf hι X
    (fun i => (hXopen i).2) hXrep

/-- If the representable open subspaces of an algebraic space over `S` are all contained in
the union of a small family of them, then its schematic locus is represented by a scheme over
`S`. -/
theorem isRepresentable_schematicLocus
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {ι : Type u} [Nonempty ι] (hι : Cardinal.mk ι < B.cutoff.ord.cof)
    (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenSubspace B S hS (X i))
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable)
    (hcof : ∀ G : Subfunctor F, IsOpenSubspace B S hS G → G.toFunctor.IsRepresentable →
      G ≤ ⨆ i, X i) :
    (schematicLocus B S hS F).toFunctor.IsRepresentable := by
  rw [schematicLocus_eq_sheafify_iSup B S hS hF hι X hXopen hXrep hcof]
  exact isRepresentable_sheafify_iSup B S hS hF.isSheaf hι X
    (fun i => (hXopen i).2) hXrep

end AlgebraicGeometry.Space

end
