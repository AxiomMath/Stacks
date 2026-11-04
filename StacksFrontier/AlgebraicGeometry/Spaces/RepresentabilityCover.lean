module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus

/-!
# Representability which remembers the covering

A sheaf `F` on the big fppf site of `S` which carries a Zariski covering by representable open
subfunctors `f i : yoneda.obj (X i) ⟶ F` is representable (Stacks 01JJ). This file records the
covering of the representing object as well: `F` is represented by an object `Y` of the site,
through an isomorphism `e : F ≅ yoneda.obj Y`, together with open immersions `g i : X i ⟶ Y`
whose images cover the scheme underlying `Y` and which satisfy `f i ≫ e.hom = yoneda.map (g i)`.

## Main results

* `CategoryTheory.Subfunctor.exists_mem_range_app_of_sigmaDesc`: a section of a coproduct of
  presheaves lands, under the coproduct morphism, in the range of one of the components.
* `AlgebraicGeometry.exists_representing_cover_of_isRepresentable`: a sheaf which is
  representable *and* carries a Zariski covering by representable open subfunctors is
  represented by an object of the site which the charts cover by open immersions.
* `AlgebraicGeometry.exists_representing_cover_over_of_isRepresentable`: the same over a test
  object, which also produces the projection of the representing object to the test object.
* `AlgebraicGeometry.isPullback_of_representing_cover_over` and
  `AlgebraicGeometry.isPullback_toScheme_of_representing_cover_over`: a piece of the covering
  is a base change of the glued projection, as soon as the chart it came from is a base change
  of the structure morphism.
* `AlgebraicGeometry.exists_representing_cover_of_zariskiCover`, and its two specializations
  `AlgebraicGeometry.exists_representing_cover_of_zariskiCover_of_lt_cof` and
  `AlgebraicGeometry.exists_representing_cover_of_zariskiCover_of_size_le`: a sheaf with a
  Zariski covering by representable open subfunctors is represented by an object of the site
  which the charts cover by open immersions.
* `AlgebraicGeometry.exists_representing_cover_over_of_zariskiCover`: its relative form over a
  test object.
* `AlgebraicGeometry.Space.exists_charts_sheafify_iSup`: the charts of the sheafified union of
  a family of representable open subspaces, with their openness and their joint local
  surjectivity.
* `AlgebraicGeometry.Space.exists_representing_cover_sheafify_iSup`: the sheafified union of a
  family of representable open subspaces is represented by an object of the site which the
  representing objects of the members cover by open immersions.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}

/-- A section of a coproduct of presheaves lands, under the morphism which the coproduct
induces out of a family `f`, in the range of one of the `f i`. -/
theorem exists_mem_range_app_of_sigmaDesc {I : Type*} {G : I → Cᵒᵖ ⥤ Type w}
    (f : ∀ i, G i ⟶ F) [HasCoproduct G] (c : Cᵒᵖ) (t : (∐ G).obj c) :
    ∃ i, (Sigma.desc f).app c t ∈ Set.range ((f i).app c) := by
  have hfac : (Sigma.desc fun i => lift (f i) (le_iSup (fun j => range (f j)) i)) ≫
      (⨆ i, range (f i)).ι = Sigma.desc f :=
    Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_desc_assoc, lift_ι, Sigma.ι_desc]
  have hmem : (Sigma.desc f).app c t ∈ (⨆ i, range (f i)).obj c := by
    rw [← hfac]
    exact ((Sigma.desc fun i => lift (f i) (le_iSup (fun j => range (f j)) i)).app c t).property
  simpa [iSup_obj] using hmem

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reading the covering off representability -/

/-- A presheaf `F` on the big fppf category over
`S` which carries a Zariski covering by representable open subfunctors — relatively
representable open immersions `f i : yoneda.obj (X i) ⟶ F` whose coproduct maps onto `F`
locally — and which *is* representable, is represented by an object `Y` of the category whose
underlying scheme is covered by the images of open immersions `g i`, one for each chart, and
each chart is identified with its piece of that covering by `f i ≫ e.hom = yoneda.map (g i)`. -/
theorem exists_representing_cover_of_isRepresentable
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ι : Type u} {X : ι → BigFppfOver B S hS}
    (f : ∀ i, yoneda.obj (X i) ⟶ F) (hf : ∀ i, Space.IsOpenImmersion B S hS (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f))
    (hrep : F.IsRepresentable) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (g : ∀ i, X i ⟶ Y),
      (∀ i, f i ≫ e.hom = yoneda.map (g i)) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)) := by
  obtain ⟨Y, ⟨e⟩⟩ : ∃ Y : BigFppfOver B S hS, Nonempty (F ≅ yoneda.obj Y) :=
    ⟨F.reprX, ⟨F.reprW.symm⟩⟩
  refine ⟨Y, e, fun i => yoneda.preimage (f i ≫ e.hom), fun i => (yoneda.map_preimage _).symm,
    fun i => ?_, ?_⟩
  · have h1 : Space.IsOpenImmersion B S hS (yoneda.map (yoneda.preimage (f i ≫ e.hom))) := by
      rw [yoneda.map_preimage]
      exact MorphismProperty.RespectsIso.postcomp _ e.hom (f i) (hf i)
    have h2 : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (yoneda.preimage (f i ≫ e.hom)) :=
      MorphismProperty.of_relative_map (F := yoneda) h1
    exact h2
  · intro y
    have hd : (Sigma.desc fun i => yoneda.map (yoneda.preimage (f i ≫ e.hom))) =
        Sigma.desc f ≫ e.hom :=
      Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_desc, Sigma.ι_desc_assoc, yoneda.map_preimage]
    have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (Sigma.desc fun i => yoneda.map (yoneda.preimage (f i ≫ e.hom))) := by
      rw [hd]
      infer_instance
    have hR := Presheaf.imageSieve_mem (BigFppfOver.topology B S hS)
      (Sigma.desc fun i => yoneda.map (yoneda.preimage (f i ≫ e.hom))) (U := op Y) (𝟙 Y)
    obtain ⟨c, h, ⟨t, ht⟩, z, hz⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS hR y
    obtain ⟨i, hi⟩ := Subfunctor.exists_mem_range_app_of_sigmaDesc _ (op c) t
    rw [ht] at hi
    obtain ⟨m, hm⟩ := hi
    have hm' : m ≫ yoneda.preimage (f i ≫ e.hom) = h := by
      simpa only [yoneda_obj_obj, yoneda_map_app, yoneda_obj_map, Quiver.Hom.unop_op,
        TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Category.comp_id] using hm
    refine ⟨i, (BigFppfOver.toScheme B S hS).map m z, ?_⟩
    rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp, hm']

/-- A presheaf `F` with a morphism `π : F ⟶ yoneda.obj T` which is representable and carries
a Zariski covering by representable open subfunctors `f i` is represented by an object `Y` of
the site, through `e : F ≅ yoneda.obj Y`, together with a projection `p : Y ⟶ T` with
`e.inv ≫ π = yoneda.map p`, and the charts cover `Y` by open immersions `g i` with
`f i ≫ e.hom = yoneda.map (g i)` and `yoneda.map (g i ≫ p) = f i ≫ π`. -/
theorem exists_representing_cover_over_of_isRepresentable
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : F ⟶ yoneda.obj T)
    {ι : Type u} {X : ι → BigFppfOver B S hS}
    (f : ∀ i, yoneda.obj (X i) ⟶ F) (hf : ∀ i, Space.IsOpenImmersion B S hS (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f))
    (hrep : F.IsRepresentable) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (p : Y ⟶ T) (g : ∀ i, X i ⟶ Y),
      e.inv ≫ π = yoneda.map p ∧
      (∀ i, f i ≫ e.hom = yoneda.map (g i)) ∧
      (∀ i, yoneda.map (g i ≫ p) = f i ≫ π) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)) := by
  obtain ⟨Y, e, g, hfg, hgopen, hgcov⟩ :=
    exists_representing_cover_of_isRepresentable B S hS f hf hsurj hrep
  refine ⟨Y, e, yoneda.preimage (e.inv ≫ π), g, (yoneda.map_preimage _).symm, hfg,
    fun i => ?_, hgopen, hgcov⟩
  rw [Functor.map_comp, ← hfg, yoneda.map_preimage, Category.assoc, Iso.hom_inv_id_assoc]

/-- In the situation of `AlgebraicGeometry.exists_representing_cover_over_of_isRepresentable`,
suppose the chart `f : yoneda.obj V ⟶ F` is the base change of a morphism `u : T' ⟶ T` of the
site along the structure morphism `π`. Then the piece `g : V ⟶ Y` of the covering of the
representing object is the base change of the glued projection `p : Y ⟶ T` along `u`. -/
theorem isPullback_of_representing_cover_over
    {T T' Y V : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {π : F ⟶ yoneda.obj T} {e : F ≅ yoneda.obj Y} {p : Y ⟶ T}
    (hp : e.inv ≫ π = yoneda.map p) {f : yoneda.obj V ⟶ F} {g : V ⟶ Y}
    (hfg : f ≫ e.hom = yoneda.map g) {q : V ⟶ T'} {u : T' ⟶ T}
    (hpb : IsPullback f (yoneda.map q) π (yoneda.map u)) :
    IsPullback g q p u := by
  have h0 : IsPullback (f ≫ e.hom) (yoneda.map q) (e.inv ≫ π) (yoneda.map u) :=
    hpb.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  rw [hfg, hp] at h0
  exact IsPullback.of_map_of_faithful yoneda h0

/-- In the situation of `AlgebraicGeometry.isPullback_of_representing_cover_over`, the
underlying morphism of schemes of `g` is the base change of that of `p` along that of `u`. -/
theorem isPullback_toScheme_of_representing_cover_over
    {T T' Y V : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {π : F ⟶ yoneda.obj T} {e : F ≅ yoneda.obj Y} {p : Y ⟶ T}
    (hp : e.inv ≫ π = yoneda.map p) {f : yoneda.obj V ⟶ F} {g : V ⟶ Y}
    (hfg : f ≫ e.hom = yoneda.map g) {q : V ⟶ T'} {u : T' ⟶ T}
    (hpb : IsPullback f (yoneda.map q) π (yoneda.map u)) :
    IsPullback ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map p) ((BigFppfOver.toScheme B S hS).map u) :=
  (isPullback_of_representing_cover_over B S hS hp hfg hpb).map (BigFppfOver.toScheme B S hS)

/-! ### Tag 01JJ over the big fppf site of a scheme, with its covering -/

/-- A sheaf `F` for the fppf topology of the big fppf category over `S` which carries a Zariski
covering by representable open subfunctors is represented by an object `Y` of that category
whose underlying scheme is covered by the images of open immersions from the charts, each
chart being identified with its piece of the covering, provided (`hcontains`) any scheme
carrying a jointly surjective family of open immersions from the charts is contained in the
site. -/
theorem exists_representing_cover_of_zariskiCover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} (X : ι → BigFppfOver B S hS) (f : ∀ i, yoneda.obj (X i) ⟶ F)
    (hf : ∀ i, Space.IsOpenImmersion B S hS (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f))
    (hcontains : ∀ (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (X i) ⟶ Z), (∀ i, IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (g : ∀ i, X i ⟶ Y),
      (∀ i, f i ≫ e.hom = yoneda.map (g i)) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)) := by
  obtain ⟨Z, q, k, hk, -, hcov, hiso⟩ := hasZariskiGluing B S hS F hF X f hf hsurj
  exact exists_representing_cover_of_isRepresentable B S hS f hf hsurj
    (Functor.IsRepresentable.mk' (hiso (hcontains Z k hk hcov)).some.symm)

/-- A sheaf `F` for the fppf topology of the big fppf category over `S` which carries a Zariski
covering by representable open subfunctors, indexed by a nonempty type `ι` with
`#ι < B.cutoff.ord.cof`, is represented by an object `Y` of that category whose underlying
scheme is covered by the images of open immersions from the charts, each chart being
identified with its piece of the covering. -/
theorem exists_representing_cover_of_zariskiCover_of_lt_cof
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} [Nonempty ι] (hι : Cardinal.mk ι < B.cutoff.ord.cof)
    (X : ι → BigFppfOver B S hS) (f : ∀ i, yoneda.obj (X i) ⟶ F)
    (hf : ∀ i, Space.IsOpenImmersion B S hS (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (g : ∀ i, X i ⟶ Y),
      (∀ i, f i ≫ e.hom = yoneda.map (g i)) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)) :=
  exists_representing_cover_of_zariskiCover B S hS hF X f hf hsurj
    fun _ k _ hcov => B.contains_of_openCover hι k hcov fun i => (X i).left.property

/-- A sheaf `F` for the fppf topology of the big fppf category over `S` which carries a Zariski
covering by representable open subfunctors, indexed by a nonempty type `ι` with `#ι ≤ μ` and
with charts of size at most `μ`, where `μ < B.cutoff`, is represented by an object `Y` of that
category whose underlying scheme is covered by the images of open immersions from the charts,
each chart being identified with its piece of the covering. -/
theorem exists_representing_cover_of_zariskiCover_of_size_le
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} [Nonempty ι] {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hι : Cardinal.mk ι ≤ μ) (X : ι → BigFppfOver B S hS)
    (hX : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ)
    (f : ∀ i, yoneda.obj (X i) ⟶ F) (hf : ∀ i, Space.IsOpenImmersion B S hS (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (g : ∀ i, X i ⟶ Y),
      (∀ i, f i ≫ e.hom = yoneda.map (g i)) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)) :=
  exists_representing_cover_of_zariskiCover B S hS hF X f hf hsurj
    fun _ k _ hcov => B.contains_of_openCover_of_size_le hμ hι k hcov hX

/-- A sheaf `F` for the fppf topology with a morphism `π : F ⟶ yoneda.obj T`, which carries a
Zariski covering by representable open subfunctors `f i`, is represented by an object `Y` of
the site, through `e : F ≅ yoneda.obj Y`, together with a projection `p : Y ⟶ T` with
`e.inv ≫ π = yoneda.map p`, and the charts cover `Y` by open immersions `g i` with
`f i ≫ e.hom = yoneda.map (g i)` and `yoneda.map (g i ≫ p) = f i ≫ π`, provided
(`hcontains`) any scheme carrying a jointly surjective family of open immersions from the
charts is contained in the site. -/
theorem exists_representing_cover_over_of_zariskiCover
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ yoneda.obj T)
    {ι : Type u} (X : ι → BigFppfOver B S hS) (f : ∀ i, yoneda.obj (X i) ⟶ F)
    (hf : ∀ i, Space.IsOpenImmersion B S hS (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f))
    (hcontains : ∀ (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (X i) ⟶ Z), (∀ i, IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (p : Y ⟶ T) (g : ∀ i, X i ⟶ Y),
      e.inv ≫ π = yoneda.map p ∧
      (∀ i, f i ≫ e.hom = yoneda.map (g i)) ∧
      (∀ i, yoneda.map (g i ≫ p) = f i ≫ π) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)) := by
  obtain ⟨Z, q, k, hk, -, hcov, hiso⟩ := hasZariskiGluing B S hS F hF X f hf hsurj
  exact exists_representing_cover_over_of_isRepresentable B S hS π f hf hsurj
    (Functor.IsRepresentable.mk' (hiso (hcontains Z k hk hcov)).some.symm)

/-! ### The sheafified union of representable open subspaces, with its covering -/

namespace Space

/-- The charts of the sheafification of a union of representable open subspaces: the
representing objects of the members of the family, mapping into the sheafification, with the
identification of each chart with the member it represents, the openness of each chart, and
their joint local surjectivity. -/
theorem exists_charts_sheafify_iSup {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable) :
    ∃ (T : ι → BigFppfOver B S hS) (w : ∀ i, yoneda.obj (T i) ≅ (X i).toFunctor)
      (f : ∀ i, yoneda.obj (T i) ⟶
        ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor),
      (∀ i, f i ≫ ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).ι =
        (w i).hom ≫ (X i).ι) ∧
      (∀ i, IsOpenImmersion B S hS (f i)) ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f) := by
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
  refine ⟨T, w, f, hfL, fun i => ?_, ?_⟩
  · refine MorphismProperty.presheaf_of_comp_mono _
      (m := ((⨆ j, X j).sheafify (BigFppfOver.topology B S hS)).ι) ?_
    rw [hfL i]
    exact MorphismProperty.RespectsIso.precomp _ (w i).hom (X i).ι (hXopen i)
  · refine ⟨fun {W} s => (BigFppfOver.topology B S hS).superset_covering ?_ s.2⟩
    intro W' h hh
    simp only [Subfunctor.sieveOfSection_apply, Subfunctor.iSup_obj, Set.mem_iUnion] at hh
    obtain ⟨i, hi⟩ := hh
    obtain ⟨v, hv⟩ : ∃ v : (X i).toFunctor.obj (op W'), v.1 = F.map h.op s.1 :=
      ⟨⟨F.map h.op s.1, hi⟩, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : (yoneda.obj (T i)).obj (op W'), (w i).hom.app (op W') t = v :=
      ⟨(w i).inv.app (op W') v, by rw [← FunctorToTypes.comp, Iso.inv_hom_id]; rfl⟩
    refine ⟨(Sigma.ι (fun j => yoneda.obj (T j)) i).app (op W') t, Subtype.ext ?_⟩
    rw [← FunctorToTypes.comp, Sigma.ι_desc]
    have h2 : (((f i).app (op W') t).1 : F.obj (op W')) =
        ((w i).hom ≫ (X i).ι).app (op W') t := by
      rw [← hfL i]
      rfl
    rw [h2]
    simp only [NatTrans.comp_app, types_comp_apply, Subfunctor.ι_app, ht]
    exact hv

/-- The sheafification of the union of a family of representable open subspaces is represented by
an object `Y` of the site whose underlying scheme is covered by the images of open immersions `g i`
from the representing objects `T i` of the members, and the composite of `g i` with the
identification of `Y` with the sheafification and the inclusion of the sheafification into the
ambient presheaf is the inclusion of the `i`-th member, provided (`hcontains`) any scheme carrying
a jointly surjective family of open immersions from objects representing the members is contained
in the site. -/
theorem exists_representing_cover_sheafify_iSup
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {ι : Type u} (X : ι → Subfunctor F) (hXopen : ∀ i, IsOpenImmersion B S hS (X i).ι)
    (hXrep : ∀ i, (X i).toFunctor.IsRepresentable)
    (hcontains : ∀ (T : ι → BigFppfOver B S hS),
      (∀ i, Nonempty (yoneda.obj (T i) ≅ (X i).toFunctor)) → ∀ (Z : Scheme.{u})
      (k : ∀ i, (BigFppfOver.toScheme B S hS).obj (T i) ⟶ Z),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z) :
    ∃ (Y : BigFppfOver B S hS)
      (e : ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).toFunctor ≅ yoneda.obj Y)
      (T : ι → BigFppfOver B S hS) (w : ∀ i, yoneda.obj (T i) ≅ (X i).toFunctor)
      (g : ∀ i, T i ⟶ Y),
      (∀ i, yoneda.map (g i) ≫ e.inv ≫
        ((⨆ i, X i).sheafify (BigFppfOver.topology B S hS)).ι = (w i).hom ≫ (X i).ι) ∧
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)) := by
  have hFt : Presieve.IsSheaf (BigFppfOver.topology B S hS) F :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hF
  obtain ⟨T, w, f, hfL, hfi, hsurj⟩ :=
    exists_charts_sheafify_iSup B S hS X hXopen hXrep
  obtain ⟨Y, e, g, hfg, hgopen, hgcov⟩ :=
    exists_representing_cover_of_zariskiCover B S hS
      ((isSheaf_iff_isSheaf_of_type _ _).2 ((⨆ i, X i).sheafify_isSheaf hFt)) T f hfi hsurj
      (hcontains T fun i => ⟨w i⟩)
  refine ⟨Y, e, T, w, g, fun i => ?_, hgopen, hgcov⟩
  rw [← hfg i, Category.assoc, Iso.hom_inv_id_assoc, hfL i]

end Space

end AlgebraicGeometry

end
