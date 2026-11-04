module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafCoproduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affineness of a morphism of algebraic spaces is local on a disjoint union of affine charts

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`. If the base change of `f` along every
étale morphism from an affine object of the site is represented by an affine object, then the
base change of `f` along a surjective étale chart of `Y` by a disjoint union of affine objects
(Stacks 03FX) is an affine morphism of algebraic spaces in the sense of Stacks 03WF. This is the
implication (3) ⇒ (4) of Stacks 03WG.

## Main results

The decomposition, in schemes:

* `AlgebraicGeometry.isAffine_of_isOpenImmersion_of_isClosed_range`: an open subscheme whose
  image is closed in an affine scheme is affine.
* `AlgebraicGeometry.iSup_opensRange_sigmaι`: the summands of a coproduct of schemes cover it.
* `AlgebraicGeometry.iSup_preimage_opensRange_sigmaι` and
  `AlgebraicGeometry.disjoint_preimage_opensRange_sigmaι`: the preimages of the summands along
  a morphism to the coproduct cover the source and are pairwise disjoint.
* `AlgebraicGeometry.exists_finset_isClosed_preimage_opensRange_sigmaι`: finitely many of those
  preimages already cover a quasi-compact source, and then each of them is closed.
* `AlgebraicGeometry.exists_finite_isColimit_cofan_of_hom_sigma`: a quasi-compact scheme with a
  morphism to a coproduct of schemes is a coproduct of finitely many open subschemes of itself
  with closed image, each of which maps into a single summand.
* `AlgebraicGeometry.isOpenImmersion_cover_disjoint_of_iso_sigma`: a family presented as a
  coproduct decomposition by an isomorphism out of `∐` is a pairwise disjoint open covering.

The decomposition, in the big fppf category over `S`:

* `AlgebraicGeometry.BigFppfOver.toScheme_map_comp_hom`: a morphism of the site commutes with
  the structure morphisms to `S`.
* `AlgebraicGeometry.BigFppfOver.exists_coproduct_of_mk_le_aleph0`: an at most countable family
  of objects of the site has a coproduct in the site, with its universal property.
* `AlgebraicGeometry.BigFppfOver.exists_finite_decomposition_of_hom_coproduct` and its affine
  form `AlgebraicGeometry.BigFppfOver.exists_finite_affine_decomposition_of_hom_coproduct`: the
  finite clopen decomposition of a quasi-compact, respectively affine, object of the site
  mapping to an object presented as a coproduct.
* `AlgebraicGeometry.BigFppfOver.existsUnique_lift_of_isOpenImmersion`: a morphism of the site
  whose image lies in the image of an open immersion factors uniquely through it.
* `AlgebraicGeometry.BigFppfOver.exists_disjoint_openCover_pullback`: a disjoint open covering
  pulls back to a disjoint open covering along an arbitrary morphism.

The gluing:

* `AlgebraicGeometry.BigFppfOver.existsUnique_section_of_disjoint_openCover`: a sheaf on the
  site turns a disjoint open covering into a product — a family of sections over the members
  has a unique amalgamation, with no compatibility hypothesis.
* `AlgebraicGeometry.BigFppfOver.section_ext_of_disjoint_openCover` and
  `AlgebraicGeometry.BigFppfOver.hom_ext_of_disjoint_openCover`: the separatedness halves.
* `AlgebraicGeometry.BigFppfOver.range_eq_preimage_range_of_disjoint_openCover`: a disjoint
  open covering lying over another one index by index does so exactly.
* `CategoryTheory.isPullback_of_existsUnique_app`: a commuting square of presheaves of types is
  a pullback square as soon as it is one on sections over every object.
* `AlgebraicGeometry.isPullback_of_disjoint_openCover`: a morphism of sheaves represented over
  each member of a disjoint open covering of the base is represented over the base.

The consequences for Stacks 03WG:

* `AlgebraicGeometry.Space.isAffineHom_pullback_snd_of_coproduct_affine_atlas`: if the base
  change of `f` along each summand of a coproduct chart is represented by an affine object,
  then the base change along the chart is an affine morphism of algebraic spaces.
* `AlgebraicGeometry.Space.exists_etaleChart_isAffineHom_of_isEtale_affine`: the implication
  (3) ⇒ (4) of Stacks 03WG.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry

/-- An open subscheme of an affine scheme whose image is closed is affine. -/
theorem isAffine_of_isOpenImmersion_of_isClosed_range {X Z : Scheme.{u}} (f : X ⟶ Z)
    [IsOpenImmersion f] [IsAffine Z] (hf : IsClosed (Set.range f)) : IsAffine X := by
  have : IsClosedImmersion f := IsClosedImmersion.of_isPreimmersion f hf
  exact isAffine_of_isAffineHom f

/-- The summands of a coproduct of schemes cover it. -/
theorem iSup_opensRange_sigmaι {I : Type u} (Y : I → Scheme.{u}) :
    (⨆ i, (Sigma.ι Y i).opensRange) = ⊤ := by
  refine TopologicalSpace.Opens.ext ?_
  rw [Opens.coe_iSup, Opens.coe_top]
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun i => Y i)).surjective x
  exact Set.mem_iUnion.2 ⟨i, by simp [sigmaMk_mk]⟩

section Sigma

variable {I : Type u} (Y : I → Scheme.{u}) {Z : Scheme.{u}} (z : Z ⟶ ∐ Y)

/-- The preimages of the summands along a morphism to a coproduct of schemes cover the
source. -/
theorem iSup_preimage_opensRange_sigmaι : (⨆ i, z ⁻¹ᵁ (Sigma.ι Y i).opensRange) = ⊤ := by
  refine TopologicalSpace.Opens.ext ?_
  rw [Opens.coe_iSup, Opens.coe_top]
  refine Set.eq_univ_of_forall fun x => ?_
  have hx : z x ∈ (⨆ i, (Sigma.ι Y i).opensRange) := by rw [iSup_opensRange_sigmaι]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  exact Set.mem_iUnion.2 ⟨i, hi⟩

/-- The preimages of two distinct summands along a morphism to a coproduct of schemes are
disjoint. -/
theorem disjoint_preimage_opensRange_sigmaι {i j : I} (hij : i ≠ j) :
    Disjoint (z ⁻¹ᵁ (Sigma.ι Y i).opensRange) (z ⁻¹ᵁ (Sigma.ι Y j).opensRange) := by
  have h := disjoint_opensRange_sigmaι Y i j hij
  rw [disjoint_iff] at h ⊢
  rw [← Scheme.Hom.preimage_inf, h]
  simp

/-- Finitely many of the preimages of the summands along a morphism from a quasi-compact scheme
to a coproduct of schemes already cover the source, and then each of them is closed. -/
theorem exists_finset_isClosed_preimage_opensRange_sigmaι [CompactSpace Z] :
    ∃ s : Finset I,
      (⋃ i ∈ s, ((z ⁻¹ᵁ (Sigma.ι Y i).opensRange : Z.Opens) : Set Z)) = Set.univ ∧
      ∀ i ∈ s, IsClosed ((z ⁻¹ᵁ (Sigma.ι Y i).opensRange : Z.Opens) : Set Z) := by
  set V : I → Z.Opens := fun i => z ⁻¹ᵁ (Sigma.ι Y i).opensRange with hV
  have hunion : (Set.univ : Set Z) ⊆ ⋃ i, (V i : Set Z) := by
    intro x _
    have hx : x ∈ (⨆ i, V i) := by rw [hV, iSup_preimage_opensRange_sigmaι]; trivial
    exact Set.mem_iUnion.2 (Opens.mem_iSup.1 hx)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun i : I => (V i : Set Z))
    (fun i => (V i).isOpen) hunion
  have hcov : (⋃ i ∈ s, (V i : Set Z)) = Set.univ :=
    Set.eq_univ_of_univ_subset (by simpa using hs)
  refine ⟨s, hcov, fun i _ => ?_⟩
  rw [← isOpen_compl_iff]
  have he : ((V i : Set Z))ᶜ = ⋃ l : {l : I // l ∈ s ∧ l ≠ i}, (V l.1 : Set Z) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    refine ⟨fun hx => ?_, fun ⟨⟨l, _, hli⟩, hxl⟩ hxi => Set.disjoint_left.mp
      (Opens.coe_disjoint.mpr (disjoint_preimage_opensRange_sigmaι Y z hli)) hxl hxi⟩
    obtain ⟨l, hls, hxl⟩ := Set.mem_iUnion₂.mp (hcov.ge (Set.mem_univ x))
    exact ⟨⟨l, hls, fun h => hx (h ▸ hxl)⟩, hxl⟩
  rw [he]
  exact isOpen_iUnion fun l => (V l.1).isOpen

/-- A quasi-compact scheme `Z` with a morphism `z` to a coproduct `∐ Y` of schemes is the coproduct
of finitely many open subschemes of itself whose images are closed, each of which maps into a
single summand compatibly with `z`. -/
@[sga "3 X 5.12" "Over affine S"]
theorem exists_finite_isColimit_cofan_of_hom_sigma [CompactSpace Z] :
    ∃ (σ : Type u) (_ : Finite σ) (k : σ → I) (Z' : σ → Scheme.{u})
      (p : ∀ a, Z' a ⟶ Z) (w : ∀ a, Z' a ⟶ Y (k a)),
      (∀ a, IsOpenImmersion (p a)) ∧
      (∀ a, IsClosed (Set.range (p a))) ∧
      Nonempty (IsColimit (Cofan.mk Z p)) ∧
      (∀ a, w a ≫ Sigma.ι Y (k a) = p a ≫ z) := by
  obtain ⟨s, hcov, hclosed⟩ := exists_finset_isClosed_preimage_opensRange_sigmaι Y z
  set V : I → Z.Opens := fun i => z ⁻¹ᵁ (Sigma.ι Y i).opensRange with hV
  have hrange : ∀ i : I, Set.range ((V i).ι ≫ z) ⊆ Set.range (Sigma.ι Y i) := by
    rintro i _ ⟨x, rfl⟩
    exact x.2
  refine ⟨{i : I // i ∈ s}, inferInstance, Subtype.val, fun a => (V a.1).toScheme,
    fun a => (V a.1).ι, fun a => IsOpenImmersion.lift _ _ (hrange a.1),
    fun a => inferInstance, fun a => ?_, ?_, fun a => IsOpenImmersion.lift_fac _ _ _⟩
  · rw [Scheme.Opens.range_ι]
    exact hclosed a.1 a.2
  · refine nonempty_isColimit_cofanMk_of _ ?_ ?_
    · refine TopologicalSpace.Opens.ext ?_
      rw [Opens.coe_iSup, Opens.coe_top, ← hcov]
      simp only [Scheme.Opens.opensRange_ι]
      exact (Set.iUnion_subtype _ _).trans rfl
    · intro a b hab
      simp only [Function.onFun, Scheme.Opens.opensRange_ι]
      exact disjoint_preimage_opensRange_sigmaι Y z (fun h => hab (Subtype.ext h))

/-- A family of morphisms whose composites with an isomorphism out of a coproduct of schemes
are the coproduct injections consists of open immersions whose images are pairwise disjoint and
jointly cover the target. -/
theorem isOpenImmersion_cover_disjoint_of_iso_sigma {I : Type u} {Y : I → Scheme.{u}}
    {P : Scheme.{u}} (e : (∐ Y) ≅ P) {c : ∀ i, Y i ⟶ P}
    (hc : ∀ i, Sigma.ι Y i ≫ e.hom = c i) :
    (∀ i, IsOpenImmersion (c i)) ∧ (∀ x : P, ∃ i, x ∈ Set.range (c i)) ∧
      Pairwise fun i i' ↦ Disjoint (Set.range (c i)) (Set.range (c i')) := by
  refine ⟨fun i ↦ by rw [← hc i]; infer_instance, fun x ↦ ?_, fun i i' hii' ↦ ?_⟩
  · have hx : e.inv x ∈ (⨆ i, (Sigma.ι Y i).opensRange) := by
      rw [iSup_opensRange_sigmaι]; trivial
    obtain ⟨i, y, hy⟩ := Opens.mem_iSup.1 hx
    refine ⟨i, y, ?_⟩
    rw [← hc i, Scheme.Hom.comp_apply, hy]
    simp
  · show Disjoint (Set.range (c i)) (Set.range (c i'))
    rw [Set.disjoint_left]
    rintro _ ⟨y, rfl⟩ ⟨y', hy'⟩
    rw [← hc i, ← hc i', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hy'
    refine Set.disjoint_left.mp
      (Opens.coe_disjoint.mpr (disjoint_opensRange_sigmaι Y i' i hii'.symm)) ⟨y', rfl⟩ ⟨y, ?_⟩
    exact (e.hom.homeomorph.injective hy').symm

end Sigma

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the big fppf category over `S` commutes with the structure morphisms to
`S` of its source and target. -/
theorem BigFppfOver.toScheme_map_comp_hom {X Y : BigFppfOver B S hS} (g : X ⟶ Y) :
    (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom :=
  (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w g))

/-- An at most countable family `T'` of objects of the big fppf category over `S` has a
coproduct in the site: an object `T` with morphisms `c a : T' a ⟶ T`, an isomorphism from the
coproduct of the underlying schemes of the `T' a` to the underlying scheme of `T` identifying
the coproduct injections with the `c a`, and a morphism out of `T` extending any family of
morphisms out of the `T' a`. -/
theorem BigFppfOver.exists_coproduct_of_mk_le_aleph0 {σ : Type u}
    (hσ : Cardinal.mk σ ≤ Cardinal.aleph0) (T' : σ → BigFppfOver B S hS) :
    ∃ (T : BigFppfOver B S hS) (c : ∀ a, T' a ⟶ T)
      (e : (∐ fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) ≅
        (BigFppfOver.toScheme B S hS).obj T),
      (∀ a, Sigma.ι (fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) a ≫ e.hom =
        (BigFppfOver.toScheme B S hS).map (c a)) ∧
      ∀ {M : BigFppfOver B S hS} (m : ∀ a, T' a ⟶ M), ∃ d : T ⟶ M, ∀ a, c a ≫ d = m a := by
  have hsize :
      (∐ fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)).size < B.cutoff :=
    Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof hσ _
      fun a ↦ (T' a).left.property
  set T : BigFppfOver B S hS := Over.mk (B.inclusion.preimage (X := B.obj hsize) (Y := B.obj hS)
    (show B.inclusion.obj (B.obj hsize) ⟶ B.inclusion.obj (B.obj hS) from
      Sigma.desc fun a ↦ B.inclusion.map (T' a).hom)) with hT
  have hTmap : B.inclusion.map T.hom =
      Sigma.desc fun a ↦ B.inclusion.map (T' a).hom := B.inclusion.map_preimage _
  have hc : ∀ a, ∃ ψ : T' a ⟶ T, (BigFppfOver.toScheme B S hS).map ψ =
      Sigma.ι (fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) a := fun a ↦
    BigFppfOver.exists_hom_of_comp_eq B S hS _ (by rw [hTmap, Sigma.ι_desc])
  choose c hcmap using hc
  refine ⟨T, c, Iso.refl _, fun a ↦ by rw [Iso.refl_hom, Category.comp_id, hcmap],
    fun {M} m ↦ ?_⟩
  have hφ : (show (BigFppfOver.toScheme B S hS).obj T ⟶
        (BigFppfOver.toScheme B S hS).obj M from
      Sigma.desc fun a ↦ (BigFppfOver.toScheme B S hS).map (m a)) ≫
      B.inclusion.map M.hom = B.inclusion.map T.hom := by
    rw [hTmap]
    refine Sigma.hom_ext _ _ fun a ↦ ?_
    rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc]
    exact BigFppfOver.toScheme_map_comp_hom (m a)
  obtain ⟨d, hd⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS _ hφ
  refine ⟨d, fun a ↦ (BigFppfOver.toScheme B S hS).map_injective ?_⟩
  rw [Functor.map_comp, hd, hcmap a, Sigma.ι_desc]

/-- Auxiliary form of `BigFppfOver.existsUnique_lift_of_isOpenImmersion`. -/
private theorem existsUnique_lift_aux
    {M N Z : BigFppfOver B S hS} (n : N ⟶ Z)
    (hn : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map n)) (m : M ⟶ Z)
    (hm : Set.range ((BigFppfOver.toScheme B S hS).map m) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map n)) :
    ∃! l : M ⟶ N, l ≫ n = m := by
  have hfac : (IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map n)
      ((BigFppfOver.toScheme B S hS).map m) hm) ≫ B.inclusion.map N.hom =
      B.inclusion.map M.hom := by
    rw [← BigFppfOver.toScheme_map_comp_hom n, ← Category.assoc, IsOpenImmersion.lift_fac,
      BigFppfOver.toScheme_map_comp_hom m]
  obtain ⟨l, hl⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS _ hfac
  refine ⟨l, (BigFppfOver.toScheme B S hS).map_injective ?_, fun l' hl' ↦ ?_⟩
  · rw [Functor.map_comp, hl]
    exact IsOpenImmersion.lift_fac _ _ _
  · refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [hl]
    refine (cancel_mono ((BigFppfOver.toScheme B S hS).map n)).mp ?_
    rw [IsOpenImmersion.lift_fac, ← Functor.map_comp, hl']

/-- Let `U` be an object of the big fppf category over `S` whose underlying scheme is the coproduct
of the underlying schemes of a family `W` along morphisms `j i : W i ⟶ U`. Then every morphism to
`U` from an object `Z` with quasi-compact underlying scheme decomposes `Z` into finitely many open
subobjects with closed image, each of which maps to a single summand `W i` compatibly with the
given morphism. -/
theorem BigFppfOver.exists_finite_decomposition_of_hom_coproduct
    {U : BigFppfOver B S hS} {I : Type u} {W : I → BigFppfOver B S hS}
    (j : ∀ i, W i ⟶ U)
    (e : (∐ fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) ≅
      (BigFppfOver.toScheme B S hS).obj U)
    (he : ∀ i, Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) i ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (j i))
    (Z : BigFppfOver B S hS) [CompactSpace ((BigFppfOver.toScheme B S hS).obj Z)]
    (z : Z ⟶ U) :
    ∃ (σ : Type u) (_ : Finite σ) (k : σ → I) (Z' : σ → BigFppfOver B S hS)
      (p : ∀ a, Z' a ⟶ Z) (w : ∀ a, Z' a ⟶ W (k a)),
      (∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p a))) ∧
      (∀ a, IsClosed (Set.range ((BigFppfOver.toScheme B S hS).map (p a)))) ∧
      (∀ x : (BigFppfOver.toScheme B S hS).obj Z,
        ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p a))) ∧
      (Pairwise fun a b ↦ Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
        (Set.range ((BigFppfOver.toScheme B S hS).map (p b)))) ∧
      Nonempty (IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj Z)
        fun a ↦ (BigFppfOver.toScheme B S hS).map (p a))) ∧
      (∀ a, w a ≫ j (k a) = p a ≫ z) := by
  obtain ⟨s, hcov, hclosed⟩ := exists_finset_isClosed_preimage_opensRange_sigmaι
    (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i))
    ((BigFppfOver.toScheme B S hS).map z ≫ e.inv)
  choose Y f hfimm hfrange _hfuniv using fun i : I ↦ exists_restrict_bigFppfOver Z
    (((BigFppfOver.toScheme B S hS).map z ≫ e.inv) ⁻¹ᵁ
      (Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) i).opensRange)
  have hjimm : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)) := by
    intro i
    rw [← he i]
    infer_instance
  have hsub : ∀ i : I, Set.range ((BigFppfOver.toScheme B S hS).map (f i ≫ z)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (j i)) := by
    intro i
    rintro _ ⟨x, rfl⟩
    have hx : (BigFppfOver.toScheme B S hS).map (f i) x ∈
        ((((BigFppfOver.toScheme B S hS).map z ≫ e.inv) ⁻¹ᵁ
          (Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) i).opensRange :
            ((BigFppfOver.toScheme B S hS).obj Z).Opens) : Set _) := by
      rw [← hfrange i]
      exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    rw [← he i, Functor.map_comp, Scheme.Hom.comp_apply, hy]
    simp
  choose w hw using fun i : I ↦ (existsUnique_lift_aux (j i) (hjimm i) (f i ≫ z) (hsub i)).exists
  have hjoint : ∀ x : (BigFppfOver.toScheme B S hS).obj Z, ∃ a : {i : I // i ∈ s},
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (f a.1)) := by
    intro x
    obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hcov.ge (Set.mem_univ x))
    exact ⟨⟨i, his⟩, by rw [hfrange i]; exact hxi⟩
  have hpair : Pairwise fun a b : {i : I // i ∈ s} ↦
      Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (f a.1)))
        (Set.range ((BigFppfOver.toScheme B S hS).map (f b.1))) := by
    intro a b hab
    rw [hfrange a.1, hfrange b.1]
    exact Opens.coe_disjoint.mpr
      (disjoint_preimage_opensRange_sigmaι _ _ (fun h ↦ hab (Subtype.ext h)))
  refine ⟨{i : I // i ∈ s}, inferInstance, Subtype.val, fun a ↦ Y a.1, fun a ↦ f a.1,
    fun a ↦ w a.1, fun a ↦ hfimm a.1, fun a ↦ ?_, hjoint, hpair, ?_, fun a ↦ ?_⟩
  · rw [hfrange a.1]
    exact hclosed a.1 a.2
  · have : ∀ a : {i : I // i ∈ s},
        IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (f a.1)) := fun a ↦ hfimm a.1
    refine nonempty_isColimit_cofanMk_of _ ?_ ?_
    · refine TopologicalSpace.Opens.ext ?_
      rw [Opens.coe_iSup, Opens.coe_top, ← hcov]
      refine (Set.iUnion_subtype _ _).trans ?_
      simp only [Scheme.Hom.coe_opensRange, hfrange]
    · intro a b hab
      simp only [Function.onFun]
      rw [← Opens.coe_disjoint, Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange]
      exact hpair hab
  · exact hw a.1

/-- Let `U` be an object of the big fppf category over `S` whose underlying scheme is the
coproduct of the underlying schemes of a family `W` along morphisms `j i : W i ⟶ U`. Then every
morphism to `U` from an affine object `Z` decomposes `Z` into finitely many affine open
subobjects, pairwise disjoint and covering `Z`, each of which maps to a single summand `W i`
compatibly with the given morphism. -/
theorem BigFppfOver.exists_finite_affine_decomposition_of_hom_coproduct
    {U : BigFppfOver B S hS} {I : Type u} {W : I → BigFppfOver B S hS}
    (j : ∀ i, W i ⟶ U)
    (e : (∐ fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) ≅
      (BigFppfOver.toScheme B S hS).obj U)
    (he : ∀ i, Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) i ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (j i))
    (Z : BigFppfOver B S hS) (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (z : Z ⟶ U) :
    ∃ (σ : Type u) (_ : Finite σ) (k : σ → I) (Z' : σ → BigFppfOver B S hS)
      (p : ∀ a, Z' a ⟶ Z) (w : ∀ a, Z' a ⟶ W (k a)),
      (∀ a, IsAffine ((BigFppfOver.toScheme B S hS).obj (Z' a))) ∧
      (∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p a))) ∧
      (∀ x : (BigFppfOver.toScheme B S hS).obj Z,
        ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p a))) ∧
      (Pairwise fun a b ↦ Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
        (Set.range ((BigFppfOver.toScheme B S hS).map (p b)))) ∧
      Nonempty (IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj Z)
        fun a ↦ (BigFppfOver.toScheme B S hS).map (p a))) ∧
      (∀ a, w a ≫ j (k a) = p a ≫ z) := by
  obtain ⟨σ, hσ, k, Z', p, w, hpimm, hpclosed, hpcov, hpdisj, hpcolim, hpfac⟩ :=
    BigFppfOver.exists_finite_decomposition_of_hom_coproduct j e he Z z
  exact ⟨σ, hσ, k, Z', p, w, fun a ↦ isAffine_of_isOpenImmersion_of_isClosed_range
    ((BigFppfOver.toScheme B S hS).map (p a)) (hpclosed a), hpimm, hpcov, hpdisj, hpcolim, hpfac⟩

/-- If an object `Z` of the big fppf category over `S` is covered by the images of pairwise
disjoint open immersions `p a` from objects `Z' a` of the site, then any family of sections of a
sheaf over the `Z' a` has a unique amalgamation over `Z`. -/
theorem BigFppfOver.existsUnique_section_of_disjoint_openCover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    {Z : BigFppfOver B S hS} {σ : Type v} {Z' : σ → BigFppfOver B S hS} (p : ∀ a, Z' a ⟶ Z)
    (hp : ∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p a)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
    (hdisj : Pairwise fun a b ↦ Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
      (Set.range ((BigFppfOver.toScheme B S hS).map (p b))))
    (x : ∀ a, F.obj (Opposite.op (Z' a))) :
    ∃! t : F.obj (Opposite.op Z), ∀ a, F.map (p a).op t = x a := by
  have hsheaf : (Presieve.ofArrows Z' p).IsSheafFor F :=
    hF.isSheafFor _ (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS p hp hcov)
  rw [Presieve.isSheafFor_arrows_iff] at hsheaf
  refine hsheaf x fun a b V ga gb hg ↦ ?_
  have hmap := congrArg (BigFppfOver.toScheme B S hS).map hg
  rw [Functor.map_comp, Functor.map_comp] at hmap
  by_cases hab : a = b
  · subst hab
    rw [(BigFppfOver.toScheme B S hS).map_injective
      ((cancel_mono ((BigFppfOver.toScheme B S hS).map (p a))).mp hmap)]
  · have hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj V) := by
      refine ⟨fun v ↦ ?_⟩
      have hv : (BigFppfOver.toScheme B S hS).map (p a)
            ((BigFppfOver.toScheme B S hS).map ga v) =
          (BigFppfOver.toScheme B S hS).map (p b)
            ((BigFppfOver.toScheme B S hS).map gb v) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hmap]
      exact Set.disjoint_left.mp (hdisj hab) ⟨_, rfl⟩ ⟨_, hv.symm⟩
    have := CategoryTheory.Presieve.IsSheaf.subsingleton_obj_of_bot_mem _ hF
      (BigFppfOver.bot_mem_topology V hempty)
    exact Subsingleton.elim _ _

end Site

end AlgebraicGeometry

namespace CategoryTheory

/-- A commuting square of presheaves of types is a pullback square as soon as, over every
object, a compatible pair of sections of the two lower corners is the image of exactly one
section of the upper left corner. -/
theorem isPullback_of_existsUnique_app {C : Type w} [Category.{v} C]
    {X₁ X₂ X₃ X₄ : Cᵒᵖ ⥤ Type u}
    {t : X₁ ⟶ X₂} {r : X₂ ⟶ X₄} {l : X₁ ⟶ X₃} {b : X₃ ⟶ X₄}
    (w : t ≫ r = l ≫ b)
    (h : ∀ (V : Cᵒᵖ) (x₂ : X₂.obj V) (x₃ : X₃.obj V), r.app V x₂ = b.app V x₃ →
      ∃! x₁ : X₁.obj V, t.app V x₁ = x₂ ∧ l.app V x₁ = x₃) :
    IsPullback t l r b := by
  have happ : ∀ V, IsIso ((Limits.pullback.lift t l w).app V) := by
    intro V
    have hpb : IsPullback ((Limits.pullback.fst r b).app V) ((Limits.pullback.snd r b).app V)
        (r.app V) (b.app V) :=
      (IsPullback.of_hasPullback r b).map ((evaluation Cᵒᵖ (Type u)).obj V)
    have hfst : ∀ x, (Limits.pullback.fst r b).app V
        ((Limits.pullback.lift t l w).app V x) = t.app V x := fun x ↦ by
      rw [← types_comp_apply ((Limits.pullback.lift t l w).app V), ← NatTrans.comp_app,
        Limits.pullback.lift_fst]
    have hsnd : ∀ x, (Limits.pullback.snd r b).app V
        ((Limits.pullback.lift t l w).app V x) = l.app V x := fun x ↦ by
      rw [← types_comp_apply ((Limits.pullback.lift t l w).app V), ← NatTrans.comp_app,
        Limits.pullback.lift_snd]
    rw [isIso_iff_bijective]
    refine ⟨fun x y hxy ↦ ?_, fun p ↦ ?_⟩
    · refine (h V (t.app V x) (l.app V x)
        (congrFun (congrArg (fun m ↦ m.app V) w) x)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
      · rw [← hfst x, ← hfst y, hxy]
      · rw [← hsnd x, ← hsnd y, hxy]
    · obtain ⟨x, ⟨hx₁, hx₂⟩, -⟩ := h V ((Limits.pullback.fst r b).app V p)
        ((Limits.pullback.snd r b).app V p)
        (congrFun (congrArg (fun m ↦ m.app V)
          (Limits.pullback.condition (f := r) (g := b))) p)
      exact ⟨x, Limits.Types.ext_of_isPullback hpb ((hfst x).trans hx₁) ((hsnd x).trans hx₂)⟩
  have : IsIso (Limits.pullback.lift t l w) := NatIso.isIso_of_isIso_app _
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso (Limits.pullback.lift t l w))
    (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)

end CategoryTheory

namespace AlgebraicGeometry

section Site2

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the big fppf category over `S` whose image lies in the image of an open
immersion of the site factors uniquely through that open immersion. -/
theorem BigFppfOver.existsUnique_lift_of_isOpenImmersion
    {M N Z : BigFppfOver B S hS} (n : N ⟶ Z)
    (hn : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map n)) (m : M ⟶ Z)
    (hm : Set.range ((BigFppfOver.toScheme B S hS).map m) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map n)) :
    ∃! l : M ⟶ N, l ≫ n = m :=
  existsUnique_lift_aux n hn m hm

/-- Pulling a disjoint open covering of an object of the big fppf category over `S` back along
an arbitrary morphism gives a disjoint open covering of the source, together with the induced
morphisms to the members of the given covering. -/
theorem BigFppfOver.exists_disjoint_openCover_pullback
    {Z V : BigFppfOver B S hS} {σ : Type v} {Z' : σ → BigFppfOver B S hS} (ι : ∀ a, Z' a ⟶ Z)
    (hιimm : ∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ι a)))
    (hιcov : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι a)))
    (hιdisj : Pairwise fun a b ↦
      Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (ι a)))
        (Set.range ((BigFppfOver.toScheme B S hS).map (ι b))))
    (v : V ⟶ Z) :
    ∃ (V' : σ → BigFppfOver B S hS) (p : ∀ a, V' a ⟶ V) (v' : ∀ a, V' a ⟶ Z' a),
      (∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p a))) ∧
      (∀ a, Set.range ((BigFppfOver.toScheme B S hS).map (p a)) =
        (BigFppfOver.toScheme B S hS).map v ⁻¹'
          Set.range ((BigFppfOver.toScheme B S hS).map (ι a))) ∧
      (∀ x : (BigFppfOver.toScheme B S hS).obj V,
        ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p a))) ∧
      (Pairwise fun a b ↦ Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
        (Set.range ((BigFppfOver.toScheme B S hS).map (p b)))) ∧
      (∀ a, v' a ≫ ι a = p a ≫ v) := by
  choose V' p hpimm hprange _hpuniv using fun a : σ ↦ exists_restrict_bigFppfOver V
    ((BigFppfOver.toScheme B S hS).map v ⁻¹ᵁ
      ((BigFppfOver.toScheme B S hS).map (ι a)).opensRange)
  have hrange : ∀ a, Set.range ((BigFppfOver.toScheme B S hS).map (p a)) =
      (BigFppfOver.toScheme B S hS).map v ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map (ι a)) := hprange
  have hsub : ∀ a, Set.range ((BigFppfOver.toScheme B S hS).map (p a ≫ v)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (ι a)) := by
    rintro a _ ⟨x, rfl⟩
    have hx : (BigFppfOver.toScheme B S hS).map (p a) x ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (p a)) := ⟨x, rfl⟩
    rw [hrange a] at hx
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hx
  choose v' hv' _ using fun a : σ ↦ BigFppfOver.existsUnique_lift_of_isOpenImmersion
    (ι a) (hιimm a) (p a ≫ v) (hsub a)
  refine ⟨V', p, v', hpimm, hrange, fun x ↦ ?_, fun a b hab ↦ ?_, hv'⟩
  · obtain ⟨a, ha⟩ := hιcov ((BigFppfOver.toScheme B S hS).map v x)
    exact ⟨a, by rw [hrange a]; exact ha⟩
  · show Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
      (Set.range ((BigFppfOver.toScheme B S hS).map (p b)))
    rw [hrange a, hrange b]
    exact Disjoint.preimage _ (hιdisj hab)

/-- A representable presheaf on the big fppf category over `S` is a sheaf of types. -/
theorem BigFppfOver.isSheaf_of_type_yoneda_obj (a : BigFppfOver B S hS) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj a) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- Two sections of a sheaf on the big fppf category over `S` which agree on the members of a
disjoint open covering are equal. -/
theorem BigFppfOver.section_ext_of_disjoint_openCover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    {Z : BigFppfOver B S hS} {σ : Type v} {Z' : σ → BigFppfOver B S hS} (p : ∀ a, Z' a ⟶ Z)
    (hp : ∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p a)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
    (hdisj : Pairwise fun a b ↦ Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
      (Set.range ((BigFppfOver.toScheme B S hS).map (p b))))
    {t t' : F.obj (Opposite.op Z)}
    (h : ∀ a, F.map (p a).op t = F.map (p a).op t') : t = t' :=
  (BigFppfOver.existsUnique_section_of_disjoint_openCover hF p hp hcov hdisj
    fun a ↦ F.map (p a).op t).unique (fun _ ↦ rfl) fun a ↦ (h a).symm

/-- Two morphisms from a representable presheaf on the big fppf category over `S` to a sheaf
which agree after restriction along the members of a disjoint open covering of the representing
object are equal. -/
theorem BigFppfOver.hom_ext_of_disjoint_openCover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    {Z : BigFppfOver B S hS} {σ : Type v} {Z' : σ → BigFppfOver B S hS} (p : ∀ a, Z' a ⟶ Z)
    (hp : ∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p a)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
    (hdisj : Pairwise fun a b ↦ Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
      (Set.range ((BigFppfOver.toScheme B S hS).map (p b))))
    {α β : yoneda.obj Z ⟶ F} (h : ∀ a, yoneda.map (p a) ≫ α = yoneda.map (p a) ≫ β) :
    α = β := by
  refine yonedaEquiv.injective
    (BigFppfOver.section_ext_of_disjoint_openCover hF p hp hcov hdisj fun a ↦ ?_)
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality, h a]

/-- If a disjoint open covering `κ` of `T` lies over a disjoint open covering `ι` of `Z` along a
morphism `P`, index by index, then the image of `κ a` is exactly the preimage along `P` of the
image of `ι a`. -/
theorem BigFppfOver.range_eq_preimage_range_of_disjoint_openCover
    {Z T : BigFppfOver B S hS} {σ : Type v} {Z' T' : σ → BigFppfOver B S hS}
    {ι : ∀ a, Z' a ⟶ Z} {κ : ∀ a, T' a ⟶ T} {q : ∀ a, T' a ⟶ Z' a} {P : T ⟶ Z}
    (hιdisj : Pairwise fun a b ↦ Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (ι a)))
      (Set.range ((BigFppfOver.toScheme B S hS).map (ι b))))
    (hκcov : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (κ a)))
    (hP : ∀ a, κ a ≫ P = q a ≫ ι a) (a : σ) :
    Set.range ((BigFppfOver.toScheme B S hS).map (κ a)) =
      (BigFppfOver.toScheme B S hS).map P ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map (ι a)) := by
  have hle : ∀ b : σ, Set.range ((BigFppfOver.toScheme B S hS).map (κ b)) ⊆
      (BigFppfOver.toScheme B S hS).map P ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map (ι b)) := by
    rintro b _ ⟨x, rfl⟩
    refine ⟨(BigFppfOver.toScheme B S hS).map (q b) x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, hP b]
  refine le_antisymm (hle a) fun y hy ↦ ?_
  obtain ⟨b, hb⟩ := hκcov y
  by_cases hab : b = a
  · exact hab ▸ hb
  · exact ((Set.disjoint_left.mp (hιdisj hab) (hle b hb)) hy).elim

/-- Let `f : X ⟶ Y` be a morphism of sheaves on the big fppf category over `S`, let
`h : yoneda.obj Z ⟶ Y` be a morphism from a representable sheaf, let `ι` be a disjoint open
covering of `Z` and let `κ` be a disjoint open covering of `T` lying over `ι` along
`P : T ⟶ Z`, index by index. If over each member of the covering of `Z` the corresponding
member of the covering of `T` represents the base change of `f`, compatibly with a morphism
`R : yoneda.obj T ⟶ X`, then `T` represents the base change of `f` along `h`. -/
theorem isPullback_of_disjoint_openCover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y)
    {f : X ⟶ Y} {Z T : BigFppfOver B S hS} {h : yoneda.obj Z ⟶ Y} {P : T ⟶ Z}
    {σ : Type v} {Z' T' : σ → BigFppfOver B S hS}
    {ι : ∀ a, Z' a ⟶ Z} {κ : ∀ a, T' a ⟶ T} {q : ∀ a, T' a ⟶ Z' a}
    (hιimm : ∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ι a)))
    (hιcov : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι a)))
    (hιdisj : Pairwise fun a b ↦ Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (ι a)))
      (Set.range ((BigFppfOver.toScheme B S hS).map (ι b))))
    (hκimm : ∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (κ a)))
    (hκcov : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ a, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (κ a)))
    (hκdisj : Pairwise fun a b ↦ Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (κ a)))
      (Set.range ((BigFppfOver.toScheme B S hS).map (κ b))))
    (hP : ∀ a, κ a ≫ P = q a ≫ ι a)
    {r : ∀ a, yoneda.obj (T' a) ⟶ X}
    (hr : ∀ a, IsPullback (r a) (yoneda.map (q a)) f (yoneda.map (ι a) ≫ h))
    {R : yoneda.obj T ⟶ X} (hR : ∀ a, yoneda.map (κ a) ≫ R = r a) :
    IsPullback R (yoneda.map P) f h := by
  have hιmono : ∀ a, Mono (ι a) := fun a ↦
    (BigFppfOver.toScheme B S hS).mono_of_mono_map
      (inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map (ι a))))
  have hκrange := BigFppfOver.range_eq_preimage_range_of_disjoint_openCover
    (ι := ι) (κ := κ) (q := q) (P := P) hιdisj hκcov hP
  have hw : R ≫ f = yoneda.map P ≫ h := by
    refine BigFppfOver.hom_ext_of_disjoint_openCover hY κ hκimm hκcov hκdisj fun a ↦ ?_
    rw [← Category.assoc, hR a, (hr a).w, ← Category.assoc, ← Functor.map_comp, ← hP a,
      Functor.map_comp, Category.assoc]
  refine isPullback_of_existsUnique_app hw ?_
  rintro ⟨V⟩ ξ v hfv
  obtain ⟨V', p, v', hpimm, hprange, hpcov, hpdisj, hv'⟩ :=
    BigFppfOver.exists_disjoint_openCover_pullback ι hιimm hιcov hιdisj v
  have hcompat : ∀ a, (f.app (Opposite.op (V' a))) (X.map (p a).op ξ) =
      ((yoneda.map (ι a) ≫ h).app (Opposite.op (V' a))) (v' a) := by
    intro a
    rw [NatTrans.naturality_apply f (p a).op ξ, hfv,
      ← NatTrans.naturality_apply h (p a).op v]
    show (h.app (Opposite.op (V' a))) (p a ≫ v) = (h.app (Opposite.op (V' a))) (v' a ≫ ι a)
    rw [hv' a]
  have hpb : ∀ a, IsPullback ((r a).app (Opposite.op (V' a)))
      ((yoneda.map (q a)).app (Opposite.op (V' a))) (f.app (Opposite.op (V' a)))
      ((yoneda.map (ι a) ≫ h).app (Opposite.op (V' a))) := fun a ↦
    (hr a).map ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj (Opposite.op (V' a)))
  choose t ht₁ ht₂ using fun a ↦ Limits.Types.exists_of_isPullback (hpb a)
    (X.map (p a).op ξ) (v' a) (hcompat a)
  have ht₂' : ∀ a, t a ≫ q a = v' a := ht₂
  have key : ∀ τ : V ⟶ T, R.app (Opposite.op V) τ = ξ → τ ≫ P = v →
      ∀ a, p a ≫ τ = t a ≫ κ a := by
    intro τ hτ₁ hτ₂ a
    have hsub : Set.range ((BigFppfOver.toScheme B S hS).map (p a ≫ τ)) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map (κ a)) := by
      rintro _ ⟨x, rfl⟩
      rw [hκrange a]
      refine ⟨(BigFppfOver.toScheme B S hS).map (v' a) x, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Scheme.Hom.comp_apply,
        ← Functor.map_comp, Category.assoc, hτ₂, ← hv' a]
    obtain ⟨ρ, hρ, -⟩ := BigFppfOver.existsUnique_lift_of_isOpenImmersion (κ a) (hκimm a)
      (p a ≫ τ) hsub
    have hρ₁ : (r a).app (Opposite.op (V' a)) ρ = X.map (p a).op ξ := by
      rw [← hR a]
      show R.app (Opposite.op (V' a)) (ρ ≫ κ a) = _
      rw [hρ]
      show R.app (Opposite.op (V' a)) ((yoneda.obj T).map (p a).op τ) = _
      rw [NatTrans.naturality_apply R (p a).op τ, hτ₁]
    have hρ₂ : (yoneda.map (q a)).app (Opposite.op (V' a)) ρ = v' a := by
      show ρ ≫ q a = v' a
      refine (cancel_mono (ι a)).mp ?_
      rw [Category.assoc, ← hP a, ← Category.assoc, hρ, Category.assoc, hτ₂, ← hv' a]
    have hρt : ρ = t a :=
      Limits.Types.ext_of_isPullback (hpb a) (hρ₁.trans (ht₁ a).symm)
        (hρ₂.trans (ht₂' a).symm)
    rw [← hρ, hρt]
  obtain ⟨τ, hτ, -⟩ := BigFppfOver.existsUnique_section_of_disjoint_openCover
    (BigFppfOver.isSheaf_of_type_yoneda_obj T) p hpimm hpcov hpdisj fun a ↦ t a ≫ κ a
  have hτ' : ∀ a, p a ≫ τ = t a ≫ κ a := hτ
  have hτ₁ : R.app (Opposite.op V) τ = ξ := by
    refine BigFppfOver.section_ext_of_disjoint_openCover hX p hpimm hpcov hpdisj fun a ↦ ?_
    rw [← NatTrans.naturality_apply R (p a).op τ]
    show R.app (Opposite.op (V' a)) (p a ≫ τ) = _
    rw [hτ' a]
    have heq := ht₁ a
    rw [← hR a] at heq
    exact heq
  have hτ₂ : τ ≫ P = v := by
    refine BigFppfOver.section_ext_of_disjoint_openCover
      (BigFppfOver.isSheaf_of_type_yoneda_obj Z) p hpimm hpcov hpdisj fun a ↦ ?_
    show p a ≫ τ ≫ P = p a ≫ v
    rw [← Category.assoc, hτ' a, Category.assoc, hP a, ← Category.assoc, ht₂' a, hv' a]
  refine ⟨τ, ⟨hτ₁, hτ₂⟩, fun τ' hτ' ↦ ?_⟩
  refine BigFppfOver.section_ext_of_disjoint_openCover
    (BigFppfOver.isSheaf_of_type_yoneda_obj T) p hpimm hpcov hpdisj fun a ↦ ?_
  show p a ≫ τ' = p a ≫ τ
  rw [key τ' hτ'.1 hτ'.2 a, key τ hτ₁ hτ₂ a]

/-- Let `f : X ⟶ Y` be a morphism of sheaves on the big fppf category over `S` and let
`g : yoneda.obj U ⟶ Y` be a chart whose source is a disjoint union of the affine objects `W i`. If
the base change of `f` along each `yoneda.map (j i) ≫ g` is represented by an affine object of the
site, then the base change of `f` along `g` is an affine morphism of algebraic spaces in the sense
of Stacks 03WF. -/
theorem Space.isAffineHom_pullback_snd_of_coproduct_affine_atlas
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y)
    {f : X ⟶ Y} {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    {I : Type u} {W : I → BigFppfOver B S hS} {j : ∀ i, W i ⟶ U}
    (e : (∐ fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) ≅
      (BigFppfOver.toScheme B S hS).obj U)
    (he : ∀ i, Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) i ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (j i))
    (hWaff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (W i)))
    (hW : ∀ i, ∃ (V : BigFppfOver B S hS) (q : V ⟶ W i) (r : yoneda.obj V ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        IsPullback r (yoneda.map q) f (yoneda.map (j i) ≫ g)) :
    Space.IsAffineHom B S hS (Limits.pullback.snd f g) := by
  intro Z₀ g'
  obtain ⟨z, rfl⟩ := yoneda.map_surjective g'
  obtain ⟨σ, hσ, k, Z', p, w, hZ'aff, hpimm, hpcov, hpdisj, -, hpw⟩ :=
    BigFppfOver.exists_finite_affine_decomposition_of_hom_coproduct j e he
      ((BigAffineFppf.inclusion B S hS).obj Z₀) Z₀.property z
  have hbc : ∀ a, ∃ (V : BigFppfOver B S hS) (q : V ⟶ Z' a) (r : yoneda.obj V ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        IsPullback r (yoneda.map q) f (yoneda.map (p a) ≫ (yoneda.map z ≫ g)) := by
    intro a
    obtain ⟨Vk, qk, rk, hVkaff, hsq⟩ := hW (k a)
    have hqk : _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B S hS).map qk) :=
      isAffineHom_of_isAffine _
    refine ⟨Limits.pullback qk (w a), Limits.pullback.snd qk (w a),
      yoneda.map (Limits.pullback.fst qk (w a)) ≫ rk, ?_, ?_⟩
    · exact IsAffine.of_isIso
        (Limits.PreservesPullback.iso (BigFppfOver.toScheme B S hS) qk (w a)).hom
    · have hsq1 : IsPullback (yoneda.map (Limits.pullback.fst qk (w a)))
          (yoneda.map (Limits.pullback.snd qk (w a))) (yoneda.map qk) (yoneda.map (w a)) :=
        (IsPullback.of_hasPullback qk (w a)).map yoneda
      have hbot : yoneda.map (w a) ≫ (yoneda.map (j (k a)) ≫ g) =
          yoneda.map (p a) ≫ (yoneda.map z ≫ g) := by
        rw [← Category.assoc, ← Functor.map_comp, hpw a, Functor.map_comp, Category.assoc]
      exact hbot ▸ hsq1.paste_horiz hsq
  choose T' q' r' hT'aff hT'sq using hbc
  obtain ⟨T, κ, e', he', hdesc⟩ := BigFppfOver.exists_coproduct_of_mk_le_aleph0
    (Cardinal.mk_le_aleph0 (α := σ)) T'
  obtain ⟨hκimm, hκcov, hκdisj⟩ := isOpenImmersion_cover_disjoint_of_iso_sigma e' he'
  have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso e'.inv
  obtain ⟨P, hP⟩ := hdesc fun a ↦ q' a ≫ p a
  obtain ⟨R₀, hR₀, -⟩ := BigFppfOver.existsUnique_section_of_disjoint_openCover hX κ hκimm
    hκcov hκdisj fun a ↦ yonedaEquiv (r' a)
  have hR : ∀ a, yoneda.map (κ a) ≫ yonedaEquiv.symm R₀ = r' a := fun a ↦
    yonedaEquiv.injective (by rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, hR₀ a])
  have hfinal : IsPullback (yonedaEquiv.symm R₀) (yoneda.map P) f (yoneda.map z ≫ g) :=
    isPullback_of_disjoint_openCover hX hY hpimm hpcov hpdisj hκimm hκcov hκdisj hP hT'sq hR
  exact ⟨⟨T, hTaff⟩, _, P, IsPullback.of_right' hfinal (IsPullback.of_hasPullback f g)⟩

/-- If the base change of a morphism of algebraic spaces over `S` along every étale morphism from
an affine object of the site is represented by an affine object, then there is a surjective
étale chart of the target over which the base change is an affine morphism of algebraic spaces.
This is the implication (3) ⇒ (4) of Stacks 03WG. -/
theorem Space.exists_etaleChart_isAffineHom_of_isEtale_affine
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (h₃ : ∀ (V : BigAffineFppf B S hS)
      (c : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ Y),
      Space.IsEtale B S hS c →
        ∃ (V' : BigAffineFppf B S hS)
          (a : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V') ⟶ X)
          (b : (BigAffineFppf.inclusion B S hS).obj V' ⟶
            (BigAffineFppf.inclusion B S hS).obj V),
          IsPullback a (yoneda.map b) f c) :
    ∃ (V : BigFppfOver B S hS) (c : yoneda.obj V ⟶ Y),
      Space.IsSurjective B S hS c ∧ Space.IsEtale B S hS c ∧
        Space.IsAffineHom B S hS (Limits.pullback.snd f c) := by
  obtain ⟨U, gc, I, W, j, e, hgcS, hgcE, hWaff, hje, -, hjetale, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS Y hY
  refine ⟨U, gc, Space.isSurjective_of_presheafSurjective B S hS gc hgcS,
    Space.isEtale_of_presheaf_etale B S hS hgcE, ?_⟩
  refine Space.isAffineHom_pullback_snd_of_coproduct_affine_atlas
    ((isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf)
    ((isSheaf_iff_isSheaf_of_type _ _).1 hY.isSheaf) e hje hWaff fun i ↦ ?_
  obtain ⟨V', a, b, hsq⟩ := h₃ ⟨W i, hWaff i⟩ (yoneda.map (j i) ≫ gc)
    (Space.isEtale_of_presheaf_etale B S hS (hjetale i))
  exact ⟨(BigAffineFppf.inclusion B S hS).obj V', b, a, V'.property, hsq⟩

end Site2

end AlgebraicGeometry

end


