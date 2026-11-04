module

public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.ClosedUnion

/-!
# Gluing invertible modules along a scheme-theoretic closed cover

`StacksTag09NE.exists_invertible_of_closed_cover_discrete_intersections` glues invertible
modules along a finite closed cover of a **reduced** scheme whose members meet pairwise in
discrete spaces. Reducedness enters that proof in exactly one way: through Mathlib's
`AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective`, a surjective closed immersion into
a reduced target being an isomorphism, and it is used only to see that a member of the cover
*fills out* the open set it surjects onto.

This file replaces that use by the hypothesis

  `⨅ i, (f i).ker = ⊥`,

i.e. that the cover is a cover **scheme-theoretically** and not merely set-theoretically. The
lever is Mathlib's `AlgebraicGeometry.IsClosedImmersion.isIso_iff_ker_eq_bot`, which is the
reducedness-free half of `isIso_of_isClosedImmersion_of_surjective`: over an affine open `W`
contained in the image of the member `f i`, every *other* member has empty preimage, so its
kernel ideal is the unit ideal there and the intersection collapses to `(f i).ker.ideal W`,
which is therefore `⊥`.

For a reduced `X` the hypothesis is automatic — `Stacks.IdealSheafData.support_inf` makes the
support of the intersection the union of the images, which is all of `X`, and
`AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff` then forces `⊥` — so the statements
here subsume the reduced ones.

## Main results

* `Stacks.IdealSheafData.ker_ideal_eq_top_of_preimage_eq_bot`: a morphism whose preimage of an
  affine open is empty has unit kernel ideal there.
* `Stacks.IdealSheafData.ker_ideal_eq_bot_of_iInf_ker_eq_bot`: the collapse of the intersection
  described above.
* `Stacks.IdealSheafData.iInf_ker_morphismRestrict_eq_bot`: the hypothesis restricts to an open.
* `Stacks.IdealSheafData.eq_of_map_subschemeι_eq`: pushforward along `subschemeι` is injective
  on ideal sheaves, which is how the hypothesis is *verified* on a scheme-theoretic union.
* `Stacks.ClosedCoverKer.isOpenImmersion_of_isClosedImmersion_of_ker_ideal_eq_bot`: the
  replacement for `isIso_of_isClosedImmersion_of_surjective`.

## References

* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Set TopologicalSpace Topology

universe v u

namespace Stacks.IdealSheafData

open AlgebraicGeometry.Scheme.IdealSheafData

/-- **A morphism missing an affine open entirely has unit kernel ideal there.** If
`f ⁻¹ᵁ W = ⊥` then `f ∣_ W` has empty source, so its kernel is `⊤`; transporting along
`AlgebraicGeometry.Scheme.ker_morphismRestrict_ideal` gives the statement for `f` itself. -/
theorem ker_ideal_eq_top_of_preimage_eq_bot {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]
    (W : X.affineOpens) (hW : f ⁻¹ᵁ W.1 = ⊥) : (Scheme.Hom.ker f).ideal W = ⊤ := by
  have hempty : IsEmpty ↥(f ⁻¹ᵁ W.1) := Set.isEmpty_coe_sort.mpr (by rw [hW]; rfl)
  have _ : IsAffine W.1.toScheme := W.2
  have hker : (Scheme.Hom.ker (f ∣_ W.1)) = ⊤ := @Scheme.ker_eq_top_of_isEmpty _ _ _ hempty
  have key := Scheme.ker_morphismRestrict_ideal f W.1 ⟨⊤, isAffineOpen_top _⟩
  rw [hker] at key
  have haff : IsAffineOpen (W.1.ι ''ᵁ (⊤ : W.1.toScheme.Opens)) :=
    (isAffineOpen_top W.1.toScheme).image_of_isOpenImmersion W.1.ι
  have key2 : (Scheme.Hom.ker f).ideal ⟨W.1.ι ''ᵁ (⊤ : W.1.toScheme.Opens), haff⟩ = ⊤ := key.symm
  have hWeq : (⟨W.1.ι ''ᵁ (⊤ : W.1.toScheme.Opens), haff⟩ : X.affineOpens) = W :=
    Subtype.ext (by simp)
  exact hWeq ▸ key2

/-- **The intersection of the kernels collapses to one member over an affine open the others
miss.** This is the reducedness-free content of a closed cover being a cover
scheme-theoretically: where only the member `i` is present, `(f i).ker` must already be the whole
intersection, hence `⊥`. -/
theorem ker_ideal_eq_bot_of_iInf_ker_eq_bot {ι : Type v} [Finite ι] {X : Scheme.{u}}
    {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ X) [∀ i, QuasiCompact (f i)]
    (hker : (⨅ i, Scheme.Hom.ker (f i)) = ⊥) (i : ι) (W : X.affineOpens)
    (hW : ∀ j, j ≠ i → f j ⁻¹ᵁ W.1 = ⊥) : (Scheme.Hom.ker (f i)).ideal W = ⊥ := by
  have h1 : (⨅ j, (Scheme.Hom.ker (f j)).ideal W) = ⊥ := by
    simpa only [ideal_iInf, iInf_apply, ideal_bot, Pi.bot_apply] using
      congrArg (fun K : X.IdealSheafData ↦ K.ideal W) hker
  have h2 : (⨅ j, (Scheme.Hom.ker (f j)).ideal W) = (Scheme.Hom.ker (f i)).ideal W := by
    refine le_antisymm (iInf_le _ i) (le_iInf fun j ↦ ?_)
    rcases eq_or_ne j i with rfl | hj
    · exact le_rfl
    · exact le_top.trans_eq (ker_ideal_eq_top_of_preimage_eq_bot _ W (hW j hj)).symm
  rw [← h2, h1]

/-- **The scheme-theoretic cover hypothesis restricts to any open.** Both sides are read off
`AlgebraicGeometry.Scheme.ker_morphismRestrict_ideal` affine open by affine open. -/
theorem iInf_ker_morphismRestrict_eq_bot {ι : Type v} [Finite ι] {X : Scheme.{u}}
    {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ X) [∀ i, QuasiCompact (f i)] (U : X.Opens)
    (hker : (⨅ i, Scheme.Hom.ker (f i)) = ⊥) :
    (⨅ i, Scheme.Hom.ker (f i ∣_ U)) = ⊥ := by
  refine Scheme.IdealSheafData.ext (funext fun V ↦ ?_)
  have h := congrArg (fun K : X.IdealSheafData ↦
    K.ideal ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion _⟩) hker
  simp only [ideal_iInf, iInf_apply, ideal_bot, Pi.bot_apply] at h ⊢
  simpa only [Scheme.ker_morphismRestrict_ideal] using! h

/-- **Pushforward along the inclusion of a closed subscheme is injective on ideal sheaves.**
Ideal sheaves on `I.subscheme` are exactly the ideal sheaves on `X` above `I`; this is the
injectivity half of that correspondence, in the only form needed below. The proof is local:
`I.subschemeι.app` is surjective on every affine open of `X`
(`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_surjective`), so `Ideal.comap` along it
is injective, and the preimages of the affine opens of `X` cover `I.subscheme`.

Mathlib has the Galois connection `AlgebraicGeometry.Scheme.IdealSheafData.map_gc` but not this
injectivity. -/
theorem eq_of_map_subschemeι_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    {K K' : I.subscheme.IdealSheafData} (h : K.map I.subschemeι = K'.map I.subschemeι) :
    K = K' := by
  refine ext_of_iSup_eq_top (ι := X.affineOpens)
    (fun U ↦ ⟨I.subschemeι ⁻¹ᵁ U.1, U.2.preimage I.subschemeι⟩) ?_ ?_
  · refine le_antisymm le_top fun x _ ↦ ?_
    have hx : I.subschemeι x ∈ (⨆ U : X.affineOpens, U.1) :=
      (iSup_affineOpens_eq_top X) ▸ trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hU⟩
  · intro U
    have hc := congrArg (fun J : X.IdealSheafData ↦ J.ideal U) h
    simp only [ideal_map_of_isAffineHom] at hc
    exact Ideal.comap_injective_of_surjective _ (I.subschemeι_app_surjective U) hc

/-- **For a reduced scheme a set-theoretic cover is automatically a scheme-theoretic one.** The
intersection of the kernels is below each of them, so its support contains every image and hence
all of `X`; on a reduced scheme an ideal sheaf with full support is `⊥`
(`AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff`).

This is what makes the statements of `Stacks.ClosedCoverKer` *subsume* their reduced
counterparts rather than merely parallel them: reducedness is not traded for an extra
hypothesis, it is traded for a consequence of itself. -/
theorem iInf_ker_eq_bot_of_isReduced {ι : Type v} [Finite ι] {X : Scheme.{u}} [IsReduced X]
    {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ X) [∀ i, QuasiCompact (f i)]
    (hcover : ∀ x : X, ∃ i z, f i z = x) : (⨅ i, Scheme.Hom.ker (f i)) = ⊥ := by
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  refine le_antisymm le_top fun x _ ↦ ?_
  obtain ⟨i, z, rfl⟩ := hcover x
  exact Scheme.IdealSheafData.support_antitone (iInf_le _ i)
    (Scheme.Hom.range_subset_ker_support (f i) ⟨z, rfl⟩)

end Stacks.IdealSheafData

namespace Stacks.ClosedCoverKer

open AlgebraicGeometry.Scheme.IdealSheafData
open CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.IdealSheafData

/-- **The coproduct inclusion followed by `Sigma.desc` is the original map, pointwise.** -/
private theorem sigmaDesc_apply_sigmaι {ι : Type v} [Finite ι] {X : Scheme.{u}}
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) (i : ι) (z : Z i) :
    Limits.Sigma.desc f (Limits.Sigma.ι Z i z) = f i z := by
  rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc]

/-- **The replacement for `isIso_of_isClosedImmersion_of_surjective`.** A closed immersion with
open range is an open immersion as soon as its kernel ideal vanishes on the affine opens inside
that range — no reducedness of the target.

Mathlib's lemma for a reduced target factors as
`AlgebraicGeometry.IsClosedImmersion.isIso_iff_ker_eq_bot` followed by
`AlgebraicGeometry.Scheme.Hom.support_ker` and
`AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff`, the last of which is where
reducedness sits. Here the kernel hypothesis is supplied directly, so only
`isIso_iff_ker_eq_bot` is used. -/
theorem isOpenImmersion_of_isClosedImmersion_of_ker_ideal_eq_bot {Y X : Scheme.{u}}
    (g : Y ⟶ X) [IsClosedImmersion g] (hopen : IsOpen (Set.range ⇑g))
    (hker : ∀ W : X.affineOpens, (W : Set X) ⊆ Set.range ⇑g →
      (Scheme.Hom.ker g).ideal W = ⊥) :
    IsOpenImmersion g := by
  let U : X.Opens := ⟨Set.range ⇑g, hopen⟩
  have hpre : g ⁻¹ᵁ U = ⊤ := le_antisymm le_top fun y _ ↦ Set.mem_range_self y
  have hkerU : Scheme.Hom.ker (g ∣_ U) = ⊥ := by
    refine Scheme.IdealSheafData.ext (funext fun V ↦ ?_)
    have hsub : ((U.ι ''ᵁ V.1 : X.Opens) : Set X) ⊆ Set.range ⇑g := by
      rintro x ⟨y, -, rfl⟩
      exact y.2
    have h := hker ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion _⟩ hsub
    simp only [ideal_bot, Pi.bot_apply]
    simpa only [Scheme.ker_morphismRestrict_ideal] using! h
  have hiso : IsIso (g ∣_ U) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hkerU
  have hιiso : IsIso ((g ⁻¹ᵁ U).ι) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y ↦ ⟨⟨y, ?_⟩, rfl⟩⟩⟩
    rw [hpre]
    trivial
  have hg : g = inv ((g ⁻¹ᵁ U).ι) ≫ (g ∣_ U) ≫ U.ι := by
    rw [morphismRestrict_ι]
    simp
  rw [hg]
  infer_instance

/-- **A finite family of closed immersions with disjoint images covering `X` is a coproduct
presentation**, under the scheme-theoretic cover hypothesis in place of reducedness of `X`.

This is `StacksTag09NE.isIso_sigmaDesc_of_disjointClosedCover` with `[IsReduced X]` traded for
`⨅ i, (f i).ker = ⊥`. Each image is clopen, and over an affine open inside the image of the
member `i` every other member has empty preimage, so
`Stacks.IdealSheafData.ker_ideal_eq_bot_of_iInf_ker_eq_bot` applies. -/
theorem isIso_sigmaDesc_of_disjointClosedCover_of_iInf_ker {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hdisjoint : Pairwise (Function.onFun Disjoint (fun i ↦ Set.range ⇑(f i))))
    (hcover : ∀ x : X, ∃ i z, f i z = x)
    (hker : (⨅ i, Scheme.Hom.ker (f i)) = ⊥) : IsIso (Limits.Sigma.desc f) := by
  have hclosed : ∀ i, IsClosed (Set.range ⇑(f i)) := fun i ↦
    (f i).isClosedEmbedding.isClosed_range
  have hcover' : (⋃ i, Set.range ⇑(f i)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, z, rfl⟩ := hcover x
    exact ⟨i, z, rfl⟩
  have hopen : ∀ i, IsOpen (Set.range ⇑(f i)) := fun i ↦
    StacksTag09NE.isOpen_of_finite_disjoint_closed_cover_piece (fun i ↦ Set.range ⇑(f i))
      hclosed hdisjoint hcover' i
  let (i : ι) : IsOpenImmersion (f i) := by
    refine isOpenImmersion_of_isClosedImmersion_of_ker_ideal_eq_bot (f i) (hopen i) ?_
    intro W hWsub
    refine ker_ideal_eq_bot_of_iInf_ker_eq_bot f hker i W fun j hji ↦ ?_
    refine le_antisymm (fun z hz ↦ ?_) bot_le
    have h1 : (f j) z ∈ (W : Set X) := hz
    exact absurd (hWsub h1) (Set.disjoint_left.mp (hdisjoint hji) ⟨z, rfl⟩)
  refine (isIso_iff_isOpenImmersion_and_surjective _).2
    ⟨isOpenImmersion_sigmaDesc Z f hdisjoint, ⟨fun x ↦ ?_⟩⟩
  obtain ⟨i, z, rfl⟩ := hcover x
  exact ⟨Limits.Sigma.ι Z i z, sigmaDesc_apply_sigmaι Z f i z⟩

/-- **Away from the overlap locus the cover pieces form a coproduct presentation**, under the
scheme-theoretic cover hypothesis in place of reducedness.

This is `StacksTag09NE.isIso_sigmaDesc_restrict_complement_overlap` with `[IsReduced X]` traded
for `⨅ i, (f i).ker = ⊥`; the hypothesis restricts to the open complement of the overlap locus
by `Stacks.IdealSheafData.iInf_ker_morphismRestrict_eq_bot`. -/
theorem isIso_sigmaDesc_restrict_complement_overlap_of_iInf_ker {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)] (hcover : ∀ x : X, ∃ i z, f i z = x)
    (hker : (⨅ i, Scheme.Hom.ker (f i)) = ⊥) :
    let U : X.Opens :=
      ⟨(StacksTag09NE.overlapLocus X Z f)ᶜ,
        (StacksTag09NE.overlapLocus_closed X Z f).isOpen_compl⟩
    IsIso (Limits.Sigma.desc (fun i ↦ f i ∣_ U)) := by
  let U : X.Opens :=
    ⟨(StacksTag09NE.overlapLocus X Z f)ᶜ,
      (StacksTag09NE.overlapLocus_closed X Z f).isOpen_compl⟩
  have hdisjoint : Pairwise
      (Function.onFun Disjoint (fun i ↦ Set.range ⇑(f i ∣_ U))) := by
    intro i j hij
    show Disjoint (Set.range ⇑(f i ∣_ U)) (Set.range ⇑(f j ∣_ U))
    rw [Set.disjoint_left]
    rintro x ⟨yi, hyi⟩ ⟨yj, hyj⟩
    have hxi_val : (f i) yi.1 = x.1 := by
      simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hyi
    have hval : (f i) yi.1 = (f j) yj.1 := by
      simpa only [morphismRestrict_base_coe] using congrArg Subtype.val (hyi.trans hyj.symm)
    have hpair : (f i) yi.1 ∈
        ⋃ p ∈ {p : ι × ι | p.1 ≠ p.2}, Set.range (f p.1) ∩ Set.range (f p.2) := by
      simp only [Set.mem_iUnion]
      exact ⟨(i, j), hij, ⟨yi.1, rfl⟩, ⟨yj.1, hval.symm⟩⟩
    have hxoverlap : (x.1 : X) ∈ StacksTag09NE.overlapLocus X Z f := by
      rw [← hxi_val]
      exact hpair
    exact (show (x.1 : X) ∉ StacksTag09NE.overlapLocus X Z f from x.2) hxoverlap
  have hcoverU : ∀ x : U, ∃ i z, (f i ∣_ U) z = x := by
    intro x
    obtain ⟨i, z, hz⟩ := hcover x.1
    have hzU : (f i) z ∈ U := hz ▸ x.2
    exact ⟨i, ⟨z, hzU⟩, Subtype.ext ((morphismRestrict_base_coe (f i) U ⟨z, hzU⟩).trans hz)⟩
  exact isIso_sigmaDesc_of_disjointClosedCover_of_iInf_ker
    (fun i ↦ (f i ⁻¹ᵁ U).toScheme) (fun i ↦ f i ∣_ U) hdisjoint hcoverU
    (iInf_ker_morphismRestrict_eq_bot f U hker)

/-- **Restriction commutes with a finite coproduct presentation, over an arbitrary open.** If the
restrictions `f i ∣_ U` present `U` as the coproduct of the `f i ⁻¹ᵁ U`, then `Sigma.desc f ∣_ U`
is an isomorphism.

This is the hypothesis-free half of
`StacksTag09NE.isIso_sigmaDesc_morphismRestrict_complement_overlap`: that proof uses
`[IsReduced X]` in exactly one step, namely to obtain the hypothesis `hh` here, and nothing
else in it depends on `U` being the complement of the overlap locus. Stated with `hh` as a
hypothesis it serves both the reduced case and the scheme-theoretic one. -/
theorem isIso_morphismRestrict_sigmaDesc_of_isIso_sigmaDesc_morphismRestrict {ι : Type v}
    [Finite ι] {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) (U : X.Opens)
    (hh : IsIso (Limits.Sigma.desc (fun i ↦ f i ∣_ U))) :
    IsIso (Limits.Sigma.desc f ∣_ U) := by
  classical
  let g : (∐ Z) ⟶ X := Limits.Sigma.desc f
  let W : (∐ Z).Opens := g ⁻¹ᵁ U
  have hsub (i : ι) :
      Set.range ⇑((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) ⊆ Set.range ⇑W.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨Limits.Sigma.ι Z i ((f i ⁻¹ᵁ U).ι z), ?_⟩, rfl⟩
    show Limits.Sigma.desc f (Limits.Sigma.ι Z i ((f i ⁻¹ᵁ U).ι z)) ∈ U
    rw [sigmaDesc_apply_sigmaι]
    exact z.2
  let kf : ∀ i, (f i ⁻¹ᵁ U).toScheme ⟶ W.toScheme := fun i ↦
    IsOpenImmersion.lift W.ι ((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) (hsub i)
  have hfac (i : ι) : kf i ≫ W.ι = (f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i :=
    IsOpenImmersion.lift_fac W.ι _ (hsub i)
  have hdisjoint : Pairwise
      (Function.onFun Disjoint (fun i ↦ Set.range ⇑(kf i))) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨yi, hyi⟩ ⟨yj, hyj⟩
    refine hij (congrArg Sigma.fst ((sigmaι_eq_iff Z i j ((f i ⁻¹ᵁ U).ι yi)
      ((f j ⁻¹ᵁ U).ι yj)).mp ?_))
    calc
      _ = W.ι (kf i yi) := by simpa using (congrArg (fun q ↦ q.base yi) (hfac i)).symm
      _ = W.ι (kf j yj) := congrArg W.ι (hyi.trans hyj.symm)
      _ = _ := by simpa using congrArg (fun q ↦ q.base yj) (hfac j)
  have hcoverW : ∀ x : W.toScheme, ∃ i z, kf i z = x := by
    intro x
    obtain ⟨i, z, hpoint⟩ := StacksTag09NE.exists_component_point_of_sigma Z (W.ι x)
    have hzU : z ∈ f i ⁻¹ᵁ U := by
      show f i z ∈ U
      have hval : f i z = g (W.ι x) := by
        rw [← hpoint]
        exact (sigmaDesc_apply_sigmaι Z f i z).symm
      exact hval ▸ x.2
    refine ⟨i, ⟨z, hzU⟩, ?_⟩
    apply W.ι.isOpenEmbedding.injective
    calc
      (kf i ≫ W.ι) ⟨z, hzU⟩ = ((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) ⟨z, hzU⟩ :=
        congrArg (fun q ↦ q ⟨z, hzU⟩) (hfac i)
      _ = Limits.Sigma.ι Z i z := by
        show Limits.Sigma.ι Z i (((f i ⁻¹ᵁ U).ι ⟨z, hzU⟩)) = _
        simp
      _ = W.ι x := hpoint
  let (i : ι) : IsOpenImmersion (kf i) := inferInstance
  have hk : IsIso (Limits.Sigma.desc kf) :=
    StacksTag09NE.isIso_sigmaDesc_of_disjointOpenCover (fun i ↦ (f i ⁻¹ᵁ U).toScheme) kf
      hdisjoint hcoverW
  have hcomp : Limits.Sigma.desc kf ≫ g ∣_ U =
      Limits.Sigma.desc (fun i ↦ f i ∣_ U) := by
    refine Limits.Sigma.hom_ext _ _ fun i ↦ ?_
    rw [← Category.assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc, ← cancel_mono U.ι,
      Category.assoc, morphismRestrict_ι, reassoc_of% hfac i, morphismRestrict_ι]
    simp [g]
  rw [← hcomp] at hh
  exact IsIso.of_isIso_comp_left (Limits.Sigma.desc kf) (g ∣_ U)

/-- **The full replacement for the reducedness step of Tag 09NE.** Over the complement of the
overlap locus, `Sigma.desc f` is an isomorphism — the statement
`StacksTag09NE.isIso_sigmaDesc_morphismRestrict_complement_overlap` proves for reduced `X`,
here under `⨅ i, (f i).ker = ⊥` instead. -/
theorem isIso_sigmaDesc_morphismRestrict_complement_overlap_of_iInf_ker {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)] (hcover : ∀ x : X, ∃ i z, f i z = x)
    (hker : (⨅ i, Scheme.Hom.ker (f i)) = ⊥) :
    let U : X.Opens :=
      ⟨(StacksTag09NE.overlapLocus X Z f)ᶜ,
        (StacksTag09NE.overlapLocus_closed X Z f).isOpen_compl⟩
    IsIso (Limits.Sigma.desc f ∣_ U) :=
  isIso_morphismRestrict_sigmaDesc_of_isIso_sigmaDesc_morphismRestrict Z f _
    (isIso_sigmaDesc_restrict_complement_overlap_of_iInf_ker Z f hcover hker)

/-- **Tag 09NE without reducedness.** Invertible modules on the members of a finite closed cover
of a scheme `X`, meeting pairwise in discrete spaces, glue to an invertible module on `X`
restricting to each — provided the cover is a cover *scheme*-theoretically,
`⨅ i, (f i).ker = ⊥`.

This is `StacksTag09NE.exists_invertible_of_closed_cover_discrete_intersections` with
`[IsReduced X]` replaced by that hypothesis. Only one step of that proof used reducedness —
`StacksTag09NE.isIso_sigmaDesc_morphismRestrict_complement_overlap`, to see that
`Sigma.desc f` is an isomorphism away from the overlap locus — and
`Stacks.ClosedCoverKer.isIso_sigmaDesc_morphismRestrict_complement_overlap_of_iInf_ker` is that
step under the kernel hypothesis instead. Everything else, including the passage through the
finite-morphism Tag 0C0T out of the coproduct, is unchanged.

The hypothesis is strictly weaker: for reduced `X` with a set-theoretic cover it holds
automatically, since `Stacks.IdealSheafData.support_inf` makes the support of the intersection
the union of the images, which is all of `X`, and
`AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff` then forces `⊥`.

The tag is withheld: Tag 09NE's statement is about a reduced scheme, and this is a different
(stronger) theorem. -/
theorem exists_invertible_of_closed_cover_discrete_intersections_of_iInf_ker
    {ι : Type v} [Finite ι] (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hcover : ∀ x : X, ∃ i z, f i z = x)
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X)))
    (hker : (⨅ i, Scheme.Hom.ker (f i)) = ⊥)
    (L : ∀ i, (Z i).Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible (Z i).presheaf (Z i).ringCatSheaf.2 (L i)] :
    ∃ (M : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M),
      ∀ i, Nonempty ((modulePullback (f i).toLRSHom.toShHom).obj M ≅ L i) := by
  classical
  let g : (∐ Z) ⟶ X := Limits.Sigma.desc f
  let U : X.Opens :=
    ⟨(StacksTag09NE.overlapLocus X Z f)ᶜ,
      (StacksTag09NE.overlapLocus_closed X Z f).isOpen_compl⟩
  let S : Scheme.{u} := ∐ Z
  let Lcop : (∐ Z).Modules := StacksTag09NE.moduleOnSchemeSigma Z L
  have hLcop : AlgebraicGeometry.SheafOfModules.IsInvertible
      (∐ Z).presheaf (∐ Z).ringCatSheaf.2 Lcop := by
    have hLoc (x : ↥S) :=
      StacksTag09NE.moduleOnSchemeSigma_exists_local_free Z L (show ↥(∐ Z) from x)
    choose U hU I e eI using hLoc
    have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
        (C := TopologicalSpace.Opens S)
        (J := Opens.grothendieckTopology S) Lcop 1 :=
      @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u}
        (TopologicalSpace.Opens S) _
        (Opens.grothendieckTopology S) S.ringCatSheaf _ _ Lcop 1
        ⟨Stacks.FiniteLocallyFree.ModuleTFAE.localGeneratorsDataOfTrivializations Lcop U hU I e,
          Stacks.FiniteLocallyFree.ModuleTFAE.localGeneratorsDataOfTrivializations_isLocallyFreeData
            Lcop U hU I e, eI⟩
    exact (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry
        S.toRingedSpace.presheaf (structureSheafRing S.toRingedSpace).property Lcop).1
      (Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one
        (h := hflf) S.toRingedSpace Lcop)
  have : IsIso (g ∣_ U) :=
    isIso_sigmaDesc_morphismRestrict_complement_overlap_of_iInf_ker Z f hcover hker
  have : DiscreteTopology (Uᶜ : Set X) :=
    StacksTag09NE.overlapComplement_discrete X Z f hdiscrete
  obtain ⟨M, hM, ⟨eM⟩⟩ := Stacks.PicFinite.exists_isInvertible_modulePullback_iso g U Lcop hLcop
  refine ⟨M, hM, fun i ↦ ?_⟩
  have hdesc : Limits.Sigma.ι Z i ≫ g = f i := Limits.Sigma.ι_desc _ _
  let eEq : (Scheme.Modules.pullback (Limits.Sigma.ι Z i ≫ g)).obj M ≅
      (Scheme.Modules.pullback (f i)).obj M :=
    eqToIso (congrArg (fun q ↦ (Scheme.Modules.pullback q).obj M) hdesc)
  let eComp := (Scheme.Modules.pullbackComp (Limits.Sigma.ι Z i) g).app M
  exact ⟨eEq.symm.trans (eComp.symm.trans
    (((Scheme.Modules.pullback (Limits.Sigma.ι Z i)).mapIso eM).trans
      (StacksTag09NE.pullback_moduleOnSchemeSigma Z L i)))⟩

end Stacks.ClosedCoverKer

end
