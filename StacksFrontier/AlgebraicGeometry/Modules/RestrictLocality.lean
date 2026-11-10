module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Pullback

/-!
# Restriction of modules to opens: the dictionary, and locality of finite type

Let `X` be a scheme and `M` an `𝒪_X`-module. Restricting `M` to an open `Z` and then to the
part of `Z` lying over a smaller open `W` gives the same module as restricting `M` to `W`
directly — but on a *different* scheme, the open subscheme `Z.ι ⁻¹ᵁ W` of `Z` rather than `W`
itself. This file records the isomorphism between the two schemes and the resulting natural
isomorphism of restriction functors, and uses them to move `SheafOfModules.IsFiniteType` and
`SheafOfModules.IsQuasicoherent` between the two readings.

With that dictionary in place, finite type is shown to be local on a scheme for quasi-coherent
modules, which is the finite type counterpart of
`Stacks.Modules.isQuasicoherent_of_restrict`. The route is through affine charts: on an affine
open a quasi-coherent module of finite type is the `tilde` of a finite module, which is the
hypothesis of
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn`. Going through
generating sections instead is not possible from `IsFiniteType` alone, which provides local
generators on an unspecified refinement rather than global ones.

The two statements are then specialized to a cover by two opens, the shape in which the gluing
step of [Stacks, Tag 01PF] consumes them.

## Main results

* `AlgebraicGeometry.isFiniteType_restrict`: restriction along an open immersion preserves
  finite type.
* `AlgebraicGeometry.preimageIsoOfLeOpensRange`: for an open immersion `f` and an open `W`
  inside its image, `f ⁻¹ᵁ W` is isomorphic to `W`.
* `AlgebraicGeometry.restrictFunctorPreimageIso`: the two readings of "restrict to `W`" agree.
* `AlgebraicGeometry.isCompact_preimage_of_le_opensRange`: and they agree topologically.
* `AlgebraicGeometry.isFiniteType_restrict_of_le`,
  `AlgebraicGeometry.isFiniteType_restrict_preimage_of_le`,
  `AlgebraicGeometry.isQuasicoherent_restrict_preimage_of_le`: the resulting transports.
* `AlgebraicGeometry.finite_specModule_of_isFiniteType`: on an affine open, a quasi-coherent
  module of finite type has a finite module of sections. This is [Stacks, Tag 01PB] for an
  affine open of an arbitrary scheme.
* `AlgebraicGeometry.isFiniteType_of_restrict_of_isQuasicoherent`: **finite type is local on a
  scheme** for a quasi-coherent module.
* `AlgebraicGeometry.isQuasicoherent_restrict_sup` and
  `AlgebraicGeometry.isFiniteType_restrict_sup`: the two-open case.
* `AlgebraicGeometry.isFiniteType_of_iSup_eq_top` and
  `AlgebraicGeometry.isQuasicoherent_of_iSup_eq_top`: the same two localities stated for a family
  of opens covering `⊤`, which is the shape the consumers of this file use. The finite type one
  is assembled from the local generators of each restriction instead of from affine charts, so it
  needs no quasi-coherence hypothesis; `AlgebraicGeometry.generatingSectionsRestrictImage` and
  `AlgebraicGeometry.restrictTopRestrictIso` are the two transports it rests on.
* `AlgebraicGeometry.isFiniteType_restrict_top_iff`: the restriction of `M` to `⊤` is of finite
  type exactly when `M` is.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a non-reducible definition wrapping `SheafOfModules`, and
instance synthesis works only up to reducible transparency, so a hypothesis about
`(F ⋙ G).obj M` is not found when the goal mentions `(G.obj (F.obj M))` and conversely. Every
such step below is therefore a named `have` whose statement is spelled the way the next lemma
wants it; the casts are definitional and the `have`s carry no proof obligation.

## References

* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace

universe u w

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Restriction along an open immersion -/

/-- **Restriction along an open immersion preserves finite type.** Restriction is isomorphic to
the pullback functor, and pullback preserves finite type on any ringed space. -/
theorem isFiniteType_restrict (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules)
    [M.IsFiniteType] : (M.restrict f).IsFiniteType :=
  have h : ((Scheme.Modules.pullback f).obj M).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom M
  have : ((Scheme.Modules.pullback f).obj M).IsFiniteType := h
  Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm

/-- Quasi-coherence is invariant under isomorphism of `𝒪_X`-modules. -/
theorem isQuasicoherent_of_modulesIso {M N : X.Modules} (e : M ≅ N) (h : M.IsQuasicoherent) :
    N.IsQuasicoherent :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf) e h

/-! ### An open inside the image of an open immersion -/

/-- For an open immersion `f : Y ⟶ X` and an open `W` of `X` contained in the image of `f`, the
open subscheme `f ⁻¹ᵁ W` of `Y` is isomorphic to the open subscheme `W` of `X`. -/
noncomputable def preimageIsoOfLeOpensRange (f : Y ⟶ X) [IsOpenImmersion f] {W : X.Opens}
    (hW : W ≤ f.opensRange) : (f ⁻¹ᵁ W : Y.Opens).toScheme ≅ (W : X.Opens).toScheme :=
  f.isoImage (f ⁻¹ᵁ W) ≪≫ X.isoOfEq (by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW])

/-- The isomorphism `preimageIsoOfLeOpensRange f hW` followed by the inclusion of `W` is the
inclusion of `f ⁻¹ᵁ W` followed by `f`. -/
@[reassoc]
lemma preimageIsoOfLeOpensRange_hom_ι (f : Y ⟶ X) [IsOpenImmersion f] {W : X.Opens}
    (hW : W ≤ f.opensRange) :
    (preimageIsoOfLeOpensRange f hW).hom ≫ W.ι = (f ⁻¹ᵁ W).ι ≫ f := by
  rw [preimageIsoOfLeOpensRange, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    Scheme.Hom.isoImage_hom_ι]

/-- An open contained in the image of an open immersion is quasi-compact exactly when its
preimage is: an open immersion is a topological embedding. -/
lemma isCompact_preimage_of_le_opensRange (f : Y ⟶ X) [IsOpenImmersion f] {W : X.Opens}
    (hW : W ≤ f.opensRange) (hc : IsCompact (W : Set X)) :
    IsCompact ((f ⁻¹ᵁ W : Y.Opens) : Set Y) := by
  rw [f.isOpenEmbedding.isEmbedding.isCompact_iff]
  convert hc using 1
  change (f.base) '' ((f.base) ⁻¹' (W : Set X)) = _
  rw [Set.image_preimage_eq_inter_range]
  exact Set.inter_eq_self_of_subset_left hW

/-- **The two readings of "restrict to `W`" agree.** For an open immersion `f : Y ⟶ X` and an
open `W` of `X` inside the image of `f`, restricting to `Y` and then to `f ⁻¹ᵁ W` is restricting
to `W` and then transporting along `AlgebraicGeometry.preimageIsoOfLeOpensRange`. -/
noncomputable def restrictFunctorPreimageIso (f : Y ⟶ X) [IsOpenImmersion f] {W : X.Opens}
    (hW : W ≤ f.opensRange) :
    Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι ≅
      Scheme.Modules.restrictFunctor W.ι ⋙
        Scheme.Modules.restrictFunctor (preimageIsoOfLeOpensRange f hW).hom :=
  (Scheme.Modules.restrictFunctorComp (f ⁻¹ᵁ W).ι f).symm ≪≫
    Scheme.Modules.restrictFunctorCongr (preimageIsoOfLeOpensRange_hom_ι f hW).symm ≪≫
    Scheme.Modules.restrictFunctorComp (preimageIsoOfLeOpensRange f hW).hom W.ι

/-! ### Transport along an isomorphism of schemes -/

open Stacks.AlgebraicGeometry.CoherentTFAE in
/-- Restriction along an isomorphism of schemes reflects finite type. -/
theorem isFiniteType_of_restrict_iso {A : Scheme.{u}} (e : A ≅ Y) (G : Y.Modules)
    (h : (G.restrict e.hom).IsFiniteType) : G.IsFiniteType :=
  have _h0 : (G.restrict e.hom).IsFiniteType := h
  have h1 : ((G.restrict e.hom).restrict e.inv).IsFiniteType := isFiniteType_restrict _ _
  have _h2 : ((G.restrict e.symm.inv).restrict e.symm.hom).IsFiniteType := h1
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} (restrictIsoSelf e.symm G)

open Stacks.AlgebraicGeometry.CoherentTFAE in
/-- Restriction along an isomorphism of schemes reflects quasi-coherence. -/
theorem isQuasicoherent_of_restrict_iso {A : Scheme.{u}} (e : A ≅ Y) (G : Y.Modules)
    (h : (G.restrict e.hom).IsQuasicoherent) : G.IsQuasicoherent :=
  have _h0 : (G.restrict e.hom).IsQuasicoherent := h
  have h1 : ((G.restrict e.hom).restrict e.inv).IsQuasicoherent := inferInstance
  isQuasicoherent_of_modulesIso (restrictIsoSelf e.symm G) h1

/-! ### Passing between two opens, one inside the other -/

/-- Finite type on an open passes to any smaller open. -/
theorem isFiniteType_restrict_of_le (M : X.Modules) {W Z : X.Opens} (hWZ : W ≤ Z)
    (hZ : ((Scheme.Modules.restrictFunctor Z.ι).obj M).IsFiniteType) :
    ((Scheme.Modules.restrictFunctor W.ι).obj M).IsFiniteType := by
  have hW : W ≤ Z.ι.opensRange := by simpa using hWZ
  have h1 : ((M.restrict Z.ι).restrict (Z.ι ⁻¹ᵁ W).ι).IsFiniteType := isFiniteType_restrict _ _
  have _h2 : ((Scheme.Modules.restrictFunctor Z.ι ⋙
      Scheme.Modules.restrictFunctor (Z.ι ⁻¹ᵁ W).ι).obj M).IsFiniteType := h1
  have h3 : ((Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.restrictFunctor
      (preimageIsoOfLeOpensRange Z.ι hW).hom).obj M).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} ((restrictFunctorPreimageIso Z.ι hW).app M)
  exact isFiniteType_of_restrict_iso _ _ h3

/-- Finite type of `M|_W`, read on the open subscheme `Z.ι ⁻¹ᵁ W` of `Z` for `W ≤ Z`. -/
theorem isFiniteType_restrict_preimage_of_le (M : X.Modules) {W Z : X.Opens}
    (hWZ : W ≤ Z) (hW : ((Scheme.Modules.restrictFunctor W.ι).obj M).IsFiniteType) :
    (((Scheme.Modules.restrictFunctor Z.ι).obj M).restrict (Z.ι ⁻¹ᵁ W).ι).IsFiniteType := by
  have hWr : W ≤ Z.ι.opensRange := by simpa using hWZ
  have h1 : (((Scheme.Modules.restrictFunctor W.ι).obj M).restrict
      (preimageIsoOfLeOpensRange Z.ι hWr).hom).IsFiniteType := isFiniteType_restrict _ _
  have _h2 : ((Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.restrictFunctor
      (preimageIsoOfLeOpensRange Z.ι hWr).hom).obj M).IsFiniteType := h1
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((restrictFunctorPreimageIso Z.ι hWr).app M).symm

/-- Quasi-coherence of `M|_W`, read on the open subscheme `Z.ι ⁻¹ᵁ W` of `Z` for `W ≤ Z`. -/
theorem isQuasicoherent_restrict_preimage_of_le (M : X.Modules) {W Z : X.Opens}
    (hWZ : W ≤ Z) (hW : ((Scheme.Modules.restrictFunctor W.ι).obj M).IsQuasicoherent) :
    (((Scheme.Modules.restrictFunctor Z.ι).obj M).restrict (Z.ι ⁻¹ᵁ W).ι).IsQuasicoherent := by
  have hWr : W ≤ Z.ι.opensRange := by simpa using hWZ
  have _h0 : ((Scheme.Modules.restrictFunctor W.ι).obj M).IsQuasicoherent := hW
  have h1 : (((Scheme.Modules.restrictFunctor W.ι).obj M).restrict
      (preimageIsoOfLeOpensRange Z.ι hWr).hom).IsQuasicoherent := inferInstance
  have h2 : ((Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.restrictFunctor
      (preimageIsoOfLeOpensRange Z.ι hWr).hom).obj M).IsQuasicoherent := h1
  exact isQuasicoherent_of_modulesIso ((restrictFunctorPreimageIso Z.ι hWr).app M).symm h2

/-! ### Finite type is local on a scheme -/

open Stacks.AlgebraicGeometry.CoherentTFAE in
/-- **On an affine open, a quasi-coherent module of finite type has a finite module of
sections.** This is [Stacks, Tag 01PB] for an affine open of an arbitrary scheme: the module
`M|_V`, read on `Spec Γ(X, V)`, is the `tilde` of its module of sections, and
`AlgebraicGeometry.tilde_isFiniteType_iff` turns finite type for a `tilde` into finiteness of
the module. -/
theorem finite_specModule_of_isFiniteType (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V)
    (h : ((Scheme.Modules.restrictFunctor V.ι).obj F).IsFiniteType) :
    Module.Finite Γ(X, V) (specModule F hV) := by
  have _h0 : ((Scheme.Modules.restrictFunctor V.ι).obj F).IsFiniteType := h
  have _h1 : (specRestrict F hV).IsFiniteType := isFiniteType_restrict _ _
  have hqc : (specRestrict F hV).IsQuasicoherent := inferInstance
  have hiso : IsIso (specRestrict F hV).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mp hqc
  have h2 : (tilde (specModule F hV)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (@asIso _ _ _ _ _ hiso).symm
  exact (tilde_isFiniteType_iff _).mp h2

open Stacks.AlgebraicGeometry.CoherentTFAE in
/-- **Finite type is local on a scheme**, for a quasi-coherent module: if `M` is quasi-coherent
and its restriction to each member of an open covering is of finite type, then `M` is of finite
type.

The covering is refined to one by affine opens, on each of which
`AlgebraicGeometry.finite_specModule_of_isFiniteType` puts `M` in the shape of [Stacks, Tag
01XZ] (4); `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn` then
concludes. Quasi-coherence is genuinely used: `SheafOfModules.IsFiniteType` provides generating
sections only on an unspecified refinement of some covering, never on a prescribed open, so the
generating-sections route of
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_restrict_generatingSections` is not
available from the hypothesis.

`AlgebraicGeometry.isFiniteType_of_restrict` proves the same conclusion without the
quasi-coherence hypothesis, by the generating-sections route; this is the quasi-coherent
form, whose proof factors through the affine shape of [Stacks, Tag 01XZ] (4). -/
theorem isFiniteType_of_restrict_of_isQuasicoherent (M : X.Modules) [M.IsQuasicoherent]
    {I : Type w} (U : I → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, ((Scheme.Modules.restrictFunctor (U i).ι).obj M).IsFiniteType) :
    M.IsFiniteType := by
  have hcov : IsOpenCover (fun s : {V : X.Opens // IsAffineOpen V ∧ ∃ i, V ≤ U i} => s.1) := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup U from hU ▸ trivial)
    obtain ⟨V, hVaff, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hi
    exact Opens.mem_iSup.mpr ⟨⟨V, hVaff, i, hVU⟩, hxV⟩
  refine isFiniteType_of_cover_isFiniteTildeOn M _ hcov (fun s => s.2.1) fun s => ?_
  obtain ⟨i, hi⟩ := s.2.2
  exact isFiniteTildeOn_of_finite_specModule M s.1 s.2.1
    (finite_specModule_of_isFiniteType M s.2.1 (isFiniteType_restrict_of_le M hi (h i)))

/-! ### The two-open case -/

/-- The two preimages of `U` and of `V` cover the open subscheme `U ⊔ V`. -/
private lemma isOpenCover_preimage_sup (U V : X.Opens) :
    IsOpenCover (fun b : Bool => if b then (U ⊔ V).ι ⁻¹ᵁ U else (U ⊔ V).ι ⁻¹ᵁ V) := by
  rw [IsOpenCover, iSup_bool_eq]
  change (U ⊔ V).ι ⁻¹ᵁ U ⊔ (U ⊔ V).ι ⁻¹ᵁ V = ⊤
  ext x
  simp only [Opens.coe_sup, Set.mem_union, Opens.coe_top, Set.mem_univ, iff_true]
  exact x.2

/-- **Quasi-coherence over a union of two opens.** -/
theorem isQuasicoherent_restrict_sup (M : X.Modules) {U V : X.Opens}
    (hU : ((Scheme.Modules.restrictFunctor U.ι).obj M).IsQuasicoherent)
    (hV : ((Scheme.Modules.restrictFunctor V.ι).obj M).IsQuasicoherent) :
    ((Scheme.Modules.restrictFunctor (U ⊔ V).ι).obj M).IsQuasicoherent := by
  refine Stacks.Modules.isQuasicoherent_of_restrict _ _
    (isOpenCover_preimage_sup U V) fun b => ?_
  cases b with
  | false => exact isQuasicoherent_restrict_preimage_of_le M le_sup_right hV
  | true => exact isQuasicoherent_restrict_preimage_of_le M le_sup_left hU

/-- **Finite type over a union of two opens**, for a module which is quasi-coherent on each of
them. -/
theorem isFiniteType_restrict_sup (M : X.Modules) {U V : X.Opens}
    (hUqc : ((Scheme.Modules.restrictFunctor U.ι).obj M).IsQuasicoherent)
    (hVqc : ((Scheme.Modules.restrictFunctor V.ι).obj M).IsQuasicoherent)
    (hU : ((Scheme.Modules.restrictFunctor U.ι).obj M).IsFiniteType)
    (hV : ((Scheme.Modules.restrictFunctor V.ι).obj M).IsFiniteType) :
    ((Scheme.Modules.restrictFunctor (U ⊔ V).ι).obj M).IsFiniteType := by
  have _hqc : ((Scheme.Modules.restrictFunctor (U ⊔ V).ι).obj M).IsQuasicoherent :=
    isQuasicoherent_restrict_sup M hUqc hVqc
  refine isFiniteType_of_restrict_of_isQuasicoherent _ _ (isOpenCover_preimage_sup U V)
    fun b => ?_
  cases b with
  | false => exact isFiniteType_restrict_preimage_of_le M le_sup_right hV
  | true => exact isFiniteType_restrict_preimage_of_le M le_sup_left hU


/-! ### Locality on a family of opens covering the whole scheme -/

/-- **Generating sections of `(M|_U)|_W`, for `W` an open of the open subscheme `U`, give
generating sections of `M|_{U.ι ''ᵁ W}`.** The two restrictions differ by the isomorphism
`AlgebraicGeometry.Scheme.Hom.isoImage` between `W` and its image in `X`; this is the
generating-sections analogue of `Stacks.Modules.presentationRestrictImage`. -/
noncomputable def generatingSectionsRestrictImage {M : X.Modules} (U : X.Opens)
    (W : U.toScheme.Opens) (σ : ((M.restrict U.ι).restrict W.ι).GeneratingSections) :
    (M.restrict (U.ι ''ᵁ W).ι).GeneratingSections :=
  let e := U.ι.isoImage W
  let iso₁ : Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor W.ι ≅
      Scheme.Modules.restrictFunctor (U.ι ''ᵁ W).ι ⋙ Scheme.Modules.restrictFunctor e.hom :=
    (Scheme.Modules.restrictFunctorComp W.ι U.ι).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoImage_hom_ι U.ι W)).symm ≪≫
      Scheme.Modules.restrictFunctorComp e.hom (U.ι ''ᵁ W).ι
  let iso₂ : Scheme.Modules.restrictFunctor e.hom ⋙
      Scheme.Modules.restrictFunctor e.inv ≅ 𝟭 _ :=
    (Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫ Scheme.Modules.restrictFunctorId
  GeneratingSections.equivOfIso (iso₂.app (M.restrict (U.ι ''ᵁ W).ι))
    (Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsRestrict e.inv
      (GeneratingSections.equivOfIso (iso₁.app M) σ))

/-- The index type of `generatingSectionsRestrictImage U W σ` is that of `σ`. -/
@[simp]
theorem generatingSectionsRestrictImage_I {M : X.Modules} (U : X.Opens) (W : U.toScheme.Opens)
    (σ : ((M.restrict U.ι).restrict W.ι).GeneratingSections) :
    (generatingSectionsRestrictImage U W σ).I = σ.I :=
  rfl

/-- **Finite type is local on an open cover**, for a cover indexed in the universe of the
scheme. -/
private theorem isFiniteType_of_iSup_eq_top_aux (M : X.Modules) {I : Type u} (W : I → X.Opens)
    (hW : ⨆ i, W i = ⊤) (h : ∀ i, (M.restrict (W i).ι).IsFiniteType) : M.IsFiniteType := by
  choose D hD using fun i ↦ (h i).exists_localGeneratorsData
  have hcov (i : I) : ⨆ k, (D i).X k = ⊤ :=
    (Opens.coversTop_iff (T := (W i).toScheme.carrier) (D i).X).mp (D i).coversTop
  have key (i : I) : ⨆ k, (W i).ι ''ᵁ (D i).X k = W i :=
    (Scheme.Hom.image_iSup (W i).ι (D i).X).symm.trans <| by
      rw [hcov i]; exact (W i).ι_image_top
  have hcover : ⨆ j : Σ i, (D i).I, (W j.1).ι ''ᵁ (D j.1).X j.2 = ⊤ := by
    rw [iSup_sigma]
    exact (iSup_congr key).trans hW
  refine Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_restrict_generatingSections M
    (I := Σ i, (D i).I) (fun j ↦ (W j.1).ι ''ᵁ (D j.1).X j.2) hcover
    (fun j ↦ generatingSectionsRestrictImage (W j.1) ((D j.1).X j.2)
      (Stacks.AlgebraicGeometry.CoherentFinite.generatingSectionsOfOver ((D j.1).X j.2)
        (M.restrict (W j.1).ι) ((D j.1).generators j.2)))
    fun j ↦ ((hD j.1).isFiniteType j.2).finite

/-- **Finite type is local on an open cover.** If `X` is covered by opens `W i` such that every
restriction `M|_{W i}` is of finite type, then `M` is of finite type.

Unlike `AlgebraicGeometry.isFiniteType_of_restrict_of_isQuasicoherent` this takes no
quasi-coherence hypothesis: the
generators are assembled from the local generators the hypothesis already provides, moved first
to the open subscheme and then to its image in `X`. -/
theorem isFiniteType_of_iSup_eq_top (M : X.Modules) {I : Type*} (W : I → X.Opens)
    (hW : ⨆ i, W i = ⊤) (h : ∀ i, (M.restrict (W i).ι).IsFiniteType) : M.IsFiniteType := by
  refine isFiniteType_of_iSup_eq_top_aux M (I := (Set.range W : Set X.Opens))
    (fun V ↦ (V : X.Opens)) ?_ ?_
  · rw [← hW]; exact (sSup_eq_iSup' (Set.range W)).symm
  · rintro ⟨V, i, rfl⟩
    exact h i

/-- **Quasi-coherence is local on an open cover.** If `X` is covered by opens `W i` such that
every restriction `M|_{W i}` is quasi-coherent, then `M` is quasi-coherent. -/
theorem isQuasicoherent_of_iSup_eq_top (M : X.Modules) {I : Type*} (W : I → X.Opens)
    (hW : ⨆ i, W i = ⊤) (h : ∀ i, (M.restrict (W i).ι).IsQuasicoherent) : M.IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_of_restrict M W hW h

/-! ### Restriction to the top open -/

/-- **Restricting to `⊤` and back is the identity.** The open immersion `(⊤ : X.Opens).ι` is the
isomorphism `AlgebraicGeometry.Scheme.topIso`, so restricting along it and along its inverse
returns `M`. -/
noncomputable def restrictTopRestrictIso (M : X.Modules) :
    (M.restrict (⊤ : X.Opens).ι).restrict X.topIso.inv ≅ M :=
  Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSelf X.topIso.symm M

/-- **The restriction of `M` to `⊤` is of finite type exactly when `M` is.** -/
theorem isFiniteType_restrict_top_iff (M : X.Modules) :
    (M.restrict (⊤ : X.Opens).ι).IsFiniteType ↔ M.IsFiniteType := by
  refine ⟨fun hM ↦ ?_, fun hM ↦ ?_⟩
  · have := hM
    have := isFiniteType_restrict X.topIso.inv (M.restrict (⊤ : X.Opens).ι)
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} (restrictTopRestrictIso M)
  · have := hM
    exact isFiniteType_restrict (⊤ : X.Opens).ι M

end AlgebraicGeometry

end
