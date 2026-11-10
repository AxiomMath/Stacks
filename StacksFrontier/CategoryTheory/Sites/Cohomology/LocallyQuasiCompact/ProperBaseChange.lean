module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.GermDetection
public import StacksFrontier.Topology.Sheaves.Functors.Pushforward.ProperPushforward

/-!
# Proper base change for the Zariski comparison: the separated half

Let `S` be a locally quasi-compact Zariski situation, let `f : X ⟶ Y` be a morphism of its site
with underlying continuous map `g`, and let `F` be a sheaf of sets on the small Zariski site of
`X`. By `isIso_properDirectImageComparison_iff` the base-change map

`π_Y^{-1} g_* ⟶ f_{Zar,*} π_X^{-1}`

is an isomorphism exactly when the counit of the `Y`-side comparison adjunction is invertible at
every `f_{Zar,*} π_X^{-1} F`, and that counit is a morphism of sheaves on `LC_Zar/Y`, hence
invertible exactly when it is objectwise bijective. This file proves that it is objectwise
**injective** whenever `g` is a closed map, which is one of the two halves of proper base change
and the one that needs no quasi-compactness.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.injective_properBaseChangeCounit_app`: for
  a closed `g`, the counit of the comparison adjunction at `f_{Zar,*} π_X^{-1} F` is injective on
  sections over every object of `LC_Zar/Y`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_opens_preimage_eq_of_map_eq`: the
  separatedness core — two sections of `F` over `g^{-1}W` whose images in
  `(π_X^{-1}F)(P ×_Y X)` agree already agree over `g^{-1}W₀` for a neighbourhood `W₀` of the
  image of any point of `P`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.mem_zariskiTopology_of_opens_cover` and
  `mem_zariskiTopology_over_of_opens_cover`: a sieve containing the open immersions of an open
  cover is a Zariski covering sieve, on the site and on its localization.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.site_pullback_snd_range`: the image of the
  second projection of a fibre product of the site is the preimage of the image of the first leg.
  This is the second conclusion of `pullback_openEmbedding_range` with its open-embedding
  hypothesis removed.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.properBaseChangeSectionsIso`: the sections
  of `π_{Y,*} f_{Zar,*} π_X^{-1} F` over an open `W ⊆ Y` are the sections of `F` over `g^{-1}W`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_opens_preimage_restrict_eq_fibre`
  and `exists_opens_preimage_glue_fibre`: the two statements of
  `StacksFrontier/Topology/Sheaves/Functors/Pushforward/ProperPushforward.lean`, restated
  for a sheaf on the small Zariski site of `X`, which is the same thing as a sheaf on the space
  `X` because `TopCat.Presheaf.IsSheaf` is a `nonrec def` for
  `Presheaf.IsSheaf (Opens.grothendieckTopology X)`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.counit_app_comparisonSectionsIso`: the
  counit of the comparison adjunction, read on sections over an open subset of `Y` through
  `comparisonSectionsIso`, is the identity. This is the right triangle identity.

## Implementation notes

The argument never describes `π_Y^{-1}` or `π_X^{-1}`, which is what keeps it available at the
three independent universes of Stacks 0DCU. The three inputs are:

* `exists_opens_comparison_section_eq`, which writes a section of `π_Y^{-1}H` as pulled back from
  a section of `H` over an open subset of `Y`, on an open neighbourhood of each point;
* `exists_opens_eq_of_comparison_section_eq`, the germ-detection statement of `GermDetection.lean`,
  which converts an equality in `(π_X^{-1}F)(Z)` into agreement of the two sections of `F` near
  the image in `X` of every point of `Z`;
* `exists_opens_preimage_restrict_eq_of_locallyEqOn_fibre`, which converts agreement near a fibre
  of a closed map into agreement over the preimage of a neighbourhood.

The fibre of `P ×_Y X ⟶ P` over a point of `P` is identified with the fibre of `g` over its image
by `site_pullback_snd_range` alone; no properness of the base change `P ×_Y X ⟶ P` is needed, and
no description of its topology, because `exists_opens_preimage_restrict_eq_of_locallyEqOn_fibre`
is applied to `g` itself rather than to a base change of it.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v t

open Stacks.Topology

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

section Generalities

/-- A sieve containing the open immersions of an open cover of `T` is a Zariski covering sieve. -/
theorem mem_zariskiTopology_of_opens_cover {T : S.category} {ι : Type t}
    (V : ι → Opens T.obj) (hcov : ∀ x : T.obj, ∃ i, x ∈ V i)
    (R : Sieve T) (hR : ∀ i, R.arrows ((S.opensToSlice T).1.obj (V i)).hom) :
    R ∈ S.zariskiTopology T := by
  let P : Presieve T := Presieve.ofArrows (fun i => ((S.opensToSlice T).1.obj (V i)).left)
    (fun i => ((S.opensToSlice T).1.obj (V i)).hom)
  have hP : P ∈ S.zariskiPrecoverage T := by
    change P ∈ (TopCat.precoverage.comap
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop)) T
    rw [Precoverage.mem_comap_iff]
    simp only [P, Presieve.map_ofArrows]
    refine ⟨?_, ?_⟩
    · rw [Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
      intro y
      obtain ⟨i, hi⟩ := hcov y
      exact ⟨i, show y ∈ Set.range (((S.opensToSlice T).1.obj (V i)).hom : _ → T.obj) by
        rwa [((S.opensToSlice T).2 (V i)).2]⟩
    · rw [MorphismProperty.ofArrows_mem_precoverage]
      exact fun i => ((S.opensToSlice T).2 (V i)).1
  refine S.zariskiTopology.superset_covering ?_
    (S.zariskiPrecoverage.generate_mem_toGrothendieck hP)
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact hR

/-- The same statement on the localized site `LC_Zar/Y`. -/
theorem mem_zariskiTopology_over_of_opens_cover {Y : S.category} {Z : Over Y} {ι : Type t}
    (V : ι → Opens Z.left.obj) (hcov : ∀ x : Z.left.obj, ∃ i, x ∈ V i)
    (R : Sieve Z) (hR : ∀ i, R.arrows (Over.homMk (((S.opensToSlice Z.left).1.obj (V i)).hom) :
      Over.mk ((((S.opensToSlice Z.left).1.obj (V i)).hom) ≫ Z.hom) ⟶ Z)) :
    R ∈ (S.zariskiTopology.over Y) Z := by
  rw [GrothendieckTopology.mem_over_iff]
  exact mem_zariskiTopology_of_opens_cover S V hcov _
    (fun i => (Sieve.overEquiv_iff R _).2 (hR i))

/-- Naturality of the sections isomorphism in the open variable: restricting a section of `G`
and then transporting it is transporting it and then restricting along the open immersion. This
is naturality of the unit of the comparison adjunction. -/
theorem comparisonSectionsIso_hom_naturality (X : S.category)
    (G : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {U U' : Opens X.obj} (h : U' ≤ U) (y : G.obj.obj (op U)) :
    ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj G).obj.map
        ((S.opensToSlice X).1.map (homOfLE h)).op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X G U).hom y) =
      (comparisonSectionsIso.{u, w, max (u + 1) v} S X G U').hom
        (G.obj.map (homOfLE h).op y) := by
  have h₁ := types_congr_hom
    (((S.comparisonAdjunction.{u, w, max (u + 1) v} X).unit.app G).hom.naturality
      (homOfLE h).op) y
  rw [types_comp_apply, types_comp_apply] at h₁
  exact h₁.symm

/-- The counit of the comparison adjunction, read on sections over an open subset of `Y` through
`comparisonSectionsIso`, is the identity: this is the right triangle identity. -/
theorem counit_app_comparisonSectionsIso (Y : S.category)
    (A : Sheaf (S.zariskiTopology.over Y) (Type (max (u + 1) v))) (U : Opens Y.obj)
    (b : ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj A).obj.obj (op U)) :
    ((S.comparisonAdjunction.{u, w, max (u + 1) v} Y).counit.app A).hom.app
        (op ((S.opensToSlice Y).1.obj U))
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S Y
          ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj A) U).hom b) = b := by
  have h := sheafHom_congr
    ((S.comparisonAdjunction.{u, w, max (u + 1) v} Y).right_triangle_components A) (op U) b
  rwa [sheafComp_hom_app_apply] at h

end Generalities

variable {X Y : S.category} (f : X ⟶ Y)

/-- The image of the second projection of a fibre product in the site is the preimage of the
image of the first leg. -/
theorem site_pullback_snd_range {U : S.category} (j : U ⟶ Y) :
    Set.range (pullback.snd j f : _ → _) =
      {x : X.obj | (f : X.obj → Y.obj) x ∈ Set.range (j : U.obj → Y.obj)} := by
  let I : S.category ⥤ TopCat := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let c := cospan j f
  let _ : CreatesLimitsOfShape WalkingCospan S.qcSite.inclusion :=
    boundedSiteInclusionCreatesPullbacks S
  let _ : CreatesLimit c S.qcSite.inclusion := inferInstance
  let _ : CreatesLimit (c ⋙ S.qcSite.inclusion) locallyQuasiCompactHausdorffToTop :=
    inferInstance
  let _ : CreatesLimit c I := inferInstance
  let e := CategoryTheory.preservesLimitIso I c
  let cTop := cospan (I.map j) (I.map f)
  let hdiag : c ⋙ I ≅ cTop := cospanCompIso I j f
  let eTop := e.trans (HasLimit.isoOfNatIso hdiag)
  have hproj : eTop.hom ≫ limit.π cTop WalkingCospan.right = I.map (pullback.snd j f) := by
    dsimp [eTop]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π]
    simp only [cospan_right, Functor.comp_obj, cospanCompIso_hom_app_right, Category.comp_id,
      c, cTop, hdiag]
    rw [← preservesLimitIso_hom_π]
  have hsndTop : limit.π cTop WalkingCospan.right = pullback.snd (I.map j) (I.map f) :=
    PullbackCone.snd_limit_cone _ _
  change Set.range (I.map (pullback.snd j f)) = _
  rw [← hproj]
  change Set.range
    ((ConcreteCategory.hom (limit.π cTop WalkingCospan.right)) ∘
      (ConcreteCategory.hom eTop.hom)) = _
  have hsurj : Function.Surjective (ConcreteCategory.hom eTop.hom) :=
    (TopCat.homeoOfIso eTop).surjective
  rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ, hsndTop,
    TopCat.pullback_snd_range]
  rfl

/-- `f_{Zar,*} π_X^{-1} F`, as a sheaf on the localized Zariski site over `Y`. -/
abbrev properBaseChangeSheaf
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))) :
    Sheaf (S.zariskiTopology.over Y) (Type (max (u + 1) v)) :=
  ((Over.pullback f).sheafPushforwardContinuous (Type (max (u + 1) v))
      (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).obj
    ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F)

/-- The sections of `π_{Y,*} f_{Zar,*} π_X^{-1}F` over an open `W ⊆ Y` are the sections of `F`
over `g^{-1}W`. -/
def properBaseChangeSectionsIso
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))) (W : Opens Y.obj) :
    F.obj.obj (op ((Opens.map
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W)) ≅
      ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
        (properBaseChangeSheaf.{u, w, v} S f F)).obj.obj (op W) :=
  comparisonSectionsIso.{u, w, max (u + 1) v} S X F _ ≪≫
    (((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.mapIso
      ((zariskiOpenPullbackIso S f).app W).op).symm

/-- A morphism of the site which is proper in the sense of Stacks 005O (5) is proper in
Mathlib's sense, hence closed with quasi-compact fibres. -/
theorem isProperMap_site (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj)) :
    _root_.IsProperMap (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) :
      X.obj → Y.obj) :=
  isProperMap_of_isProperMap (by fun_prop) hf

/-- `exists_opens_preimage_restrict_eq_of_locallyEqOn_fibre` for a sheaf on the small Zariski
site of `X`, which is the same thing as a sheaf on the space `X` by definitional unfolding of
`TopCat.Presheaf.IsSheaf`. -/
theorem exists_opens_preimage_restrict_eq_fibre
    (hg : IsClosedMap (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) :
      X.obj → Y.obj))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {W : Opens Y.obj} {y : Y.obj} (hy : y ∈ W)
    (s t : F.obj.obj (op ((Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W)))
    (hloc : ∀ x : X.obj, (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) :
        X.obj → Y.obj) x = y →
      ∃ (N : Opens X.obj) (_ : x ∈ N) (iN : N ⟶ (Opens.map
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W),
        F.obj.map iN.op s = F.obj.map iN.op t) :
    ∃ (W₀ : Opens Y.obj) (_ : y ∈ W₀) (h₀ : W₀ ≤ W),
      F.obj.map ((Opens.map
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).map
            (homOfLE h₀)).op s =
        F.obj.map ((Opens.map
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).map
            (homOfLE h₀)).op t :=
  exists_opens_preimage_restrict_eq_of_locallyEqOn_fibre
    (g := (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)
    (CC := fun Z => Z) hg
    (F := (⟨F.obj, F.property⟩ : TopCat.Sheaf (Type (max (u + 1) v))
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X)))
    hy s t hloc

/-- `exists_opens_preimage_glue_of_isCompact_fibre` for a sheaf on the small Zariski site of
`X`. -/
theorem exists_opens_preimage_glue_fibre
    (hg : IsClosedMap (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) :
      X.obj → Y.obj))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {y : Y.obj}
    (hK : IsCompact ((((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) :
      X.obj → Y.obj) ⁻¹' {y}))
    (W : Opens Y.obj) (hy : y ∈ W)
    {ι : Type t} (N : ι → Opens X.obj) (sec : ∀ i, F.obj.obj (op (N i)))
    (hcover : ∀ x : X.obj, (((S.qcSite.inclusion ⋙
      locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj) x = y → ∃ i, x ∈ N i)
    (hloc : ∀ i j : ι, ∀ x : X.obj, (((S.qcSite.inclusion ⋙
        locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj) x = y →
      x ∈ N i → x ∈ N j →
      ∃ (M : Opens X.obj) (_ : x ∈ M) (iMi : M ⟶ N i) (iMj : M ⟶ N j),
        F.obj.map iMi.op (sec i) = F.obj.map iMj.op (sec j)) :
    ∃ (W₀ : Opens Y.obj) (_ : y ∈ W₀) (_ : W₀ ≤ W)
      (r : F.obj.obj (op ((Opens.map
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W₀))),
      ∀ x : X.obj, (((S.qcSite.inclusion ⋙
          locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj) x = y →
        ∃ (i : ι) (M : Opens X.obj) (_ : x ∈ M) (iM₀ : M ⟶ (Opens.map
            ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W₀)
          (iMi : M ⟶ N i),
          F.obj.map iM₀.op r = F.obj.map iMi.op (sec i) := by
  have : T2Space ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X) :=
    inferInstanceAs (T2Space X.obj)
  exact exists_opens_preimage_glue_of_isCompact_fibre
    (g := (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)
    (CC := fun Z => Z) hg
    (F := (⟨F.obj, F.property⟩ : TopCat.Sheaf (Type (max (u + 1) v))
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X)))
    hK W hy N sec hcover hloc

/-- Two morphisms over `T` into an object whose structure morphism is a monomorphism are
equal. -/
theorem over_hom_ext_of_mono {T : S.category} {P Q : Over T} (hQ : Mono Q.hom)
    (α β : P ⟶ Q) : α = β :=
  Over.OverMorphism.ext ((cancel_mono Q.hom).1 (by rw [Over.w, Over.w]))

/-- The structure morphism of an open subspace of `T`, viewed over `T`, is a monomorphism. -/
theorem mono_opensToSlice_hom (T : S.category) (U : Opens T.obj) :
    Mono (((S.opensToSlice T).1.obj U).hom) :=
  ConcreteCategory.mono_of_injective _ ((S.opensToSlice T).2 U).1.injective

/-- An inclusion of opens of `Z.left`, as a morphism of the localized site over `T`. -/
def opensToSliceRestrict {T : S.category} (Z : Over T) {V V' : Opens Z.left.obj} (h : V' ≤ V) :
    Over.mk ((((S.opensToSlice Z.left).1.obj V').hom) ≫ Z.hom) ⟶
      Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) :=
  Over.homMk (((S.opensToSlice Z.left).1.map (homOfLE h)).left) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, Over.w])

/-- The inclusion of `V'` into `V`, followed by the structure morphism of `V` over `Z`, is the
structure morphism of `V'` over `Z`. -/
@[simp]
theorem opensToSliceRestrict_comp {T : S.category} (Z : Over T) {V V' : Opens Z.left.obj}
    (h : V' ≤ V) :
    opensToSliceRestrict S Z h ≫ (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
        Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z) =
      (Over.homMk (((S.opensToSlice Z.left).1.obj V').hom) :
        Over.mk ((((S.opensToSlice Z.left).1.obj V').hom) ≫ Z.hom) ⟶ Z) :=
  Over.OverMorphism.ext (Over.w ((S.opensToSlice Z.left).1.map (homOfLE h)))

/-- Naturality of `properBaseChangeSectionsIso` in the open subset of `Y`. -/
theorem properBaseChangeSectionsIso_hom_naturality
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {W W' : Opens Y.obj} (h : W' ≤ W)
    (s : F.obj.obj (op ((Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W))) :
    ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
          (properBaseChangeSheaf.{u, w, v} S f F)).obj.map (homOfLE h).op
        ((properBaseChangeSectionsIso.{u, w, v} S f F W).hom s) =
      (properBaseChangeSectionsIso.{u, w, v} S f F W').hom
        (F.obj.map ((Opens.map
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).map
            (homOfLE h)).op s) := by
  have h' : (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W' ≤
      (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W :=
    fun x hx => h hx
  have hkey : (Over.pullback f).map ((S.opensToSlice Y).1.map (homOfLE h)) ≫
        ((zariskiOpenPullbackIso S f).app W).inv =
      ((zariskiOpenPullbackIso S f).app W').inv ≫ (S.opensToSlice X).1.map (homOfLE h') := by
    rw [Subsingleton.elim (homOfLE h')
      ((Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).map
        (homOfLE h))]
    exact (zariskiOpenPullbackIso S f).inv.naturality (homOfLE h)
  rw [Subsingleton.elim ((Opens.map ((S.qcSite.inclusion ⋙
    locallyQuasiCompactHausdorffToTop).map f)).map (homOfLE h)) (homOfLE h')]
  change ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
      ((Over.pullback f).map ((S.opensToSlice Y).1.map (homOfLE h))).op
      (((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
        (((zariskiOpenPullbackIso S f).app W).inv).op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F _).hom s)) = _
  rw [← types_comp_apply
      (((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map _)
    (((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map _),
    ← Functor.map_comp, ← op_comp, hkey]
  change _ = ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
      (((zariskiOpenPullbackIso S f).app W').inv).op
      ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F _).hom
        (F.obj.map (homOfLE h').op s))
  rw [← comparisonSectionsIso_hom_naturality.{u, w, v} S X F h' s, op_comp, Functor.map_comp,
    types_comp_apply]

/-- Any two morphisms over `T` into an open subspace of `T` agree. -/
theorem over_hom_opensToSlice_ext {T : S.category} {P : Over T} {W : Opens T.obj}
    (α β : P ⟶ (S.opensToSlice T).1.obj W) : α = β :=
  over_hom_ext_of_mono S (mono_opensToSlice_hom S T W) α β

/-- An object over `T` whose structure morphism has image inside an open `W` maps to `W` over
`T`. -/
theorem nonempty_over_hom_opensToSlice {T : S.category} (P : Over T) (W : Opens T.obj)
    (hP : ∀ p : P.left.obj, (P.hom : P.left.obj → T.obj) p ∈ W) :
    Nonempty (P ⟶ (S.opensToSlice T).1.obj W) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_comp_eq_of_range_subset S P.hom
    (((S.opensToSlice T).1.obj W).hom) ((S.opensToSlice T).2 W).1
    (by
      rw [((S.opensToSlice T).2 W).2]
      rintro q ⟨p, rfl⟩
      exact hP p)
  exact ⟨Over.homMk ψ hψ⟩

/-- A point of an object over `T` admitting a morphism to an open `W` of `T` has image in `W`.
This is the converse of `nonempty_over_hom_opensToSlice`. -/
theorem over_hom_opensToSlice_mem {T : S.category} {P : Over T} {W : Opens T.obj}
    (d : P ⟶ (S.opensToSlice T).1.obj W) (p : P.left.obj) :
    (P.hom : P.left.obj → T.obj) p ∈ W := by
  have hw := congrArg (fun k : P.left ⟶ T => (k : P.left.obj → T.obj) p) (Over.w d)
  have hmem : (((S.opensToSlice T).1.obj W).hom : _ → T.obj) ((d.left : P.left.obj → _) p) ∈
      Set.range (((S.opensToSlice T).1.obj W).hom : _ → T.obj) := Set.mem_range_self _
  rw [((S.opensToSlice T).2 W).2] at hmem
  rwa [← hw]

/-- `π_Y^{-1} π_{Y,*} f_{Zar,*} π_X^{-1} F`, the source of the counit. -/
abbrev properBaseChangeUnitSheaf
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))) :
    Sheaf (S.zariskiTopology.over Y) (Type (max (u + 1) v)) :=
  (S.comparisonInverseImage.{u, w, max (u + 1) v} Y).obj
    ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
      (properBaseChangeSheaf.{u, w, v} S f F))

/-- The counit of the `Y`-side comparison adjunction at `f_{Zar,*} π_X^{-1} F`. -/
abbrev properBaseChangeCounit
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))) :
    properBaseChangeUnitSheaf.{u, w, v} S f F ⟶ properBaseChangeSheaf.{u, w, v} S f F :=
  (S.comparisonAdjunction.{u, w, max (u + 1) v} Y).counit.app
    (properBaseChangeSheaf.{u, w, v} S f F)

/-- **The separatedness core of proper base change.** Let `s₁, s₂` be sections of `F` over
`g^{-1}W` for an open `W ⊆ Y`, let `P` be an object of the localized site over `Y` mapping to
`W`, and suppose the two sections of `f_{Zar,*}π_X^{-1}F` they determine over `W` have the same
pullback to `P`. Then `s₁` and `s₂` agree over `g^{-1}W₀` for an open neighbourhood `W₀ ⊆ W` of
the image of any given point of `P`. -/
theorem exists_opens_preimage_eq_of_map_eq
    (hg : IsClosedMap (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) :
      X.obj → Y.obj))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {W : Opens Y.obj}
    (s₁ s₂ : F.obj.obj (op ((Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W)))
    {P : Over Y} (d : P ⟶ (S.opensToSlice Y).1.obj W) (p₀ : P.left.obj)
    (hd : (properBaseChangeSheaf.{u, w, v} S f F).obj.map d.op
        ((properBaseChangeSectionsIso.{u, w, v} S f F W).hom s₁) =
      (properBaseChangeSheaf.{u, w, v} S f F).obj.map d.op
        ((properBaseChangeSectionsIso.{u, w, v} S f F W).hom s₂)) :
    ∃ (W₀ : Opens Y.obj) (_ : (P.hom : P.left.obj → Y.obj) p₀ ∈ W₀) (h₀ : W₀ ≤ W),
      F.obj.map ((Opens.map
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).map
            (homOfLE h₀)).op s₁ =
        F.obj.map ((Opens.map
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).map
            (homOfLE h₀)).op s₂ := by
  have hps : ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
        ((Over.pullback f).map d ≫ ((zariskiOpenPullbackIso S f).app W).inv).op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F _).hom s₁) =
      ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
        ((Over.pullback f).map d ≫ ((zariskiOpenPullbackIso S f).app W).inv).op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F _).hom s₂) := by
    have key : ∀ r : F.obj.obj (op ((Opens.map
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W)),
        ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
            ((Over.pullback f).map d ≫ ((zariskiOpenPullbackIso S f).app W).inv).op
            ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F _).hom r) =
          (properBaseChangeSheaf.{u, w, v} S f F).obj.map d.op
            ((properBaseChangeSectionsIso.{u, w, v} S f F W).hom r) := by
      intro r
      rw [op_comp, Functor.map_comp, types_comp_apply]
      rfl
    rw [key s₁, key s₂]
    exact hd
  have hloc : ∀ x : X.obj, (((S.qcSite.inclusion ⋙
        locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj) x =
      (P.hom : P.left.obj → Y.obj) p₀ →
      ∃ (N : Opens X.obj) (_ : x ∈ N) (iN : N ⟶ (Opens.map
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W),
        F.obj.map iN.op s₁ = F.obj.map iN.op s₂ := by
    intro x hx
    obtain ⟨p, hp⟩ : ∃ p : ((Over.pullback f).obj P).left.obj,
        (((Over.pullback f).obj P).hom : _ → X.obj) p = x :=
      show x ∈ Set.range (pullback.snd P.hom f : _ → _) by
        rw [site_pullback_snd_range S f P.hom]
        exact ⟨p₀, hx.symm⟩
    obtain ⟨N, hxN, hNW, heqN⟩ :=
      exists_opens_eq_of_comparison_section_eq.{u, w, v} S X F
        ((Over.pullback f).map d ≫ ((zariskiOpenPullbackIso S f).app W).inv) s₁ s₂ p hps
    rw [hp] at hxN
    exact ⟨N, hxN, homOfLE hNW, heqN⟩
  exact exists_opens_preimage_restrict_eq_fibre.{u, w, v} S f hg F
    (over_hom_opensToSlice_mem S d p₀) s₁ s₂ hloc

/-- The underlying map of a composite of morphisms of the site, on a point. -/
theorem site_hom_comp_apply {A B C : S.category} (α : A ⟶ B) (β : B ⟶ C) (p : A.obj) :
    ((α ≫ β : A ⟶ C) : A.obj → C.obj) p = (β : B.obj → C.obj) ((α : A.obj → B.obj) p) := rfl

/-- Two successive restrictions of a section of a presheaf. -/
theorem presheaf_map_op_comp_apply {D : Type*} [Category* D] (G : Dᵒᵖ ⥤ Type t)
    {T T' T'' : D} (k : T' ⟶ T) (k' : T'' ⟶ T') (x : G.obj (op T)) :
    G.map k'.op (G.map k.op x) = G.map (k' ≫ k).op x := by
  rw [← types_comp_apply, ← Functor.map_comp, ← op_comp]

/-- Restricting a section over `Z` to an open `V'` of `Z` factors through any larger open. -/
theorem map_opensToSlice_le {T : S.category} {Z : Over T} {V V' : Opens Z.left.obj} (h : V' ≤ V)
    (G : Sheaf (S.zariskiTopology.over T) (Type (max (u + 1) v))) (a : G.obj.obj (op Z)) :
    G.obj.map (Over.homMk (((S.opensToSlice Z.left).1.obj V').hom) :
        Over.mk ((((S.opensToSlice Z.left).1.obj V').hom) ≫ Z.hom) ⟶ Z).op a =
      G.obj.map (opensToSliceRestrict S Z h).op
        (G.obj.map (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
          Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z).op a) := by
  rw [presheaf_map_op_comp_apply, opensToSliceRestrict_comp]

/-- The image of a point of an open subspace of `Z.left`, as a point of `Z.left`. -/
theorem exists_opensToSlice_preimage {T : S.category} {Z : Over T} (V : Opens Z.left.obj)
    {x : Z.left.obj} (hx : x ∈ V) :
    ∃ p : ((S.opensToSlice Z.left).1.obj V).left.obj,
      ((((S.opensToSlice Z.left).1.obj V).hom) : _ → Z.left.obj) p = x := by
  rwa [← Set.mem_range, ((S.opensToSlice Z.left).2 V).2]

/-- Every point of an open subspace of `T` maps into that open. -/
theorem opensToSlice_hom_mem {T : S.category} (V : Opens T.obj)
    (p : ((S.opensToSlice T).1.obj V).left.obj) :
    ((((S.opensToSlice T).1.obj V).hom) : _ → T.obj) p ∈ V :=
  over_hom_opensToSlice_mem S (𝟙 _) p

/-- Naturality of the counit, read on an element. -/
theorem properBaseChangeCounit_naturality_apply
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {T T' : Over Y} (k : T' ⟶ T)
    (x : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.obj (op T)) :
    (properBaseChangeCounit.{u, w, v} S f F).hom.app (op T')
        ((properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map k.op x) =
      (properBaseChangeSheaf.{u, w, v} S f F).obj.map k.op
        ((properBaseChangeCounit.{u, w, v} S f F).hom.app (op T) x) := by
  have h := types_congr_hom
    ((properBaseChangeCounit.{u, w, v} S f F).hom.naturality k.op) x
  rwa [types_comp_apply, types_comp_apply] at h

/-- Applying an isomorphism of types to the image of its inverse. -/
theorem type_iso_hom_inv_apply {A B : Type t} (e : A ≅ B) (b : B) : e.hom (e.inv b) = b := by
  simp

/-- The counit, computed on a section which is pulled back from an open subset of `Y`: it is the
section of `π_{Y,*}f_{Zar,*}π_X^{-1}F` that the section came from. -/
theorem counit_app_eq_of_eq_map_comparisonSectionsIso
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over Y} (a : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.obj (op Z))
    {V : Opens Z.left.obj} {W : Opens Y.obj}
    (d : Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶
      (S.opensToSlice Y).1.obj W)
    (r : ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
      (properBaseChangeSheaf.{u, w, v} S f F)).obj.obj (op W))
    (ha : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map
        (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
          Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z).op a =
      (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map d.op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S Y
          ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
            (properBaseChangeSheaf.{u, w, v} S f F)) W).hom r)) :
    (properBaseChangeSheaf.{u, w, v} S f F).obj.map
        (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
          Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z).op
        ((properBaseChangeCounit.{u, w, v} S f F).hom.app (op Z) a) =
      (properBaseChangeSheaf.{u, w, v} S f F).obj.map d.op r := by
  rw [← properBaseChangeCounit_naturality_apply, ha,
    properBaseChangeCounit_naturality_apply, counit_app_comparisonSectionsIso]

/-- A section of `π_Y^{-1}π_{Y,*}f_{Zar,*}π_X^{-1}F` which over `V` is pulled back from an open
`Wi` of `Y`, restricted to a smaller open `V'` mapping into a smaller open `W'`, is pulled back
from `W'`. -/
theorem exists_section_of_restrict_eq
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over Y} (a : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.obj (op Z))
    {Vi : Opens Z.left.obj} {Wi : Opens Y.obj}
    (ci : Over.mk ((((S.opensToSlice Z.left).1.obj Vi).hom) ≫ Z.hom) ⟶
      (S.opensToSlice Y).1.obj Wi)
    (bi : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.obj
      (op ((S.opensToSlice Y).1.obj Wi)))
    (hbi : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map
        (Over.homMk (((S.opensToSlice Z.left).1.obj Vi).hom) :
          Over.mk ((((S.opensToSlice Z.left).1.obj Vi).hom) ≫ Z.hom) ⟶ Z).op a =
      (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map ci.op bi)
    {V' : Opens Z.left.obj} (hV' : V' ≤ Vi) {W' : Opens Y.obj} (hW' : W' ≤ Wi)
    (d : Over.mk ((((S.opensToSlice Z.left).1.obj V').hom) ≫ Z.hom) ⟶
      (S.opensToSlice Y).1.obj W')
    (hd : d ≫ (S.opensToSlice Y).1.map (homOfLE hW') =
      opensToSliceRestrict S Z hV' ≫ ci) :
    ∃ r : ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
      (properBaseChangeSheaf.{u, w, v} S f F)).obj.obj (op W'),
      (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map
          (Over.homMk (((S.opensToSlice Z.left).1.obj V').hom) :
            Over.mk ((((S.opensToSlice Z.left).1.obj V').hom) ≫ Z.hom) ⟶ Z).op a =
        (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map d.op
          ((comparisonSectionsIso.{u, w, max (u + 1) v} S Y
            ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
              (properBaseChangeSheaf.{u, w, v} S f F)) W').hom r) := by
  refine ⟨((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
    (properBaseChangeSheaf.{u, w, v} S f F)).obj.map (homOfLE hW').op
      ((comparisonSectionsIso.{u, w, max (u + 1) v} S Y _ Wi).inv bi), ?_⟩
  rw [map_opensToSlice_le S hV' _ a, hbi, presheaf_map_op_comp_apply, ← hd,
    ← presheaf_map_op_comp_apply,
    ← comparisonSectionsIso_hom_naturality.{u, w, v} S Y _ hW', type_iso_hom_inv_apply]

/-- Two sections pulled back from an open `W` of `Y` which agree after restriction to `W₀` agree
over the part of `V` lying over `W₀`. -/
theorem restrict_eq_of_restrict_section_eq
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over Y} {V : Opens Z.left.obj} {W W₀ : Opens Y.obj} (h₀ : W₀ ≤ W)
    (d : Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶
      (S.opensToSlice Y).1.obj W)
    (r₁ r₂ : ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
      (properBaseChangeSheaf.{u, w, v} S f F)).obj.obj (op W))
    (hr : ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
          (properBaseChangeSheaf.{u, w, v} S f F)).obj.map (homOfLE h₀).op r₁ =
      ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
        (properBaseChangeSheaf.{u, w, v} S f F)).obj.map (homOfLE h₀).op r₂)
    (a₁ a₂ : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.obj (op Z))
    (hr₁ : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map
        (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
          Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z).op a₁ =
      (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map d.op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S Y
          ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
            (properBaseChangeSheaf.{u, w, v} S f F)) W).hom r₁))
    (hr₂ : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map
        (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
          Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z).op a₂ =
      (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map d.op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S Y
          ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
            (properBaseChangeSheaf.{u, w, v} S f F)) W).hom r₂)) :
    (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map
        (Over.homMk (((S.opensToSlice Z.left).1.obj (V ⊓ (Opens.map
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj
            W₀)).hom) :
          Over.mk ((((S.opensToSlice Z.left).1.obj (V ⊓ (Opens.map
            ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj
              W₀)).hom) ≫ Z.hom) ⟶ Z).op a₁ =
      (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map
        (Over.homMk (((S.opensToSlice Z.left).1.obj (V ⊓ (Opens.map
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj
            W₀)).hom) :
          Over.mk ((((S.opensToSlice Z.left).1.obj (V ⊓ (Opens.map
            ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj
              W₀)).hom) ≫ Z.hom) ⟶ Z).op a₂ := by
  have hPW₀ : ∀ p : ((S.opensToSlice Z.left).1.obj (V ⊓ (Opens.map
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj
          W₀)).left.obj,
      ((Over.mk ((((S.opensToSlice Z.left).1.obj (V ⊓ (Opens.map
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj
          W₀)).hom) ≫ Z.hom)).hom : _ → Y.obj) p ∈ W₀ := fun p =>
    (opensToSlice_hom_mem S (T := Z.left) (V ⊓ (Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj W₀) p).2
  obtain ⟨d₀⟩ := nonempty_over_hom_opensToSlice S
    (Over.mk ((((S.opensToSlice Z.left).1.obj (V ⊓ (Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj
        W₀)).hom) ≫ Z.hom)) W₀ hPW₀
  have hdd : opensToSliceRestrict S Z (inf_le_left : V ⊓ (Opens.map
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj W₀ ≤ V) ≫ d =
      d₀ ≫ (S.opensToSlice Y).1.map (homOfLE h₀) :=
    over_hom_opensToSlice_ext S _ _
  rw [map_opensToSlice_le S (inf_le_left : V ⊓ (Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj W₀ ≤ V) _ a₁,
    map_opensToSlice_le S (inf_le_left : V ⊓ (Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj W₀ ≤ V) _ a₂,
    hr₁, hr₂, presheaf_map_op_comp_apply, presheaf_map_op_comp_apply, hdd,
    ← presheaf_map_op_comp_apply, ← presheaf_map_op_comp_apply,
    comparisonSectionsIso_hom_naturality.{u, w, v} S Y _ h₀,
    comparisonSectionsIso_hom_naturality.{u, w, v} S Y _ h₀, hr]

/-- **Local injectivity of the counit at `f_{Zar,*}π_X^{-1}F`.** Two sections of
`π_Y^{-1}π_{Y,*}f_{Zar,*}π_X^{-1}F` over an object `Z` of the localized site with the same image
under the counit agree on an open neighbourhood of every point of `Z`. -/
theorem exists_opens_restrict_eq_of_counit_eq
    (hg : IsClosedMap (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) :
      X.obj → Y.obj))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over Y} (a₁ a₂ : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.obj (op Z))
    (heq : (properBaseChangeCounit.{u, w, v} S f F).hom.app (op Z) a₁ =
      (properBaseChangeCounit.{u, w, v} S f F).hom.app (op Z) a₂)
    (z : Z.left.obj) :
    ∃ (V : Opens Z.left.obj) (_ : z ∈ V),
      (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map
          (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
            Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z).op a₁ =
        (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map
          (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
            Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z).op a₂ := by
  obtain ⟨V₁, hzV₁, W₁, c₁, b₁, hb₁⟩ :=
    exists_opens_comparison_section_eq.{u, w, v} S Y
      ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
        (properBaseChangeSheaf.{u, w, v} S f F)) a₁ z
  obtain ⟨V₂, hzV₂, W₂, c₂, b₂, hb₂⟩ :=
    exists_opens_comparison_section_eq.{u, w, v} S Y
      ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
        (properBaseChangeSheaf.{u, w, v} S f F)) a₂ z
  have hzV : z ∈ V₁ ⊓ V₂ := ⟨hzV₁, hzV₂⟩
  have hPW : ∀ p : ((S.opensToSlice Z.left).1.obj (V₁ ⊓ V₂)).left.obj,
      ((Over.mk ((((S.opensToSlice Z.left).1.obj (V₁ ⊓ V₂)).hom) ≫ Z.hom)).hom :
        _ → Y.obj) p ∈ W₁ ⊓ W₂ := fun p =>
    ⟨over_hom_opensToSlice_mem S
        (opensToSliceRestrict S Z (inf_le_left : V₁ ⊓ V₂ ≤ V₁) ≫ c₁) p,
      over_hom_opensToSlice_mem S
        (opensToSliceRestrict S Z (inf_le_right : V₁ ⊓ V₂ ≤ V₂) ≫ c₂) p⟩
  obtain ⟨d⟩ := nonempty_over_hom_opensToSlice S
    (Over.mk ((((S.opensToSlice Z.left).1.obj (V₁ ⊓ V₂)).hom) ≫ Z.hom)) (W₁ ⊓ W₂) hPW
  obtain ⟨r₁, hr₁⟩ := exists_section_of_restrict_eq.{u, w, v} S f F a₁ c₁ b₁ hb₁
    (inf_le_left : V₁ ⊓ V₂ ≤ V₁) (inf_le_left : W₁ ⊓ W₂ ≤ W₁) d (over_hom_opensToSlice_ext S _ _)
  obtain ⟨r₂, hr₂⟩ := exists_section_of_restrict_eq.{u, w, v} S f F a₂ c₂ b₂ hb₂
    (inf_le_right : V₁ ⊓ V₂ ≤ V₂) (inf_le_right : W₁ ⊓ W₂ ≤ W₂) d
    (over_hom_opensToSlice_ext S _ _)
  obtain ⟨p₀, hp₀⟩ := exists_opensToSlice_preimage S (Z := Z) (V₁ ⊓ V₂) hzV
  obtain ⟨W₀, hyW₀, h₀, hs⟩ := exists_opens_preimage_eq_of_map_eq.{u, w, v} S f hg F
    ((properBaseChangeSectionsIso.{u, w, v} S f F (W₁ ⊓ W₂)).inv r₁)
    ((properBaseChangeSectionsIso.{u, w, v} S f F (W₁ ⊓ W₂)).inv r₂) d p₀
    (by rw [type_iso_hom_inv_apply, type_iso_hom_inv_apply,
      ← counit_app_eq_of_eq_map_comparisonSectionsIso.{u, w, v} S f F a₁ d r₁ hr₁,
      ← counit_app_eq_of_eq_map_comparisonSectionsIso.{u, w, v} S f F a₂ d r₂ hr₂, heq])
  have hzW₀ : z ∈ (Opens.map ((S.qcSite.inclusion ⋙
      locallyQuasiCompactHausdorffToTop).map Z.hom)).obj W₀ := by
    have hw : ((Over.mk ((((S.opensToSlice Z.left).1.obj (V₁ ⊓ V₂)).hom) ≫ Z.hom)).hom :
        _ → Y.obj) p₀ = (Z.hom : Z.left.obj → Y.obj) z := by
      simp only [Over.mk_hom, site_hom_comp_apply, hp₀]
    rwa [hw] at hyW₀
  refine ⟨(V₁ ⊓ V₂) ⊓ (Opens.map ((S.qcSite.inclusion ⋙
      locallyQuasiCompactHausdorffToTop).map Z.hom)).obj W₀, ⟨hzV, hzW₀⟩,
    restrict_eq_of_restrict_section_eq.{u, w, v} S f F h₀ d r₁ r₂ ?_ a₁ a₂ hr₁ hr₂⟩
  rw [← type_iso_hom_inv_apply (properBaseChangeSectionsIso.{u, w, v} S f F (W₁ ⊓ W₂)) r₁,
    ← type_iso_hom_inv_apply (properBaseChangeSectionsIso.{u, w, v} S f F (W₁ ⊓ W₂)) r₂,
    properBaseChangeSectionsIso_hom_naturality.{u, w, v} S f F h₀,
    properBaseChangeSectionsIso_hom_naturality.{u, w, v} S f F h₀, hs]

/-- **Injectivity of the counit at `f_{Zar,*}π_X^{-1}F`**, for a closed `g`. The counit is
injective on sections over every object `Z` of the localized Zariski site over `Y`. -/
theorem injective_properBaseChangeCounit_app
    (hg : IsClosedMap (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) :
      X.obj → Y.obj))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))) (Z : Over Y) :
    Function.Injective ((properBaseChangeCounit.{u, w, v} S f F).hom.app (op Z)) := by
  intro a₁ a₂ heq
  let R : Sieve Z :=
    { arrows := fun T k => (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map k.op a₁ =
        (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map k.op a₂
      downward_closed := by
        intro T T' k hk k'
        rw [← presheaf_map_op_comp_apply, ← presheaf_map_op_comp_apply, hk] }
  choose V hzV hVR using fun z =>
    exists_opens_restrict_eq_of_counit_eq.{u, w, v} S f hg F a₁ a₂ heq z
  exact (((isSheaf_iff_isSheaf_of_type _ _).1
    (properBaseChangeUnitSheaf.{u, w, v} S f F).property _
      (mem_zariskiTopology_over_of_opens_cover S V (fun x => ⟨x, hzV x⟩) R
        hVR)).isSeparatedFor.ext fun _ k hk => hk)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
