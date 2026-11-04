module

public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleLift
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.InverseImageInjective
public import StacksFrontier.AlgebraicGeometry.ProEtale.FilteredColimitsOfProetaleCohomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.CoveringCharacterization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineDenseSubsite

/-!
# Exactness of the open-closed sequence on the small pro-étale site

Let `X` be a scheme, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` the inclusion of the
complementary open subscheme, assumed quasi-compact. An abelian sheaf `ℋ` on `X_proétale` with
`j⁻¹ ℋ = 0` and `i⁻¹ ℋ = 0` is zero: a section `s` of `ℋ` over an affine object `V` vanishes
over `V ×_X U`, and since `i⁻¹ ℋ` is the sheafification of the left Kan extension of `ℋ` along
base change, the vanishing of the image of `s` in `i⁻¹ ℋ (V ×_X Z)` produces finitely many
morphisms `V'_k ⟶ V` over which `s` vanishes and whose images cover the closed part of `V`.
Together with `V ×_X U ⟶ V` they form a pro-étale covering of `V`, so `s = 0`.

Consequently, when `X` is affine, the open-closed sequence `0 ⟶ j_! j⁻¹ ℱ ⟶ ℱ ⟶ i_* i⁻¹ ℱ ⟶ 0`
is short exact for every abelian sheaf `ℱ` (Stacks 09AH): it is short exact after `j⁻¹`, and
after `i⁻¹` because `i⁻¹ i_* = id` (Stacks 09BL (5)).

## Main results

* `AlgebraicGeometry.Scheme.ProEt.ofArrows_mem_topology_of_isAffine`: a family of morphisms into
  an affine object of the small pro-étale site is a covering as soon as finitely many
  quasi-compact opens of the sources have images covering the target.
* `AlgebraicGeometry.ProEtale.isZero_of_isZero_proetaleRestriction_of_isZero_proetaleInverseImage`:
  `j⁻¹` and `i⁻¹` jointly detect zero objects.
* `AlgebraicGeometry.ProEtale.shortExact_openClosedShortComplex`: the open-closed sequence is
  short exact over an affine scheme.

## References

* [Stacks Project, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.ShortComplex

variable {A : Type*} [Category* A] [Abelian A] {B₁ : Type*} [Category* B₁] [Abelian B₁]
  {B₂ : Type*} [Category* B₂] [Abelian B₂]

/-- **Two exact functors jointly detecting zero objects reflect short exactness.** -/
theorem shortExact_of_shortExact_map_of_isZero (F₁ : A ⥤ B₁) (F₂ : A ⥤ B₂) [F₁.Additive]
    [F₂.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (h : ∀ X : A, IsZero (F₁.obj X) → IsZero (F₂.obj X) → IsZero X) {S : ShortComplex A}
    (h₁ : (S.map F₁).ShortExact) (h₂ : (S.map F₂).ShortExact) : S.ShortExact := by
  have : Mono (F₁.map S.f) := h₁.mono_f
  have : Mono (F₂.map S.f) := h₂.mono_f
  have : Epi (F₁.map S.g) := h₁.epi_g
  have : Epi (F₂.map S.g) := h₂.epi_g
  have : Mono S.f := Preadditive.mono_of_isZero_kernel _ (h _
    ((isZero_kernel_of_mono (F₁.map S.f)).of_iso (PreservesKernel.iso F₁ S.f))
    ((isZero_kernel_of_mono (F₂.map S.f)).of_iso (PreservesKernel.iso F₂ S.f)))
  have : Epi S.g := Preadditive.epi_of_isZero_cokernel _ (h _
    ((isZero_cokernel_of_epi (F₁.map S.g)).of_iso (PreservesCokernel.iso F₁ S.g))
    ((isZero_cokernel_of_epi (F₂.map S.g)).of_iso (PreservesCokernel.iso F₂ S.g)))
  refine ⟨S.exact_iff_isZero_homology.2 (h _ ?_ ?_)⟩
  · exact (S.map F₁).exact_iff_isZero_homology.1 h₁.exact |>.of_iso (S.mapHomologyIso F₁).symm
  · exact (S.map F₂).exact_iff_isZero_homology.1 h₂.exact |>.of_iso (S.mapHomologyIso F₂).symm

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry

/-- A compact subset of a scheme is contained in a quasi-compact open subscheme. -/
theorem Scheme.exists_isCompact_opens_superset (T : Scheme.{u}) {K : Set T} (hK : IsCompact K) :
    ∃ O : T.Opens, IsCompact (O : Set T) ∧ K ⊆ O := by
  have hcov : K ⊆ ⋃ U : T.affineOpens, (U : Set T) := fun x _ ↦ by
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun U : T.affineOpens ↦ (U : Set T))
    (fun U ↦ U.1.isOpen) hcov
  refine ⟨⨆ U : t, (U.1 : T.Opens), ?_, ?_⟩
  · rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun U ↦ U.1.2.isCompact
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht hx)
    rw [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨U, hU⟩, hxU⟩

/-- **A pro-étale covering of an affine object.** A family of morphisms into an affine object `V`
of the small pro-étale site is a covering as soon as finitely many quasi-compact opens of the
sources have images covering `V`. -/
theorem Scheme.ProEt.ofArrows_mem_topology_of_isAffine {S : Scheme.{u}} {V : S.ProEt}
    [IsAffine V.left] {ι : Type*} (T : ι → S.ProEt) (f : ∀ k, T k ⟶ V) (n : ℕ)
    (a : Fin n → ι) (W : ∀ m, (T (a m)).left.Opens)
    (hW : ∀ m, IsCompact (W m : Set (T (a m)).left))
    (hcov : ⋃ m, (f (a m)).left '' (W m : Set (T (a m)).left) = Set.univ) :
    Sieve.ofArrows T f ∈ Scheme.ProEt.topology S V := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  show Presieve.map (Scheme.ProEt.forget S ⋙ Over.forget S) (Presieve.ofArrows T f) ∈
    Scheme.proetalePrecoverage _
  rw [Presieve.map_ofArrows, mem_proetalePrecoverage_iff_exists_affine_open_cover]
  have : IsAffine ((Scheme.ProEt.forget S ⋙ Over.forget S).obj V) := ‹IsAffine V.left›
  refine ⟨fun k ↦ ?_, PUnit, fun _ ↦ ⊤, fun _ ↦ isAffineOpen_top _, Set.iUnion_const _,
    fun _ ↦ ⟨n, a, W, hW, ?_⟩⟩
  swap
  · rwa [TopologicalSpace.Opens.coe_top]
  have hk : WeaklyEtale ((f k).left ≫ V.hom) := by
    rw [MorphismProperty.Over.w (f k)]
    exact (T k).prop
  exact MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) (f k).left V.hom
    V.prop hk

namespace ProEtale

/-- Two sections of an abelian sheaf on the small pro-étale site agreeing on a covering sieve
are equal. -/
theorem eq_of_equalizerSieve_mem {X : Scheme.{u}}
    (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) {V : X.ProEt}
    (x y : H.obj.obj (op V))
    (h : Presheaf.equalizerSieve (F := H.obj) (X := op V) x y ∈ Scheme.ProEt.topology X V) :
    x = y := by
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose (Scheme.ProEt.topology X) (CategoryTheory.forget AddCommGrpCat)).obj
      H).2).isSeparated
  exact (hsep _ h).ext fun _ _ hf ↦ hf

/-- The comma categories computing the left Kan extension along pro-étale base change are
filtered: base change preserves finite limits. -/
instance isFiltered_costructuredArrow_op_proetaleBaseChange {Z X : Scheme.{u}} (i : Z ⟶ X)
    (W : Z.ProEtᵒᵖ) : IsFiltered (CostructuredArrow (Scheme.proetaleBaseChange i).op W) := by
  have : RepresentablyFlat (Scheme.proetaleBaseChange i) := flat_of_preservesFiniteLimits _
  exact IsFiltered.of_equivalence
    (structuredArrowOpEquivalence (Scheme.proetaleBaseChange i) W.unop)

private theorem eq_of_isZero_sheaf {X : Scheme.{u}}
    {H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}} (hH : IsZero H)
    {V : X.ProEt} (x y : H.obj.obj (op V)) : x = y :=
  (AddCommGrpCat.isZero_iff_subsingleton.1
    (((sheafToPresheaf _ _).map_isZero hH).obj (op V))).elim _ _

/-- **Sections of the left Kan extension along base change which vanish.** Let `P` be an
abelian presheaf on `X_proétale`, `s ∈ P(V)`, and `g : W ⟶ V ×_X Z`. If the image of `s` in the
left Kan extension of `P` along base change at `W` is zero, then `s` vanishes on some `V' ⟶ V`
such that `g` factors through `V' ×_X Z`. -/
theorem exists_eq_zero_of_lan_map_eq_zero {Z X : Scheme.{u}} (i : Z ⟶ X)
    (P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) {V : X.ProEt} (s : P.obj (op V))
    {W : Z.ProEt} (g : W ⟶ (Scheme.proetaleBaseChange i).obj V)
    (h : ((Scheme.proetaleBaseChange i).op.lan.obj P).map g.op
      (((Scheme.proetaleBaseChange i).op.lanUnit.app P).app (op V) s) = 0) :
    ∃ (V' : X.ProEt) (φ : V' ⟶ V) (g' : W ⟶ (Scheme.proetaleBaseChange i).obj V'),
      g' ≫ (Scheme.proetaleBaseChange i).map φ = g ∧ P.map φ.op s = 0 := by
  let u := Scheme.proetaleBaseChange i
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
  let hc := Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit u.op P (op W)
  let j₀ : CostructuredArrow u.op (op W) := CostructuredArrow.mk g.op
  obtain ⟨k, f, f', hk⟩ :=
    (Concrete.isColimit_rep_eq_iff_exists _ hc (i := j₀) (j := j₀) s 0).1 (by rwa [map_zero])
  exact ⟨k.left.unop, f.left.unop, k.hom.unop, congrArg Quiver.Hom.unop (CostructuredArrow.w f),
    by rwa [map_zero] at hk⟩

/-- An abelian sheaf on the small pro-étale site whose sections over every affine object vanish
is zero: every object is covered by affine objects. -/
theorem isZero_of_forall_isAffine {X : Scheme.{u}}
    (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (hH : ∀ V : X.ProEt, IsAffine V.left → ∀ s : H.obj.obj (op V), s = 0) : IsZero H := by
  refine isZero_of_forall_isZero_proetaleSections _ fun W ↦ ?_
  refine @AddCommGrpCat.isZero_of_subsingleton _ ⟨fun s t ↦ ?_⟩
  have key : ∀ s : H.obj.obj (op W), s = 0 := fun s ↦ by
    refine eq_of_equalizerSieve_mem H s 0 ((Scheme.ProEt.topology X).superset_covering ?_
      (generate_isAffineIndEtaleOverEtale_mem X W))
    rintro V g ⟨T, a, b, hT, rfl⟩
    show H.obj.map (a ≫ b).op s = H.obj.map (a ≫ b).op 0
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hH T hT.1 (H.obj.map b.op s),
      map_zero, map_zero]
  rw [key s, key t]

/-- **Vanishing in `i⁻¹ ℋ` near the closed part.** If `i⁻¹ ℋ = 0`, a section `s` of `ℋ` over an
affine object `V` vanishes on finitely many `V'_k ⟶ V` such that quasi-compact opens of the
`V'_k` have images covering the part of `V` lying over the image of `i`. -/
theorem exists_finite_cover_of_isZero_proetaleInverseImage {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (hZ : IsZero ((Abelian.proetaleInverseImage.{u, v} i).obj H)) {V : X.ProEt} [IsAffine V.left]
    (s : H.obj.obj (op V)) :
    ∃ (ι : Type (u + 1)) (_ : Finite ι) (V' : ι → X.ProEt) (φ : ∀ k, V' k ⟶ V)
      (O : ∀ k, (V' k).left.Opens), (∀ k, IsCompact (O k : Set (V' k).left)) ∧
      (∀ k, H.obj.map (φ k).op s = 0) ∧
      ∀ x : V.left, V.hom x ∈ Set.range i.base →
        ∃ k, x ∈ (φ k).left '' (O k : Set (V' k).left) := by
  let bc := Scheme.proetaleBaseChange i
  let VZ := bc.obj V
  have hVZ : IsAffine VZ.left :=
    have : IsAffine ((𝟭 Scheme.{u}).obj V.left) := ‹IsAffine V.left›
    IsAffine.of_isPullback (IsPullback.of_hasPullback V.hom i)
  let : (Scheme.ProEt.topology Z).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let P := bc.op.lan.obj H.obj
  let s₀ := (bc.op.lanUnit.app H.obj).app (op V) s
  have ht : (toSheafify (Scheme.ProEt.topology Z) P).app (op VZ) s₀ = 0 :=
    eq_of_isZero_sheaf hZ _ _
  have hloc : Presheaf.equalizerSieve (F := P) (X := op VZ) s₀ 0 ∈
      Scheme.ProEt.topology Z VZ :=
    Presheaf.equalizerSieve_mem _ (toSheafify (Scheme.ProEt.topology Z) P) s₀ 0
      (ht.trans (map_zero _).symm)
  obtain ⟨E, hfin, hEcov, hEle, hEaff⟩ := exists_finite_affine_covering_le VZ _ hloc
  have hE : ∀ k, (bc.op.lan.obj H.obj).map (E.f k).op s₀ = 0 := fun k ↦ by
    have := hEle _ (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk k))
    change P.map (E.f k).op s₀ = P.map (E.f k).op 0 at this
    rwa [map_zero] at this
  choose V' φ g' hg' hs using fun k ↦ exists_eq_zero_of_lan_map_eq_zero i H.obj s (E.f k) (hE k)
  have hK (k : E.I₀) : IsCompact (Set.range ((g' k).left ≫ pullback.fst (V' k).hom i)) := by
    have := hEaff k
    exact isCompact_range (Scheme.Hom.continuous _)
  choose O hOc hOK using fun k ↦ Scheme.exists_isCompact_opens_superset _ (hK k)
  refine ⟨E.I₀, hfin, V', φ, O, hOc, hs, fun x hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := hx
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
  have hEs : Presieve.map (Scheme.ProEt.forget Z ⋙ Over.forget Z) E.presieve₀ ∈
      Scheme.precoverage @WeaklyEtale _ := hEcov.2
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hEs
  obtain ⟨k, w, hw⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 hEs).1 z
  refine ⟨k, ((g' k).left ≫ pullback.fst (V' k).hom i) w, hOK k ⟨w, rfl⟩, ?_⟩
  have h₁ : (g' k).left ≫ (bc.map (φ k)).left = (E.f k).left :=
    congrArg (fun g ↦ g.left) (hg' k)
  have h₂ : (g' k).left ≫ pullback.fst (V' k).hom i ≫ (φ k).left =
      (E.f k).left ≫ pullback.fst V.hom i :=
    (congrArg ((g' k).left ≫ ·) (pullback.lift_fst _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst V.hom i) h₁))
  have h₃ : ((g' k).left ≫ pullback.fst (V' k).hom i ≫ (φ k).left) w =
      ((E.f k).left ≫ pullback.fst V.hom i) w := by rw [h₂]
  refine h₃.trans ?_
  show pullback.fst V.hom i ((E.f k).left w) = x
  rw [show (E.f k).left w = z from hw, hz]

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  [QuasiCompact j] (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij in
/-- **`j⁻¹` and `i⁻¹` jointly detect zero objects.** For a closed immersion `i : Z ⟶ X` with
quasi-compact open complement `j : U ⟶ X`, an abelian sheaf `ℋ` on `X_proétale` with `j⁻¹ ℋ = 0`
and `i⁻¹ ℋ = 0` is zero. -/
theorem isZero_of_isZero_proetaleRestriction_of_isZero_proetaleInverseImage
    (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (hU : IsZero ((Abelian.proetaleRestriction.{u, v} j).obj H))
    (hZ : IsZero ((Abelian.proetaleInverseImage.{u, v} i).obj H)) : IsZero H := by
  refine isZero_of_forall_isAffine H fun V hV s ↦ ?_
  have := hV
  obtain ⟨ι, _, V', φ, O, hOc, hs, hOK⟩ :=
    exists_finite_cover_of_isZero_proetaleInverseImage i H hZ s
  let VU : X.ProEt := (proetalePostcompose j).obj ((Scheme.proetaleBaseChange j).obj V)
  let ιU : VU ⟶ V := MorphismProperty.Over.homMk (pullback.fst V.hom j)
    (pullback.condition (f := V.hom) (g := j)) trivial
  have hsU : H.obj.map ιU.op s = 0 :=
    eq_of_isZero_sheaf hU _ _
  let T : Option ι → X.ProEt := fun o ↦ o.elim VU V'
  let f : ∀ o, T o ⟶ V := fun o ↦ match o with
    | none => ιU
    | some k => φ k
  have hVU : CompactSpace (T none).left := by
    show CompactSpace (Limits.pullback (C := Scheme.{u}) V.hom j)
    have : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj V.left) :=
      inferInstanceAs (QuasiSeparatedSpace V.left)
    have : CompactSpace ((𝟭 Scheme.{u}).obj V.left) := inferInstanceAs (CompactSpace V.left)
    have : QuasiCompact (pullback.fst V.hom j) := inferInstance
    exact (quasiCompact_iff_compactSpace (pullback.fst V.hom j)).1 this
  let W' : ∀ o, (T o).left.Opens := fun o ↦ match o with
    | none => ⊤
    | some k => O k
  have hW' : ∀ o, IsCompact (W' o : Set (T o).left) := fun o ↦ match o with
    | none => isCompact_univ
    | some k => hOc k
  have hcov : ⋃ o, (f o).left '' (W' o : Set (T o).left) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
    by_cases hx : V.hom x ∈ Set.range j.base
    · obtain ⟨y, hy⟩ := hx
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      exact ⟨none, z, trivial, hz⟩
    · rw [hij, Set.mem_compl_iff, not_not] at hx
      obtain ⟨k, hk⟩ := hOK x hx
      exact ⟨some k, hk⟩
  let e := Finite.equivFin (Option ι)
  have hmem := Scheme.ProEt.ofArrows_mem_topology_of_isAffine T f (Nat.card (Option ι))
    e.symm (fun m ↦ W' (e.symm m)) (fun m ↦ hW' _) (by
      rw [← hcov]
      exact (e.symm.surjective.iUnion_comp (fun o ↦ (f o).left '' (W' o : Set (T o).left))))
  refine eq_of_equalizerSieve_mem H s 0 ((Scheme.ProEt.topology X).superset_covering ?_ hmem)
  rintro Y g ⟨Y', g₁, g₂, ⟨o⟩, rfl⟩
  show H.obj.map (g₁ ≫ f o).op s = H.obj.map (g₁ ≫ f o).op 0
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, map_zero]
  cases o with
  | none => rw [show H.obj.map (f none).op s = 0 from hsU, map_zero]
  | some k => rw [show H.obj.map (f (some k)).op s = 0 from hs k, map_zero]

omit [IsClosedImmersion i] [QuasiCompact j] in
/-- Restriction of abelian pro-étale sheaves along an open immersion is exact: it is both a left
and a right adjoint. -/
instance preservesFiniteLimits_proetaleRestriction :
    PreservesFiniteLimits (Abelian.proetaleRestriction.{u, v} j) := by
  have := (Abelian.extensionByZero_adjunction.{u, v} j).rightAdjoint_preservesLimits
  infer_instance

omit [IsClosedImmersion i] [QuasiCompact j] in
/-- Restriction of abelian pro-étale sheaves along an open immersion preserves finite colimits. -/
instance preservesFiniteColimits_proetaleRestriction :
    PreservesFiniteColimits (Abelian.proetaleRestriction.{u, v} j) := by
  obtain ⟨⟨R, adj⟩⟩ := exists_directImage_abelian.{u, v} j
  have := adj.leftAdjoint_preservesColimits
  infer_instance

omit [IsClosedImmersion i] in
/-- Inverse image of abelian pro-étale sheaves is left exact: the left Kan extension along base
change is computed by filtered colimits, base change preserving finite limits. -/
instance preservesFiniteLimits_proetaleInverseImage :
    PreservesFiniteLimits (Abelian.proetaleInverseImage.{u, v} i) := by
  have : RepresentablyFlat (Scheme.proetaleBaseChange i) := flat_of_preservesFiniteLimits _
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
  have : PreservesFiniteLimits ((Scheme.proetaleBaseChange i).op.lan :
      (X.ProEtᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) ⥤ _) :=
    Stacks.Topology.lan_preservesFiniteLimits_of_flat _ fun _ ↦ inferInstance
  have := Functor.sheafPullbackConstruction.preservesFiniteLimits (Scheme.proetaleBaseChange i)
    AddCommGrpCat.{max (u + 1) v} (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)
  exact preservesFiniteLimits_of_natIso
    ((Functor.sheafAdjunctionContinuous (Scheme.proetaleBaseChange i) AddCommGrpCat.{max (u + 1) v}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)).leftAdjointUniq
        (Abelian.proetaleInverseImageDirectImageAdj.{u, v} i))

omit [IsClosedImmersion i] in
/-- Inverse image of abelian pro-étale sheaves preserves finite colimits. -/
instance preservesFiniteColimits_proetaleInverseImage :
    PreservesFiniteColimits (Abelian.proetaleInverseImage.{u, v} i) := by
  have := (Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).leftAdjoint_preservesColimits
  infer_instance

end ProEtale

end AlgebraicGeometry

end
