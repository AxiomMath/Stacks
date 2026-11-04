module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RigidifiedPicardBigSite
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RankOneLocusField
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RankOneLocusRepresentable
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Representability.PicardGroupCardinality
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Representability.BigSiteRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace

/-!
# The Picard functor of a smooth projective curve over a separably closed field is representable

This file proves [Stacks, Tag 0B9Z]: let `k` be a separably closed field and `X` a smooth
projective curve over `k`; then the Picard functor `Pic_{X/k}` of [Stacks, Tag 0B9L] is
representable.

## The proof

The source proof chooses a rational point `σ` ([Stacks, Tag 056U]), replaces `Pic_{X/k}` by the
isomorphic functor `Pic_{X/k, σ}` ([Stacks, Tag 0B9N], [Stacks, Tag 0B9U]) and checks the
conditions of the criterion [Stacks, Tag 0B9Q]:

1. `Pic_{X/k, σ}` is an fppf sheaf, being isomorphic to `Pic_{X/k}`
   (`AlgebraicGeometry.RigidifiedPicard.isSheaf_shrink_bigSitePicardFunctor`);
2. the subfunctor `F` of [Stacks, Tag 0B9V] is representable by an open `W` of the Hilbert
   scheme `H = Hilb^g_{X/k}` ([Stacks, Tag 0B9X]), the inclusion `F ⊆ Pic_{X/k, σ}` is
   representable by open immersions ([Stacks, Tag 0B9V]), and every field-valued point of
   `Pic_{X/k, σ}` is translated into `F` by a `k`-point ([Stacks, Tag 0B9Y],
   `AlgebraicGeometry.RigidifiedPicard.exists_add_mem_rankOneLocus`).

The proof of [Stacks, Tag 0B9Q] is [Stacks, Tag 01JJ] applied to the translates of `F` by the
`k`-points `r ∈ Pic_{X/k, σ}(k)`. That is what is done here, on the big fppf site `B` on which
`Pic_{X/k}` lives, through `AlgebraicGeometry.Space.isRepresentable_of_isOpenImmersion_cover`
(Tag 01JJ for the big fppf site, in point-set form): the charts are `W ⟶ Pic_{X/k, σ}`,
`m ↦ m^*ℒ_H + r`, one for each `r`. The formulation of [Stacks, Tag 0B9Q] in
`StacksFrontier/AlgebraicGeometry/PicardScheme/Representability/GroupSchemeCriterion.lean` is not
used: it is stated on all schemes over `k` for a functor with values in `Type u`, whereas
`Pic_{X/k}` lives on the big site and its values are classes of modules; Tag 01JJ on the big site
asks for neither the Zariski sheaf property on all `k`-schemes nor a group-valued functor, and
the size bound it does ask for is supplied by `Stacks.Picard.mk_ofScheme_lt`, the number of
charts being `#Pic(X) < cutoff`.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_ι_of_forall_exists_opens`: a subfunctor of a presheaf
  on the big fppf site which is cut out, over every object `A` and section over `A`, by an open
  subscheme of `A`, is an open subspace.
* `AlgebraicGeometry.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed`:
  **[Stacks, Tag 0B9Z]**, untagged, with the two named arguments of [Stacks, Tag 0B9V] and
  [Stacks, Tag 0B9X]: `hPerfBC` ([Stacks, Tag 0A1H]) and `hRankOpen` (description
  (2) of [Stacks, Tag 0BDK] for arbitrary morphisms). A scheme `H`
  representing `Hilb^g_{X/k}` is data, an object of the site, as in [Stacks, Tag 0B9X].

## Implementation notes

`Pic_{X/k}` is the functor `Stacks.PicardFunctor.picardFunctor B hX hk f` on the `k`-schemes of a
big fppf site `B` ([Stacks, Tag 021R]), and *representable* has its meaning for a presheaf on a
category: there is an object of the site representing it. The scheme `H` representing the
Hilbert functor is accordingly taken as an object of the site: the Hilbert functor of
[Stacks, Tag 0B94] is a functor on `(Sch/k)_{fppf}`, and [Stacks, Tag 0B9I] provides an object
representing it.

## References

* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A subfunctor cut out by open subschemes is an open subspace.** Let `P` be a subfunctor of a
presheaf `G` on the big fppf site of `S` such that for every object `A` of the site and every
section `x ∈ G(A)` there is an open `U ⊆ A` with: `h^*x ∈ P(T)` exactly when `h : T ⟶ A` has image
in `U`. Then the inclusion of `P` is an open immersion: the base change of `P ⊆ G` along `x` is
represented by `U`. -/
theorem isOpenImmersion_ι_of_forall_exists_opens {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (P : Subfunctor G)
    (hP : ∀ (A : BigFppfOver B S hS) (x : G.obj (op A)),
      ∃ U : ((BigFppfOver.toScheme B S hS).obj A).Opens, ∀ {T : BigFppfOver B S hS} (h : T ⟶ A),
        G.map h.op x ∈ P.obj (op T) ↔
          Set.range ((BigFppfOver.toScheme B S hS).map h) ⊆ (U : Set _)) :
    IsOpenImmersion B S hS P.ι := by
  have hRI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists ?_
  intro A q
  obtain ⟨U, hU⟩ := hP A (yonedaEquiv q)
  obtain ⟨b, i, hi, hirange, hilift⟩ := exists_restrict_bigFppfOver A U
  have : Mono i := inverseImage_isOpenImmersion_le_monomorphisms i hi
  have hq : ∀ {T : BigFppfOver B S hS} (h : T ⟶ A),
      q.app (op T) h = G.map h.op (yonedaEquiv q) := by
    intro T h
    rw [yonedaEquiv_apply, ← NatTrans.naturality_apply]
    congr 1
  have hkey : Subfunctor.range (yoneda.map i) = P.preimage q := by
    refine Subfunctor.ext (funext fun T => Set.ext fun h => ?_)
    show (∃ t, (yoneda.map i).app T t = h) ↔ q.app T h ∈ P.obj T
    rw [hq h, hU h]
    constructor
    · rintro ⟨t, rfl⟩
      show Set.range ((BigFppfOver.toScheme B S hS).map (t ≫ i)) ⊆ _
      rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hirange]
      exact Set.image_subset_range _ _
    · intro hh
      obtain ⟨t, ht⟩ := hilift h hh
      exact ⟨t, ht⟩
  have hsq := Subfunctor.isPullback_fromPreimage P q
  have hiso := Subfunctor.isIso_lift hkey.le hkey.ge
  refine ⟨b, Subfunctor.lift (yoneda.map i) hkey.le ≫ P.fromPreimage q, i, ?_, hi⟩
  refine IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, P.fromPreimage_ι q, ← Category.assoc, Subfunctor.lift_ι]⟩
    (asIso (Subfunctor.lift (yoneda.map i) hkey.le) ≪≫ hsq.isoPullback) ?_ ?_
  · simp [hsq.isoPullback_hom_fst]
  · simp [hsq.isoPullback_hom_snd]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.RigidifiedPicard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward) in
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor) in
/-- **[Stacks, Tag 0B9Z], with [Stacks, Tag 0A1H] (`hPerfBC`) and description (2) of
[Stacks, Tag 0BDK] for arbitrary morphisms (`hRankOpen`) as arguments.** Let `k` be a separably
closed field and let `X` be a smooth projective curve over `k`. Then the Picard functor `Pic_{X/k}`
is representable.

Here `Pic_{X/k}` is the Picard functor of [Stacks, Tag 0B9L] on the `k`-schemes of a big fppf
site `B` containing `X` and `Spec k`, and `H`, an object of the site representing
`Hilb^g_{X/k}` with `g` the genus of `X`, is the data of [Stacks, Tag 0B9I] used in
[Stacks, Tag 0B9X]. The two named arguments are typed exactly as in
`AlgebraicGeometry.RigidifiedPicard.rankOneLocus_isSubfunctor_and_representable`
([Stacks, Tag 0B9V]). -/
theorem isRepresentable_picardFunctor_of_isSepClosed
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    (hRankOpen : ∀ {Z : Scheme.{u}} (E : DerivedCategory Z.Modules),
      RingedSpace.IsPerfect (X := Z.toRingedSpace) E → ∀ (i : ℤ) (r : ℕ) {Y : Scheme.{u}}
        (h : Y ⟶ Z),
        (∃ g : Y ⟶ (Scheme.Modules.singleDegreeRankOpen E i r).toScheme,
            g ≫ (Scheme.Modules.singleDegreeRankOpen E i r).ι = h) ↔
          ∃ M : Y.Modules,
            AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
              Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  h.toLRSHom.toShHom).obj E ≅
                (DerivedCategory.singleFunctor Y.Modules i).obj M))
    (B : BigFppfSite.{u}) {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (hX : B.Contains X) (hk : B.Contains (Spec (.of k))) (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    (H : BigFppfOver B (Spec (.of k)) hk)
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f)
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj H) (genus f)) :
    (Stacks.PicardFunctor.picardFunctor B hX hk (ObjectProperty.homMk f)).IsRepresentable := by
  classical
  have : IsProper f := inferInstance
  -- a rational point ([Stacks, Tag 056U])
  obtain ⟨σ, hσ, -⟩ := exists_section_of_isSepClosed f
  -- it suffices to represent `Pic_{X/k, σ}`
  refine isRepresentable_picardFunctor_of_isRepresentable_smallPicardFunctor B hX hk f σ hσ ?_
  -- (1) the sheaf property
  have hGsheaf : Presheaf.IsSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
      (smallPicardFunctor B hk f σ hσ) :=
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_shrink_bigSitePicardFunctor B hX hk f σ hσ)
  -- (2)(a) the open `W ⊆ H` representing `F` ([Stacks, Tag 0B9X])
  obtain ⟨W, hW⟩ := rankOneLocus_representable_by_open_of_hilbert f σ hσ hPerfBC hRankOpen hH
  obtain ⟨Wb, i, hi, hirange, hilift⟩ := exists_restrict_bigFppfOver H W
  have : Mono i := Space.inverseImage_isOpenImmersion_le_monomorphisms i hi
  have hiW : ∀ {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ Wb),
      ∃ h : ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T).left ⟶ W.toScheme,
        h ≫ W.ι = ((BigFppfOver.toOver B (Spec (.of k)) hk).map (t ≫ i)).left := by
    intro T t
    have hr : Set.range ((BigFppfOver.toOver B (Spec (.of k)) hk).map i).left ⊆
        Set.range W.ι := by
      rw [W.range_ι]
      exact hirange.le
    refine ⟨((BigFppfOver.toOver B (Spec (.of k)) hk).map t).left ≫ IsOpenImmersion.lift W.ι
      ((BigFppfOver.toOver B (Spec (.of k)) hk).map i).left hr, ?_⟩
    rw [Category.assoc, IsOpenImmersion.lift_fac, ← Over.comp_left, ← Functor.map_comp]
  -- the chart `Wb ⟶ Pic_{X/k, σ}`, `m ↦ m^*ℒ_H`
  obtain ⟨φ, hφ⟩ : ∃ φ : yoneda.obj Wb ⟶ smallPicardFunctor B hk f σ hσ,
      ∀ {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ Wb),
        smallPicardFunctorEquiv B hk f σ hσ T (φ.app (op T) t) =
          (picardFunctor f σ hσ).map ((BigFppfOver.toOver B (Spec (.of k)) hk).map (t ≫ i)).op
            (universalClass f σ hσ hH) := by
    refine ⟨yonedaEquiv.symm ((smallPicardFunctorEquiv B hk f σ hσ Wb).symm
      ((picardFunctor f σ hσ).map ((BigFppfOver.toOver B (Spec (.of k)) hk).map i).op
        (universalClass f σ hσ hH))), fun {T} t => ?_⟩
    show smallPicardFunctorEquiv B hk f σ hσ T ((smallPicardFunctor B hk f σ hσ).map t.op
      ((smallPicardFunctorEquiv B hk f σ hσ Wb).symm _)) = _
    rw [smallPicardFunctorEquiv_map, Equiv.apply_symm_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ← Functor.map_comp]
  -- the subfunctor `F` of [Stacks, Tag 0B9V]
  obtain ⟨hsub, hopen⟩ := rankOneLocus_isSubfunctor_and_representable f σ hσ hPerfBC hRankOpen
  obtain ⟨F, hF⟩ : ∃ F : Subfunctor (smallPicardFunctor B hk f σ hσ),
      ∀ (T : BigFppfOver B (Spec (.of k)) hk) (x : (smallPicardFunctor B hk f σ hσ).obj (op T)),
        x ∈ F.obj (op T) ↔ smallPicardFunctorEquiv B hk f σ hσ T x ∈
          rankOneLocus f σ hσ ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T) := by
    refine ⟨{ obj := fun T => (smallPicardFunctorEquiv B hk f σ hσ T.unop) ⁻¹'
                rankOneLocus f σ hσ ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T.unop)
              map := fun {T T'} g x hx => ?_ }, fun _ _ => Iff.rfl⟩
    rw [Set.mem_preimage, Set.mem_preimage, ← Quiver.Hom.op_unop g,
      smallPicardFunctorEquiv_map]
    exact hsub _ _ hx
  -- (2)(b) `F ⊆ Pic_{X/k, σ}` is an open subspace ([Stacks, Tag 0B9V])
  have hFopen : Space.IsOpenImmersion B (Spec (.of k)) hk F.ι := by
    refine Space.isOpenImmersion_ι_of_forall_exists_opens B (Spec (.of k)) hk F fun A x => ?_
    obtain ⟨U, hU⟩ := hopen ((BigFppfOver.toOver B (Spec (.of k)) hk).obj A)
      (smallPicardFunctorEquiv B hk f σ hσ A x)
    refine ⟨U, fun {T} h => ?_⟩
    rw [hF, smallPicardFunctorEquiv_map, hU]
    constructor
    · rintro ⟨h', hh'⟩
      show Set.range ((BigFppfOver.toOver B (Spec (.of k)) hk).map h).left ⊆ _
      rw [← hh', Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact (Set.image_subset_range _ _).trans_eq U.range_ι
    · intro hh
      exact ⟨IsOpenImmersion.lift U.ι _ (by rw [U.range_ι]; exact hh),
        IsOpenImmersion.lift_fac _ _ _⟩
  -- the chart is an isomorphism onto `F`
  have hrange : Subfunctor.range φ = F := by
    refine Subfunctor.ext (funext fun T => Set.ext fun x => ⟨?_, fun hx => ?_⟩)
    · rintro ⟨t, rfl⟩
      rw [hF, hφ]
      obtain ⟨eW, heW⟩ := hW ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T.unop)
      rw [← heW ⟨_, hiW t⟩]
      exact (eW ⟨_, hiW t⟩).2
    · rw [hF] at hx
      obtain ⟨eW, heW⟩ := hW ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T.unop)
      obtain ⟨⟨m, h, hh⟩, hm⟩ := eW.surjective ⟨_, hx⟩
      have hm' := congrArg Subtype.val hm
      rw [heW] at hm'
      obtain ⟨m', hmm'⟩ : ∃ m' : T.unop ⟶ H, (BigFppfOver.toOver B (Spec (.of k)) hk).map m' = m :=
        ⟨_, (BigFppfOver.fullyFaithfulToOver B (Spec (.of k)) hk).map_preimage m⟩
      obtain ⟨t, ht⟩ := hilift m' (by
        show Set.range ((BigFppfOver.toOver B (Spec (.of k)) hk).map m').left ⊆ _
        rw [hmm', ← hh, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
        exact (Set.image_subset_range _ _).trans_eq W.range_ι)
      refine ⟨t, (smallPicardFunctorEquiv B hk f σ hσ T.unop).injective ?_⟩
      rw [hφ, ht, hmm']
      exact hm'
  have hφmono : Mono φ := by
    rw [NatTrans.mono_iff_mono_app]
    intro T
    rw [mono_iff_injective]
    intro t₁ t₂ ht
    obtain ⟨eW, heW⟩ := hW ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T.unop)
    have heq : eW ⟨_, hiW t₁⟩ = eW ⟨_, hiW t₂⟩ := by
      apply Subtype.ext
      rw [heW, heW, ← hφ, ← hφ]
      exact congrArg _ ht
    have hm := congrArg Subtype.val (eW.injective heq)
    have hti : t₁ ≫ i = t₂ ≫ i :=
      (BigFppfOver.fullyFaithfulToOver B (Spec (.of k)) hk).map_injective hm
    exact (cancel_mono i).1 hti
  have hφopen : Space.IsOpenImmersion B (Spec (.of k)) hk φ := by
    have hiso := Subfunctor.isIso_lift (p := φ) hrange.le hrange.ge
    rw [← Subfunctor.lift_ι φ hrange.le]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hFopen
  -- the translates of the chart by the `k`-points of `Pic_{X/k, σ}`
  obtain ⟨I, eI⟩ : ∃ I : Type u,
      Nonempty (I ≃ (picardFunctor f σ hσ).obj (op (Over.mk (𝟙 (Spec (.of k)))))) :=
    ⟨_, ⟨(equivShrink _).symm⟩⟩
  obtain ⟨eI⟩ := eI
  have hchart : ∀ j : I, Space.IsOpenImmersion B (Spec (.of k)) hk
      (φ ≫ (translationIso B hk f σ hσ (eI j)).hom) := fun j =>
    MorphismProperty.RespectsIso.postcomp _ _ _ hφopen
  -- the number of charts is below the cutoff: `#Pic(X) < cutoff`
  have hI : #I < B.cutoff := by
    have hXk : B.Contains (pullback f (𝟙 (Spec (.of k)))) :=
      Scheme.size_pullback_lt f (𝟙 (Spec (.of k))) hX hk
    have h₁ : lift.{u + 1} #I =
        lift.{u} #((picardFunctor f σ hσ).obj (op (Over.mk (𝟙 (Spec (.of k)))))) :=
      lift_mk_eq'.2 ⟨eI⟩
    have h₂ : #((picardFunctor f σ hσ).obj (op (Over.mk (𝟙 (Spec (.of k)))))) ≤
        #(Stacks.Picard.ofScheme (pullback f (Over.mk (𝟙 (Spec (.of k)))).hom)) :=
      mk_subtype_le _
    have h₃ := Stacks.Picard.mk_ofScheme_lt (pullback f (𝟙 (Spec (.of k))))
      B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hXk
    have h₄ : lift.{u + 1} #I < lift.{u + 1} B.cutoff := by
      rw [h₁, lift_id'.{u, u + 1}]
      exact h₂.trans_lt h₃
    exact lift_lt.1 h₄
  -- (2)(c) every point lies on a chart ([Stacks, Tag 0B9Y])
  refine Space.isRepresentable_of_isOpenImmersion_cover B (Spec (.of k)) hk hGsheaf hI
    Wb.left.property (W := fun _ => Wb) (fun _ => le_rfl)
    (fun j => φ ≫ (translationIso B hk f σ hσ (eI j)).hom) hchart ?_
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨q, rfl⟩ := Quot.exists_rep y
  obtain ⟨c, hc⟩ : ∃ c : (picardFunctor f σ hσ).obj
      (op ((BigFppfOver.toOver B (Spec (.of k)) hk).obj
        (Space.FieldValuedPoint.siteObject B (Spec (.of k)) hk _ q))),
      c = smallPicardFunctorEquiv B hk f σ hσ _ q.value := ⟨_, rfl⟩
  obtain ⟨r₀, hr₀⟩ := exists_add_mem_rankOneLocus f σ hσ q.carrier q.toBase c
  have hmem : (smallPicardFunctorEquiv B hk f σ hσ
      (Space.FieldValuedPoint.siteObject B (Spec (.of k)) hk _ q)).symm
      ((picardFunctor f σ hσ).map (toBase B hk
        (Space.FieldValuedPoint.siteObject B (Spec (.of k)) hk _ q)).op r₀ + c) ∈
      F.obj (op (Space.FieldValuedPoint.siteObject B (Spec (.of k)) hk _ q)) := by
    rw [hF, Equiv.apply_symm_apply]
    exact hr₀
  rw [← hrange] at hmem
  obtain ⟨m, hm⟩ := hmem
  refine Set.mem_iUnion.2 ⟨eI.symm (-r₀), ⟨Space.FieldValuedPoint.class B (Spec (.of k)) hk _
    { carrier := q.carrier, contained := q.contained, toBase := q.toBase, value := m }, ?_⟩⟩
  rw [Space.pointsMap_class]
  congr 1
  have hv : (translationIso B hk f σ hσ (eI (eI.symm (-r₀)))).hom.app _ (φ.app _ m) = q.value := by
    apply (smallPicardFunctorEquiv B hk f σ hσ _).injective
    rw [symm_translationIso_hom_app, hm, Equiv.apply_symm_apply, Equiv.apply_symm_apply, map_neg,
      add_comm _ c, add_assoc, add_neg_cancel, add_zero]
    exact hc
  obtain ⟨K, contained, toBase, value⟩ := q
  exact congrArg (fun v => (⟨K, contained, toBase, v⟩ : Space.FieldValuedPoint B (Spec (.of k)) hk
    (smallPicardFunctor B hk f σ hσ))) hv

end AlgebraicGeometry.RigidifiedPicard

end
