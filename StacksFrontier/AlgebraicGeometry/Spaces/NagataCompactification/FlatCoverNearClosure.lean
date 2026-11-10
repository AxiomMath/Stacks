module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.FibreProductClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFiniteFlatNearClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCompactificationProperExtension
import all StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteLocallyFreeOverOpenBlowup

/-!
# A flat cover near the closure of `f⁻¹ Z₁`, after a blowup of `X₂`

This file carries out the fifth paragraph of the proof of Stacks 0F4B. Let `X₁₂` be the closure
of `V₁₂ = V₁ ×_U V₂` in `X₁ ×_Y X₂`, with projections `p₁, p₂`
(`AlgebraicGeometry.Space.exists_isOpenImmersion_denseRange_closure_pullback`). The closed
subspace `A = p₁⁻¹ f⁻¹ Z₁` of `V₁₂ = p₂⁻¹(V₂)` is closed in `p₂⁻¹(V₂)`, and `p₂` is étale along
it, because `V₁₂ ⟶ V₂` is a base change of `ψ₁`, which restricts to the étale `f` on `U₁`.
Stacks 0F48 then gives a `V₂`-admissible blowup `X₂' ⟶ X₂` and a flat morphism `E ⟶ X₂'`
through the strict transform of `X₁₂` whose image contains the closure of `A`.

## Main results

* `AlgebraicGeometry.Space.exists_closedSubspace_isEtaleAt_of_closure_pullback`: the closed
  subspace `A` of `p₂⁻¹(V₂)` and the étaleness of `p₂` along it.
* `AlgebraicGeometry.Space.exists_point_strictTransformSpace_of_notMem`: the strict transform
  contains every point off the exceptional divisor.
* `AlgebraicGeometry.Space.exists_isFlat_cover_closure_of_isEtaleAt`: Stacks 0F48 in terms of
  points.
* `AlgebraicGeometry.Space.exists_isFlat_cover_closure_of_isEtale`: the flat cover used in the
  valuative step of the proof of Stacks 0F4B.

## References

* [Stacks Project, Tag 0F48](https://stacks.math.columbia.edu/tag/0F48)
* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

variable {U V₁ V₂ X₂ U₁ P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **`p₂` is étale over `U₁ ×_U V₂`.** Let `k : V₁ ×_U V₂ ⟶ P` be an open immersion and
`p₂ : P ⟶ X₂` with `k ≫ p₂ = pr₂ ≫ ι₂`, `ι₂` an open immersion, and let `j : U₁ ⟶ V₁` be an
open immersion with `j ≫ ψ₁` étale. Then `p₂` is étale at the image under `k` of every point
whose first projection lies in the image of `j`. -/
theorem isEtaleAt_pointsMap_of_mem_range (hU : IsAlgebraicSpace B S hS U)
    (hV₂ : IsAlgebraicSpace B S hS V₂) (hU₁ : IsAlgebraicSpace B S hS U₁)
    {ψ₁ : V₁ ⟶ U} {ψ₂ : V₂ ⟶ U} {ι₂ : V₂ ⟶ X₂} {j : U₁ ⟶ V₁}
    (hj : IsOpenImmersion B S hS j) (hf : IsEtale B S hS (j ≫ ψ₁))
    (hι₂ : IsOpenImmersion B S hS ι₂) {k : pullback ψ₁ ψ₂ ⟶ P} (hk : IsOpenImmersion B S hS k)
    {p₂ : P ⟶ X₂} (hkp₂ : k ≫ p₂ = pullback.snd ψ₁ ψ₂ ≫ ι₂) (w : points B S hS (pullback ψ₁ ψ₂))
    (hw : pointsMap B S hS _ (pullback.fst ψ₁ ψ₂) w ∈ Set.range (pointsMap B S hS U₁ j)) :
    IsEtaleAt B S hS p₂ (pointsMap B S hS _ k w) := by
  have sq := isPullback_pullbackMap_fst_of_comp j ψ₁ ψ₂
  set c := pullback.map (j ≫ ψ₁) ψ₂ ψ₁ ψ₂ j (𝟙 V₂) (𝟙 U) (by simp) (by simp) with hc
  have hco : IsOpenImmersion B S hS c := isOpenImmersion_snd_of_isPullback sq.flip hj
  have hW : IsAlgebraicSpace B S hS (pullback (j ≫ ψ₁) ψ₂) :=
    isAlgebraicSpace_pullback B S hS _ _ hU₁ hV₂ hU
  have hm : IsOpenImmersion B S hS (c ≫ k) := isOpenImmersion_comp B S hS _ _ hco hk
  have : Mono (c ≫ k) := mono_of_presheaf_isOpenImmersion hm
  have hrange := preimage_image_pointsMap_of_isPullback B S hS sq.flip Set.univ
  rw [Set.image_univ, Set.preimage_univ, Set.image_univ] at hrange
  obtain ⟨w', hw'⟩ : w ∈ Set.range (pointsMap B S hS _ c) := hrange ▸ hw
  refine ⟨Subfunctor.range (c ≫ k), isOpenSubspace_subfunctorRange B S hS hW hm,
    pointsMap B S hS _ (Subfunctor.toRange (c ≫ k)) w', ?_, ?_⟩
  · rw [← pointsMap_comp_apply, Subfunctor.toRange_ι, pointsMap_comp_apply, hw']
  · have hsnd : IsEtale B S hS (pullback.snd (j ≫ ψ₁) ψ₂) :=
      isEtale_of_isPullback_of_isAlgebraicSpace B S hS (IsPullback.of_hasPullback _ _).flip hW
        hV₂ hU₁ hU hf
    have he : (Subfunctor.range (c ≫ k)).ι ≫ p₂ =
        inv (Subfunctor.toRange (c ≫ k)) ≫ pullback.snd (j ≫ ψ₁) ψ₂ ≫ ι₂ := by
      rw [IsIso.eq_inv_comp, ← Category.assoc, Subfunctor.toRange_ι, Category.assoc, hkp₂, hc,
        pullback.lift_snd_assoc, Category.comp_id]
    rw [he]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _)
      (isEtale_comp B S hS hsnd (isEtale_of_isOpenImmersion B S hS hι₂))

/-- **The closed subspace `p₁⁻¹ f⁻¹ Z₁` of `p₂⁻¹(V₂)`, along which `p₂` is étale.** Let
`k : V₁ ×_U V₂ ⟶ X₁₂` be an open immersion and `p₂ : X₁₂ ⟶ X₂` with `k ≫ p₂ = pr₂ ≫ ι₂`, every
point of `X₁₂` over `V₂` lying in the image of `k`. Let `T ⊆ |V₁|` be closed and contained in
the image of an open immersion `j : U₁ ⟶ V₁` with `j ≫ ψ₁` étale. Then the image under `k` of
`pr₁⁻¹ T` is the set of points of a closed subspace `A` of `p₂⁻¹(V₂)`, and `p₂` is étale at
every point of `A`. -/
theorem exists_closedSubspace_isEtaleAt_of_closure_pullback (hU : IsAlgebraicSpace B S hS U)
    (hV₁ : IsAlgebraicSpace B S hS V₁) (hV₂ : IsAlgebraicSpace B S hS V₂)
    (hX₂ : IsAlgebraicSpace B S hS X₂) (hU₁ : IsAlgebraicSpace B S hS U₁)
    (hP : IsAlgebraicSpace B S hS P) {ψ₁ : V₁ ⟶ U} {ψ₂ : V₂ ⟶ U} {ι₂ : V₂ ⟶ X₂} {j : U₁ ⟶ V₁}
    (hj : IsOpenImmersion B S hS j) (hf : IsEtale B S hS (j ≫ ψ₁))
    (hι₂ : IsOpenImmersion B S hS ι₂) {k : pullback ψ₁ ψ₂ ⟶ P} (hk : IsOpenImmersion B S hS k)
    {p₂ : P ⟶ X₂} (hkp₂ : k ≫ p₂ = pullback.snd ψ₁ ψ₂ ≫ ι₂)
    (hfoot : pointsMap B S hS P p₂ ⁻¹' Set.range (pointsMap B S hS V₂ ι₂) ⊆
      Set.range (pointsMap B S hS _ k))
    (T : Set (points B S hS V₁)) (hT : IsClosed T) (hTj : T ⊆ Set.range (pointsMap B S hS U₁ j)) :
    ∃ A : ClosedSubspaces B S hS ((Subfunctor.range ι₂).preimage p₂).toFunctor,
      Set.range (pointsMap B S hS _ (A.1.ι ≫ ((Subfunctor.range ι₂).preimage p₂).ι)) =
        pointsMap B S hS _ k '' (pointsMap B S hS _ (pullback.fst ψ₁ ψ₂) ⁻¹' T) ∧
      ∀ a : points B S hS A.1.toFunctor,
        IsEtaleAt B S hS p₂
          (pointsMap B S hS _ (A.1.ι ≫ ((Subfunctor.range ι₂).preimage p₂).ι) a) := by
  have : Mono ι₂ := mono_of_presheaf_isOpenImmersion hι₂
  have : Mono k := mono_of_presheaf_isOpenImmersion hk
  have hV₁₂ : IsAlgebraicSpace B S hS (pullback ψ₁ ψ₂) :=
    isAlgebraicSpace_pullback B S hS ψ₁ ψ₂ hV₁ hV₂ hU
  set Q := (Subfunctor.range ι₂).preimage p₂ with hQ
  have hQo : IsOpenSubspace B S hS Q :=
    isOpenSubspace_preimage B S hS p₂ _ hX₂ hP (isOpenSubspace_subfunctorRange B S hS hV₂ hι₂)
  have hQpts : Set.range (pointsMap B S hS _ Q.ι) =
      pointsMap B S hS P p₂ ⁻¹' Set.range (pointsMap B S hS V₂ ι₂) := by
    change subspacePointSet B S hS P Q = _
    rw [hQ, subspacePointSet_preimage, subspacePointSet_range]
  set C := pointsMap B S hS _ (pullback.fst ψ₁ ψ₂) ⁻¹' T
  have hCcl : IsClosed C := hT.preimage (continuous_pointsMap B S hS _)
  have hkemb : IsOpenEmbedding (pointsMap B S hS _ k) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS k) (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hk)
  have hkC : pointsMap B S hS _ k '' C ⊆ Set.range (pointsMap B S hS _ Q.ι) := by
    rintro _ ⟨w, -, rfl⟩
    rw [hQpts, Set.mem_preimage, ← pointsMap_comp_apply, hkp₂, pointsMap_comp_apply]
    exact ⟨_, rfl⟩
  -- the set of points of `A` in `p₂⁻¹(V₂)`, and its closedness
  set Aset := pointsMap B S hS _ Q.ι ⁻¹' (pointsMap B S hS _ k '' C) with hAset
  have hAcl : IsClosed Aset := by
    have : Aset = pointsMap B S hS _ Q.ι ⁻¹' closure (pointsMap B S hS _ k '' C) := by
      refine Set.Subset.antisymm (Set.preimage_mono subset_closure) fun x hx => ?_
      obtain ⟨w, hw⟩ : pointsMap B S hS _ Q.ι x ∈ Set.range (pointsMap B S hS _ k) :=
        hfoot (hQpts ▸ ⟨x, rfl⟩)
      refine ⟨w, ?_, hw⟩
      rwa [← hCcl.closure_eq, hkemb.isInducing.closure_eq_preimage_closure_image, Set.mem_preimage,
        hw]
    rw [this]
    exact isClosed_closure.preimage (continuous_pointsMap B S hS _)
  let A : ClosedSubspaces B S hS Q.toFunctor :=
    ⟨reducedClosedSubspace B S hS Q.toFunctor hQo.1 Aset hAcl,
      isClosedSubspace_reducedClosedSubspace B S hS Q.toFunctor hQo.1 Aset hAcl⟩
  have hArange : Set.range (pointsMap B S hS _ (A.1.ι ≫ Q.ι)) =
      pointsMap B S hS _ k '' C := by
    rw [pointsMap_comp, Set.range_comp,
      range_pointsMap_ι_reducedClosedSubspace B S hS Q.toFunctor hQo.1 Aset hAcl, hAset,
      Set.image_preimage_eq_of_subset hkC]
  refine ⟨A, hArange, fun a => ?_⟩
  obtain ⟨w, hwC, hw⟩ : pointsMap B S hS _ (A.1.ι ≫ Q.ι) a ∈ pointsMap B S hS _ k '' C :=
    hArange ▸ ⟨a, rfl⟩
  rw [← hw]
  exact isEtaleAt_pointsMap_of_mem_range hU hV₂ hU₁ hj hf hι₂ hk hkp₂ w (hTj hwC)

/-- **A morphism into the image of an open immersion factors through it.** If `k : A ⟶ P` is an
open immersion of algebraic spaces and every point in the image of `s : T ⟶ P` lies in the image
of `k`, then `s` factors through `k`. -/
theorem exists_comp_eq_of_isOpenImmersion_of_range_pointsMap_subset
    {A T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hT : IsAlgebraicSpace B S hS T)
    (hP : IsAlgebraicSpace B S hS P) {k : A ⟶ P} (hk : IsOpenImmersion B S hS k) (s : T ⟶ P)
    (hs : Set.range (pointsMap B S hS T s) ⊆ Set.range (pointsMap B S hS A k)) :
    ∃ w : T ⟶ A, w ≫ k = s := by
  have : Mono k := mono_of_presheaf_isOpenImmersion hk
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS hP hT (Subfunctor.range k)
    (isOpenSubspace_subfunctorRange B S hS hA hk) s).2
      (by rwa [← subspacePointSet, subspacePointSet_range])
  exact ⟨g ≫ (asIso (Subfunctor.toRange k)).inv, by rw [Category.assoc, inv_toRange_comp, hg]⟩

/-- **The strict transform contains every point off the exceptional divisor.** Let `b : A' ⟶ A`
be the blowup of `A` in `Zc` and `f : X ⟶ A`. A point of `X` and a point of `A'` with the same
image in `A`, not in `Zc`, come from a point of the strict transform of `X`. -/
theorem exists_point_strictTransformSpace_of_notMem {X A A' : AlgebraicSpaces B S hS}
    (f : X ⟶ A) {b : A' ⟶ A} {Zc : ClosedSubspaces B S hS A.1} (hb : IsBlowupAlong B S hS Zc b)
    (x : points B S hS X.1) (a' : points B S hS A'.1)
    (h : pointsMap B S hS _ f.hom x = pointsMap B S hS _ b.hom a')
    (ha' : pointsMap B S hS _ b.hom a' ∉ subspacePointSet B S hS A.1 Zc.1) :
    ∃ y : points B S hS (strictTransformSpace B S hS f b (Zc.1.preimage b.hom)).1,
      pointsMap B S hS _ (strictTransformSpaceι B S hS f b (Zc.1.preimage b.hom) ≫
        strictTransformPullbackToSource B S hS f b).hom y = x ∧
      pointsMap B S hS _ (strictTransformSpaceToBlowUp B S hS f b (Zc.1.preimage b.hom)).hom y =
        a' := by
  let E : ClosedSubspaces B S hS A'.1 :=
    ⟨Zc.1.preimage b.hom, isClosedSubspace_preimage B S hS b.hom Zc.1 A.2 A'.2 Zc.2⟩
  obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback f.hom b.hom) x a' h
  have hle := preimage_openComplement_le_strictTransformSubfunctor B S hS f b E
    hb.isPullbackDefined
  have hwO : w ∈ subspacePointSet B S hS (strictTransformPullback B S hS f b).1
      ((openComplementOfClosedSubspace B S hS A' E).1.preimage
        (strictTransformPullbackToBlowUp B S hS f b).hom) := by
    rw [subspacePointSet_preimage, subspacePointSet_openComplement]
    intro hmem
    change pointsMap B S hS _ (pullback.snd f.hom b.hom) w ∈
      subspacePointSet B S hS A'.1 (Zc.1.preimage b.hom) at hmem
    rw [hw₂, subspacePointSet_preimage] at hmem
    exact ha' hmem
  obtain ⟨o, ho⟩ := hwO
  have key : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (g : (strictTransformPullback B S hS f b).1 ⟶ W),
      pointsMap B S hS _ ((strictTransformSubfunctor B S hS f b E.1).ι ≫ g)
        (pointsMap B S hS _ (Subfunctor.homOfLe hle) o) = pointsMap B S hS _ g w := by
    intro W g
    rw [← pointsMap_comp_apply, ← Category.assoc, Subfunctor.homOfLe_ι, pointsMap_comp_apply, ho]
  exact ⟨_, (key _).trans hw₁, (key _).trans hw₂⟩

/-- **Stacks 0F48 in terms of points.** Let `f : X ⟶ Y` be a
proper morphism of quasi-compact and quasi-separated algebraic spaces, `V ⊆ Y` a quasi-compact
open subspace and `A` a closed subspace of `f⁻¹(V)` along which `f` is étale. Then there are a
proper `b : Y' ⟶ Y` (a `V`-admissible blowup) through which `V` lifts by an open immersion, an
algebraic space `X'` with `c : X' ⟶ X` and a proper `f' : X' ⟶ Y'` over `b` (the strict
transform), and `p₀ : E ⟶ X'` with `p₀ ≫ f'` flat, such that

* every pair of points of `X` and of `Y'` over a common point of `V` comes from a point of `X'`,
* every point of the closure of `c⁻¹ |A|` is in the image of `p₀`. -/
theorem exists_isFlat_cover_closure_of_isEtaleAt (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (V : OpenSubspaces B S hS Y.1) (hVqc : IsQuasiCompactSpace B S hS V.1.toFunctor)
    (A : ClosedSubspaces B S hS (V.1.preimage f.hom).toFunctor)
    (het : ∀ a : points B S hS A.1.toFunctor,
      IsEtaleAt B S hS f.hom (pointsMap B S hS _ (A.1.ι ≫ (V.1.preimage f.hom).ι) a)) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y) (ι' : V.1.toFunctor ⟶ Y'.1)
      (X' E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : X' ⟶ X.1) (f' : X' ⟶ Y'.1) (p₀ : E ⟶ X'),
      IsAlgebraicSpace B S hS X' ∧ IsAlgebraicSpace B S hS E ∧ IsProper B S hS b.hom ∧
      ι' ≫ b.hom = V.1.ι ∧ IsOpenImmersion B S hS ι' ∧ c ≫ f.hom = f' ≫ b.hom ∧
      IsProper B S hS f' ∧ IsFlat B S hS (p₀ ≫ f') ∧
      (∀ (x : points B S hS X.1) (y : points B S hS Y'.1),
        pointsMap B S hS _ f.hom x = pointsMap B S hS _ b.hom y →
        pointsMap B S hS _ b.hom y ∈ subspacePointSet B S hS Y.1 V.1 →
        ∃ x' : points B S hS X', pointsMap B S hS _ c x' = x ∧ pointsMap B S hS _ f' x' = y) ∧
      ∀ a ∈ closure (pointsMap B S hS _ c ⁻¹'
          Set.range (pointsMap B S hS _ (A.1.ι ≫ (V.1.preimage f.hom).ι))),
        ∃ a₀ : points B S hS E, pointsMap B S hS _ p₀ a₀ = a := by
  obtain ⟨Y', b, Yc, hadm, -, hYcV, hbl, E, p₀, hflat, -, -, -, -, hcov⟩ :=
    exists_isAdmissibleBlowup_isFlat_cover_closure hZ hXqc hXqs hYqc hYqs f hf V hVqc A
      het ∅ isClosed_empty (Set.disjoint_empty _)
  obtain ⟨ι', hι'b, hι'r⟩ := exists_lift_range_eq_preimage_of_isBlowupAlong V.2.1 hbl V.1.ι
    (by rwa [Subfunctor.range_ι])
  have : Mono ι' := mono_of_mono_fac hι'b
  have hι'o : IsOpenImmersion B S hS ι' := by
    have hro : IsOpenSubspace B S hS (Subfunctor.range ι') := by
      rw [hι'r]
      exact isOpenSubspace_preimage B S hS b.hom _ Y.2 Y'.2 (by rw [Subfunctor.range_ι]; exact V.2)
    rw [← Subfunctor.toRange_ι ι']
    exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) hro.2
  refine ⟨Y', b, ι', _, E.1, _, _, p₀.hom, (strictTransformSpace B S hS f b _).2, E.2,
    hadm.isProper, hι'b, hι'o, ?_, isProper_strictTransformSpaceToBlowUp_of_isProper f b _ hf,
    hflat,
    fun x y hxy hy => exists_point_strictTransformSpace_of_notMem f hbl x y hxy
      fun h => Set.disjoint_left.1 hYcV hy h,
    fun a ha => (hcov a ha).imp fun _ h => h.1⟩
  have hsq : (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom =
      (strictTransformPullbackToBlowUp B S hS f b).hom ≫ b.hom := pullback.condition
  change (strictTransformSpaceι B S hS f b (Yc.1.preimage b.hom)).hom ≫
      (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom =
    (strictTransformSpaceι B S hS f b (Yc.1.preimage b.hom)).hom ≫
      (strictTransformPullbackToBlowUp B S hS f b).hom ≫ b.hom
  rw [hsq]

/-- **The closure of `ι₂'(ψ₂⁻¹ Z)` lies in the image of a closure.** Let `k : V₁ ×_U V₂ ⟶ P` and
`p₂ : P ⟶ X₂` with `k ≫ p₂ = pr₂ ≫ ι₂`, `b : X₂' ⟶ X₂` with a lift `ι₂'` of `ι₂`, and
`c : X' ⟶ P`, `f' : X' ⟶ X₂'` proper, through which pairs of points over `V₂` lift. If every point
of `V₂` over `Z` is the second coordinate of a point of `pr₁⁻¹ T`, then the closure of
`ι₂'(ψ₂⁻¹ Z)` lies in the image under `f'` of the closure of `c⁻¹ k(pr₁⁻¹ T)`. -/
theorem closure_image_preimage_subset_image_closure_of_lift
    {X₂' X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX₂' : IsAlgebraicSpace B S hS X₂')
    {ψ₁ : V₁ ⟶ U} {ψ₂ : V₂ ⟶ U} {ι₂ : V₂ ⟶ X₂} {k : pullback ψ₁ ψ₂ ⟶ P} {p₂ : P ⟶ X₂}
    (hkp₂ : k ≫ p₂ = pullback.snd ψ₁ ψ₂ ≫ ι₂) {b : X₂' ⟶ X₂} {ι₂' : V₂ ⟶ X₂'}
    (hι₂'b : ι₂' ≫ b = ι₂) {c : X' ⟶ P} {f' : X' ⟶ X₂'} (hf' : IsProper B S hS f')
    (hlift : ∀ (x : points B S hS P) (y : points B S hS X₂'),
      pointsMap B S hS _ p₂ x = pointsMap B S hS _ b y →
      pointsMap B S hS _ b y ∈ Set.range (pointsMap B S hS V₂ ι₂) →
      ∃ x' : points B S hS X', pointsMap B S hS _ c x' = x ∧ pointsMap B S hS _ f' x' = y)
    (T : Set (points B S hS V₁)) (Zs : Set (points B S hS U))
    (hsurj : ∀ z : points B S hS V₂, pointsMap B S hS _ ψ₂ z ∈ Zs →
      ∃ w : points B S hS (pullback ψ₁ ψ₂), pointsMap B S hS _ (pullback.fst ψ₁ ψ₂) w ∈ T ∧
        pointsMap B S hS _ (pullback.snd ψ₁ ψ₂) w = z) :
    closure (pointsMap B S hS V₂ ι₂' '' (pointsMap B S hS V₂ ψ₂ ⁻¹' Zs)) ⊆
      pointsMap B S hS _ f' '' closure (pointsMap B S hS _ c ⁻¹'
        (pointsMap B S hS _ k '' (pointsMap B S hS _ (pullback.fst ψ₁ ψ₂) ⁻¹' T))) := by
  refine closure_minimal (Set.Subset.trans ?_ (Set.image_mono subset_closure))
    (isClosedMap_pointsMap_of_pullback_fst_id B S hS f' (hf'.2.2 X₂' hX₂' (𝟙 X₂')) _
      isClosed_closure)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨w, hwT, hwz⟩ := hsurj z hz
  have hb : pointsMap B S hS _ p₂ (pointsMap B S hS _ k w) =
      pointsMap B S hS _ b (pointsMap B S hS _ ι₂' z) := by
    rw [← pointsMap_comp_apply, hkp₂, pointsMap_comp_apply, hwz, ← pointsMap_comp_apply, hι₂'b]
  obtain ⟨x', hx'c, hx'f⟩ := hlift _ _ hb (by
    rw [← pointsMap_comp_apply, hι₂'b]
    exact ⟨z, rfl⟩)
  refine ⟨x', ?_, hx'f⟩
  rw [Set.mem_preimage, hx'c]
  exact ⟨w, hwT, rfl⟩

/-- **Morphisms over `V₂` come from `V₁`.** Let `k : V₁ ×_U V₂ ⟶ P` be an open immersion with
`k ≫ pᵢ = prᵢ ≫ ιᵢ`, every point of `P` over `V₂` lying in the image of `k`. A morphism
`g : T' ⟶ P` with `g ≫ p₂ = v ≫ ι₂` comes from some `v₁ : T' ⟶ V₁` with `v₁ ≫ ψ₁ = v ≫ ψ₂`. -/
theorem exists_lift_fst_of_comp_eq {X₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV₁ : IsAlgebraicSpace B S hS V₁)
    (hV₂ : IsAlgebraicSpace B S hS V₂) (hP : IsAlgebraicSpace B S hS P) {ψ₁ : V₁ ⟶ U}
    {ψ₂ : V₂ ⟶ U} {ι₁ : V₁ ⟶ X₁} {ι₂ : V₂ ⟶ X₂} (hι₂ : IsOpenImmersion B S hS ι₂)
    {k : pullback ψ₁ ψ₂ ⟶ P} (hk : IsOpenImmersion B S hS k) {p₁ : P ⟶ X₁} {p₂ : P ⟶ X₂}
    (hkp₁ : k ≫ p₁ = pullback.fst ψ₁ ψ₂ ≫ ι₁) (hkp₂ : k ≫ p₂ = pullback.snd ψ₁ ψ₂ ≫ ι₂)
    (hfoot : pointsMap B S hS P p₂ ⁻¹' Set.range (pointsMap B S hS V₂ ι₂) ⊆
      Set.range (pointsMap B S hS _ k))
    {T' : BigFppfOver B S hS} (g : yoneda.obj T' ⟶ P) (v : yoneda.obj T' ⟶ V₂)
    (hg : g ≫ p₂ = v ≫ ι₂) :
    ∃ v₁ : yoneda.obj T' ⟶ V₁, v₁ ≫ ι₁ = g ≫ p₁ ∧ v₁ ≫ ψ₁ = v ≫ ψ₂ := by
  have : Mono ι₂ := mono_of_presheaf_isOpenImmersion hι₂
  obtain ⟨w, hw⟩ := exists_comp_eq_of_isOpenImmersion_of_range_pointsMap_subset
    (isAlgebraicSpace_pullback B S hS ψ₁ ψ₂ hV₁ hV₂ hU) (isAlgebraicSpace_yoneda B S hS T') hP hk g
    (by
      rintro _ ⟨τ, rfl⟩
      refine hfoot ⟨pointsMap B S hS _ v τ, ?_⟩
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hg])
  have hwv : w ≫ pullback.snd ψ₁ ψ₂ = v := by
    refine (cancel_mono ι₂).1 ?_
    rw [Category.assoc, ← hkp₂, reassoc_of% hw, hg]
  refine ⟨w ≫ pullback.fst ψ₁ ψ₂, ?_, ?_⟩
  · rw [Category.assoc, ← hkp₁, reassoc_of% hw]
  · rw [Category.assoc, pullback.condition, reassoc_of% hwv]

/-- **Restricting a flat cover to the part over `N`.** In the situation of the fifth paragraph of
the proof of Stacks 0F4B, let `k : V₁ ×_U V₂ ⟶ X₁₂` be an open immersion with projections
`pᵢ : X₁₂ ⟶ Xᵢ`, all points over `V₂` lying in the image of `k`. Let `b : X₂' ⟶ X₂` with a lift
`ι₂'` of `ι₂`, `c : X' ⟶ X₁₂` and a proper `f' : X' ⟶ X₂'` over `b`, through which pairs of points
over `V₂` lift, and `p₀ : E ⟶ X'` with `p₀ ≫ f'` flat, whose image contains the closure of
`c⁻¹ k(pr₁⁻¹ T)`. If every point of `V₂` over `Z` is the second coordinate of a point of
`pr₁⁻¹ T`, and `N ⊆ |X₁|` is an open set containing the closure of `ι₁(T)`, then the open part
`E°` of `E` over `N` is flat over `X₂'`, its image contains the closure of `ψ₂⁻¹ Z`, and its
scheme points over `V₂` come from `V₁`. -/
theorem exists_isFlat_of_isFlat_cover {Y X₁ X₂ X₂' X' E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV₁ : IsAlgebraicSpace B S hS V₁)
    (hV₂ : IsAlgebraicSpace B S hS V₂) (hP : IsAlgebraicSpace B S hS P)
    (hX₂' : IsAlgebraicSpace B S hS X₂')
    (hE : IsAlgebraicSpace B S hS E) {ψ₁ : V₁ ⟶ U} {ψ₂ : V₂ ⟶ U} {π₁ : X₁ ⟶ Y} {π₂ : X₂ ⟶ Y}
    {ι₁ : V₁ ⟶ X₁} {ι₂ : V₂ ⟶ X₂} (hι₂ : IsOpenImmersion B S hS ι₂)
    {k : pullback ψ₁ ψ₂ ⟶ P} (hk : IsOpenImmersion B S hS k) {p₁ : P ⟶ X₁} {p₂ : P ⟶ X₂}
    (hkp₁ : k ≫ p₁ = pullback.fst ψ₁ ψ₂ ≫ ι₁) (hkp₂ : k ≫ p₂ = pullback.snd ψ₁ ψ₂ ≫ ι₂)
    (hpp : p₁ ≫ π₁ = p₂ ≫ π₂)
    (hfoot : pointsMap B S hS P p₂ ⁻¹' Set.range (pointsMap B S hS V₂ ι₂) ⊆
      Set.range (pointsMap B S hS _ k))
    {b : X₂' ⟶ X₂} {ι₂' : V₂ ⟶ X₂'} (hι₂'b : ι₂' ≫ b = ι₂) {c : X' ⟶ P} {f' : X' ⟶ X₂'}
    (hcf : c ≫ p₂ = f' ≫ b) (hf' : IsProper B S hS f') {p₀ : E ⟶ X'}
    (hflat : IsFlat B S hS (p₀ ≫ f'))
    (hlift : ∀ (x : points B S hS P) (y : points B S hS X₂'),
      pointsMap B S hS _ p₂ x = pointsMap B S hS _ b y →
      pointsMap B S hS _ b y ∈ Set.range (pointsMap B S hS V₂ ι₂) →
      ∃ x' : points B S hS X', pointsMap B S hS _ c x' = x ∧ pointsMap B S hS _ f' x' = y)
    (T : Set (points B S hS V₁))
    (hcov : ∀ a ∈ closure (pointsMap B S hS _ c ⁻¹'
        (pointsMap B S hS _ k '' (pointsMap B S hS _ (pullback.fst ψ₁ ψ₂) ⁻¹' T))),
      ∃ a₀ : points B S hS E, pointsMap B S hS _ p₀ a₀ = a)
    (Zs : Set (points B S hS U))
    (hsurj : ∀ z : points B S hS V₂, pointsMap B S hS _ ψ₂ z ∈ Zs →
      ∃ w : points B S hS (pullback ψ₁ ψ₂), pointsMap B S hS _ (pullback.fst ψ₁ ψ₂) w ∈ T ∧
        pointsMap B S hS _ (pullback.snd ψ₁ ψ₂) w = z)
    (Nset : Set (points B S hS X₁)) (hNo : IsOpen Nset)
    (hN : closure (pointsMap B S hS V₁ ι₁ '' T) ⊆ Nset) :
    ∃ (E' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t : E' ⟶ X₂') (r : E' ⟶ X₁),
      IsAlgebraicSpace B S hS E' ∧ IsFlat B S hS t ∧ r ≫ π₁ = t ≫ b ≫ π₂ ∧
      Set.range (pointsMap B S hS E' r) ⊆ Nset ∧
      closure (pointsMap B S hS V₂ ι₂' '' (pointsMap B S hS V₂ ψ₂ ⁻¹' Zs)) ⊆
        Set.range (pointsMap B S hS E' t) ∧
      ∀ (T' : BigFppfOver B S hS) (s : yoneda.obj T' ⟶ E') (v : yoneda.obj T' ⟶ V₂),
        s ≫ t = v ≫ ι₂' → ∃ v₁ : yoneda.obj T' ⟶ V₁, v₁ ≫ ι₁ = s ≫ r ∧ v₁ ≫ ψ₁ = v ≫ ψ₂ := by
  set Eset := pointsMap B S hS _ (p₀ ≫ c ≫ p₁) ⁻¹' Nset with hEset
  set Eo := openSubspaceOfPoints B S hS E Eset
  have hEos : IsOpenSubspace B S hS Eo := isOpenSubspace_openSubspaceOfPoints B S hS hE Eset
    (hNo.preimage (continuous_pointsMap B S hS _))
  have hEorange : Set.range (pointsMap B S hS _ Eo.ι) = Eset :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS Eset
  set Ak := pointsMap B S hS _ k '' (pointsMap B S hS _ (pullback.fst ψ₁ ψ₂) ⁻¹' T)
  refine ⟨Eo.toFunctor, Eo.ι ≫ p₀ ≫ f', Eo.ι ≫ p₀ ≫ c ≫ p₁, hEos.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact isFlat_comp B S hS hEos.1 hE hX₂' _ _
      (isFlat_of_isEtale B S hS (isEtale_ι_of_isOpenSubspace hEos)) hflat
  · simp only [Category.assoc]
    rw [hpp, reassoc_of% hcf]
  · rintro _ ⟨e, rfl⟩
    rw [pointsMap_comp_apply]
    exact hEorange.subset ⟨e, rfl⟩
  · -- the image of `t` contains the closure of `ψ₂⁻¹ Z`
    intro x hx
    obtain ⟨a, ha, rfl⟩ := closure_image_preimage_subset_image_closure_of_lift hX₂' hkp₂ hι₂'b hf'
      hlift T Zs hsurj hx
    obtain ⟨a₀, ha₀⟩ := hcov a ha
    -- `a₀` lies over `N`
    have hcN : pointsMap B S hS _ (c ≫ p₁) '' closure (pointsMap B S hS _ c ⁻¹' Ak) ⊆ Nset := by
      refine (image_closure_subset_closure_image (continuous_pointsMap B S hS _)).trans
        ((closure_mono ?_).trans hN)
      rintro _ ⟨a', ⟨w, hwT, hw⟩, rfl⟩
      refine ⟨_, hwT, ?_⟩
      rw [pointsMap_comp_apply, ← hw, ← pointsMap_comp_apply, ← pointsMap_comp_apply, hkp₁,
        pointsMap_comp_apply]
    have ha₀E : a₀ ∈ Eset := by
      rw [hEset, Set.mem_preimage, pointsMap_comp_apply, ha₀]
      exact hcN ⟨a, ha, rfl⟩
    obtain ⟨e, he⟩ : a₀ ∈ Set.range (pointsMap B S hS _ Eo.ι) := hEorange ▸ ha₀E
    refine ⟨e, ?_⟩
    rw [pointsMap_comp_apply, he, pointsMap_comp_apply, ha₀]
  · -- scheme points over `V₂` come from `V₁`
    intro T' s v hsv
    have hs' : (s ≫ Eo.ι ≫ p₀ ≫ c) ≫ p₂ = v ≫ ι₂ := by
      simp only [Category.assoc, hcf, reassoc_of% hsv, hι₂'b]
    simpa only [Category.assoc] using exists_lift_fst_of_comp_eq hU hV₁ hV₂ hP hι₂ hk hkp₁ hkp₂
      hfoot (s ≫ Eo.ι ≫ p₀ ≫ c) v hs'

/-- **Points of `V₂` over `Z` lift to `V₁ ×_U V₂`.** If `f = j ≫ ψ₁` is an isomorphism over the
reduced closed subspace on `Z`, every point of `V₂` over `Z` is the second coordinate of a point of
`V₁ ×_U V₂` whose first coordinate lies in `j(f⁻¹ Z)`. -/
theorem exists_pullback_point_of_isIso_fromPreimage (hU : IsAlgebraicSpace B S hS U)
    (Zs : Set (points B S hS U)) (hZs : IsClosed Zs) {ψ₁ : V₁ ⟶ U} {ψ₂ : V₂ ⟶ U}
    {j : U₁ ⟶ V₁}
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU Zs hZs).fromPreimage (j ≫ ψ₁)))
    (z : points B S hS V₂) (hz : pointsMap B S hS _ ψ₂ z ∈ Zs) :
    ∃ w : points B S hS (pullback ψ₁ ψ₂),
      pointsMap B S hS _ (pullback.fst ψ₁ ψ₂) w ∈
        pointsMap B S hS U₁ j '' (pointsMap B S hS U₁ (j ≫ ψ₁) ⁻¹' Zs) ∧
      pointsMap B S hS _ (pullback.snd ψ₁ ψ₂) w = z := by
  set Zc := reducedClosedSubspace B S hS U hU Zs hZs
  obtain ⟨y, hy⟩ : pointsMap B S hS _ ψ₂ z ∈ Set.range (pointsMap B S hS _ Zc.ι) := by
    rwa [range_pointsMap_ι_reducedClosedSubspace B S hS U hU Zs hZs]
  obtain ⟨u, rfl⟩ := pointsMap_surjective_of_isIso B S hS (Zc.fromPreimage (j ≫ ψ₁)) y
  have hu : pointsMap B S hS _ (j ≫ ψ₁) (pointsMap B S hS _ (Zc.preimage (j ≫ ψ₁)).ι u) =
      pointsMap B S hS _ ψ₂ z := by
    rw [← hy, ← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
  obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback ψ₁ ψ₂)
    (pointsMap B S hS _ j (pointsMap B S hS _ (Zc.preimage (j ≫ ψ₁)).ι u)) z
    (by rwa [← pointsMap_comp_apply])
  refine ⟨w, ?_, hw₂⟩
  rw [hw₁]
  exact ⟨_, by rwa [Set.mem_preimage, hu], rfl⟩

/-- **A flat cover near the closure of `f⁻¹ Z₁`** (the fifth
paragraph of the proof of Stacks 0F4B). Let `π₁ : X₁ ⟶ Y` and `π₂ : X₂ ⟶ Y` be proper over a
quasi-compact and quasi-separated `Y`, `ιᵢ : Vᵢ ⟶ Xᵢ` open immersions, `ψᵢ : Vᵢ ⟶ U` proper with
`ψᵢ ≫ q = ιᵢ ≫ πᵢ` and `q` separated and quasi-compact, `V₂` quasi-compact, and `j : U₁ ⟶ V₁` an
open immersion such that `f = j ≫ ψ₁` is étale and an isomorphism over the reduced closed
subspace on a closed set `Z ⊆ |U|`. Let `N ⊆ |X₁|` be open and contain the closure of `f⁻¹ Z`.

Then there are a proper modification `b : X₂' ⟶ X₂` (a `V₂`-admissible blowup), a lift `ι₂'` of
`ι₂`, and a flat morphism `t : E ⟶ X₂'` with `r : E ⟶ X₁` over `Y` landing in `N`, such that
the image of `t` contains the closure of `ψ₂⁻¹ Z` and every scheme point of `E` lying over `V₂`
comes, through `r`, from a point of `V₁` with the same image in `U`. -/
theorem exists_isFlat_cover_closure_of_isEtale (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y X₁ X₂ : AlgebraicSpaces B S hS} (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hU : IsAlgebraicSpace B S hS U)
    (hV₁ : IsAlgebraicSpace B S hS V₁) (hV₂ : IsAlgebraicSpace B S hS V₂)
    (hU₁ : IsAlgebraicSpace B S hS U₁) {ψ₁ : V₁ ⟶ U} {ψ₂ : V₂ ⟶ U} {q : U ⟶ Y.1}
    {π₁ : X₁.1 ⟶ Y.1} {π₂ : X₂.1 ⟶ Y.1} {ι₁ : V₁ ⟶ X₁.1} {ι₂ : V₂ ⟶ X₂.1} {j : U₁ ⟶ V₁}
    (hψ₁ : IsProper B S hS ψ₁) (hψ₂ : IsProper B S hS ψ₂) (hq : IsSeparated B S hS q)
    (hqc : IsQuasiCompact B S hS q) (hπ₁ : IsProper B S hS π₁) (hπ₂ : IsProper B S hS π₂)
    (hι₁ : IsOpenImmersion B S hS ι₁) (hι₂ : IsOpenImmersion B S hS ι₂)
    (h₁ : ψ₁ ≫ q = ι₁ ≫ π₁) (h₂ : ψ₂ ≫ q = ι₂ ≫ π₂) (hV₂qc : IsQuasiCompactSpace B S hS V₂)
    (hj : IsOpenImmersion B S hS j) (hf : IsEtale B S hS (j ≫ ψ₁))
    (Zs : Set (points B S hS U)) (hZs : IsClosed Zs)
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU Zs hZs).fromPreimage (j ≫ ψ₁)))
    (Nset : Set (points B S hS X₁.1)) (hNo : IsOpen Nset)
    (hN : closure (pointsMap B S hS U₁ (j ≫ ι₁) '' (pointsMap B S hS U₁ (j ≫ ψ₁) ⁻¹' Zs)) ⊆ Nset) :
    ∃ (X₂' : AlgebraicSpaces B S hS) (b : X₂' ⟶ X₂) (ι₂' : V₂ ⟶ X₂'.1)
      (E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t : E ⟶ X₂'.1) (r : E ⟶ X₁.1),
      IsAlgebraicSpace B S hS E ∧ IsProper B S hS b.hom ∧ ι₂' ≫ b.hom = ι₂ ∧
      IsOpenImmersion B S hS ι₂' ∧ IsFlat B S hS t ∧ r ≫ π₁ = t ≫ b.hom ≫ π₂ ∧
      Set.range (pointsMap B S hS E r) ⊆ Nset ∧
      closure (pointsMap B S hS V₂ ι₂' '' (pointsMap B S hS V₂ ψ₂ ⁻¹' Zs)) ⊆
        Set.range (pointsMap B S hS E t) ∧
      ∀ (T : BigFppfOver B S hS) (s : yoneda.obj T ⟶ E) (v : yoneda.obj T ⟶ V₂),
        s ≫ t = v ≫ ι₂' → ∃ v₁ : yoneda.obj T ⟶ V₁, v₁ ≫ ι₁ = s ≫ r ∧ v₁ ≫ ψ₁ = v ≫ ψ₂ := by
  have : Mono ι₂ := mono_of_presheaf_isOpenImmersion hι₂
  obtain ⟨P, k, p₁, p₂, hP, hk, -, hkp₁, hkp₂, hpp, hp₂, hfoot⟩ :=
    exists_isOpenImmersion_denseRange_closure_pullback Y.2 hU hV₁ hV₂ X₁.2 X₂.2 hψ₁ hψ₂ hq hqc
      hπ₁ hπ₂.1 hι₁ hι₂ h₁ h₂
  set T := pointsMap B S hS U₁ j '' (pointsMap B S hS U₁ (j ≫ ψ₁) ⁻¹' Zs) with hTdef
  have hT : IsClosed T := isClosed_image_preimage_of_isIso_fromPreimage hV₁ hU hU₁ hψ₁ j Zs hZs hiso
  obtain ⟨A, hArange, het⟩ := exists_closedSubspace_isEtaleAt_of_closure_pullback hU hV₁ hV₂ X₂.2
    hU₁ hP hj hf hι₂ hk hkp₂ hfoot T hT (Set.image_subset_range _ _)
  -- quasi-compactness and quasi-separatedness
  have hqcqs : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
      (hY : IsAlgebraicSpace B S hS Y) (g : X ⟶ Y), IsProper B S hS g →
      IsQuasiCompactSpace B S hS Y → IsAbsolutelyQuasiSeparated B S hS hZ Y →
      IsQuasiCompactSpace B S hS X ∧ IsAbsolutelyQuasiSeparated B S hS hZ X :=
    fun hX hY _ hg hqc hqs =>
      ⟨(hg.isFiniteType.2 _ hY hqc (𝟙 _)).of_iso B S hS (asIso (pullback.snd (𝟙 _) _)),
        isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX hqs
          (isQuasiSeparated_of_isSeparated B S hS hg.isSeparated)⟩
  obtain ⟨hX₂qc, hX₂qs⟩ := hqcqs X₂.2 Y.2 _ hπ₂ hYqc hYqs
  obtain ⟨hPqc, hPqs⟩ := hqcqs hP X₂.2 _ hp₂ hX₂qc hX₂qs
  have hVqc : IsQuasiCompactSpace B S hS (Subfunctor.range ι₂).toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (asIso (Subfunctor.toRange ι₂)) hV₂qc
  obtain ⟨X₂', b, ι', X', E, c, f', p₀, hX', hE, hb, hι'b, hι'o, hcf, hf'P, hflat, hlift, hcov⟩ :=
    exists_isFlat_cover_closure_of_isEtaleAt hZ (X := ⟨P, hP⟩) hPqc hPqs hX₂qc hX₂qs
      (ObjectProperty.homMk p₂) hp₂
      ⟨Subfunctor.range ι₂, isOpenSubspace_subfunctorRange B S hS hV₂ hι₂⟩ hVqc A het
  -- the lift of `ι₂`
  have hι₂' : (Subfunctor.toRange ι₂ ≫ ι') ≫ b.hom = ι₂ := by
    rw [Category.assoc, hι'b, Subfunctor.toRange_ι]
  have hι₂'o : IsOpenImmersion B S hS (Subfunctor.toRange ι₂ ≫ ι') :=
    isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) hι'o
  obtain ⟨E', t, r, hE', ht, hr, hrN, hcl, hfac⟩ := exists_isFlat_of_isFlat_cover hU hV₁ hV₂ hP
    X₂'.2 hE hι₂ hk hkp₁ hkp₂ hpp hfoot hι₂' hcf hf'P hflat
    (fun x y hxy hy => hlift x y hxy (by rwa [← subspacePointSet_range] at hy)) T
    (by rwa [← hArange]) Zs (exists_pullback_point_of_isIso_fromPreimage hU Zs hZs hiso) Nset hNo
    (by rwa [hTdef, ← Set.image_comp, ← pointsMap_comp])
  exact ⟨X₂', b, _, E', t, r, hE', hb, hι₂', hι₂'o, ht, hr, hrN, hcl, hfac⟩

end AlgebraicGeometry.Space

end
