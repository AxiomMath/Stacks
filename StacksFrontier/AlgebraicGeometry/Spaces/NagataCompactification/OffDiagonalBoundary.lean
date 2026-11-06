module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.OffDiagonalBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.OffDiagonalStepOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic

/-!
# The off-diagonal of an étale extension and the boundary

Let `π : X ⟶ Y` be separated, `ι : V ⟶ X` an open immersion and `ψ : V ⟶ U` a proper morphism
over `Y`. Let `j : U₁ ⟶ V` be an open immersion such that `f = j ≫ ψ` is étale and is an
isomorphism over the reduced closed subspace of `U` on a closed set `Z`; this is the situation
of the repaired proof of Stacks 0F4B, with `V = V₁` the open of the compactification `X = X₁`
of `U₁` on which `f` extends to a proper `ψ = ψ₁`, and `Z = Z₁` the complement of `U₂`.

Let `O` be the image in `X ×_Y X` of the complement of the diagonal in `U₁ ×_U U₁` (the
off-diagonal points) and `T` the image in `X` of `f⁻¹ Z`. This file proves the facts about
`O` and `T` which the repair needs before any blowup:

* `T` is closed in `V`, since `f⁻¹ Z ≅ Z` is proper over the separated `ψ` (Stacks 04NX);
* `O` is closed in the open set of points with both coordinates in `U₁`;
* no point of `O` has a coordinate in the closure of `T`;
* (Step 1) a point of the closure of `O` with both coordinates in the closure of `T` has both
  coordinates on the boundary `X ∖ V`.

The last statement rests on Lemma 1 of the repair
(`AlgebraicGeometry.Space.mem_range_of_mem_closure_of_fst_mem`): a point of the closure of `O`
with a coordinate in `V` comes from `V ×_U V`.

## Main results

* `AlgebraicGeometry.Space.mem_range_diagonal_of_mem_reducedClosedSubspace`: a point of
  `U₁ ×_U U₁` with a coordinate over `Z` lies on the diagonal.
* `AlgebraicGeometry.Space.closure_image_inter_range_subset`: `T` is closed in `V`.
* `AlgebraicGeometry.Space.mem_offDiagonal_of_mem_closure`: `O` is closed among the points with
  both coordinates in `U₁`.
* `AlgebraicGeometry.Space.notMem_range_of_mem_closure_offDiagonal`: Step 1.
* `AlgebraicGeometry.Space.fst_notMem_closure_of_mem_offDiagonal`,
  `AlgebraicGeometry.Space.snd_notMem_closure_of_mem_offDiagonal`: the coordinates of `O` avoid
  the closure of `T`.

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_OffDiagonalBoundary :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_OffDiagonalBoundary
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Over a closed subset where `f` is an isomorphism, `U₁ ×_U U₁` is the diagonal.** Let
`f : U₁ ⟶ U` be a morphism which is an isomorphism over the reduced closed subspace of `U` on a
closed set `Z`. A point of `U₁ ×_U U₁` whose first coordinate maps into `Z` lies on the
diagonal. -/
theorem mem_range_diagonal_of_mem_reducedClosedSubspace {U₁ U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (f : U₁ ⟶ U) (Z : Set (points B S hS U)) (hZ : IsClosed Z)
    (hf : IsIso ((reducedClosedSubspace B S hS U hU Z hZ).fromPreimage f))
    (k : points B S hS (pullback f f))
    (hk : pointsMap B S hS U₁ f (pointsMap B S hS _ (pullback.fst f f) k) ∈ Z) :
    k ∈ Set.range (pointsMap B S hS U₁ (pullback.diagonal f)) := by
  classical
  obtain ⟨p, rfl⟩ := Quot.exists_rep k
  obtain ⟨c, cont, tb, v⟩ := p
  let T : BigFppfOver B S hS := Over.mk (⟨tb⟩ : B.obj cont ⟶ B.obj hS)
  set m : yoneda.obj T ⟶ pullback f f := yonedaEquiv.symm v with hm
  set a := m ≫ pullback.fst f f
  set b := m ≫ pullback.snd f f
  have hab : a ≫ f = b ≫ f := by simp only [a, b, Category.assoc, pullback.condition]
  have hmem := (FieldValuedPoint.mem_obj_reducedClosedSubspace_iff_class_mem B S hS hU Z hZ
    ⟨c, cont, tb, yonedaEquiv (a ≫ f)⟩).2 (by
      convert hk using 1
      rw [pointsMap_class, pointsMap_class]
      congr 1
      show (⟨c, cont, tb, yonedaEquiv (a ≫ f)⟩ : FieldValuedPoint B S hS U) =
        ⟨c, cont, tb, f.app _ ((pullback.fst f f).app _ v)⟩
      rw [yonedaEquiv_comp, yonedaEquiv_comp, hm, Equiv.apply_symm_apply])
  have hbij : Function.Bijective ((Subfunctor.fromPreimage
      (reducedClosedSubspace B S hS U hU Z hZ) f).app (op T)) :=
    (isIso_iff_bijective _).1 inferInstance
  have ha : f.app (op T) (yonedaEquiv a) = yonedaEquiv (a ≫ f) := (yonedaEquiv_comp a f).symm
  have hb : f.app (op T) (yonedaEquiv b) = yonedaEquiv (a ≫ f) := by
    rw [hab]; exact (yonedaEquiv_comp b f).symm
  have hyab : yonedaEquiv a = yonedaEquiv b := by
    have := @hbij.1 ⟨yonedaEquiv a, show f.app (op T) (yonedaEquiv a) ∈ _ from ha ▸ hmem⟩
      ⟨yonedaEquiv b, show f.app (op T) (yonedaEquiv b) ∈ _ from hb ▸ hmem⟩
      (Subtype.ext (ha.trans hb.symm))
    exact congrArg Subtype.val this
  have hab' : a = b := yonedaEquiv.injective hyab
  have hma : a ≫ pullback.diagonal f = m := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hab']
  refine ⟨(⟨c, cont, tb, yonedaEquiv a⟩ : FieldValuedPoint B S hS U₁).class B S hS U₁, ?_⟩
  rw [pointsMap_class]
  congr 1
  show (⟨c, cont, tb, (pullback.diagonal f).app _ (yonedaEquiv a)⟩ :
    FieldValuedPoint B S hS _) = _
  rw [← yonedaEquiv_comp, hma, hm, Equiv.apply_symm_apply]

/-- **`U₁ ×_U U₁` inside `U₁ ×_U V`.** For `j : U₁ ⟶ V`, `ψ : V ⟶ U` and `g : W ⟶ U`, the
comparison `W ×_U U₁ ⟶ W ×_U V` is the base change of `j` along the second projection. -/
theorem isPullback_pullbackMap_snd {U₁ V U W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : U₁ ⟶ V)
    (ψ : V ⟶ U) (g : W ⟶ U) :
    IsPullback (pullback.map g (j ≫ ψ) g ψ (𝟙 W) j (𝟙 U) (by simp) (by simp))
      (pullback.snd g (j ≫ ψ)) (pullback.snd g ψ) j :=
  IsPullback.of_right (by simpa using IsPullback.of_hasPullback g (j ≫ ψ)) (by simp)
    (IsPullback.of_hasPullback g ψ)

/-- The comparison `pullback.map` along two monomorphisms is a monomorphism. -/
theorem mono_pullbackMap {C : Type*} [Category C] {W X Y₁ Y₂ Z T : C} [HasPullbacks C]
    (f₁ : W ⟶ T) (f₂ : X ⟶ T) (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z) (i₁ : W ⟶ Y₁) (i₂ : X ⟶ Y₂)
    (i₃ : T ⟶ Z) [Mono i₁] [Mono i₂] (h₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (h₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    Mono (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ h₁ h₂) := by
  refine ⟨fun a b hab => ?_⟩
  apply pullback.hom_ext
  · rw [← cancel_mono i₁]
    simpa using hab =≫ pullback.fst g₁ g₂
  · rw [← cancel_mono i₂]
    simpa using hab =≫ pullback.snd g₁ g₂


/-- Open immersions of presheaves are stable under base change. -/
theorem isOpenImmersion_snd_of_isPullback {P X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : IsOpenImmersion B S hS f) : IsOpenImmersion B S hS snd :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sq hf

/-- The map on points of an open immersion of presheaves is an open embedding. -/
private theorem isOpenEmbedding_pointsMap_of_isOpenImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} (hf : IsOpenImmersion B S hS f) :
    Topology.IsOpenEmbedding (pointsMap B S hS F f) :=
  have : Mono f := mono_of_presheaf_isOpenImmersion hf
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
    (pointsMap_injective_of_mono B S hS f) (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hf)

section Restriction

variable {V U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : U₁ ⟶ V) (ψ : V ⟶ U)

/-- **`U₁ ×_U U₁` is open in `V ×_U V`.** For an open immersion `j : U₁ ⟶ V` and `ψ : V ⟶ U`,
the comparison `U₁ ×_U U₁ ⟶ V ×_U V` is an open immersion. -/
theorem isOpenImmersion_pullbackMap_of_isOpenImmersion (hj : IsOpenImmersion B S hS j) :
    IsOpenImmersion B S hS
      (pullback.map (j ≫ ψ) (j ≫ ψ) ψ ψ j j (𝟙 U) (by simp) (by simp)) := by
  have hA : IsOpenImmersion B S hS
      (pullback.map (j ≫ ψ) ψ ψ ψ j (𝟙 V) (𝟙 U) (by simp) (by simp)) :=
    isOpenImmersion_snd_of_isPullback (isPullback_pullbackMap_ι_fst B S hS j ψ).flip hj
  have hB : IsOpenImmersion B S hS
      (pullback.map (j ≫ ψ) (j ≫ ψ) (j ≫ ψ) ψ (𝟙 U₁) j (𝟙 U) (by simp) (by simp)) :=
    isOpenImmersion_snd_of_isPullback (isPullback_pullbackMap_snd j ψ (j ≫ ψ)).flip hj
  have he : pullback.map (j ≫ ψ) (j ≫ ψ) (j ≫ ψ) ψ (𝟙 U₁) j (𝟙 U) (by simp) (by simp) ≫
      pullback.map (j ≫ ψ) ψ ψ ψ j (𝟙 V) (𝟙 U) (by simp) (by simp) =
      pullback.map (j ≫ ψ) (j ≫ ψ) ψ ψ j j (𝟙 U) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp
  rw [← he]
  exact isOpenImmersion_comp B S hS _ _ hB hA

/-- **Points of `V ×_U V` with both coordinates in `U₁` come from `U₁ ×_U U₁`.** -/
theorem mem_range_pullbackMap_of_mem_range (v : points B S hS (pullback ψ ψ))
    (h₁ : pointsMap B S hS _ (pullback.fst ψ ψ) v ∈ Set.range (pointsMap B S hS U₁ j))
    (h₂ : pointsMap B S hS _ (pullback.snd ψ ψ) v ∈ Set.range (pointsMap B S hS U₁ j)) :
    v ∈ Set.range (pointsMap B S hS _
      (pullback.map (j ≫ ψ) (j ≫ ψ) ψ ψ j j (𝟙 U) (by simp) (by simp))) := by
  have hA := preimage_image_pointsMap_of_isPullback B S hS
    (isPullback_pullbackMap_ι_fst B S hS j ψ).flip Set.univ
  have hB := preimage_image_pointsMap_of_isPullback B S hS
    (isPullback_pullbackMap_snd j ψ (j ≫ ψ)).flip Set.univ
  rw [Set.image_univ, Set.preimage_univ, Set.image_univ] at hA hB
  obtain ⟨v₁, rfl⟩ : v ∈ Set.range (pointsMap B S hS _
      (pullback.map (j ≫ ψ) ψ ψ ψ j (𝟙 V) (𝟙 U) (by simp) (by simp))) := by
    rw [← hA]; exact h₁
  obtain ⟨k, rfl⟩ : v₁ ∈ Set.range (pointsMap B S hS _
      (pullback.map (j ≫ ψ) (j ≫ ψ) (j ≫ ψ) ψ (𝟙 U₁) j (𝟙 U) (by simp) (by simp))) := by
    rw [← hB]
    show v₁ ∈ pointsMap B S hS _ (pullback.snd (j ≫ ψ) ψ) ⁻¹' _
    rw [← pointsMap_comp_apply] at h₂
    simpa using h₂
  refine ⟨k, ?_⟩
  rw [← pointsMap_comp_apply]
  congr 1
  apply pullback.hom_ext <;> simp

end Restriction

/-- **The image of the preimage of a closed set under an étale extension is closed.** Let
`ψ : V ⟶ U` be proper and `j : U₁ ⟶ V` such that `f = j ≫ ψ` is an isomorphism over the reduced
closed subspace of `U` on a closed set `Z`. Then the image in `V` of `f⁻¹ Z` is closed: the
closed subspace `f⁻¹ Z ≅ Z` of `U₁` is proper over `U`, hence over the separated `ψ` (Stacks
04NX). -/
theorem isClosed_image_preimage_of_isIso_fromPreimage {V U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hU₁ : IsAlgebraicSpace B S hS U₁) {ψ : V ⟶ U} (hψ : IsProper B S hS ψ) (j : U₁ ⟶ V)
    (Z : Set (points B S hS U)) (hZ : IsClosed Z)
    (hf : IsIso ((reducedClosedSubspace B S hS U hU Z hZ).fromPreimage (j ≫ ψ))) :
    IsClosed (pointsMap B S hS U₁ j '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Z)) := by
  set Zc := reducedClosedSubspace B S hS U hU Z hZ
  have hZc := isClosedSubspace_reducedClosedSubspace B S hS U hU Z hZ
  have hP := isClosedSubspace_preimage B S hS (j ≫ ψ) Zc hU hU₁ hZc
  have hcomp : ((Zc.preimage (j ≫ ψ)).ι ≫ j) ≫ ψ = Zc.fromPreimage (j ≫ ψ) ≫ Zc.ι := by
    rw [Category.assoc, Subfunctor.fromPreimage_ι]
  have hprop : IsProper B S hS ((Zc.preimage (j ≫ ψ)).ι ≫ j) := by
    refine isProper_of_comp_of_isSeparated B S hS hP.1 hV hU _ ψ ?_ hψ.1
    rw [hcomp]
    exact isProper_comp B S hS hP.1 hZc.1 hU _ _ (isProper_of_isIso B S hS _)
      (isProper_of_isClosedImmersion B S hS hZc.1 hU _ hZc.2)
  have hcl := isClosed_range_pointsMap_of_isProper B S hS hV hprop
  convert hcl using 1
  rw [pointsMap_comp B S hS _ (Zc.preimage (j ≫ ψ)).ι j, Set.range_comp,
    show Set.range (pointsMap B S hS _ (Zc.preimage (j ≫ ψ)).ι) =
      subspacePointSet B S hS U₁ (Zc.preimage (j ≫ ψ)) from rfl, subspacePointSet_preimage,
    show subspacePointSet B S hS U Zc = Z from
      range_pointsMap_ι_reducedClosedSubspace B S hS U hU Z hZ]

/-- **`f⁻¹ Z` is closed in `V`, seen in `X`.** In the situation of
`AlgebraicGeometry.Space.isClosed_image_preimage_of_isIso_fromPreimage`, for an open immersion
`ι : V ⟶ X` the points of the closure in `X` of the image of `f⁻¹ Z` which lie in `V` lie in that
image. -/
theorem closure_image_inter_range_subset {X V U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hU₁ : IsAlgebraicSpace B S hS U₁) {ψ : V ⟶ U} (hψ : IsProper B S hS ψ) (j : U₁ ⟶ V)
    {ι : V ⟶ X} (hι : IsOpenImmersion B S hS ι)
    (Z : Set (points B S hS U)) (hZ : IsClosed Z)
    (hf : IsIso ((reducedClosedSubspace B S hS U hU Z hZ).fromPreimage (j ≫ ψ))) :
    closure (pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Z)) ∩
        Set.range (pointsMap B S hS V ι) ⊆
      pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Z) := by
  have hιemb := isOpenEmbedding_pointsMap_of_isOpenImmersion hι
  have hcl := isClosed_image_preimage_of_isIso_fromPreimage hV hU hU₁ hψ j Z hZ hf
  rw [pointsMap_comp, Set.image_comp]
  rintro _ ⟨hx, y, rfl⟩
  refine ⟨y, ?_, rfl⟩
  rw [← hcl.closure_eq, hιemb.isInducing.closure_eq_preimage_closure_image]
  exact hx

variable (B S hS) in
/-- **`V ×_U V` embeds into `X ×_Y X`.** For `ψ : V ⟶ U` proper over `Y`, `π` separated and
`ι : V ⟶ X` an open immersion, the map on points of `V ×_U V ⟶ V ×_Y X ⟶ X ×_Y X` is an
embedding: the first map is proper and a monomorphism, so a closed embedding, and the second is
an open immersion. -/
theorem isEmbedding_pointsMap_pullbackMap_comp {X Y V U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {ψ : V ⟶ U} {ι : V ⟶ X} {q : U ⟶ Y} {π : X ⟶ Y} (hψ : IsProper B S hS ψ)
    (hπ : IsSeparated B S hS π) (hι : IsOpenImmersion B S hS ι) (h : ψ ≫ q = ι ≫ π) :
    Topology.IsEmbedding (pointsMap B S hS _
      (pullback.map ψ ψ (ι ≫ π) π (𝟙 V) ι q (by simp [h]) h ≫
        pullback.map (ι ≫ π) π π π ι (𝟙 X) (𝟙 Y) (by simp) (by simp))) := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  have := mono_pullbackMap ψ ψ (ι ≫ π) π (𝟙 V) ι q (by simp [h]) h
  have := mono_pullbackMap (ι ≫ π) π π π ι (𝟙 X) (𝟙 Y) (by simp) (by simp)
  have hacl : Topology.IsClosedEmbedding (pointsMap B S hS _
      (pullback.map ψ ψ (ι ≫ π) π (𝟙 V) ι q (by simp [h]) h)) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (continuous_pointsMap B S hS _) (pointsMap_injective_of_mono B S hS _)
      (isClosedMap_pointsMap_of_pullback_fst_id B S hS _
        ((isProper_pullbackMap_of_isProper B S hS hV hU hX hY hψ hπ h).2.2 _
          (isAlgebraicSpace_pullback B S hS (ι ≫ π) π hV hX hY) (𝟙 _)))
  have hj₁ := isOpenEmbedding_pointsMap_of_isOpenImmersion
    (isOpenImmersion_snd_of_isPullback (isPullback_pullbackMap_ι_fst B S hS ι π).flip hι)
  rw [pointsMap_comp]
  exact hj₁.isEmbedding.comp hacl.isEmbedding

/-- If `e ≫ p = c ≫ ι` with `ι` a monomorphism, a point of the source of `c` whose image under `e`
and `p` is the image of `x` under `d ≫ ι` has the same image under `c` as `x` has under `d`. -/
private theorem pointsMap_eq_of_pointsMap_comp_eq {P Q V W X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {ι : V ⟶ X} [Mono ι] {d : P ⟶ V} {c : Q ⟶ V} {p : W ⟶ X} {e : Q ⟶ W}
    (he : e ≫ p = c ≫ ι) {x : points B S hS P} {v : points B S hS Q}
    (hx : pointsMap B S hS _ (d ≫ ι) x = pointsMap B S hS _ p (pointsMap B S hS _ e v)) :
    pointsMap B S hS _ d x = pointsMap B S hS _ c v :=
  pointsMap_injective_of_mono B S hS ι (by
    rw [← pointsMap_comp_apply, hx, ← pointsMap_comp_apply, he, pointsMap_comp_apply])

section StepOne

-- Instance search for `Mono (j ≫ ψ)` (the simp lemma's side condition) times out.
attribute [-simp] pullbackSymmetry_hom_of_mono_eq

variable {X Y : AlgebraicSpaces B S hS} {π : X ⟶ Y} {V U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {ι : V ⟶ X.1} {ψ : V ⟶ U} {q : U ⟶ Y.1} {j : U₁ ⟶ V}
  {ρ : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π.hom π.hom}
  (hρ₁ : ρ ≫ pullback.fst π.hom π.hom = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι)
  (hρ₂ : ρ ≫ pullback.snd π.hom π.hom = pullback.snd (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι)

include hρ₁ hρ₂

/-- The comparison `U₁ ×_U U₁ ⟶ X ×_Y X` factors through `V ×_U V ⟶ V ×_Y X ⟶ X ×_Y X`. -/
theorem eq_pullbackMap_comp_of_fst_snd (h : ψ ≫ q = ι ≫ π.hom) :
    ρ = pullback.map (j ≫ ψ) (j ≫ ψ) ψ ψ j j (𝟙 U) (by simp) (by simp) ≫
      pullback.map ψ ψ (ι ≫ π.hom) π.hom (𝟙 V) ι q (by simp [h]) h ≫
        pullback.map (ι ≫ π.hom) π.hom π.hom π.hom ι (𝟙 X.1) (𝟙 Y.1) (by simp) (by simp) := by
  apply pullback.hom_ext
  · rw [hρ₁]; simp
  · rw [hρ₂]; simp

/-- The comparison `U₁ ×_U U₁ ⟶ X ×_Y X` is a monomorphism when `j` and `ι` are. -/
theorem mono_of_fst_snd [Mono j] [Mono ι] : Mono ρ := by
  refine ⟨fun g g' hgg => ?_⟩
  apply pullback.hom_ext
  · rw [← cancel_mono (j ≫ ι)]
    simpa [hρ₁] using hgg =≫ pullback.fst π.hom π.hom
  · rw [← cancel_mono (j ≫ ι)]
    simpa [hρ₂] using hgg =≫ pullback.snd π.hom π.hom

/-- **The off-diagonal points are symmetric.** The swap of `X ×_Y X` maps the image of the
complement of the diagonal of `U₁ ×_U U₁` into itself. -/
theorem pointsMap_pullbackSymmetry_mem_offDiagonal {w : points B S hS (pullback π.hom π.hom)}
    (hw : w ∈ pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ) :
    pointsMap B S hS _ (pullbackSymmetry π.hom π.hom).hom w ∈ pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ := by
  obtain ⟨k, hk, rfl⟩ := hw
  have hσρ : (pullbackSymmetry (j ≫ ψ) (j ≫ ψ)).hom ≫ ρ =
      ρ ≫ (pullbackSymmetry π.hom π.hom).hom := by
    apply pullback.hom_ext
    · simp [hρ₁, hρ₂]
    · simp [hρ₁, hρ₂]
  have hσσ : (pullbackSymmetry (j ≫ ψ) (j ≫ ψ)).hom ≫ (pullbackSymmetry (j ≫ ψ) (j ≫ ψ)).hom =
      𝟙 _ := by apply pullback.hom_ext <;> simp
  have hσΔ : pullback.diagonal (j ≫ ψ) ≫ (pullbackSymmetry (j ≫ ψ) (j ≫ ψ)).hom =
      pullback.diagonal (j ≫ ψ) := by apply pullback.hom_ext <;> simp
  refine ⟨pointsMap B S hS _ (pullbackSymmetry (j ≫ ψ) (j ≫ ψ)).hom k, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    apply hk
    refine ⟨u, ?_⟩
    have := congrArg (pointsMap B S hS _ (pullbackSymmetry (j ≫ ψ) (j ≫ ψ)).hom) hu
    rwa [← pointsMap_comp_apply, hσΔ, ← pointsMap_comp_apply, hσσ, pointsMap_id] at this
  · rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hσρ]

variable (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
  (hψ : IsProper B S hS ψ) (hπ : IsSeparated B S hS π.hom) (hι : IsOpenImmersion B S hS ι)
  (h : ψ ≫ q = ι ≫ π.hom)

include hV hU hψ hπ hι h in
/-- **Lemma 1 of the repaired proof of Stacks 0F4B, for the off-diagonal.** A point in the closure
of the off-diagonal points whose first coordinate lies in `V` comes from `V ×_U V`. -/
theorem mem_range_of_mem_closure_offDiagonal_of_fst_mem {w : points B S hS (pullback π.hom π.hom)}
    (hw : w ∈ closure (pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ))
    (hw₁ : pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∈ Set.range (pointsMap B S hS V ι)) :
    w ∈ Set.range (pointsMap B S hS _
      (pullback.map ψ ψ (ι ≫ π.hom) π.hom (𝟙 V) ι q (by simp [h]) h ≫
        pullback.map (ι ≫ π.hom) π.hom π.hom π.hom ι (𝟙 X.1) (𝟙 Y.1) (by simp) (by simp))) := by
  refine mem_range_of_mem_closure_of_fst_mem B S hS hV hU X.2 Y.2 hψ hπ hι h ?_ hw hw₁
  rintro _ ⟨k, -, rfl⟩
  refine ⟨pointsMap B S hS _
    (pullback.map (j ≫ ψ) (j ≫ ψ) ψ ψ j j (𝟙 U) (by simp) (by simp)) k, ?_⟩
  rw [eq_pullbackMap_comp_of_fst_snd hρ₁ hρ₂ h, ← pointsMap_comp_apply]

include hV hU hψ hπ hι h in
/-- **Lemma 1 for the second coordinate.** A point in the closure of the off-diagonal points
whose second coordinate lies in `V` comes from `V ×_U V`; this is the first-coordinate form
applied after the swap of `X ×_Y X`, which preserves both sets. -/
theorem mem_range_of_mem_closure_offDiagonal_of_snd_mem {w : points B S hS (pullback π.hom π.hom)}
    (hw : w ∈ closure (pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ))
    (hw₂ : pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∈ Set.range (pointsMap B S hS V ι)) :
    w ∈ Set.range (pointsMap B S hS _
      (pullback.map ψ ψ (ι ≫ π.hom) π.hom (𝟙 V) ι q (by simp [h]) h ≫
        pullback.map (ι ≫ π.hom) π.hom π.hom π.hom ι (𝟙 X.1) (𝟙 Y.1) (by simp) (by simp))) := by
  set σ := (pullbackSymmetry π.hom π.hom).hom
  have hσσ : σ ≫ σ = 𝟙 _ := by apply pullback.hom_ext <;> simp [σ]
  have hσw : pointsMap B S hS _ σ w ∈ closure (pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ) :=
    closure_mono (by
        rintro _ ⟨w', hw', rfl⟩
        exact pointsMap_pullbackSymmetry_mem_offDiagonal hρ₁ hρ₂ hw')
      (image_closure_subset_closure_image (continuous_pointsMap B S hS σ) ⟨w, hw, rfl⟩)
  obtain ⟨v, hv⟩ := mem_range_of_mem_closure_offDiagonal_of_fst_mem hρ₁ hρ₂ hV hU hψ hπ hι h hσw
    (by rw [← pointsMap_comp_apply]; simpa [σ] using hw₂)
  refine ⟨pointsMap B S hS _ (pullbackSymmetry ψ ψ).hom v, ?_⟩
  have hσe : (pullbackSymmetry ψ ψ).hom ≫
      pullback.map ψ ψ (ι ≫ π.hom) π.hom (𝟙 V) ι q (by simp [h]) h ≫
        pullback.map (ι ≫ π.hom) π.hom π.hom π.hom ι (𝟙 X.1) (𝟙 Y.1) (by simp) (by simp) =
      (pullback.map ψ ψ (ι ≫ π.hom) π.hom (𝟙 V) ι q (by simp [h]) h ≫
        pullback.map (ι ≫ π.hom) π.hom π.hom π.hom ι (𝟙 X.1) (𝟙 Y.1) (by simp) (by simp)) ≫ σ := by
    apply pullback.hom_ext <;> simp [σ]
  rw [← pointsMap_comp_apply, hσe, pointsMap_comp_apply, hv, ← pointsMap_comp_apply, hσσ,
    pointsMap_id]
  rfl

include hV hU hψ hπ hι h in
/-- **The off-diagonal points are closed among the points with both coordinates in `U₁`.**
A point of the closure of the image `O` of the complement of the diagonal of `U₁ ×_U U₁` with
both coordinates in `U₁` lies in `O`: by Lemma 1 it comes from `V ×_U V`, whose map to
`X ×_Y X` is an embedding (a closed embedding followed by an open one), then from
`U₁ ×_U U₁`, where the diagonal is open because `f` is étale. -/
theorem mem_offDiagonal_of_mem_closure (hU₁ : IsAlgebraicSpace B S hS U₁)
    (hj : IsOpenImmersion B S hS j) (hf : IsEtale B S hS (j ≫ ψ))
    {w : points B S hS (pullback π.hom π.hom)}
    (hw : w ∈ closure (pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ))
    (hw₁ : pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∈
      Set.range (pointsMap B S hS U₁ (j ≫ ι)))
    (hw₂ : pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∈
      Set.range (pointsMap B S hS U₁ (j ≫ ι))) :
    w ∈ pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  have : Mono j := mono_of_presheaf_isOpenImmersion hj
  let a := pullback.map ψ ψ (ι ≫ π.hom) π.hom (𝟙 V) ι q (by simp [h]) h
  let j₁ := pullback.map (ι ≫ π.hom) π.hom π.hom π.hom ι (𝟙 X.1) (𝟙 Y.1) (by simp) (by simp)
  let m := pullback.map (j ≫ ψ) (j ≫ ψ) ψ ψ j j (𝟙 U) (by simp) (by simp)
  have hρ : ρ = m ≫ a ≫ j₁ := eq_pullbackMap_comp_of_fst_snd hρ₁ hρ₂ h
  have : Mono m := mono_pullbackMap (j ≫ ψ) (j ≫ ψ) ψ ψ j j (𝟙 U) _ _
  have hemb := isEmbedding_pointsMap_pullbackMap_comp B S hS hV hU X.2 Y.2 hψ hπ hι h
  have hmemb := isOpenEmbedding_pointsMap_of_isOpenImmersion
    (isOpenImmersion_pullbackMap_of_isOpenImmersion j ψ hj)
  have hΔopen : IsOpen (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ)))) := by
    rw [← Set.image_univ]
    exact isOpenMap_pointsMap_of_isOpenImmersion B S hS _
      (isOpenImmersion_diagonal_of_isUnramified B S hS hU₁ hU (j ≫ ψ)
        (isUnramified_of_isEtale B S hS hf)) _ isOpen_univ
  obtain ⟨x₁, hx₁⟩ := hw₁
  obtain ⟨x₂, hx₂⟩ := hw₂
  obtain ⟨v, rfl⟩ := mem_range_of_mem_closure_offDiagonal_of_fst_mem hρ₁ hρ₂ hV hU hψ hπ hι h hw
    ⟨pointsMap B S hS _ j x₁, by rwa [← pointsMap_comp_apply]⟩
  have he₁ : (a ≫ j₁) ≫ pullback.fst π.hom π.hom = pullback.fst ψ ψ ≫ ι := by simp [a, j₁]
  have he₂ : (a ≫ j₁) ≫ pullback.snd π.hom π.hom = pullback.snd ψ ψ ≫ ι := by simp [a, j₁]
  have hv₁ : pointsMap B S hS _ (pullback.fst ψ ψ) v ∈ Set.range (pointsMap B S hS U₁ j) :=
    ⟨x₁, pointsMap_eq_of_pointsMap_comp_eq he₁ hx₁⟩
  have hv₂ : pointsMap B S hS _ (pullback.snd ψ ψ) v ∈ Set.range (pointsMap B S hS U₁ j) :=
    ⟨x₂, pointsMap_eq_of_pointsMap_comp_eq he₂ hx₂⟩
  obtain ⟨k, rfl⟩ := mem_range_pullbackMap_of_mem_range j ψ v hv₁ hv₂
  have hk : k ∈ closure (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ := by
    rwa [hmemb.isInducing.closure_eq_preimage_closure_image,
      hemb.isInducing.closure_eq_preimage_closure_image, ← Set.image_comp, ← pointsMap_comp,
      ← hρ]
  rw [hΔopen.isClosed_compl.closure_eq] at hk
  exact ⟨k, hk, by rw [hρ, pointsMap_comp_apply]⟩

include hV hU hψ hπ hι h in
/-- **Step 1 of the repaired proof of Stacks 0F4B.** In the situation of
`AlgebraicGeometry.Space.mem_offDiagonal_of_mem_closure`, let `f = j ≫ ψ` be an isomorphism over
the reduced closed subspace of `U` on a closed set `Z`, and let `T` be the image of `f⁻¹ Z` in
`X`. A point of the closure of the off-diagonal points with both coordinates in the closure of `T`
has both coordinates outside `V`.

If a coordinate lies in `V`, the point comes from `V ×_U V` by Lemma 1; both coordinates then
lie in `T`, which is closed in `V`, so the point comes from `U₁ ×_U U₁` with a coordinate in
`f⁻¹ Z`, hence lies on the diagonal, since `f⁻¹ Z ≅ Z`. But the closure of the off-diagonal
points meets the diagonal nowhere. -/
theorem notMem_range_of_mem_closure_offDiagonal (hU₁ : IsAlgebraicSpace B S hS U₁)
    (hj : IsOpenImmersion B S hS j) (hf : IsEtale B S hS (j ≫ ψ))
    (Z : Set (points B S hS U)) (hZ : IsClosed Z)
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU Z hZ).fromPreimage (j ≫ ψ)))
    {w : points B S hS (pullback π.hom π.hom)}
    (hw : w ∈ closure (pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ))
    (h₁ : pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∈
      closure (pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Z)))
    (h₂ : pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∈
      closure (pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Z))) :
    pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∉ Set.range (pointsMap B S hS V ι) ∧
      pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∉ Set.range (pointsMap B S hS V ι) := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  have : Mono j := mono_of_presheaf_isOpenImmersion hj
  have : Mono ρ := mono_of_fst_snd hρ₁ hρ₂
  have hjinj := pointsMap_injective_of_mono B S hS j
  let e := pullback.map ψ ψ (ι ≫ π.hom) π.hom (𝟙 V) ι q (by simp [h]) h ≫
    pullback.map (ι ≫ π.hom) π.hom π.hom π.hom ι (𝟙 X.1) (𝟙 Y.1) (by simp) (by simp)
  let m := pullback.map (j ≫ ψ) (j ≫ ψ) ψ ψ j j (𝟙 U) (by simp) (by simp)
  have hρ : ρ = m ≫ e := eq_pullbackMap_comp_of_fst_snd hρ₁ hρ₂ h
  have he₁ : e ≫ pullback.fst π.hom π.hom = pullback.fst ψ ψ ≫ ι := by simp [e]
  have he₂ : e ≫ pullback.snd π.hom π.hom = pullback.snd ψ ψ ≫ ι := by simp [e]
  have hm₁ : m ≫ pullback.fst ψ ψ = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j := by simp [m]
  have hTV := closure_image_inter_range_subset hV hU hU₁ hψ j hι Z hZ hiso
  -- a point of the image of `V ×_U V` with coordinates in `T` lies on the diagonal
  have hKΔ : ∀ w ∈ Set.range (pointsMap B S hS _ e),
      pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∈
        pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Z) →
      pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∈
        pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Z) →
      w ∈ pointsMap B S hS _ ρ '' Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))) := by
    rintro _ ⟨v, rfl⟩ ⟨z₁, hz₁, hz₁v⟩ ⟨z₂, -, hz₂v⟩
    have hv₁ := pointsMap_eq_of_pointsMap_comp_eq he₁ hz₁v
    have hv₂ := pointsMap_eq_of_pointsMap_comp_eq he₂ hz₂v
    obtain ⟨k, rfl⟩ := mem_range_pullbackMap_of_mem_range j ψ v ⟨z₁, hv₁⟩ ⟨z₂, hv₂⟩
    have hk₁ : pointsMap B S hS _ (pullback.fst (j ≫ ψ) (j ≫ ψ)) k = z₁ := hjinj (by
      rw [hv₁, ← pointsMap_comp_apply, ← pointsMap_comp_apply, hm₁])
    refine ⟨k, mem_range_diagonal_of_mem_reducedClosedSubspace hU (j ≫ ψ) Z hZ hiso k
      (by rwa [hk₁]), ?_⟩
    rw [hρ, pointsMap_comp_apply]
  -- the closure of the off-diagonal points does not meet the diagonal
  have hΔ : Disjoint (closure (pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ))
      (pointsMap B S hS _ ρ '' Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ)))) := by
    rw [Set.disjoint_right]
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩ hcl
    obtain ⟨k, hk, hke⟩ := mem_offDiagonal_of_mem_closure hρ₁ hρ₂ hV hU hψ hπ hι h hU₁ hj hf hcl
      ⟨u, by
        rw [← pointsMap_comp_apply, ← pointsMap_comp_apply]
        congr 1
        rw [hρ₁, pullback.diagonal_fst_assoc]⟩
      ⟨u, by
        rw [← pointsMap_comp_apply, ← pointsMap_comp_apply]
        congr 1
        rw [hρ₂, pullback.diagonal_snd_assoc]⟩
    exact hk ⟨u, (pointsMap_injective_of_mono B S hS ρ hke).symm⟩
  exact notMem_of_mem_closure_of_mem_closure _ _ hTV
    (fun w hw => mem_range_of_mem_closure_offDiagonal_of_fst_mem hρ₁ hρ₂ hV hU hψ hπ hι h hw.1
      hw.2)
    (fun w hw => mem_range_of_mem_closure_offDiagonal_of_snd_mem hρ₁ hρ₂ hV hU hψ hπ hι h hw.1
      hw.2)
    (by
      rintro _ ⟨v, rfl⟩
      exact ⟨⟨pointsMap B S hS _ (pullback.fst ψ ψ) v, by
        rw [← pointsMap_comp_apply, ← pointsMap_comp_apply]; congr 1; exact he₁.symm⟩,
        ⟨pointsMap B S hS _ (pullback.snd ψ ψ) v, by
        rw [← pointsMap_comp_apply, ← pointsMap_comp_apply]; congr 1; exact he₂.symm⟩⟩)
    hKΔ hΔ hw h₁ h₂

omit hρ₂ in
include hρ₁ hV hU hψ hι in
/-- **No off-diagonal point has a coordinate in the closure of `f⁻¹ Z`.** -/
theorem fst_notMem_closure_of_mem_offDiagonal (hU₁ : IsAlgebraicSpace B S hS U₁)
    (hj : IsOpenImmersion B S hS j) (Z : Set (points B S hS U)) (hZ : IsClosed Z)
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU Z hZ).fromPreimage (j ≫ ψ)))
    {w : points B S hS (pullback π.hom π.hom)}
    (hw : w ∈ pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ) :
    pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∉
      closure (pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Z)) := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  have : Mono j := mono_of_presheaf_isOpenImmersion hj
  obtain ⟨k, hk, rfl⟩ := hw
  intro hcl
  have hpt : pointsMap B S hS _ (pullback.fst π.hom π.hom) (pointsMap B S hS _ ρ k) =
      pointsMap B S hS _ (j ≫ ι) (pointsMap B S hS _ (pullback.fst (j ≫ ψ) (j ≫ ψ)) k) := by
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hρ₁]
  obtain ⟨z, hz, hzk⟩ := closure_image_inter_range_subset hV hU hU₁ hψ j hι Z hZ hiso
    ⟨hcl, ⟨pointsMap B S hS _ j (pointsMap B S hS _ (pullback.fst (j ≫ ψ) (j ≫ ψ)) k), by
      rw [hpt, pointsMap_comp_apply]⟩⟩
  rw [hpt] at hzk
  have := pointsMap_injective_of_mono B S hS (j ≫ ι) hzk
  exact hk (mem_range_diagonal_of_mem_reducedClosedSubspace hU (j ≫ ψ) Z hZ hiso k
    (by rw [← this]; exact hz))

include hρ₁ hρ₂ hV hU hψ hι in
/-- **No off-diagonal point has its second coordinate in the closure of `f⁻¹ Z`.** This is
`AlgebraicGeometry.Space.fst_notMem_closure_of_mem_offDiagonal` after the swap of `X ×_Y X`. -/
theorem snd_notMem_closure_of_mem_offDiagonal (hU₁ : IsAlgebraicSpace B S hS U₁)
    (hj : IsOpenImmersion B S hS j) (Z : Set (points B S hS U)) (hZ : IsClosed Z)
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU Z hZ).fromPreimage (j ≫ ψ)))
    {w : points B S hS (pullback π.hom π.hom)}
    (hw : w ∈ pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ) :
    pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∉
      closure (pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Z)) := by
  have := fst_notMem_closure_of_mem_offDiagonal hρ₁ hV hU hψ hι hU₁ hj Z hZ hiso
    (pointsMap_pullbackSymmetry_mem_offDiagonal hρ₁ hρ₂ hw)
  rwa [← pointsMap_comp_apply, pullbackSymmetry_hom_comp_fst] at this

end StepOne

end AlgebraicGeometry.Space

end
