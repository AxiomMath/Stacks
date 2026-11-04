module

public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject

/-!
# Transporting essential constancy along functors and reindexings

Let `M : J ⥤ C` be essentially constant with respect to a cocone `t`, in the sense of
Stacks 05PU(1): there are an index `i` and a section `r : t.pt ⟶ M i` of the coprojection at
`i` through which every transition map of `M` eventually factors
(`EssentiallyConstantInd.IsEssentiallyConstantWith`). This file shows how such a witness moves
along the following operations, and dually for pro-objects:

* postcomposition with an arbitrary functor `G : C ⥤ C'` (the witness is `G.map r`);
* replacing the diagram by a naturally isomorphic one;
* restricting along a full and essentially surjective functor of index categories — in
  particular along an equivalence;
* restricting along a full functor `Φ : I ⥤ J` into a filtered category every object of which
  maps to an object of the image of `Φ`, and conversely extending a witness for `Φ ⋙ M` back
  to `M`.

The last pair is the cofinality argument of Stacks 05T5: for such a `Φ` a cocone on `M` is
essentially constant exactly when its restriction along `Φ` is.

The consequences for the predicates `IsEssentiallyConstantInd` / `IsEssentiallyConstantPro`
(the value quantified existentially) are recorded as well.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.EssentiallyConstantInd

variable {J : Type*} [Category J] {C : Type*} [Category C]
  {M : J ⥤ C} {t : Cocone M} {i : J} {r : t.pt ⟶ M.obj i}

namespace IsEssentiallyConstantWith

/-- Essential constancy is preserved by postcomposition with any functor (Stacks 05SH at the
level of witnesses): `G.map r` is a witness for `G.mapCocone t`. -/
theorem map (h : IsEssentiallyConstantWith M t i r) {C' : Type*} [Category C'] (G : C ⥤ C') :
    IsEssentiallyConstantWith (M ⋙ G) (G.mapCocone t) i (G.map r) where
  retraction := by simpa using congrArg G.map h.retraction
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    exact ⟨k, σ, τ, by simp [hk]⟩

/-- Essential constancy is transported along a natural isomorphism of diagrams. -/
theorem precompose (h : IsEssentiallyConstantWith M t i r) {N : J ⥤ C} (α : N ≅ M) :
    IsEssentiallyConstantWith N ((Cocone.precompose α.hom).obj t) i (r ≫ α.inv.app i) where
  retraction := by simp [h.retraction]
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    refine ⟨k, σ, τ, ?_⟩
    have hN : ∀ {a b : J} (f : a ⟶ b), N.map f = α.hom.app a ≫ M.map f ≫ α.inv.app b := by
      intro a b f
      rw [← Category.assoc, ← α.hom.naturality, Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id]
    rw [hN τ, hN σ]
    simp [hk]

/-- Essential constancy is inherited by the restriction along a full and essentially surjective
functor of index categories, e.g. along an equivalence. -/
theorem whisker_of_essSurj (h : IsEssentiallyConstantWith M t i r)
    {J' : Type*} [Category J'] (e : J' ⥤ J) [e.Full] [e.EssSurj] :
    IsEssentiallyConstantWith (e ⋙ M) (t.whisker e) (e.objPreimage i)
      (r ≫ M.map (e.objObjPreimageIso i).inv) where
  retraction := by simp [h.retraction]
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal (e.obj j)
    refine ⟨e.objPreimage k, e.preimage ((e.objObjPreimageIso i).hom ≫ σ ≫
      (e.objObjPreimageIso k).inv), e.preimage (τ ≫ (e.objObjPreimageIso k).inv), ?_⟩
    simp [hk]

/-- Restriction along a full functor `Φ : I ⥤ J` into a filtered category every object of which
maps to an object in the image of `Φ`: an essential-constancy witness for `M` yields one for
`Φ ⋙ M` on the restricted cocone. -/
theorem exists_whisker [IsFilteredOrEmpty J] (h : IsEssentiallyConstantWith M t i r)
    {I : Type*} [Category I] (Φ : I ⥤ J) [Φ.Full] (hΦ : ∀ j, ∃ a, Nonempty (j ⟶ Φ.obj a)) :
    ∃ (a : I) (r' : t.pt ⟶ (Φ ⋙ M).obj a),
      IsEssentiallyConstantWith (Φ ⋙ M) (t.whisker Φ) a r' := by
  obtain ⟨a₀, ⟨u⟩⟩ := hΦ i
  refine ⟨a₀, r ≫ M.map u, ⟨by simp [h.retraction], fun b => ?_⟩⟩
  obtain ⟨k, σ, τ, hk⟩ := h.cofinal (Φ.obj b)
  obtain ⟨a₁, ⟨d⟩⟩ := hΦ k
  let e₁ := IsFiltered.leftToMax (Φ.obj a₀) (Φ.obj a₁)
  let e₂ := IsFiltered.rightToMax (Φ.obj a₀) (Φ.obj a₁)
  let w := IsFiltered.coeqHom (u ≫ e₁) (σ ≫ d ≫ e₂)
  obtain ⟨a₂, ⟨d₂⟩⟩ := hΦ (IsFiltered.coeq (u ≫ e₁) (σ ≫ d ≫ e₂))
  have hw : u ≫ e₁ ≫ w = σ ≫ d ≫ e₂ ≫ w := by
    simpa only [Category.assoc] using IsFiltered.coeq_condition (u ≫ e₁) (σ ≫ d ≫ e₂)
  refine ⟨a₂, Φ.preimage (e₁ ≫ w ≫ d₂), Φ.preimage (τ ≫ d ≫ e₂ ≫ w ≫ d₂), ?_⟩
  have hu : M.map u ≫ M.map (e₁ ≫ w ≫ d₂) = M.map σ ≫ M.map (d ≫ e₂ ≫ w ≫ d₂) := by
    rw [← M.map_comp, ← M.map_comp]
    congr 1
    simpa only [Category.assoc] using congrArg (· ≫ d₂) hw
  simp only [Functor.comp_map, Functor.map_preimage, Cocone.whisker_ι, Functor.whiskerLeft_app]
  rw [M.map_comp, hk]
  simp only [Category.assoc]
  rw [hu]

/-- Extension along `Φ : I ⥤ J` when every object of `J` maps to an object in the image of
`Φ`: a witness for the restricted cocone `t.whisker Φ` is a witness for `t` itself. -/
theorem of_whisker {I : Type*} [Category I] (Φ : I ⥤ J)
    (hΦ : ∀ j, ∃ a, Nonempty (j ⟶ Φ.obj a)) {a : I} {r : t.pt ⟶ M.obj (Φ.obj a)}
    (h : IsEssentiallyConstantWith (Φ ⋙ M) (t.whisker Φ) a r) :
    IsEssentiallyConstantWith M t (Φ.obj a) r where
  retraction := h.retraction
  cofinal j := by
    obtain ⟨b, ⟨d⟩⟩ := hΦ j
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal b
    refine ⟨Φ.obj k, Φ.map σ, d ≫ Φ.map τ, ?_⟩
    simp only [Functor.comp_map, Cocone.whisker_ι, Functor.whiskerLeft_app] at hk
    rw [M.map_comp, hk, ← Category.assoc, t.w]

end IsEssentiallyConstantWith

/-- The predicate `IsEssentiallyConstantInd` is invariant under reindexing along an equivalence,
postcomposition with a functor and natural isomorphism of diagrams. -/
theorem IsEssentiallyConstantInd.of_equivalence {M : J ⥤ C} (h : IsEssentiallyConstantInd M)
    {J' : Type*} [Category J'] {C' : Type*} [Category C'] {N : J' ⥤ C'} (e : J' ⥤ J)
    [e.IsEquivalence] (G : C ⥤ C') (α : N ≅ e ⋙ M ⋙ G) : IsEssentiallyConstantInd N := by
  obtain ⟨t, i, r, h⟩ := h
  exact ⟨_, _, _, ((h.map G).whisker_of_essSurj e).precompose α⟩

/-- Transport of an essentially constant ind-object with an invertible coprojection at a
distinguished index, along an equivalence `e` of index categories, a functor `G` of targets and a
natural isomorphism `α`: the transported cocone has an invertible coprojection at any index `j₀`
with `e.obj j₀ ≅ i₀`. -/
theorem exists_isIso_of_equivalence {M : J ⥤ C} {J' : Type*} [Category J'] {C' : Type*}
    [Category C'] {N : J' ⥤ C'} (e : J' ⥤ J) [e.IsEquivalence] (G : C ⥤ C')
    (α : N ≅ e ⋙ M ⋙ G) {j₀ : J'} {i₀ : J} (φ : e.obj j₀ ≅ i₀)
    (h : ∃ c : Cocone M, (∃ i r, IsEssentiallyConstantWith M c i r) ∧ IsIso (c.ι.app i₀)) :
    ∃ c : Cocone N, (∃ i r, IsEssentiallyConstantWith N c i r) ∧ IsIso (c.ι.app j₀) := by
  obtain ⟨c, ⟨i, r, hc⟩, hi⟩ := h
  refine ⟨_, ⟨_, _, ((hc.map G).whisker_of_essSurj e).precompose α⟩, ?_⟩
  have h₁ : c.ι.app (e.obj j₀) = M.map φ.hom ≫ c.ι.app i₀ := (c.w φ.hom).symm
  simp only [Cocone.precompose_obj_ι, NatTrans.comp_app, Cocone.whisker_ι,
    Functor.whiskerLeft_app, Functor.mapCocone_ι_app, h₁, G.map_comp]
  infer_instance

/-- An essential-constancy witness is carried along an isomorphism of cocones. -/
theorem IsEssentiallyConstantWith.of_iso {M : J ⥤ C} {t t' : Cocone M} {i : J}
    {r : t.pt ⟶ M.obj i} (h : IsEssentiallyConstantWith M t i r) (e : t ≅ t') :
    IsEssentiallyConstantWith M t' i (e.inv.hom ≫ r) where
  retraction := by
    rw [Category.assoc, ← e.hom.w i, reassoc_of% h.retraction]
    simp
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    exact ⟨k, σ, τ, by simp [hk]⟩

/-- Reflection along a fully faithful functor `G`: if `M ⋙ G` is essentially constant with
respect to a cocone whose vertex is the image of an object `Y`, then `M` is essentially constant
(with value `Y`). -/
theorem IsEssentiallyConstantInd.of_comp_fullyFaithful {M : J ⥤ C} {C' : Type*} [Category C']
    {G : C ⥤ C'} (hG : G.FullyFaithful) {t : Cocone (M ⋙ G)} {i : J} {r : t.pt ⟶ G.obj (M.obj i)}
    (h : IsEssentiallyConstantWith (M ⋙ G) t i r) {Y : C} (e : G.obj Y ≅ t.pt) :
    IsEssentiallyConstantInd M := by
  let t' : Cocone M :=
    { pt := Y
      ι := { app j := hG.preimage (t.ι.app j ≫ e.inv)
             naturality j k f := hG.map_injective (by simpa using t.w_assoc f e.inv) } }
  refine ⟨t', i, hG.preimage (e.hom ≫ r), ⟨hG.map_injective ?_, fun j => ?_⟩⟩
  · simp [t', reassoc_of% h.retraction]
  · obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    exact ⟨k, σ, τ, hG.map_injective (by simpa [t'] using hk)⟩

/-- For a filtered index category, a cocone that the covariant Hom functors `Mor(W, -)` all send to
colimit cocones carries an essential-constancy witness (Stacks 05PY, (2) ⇒ (1)); no smallness of
the index category is needed. -/
theorem exists_isEssentiallyConstantWith_of_isColimit_coyoneda [IsFiltered J] {M : J ⥤ C}
    (c : Cocone M)
    (hc : ∀ W : C, Nonempty (IsColimit ((coyoneda.obj (Opposite.op W)).mapCocone c))) :
    ∃ i r, IsEssentiallyConstantWith M c i r := by
  obtain ⟨j, r, hr⟩ := Types.jointly_surjective_of_isColimit (hc c.pt).some (𝟙 c.pt)
  dsimp at hr
  refine ⟨j, r, hr, fun i => ?_⟩
  have h : ((coyoneda.obj (Opposite.op (M.obj i))).mapCocone c).ι.app i (𝟙 _) =
      ((coyoneda.obj (Opposite.op (M.obj i))).mapCocone c).ι.app j (c.ι.app i ≫ r) := by
    dsimp
    rw [Category.id_comp, Category.assoc, hr, Category.comp_id]
  obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.isColimit_eq_iff _ (hc (M.obj i)).some).1 h
  exact ⟨k, g, f, by simpa using hfg⟩

end CategoryTheory.EssentiallyConstantInd

namespace CategoryTheory.EssentiallyConstantPro

variable {J : Type*} [Category J] {C : Type*} [Category C]
  {M : J ⥤ C} {t : Cone M} {i : J} {r : M.obj i ⟶ t.pt}

namespace IsEssentiallyConstantWith

/-- Essential constancy of a pro-object is preserved by postcomposition with any functor. -/
theorem map (h : IsEssentiallyConstantWith M t i r) {C' : Type*} [Category C'] (G : C ⥤ C') :
    IsEssentiallyConstantWith (M ⋙ G) (G.mapCone t) i (G.map r) where
  retraction := by simpa using congrArg G.map h.retraction
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    exact ⟨k, σ, τ, by simp [hk]⟩

/-- Essential constancy of a pro-object is transported along a natural isomorphism. -/
theorem postcompose (h : IsEssentiallyConstantWith M t i r) {N : J ⥤ C} (α : M ≅ N) :
    IsEssentiallyConstantWith N ((Cone.postcompose α.hom).obj t) i (α.inv.app i ≫ r) where
  retraction := by simp [h.retraction]
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    refine ⟨k, σ, τ, ?_⟩
    have hN : ∀ {a b : J} (f : a ⟶ b), N.map f = α.inv.app a ≫ M.map f ≫ α.hom.app b := by
      intro a b f
      rw [α.hom.naturality, Iso.inv_hom_id_app_assoc]
    rw [hN τ, hN σ]
    simp [hk]

/-- Essential constancy of a pro-object is inherited by the restriction along a full and
essentially surjective functor of index categories. -/
theorem whisker_of_essSurj (h : IsEssentiallyConstantWith M t i r)
    {J' : Type*} [Category J'] (e : J' ⥤ J) [e.Full] [e.EssSurj] :
    IsEssentiallyConstantWith (e ⋙ M) (t.whisker e) (e.objPreimage i)
      (M.map (e.objObjPreimageIso i).hom ≫ r) where
  retraction := by simp [h.retraction]
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal (e.obj j)
    refine ⟨e.objPreimage k, e.preimage ((e.objObjPreimageIso k).hom ≫ σ ≫
      (e.objObjPreimageIso i).inv), e.preimage ((e.objObjPreimageIso k).hom ≫ τ), ?_⟩
    simp [hk]

/-- Restriction of a pro-object along a full functor `Φ : I ⥤ J` into a cofiltered category every
object of which receives a map from an object in the image of `Φ`. -/
theorem exists_whisker [IsCofilteredOrEmpty J] (h : IsEssentiallyConstantWith M t i r)
    {I : Type*} [Category I] (Φ : I ⥤ J) [Φ.Full] (hΦ : ∀ j, ∃ a, Nonempty (Φ.obj a ⟶ j)) :
    ∃ (a : I) (r' : (Φ ⋙ M).obj a ⟶ t.pt),
      IsEssentiallyConstantWith (Φ ⋙ M) (t.whisker Φ) a r' := by
  obtain ⟨a₀, ⟨u⟩⟩ := hΦ i
  refine ⟨a₀, M.map u ≫ r, ⟨?_, fun b => ?_⟩⟩
  · simp [h.retraction]
  obtain ⟨k, σ, τ, hk⟩ := h.cofinal (Φ.obj b)
  obtain ⟨a₁, ⟨d⟩⟩ := hΦ k
  let e₁ := IsCofiltered.minToLeft (Φ.obj a₀) (Φ.obj a₁)
  let e₂ := IsCofiltered.minToRight (Φ.obj a₀) (Φ.obj a₁)
  let w := IsCofiltered.eqHom (e₁ ≫ u) (e₂ ≫ d ≫ σ)
  obtain ⟨a₂, ⟨d₂⟩⟩ := hΦ (IsCofiltered.eq (e₁ ≫ u) (e₂ ≫ d ≫ σ))
  have hw : w ≫ e₁ ≫ u = w ≫ e₂ ≫ d ≫ σ := by
    simpa only [Category.assoc] using IsCofiltered.eq_condition (e₁ ≫ u) (e₂ ≫ d ≫ σ)
  refine ⟨a₂, Φ.preimage (d₂ ≫ w ≫ e₁), Φ.preimage (d₂ ≫ w ≫ e₂ ≫ d ≫ τ), ?_⟩
  have hu : M.map (d₂ ≫ w ≫ e₁) ≫ M.map u = M.map (d₂ ≫ w ≫ e₂ ≫ d) ≫ M.map σ := by
    rw [← M.map_comp, ← M.map_comp]
    congr 1
    simpa only [Category.assoc] using congrArg (d₂ ≫ ·) hw
  simp only [Functor.comp_map, Functor.map_preimage, Cone.whisker_π, Functor.whiskerLeft_app]
  rw [show d₂ ≫ w ≫ e₂ ≫ d ≫ τ = (d₂ ≫ w ≫ e₂ ≫ d) ≫ τ by simp only [Category.assoc],
    M.map_comp, hk]
  simp only [Category.assoc]
  rw [reassoc_of% hu]

/-- Extension of a pro-object witness along `Φ : I ⥤ J` when every object of `J` receives a map
from an object in the image of `Φ`. -/
theorem of_whisker {I : Type*} [Category I] (Φ : I ⥤ J)
    (hΦ : ∀ j, ∃ a, Nonempty (Φ.obj a ⟶ j)) {a : I} {r : M.obj (Φ.obj a) ⟶ t.pt}
    (h : IsEssentiallyConstantWith (Φ ⋙ M) (t.whisker Φ) a r) :
    IsEssentiallyConstantWith M t (Φ.obj a) r where
  retraction := h.retraction
  cofinal j := by
    obtain ⟨b, ⟨d⟩⟩ := hΦ j
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal b
    refine ⟨Φ.obj k, Φ.map σ, Φ.map τ ≫ d, ?_⟩
    simp only [Functor.comp_map, Cone.whisker_π, Functor.whiskerLeft_app] at hk
    rw [M.map_comp, hk, Category.assoc, Category.assoc, t.w]

end IsEssentiallyConstantWith

/-- The predicate `IsEssentiallyConstantPro` is invariant under reindexing along an equivalence,
postcomposition with a functor and natural isomorphism of diagrams. -/
theorem IsEssentiallyConstantPro.of_equivalence {M : J ⥤ C} (h : IsEssentiallyConstantPro M)
    {J' : Type*} [Category J'] {C' : Type*} [Category C'] {N : J' ⥤ C'} (e : J' ⥤ J)
    [e.IsEquivalence] (G : C ⥤ C') (α : e ⋙ M ⋙ G ≅ N) : IsEssentiallyConstantPro N := by
  obtain ⟨t, i, r, h⟩ := h
  exact ⟨_, _, _, ((h.map G).whisker_of_essSurj e).postcompose α⟩

/-- Transport of an essentially constant pro-object with an invertible projection at a
distinguished index, along an equivalence `e` of index categories, a functor `G` of targets and a
natural isomorphism `α`: the transported cone has an invertible projection at any index `j₀` with
`e.obj j₀ ≅ i₀`. -/
theorem exists_isIso_of_equivalence {M : J ⥤ C} {J' : Type*} [Category J'] {C' : Type*}
    [Category C'] {N : J' ⥤ C'} (e : J' ⥤ J) [e.IsEquivalence] (G : C ⥤ C')
    (α : e ⋙ M ⋙ G ≅ N) {j₀ : J'} {i₀ : J} (φ : e.obj j₀ ≅ i₀)
    (h : ∃ c : Cone M, (∃ i r, IsEssentiallyConstantWith M c i r) ∧ IsIso (c.π.app i₀)) :
    ∃ c : Cone N, (∃ i r, IsEssentiallyConstantWith N c i r) ∧ IsIso (c.π.app j₀) := by
  obtain ⟨c, ⟨i, r, hc⟩, hi⟩ := h
  refine ⟨_, ⟨_, _, ((hc.map G).whisker_of_essSurj e).postcompose α⟩, ?_⟩
  have h₁ : c.π.app (e.obj j₀) = c.π.app i₀ ≫ M.map φ.inv := (c.w φ.inv).symm
  simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
    Functor.whiskerLeft_app, Functor.mapCone_π_app, h₁, G.map_comp]
  infer_instance

/-- An essential-constancy witness of a pro-object is carried along an isomorphism of cones. -/
theorem IsEssentiallyConstantWith.of_iso {M : J ⥤ C} {t t' : Cone M} {i : J}
    {r : M.obj i ⟶ t.pt} (h : IsEssentiallyConstantWith M t i r) (e : t ≅ t') :
    IsEssentiallyConstantWith M t' i (r ≫ e.hom.hom) where
  retraction := by
    rw [← e.inv.w i, Category.assoc, reassoc_of% h.retraction]
    simp
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    exact ⟨k, σ, τ, by simp [hk]⟩

/-- Reflection of a pro-object along a fully faithful functor `G`: if `M ⋙ G` is essentially
constant with respect to a cone whose vertex is the image of an object `Y`, then `M` is
essentially constant (with value `Y`). -/
theorem IsEssentiallyConstantPro.of_comp_fullyFaithful {M : J ⥤ C} {C' : Type*} [Category C']
    {G : C ⥤ C'} (hG : G.FullyFaithful) {t : Cone (M ⋙ G)} {i : J} {r : G.obj (M.obj i) ⟶ t.pt}
    (h : IsEssentiallyConstantWith (M ⋙ G) t i r) {Y : C} (e : G.obj Y ≅ t.pt) :
    IsEssentiallyConstantPro M := by
  let t' : Cone M :=
    { pt := Y
      π := { app j := hG.preimage (e.hom ≫ t.π.app j)
             naturality j k f := hG.map_injective (by simpa using (t.w f).symm) } }
  refine ⟨t', i, hG.preimage (r ≫ e.inv), ⟨hG.map_injective ?_, fun j => ?_⟩⟩
  · simp [t', reassoc_of% h.retraction]
  · obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    exact ⟨k, σ, τ, hG.map_injective (by simpa [t'] using hk)⟩

/-- For a cofiltered index category, a cone that the contravariant Hom functors `Mor(-, W)` all
send to colimit cocones carries an essential-constancy witness (Stacks 05PZ, (2) ⇒ (1)); no
smallness of the index category is needed. -/
theorem exists_isEssentiallyConstantWith_of_isColimit_yoneda [IsCofiltered J] {M : J ⥤ C}
    (c : Cone M) (hc : ∀ W : C, Nonempty (IsColimit ((yoneda.obj W).mapCocone c.op))) :
    ∃ i r, IsEssentiallyConstantWith M c i r := by
  obtain ⟨j, r, hr⟩ := Types.jointly_surjective_of_isColimit (hc c.pt).some (𝟙 c.pt)
  dsimp at hr
  refine ⟨j.unop, r, hr, fun i => ?_⟩
  have h : ((yoneda.obj (M.obj i)).mapCocone c.op).ι.app (Opposite.op i) (𝟙 _) =
      ((yoneda.obj (M.obj i)).mapCocone c.op).ι.app j (r ≫ c.π.app i) := by
    dsimp
    rw [Category.comp_id, ← Category.assoc, hr, Category.id_comp]
  obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.isColimit_eq_iff _ (hc (M.obj i)).some).1 h
  exact ⟨k.unop, g.unop, f.unop, by simpa using hfg⟩

end CategoryTheory.EssentiallyConstantPro
