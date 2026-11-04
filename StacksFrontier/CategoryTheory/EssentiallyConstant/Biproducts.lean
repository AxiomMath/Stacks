module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject

/-!
# Essentially constant systems and direct sum decompositions

Stacks, Homological Algebra, Section 12.30 and 12.31: in a Karoubian additive category the colimit
of a direct sum `F ⊞ G` exists iff both colimits exist, and is their direct sum (0A2F); `F ⊞ G` is
essentially constant iff both `F` and `G` are (0A2G); and an inverse system in an abelian category
is essentially constant iff it eventually splits as its limit plus a summand that eventually
vanishes (070C). Essential constancy of a diagram is
`CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantInd` (Stacks 05PU).
-/

@[expose] public section

section

/-!
## Stacks tag 0A2F

In a Karoubian additive category, the colimit of a pointwise direct sum
`F ⊞ G` exists iff both `colim F` and `colim G` exist, and in that case
`colim (F ⊞ G) ≅ colim F ⊞ colim G`.
-/

open CategoryTheory CategoryTheory.Limits

section Retract

variable {I C : Type*} [Category I] [Category C]

/-- The components of a retraction `i ≫ r = 𝟙 F` of functors are retractions. -/
@[reassoc]
lemma app_comp_app_of_comp_eq_id {F H : I ⥤ C} {i : F ⟶ H} {r : H ⟶ F} (hir : i ≫ r = 𝟙 F)
    (j : I) : i.app j ≫ r.app j = 𝟙 (F.obj j) := by
  simpa using NatTrans.congr_app hir j

/-- Let `F` be a retract of `H` (`i ≫ r = 𝟙 F`) and let `s ≫ p = 𝟙 X`, `p ≫ s = colimMap (r ≫ i)`
split the induced idempotent of `colimit H`. Then `X`, with the maps `i ≫ colimit.ι H ≫ p`, is a
colimit of `F`. -/
noncomputable def isColimitOfRetract {F H : I ⥤ C} (i : F ⟶ H) (r : H ⟶ F) (hir : i ≫ r = 𝟙 F)
    [HasColimit H] {X : C} (s : X ⟶ colimit H) (p : colimit H ⟶ X) (hsp : s ≫ p = 𝟙 X)
    (hps : p ≫ s = colimMap (r ≫ i)) :
    IsColimit ((Cocone.precompose i).obj ((colimit.cocone H).extend p)) where
  desc t := s ≫ colimit.desc H ((Cocone.precompose r).obj t)
  fac t j := by
    have h : colimit.ι H j ≫ p ≫ s = r.app j ≫ i.app j ≫ colimit.ι H j := by
      rw [hps, ι_colimMap, NatTrans.comp_app, Category.assoc]
    dsimp
    simp only [Category.assoc]
    rw [reassoc_of% h, app_comp_app_of_comp_eq_id_assoc hir, colimit.ι_desc]
    dsimp
    rw [app_comp_app_of_comp_eq_id_assoc hir]
  uniq t m hm := by
    have h (j : I) : colimit.ι H j ≫ p ≫ s = r.app j ≫ i.app j ≫ colimit.ι H j := by
      rw [hps, ι_colimMap, NatTrans.comp_app, Category.assoc]
    have hpm : p ≫ m = p ≫ s ≫ colimit.desc H ((Cocone.precompose r).obj t) := by
      refine colimit.hom_ext fun j => ?_
      have hj : i.app j ≫ colimit.ι H j ≫ p ≫ m = t.ι.app j := by simpa using hm j
      have hp : p ≫ m = p ≫ s ≫ p ≫ m := by rw [reassoc_of% hsp]
      rw [hp]
      simp only [reassoc_of% (h j)]
      rw [hj, colimit.ι_desc]
      dsimp
      rw [app_comp_app_of_comp_eq_id_assoc hir]
    calc m = (s ≫ p) ≫ m := by rw [hsp, Category.id_comp]
      _ = s ≫ p ≫ s ≫ colimit.desc H ((Cocone.precompose r).obj t) := by
        rw [Category.assoc, hpm]
      _ = s ≫ colimit.desc H ((Cocone.precompose r).obj t) := by rw [reassoc_of% hsp]

/-- In an idempotent complete category, a retract of a functor with a colimit has a colimit. -/
lemma hasColimit_of_retract [IsIdempotentComplete C] {F H : I ⥤ C} (i : F ⟶ H) (r : H ⟶ F)
    (hir : i ≫ r = 𝟙 F) [HasColimit H] : HasColimit F := by
  have hidem : colimMap (r ≫ i) ≫ colimMap (r ≫ i) = colimMap (r ≫ i) := by
    ext j
    simp [app_comp_app_of_comp_eq_id_assoc hir]
  obtain ⟨X, s, p, hsp, hps⟩ := IsIdempotentComplete.idempotents_split _ _ hidem
  exact ⟨⟨⟨_, isColimitOfRetract i r hir s p hsp hps⟩⟩⟩

end Retract

namespace CategoryTheory.Limits.BinaryBicone

variable {I C : Type*} [Category I] [Category C] [HasZeroMorphisms C] {F G : I ⥤ C}
  (c : BinaryBicone F G)

/-- The components of the inclusion and projection of a bicone of functors compose to `𝟙`. -/
@[reassoc (attr := simp)]
lemma inl_app_fst_app (j : I) : c.inl.app j ≫ c.fst.app j = 𝟙 (F.obj j) := by
  rw [← NatTrans.comp_app, c.inl_fst, NatTrans.id_app]

/-- The components of the inclusion and projection of a bicone of functors compose to `0`. -/
@[reassoc (attr := simp)]
lemma inl_app_snd_app (j : I) : c.inl.app j ≫ c.snd.app j = 0 := by
  rw [← NatTrans.comp_app, c.inl_snd, zero_app]

/-- The components of the inclusion and projection of a bicone of functors compose to `0`. -/
@[reassoc (attr := simp)]
lemma inr_app_fst_app (j : I) : c.inr.app j ≫ c.fst.app j = 0 := by
  rw [← NatTrans.comp_app, c.inr_fst, zero_app]

/-- The components of the inclusion and projection of a bicone of functors compose to `𝟙`. -/
@[reassoc (attr := simp)]
lemma inr_app_snd_app (j : I) : c.inr.app j ≫ c.snd.app j = 𝟙 (G.obj j) := by
  rw [← NatTrans.comp_app, c.inr_snd, NatTrans.id_app]

end CategoryTheory.Limits.BinaryBicone

section Bicone

variable {I C : Type*} [Category I] [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {F G : I ⥤ C} (c : BinaryBicone F G) [HasColimit F] [HasColimit G]

/-- For a binary bicone `c` on `F` and `G`, the cocone on `c.pt` with vertex
`colimit F ⊞ colimit G` and components `c.fst ≫ colimit.ι F ≫ inl + c.snd ≫ colimit.ι G ≫ inr`. -/
@[implicit_reducible, simps]
noncomputable def biprodCocone : Cocone c.pt where
  pt := colimit F ⊞ colimit G
  ι := c.fst ≫ (colimit.cocone F).ι ≫ (Functor.const I).map biprod.inl +
    c.snd ≫ (colimit.cocone G).ι ≫ (Functor.const I).map biprod.inr

/-- If `c` is a biproduct bicone (`c.fst ≫ c.inl + c.snd ≫ c.inr = 𝟙`), then `biprodCocone c` is a
colimit cocone: the colimit of `F ⊞ G` is `colimit F ⊞ colimit G`. -/
noncomputable def isColimitBiprodCocone (htot : c.fst ≫ c.inl + c.snd ≫ c.inr = 𝟙 c.pt) :
    IsColimit (biprodCocone c) where
  desc t := biprod.desc (colimit.desc F ((Cocone.precompose c.inl).obj t))
    (colimit.desc G ((Cocone.precompose c.inr).obj t))
  fac t j := by
    have h := NatTrans.congr_app htot j
    simp only [NatTrans.app_add, NatTrans.comp_app, NatTrans.id_app] at h
    simp only [biprodCocone_ι, NatTrans.app_add, NatTrans.comp_app, Preadditive.add_comp,
      Category.assoc]
    simpa [Preadditive.add_comp] using congrArg (· ≫ t.ι.app j) h
  uniq t m hm := by
    refine biprod.hom_ext' _ _ (colimit.hom_ext fun j => ?_) (colimit.hom_ext fun j => ?_)
    · simpa [Preadditive.comp_add, Preadditive.add_comp] using congrArg (c.inl.app j ≫ ·) (hm j)
    · simpa [Preadditive.comp_add, Preadditive.add_comp] using congrArg (c.inr.app j ≫ ·) (hm j)

end Bicone

/-- Backward direction: if `F` and `G` both have colimits, so does `F ⊞ G`. -/
lemma hasColimit_biprod_of_hasColimit_aux
    {I C : Type*} [Category I] [Category C]
    [Preadditive C] [HasBinaryBiproducts C]
    (F G : I ⥤ C) [HasColimit F] [HasColimit G] :
    HasColimit (F ⊞ G) :=
  ⟨⟨⟨_, isColimitBiprodCocone (BinaryBiproduct.bicone F G) biprod.total⟩⟩⟩

/-- Existence of the canonical iso `colimit (F ⊞ G) ≅ colimit F ⊞ colimit G`. -/
lemma colimitBiprodIso_nonempty
    {I C : Type*} [Category I] [Category C]
    [Preadditive C] [HasBinaryBiproducts C]
    (F G : I ⥤ C) [HasColimit F] [HasColimit G] [HasColimit (F ⊞ G)] :
    Nonempty (colimit (F ⊞ G) ≅ colimit F ⊞ colimit G) :=
  ⟨(colimit.isColimit (F ⊞ G)).coconePointUniqueUpToIso
    (isColimitBiprodCocone (BinaryBiproduct.bicone F G) biprod.total)⟩

/-- Forward direction (left component): in a Karoubian additive category, if
`F ⊞ G` has a colimit, then so does `F`. -/
lemma hasColimit_of_hasColimit_biprod_left_aux
    {I C : Type*} [Category I] [Category C]
    [Preadditive C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
    (F G : I ⥤ C) [HasColimit (F ⊞ G)] :
    HasColimit F :=
  hasColimit_of_retract (biprod.inl : F ⟶ F ⊞ G) biprod.fst biprod.inl_fst

/-- Forward direction (right component). -/
lemma hasColimit_of_hasColimit_biprod_right_aux
    {I C : Type*} [Category I] [Category C]
    [Preadditive C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
    (F G : I ⥤ C) [HasColimit (F ⊞ G)] :
    HasColimit G :=
  hasColimit_of_retract (biprod.inr : G ⟶ F ⊞ G) biprod.snd biprod.inr_snd

/-- In a Karoubian additive category, the pointwise biproduct functor `F ⊞ G`
has a colimit iff both `F` and `G` do. -/
@[stacks 0A2F "iff"]
theorem hasColimit_biprod_iff
    {I C : Type*} [Category I] [Category C]
    [Preadditive C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
    (F G : I ⥤ C) :
    HasColimit (F ⊞ G) ↔ HasColimit F ∧ HasColimit G :=
  ⟨fun _ => ⟨hasColimit_of_hasColimit_biprod_left_aux F G,
      hasColimit_of_hasColimit_biprod_right_aux F G⟩,
    fun ⟨_, _⟩ => hasColimit_biprod_of_hasColimit_aux F G⟩

/-- If `F` and `G` have colimits, then so does `F ⊞ G`. -/
lemma hasColimit_biprod_of_hasColimit
    {I C : Type*} [Category I] [Category C]
    [Preadditive C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
    (F G : I ⥤ C) [HasColimit F] [HasColimit G] :
    HasColimit (F ⊞ G) :=
  (hasColimit_biprod_iff F G).mpr ⟨inferInstance, inferInstance⟩

/-- If `F ⊞ G` has a colimit, then so does `F`. -/
alias hasColimit_of_hasColimit_biprod_left := hasColimit_of_hasColimit_biprod_left_aux

/-- If `F ⊞ G` has a colimit, then so does `G`. -/
alias hasColimit_of_hasColimit_biprod_right := hasColimit_of_hasColimit_biprod_right_aux

/-- In a Karoubian additive category, if both `F` and `G` have colimits, then
the colimit of the pointwise biproduct is canonically isomorphic to the
biproduct of the colimits. -/
@[stacks 0A2F "iso"]
noncomputable def colimitBiprodIso
    {I C : Type*} [Category I] [Category C]
    [Preadditive C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
    (F G : I ⥤ C) [HasColimit F] [HasColimit G] :
    haveI := hasColimit_biprod_of_hasColimit F G
    colimit (F ⊞ G) ≅ colimit F ⊞ colimit G :=
  haveI := hasColimit_biprod_of_hasColimit F G
  (colimit.isColimit (F ⊞ G)).coconePointUniqueUpToIso
    (isColimitBiprodCocone (BinaryBiproduct.bicone F G) biprod.total)

/-- In a Karoubian additive category, if `F ⊞ G` has a colimit, then it is canonically isomorphic
to the biproduct of the colimits of `F` and `G`. -/
@[stacks 0A2F "iso_from_biprod"]
noncomputable def colimitBiprodIso_of_hasColimit_biprod
    {I C : Type*} [Category I] [Category C]
    [Preadditive C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
    (F G : I ⥤ C) [HasColimit (F ⊞ G)] :
    haveI := hasColimit_of_hasColimit_biprod_left F G
    haveI := hasColimit_of_hasColimit_biprod_right F G
    colimit (F ⊞ G) ≅ colimit F ⊞ colimit G :=
  haveI := hasColimit_of_hasColimit_biprod_left F G
  haveI := hasColimit_of_hasColimit_biprod_right F G
  (colimit.isColimit (F ⊞ G)).coconePointUniqueUpToIso
    (isColimitBiprodCocone (BinaryBiproduct.bicone F G) biprod.total)

end

section

/-!
## Stacks tag 0A2G

Let `I` be a filtered category and `C` an additive Karoubian category. For
two functors `F, G : I ⥤ C`, the direct sum `F ⊞ G` is essentially constant
iff both `F` and `G` are essentially constant.
-/

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

open CategoryTheory.EssentiallyConstantInd

section Witness

variable {I : Type u} [Category.{v} I] {C : Type u'} [Category.{v'} C]

/-- Over a filtered category, an essential-constancy witness `(t, i₀, r)` of `M` can be moved
forward along any `f : i₀ ⟶ i₁`: `(t, i₁, r ≫ M.map f)` is again a witness. -/
lemma CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith.comp_map [IsFiltered I]
    {M : I ⥤ C} {t : Cocone M} {i₀ : I} {r : t.pt ⟶ M.obj i₀}
    (h : IsEssentiallyConstantWith M t i₀ r) {i₁ : I} (f : i₀ ⟶ i₁) :
    IsEssentiallyConstantWith M t i₁ (r ≫ M.map f) where
  retraction := by simpa using h.retraction
  cofinal j := by
    obtain ⟨k, v, u, huv⟩ := h.cofinal j
    obtain ⟨m, α, β, hαβ⟩ := IsFiltered.span v f
    refine ⟨m, β, u ≫ α, ?_⟩
    rw [M.map_comp, huv]
    simpa using congrArg (fun g => t.ι.app j ≫ r ≫ M.map g) hαβ

/-- Over a filtered category, a retract of an essentially constant functor with values in an
idempotent complete category is essentially constant: split the idempotent of the value
`X` induced by `r ≫ i`. -/
lemma isEssentiallyConstantInd_of_retract [IsFiltered I] [IsIdempotentComplete C] {F H : I ⥤ C}
    (i : F ⟶ H) (r : H ⟶ F) (hir : i ≫ r = 𝟙 F) (hH : IsEssentiallyConstantInd H) :
    IsEssentiallyConstantInd F := by
  obtain ⟨t, i₀, b, hb, h⟩ := hH
  obtain ⟨k₀, v₀, u₀, hu₀⟩ := h i₀
  have hu₀' : r.app i₀ ≫ F.map u₀ = t.ι.app i₀ ≫ b ≫ r.app i₀ ≫ F.map v₀ := by
    simpa using congrArg (· ≫ r.app k₀) hu₀
  have K : t.ι.app i₀ ≫ b ≫ r.app i₀ ≫ i.app i₀ ≫ t.ι.app i₀ =
      r.app i₀ ≫ i.app i₀ ≫ t.ι.app i₀ := by
    simpa using (congrArg (· ≫ r.app k₀ ≫ i.app k₀ ≫ t.ι.app k₀) hu₀).symm
  have hidem : (b ≫ r.app i₀ ≫ i.app i₀ ≫ t.ι.app i₀) ≫ (b ≫ r.app i₀ ≫ i.app i₀ ≫ t.ι.app i₀) =
      b ≫ r.app i₀ ≫ i.app i₀ ≫ t.ι.app i₀ := by
    simp [K, app_comp_app_of_comp_eq_id_assoc hir]
  obtain ⟨X, s, p, hsp, hps⟩ := IsIdempotentComplete.idempotents_split _ _ hidem
  refine ⟨Cocone.mk X (i ≫ t.ι ≫ (Functor.const I).map p), i₀, s ≫ b ≫ r.app i₀, ?_,
    fun j => ?_⟩
  · simp only [NatTrans.comp_app, Functor.const_map_app, Category.assoc]
    rw [← reassoc_of% hps, reassoc_of% hsp, hsp]
  · obtain ⟨k, v, u, hu⟩ := h j
    have hu' : r.app j ≫ F.map u = t.ι.app j ≫ b ≫ r.app i₀ ≫ F.map v := by
      simpa using congrArg (· ≫ r.app k) hu
    obtain ⟨m, α, β, hαβ⟩ := IsFiltered.span u₀ v
    have hαβ' := congrArg F.map hαβ
    simp only [F.map_comp] at hαβ'
    refine ⟨m, v₀ ≫ α, u ≫ β, ?_⟩
    simp only [NatTrans.comp_app, Functor.const_map_app, Category.assoc, Functor.map_comp]
    rw [reassoc_of% hps, ← reassoc_of% hu₀', app_comp_app_of_comp_eq_id_assoc hir,
      hαβ', ← reassoc_of% hu', app_comp_app_of_comp_eq_id_assoc hir]

/-- Over a filtered category, if `F` and `G` are essentially constant, then so is the vertex of
any biproduct bicone on `F` and `G`. -/
lemma isEssentiallyConstantInd_of_isBiproductBicone [IsFiltered I] [Preadditive C]
    [HasBinaryBiproducts C] {F G : I ⥤ C} (c : BinaryBicone F G)
    (htot : c.fst ≫ c.inl + c.snd ≫ c.inr = 𝟙 c.pt)
    (hF : IsEssentiallyConstantInd F) (hG : IsEssentiallyConstantInd G) :
    IsEssentiallyConstantInd c.pt := by
  obtain ⟨t, i₁, b₁, h₁⟩ := hF
  obtain ⟨t', i₂, b₂, h₂⟩ := hG
  obtain ⟨i₀, f₁, f₂, -⟩ := IsFilteredOrEmpty.cocone_objs i₁ i₂
  obtain ⟨-, h⟩ := h₁.comp_map f₁
  obtain ⟨-, h'⟩ := h₂.comp_map f₂
  have ext (m : I) {Z : C} (f g : Z ⟶ c.pt.obj m) (hfst : f ≫ c.fst.app m = g ≫ c.fst.app m)
      (hsnd : f ≫ c.snd.app m = g ≫ c.snd.app m) : f = g := by
    have ht := NatTrans.congr_app htot m
    simp only [NatTrans.app_add, NatTrans.comp_app, NatTrans.id_app] at ht
    rw [← Category.comp_id f, ← Category.comp_id g, ← ht]
    simp [Preadditive.comp_add, reassoc_of% hfst, reassoc_of% hsnd]
  refine ⟨Cocone.mk (t.pt ⊞ t'.pt) (c.fst ≫ t.ι ≫ (Functor.const I).map biprod.inl +
      c.snd ≫ t'.ι ≫ (Functor.const I).map biprod.inr), i₀,
      biprod.fst ≫ (b₁ ≫ F.map f₁) ≫ c.inl.app i₀ + biprod.snd ≫ (b₂ ≫ G.map f₂) ≫ c.inr.app i₀,
      ?_, fun j => ?_⟩
  · simp [Preadditive.add_comp, Preadditive.comp_add, reassoc_of% h₁.retraction,
      reassoc_of% h₂.retraction]
  · obtain ⟨k₁, v₁, u₁, hu₁⟩ := h j
    obtain ⟨k₂, v₂, u₂, hu₂⟩ := h' j
    obtain ⟨m, α, β, hu, hv⟩ := IsFiltered.bowtie u₁ u₂ v₁ v₂
    refine ⟨m, v₁ ≫ α, u₁ ≫ α, ext m _ _ ?_ ?_⟩
    · have := congrArg (· ≫ F.map α) hu₁
      simp only [Category.assoc] at this
      simp [Preadditive.add_comp, Preadditive.comp_add, this]
    · have e₁ := congrArg G.map hu
      have e₂ := congrArg G.map hv
      simp only [G.map_comp] at e₁ e₂
      simp [Preadditive.add_comp, Preadditive.comp_add, e₁, e₂, reassoc_of% hu₂]

end Witness

/-- Forward direction: if `F` and `G` are essentially constant, so is `F ⊞ G`. -/
lemma isEssentiallyConstantInd_biprod_of
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C] [Preadditive C]
    [HasFiniteBiproducts C]
    (F G : I ⥤ C)
    (hF : IsEssentiallyConstantInd F) (hG : IsEssentiallyConstantInd G) :
    haveI : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
    IsEssentiallyConstantInd (F ⊞ G) :=
  have : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
  isEssentiallyConstantInd_of_isBiproductBicone (BinaryBiproduct.bicone F G) biprod.total hF hG

/-- Backward direction (F-part): in an additive Karoubian category, if `F ⊞ G`
is essentially constant, so is `F`. -/
lemma isEssentiallyConstantInd_of_biprod_left
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C] [Preadditive C]
    [HasFiniteBiproducts C] [IsIdempotentComplete C]
    (F G : I ⥤ C)
    (h : haveI : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
         IsEssentiallyConstantInd (F ⊞ G)) :
    IsEssentiallyConstantInd F :=
  have : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
  isEssentiallyConstantInd_of_retract (biprod.inl : F ⟶ F ⊞ G) biprod.fst biprod.inl_fst h

/-- Backward direction (G-part). -/
lemma isEssentiallyConstantInd_of_biprod_right
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C] [Preadditive C]
    [HasFiniteBiproducts C] [IsIdempotentComplete C]
    (F G : I ⥤ C)
    (h : haveI : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
         IsEssentiallyConstantInd (F ⊞ G)) :
    IsEssentiallyConstantInd G :=
  have : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
  isEssentiallyConstantInd_of_retract (biprod.inr : G ⟶ F ⊞ G) biprod.snd biprod.inr_snd h

/-- Let `I` be a filtered category and `C` an additive Karoubian category. For
two functors `F, G : I ⥤ C`, the direct sum `F ⊞ G` is essentially constant
iff both `F` and `G` are essentially constant. -/
@[stacks 0A2G]
theorem isEssentiallyConstantInd_biprod_iff
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C] [Preadditive C]
    [HasFiniteBiproducts C] [IsIdempotentComplete C]
    (F G : I ⥤ C) :
    haveI : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
    IsEssentiallyConstantInd (F ⊞ G) ↔
      IsEssentiallyConstantInd F ∧ IsEssentiallyConstantInd G :=
  ⟨fun h => ⟨isEssentiallyConstantInd_of_biprod_left F G h,
      isEssentiallyConstantInd_of_biprod_right F G h⟩,
    fun ⟨hF, hG⟩ => isEssentiallyConstantInd_biprod_of F G hF hG⟩

end

section

/-!
## Stacks tag 070C

Characterization of essentially constant inverse systems in an abelian category.

For a directed preorder `ι` and an inverse system `F : ιᵒᵖ ⥤ 𝓐` with limit cone
`c`, the system is essentially constant if and only if there is an index `i₀`
and, for every `j ≥ i₀`, a direct-sum decomposition `F(j) ≅ c.pt ⊕ Z j` whose
transition maps are block-diagonal and whose `Z`-summand eventually vanishes.
-/

open CategoryTheory Limits Opposite

universe u

variable {ι : Type u} [Preorder ι]
variable {𝓐 : Type*} [Category 𝓐] [Abelian 𝓐]

/-- The direct-sum decomposition data for an inverse system with cone and
starting index. -/
structure DirectSumDecompositionData
    (F : ιᵒᵖ ⥤ 𝓐) (c : Cone F) (i₀ : ι) where
  Z : ∀ (j : ι), i₀ ≤ j → 𝓐
  iso : ∀ (j : ι) (hj : i₀ ≤ j), F.obj (op j) ≅ c.pt ⊞ Z j hj
  π_eq_inl : ∀ (j : ι) (hj : i₀ ≤ j),
    c.π.app (op j) ≫ (iso j hj).hom = biprod.inl
  Zmap : ∀ (j j' : ι) (hj : i₀ ≤ j) (hjj' : j ≤ j'),
    Z j' (le_trans hj hjj') ⟶ Z j hj
  map_compat : ∀ (j j' : ι) (hj : i₀ ≤ j) (hjj' : j ≤ j'),
    (iso j' (le_trans hj hjj')).inv ≫
        F.map (op (homOfLE hjj')) ≫ (iso j hj).hom =
      biprod.map (𝟙 c.pt) (Zmap j j' hj hjj')
  Z_eventually_zero : ∀ (j : ι) (hj : i₀ ≤ j),
    ∃ (j' : ι) (hjj' : j ≤ j'), Zmap j j' hj hjj' = 0

/-- `F` has a direct-sum decomposition: there is some `i₀` and a
`DirectSumDecompositionData` from `i₀`. -/
@[implicit_reducible]
def HasDirectSumDecomposition (F : ιᵒᵖ ⥤ 𝓐) (c : Cone F) : Prop :=
  ∃ (i₀ : ι), Nonempty (DirectSumDecompositionData F c i₀)

/-- A retraction splits its source as the target plus its kernel. -/
private lemma exists_kernel_biprod_iso {X Y : 𝓐}
    (s : X ⟶ Y) (r : Y ⟶ X) (h : s ≫ r = 𝟙 X) :
    ∃ e : Y ≅ X ⊞ kernel r,
      biprod.inl ≫ e.inv = s ∧ biprod.inr ≫ e.inv = kernel.ι r := by
  let q : Y ⟶ kernel r := kernel.lift r (𝟙 Y - r ≫ s) (by
    simp [Preadditive.sub_comp, h])
  have hq : q ≫ kernel.ι r = 𝟙 Y - r ≫ s := kernel.lift_ι _ _ _
  have hs : s ≫ q = 0 := by
    apply (cancel_mono (kernel.ι r)).1
    rw [Category.assoc, hq, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, h, Category.id_comp, sub_self, zero_comp]
  have hk : kernel.ι r ≫ q = 𝟙 _ := by
    apply (cancel_mono (kernel.ι r)).1
    simp [hq, Preadditive.comp_sub]
  refine ⟨{ hom := biprod.lift r q
            inv := biprod.desc s (kernel.ι r)
            hom_inv_id := ?_
            inv_hom_id := ?_ }, by simp, by simp⟩
  · rw [biprod.lift_desc, hq]
    abel
  · apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [h, hs, hk]

/-- Forward direction: from an index `i` and a section `s` of the cone projection at `i` through
which the transition maps eventually factor, construct `DirectSumDecompositionData F c i`. -/
lemma essentially_constant_to_direct_sum
    (F : ιᵒᵖ ⥤ 𝓐) (c : Cone F) (i : ι) (s : F.obj (op i) ⟶ c.pt)
    (hs : c.π.app (op i) ≫ s = 𝟙 c.pt)
    (hfac : ∀ j : ι, ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      F.map (op (homOfLE hjk)) = F.map (op (homOfLE hik)) ≫ s ≫ c.π.app (op j)) :
    Nonempty (DirectSumDecompositionData F c i) := by
  let r (j : ι) (hj : i ≤ j) : F.obj (op j) ⟶ c.pt :=
    F.map (op (homOfLE hj)) ≫ s
  have hr (j : ι) (hj : i ≤ j) : c.π.app (op j) ≫ r j hj = 𝟙 _ := by
    simpa [r] using hs
  have hmap (j j' : ι) (hj : i ≤ j) (hjj' : j ≤ j') :
      F.map (op (homOfLE hjj')) ≫ r j hj = r j' (le_trans hj hjj') := by
    simp only [r, ← Category.assoc, ← F.map_comp]
    rfl
  choose e heinl heinr using fun j hj =>
    exists_kernel_biprod_iso (c.π.app (op j)) (r j hj) (hr j hj)
  have hπ (j : ι) (hj : i ≤ j) :
      c.π.app (op j) ≫ (e j hj).hom = biprod.inl := by
    apply (cancel_mono (e j hj).inv).1
    simp [heinl]
  let zmap (j j' : ι) (hj : i ≤ j) (hjj' : j ≤ j') :
      kernel (r j' (le_trans hj hjj')) ⟶ kernel (r j hj) :=
    kernel.lift _ (kernel.ι _ ≫ F.map (op (homOfLE hjj'))) (by
      rw [Category.assoc, hmap, kernel.condition])
  have hzmap (j j' : ι) (hj : i ≤ j) (hjj' : j ≤ j') :
      zmap j j' hj hjj' ≫ kernel.ι (r j hj) =
        kernel.ι _ ≫ F.map (op (homOfLE hjj')) := kernel.lift_ι _ _ _
  refine ⟨{ Z := fun j hj => kernel (r j hj)
            iso := e
            π_eq_inl := hπ
            Zmap := zmap
            map_compat := ?_
            Z_eventually_zero := ?_ }⟩
  · intro j j' hj hjj'
    apply biprod.hom_ext'
    · simp only [← Category.assoc, heinl, Cone.w, biprod.inl_map, Category.id_comp]
      exact hπ j hj
    · simp only [← Category.assoc, heinr, biprod.inr_map]
      rw [← hzmap j j' hj hjj']
      have hk : kernel.ι (r j hj) ≫ (e j hj).hom = biprod.inr := by
        apply (cancel_mono (e j hj).inv).1
        simp [heinr]
      rw [Category.assoc]
      exact congrArg (fun f => zmap j j' hj hjj' ≫ f) hk
  · intro j hj
    obtain ⟨k, hik, hjk, hk⟩ := hfac j
    refine ⟨k, hjk, ?_⟩
    apply (cancel_mono (kernel.ι (r j hj))).1
    rw [hzmap, zero_comp, hk]
    simpa only [r, Category.assoc, zero_comp] using
      kernel.condition_assoc (r k hik) (c.π.app (op j))

/-- Backward direction: a `DirectSumDecompositionData` gives an essential-constancy witness. -/
lemma direct_sum_to_essentially_constant
    [IsDirected ι (· ≤ ·)]
    (F : ιᵒᵖ ⥤ 𝓐) (c : Cone F)
    (i₀ : ι) (d : DirectSumDecompositionData F c i₀) :
    ∃ (i : ιᵒᵖ) (s : F.obj i ⟶ c.pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith F c i s := by
  let r (j : ι) (hj : i₀ ≤ j) : F.obj (op j) ⟶ c.pt :=
    (d.iso j hj).hom ≫ biprod.fst
  have hr (j : ι) (hj : i₀ ≤ j) : c.π.app (op j) ≫ r j hj = 𝟙 _ := by
    simp [r, ← Category.assoc, d.π_eq_inl]
  have hmap (j j' : ι) (hj : i₀ ≤ j) (hjj' : j ≤ j') :
      F.map (op (homOfLE hjj')) ≫ r j hj = r j' (le_trans hj hjj') := by
    apply (cancel_epi (d.iso j' (le_trans hj hjj')).inv).1
    simpa [r] using
      congrArg (fun f => f ≫ biprod.fst) (d.map_compat j j' hj hjj')
  have hzero (j j' : ι) (hj : i₀ ≤ j) (hjj' : j ≤ j')
      (hz : d.Zmap j j' hj hjj' = 0) :
      F.map (op (homOfLE hjj')) = r j' (le_trans hj hjj') ≫ c.π.app (op j) := by
    apply (cancel_epi (d.iso j' (le_trans hj hjj')).inv).1
    apply (cancel_mono (d.iso j hj).hom).1
    simpa [r, d.π_eq_inl, hz, biprod.map_eq] using
      d.map_compat j j' hj hjj'
  refine ⟨op i₀, r i₀ le_rfl, ⟨hr i₀ le_rfl, fun j => ?_⟩⟩
  obtain ⟨l, hil, hjl⟩ := directed_of (· ≤ ·) i₀ j.unop
  obtain ⟨k, hlk, hk⟩ := d.Z_eventually_zero l hil
  refine ⟨op k, op (homOfLE (le_trans hil hlk)), op (homOfLE (le_trans hjl hlk)), ?_⟩
  rw [← Category.assoc, hmap]
  calc
    F.map (op (homOfLE (le_trans hjl hlk))) =
        F.map (op (homOfLE hlk)) ≫ F.map (op (homOfLE hjl)) := by
      rw [← F.map_comp]
      rfl
    _ = r k (le_trans hil hlk) ≫ c.π.app (op l) ≫
        F.map (op (homOfLE hjl)) := by rw [hzero l k hil hlk hk, Category.assoc]
    _ = _ := by rw [Cone.w]

/-- For a directed preorder `ι` and an inverse system `F : ιᵒᵖ ⥤ 𝓐` in an
abelian category with a limit cone `c`, the system is essentially constant if
and only if there is an index `i₀` admitting a compatible direct-sum
decomposition with eventually-vanishing `Z`-summand. -/
@[stacks 070C]
theorem essentially_constant_iff_direct_sum_decomposition
    [IsDirected ι (· ≤ ·)]
    (F : ιᵒᵖ ⥤ 𝓐) (c : Cone F) (_hc : IsLimit c) :
    (∃ (i : ιᵒᵖ) (s : F.obj i ⟶ c.pt),
        EssentiallyConstantPro.IsEssentiallyConstantWith F c i s) ↔
      HasDirectSumDecomposition F c := by
  refine ⟨fun ⟨i, s, h⟩ => ?_, fun ⟨i₀, ⟨d⟩⟩ => direct_sum_to_essentially_constant F c i₀ d⟩
  refine ⟨i.unop, essentially_constant_to_direct_sum F c i.unop s h.retraction fun j => ?_⟩
  obtain ⟨k, σ, τ, e⟩ := h.cofinal (op j)
  refine ⟨k.unop, leOfHom σ.unop, leOfHom τ.unop, ?_⟩
  rw [show op (homOfLE (leOfHom τ.unop)) = τ from Subsingleton.elim _ _,
    show op (homOfLE (leOfHom σ.unop)) = σ from Subsingleton.elim _ _]
  exact e

end
