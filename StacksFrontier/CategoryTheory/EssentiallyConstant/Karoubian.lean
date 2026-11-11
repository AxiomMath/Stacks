module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Cofinal
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Initial
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Operations

/-!
# Essentially constant systems in Karoubian categories

Let `M : I ⥤ A` be a diagram in a preadditive Karoubian category. When `I` is filtered, `M` is
essentially constant (Stacks 05PU) if and only if `X = colim M` exists and, over a cofinal filtered
subcategory `I'` of `I`, every `M i'` splits as a direct sum `X_{i'} ⊕ Z_{i'}` in which `X_{i'}`
maps isomorphically onto `X` and `Z_{i'}` dies under some transition map `M i' ⟶ M i''` of `I'`.
Dually, when `I` is cofiltered, `M` is essentially constant if and only if `X = lim M` exists and,
over an initial cofiltered subcategory, every `M i'` splits as `X_{i'} ⊕ Z_{i'}` with `X` mapping
isomorphically onto `X_{i'}` and some transition map `M i'' ⟶ M i'` of `I'` vanishing into
`Z_{i'}`.

## Main results

* `CategoryTheory.EssentiallyConstantInd.isEssentiallyConstantInd_iff_exists_subcategory`:
  Stacks 0A2E (1), the filtered case.
* `CategoryTheory.EssentiallyConstantPro.isEssentiallyConstantPro_iff_exists_subcategory`:
  Stacks 0A2E (2), the cofiltered case.
* `CategoryTheory.EssentiallyConstantInd.isEssentiallyConstantInd_iff_exists_biproduct` and
  `CategoryTheory.EssentiallyConstantPro.isEssentiallyConstantPro_iff_exists_biproduct`: the
  variants in which the subcategory `I'` is required to be full.
* `CategoryTheory.EssentiallyConstantInd.isEssentiallyConstantWith_of_forall_exists`: a diagram
  over a filtered category is essentially constant as soon as every coprojection `c_j` has a
  section `s_j` such that some transition map `M_j ⟶ M_a` factors as `c_j ≫ s_j` followed by
  itself. Its dual is
  `CategoryTheory.EssentiallyConstantPro.isEssentiallyConstantWith_of_forall_exists`.
* `CategoryTheory.Limits.exists_isBilimit_of_retraction`: in a preadditive Karoubian category a
  retraction `s ≫ r = 𝟙 X` of `s : X ⟶ Y` exhibits `Y` as a direct sum of `X` and a complement.

## Implementation notes

A (not necessarily full) subcategory `I' ⊂ I` of the source (Stacks 0012) is encoded as a
faithful functor `H : I' ⥤ I` injective on objects, i.e. a category isomorphic to a subcategory
via `H`; "cofinal" (resp. "initial") is `H.Final` (resp. `H.Initial`), the Stacks notion for
functors between filtered (resp. cofiltered) categories. The implication (b) ⇒ (a) is proved
for an arbitrary final (resp. initial) functor from a filtered (resp. cofiltered) category, with
neither faithfulness nor injectivity on objects; for (a) ⇒ (b) the functor produced is the
inclusion of the full subcategory of objects receiving (resp. admitting) a morphism from (resp.
to) the index of an essential-constancy witness.

A direct sum decomposition `M_{i'} = X_{i'} ⊕ Z_{i'}` is a bilimit binary bicone on
`X_{i'}, Z_{i'}` together with an isomorphism of its cone point with `M_{i'}`; no binary
biproducts are assumed to exist in `A`.

## References

* [Stacks: Tag 0A2E](https://stacks.math.columbia.edu/tag/0A2E)
-/

public section

open CategoryTheory Limits

universe v u v' u'

namespace CategoryTheory

namespace Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [IsIdempotentComplete C]

/-- In a preadditive Karoubian category, if `s : X ⟶ Y` has a retraction `r`, then `Y` is a direct
sum of `X` and a complement `Z`, with `s` the inclusion and `r` the projection of the summand
`X`. -/
theorem exists_isBilimit_of_retraction {X Y : C} (s : X ⟶ Y) (r : Y ⟶ X) (h : s ≫ r = 𝟙 X) :
    ∃ (Z : C) (b : BinaryBicone X Z) (_ : b.IsBilimit) (e : b.pt ≅ Y),
      b.inl ≫ e.hom = s ∧ e.inv ≫ b.fst = r := by
  have hp : (𝟙 Y - r ≫ s) ≫ (𝟙 Y - r ≫ s) = 𝟙 Y - r ≫ s := by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, reassoc_of% h]
  obtain ⟨Z, i, p, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split Y _ hp
  have hsp : s ≫ p = 0 := by
    have : s ≫ p = s ≫ (p ≫ i) ≫ p := by rw [Category.assoc, h₁, Category.comp_id]
    rw [this, h₂]
    simp [Preadditive.sub_comp, Preadditive.comp_sub, reassoc_of% h]
  have hir : i ≫ r = 0 := by
    have : i ≫ r = i ≫ (p ≫ i) ≫ r := by simp [reassoc_of% h₁]
    rw [this, h₂]
    simp [Preadditive.sub_comp, h]
  let b : BinaryBicone X Z :=
    { pt := Y, fst := r, snd := p, inl := s, inr := i
      inl_fst := h, inl_snd := hsp, inr_fst := hir, inr_snd := h₁ }
  refine ⟨Z, b, isBinaryBilimitOfTotal b ?_, Iso.refl _, by simp [b], by simp [b]⟩
  change r ≫ s + p ≫ i = 𝟙 Y
  rw [h₂]
  abel

end Limits

namespace EssentiallyConstantInd

variable {C : Type u} [Category.{v} C] {I : Type u'} [Category.{v'} I]

/-- Let `t` be a cocone on `M : I ⥤ C` over a filtered category. Suppose that each coprojection
`t.ι.app j` has a section `s j`, and that for each `j` some transition map `M.map f` out of `M j`
factors as `t.ι.app j ≫ s j ≫ M.map f`. Then `M` is essentially constant with value `t.pt`,
witnessed at any index `i` by `s i`. -/
theorem isEssentiallyConstantWith_of_forall_exists [IsFilteredOrEmpty I] {M : I ⥤ C}
    (t : Cocone M) (s : ∀ j, t.pt ⟶ M.obj j) (hs : ∀ j, s j ≫ t.ι.app j = 𝟙 t.pt)
    (hf : ∀ j, ∃ (a : I) (f : j ⟶ a), M.map f = t.ι.app j ≫ s j ≫ M.map f) (i : I) :
    IsEssentiallyConstantWith M t i (s i) where
  retraction := hs i
  cofinal j := by
    obtain ⟨a, f, hfa⟩ := hf j
    obtain ⟨b, g, hg⟩ := hf (IsFiltered.max a i)
    have key : ∀ u : t.pt ⟶ M.obj (IsFiltered.max a i), u ≫ t.ι.app _ = 𝟙 t.pt →
        u ≫ M.map g = s _ ≫ M.map g := by
      intro u hu
      conv_lhs => rw [hg]
      rw [← Category.assoc, hu, Category.id_comp]
    refine ⟨b, IsFiltered.rightToMax a i ≫ g, f ≫ IsFiltered.leftToMax a i ≫ g, ?_⟩
    have h₁ := key (s j ≫ M.map (f ≫ IsFiltered.leftToMax a i)) (by
      rw [Category.assoc, t.w, hs])
    have h₂ := key (s i ≫ M.map (IsFiltered.rightToMax a i)) (by
      rw [Category.assoc, t.w, hs])
    simp only [Functor.map_comp, Category.assoc] at h₁ h₂ ⊢
    rw [hfa]
    simp only [Category.assoc]
    rw [h₁, h₂]

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The forward direction of Stacks 0A2E (1), in its strongest form: an essentially constant
diagram over a filtered category splits as in `isEssentiallyConstantInd_iff_exists_subcategory`
over a full subcategory `I'`, i.e. along a fully faithful final functor `H : I' ⥤ I` that is
injective on objects. -/
theorem exists_fullSubcategory_biproduct_of_isEssentiallyConstantInd [IsFiltered I]
    [IsIdempotentComplete A] {M : I ⥤ A} (h : IsEssentiallyConstantInd M) :
    ∃ (_ : HasColimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsFiltered I')
      (H : I' ⥤ I) (_ : H.Full) (_ : H.Faithful) (_ : Function.Injective H.obj) (_ : H.Final),
      ∀ i' : I',
        ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
          IsIso (b.inl ≫ e.hom ≫ colimit.ι M (H.obj i')) ∧
          ∃ (i'' : I') (f : i' ⟶ i''), b.inr ≫ e.hom ≫ M.map (H.map f) = 0 := by
  have hc : HasColimit M := h.hasColimit
  obtain ⟨i, r, hr⟩ := h.exists_retraction_colimit
  let P : ObjectProperty I := fun j => Nonempty (i ⟶ j)
  have hP : ∀ d, ∃ c : P.FullSubcategory, Nonempty (d ⟶ P.ι.obj c) := fun d =>
    ⟨⟨IsFiltered.max i d, ⟨IsFiltered.leftToMax i d⟩⟩, ⟨IsFiltered.rightToMax i d⟩⟩
  refine ⟨hc, P.FullSubcategory, inferInstance,
    IsFiltered.of_exists_of_isFiltered_of_fullyFaithful P.ι hP, P.ι, inferInstance,
    inferInstance, fun _ _ h => ObjectProperty.FullSubcategory.ext h,
    Functor.final_of_exists_of_isFiltered_of_fullyFaithful P.ι hP, fun j => ?_⟩
  have hsec : (r ≫ M.map j.property.some) ≫ colimit.ι M j.obj = 𝟙 _ := by
    simpa using hr.retraction
  obtain ⟨Z, b, hb, e, hinl, hfst⟩ := Limits.exists_isBilimit_of_retraction _ _ hsec
  have he : e.hom ≫ colimit.ι M j.obj = b.fst := by rw [← hfst, Iso.hom_inv_id_assoc]
  obtain ⟨k, σ, τ, hτ⟩ := hr.cofinal j.obj
  refine ⟨_, Z, b, hb, e, ?_, ⟨k, ⟨σ⟩⟩, ObjectProperty.homMk τ, ?_⟩
  · change IsIso (b.inl ≫ e.hom ≫ colimit.ι M j.obj)
    rw [reassoc_of% hinl, ← Category.assoc, hsec]
    infer_instance
  · change b.inr ≫ e.hom ≫ M.map τ = 0
    rw [hτ]
    simp only [colimit.cocone_ι]
    rw [reassoc_of% he, b.inr_fst_assoc, zero_comp]

/-- The forward direction of Stacks 0A2E (1) along a fully faithful final functor: an
essentially constant diagram over a filtered category splits as in
`isEssentiallyConstantInd_iff_exists_biproduct`. -/
theorem exists_biproduct_of_isEssentiallyConstantInd [IsFiltered I] [IsIdempotentComplete A]
    {M : I ⥤ A} (h : IsEssentiallyConstantInd M) :
    ∃ (_ : HasColimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsFiltered I')
      (H : I' ⥤ I) (_ : H.Full) (_ : H.Faithful) (_ : H.Final), ∀ i' : I',
        ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
          IsIso (b.inl ≫ e.hom ≫ colimit.ι M (H.obj i')) ∧
          ∃ (i'' : I') (f : i' ⟶ i''), b.inr ≫ e.hom ≫ M.map (H.map f) = 0 := by
  obtain ⟨hc, I', cI, fI, H, hF, hF', _, hH, h⟩ :=
    exists_fullSubcategory_biproduct_of_isEssentiallyConstantInd h
  exact ⟨hc, I', cI, fI, H, hF, hF', hH, h⟩

/-- The backward direction of Stacks 0A2E (1), for an arbitrary final functor `H : I' ⥤ I` from a
filtered category (in particular for the inclusion of any cofinal filtered subcategory): a diagram
over a filtered category splitting as in `isEssentiallyConstantInd_iff_exists_subcategory` is
essentially constant. -/
theorem isEssentiallyConstantInd_of_final_of_exists_biproduct [IsFiltered I]
    [IsIdempotentComplete A] {M : I ⥤ A}
    (h : ∃ (_ : HasColimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsFiltered I')
      (H : I' ⥤ I) (_ : H.Final), ∀ i' : I',
        ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
          IsIso (b.inl ≫ e.hom ≫ colimit.ι M (H.obj i')) ∧
          ∃ (i'' : I') (f : i' ⟶ i''), b.inr ≫ e.hom ≫ M.map (H.map f) = 0) :
    IsEssentiallyConstantInd M := by
  obtain ⟨hc, I', cI, fI, H, _, h⟩ := h
  apply essentiallyConstant_of_comp_final H M
  choose X' Z' b hb e hiso i'' f hf using h
  let t : Cocone (H ⋙ M) := (colimit.cocone M).whisker H
  let s : ∀ j, t.pt ⟶ (H ⋙ M).obj j := fun j =>
    inv ((b j).inl ≫ (e j).hom ≫ colimit.ι M (H.obj j)) ≫ (b j).inl ≫ (e j).hom
  refine ⟨t, (IsFiltered.nonempty (C := I')).some, _,
    isEssentiallyConstantWith_of_forall_exists t s (fun j => ?_) (fun j => ⟨i'' j, f j, ?_⟩) _⟩
  · simp [t, s]
  · have htot : (b j).fst ≫ (b j).inl = 𝟙 _ - (b j).snd ≫ (b j).inr := by
      rw [← Limits.IsBilimit.binary_total (hb j)]
      abel
    have hz : (b j).inr ≫ (e j).hom ≫ colimit.ι M (H.obj j) = 0 := by
      rw [← colimit.w M (H.map (f j)), reassoc_of% (hf j), zero_comp]
    have hfst : (e j).inv ≫ (b j).fst ≫
        ((b j).inl ≫ (e j).hom ≫ colimit.ι M (H.obj j)) = colimit.ι M (H.obj j) := by
      rw [← Category.assoc (b j).fst, htot]
      simp [Preadditive.sub_comp, hz]
    have hM : M.map (H.map (f j)) =
        (e j).inv ≫ (b j).fst ≫ (b j).inl ≫ (e j).hom ≫ M.map (H.map (f j)) := by
      rw [← Category.assoc (b j).fst, htot]
      simp [Preadditive.sub_comp, hf j]
    have hc' : colimit.ι M (H.obj j) ≫
        inv ((b j).inl ≫ (e j).hom ≫ colimit.ι M (H.obj j)) = (e j).inv ≫ (b j).fst := by
      rw [IsIso.comp_inv_eq, Category.assoc, hfst]
    change M.map (H.map (f j)) = colimit.ι M (H.obj j) ≫ s j ≫ M.map (H.map (f j))
    simp only [s, Category.assoc]
    rw [reassoc_of% hc', ← hM]

/-- The backward direction of Stacks 0A2E (1) along a fully faithful final functor: a diagram over
a filtered category splitting as in `isEssentiallyConstantInd_iff_exists_biproduct` is
essentially constant. See `isEssentiallyConstantInd_of_final_of_exists_biproduct` for an
arbitrary final functor. -/
theorem isEssentiallyConstantInd_of_exists_biproduct [IsFiltered I] [IsIdempotentComplete A]
    {M : I ⥤ A}
    (h : ∃ (_ : HasColimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsFiltered I')
      (H : I' ⥤ I) (_ : H.Full) (_ : H.Faithful) (_ : H.Final), ∀ i' : I',
        ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
          IsIso (b.inl ≫ e.hom ≫ colimit.ι M (H.obj i')) ∧
          ∃ (i'' : I') (f : i' ⟶ i''), b.inr ≫ e.hom ≫ M.map (H.map f) = 0) :
    IsEssentiallyConstantInd M := by
  obtain ⟨hc, I', cI, fI, H, _, _, hH, h⟩ := h
  exact isEssentiallyConstantInd_of_final_of_exists_biproduct ⟨hc, I', cI, fI, H, hH, h⟩

/-- A variant of Stacks 0A2E (1) in which the subcategory `I'` is required to be full. Let
`M : I ⥤ A` be a diagram over a filtered category in a preadditive Karoubian category. Then `M` is
essentially constant if and only if `colim M` exists and there are a filtered category `I'` with a
fully faithful cofinal functor `H : I' ⥤ I` and, for each `i' : I'`, a direct sum
decomposition `M (H i') ≅ X_{i'} ⊕ Z_{i'}` such that `X_{i'}` maps isomorphically to `colim M` and
`Z_{i'}` maps to zero in `M (H i'')` for some `i' ⟶ i''` in `I'`. The Stacks statement, over an
arbitrary (not necessarily full) cofinal filtered subcategory, is
`isEssentiallyConstantInd_iff_exists_subcategory`. -/
theorem isEssentiallyConstantInd_iff_exists_biproduct [IsFiltered I] [IsIdempotentComplete A]
    (M : I ⥤ A) :
    IsEssentiallyConstantInd M ↔
      ∃ (_ : HasColimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsFiltered I')
        (H : I' ⥤ I) (_ : H.Full) (_ : H.Faithful) (_ : H.Final), ∀ i' : I',
          ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
            IsIso (b.inl ≫ e.hom ≫ colimit.ι M (H.obj i')) ∧
            ∃ (i'' : I') (f : i' ⟶ i''), b.inr ≫ e.hom ≫ M.map (H.map f) = 0 :=
    ⟨exists_biproduct_of_isEssentiallyConstantInd, isEssentiallyConstantInd_of_exists_biproduct⟩

/-- Stacks 0A2E (1). Let `M : I ⥤ A` be a diagram over a filtered category in a preadditive
Karoubian category. Then `M` is essentially constant if and only if `colim M` exists and there are
a cofinal filtered subcategory `I'` of `I` (a filtered category `I'` with a faithful final functor
`H : I' ⥤ I` injective on objects, i.e. an isomorphism onto a subcategory) and, for each `i' : I'`,
a direct sum decomposition `M (H i') ≅ X_{i'} ⊕ Z_{i'}` such that `X_{i'}` maps isomorphically to
`colim M` and `Z_{i'}` maps to zero in `M (H i'')` for some `i' ⟶ i''` in `I'`. -/
@[stacks 0A2E "(1)"]
theorem isEssentiallyConstantInd_iff_exists_subcategory [IsFiltered I] [IsIdempotentComplete A]
    (M : I ⥤ A) :
    IsEssentiallyConstantInd M ↔
      ∃ (_ : HasColimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsFiltered I')
        (H : I' ⥤ I) (_ : H.Faithful) (_ : Function.Injective H.obj) (_ : H.Final), ∀ i' : I',
          ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
            IsIso (b.inl ≫ e.hom ≫ colimit.ι M (H.obj i')) ∧
            ∃ (i'' : I') (f : i' ⟶ i''), b.inr ≫ e.hom ≫ M.map (H.map f) = 0 := by
  refine ⟨fun h => ?_, fun ⟨hc, I', cI, fI, H, _, _, hH, h⟩ =>
    isEssentiallyConstantInd_of_final_of_exists_biproduct ⟨hc, I', cI, fI, H, hH, h⟩⟩
  obtain ⟨hc, I', cI, fI, H, _, hF, hinj, hH, h⟩ :=
    exists_fullSubcategory_biproduct_of_isEssentiallyConstantInd h
  exact ⟨hc, I', cI, fI, H, hF, hinj, hH, h⟩

end EssentiallyConstantInd

namespace EssentiallyConstantPro

variable {C : Type u} [Category.{v} C] {I : Type u'} [Category.{v'} I]

/-- Let `t` be a cone on `M : I ⥤ C` over a cofiltered category. Suppose that each projection
`t.π.app j` has a retraction `s j`, and that for each `j` some transition map `M.map f` into `M j`
factors as `M.map f ≫ s j ≫ t.π.app j`. Then `M` is essentially constant with value `t.pt`,
witnessed at any index `i` by `s i`. -/
theorem isEssentiallyConstantWith_of_forall_exists [IsCofilteredOrEmpty I] {M : I ⥤ C}
    (t : Cone M) (s : ∀ j, M.obj j ⟶ t.pt) (hs : ∀ j, t.π.app j ≫ s j = 𝟙 t.pt)
    (hf : ∀ j, ∃ (a : I) (f : a ⟶ j), M.map f = M.map f ≫ s j ≫ t.π.app j) (i : I) :
    IsEssentiallyConstantWith M t i (s i) where
  retraction := hs i
  cofinal j := by
    obtain ⟨a, f, hfa⟩ := hf j
    obtain ⟨b, g, hg⟩ := hf (IsCofiltered.min a i)
    have key : ∀ u : M.obj (IsCofiltered.min a i) ⟶ t.pt, t.π.app _ ≫ u = 𝟙 t.pt →
        M.map g ≫ u = M.map g ≫ s _ := by
      intro u hu
      conv_lhs => rw [hg]
      rw [Category.assoc, Category.assoc, hu, Category.comp_id]
    refine ⟨b, g ≫ IsCofiltered.minToRight a i, g ≫ IsCofiltered.minToLeft a i ≫ f, ?_⟩
    have h₁ := key (M.map (IsCofiltered.minToLeft a i ≫ f) ≫ s j) (by
      rw [t.w_assoc, hs])
    have h₂ := key (M.map (IsCofiltered.minToRight a i) ≫ s i) (by
      rw [t.w_assoc, hs])
    simp only [Functor.map_comp, Category.assoc] at h₁ h₂ ⊢
    rw [hfa, reassoc_of% h₁, reassoc_of% h₂]

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The forward direction of Stacks 0A2E (2), in its strongest form: an essentially constant
diagram over a cofiltered category splits as in `isEssentiallyConstantPro_iff_exists_subcategory`
over a full subcategory `I'`, i.e. along a fully faithful initial functor `H : I' ⥤ I` that is
injective on objects. -/
theorem exists_fullSubcategory_biproduct_of_isEssentiallyConstantPro [IsCofiltered I]
    [IsIdempotentComplete A] {M : I ⥤ A} (h : IsEssentiallyConstantPro M) :
    ∃ (_ : HasLimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsCofiltered I')
      (H : I' ⥤ I) (_ : H.Full) (_ : H.Faithful) (_ : Function.Injective H.obj) (_ : H.Initial),
      ∀ i' : I',
        ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
          IsIso (limit.π M (H.obj i') ≫ e.inv ≫ b.fst) ∧
          ∃ (i'' : I') (f : i'' ⟶ i'), M.map (H.map f) ≫ e.inv ≫ b.snd = 0 := by
  rw [isEssentiallyConstantPro_iff_op] at h
  have hc : HasLimit M := h.hasLimit_of_op
  obtain ⟨i, r, hr⟩ := h.exists_retraction_op_limit
  have hr' : IsEssentiallyConstantWith M (limit.cone M) i.unop r.unop :=
    isEssentiallyConstantWith_of_op hr
  let P : ObjectProperty I := fun j => Nonempty (j ⟶ i.unop)
  have hP : ∀ d, ∃ c : P.FullSubcategory, Nonempty (P.ι.obj c ⟶ d) := fun d =>
    ⟨⟨IsCofiltered.min i.unop d, ⟨IsCofiltered.minToLeft i.unop d⟩⟩,
      ⟨IsCofiltered.minToRight i.unop d⟩⟩
  refine ⟨hc, P.FullSubcategory, inferInstance,
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful P.ι hP, P.ι, inferInstance,
    inferInstance, fun _ _ h => ObjectProperty.FullSubcategory.ext h,
    Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful P.ι hP, fun j => ?_⟩
  have hsec : limit.π M j.obj ≫ (M.map j.property.some ≫ r.unop) = 𝟙 _ := by
    simpa using hr'.retraction
  obtain ⟨Z, b, hb, e, hinl, hfst⟩ := Limits.exists_isBilimit_of_retraction _ _ hsec
  have he : limit.π M j.obj ≫ e.inv = b.inl := by
    rw [← hinl, Category.assoc, e.hom_inv_id, Category.comp_id]
  obtain ⟨k, σ, τ, hτ⟩ := hr'.cofinal j.obj
  refine ⟨_, Z, b, hb, e, ?_, ⟨k, ⟨σ⟩⟩, ObjectProperty.homMk τ, ?_⟩
  · change IsIso (limit.π M j.obj ≫ e.inv ≫ b.fst)
    rw [hfst, hsec]
    infer_instance
  · change M.map τ ≫ e.inv ≫ b.snd = 0
    rw [hτ]
    simp only [limit.cone_π, Category.assoc]
    rw [reassoc_of% he, b.inl_snd, comp_zero, comp_zero]

/-- The forward direction of Stacks 0A2E (2) along a fully faithful initial functor: an
essentially constant diagram over a cofiltered category splits as in
`isEssentiallyConstantPro_iff_exists_biproduct`. -/
theorem exists_biproduct_of_isEssentiallyConstantPro [IsCofiltered I] [IsIdempotentComplete A]
    {M : I ⥤ A} (h : IsEssentiallyConstantPro M) :
    ∃ (_ : HasLimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsCofiltered I')
      (H : I' ⥤ I) (_ : H.Full) (_ : H.Faithful) (_ : H.Initial), ∀ i' : I',
        ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
          IsIso (limit.π M (H.obj i') ≫ e.inv ≫ b.fst) ∧
          ∃ (i'' : I') (f : i'' ⟶ i'), M.map (H.map f) ≫ e.inv ≫ b.snd = 0 := by
  obtain ⟨hc, I', cI, fI, H, hF, hF', _, hH, h⟩ :=
    exists_fullSubcategory_biproduct_of_isEssentiallyConstantPro h
  exact ⟨hc, I', cI, fI, H, hF, hF', hH, h⟩

/-- The backward direction of Stacks 0A2E (2), for an arbitrary initial functor `H : I' ⥤ I` from
a cofiltered category (in particular for the inclusion of any initial cofiltered subcategory): a
diagram over a cofiltered category splitting as in
`isEssentiallyConstantPro_iff_exists_subcategory` is essentially constant. -/
theorem isEssentiallyConstantPro_of_initial_of_exists_biproduct [IsCofiltered I]
    [IsIdempotentComplete A] {M : I ⥤ A}
    (h : ∃ (_ : HasLimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsCofiltered I')
      (H : I' ⥤ I) (_ : H.Initial), ∀ i' : I',
        ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
          IsIso (limit.π M (H.obj i') ≫ e.inv ≫ b.fst) ∧
          ∃ (i'' : I') (f : i'' ⟶ i'), M.map (H.map f) ≫ e.inv ≫ b.snd = 0) :
    IsEssentiallyConstantPro M := by
  obtain ⟨hc, I', cI, fI, H, _, h⟩ := h
  apply essentiallyConstant_of_comp_initial H M
  choose X' Z' b hb e hiso i'' f hf using h
  let t : Cone (H ⋙ M) := (limit.cone M).whisker H
  let s : ∀ j, (H ⋙ M).obj j ⟶ t.pt := fun j =>
    (e j).inv ≫ (b j).fst ≫ inv (limit.π M (H.obj j) ≫ (e j).inv ≫ (b j).fst)
  refine ⟨t, (IsCofiltered.nonempty (C := I')).some, _,
    isEssentiallyConstantWith_of_forall_exists t s (fun j => ?_) (fun j => ⟨i'' j, f j, ?_⟩) _⟩
  · have := IsIso.hom_inv_id (limit.π M (H.obj j) ≫ (e j).inv ≫ (b j).fst)
    simp only [Category.assoc] at this
    exact this
  · have hz : limit.π M (H.obj j) ≫ (e j).inv ≫ (b j).snd = 0 := by
      rw [← limit.w M (H.map (f j)), Category.assoc, hf j, comp_zero]
    have htot : (b j).fst ≫ (b j).inl = 𝟙 _ - (b j).snd ≫ (b j).inr := by
      rw [← Limits.IsBilimit.binary_total (hb j)]
      abel
    have hinl : (limit.π M (H.obj j) ≫ (e j).inv ≫ (b j).fst) ≫ (b j).inl ≫ (e j).hom =
        limit.π M (H.obj j) := by
      simp only [Category.assoc]
      rw [reassoc_of% htot]
      simp [Preadditive.sub_comp, Preadditive.comp_sub, reassoc_of% hz]
    have hM : M.map (H.map (f j)) =
        M.map (H.map (f j)) ≫ (e j).inv ≫ (b j).fst ≫ (b j).inl ≫ (e j).hom := by
      rw [reassoc_of% htot]
      simp [Preadditive.sub_comp, Preadditive.comp_sub, reassoc_of% (hf j)]
    have hc' : inv (limit.π M (H.obj j) ≫ (e j).inv ≫ (b j).fst) ≫ limit.π M (H.obj j) =
        (b j).inl ≫ (e j).hom := by
      rw [IsIso.inv_comp_eq, hinl]
    change M.map (H.map (f j)) = M.map (H.map (f j)) ≫ s j ≫ limit.π M (H.obj j)
    simp only [s, Category.assoc]
    rw [hc']
    exact hM

/-- The backward direction of Stacks 0A2E (2) along a fully faithful initial functor: a diagram
over a cofiltered category splitting as in `isEssentiallyConstantPro_iff_exists_biproduct` is
essentially constant. See `isEssentiallyConstantPro_of_initial_of_exists_biproduct` for an
arbitrary initial functor. -/
theorem isEssentiallyConstantPro_of_exists_biproduct [IsCofiltered I] [IsIdempotentComplete A]
    {M : I ⥤ A}
    (h : ∃ (_ : HasLimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsCofiltered I')
      (H : I' ⥤ I) (_ : H.Full) (_ : H.Faithful) (_ : H.Initial), ∀ i' : I',
        ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
          IsIso (limit.π M (H.obj i') ≫ e.inv ≫ b.fst) ∧
          ∃ (i'' : I') (f : i'' ⟶ i'), M.map (H.map f) ≫ e.inv ≫ b.snd = 0) :
    IsEssentiallyConstantPro M := by
  obtain ⟨hc, I', cI, fI, H, _, _, hH, h⟩ := h
  exact isEssentiallyConstantPro_of_initial_of_exists_biproduct ⟨hc, I', cI, fI, H, hH, h⟩

/-- A variant of Stacks 0A2E (2) in which the subcategory `I'` is required to be full. Let
`M : I ⥤ A` be a diagram over a cofiltered category in a preadditive Karoubian category. Then `M`
is essentially constant if and only if `lim M` exists and there are a cofiltered category `I'`
with a fully faithful initial functor `H : I' ⥤ I` and, for each `i' : I'`, a direct
sum decomposition `M (H i') ≅ X_{i'} ⊕ Z_{i'}` such that `lim M` maps isomorphically to `X_{i'}`
and `M (H i'') ⟶ Z_{i'}` is zero for some `i'' ⟶ i'` in `I'`. The Stacks statement, over an
arbitrary (not necessarily full) initial cofiltered subcategory, is
`isEssentiallyConstantPro_iff_exists_subcategory`. -/
theorem isEssentiallyConstantPro_iff_exists_biproduct [IsCofiltered I] [IsIdempotentComplete A]
    (M : I ⥤ A) :
    IsEssentiallyConstantPro M ↔
      ∃ (_ : HasLimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsCofiltered I')
        (H : I' ⥤ I) (_ : H.Full) (_ : H.Faithful) (_ : H.Initial), ∀ i' : I',
          ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
            IsIso (limit.π M (H.obj i') ≫ e.inv ≫ b.fst) ∧
            ∃ (i'' : I') (f : i'' ⟶ i'), M.map (H.map f) ≫ e.inv ≫ b.snd = 0 :=
    ⟨exists_biproduct_of_isEssentiallyConstantPro, isEssentiallyConstantPro_of_exists_biproduct⟩

/-- Stacks 0A2E (2). Let `M : I ⥤ A` be a diagram over a cofiltered category in a preadditive
Karoubian category. Then `M` is essentially constant if and only if `lim M` exists and there are
an initial cofiltered subcategory `I'` of `I` (a cofiltered category `I'` with a faithful initial
functor `H : I' ⥤ I` injective on objects, i.e. an isomorphism onto a subcategory) and, for each
`i' : I'`, a direct sum decomposition `M (H i') ≅ X_{i'} ⊕ Z_{i'}` such that `lim M` maps
isomorphically to `X_{i'}` and `M (H i'') ⟶ Z_{i'}` is zero for some `i'' ⟶ i'` in `I'`. -/
@[stacks 0A2E "(2)"]
theorem isEssentiallyConstantPro_iff_exists_subcategory [IsCofiltered I] [IsIdempotentComplete A]
    (M : I ⥤ A) :
    IsEssentiallyConstantPro M ↔
      ∃ (_ : HasLimit M) (I' : Type u') (_ : Category.{v'} I') (_ : IsCofiltered I')
        (H : I' ⥤ I) (_ : H.Faithful) (_ : Function.Injective H.obj) (_ : H.Initial), ∀ i' : I',
          ∃ (X' Z' : A) (b : BinaryBicone X' Z') (_ : b.IsBilimit) (e : b.pt ≅ M.obj (H.obj i')),
            IsIso (limit.π M (H.obj i') ≫ e.inv ≫ b.fst) ∧
            ∃ (i'' : I') (f : i'' ⟶ i'), M.map (H.map f) ≫ e.inv ≫ b.snd = 0 := by
  refine ⟨fun h => ?_, fun ⟨hc, I', cI, fI, H, _, _, hH, h⟩ =>
    isEssentiallyConstantPro_of_initial_of_exists_biproduct ⟨hc, I', cI, fI, H, hH, h⟩⟩
  obtain ⟨hc, I', cI, fI, H, _, hF, hinj, hH, h⟩ :=
    exists_fullSubcategory_biproduct_of_isEssentiallyConstantPro h
  exact ⟨hc, I', cI, fI, H, hF, hinj, hH, h⟩

end EssentiallyConstantPro

end CategoryTheory
