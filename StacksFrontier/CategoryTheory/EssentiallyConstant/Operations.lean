module

public import Mathlib.CategoryTheory.Limits.Opposites
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Transport
import StacksCore.Tactic.EgaSgaAttribute

/-! # Essentially constant systems: composition, (co)limits, and a product index category

Every statement here concerns `IsEssentiallyConstantInd` (from
`StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject`, faithfully following Stacks 05PU),
not Mathlib's `Functor.IsEventuallyConstantFrom` / `IsEventuallyConstantTo`. Three results:

* Stacks 05SH: essential constancy of `M` is inherited by `M ⋙ F` for any functor `F`, in both
  the ind form and the pro (opposite) form.
* Stacks 0G2V: an essentially constant `M` has a colimit, and the colimit cocone itself
  witnesses essential constancy with value `colimit M`; dually an `M` essentially constant as a
  pro-object has a limit, realized by `op (limit M)`. Filteredness of the index category, which
  the source assumes, is not needed for either half.
* Stacks 0A2C: for filtered `I` and any `M : J ⥤ C`, `M` is essentially constant iff
  `Prod.snd I J ⋙ M` is.

The mathematical core is `IsEssentiallyConstantWith.isColimit`: the cocone supplied by the
essential constancy data is already a colimit cocone.
`IsEssentiallyConstantInd.exists_retraction_of_isColimit` turns that around: because any two
colimit cocones are canonically isomorphic, the retraction and cofinality data transport onto
*any* prescribed colimit cocone, which is what both halves of 0G2V need.
-/

@[expose] public section

open CategoryTheory Limits Opposite CategoryTheory.EssentiallyConstantInd

variable {I : Type*} [Category I] {J : Type*} [Category J] {C : Type*} [Category C]
  {D : Type*} [Category D]

namespace CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantInd

/-- Essential-constancy data for `M` transports onto any prescribed colimit cocone `t` of `M`:
there are an index `i₀` and a retraction `b : t.pt ⟶ M.obj i₀` of `t.ι.app i₀` witnessing
essential constancy of `M` with respect to `t`.

The witnessing cocone is a colimit cocone (`IsEssentiallyConstantWith.isColimit`), so it is
isomorphic to `t`, and the witness is carried along that isomorphism. -/
theorem exists_retraction_of_isColimit {M : I ⥤ C} {t : Cocone M}
    (h : IsEssentiallyConstantInd M) (ht : IsColimit t) :
    ∃ (i₀ : I) (b : t.pt ⟶ M.obj i₀), IsEssentiallyConstantWith M t i₀ b := by
  obtain ⟨s, i₀, b, hs⟩ := h
  exact ⟨i₀, _, hs.of_iso (hs.isColimit.uniqueUpToIso ht)⟩

/-! ## Statement 1 (Stacks tag 05SH): stability under postcomposition. -/

/-- (ind) Essential constancy is stable under postcomposition by any functor. -/
@[stacks 05SH]
theorem comp {M : I ⥤ C} (h : IsEssentiallyConstantInd M) (F : C ⥤ D) :
    IsEssentiallyConstantInd (M ⋙ F) := by
  obtain ⟨t, i₀, b, h⟩ := h
  exact ⟨_, _, _, h.map F⟩

/-- (pro) Essential constancy as a pro-object is stable under postcomposition. -/
@[stacks 05SH]
theorem op_comp {M : I ⥤ C} (h : IsEssentiallyConstantInd M.op) (F : C ⥤ D) :
    IsEssentiallyConstantInd (M ⋙ F).op :=
  h.comp F.op

/-! ## Statement 2 (Stacks tag 0G2V): (co)limits with value. -/

/-- (ind, part 1) An essentially constant `M` has a colimit. -/
@[stacks 0G2V]
theorem hasColimit {M : I ⥤ C} (h : IsEssentiallyConstantInd M) : HasColimit M := by
  obtain ⟨t, _, _, h⟩ := h
  exact HasColimit.mk ⟨t, h.isColimit⟩

/-- (ind, part 2) The colimit cocone realizes `IsEssentiallyConstantInd M` with value
`colimit M`: some `i₀` admits a retraction `b` of `colimit.ι M i₀` through which every
`colimit.ι M j` factors. -/
@[stacks 0G2V]
theorem exists_retraction_colimit {M : I ⥤ C} (h : IsEssentiallyConstantInd M) [HasColimit M] :
    ∃ (i₀ : I) (b : colimit M ⟶ M.obj i₀), IsEssentiallyConstantWith M (colimit.cocone M) i₀ b :=
  h.exists_retraction_of_isColimit (colimit.isColimit M)

/-- (pro, part 1) If `M` is essentially constant as a pro-object, `M` has a limit. -/
@[stacks 0G2V]
theorem hasLimit_of_op {M : I ⥤ C} (h : IsEssentiallyConstantInd M.op) : HasLimit M :=
  have : HasColimit M.op := h.hasColimit
  hasLimit_of_hasColimit_op M

/-- (pro, part 2) The (opposite) limit cone realizes `IsEssentiallyConstantInd M.op` with value
`op (limit M)`: some `i₀` admits a retraction `b` of `(limit.π M i₀.unop).op` through which every
`(limit.π M j.unop).op` factors. -/
@[stacks 0G2V]
theorem exists_retraction_op_limit {M : I ⥤ C} (h : IsEssentiallyConstantInd M.op)
    [HasLimit M] :
    ∃ (i₀ : Iᵒᵖ) (b : op (limit M) ⟶ M.op.obj i₀),
      IsEssentiallyConstantWith M.op (limit.cone M).op i₀ b :=
  h.exists_retraction_of_isColimit (IsLimit.op (limit.isLimit M))

/-! ## Statement 3 (Stacks tag 0A2C): filtered second projection. -/

/-- Essential constancy of `M : J ⥤ C` is inherited by `Prod.snd I J ⋙ M` for filtered `I`:
whisker the witnessing cocone along `Prod.snd I J`, keep the same value and retraction, and
index by `(i₀, j₀)` for any base point `i₀ : I`. Cofinality in the `I` coordinate is supplied by
`IsFiltered.max`, in the `J` coordinate by the cofinality data of `M`. -/
theorem comp_prod_snd [IsFiltered I] {M : J ⥤ C} (h : IsEssentiallyConstantInd M) :
    IsEssentiallyConstantInd (CategoryTheory.Prod.snd I J ⋙ M) := by
  obtain ⟨t, j₀, b, hb, hcompat⟩ := h
  obtain ⟨i₀⟩ := (IsFiltered.nonempty : Nonempty I)
  refine ⟨t.whisker (CategoryTheory.Prod.snd I J), (i₀, j₀), b, hb, ?_⟩
  rintro ⟨i, j⟩
  obtain ⟨k, v, u, huv⟩ := hcompat j
  exact ⟨(IsFiltered.max i i₀, k), (IsFiltered.rightToMax i i₀, v),
    (IsFiltered.leftToMax i i₀, u), huv⟩

/-- Essential constancy of `Prod.snd I J ⋙ M` descends to `M`: restrict the witnessing cocone
along `Prod.sectR i₀ J : J ⥤ I × J`, `j ↦ (i₀, j)`, where `(i₀, j₀)` is the witnessing index.
All the data is obtained by discarding the `I` coordinate, so no filteredness is needed. -/
theorem of_comp_prod_snd {M : J ⥤ C}
    (h : IsEssentiallyConstantInd (CategoryTheory.Prod.snd I J ⋙ M)) :
    IsEssentiallyConstantInd M := by
  obtain ⟨t, ⟨i₀, j₀⟩, b, hb, hcompat⟩ := h
  refine ⟨t.whisker (CategoryTheory.Prod.sectR i₀ J), j₀, b, hb, fun j => ?_⟩
  obtain ⟨⟨_, k⟩, ⟨_, v⟩, ⟨_, u⟩, huv⟩ := hcompat (i₀, j)
  exact ⟨k, v, u, huv⟩

end CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantInd

/-- The product of two filtered categories is filtered. -/
@[stacks 0A2C, sga "4 I 8.5.4"]
theorem isFiltered_prod [IsFiltered I] [IsFiltered J] : IsFiltered (I × J) :=
  inferInstance

variable (I)

/-- For filtered `I` and any `M : J ⥤ C`, essential constancy of `M` is equivalent to essential
constancy of `M` precomposed with `Prod.snd I J`. -/
@[stacks 0A2C]
theorem isEssentiallyConstantInd_iff_comp_prod_snd [IsFiltered I] (M : J ⥤ C) :
    IsEssentiallyConstantInd M ↔ IsEssentiallyConstantInd (CategoryTheory.Prod.snd I J ⋙ M) :=
  ⟨fun h => h.comp_prod_snd, fun h => h.of_comp_prod_snd⟩
