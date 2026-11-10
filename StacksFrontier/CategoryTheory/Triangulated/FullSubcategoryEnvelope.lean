module

public import Mathlib.CategoryTheory.Triangulated.Generators
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# The stages of the triangulated envelope inside a triangulated subcategory

Let `C` be a pretriangulated category and let `P` be a triangulated property of objects of `C`
which is closed under isomorphisms, so that `P.FullSubcategory` is pretriangulated and its
inclusion `ι` is exact and fully faithful. Let `Q` be a property of objects of the subcategory.
This file shows that the stages `⟨Q⟩ₙ` of the triangulated envelope computed *inside* the
subcategory are the traces of the stages `⟨ι Q⟩ₙ` computed in `C`:

`ι X ∈ ⟨ι Q⟩ₙ  ⟹  X ∈ ⟨Q⟩ₙ`.

No closure of `P` under direct summands is needed: by
`CategoryTheory.ObjectProperty.retractClosure_extensionProductIter_retractClosure` the stage
`⟨−⟩ₙ` is the retract closure of the `n`-fold extensions of finite sums of shifts, the latter
objects are built from objects of `P` by shifts, sums and cones and so lie in `P`, and a retract
of the image of an object of the subcategory, inside the image, is a retract in the subcategory,
`ι` being fully faithful.

This is what lets a strong generator be found by a computation in the ambient category: the
proof of [Stacks, Tag 0FZ6] places a perfect complex in `⟨𝒢⟩ₙ` in `D(𝒪_X)`, and `D_perf(𝒪_X)`
is a triangulated subcategory.

## Main results

* `CategoryTheory.ObjectProperty.extensionProductIter_map_ι_le`: the `n`-fold extensions of
  finite sums of shifts of `ι Q` are, up to isomorphism, images of those of `Q`.
* `CategoryTheory.ObjectProperty.triangEnvelopeIter_of_triangEnvelopeIter_map_ι`: the trace
  statement above.
* `CategoryTheory.ObjectProperty.isStrongTriangulatedGenerator_of_triangEnvelopeIter_map_ι`: if
  every object of the subcategory lies in `⟨ι Q⟩ₙ` in `C`, for one `n`, then `Q` is a strong
  generator of the subcategory.

## References

* [Stacks Project, Tag 0FZ6](https://stacks.math.columbia.edu/tag/0FZ6)
* [Stacks Project, Tag 09SJ](https://stacks.math.columbia.edu/tag/09SJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- The image under `ι` of a binary product in the subcategory is the binary product of the
images. -/
noncomputable def ιProdIso (Y₁ Y₂ : P.FullSubcategory) :
    P.ι.obj (Y₁ ⨯ Y₂) ≅ P.ι.obj Y₁ ⨯ P.ι.obj Y₂ :=
  PreservesLimitPair.iso P.ι Y₁ Y₂

/-- **Finite sums of shifts of `ι Q` are images of finite sums of shifts of `Q`.** -/
theorem binaryProductsClosure_shiftClosure_map_ι_le (Q : ObjectProperty P.FullSubcategory) :
    ((Q.map P.ι).shiftClosure ℤ).binaryProductsClosure ≤
      ((Q.shiftClosure ℤ).binaryProductsClosure.map P.ι) := by
  have : ((Q.shiftClosure ℤ).binaryProductsClosure.map P.ι).IsClosedUnderBinaryProducts :=
    isClosedUnderBinaryProducts_of_prop_prod _ (by
      rintro Z₁ Z₂ ⟨Y₁, hY₁, ⟨e₁⟩⟩ ⟨Y₂, hY₂, ⟨e₂⟩⟩
      exact ⟨Y₁ ⨯ Y₂, (Q.shiftClosure ℤ).binaryProductsClosure.prop_prod _ _ hY₁ hY₂,
        ⟨ιProdIso P Y₁ Y₂ ≪≫ prod.mapIso e₁ e₂⟩⟩)
  refine limitsClosure_le ?_
  rintro Z ⟨W, a, e, ⟨Y, hY, ⟨e'⟩⟩⟩
  exact ⟨Y⟦a⟧, le_limitsClosure _ _ _ ⟨Y, a, Iso.refl _, hY⟩,
    ⟨(P.ι.commShiftIso a).app Y ≪≫ (shiftFunctor C a).mapIso e' ≪≫ e.symm⟩⟩

/-- **The `n`-fold extensions of finite sums of shifts of `ι Q` are images of those of `Q`.**
Shifts, binary products and cones of objects of the image of `ι` are again, up to isomorphism, in
that image, `ι` being exact and the subcategory triangulated. -/
theorem extensionProductIter_map_ι_le (Q : ObjectProperty P.FullSubcategory) (n : ℕ) :
    ((Q.map P.ι).shiftClosure ℤ).binaryProductsClosure.extensionProductIter n ≤
      (((Q.shiftClosure ℤ).binaryProductsClosure.extensionProductIter n).map P.ι) := by
  induction n with
  | zero => exact binaryProductsClosure_shiftClosure_map_ι_le P Q
  | succ n ih =>
    rw [extensionProductIter_succ, extensionProductIter_succ]
    rintro Z ⟨Y₁, Y₃, f, g, h, hT, hY₁, hY₃⟩
    obtain ⟨Y₁', hY₁', ⟨e₁⟩⟩ := binaryProductsClosure_shiftClosure_map_ι_le P Q Y₁ hY₁
    obtain ⟨Y₃', hY₃', ⟨e₃⟩⟩ := ih Y₃ hY₃
    obtain ⟨h', hh'⟩ := P.ι.map_surjective (e₃.hom ≫ h ≫ e₁.inv⟦(1 : ℤ)⟧' ≫
      (P.ι.commShiftIso (1 : ℤ)).inv.app Y₁')
    obtain ⟨Y₂', f', g', H⟩ := distinguished_cocone_triangle₂ h'
    refine ⟨Y₂', ⟨Y₁', Y₃', f', g', h', H, hY₁', hY₃'⟩, ⟨?_⟩⟩
    exact Triangle.π₂.mapIso (isoTriangleOfIso₁₃ _ (Triangle.mk f g h)
      (P.ι.map_distinguished _ H) hT e₁ e₃ (by
        change (P.ι.map h' ≫ (P.ι.commShiftIso (1 : ℤ)).hom.app Y₁') ≫ e₁.hom⟦(1 : ℤ)⟧' =
          e₃.hom ≫ h
        rw [hh']
        simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id,
          Functor.map_id, Category.comp_id]))

/-- **The stages of the envelope inside the subcategory are the traces of the ambient ones**:
if `ι X ∈ ⟨ι Q⟩ₙ` in `C`, then `X ∈ ⟨Q⟩ₙ` in the subcategory. -/
theorem triangEnvelopeIter_of_triangEnvelopeIter_map_ι (Q : ObjectProperty P.FullSubcategory)
    (n : ℕ) {X : P.FullSubcategory} (hX : (Q.map P.ι).triangEnvelopeIter n (P.ι.obj X)) :
    Q.triangEnvelopeIter n X := by
  rw [triangEnvelopeIter, retractClosure_extensionProductIter_retractClosure] at hX ⊢
  obtain ⟨Z, hZ, ⟨r⟩⟩ := hX
  obtain ⟨Z', hZ', ⟨e⟩⟩ := extensionProductIter_map_ι_le P Q n Z hZ
  refine ⟨Z', hZ', ⟨⟨P.fullyFaithfulι.preimage (r.i ≫ e.inv),
    P.fullyFaithfulι.preimage (e.hom ≫ r.r), P.ι.map_injective ?_⟩⟩⟩
  simp [r.retract]

/-- **A strong generator of the subcategory, from a uniform ambient bound**: if for one `n` every
object `X` of the subcategory has `ι X ∈ ⟨ι Q⟩ₙ` in `C`, then `Q` is a strong generator of the
subcategory. -/
theorem isStrongTriangulatedGenerator_of_triangEnvelopeIter_map_ι
    (Q : ObjectProperty P.FullSubcategory) (n : ℕ)
    (h : ∀ X : P.FullSubcategory, (Q.map P.ι).triangEnvelopeIter n (P.ι.obj X)) :
    Q.IsStrongTriangulatedGenerator :=
  ⟨n, le_antisymm le_top fun X _ => triangEnvelopeIter_of_triangEnvelopeIter_map_ι P Q n (h X)⟩

end CategoryTheory.ObjectProperty
