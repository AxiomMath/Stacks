module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Slice

/-!
# Categories fibred in groupoids and a change of slice

Let `g : X ⟶ Y` be a morphism of `𝒞` and let `p : 𝒮 ⥤ 𝒞/X` be a category over the slice at `X`.
Composing with `CategoryTheory.Over.map g` makes `𝒮` a category over the slice at `Y`, and it is
fibred in groupoids there exactly when `p` is fibred in groupoids over `𝒞/X`. This is
Constructions A and B of Stacks, Section 04WT at the level of categories fibred in groupoids: the
data of a category fibred in groupoids over `𝒞/X` is the same as that of a category fibred in
groupoids over `𝒞/Y` with a 1-morphism to `X/Y`, because `𝒞/X` is the localization of `𝒞/Y` at
the object `X/Y` and `Over.map g` is the corresponding localization functor
(`CategoryTheory.Over.iteratedSliceBackward_forget`).

## Main results

* `CategoryTheory.Functor.isFiberedInGroupoids_comp_overMap_iff`: composing with
  `CategoryTheory.Over.map g` neither creates nor destroys the property of being fibred in
  groupoids.

## References

* [Stacks Project, Section 04WT](https://stacks.math.columbia.edu/tag/04WT)
* [Stacks Project, Tag 02XT](https://stacks.math.columbia.edu/tag/02XT)
* [Stacks Project, Tag 09WW](https://stacks.math.columbia.edu/tag/09WW)
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- A category over the slice `𝒞/X` is fibred in groupoids there exactly when, viewed over the
slice `𝒞/Y` along `g : X ⟶ Y`, it is fibred in groupoids over `𝒞/Y`. -/
theorem isFiberedInGroupoids_comp_overMap_iff {X Y : 𝒞} (g : X ⟶ Y) (p : 𝒮 ⥤ Over X) :
    (p ⋙ Over.map g).IsFiberedInGroupoids ↔ p.IsFiberedInGroupoids := by
  refine ⟨fun h => IsFiberedInGroupoids.of_comp_over X (p ⋙ Over.forget X) p rfl ?_,
    fun h => IsFiberedInGroupoids.comp p (Over.map g) h (.over_map g)⟩
  have h₂ := IsFiberedInGroupoids.comp _ _ h (IsFiberedInGroupoids.over_forget Y)
  rwa [Functor.assoc, Over.mapForget_eq g] at h₂

end CategoryTheory.Functor

end
