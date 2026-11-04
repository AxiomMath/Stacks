module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerObject

/-!
# Short exact sequences of a dimension layer from short exact sequences of modules

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project. The
short exact sequences produced by the constructions of chapter 42 are sequences of
`𝒪_X`-modules; to read them in the Grothendieck group of a dimension layer they have to be
presented as short exact sequences of `Stacks.Chow.CoherentModulesDimLE`. The objects of that
category are modules carrying two proofs and its morphisms are the morphisms of modules carrying
none, so the passage is a repackaging, and
`Stacks.Chow.shortExact_coherentModulesDimLE` supplies the short exactness.

## Main definitions

* `Stacks.Chow.layerHomMk` — a morphism of a dimension layer from a morphism of modules.
* `Stacks.Chow.layerShortComplex` — a short complex of a dimension layer from a short complex of
  modules whose three terms lie in it.

## Main results

* `Stacks.Chow.coherentDimensionKZeroMk_add_of_modules` — a short exact sequence of `𝒪_X`-modules
  whose three terms lie in the layer gives additivity of the class in the Grothendieck group of the
  layer.

## References

* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-- A morphism of a dimension layer from a morphism of the underlying modules: the layer is a
full subcategory of a full subcategory, so a morphism is the underlying morphism wrapped
twice. -/
def layerHomMk {b : ℤ} {M N : CoherentModulesDimLE C f b} (φ : M.obj.obj ⟶ N.obj.obj) : M ⟶ N :=
  ObjectProperty.homMk (ObjectProperty.homMk φ)

/-- The underlying morphism of modules of `layerHomMk C f φ` is `φ`. -/
@[simp]
theorem layerHomMk_hom_hom {b : ℤ} {M N : CoherentModulesDimLE C f b}
    (φ : M.obj.obj ⟶ N.obj.obj) : (layerHomMk C f φ).hom.hom = φ :=
  rfl

/-- A short complex of a dimension layer from the underlying morphisms of modules. -/
def layerShortComplex {b : ℤ} {A B D : CoherentModulesDimLE C f b} (u : A.obj.obj ⟶ B.obj.obj)
    (v : B.obj.obj ⟶ D.obj.obj) (w : u ≫ v = 0) :
    ShortComplex (CoherentModulesDimLE C f b) :=
  ShortComplex.mk (layerHomMk C f u) (layerHomMk C f v)
    (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      exact w)

/-- The image in `𝒪_X`-modules of the short complex built from `u` and `v` is the short complex
built from `u` and `v`. -/
theorem layerShortComplex_map_ι {b : ℤ} {A B D : CoherentModulesDimLE C f b}
    (u : A.obj.obj ⟶ B.obj.obj) (v : B.obj.obj ⟶ D.obj.obj) (w : u ≫ v = 0) :
    ((layerShortComplex C f u v w).map (coherentModulesDimLE C f b).ι).map
        (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι =
      ShortComplex.mk u v w :=
  rfl

/-- **Additivity of the class in a dimension layer, from a short exact sequence of modules.**
Given a short exact sequence `0 ⟶ A ⟶ B ⟶ D ⟶ 0` of `𝒪_X`-modules whose three terms lie in the
layer `Coh_{≤b}(𝒪_X)`, the class of the middle term in the Grothendieck group of the layer
`(a, b]` is the sum of the classes of the outer terms. -/
theorem coherentDimensionKZeroMk_add_of_modules (a b : ℤ)
    {A B D : CoherentModulesDimLE C f b} (u : A.obj.obj ⟶ B.obj.obj)
    (v : B.obj.obj ⟶ D.obj.obj) (w : u ≫ v = 0) (h : (ShortComplex.mk u v w).ShortExact) :
    coherentDimensionKZeroMk C f a b B =
      coherentDimensionKZeroMk C f a b A + coherentDimensionKZeroMk C f a b D :=
  coherentDimensionKZeroMk_add C f a b
    (shortExact_coherentModulesDimLE C f b
      (by rw [layerShortComplex_map_ι C f u v w]; exact h))

end Stacks.Chow

end
