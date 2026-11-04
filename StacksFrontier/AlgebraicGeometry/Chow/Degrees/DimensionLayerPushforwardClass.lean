module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerFinitePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerShortComplex

/-!
# Classes in a dimension layer along a finite morphism

Let `π : Z ⟶ X` be a finite morphism of schemes locally of finite type over the base scheme of
chapter 42 of the Stacks Project. Direct image along `π` is an exact functor between the
dimension layers `Coh_{≤b}`, so a short exact sequence over `Z` gives additivity of the classes
of the direct images in the Grothendieck group of the layer over `X`. That is the shape in which
the descent arguments of chapter 42 — which produce their short exact sequences on a closed
subscheme and read the resulting classes upstairs — use the K-group of a layer.

Two isomorphic modules have the same class, and for objects of a layer, which form a full
subcategory, an isomorphism of the underlying modules is an isomorphism of the objects.

## Main definitions

* `Stacks.Chow.layerIsoMk` — an isomorphism of layer objects from one of the underlying modules.

## Main results

* `Stacks.Chow.coherentDimensionKZeroMk_eq_of_moduleIso` — isomorphic underlying modules have the
  same class in the Grothendieck group of a layer.
* `Stacks.Chow.coherentDimensionKZeroMk_finitePushforward_add` — a short exact sequence of a
  dimension layer over `Z` gives additivity of the classes of the direct images over `X`.

## References

* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU)
* [Stacks Project, Tag 0FDR](https://stacks.math.columbia.edu/tag/0FDR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-- An isomorphism of objects of a dimension layer from an isomorphism of the underlying
modules: the layer is a full subcategory of a full subcategory, so the two notions agree. -/
def layerIsoMk {b : ℤ} {M N : CoherentModulesDimLE C f b} (e : M.obj.obj ≅ N.obj.obj) : M ≅ N where
  hom := layerHomMk C f e.hom
  inv := layerHomMk C f e.inv
  hom_inv_id := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ e.hom_inv_id)
  inv_hom_id := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ e.inv_hom_id)

/-- **Isomorphic underlying modules have the same class in the Grothendieck group of a layer.** -/
theorem coherentDimensionKZeroMk_eq_of_moduleIso (a b : ℤ) {M N : CoherentModulesDimLE C f b}
    (e : M.obj.obj ≅ N.obj.obj) :
    coherentDimensionKZeroMk C f a b M = coherentDimensionKZeroMk C f a b N :=
  coherentDimensionKZeroMk_eq_of_iso C f a b (layerIsoMk C f e)

/-- **Additivity of the classes of the direct images along a finite morphism.** A short exact
sequence of coherent modules of support dimension at most `b` on `Z` pushes forward to a short
exact sequence on `X`, so the class of the direct image of the middle term is the sum of the
classes of the direct images of the outer terms. -/
theorem coherentDimensionKZeroMk_finitePushforward_add {Z : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (π : Z ⟶ X) [IsFinite π] (hπ : π ≫ f = sZ) (a b : ℤ)
    {S : ShortComplex (CoherentModulesDimLE C sZ b)} (hS : S.ShortExact) :
    coherentDimensionKZeroMk C f a b
        ((finitePushforwardDimLE C sZ f π hπ b).obj S.X₂) =
      coherentDimensionKZeroMk C f a b
          ((finitePushforwardDimLE C sZ f π hπ b).obj S.X₁) +
        coherentDimensionKZeroMk C f a b
          ((finitePushforwardDimLE C sZ f π hπ b).obj S.X₃) :=
  coherentDimensionKZeroMk_add C f a b
    (shortExact_map_finitePushforwardDimLE C sZ f π hπ b hS)

end Stacks.Chow

end
