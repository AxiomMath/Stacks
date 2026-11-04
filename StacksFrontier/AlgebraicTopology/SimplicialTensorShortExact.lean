module

public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity

/-!
# Short exact sequences of Moore complexes of simplicial modules

* `StacksDraft.SimplicialTensor.shortExact_map_alternatingFaceMapComplex_of_linear`: a
  degreewise short exact sequence of simplicial modules gives a short exact sequence of Moore
  complexes.
* `StacksDraft.SimplicialTensor.shortExact_tensor_simpKer`: the degreewise kernel sequence of a
  degreewise surjection stays short exact after tensoring with a degreewise flat simplicial
  module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject MonoidalCategory
open Opposite AlgebraicTopology

open scoped Simplicial TensorProduct

universe v w

namespace StacksDraft.SimplicialTensor

variable {B : Type w} [CommRing B]

/-- A short complex of simplicial modules which is short exact in each degree gives a short
exact sequence of Moore complexes. -/
theorem shortExact_map_alternatingFaceMapComplex_of_linear {R : Type*} [Ring R]
    {T : ShortComplex (SimplicialObject (ModuleCat.{v} R))}
    (hexact : ∀ n : SimplexCategoryᵒᵖ, Function.Exact (T.f.app n).hom (T.g.app n).hom)
    (hmono : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (T.f.app n).hom)
    (hepi : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (T.g.app n).hom) :
    (T.map (alternatingFaceMapComplex (ModuleCat.{v} R))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun _ =>
    ModuleCat.shortComplex_shortExact _ (hexact _) (hmono _) (hepi _)

/-- The degreewise kernel sequence `0 → ker f → X → Y → 0` of a degreewise surjective morphism of
simplicial modules, tensored on the left with a degreewise flat simplicial module `M`, gives a
short exact sequence of Moore complexes. -/
theorem shortExact_tensor_simpKer (M : SimplicialObject (ModuleCat.{max v w} B))
    (hM : ∀ n, Module.Flat B (M.obj n)) {X Y : SimplicialObject (ModuleCat.{max v w} B)}
    (f : X ⟶ Y) (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom) :
    ((ShortComplex.mk (M ◁ simpKerι f) (M ◁ f) (by
      rw [← MonoidalCategory.whiskerLeft_comp, simpKerι_comp]
      exact whiskerLeft_eq_zero M)).map
        (alternatingFaceMapComplex _)).ShortExact := by
  refine shortExact_map_alternatingFaceMapComplex_of_linear (fun n => ?_) (fun n => ?_)
    (fun n => ?_)
  · exact Module.Flat.lTensor_exact (M := M.obj n)
      (LinearMap.exact_subtype_ker_map (f.app n).hom)
  · exact Module.Flat.lTensor_preserves_injective_linearMap (M := M.obj n) _
      (LinearMap.ker (f.app n).hom).injective_subtype
  · exact LinearMap.lTensor_surjective _ (hf n)

end StacksDraft.SimplicialTensor

end
