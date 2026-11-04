module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunction

/-!
# Absorbing a tensor prefix into the transpose of [stacks 0A63]

For a `StacksDraft.DerivedHom.DerivedHomAdjunction`, a transpose precomposed with a tensor prefix
`tensor.map (u, 𝟙 L)` in the first variable is the transpose of `u` followed by the original
morphism: this is the naturality of the transpose in its source variable. This file records the
two-step form of this absorption, the equivalent form of an equation between a prefixed transpose
and a morphism out of the tensor product, and the naturality of the inverse transpose in the
target variable, all at arbitrary objects.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.tensor_map_id_comp_tensor_map_id` -- two morphisms
  of the first variable merge into one.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.tensor_map_id_comp_homEquiv` -- a transpose with a
  two-step tensor prefix is the transpose of the composite.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.tensor_map_id_comp_homEquiv_eq_iff` -- so comparing
  it against a morphism out of the tensor product is comparing that composite against the
  morphism's own transpose.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_naturality_right` -- the inverse
  transpose of a morphism followed by one of the target is the inverse transpose followed by the
  internal Hom of that one.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R)

/-- **Two morphisms of the first tensor variable merge into one**: the tensor bifunctor of
[stacks 0A63] sends `(u, 𝟙 L)` followed by `(v, 𝟙 L)` to `(u ≫ v, 𝟙 L)`. -/
public theorem tensor_map_id_comp_tensor_map_id
    {X X' X'' L : DerivedCategory (ModuleCat.{v} R)} (u : X ⟶ X') (v : X' ⟶ X'') :
    d.tensor.map ((u, 𝟙 L) : ((X, L) : DerivedCategory (ModuleCat.{v} R) ×
          DerivedCategory (ModuleCat.{v} R)) ⟶ (X', L)) ≫
        d.tensor.map ((v, 𝟙 L) : ((X', L) : DerivedCategory (ModuleCat.{v} R) ×
          DerivedCategory (ModuleCat.{v} R)) ⟶ (X'', L)) =
      d.tensor.map ((u ≫ v, 𝟙 L) : ((X, L) : DerivedCategory (ModuleCat.{v} R) ×
        DerivedCategory (ModuleCat.{v} R)) ⟶ (X'', L)) := by
  rw [← d.tensor.map_comp, CategoryTheory.prod_comp, Category.comp_id]

/-- **A transpose with a two-step tensor prefix is the transpose of the composite**: the transpose
of `a` precomposed with `tensor.map (v, 𝟙 L)` and then with `tensor.map (u, 𝟙 L)` is the transpose
of `u ≫ v ≫ a`. -/
public theorem tensor_map_id_comp_homEquiv
    {X X' X'' L M : DerivedCategory (ModuleCat.{v} R)} (u : X ⟶ X') (v : X' ⟶ X'')
    (a : X'' ⟶ d.hom.obj (Opposite.op L, M)) :
    d.tensor.map ((u, 𝟙 L) : ((X, L) : DerivedCategory (ModuleCat.{v} R) ×
            DerivedCategory (ModuleCat.{v} R)) ⟶ (X', L)) ≫
        (d.tensor.map ((v, 𝟙 L) : ((X', L) : DerivedCategory (ModuleCat.{v} R) ×
              DerivedCategory (ModuleCat.{v} R)) ⟶ (X'', L)) ≫
          d.homEquiv X'' L M a) =
      d.homEquiv X L M (u ≫ v ≫ a) := by
  rw [d.homEquiv_naturality_left u (v ≫ a), d.homEquiv_naturality_left v a]

/-- **Comparing a prefixed transpose against a morphism out of the tensor product is comparing a
composite against that morphism's own transpose**: the transpose of `a` with the tensor prefix of
`u` and `v` equals `g` if and only if `u ≫ v ≫ a` equals the inverse transpose of `g`. -/
public theorem tensor_map_id_comp_homEquiv_eq_iff
    {X X' X'' L M : DerivedCategory (ModuleCat.{v} R)} (u : X ⟶ X') (v : X' ⟶ X'')
    (a : X'' ⟶ d.hom.obj (Opposite.op L, M)) (g : d.tensor.obj (X, L) ⟶ M) :
    d.tensor.map ((u, 𝟙 L) : ((X, L) : DerivedCategory (ModuleCat.{v} R) ×
              DerivedCategory (ModuleCat.{v} R)) ⟶ (X', L)) ≫
          (d.tensor.map ((v, 𝟙 L) : ((X', L) : DerivedCategory (ModuleCat.{v} R) ×
                DerivedCategory (ModuleCat.{v} R)) ⟶ (X'', L)) ≫
            d.homEquiv X'' L M a) =
        g ↔
      u ≫ v ≫ a = (d.homEquiv X L M).symm g := by
  rw [d.tensor_map_id_comp_homEquiv, AddEquiv.eq_symm_apply]

/-- **The inverse transpose of a morphism followed by one of the target**: the inverse transpose
of `b ≫ g` is the inverse transpose of `b` followed by the internal Hom of `g`. This is the
naturality of the transpose of [stacks 0A63] in its target variable. -/
public theorem homEquiv_symm_naturality_right
    {K L M M' : DerivedCategory (ModuleCat.{v} R)} (g : M ⟶ M')
    (b : d.tensor.obj (K, L) ⟶ M) :
    (d.homEquiv K L M').symm (b ≫ g) =
      (d.homEquiv K L M).symm b ≫ d.hom.map (𝟙 (Opposite.op L), g) := by
  apply (d.homEquiv K L M').injective
  rw [AddEquiv.apply_symm_apply, d.homEquiv_naturality_right, AddEquiv.apply_symm_apply]

end StacksDraft.DerivedHom.DerivedHomAdjunction

end
