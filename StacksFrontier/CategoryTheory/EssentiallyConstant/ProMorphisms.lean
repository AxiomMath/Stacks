module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of pro-objects as transformations of functors

Let `𝒞` be a category and let `F : I ⥤ 𝒞` and `G : J ⥤ 𝒞` be diagrams in `𝒞`. A morphism of
pro-systems from `F` to `G` is an element of `lim_j colim_i Mor(F i, G j)`. These are identified
with the transformations of functors `t : B ⟶ A`, where

* `A(X) = colim_i Mor(F i, X)`, and
* `B(X) = colim_j Mor(G j, X)`,

by sending `t` to the family obtained by applying `t` to the class of `id_{G j}` in `B(G j)`. No
cofilteredness hypothesis is imposed on `I` or `J`.

## Main definitions

* `CategoryTheory.Pro.coyonedaColim`: the functor `A(X) = colim_i Mor(F i, X)` attached to a
  diagram `F`, together with `CategoryTheory.Pro.coyonedaColimObjIso` identifying its value at `X`
  with `colim_i Mor(F i, X)`.
* `CategoryTheory.Pro.Hom`: the morphisms `lim_j colim_i Mor(F i, G j)` of pro-objects.
* `CategoryTheory.Pro.homEquiv`: the bijection between transformations `B ⟶ A` and morphisms of
  pro-objects from `F` to `G`.

## Main results

* `CategoryTheory.Pro.component_homEquiv`: the bijection sends `t` to the family of images under
  `t` of the classes of the identities `id_{G j}`.

## References

* [Stacks Project, Tag 05PX](https://stacks.math.columbia.edu/tag/05PX)
* [Stacks Project, Tag 0G2X](https://stacks.math.columbia.edu/tag/0G2X)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Pro

variable {𝒞 : Type u} [Category.{v} 𝒞] {I : Type v} [Category.{v} I] {J : Type v}
  [Category.{v} J]

/-- The functor `A(X) = colim_i Mor(F i, X)` attached to a diagram `F : I ⥤ 𝒞`, that is, the
pro-object `F` regarded as a functor `𝒞 ⥤ Type v`. It is the colimit of the composite
`F.op ⋙ coyoneda` in the functor category, and `coyonedaColimObjIso` identifies its value at `X`
with `colim_i Mor(F i, X)`. -/
@[sga "4 XVII 0.5"]
noncomputable abbrev coyonedaColim (F : I ⥤ 𝒞) : 𝒞 ⥤ Type v := colimit (F.op ⋙ coyoneda)

/-- The value of `coyonedaColim F` at `X` is `colim_i Mor(F i, X)`: colimits in a functor category
are computed pointwise. -/
noncomputable def coyonedaColimObjIso (F : I ⥤ 𝒞) (X : 𝒞) :
    (coyonedaColim F).obj X ≅ colimit (F.op ⋙ coyoneda ⋙ (evaluation 𝒞 (Type v)).obj X) :=
  colimitObjIsoColimitCompEvaluation _ X

/-- The type of morphisms of pro-objects from `F` to `G`,
`Mor_{Pro-𝒞}(F, G) = lim_j colim_i Mor(F i, G j)`. -/
noncomputable abbrev Hom (F : I ⥤ 𝒞) (G : J ⥤ 𝒞) : Type v := limit (G ⋙ coyonedaColim F)

variable (F : I ⥤ 𝒞) (G : J ⥤ 𝒞)

/-- The `j`-th component `ξ_j ∈ A(G j) = colim_i Mor(F i, G j)` of a morphism of pro-objects. -/
noncomputable def component (ξ : Hom F G) (j : J) : (coyonedaColim F).obj (G.obj j) :=
  limit.π (G ⋙ coyonedaColim F) j ξ

/-- The projections of the limit `Hom F G` are the components. -/
lemma limit_π_apply (ξ : Hom F G) (j : J) :
    limit.π (G ⋙ coyonedaColim F) j ξ = component F G ξ j :=
  rfl

/-- The components of a morphism of pro-objects are compatible with the transition maps of `G`. -/
lemma map_component {j j' : J} (f : j ⟶ j') (ξ : Hom F G) :
    (coyonedaColim F).map (G.map f) (component F G ξ j) = component F G ξ j' :=
  ConcreteCategory.congr_hom (limit.w (G ⋙ coyonedaColim F) f) ξ

/-- The morphism of pro-objects attached to a transformation `t : B ⟶ A`: the family of elements
`coyonedaEquiv (ι_j ≫ t)` of `A(G j) = colim_i Mor(F i, G j)`. -/
noncomputable def toHom (t : coyonedaColim G ⟶ coyonedaColim F) : Hom F G := by
  refine Types.Limit.mk (G ⋙ coyonedaColim F)
    (fun j => (coyonedaEquiv (colimit.ι (G.op ⋙ coyoneda) (op j) ≫ t) :
      (coyonedaColim F).obj (G.obj j))) (fun j j' f => ?_)
  have hw : coyoneda.map (G.map f).op ≫ colimit.ι (G.op ⋙ coyoneda) (op j) =
      colimit.ι (G.op ⋙ coyoneda) (op j') := colimit.w (G.op ⋙ coyoneda) f.op
  dsimp only [Functor.comp_map]
  rw [coyonedaEquiv_naturality (colimit.ι (G.op ⋙ coyoneda) (op j) ≫ t) (G.map f),
    ← Category.assoc, hw]

/-- The `j`-th component of `toHom F G t` is `coyonedaEquiv (ι_j ≫ t)`, the element of
`colim_i Mor(F i, G j)` that the co-Yoneda lemma attaches to the `j`-th leg of `t`. -/
@[simp]
lemma component_toHom (t : coyonedaColim G ⟶ coyonedaColim F) (j : J) :
    component F G (toHom F G t) j = coyonedaEquiv (colimit.ι (G.op ⋙ coyoneda) (op j) ≫ t) := by
  simp [component, toHom]

/-- The transformation `B ⟶ A` attached to a morphism of pro-objects `ξ`, that is a compatible
family `ξ_j ∈ colim_i Mor(F i, G j)`: the map out of the colimit `B = colim_j Mor(G j, -)` whose
`j`-th leg is the map corresponding to `ξ_j` under the co-Yoneda lemma. -/
noncomputable def ofHom (ξ : Hom F G) : coyonedaColim G ⟶ coyonedaColim F :=
  colimit.desc (G.op ⋙ coyoneda)
    { pt := coyonedaColim F
      ι :=
        { app := fun j => coyonedaEquiv.symm (component F G ξ j.unop)
          naturality := fun x₁ x₂ φ => by
            have h : coyonedaEquiv.symm (component F G ξ (unop x₁)) =
                coyoneda.map (G.map φ.unop).op ≫
                  coyonedaEquiv.symm (component F G ξ (unop x₂)) := by
              rw [← map_component F G φ.unop ξ]
              exact coyonedaEquiv_symm_map (G.map φ.unop) (F := coyonedaColim F)
                (component F G ξ (unop x₂))
            simpa using h.symm } }

/-- The `j`-th leg of `ofHom F G ξ` is the map corresponding to `ξ_j` under the co-Yoneda
lemma. -/
@[simp]
lemma ι_comp_ofHom (ξ : Hom F G) (j : J) :
    colimit.ι (G.op ⋙ coyoneda) (op j) ≫ ofHom F G ξ = coyonedaEquiv.symm (component F G ξ j) :=
  colimit.ι_desc _ _

/-- A morphism of pro-systems from `F` to `G` is the same thing as a transformation of functors
`t : B ⟶ A`, where `A(X) = colim_i Mor(F i, X)` and `B(X) = colim_j Mor(G j, X)`. The bijection
sends `t` to the family of images under `t` of the classes of the identities `id_{G j}`; see
`component_homEquiv`. -/
@[stacks 0G2X]
noncomputable def homEquiv : (coyonedaColim G ⟶ coyonedaColim F) ≃ Hom F G where
  toFun := toHom F G
  invFun := ofHom F G
  left_inv t := colimit.hom_ext fun j => by
    rw [ι_comp_ofHom, component_toHom, Equiv.symm_apply_apply]
  right_inv ξ := Types.limit_ext' _ _ _ fun j => by
    rw [limit_π_apply, limit_π_apply, component_toHom, ι_comp_ofHom, Equiv.apply_symm_apply]

/-- The bijection `homEquiv` sends a transformation `t : B ⟶ A` to the family
`ξ_j = t(id_{G j}) ∈ A(G j) = colim_i Mor(F i, G j)`, where `id_{G j}` is read as its class in
`B(G j) = colim_{j'} Mor(G j', G j)`. -/
lemma component_homEquiv (t : coyonedaColim G ⟶ coyonedaColim F) (j : J) :
    component F G (homEquiv F G t) j =
      t.app (G.obj j)
        ((colimit.ι (G.op ⋙ coyoneda) (op j)).app (G.obj j) (𝟙 (G.obj j))) := by
  rw [show homEquiv F G t = toHom F G t from rfl, component_toHom, coyonedaEquiv_apply]
  rfl

end CategoryTheory.Pro
