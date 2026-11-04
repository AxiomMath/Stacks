module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# Global regular functions on the algebraic space represented by a scheme

Let `S` be a scheme in a big fppf site `B` and let `W` be a scheme of the site over `S`. The
ring of global regular functions on the algebraic space represented by `W` is `Γ(W, 𝒪_W)`: the
compatible families of regular functions on the scheme charts of `yoneda W` are determined by
their value on the identity chart, which is terminal among the charts. Pullback of global
regular functions along the morphism of represented spaces induced by a morphism of schemes is
then pullback of global sections.

## Main definitions

* `AlgebraicGeometry.Space.chartFunctionsYonedaEquiv`: compatible families of regular functions on
  the scheme charts of `yoneda W` are `Γ(W, 𝒪_W)`.

## Main results

* `AlgebraicGeometry.Space.chartFunctionsYonedaEquiv_map`: precomposition along the morphism of
  represented presheaves induced by a morphism of schemes is pullback of global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Compatible families of regular functions on the scheme charts of the presheaf represented by
a scheme `W` are the global sections of `W`**: the identity chart is terminal, so a family is
determined by its value there. -/
noncomputable def chartFunctionsYonedaEquiv (W : BigFppfOver B S hS) :
    chartFunctions B S hS (yoneda.obj W) ≃+*
      (chartPresheaf B S hS (yoneda.obj W)).obj (op (CostructuredArrow.mk (𝟙 (yoneda.obj W)))) where
  toFun s := s.val (op (CostructuredArrow.mk (𝟙 (yoneda.obj W))))
  invFun x := ⟨fun j => (chartPresheaf B S hS (yoneda.obj W)).map
      ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).from j.unop).op
        x,
    fun {j k} g => by
      change (chartPresheaf B S hS (yoneda.obj W)).map g ((chartPresheaf B S hS (yoneda.obj W)).map
        ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).from j.unop).op x) =
        (chartPresheaf B S hS (yoneda.obj W)).map
          ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).from k.unop).op x
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrArg (fun (m : op (CostructuredArrow.mk (𝟙 (yoneda.obj W))) ⟶ k) =>
          (chartPresheaf B S hS (yoneda.obj W)).map m x)
        (Quiver.Hom.unop_inj ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).hom_ext
          (g.unop ≫ (CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).from j.unop)
          ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).from k.unop)))⟩
  left_inv s := by
    ext j
    exact s.property ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).from j.unop).op
  right_inv x := by
    let t : CostructuredArrow yoneda (yoneda.obj W) := CostructuredArrow.mk (𝟙 (yoneda.obj W))
    have h : (CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).from t = 𝟙 t :=
      (CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).hom_ext
        ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).from t) (𝟙 t)
    change (chartPresheaf B S hS (yoneda.obj W)).map
      ((CostructuredArrow.mkIdTerminal (S := yoneda) (Y := W)).from t).op x = x
    rw [h, op_id, CategoryTheory.Functor.map_id]
    rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The ring of global sections of the identity chart of `yoneda W` is `Γ(W, 𝒪_W)`. -/
lemma chartPresheaf_obj_id (W : BigFppfOver B S hS) :
    (chartPresheaf B S hS (yoneda.obj W)).obj (op (CostructuredArrow.mk (𝟙 (yoneda.obj W)))) =
      Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj W)) := rfl

/-- The restriction map of chart functions along the morphism of charts induced by a morphism of
schemes is pullback of global sections. -/
lemma chartPresheaf_map_homMk {V W : BigFppfOver B S hS} (g : V ⟶ W) :
    (chartPresheaf B S hS (yoneda.obj W)).map
        (CostructuredArrow.homMk (S := yoneda) (T := yoneda.obj W)
          (f := CostructuredArrow.mk (𝟙 (yoneda.obj V) ≫ yoneda.map g))
          (f' := CostructuredArrow.mk (𝟙 (yoneda.obj W))) g (by simp)).op =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op := rfl

/-- **Precomposition of chart functions along the morphism of represented presheaves induced by a
morphism of schemes is restriction along the induced morphism of identity charts.** -/
theorem chartFunctionsYonedaEquiv_map {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (t : chartFunctions B S hS (yoneda.obj W)) :
    chartFunctionsYonedaEquiv B S hS V (chartFunctionsMap B S hS (yoneda.map g) t) =
      (chartPresheaf B S hS (yoneda.obj W)).map
        (CostructuredArrow.homMk (S := yoneda) (T := yoneda.obj W)
          (f := CostructuredArrow.mk (𝟙 (yoneda.obj V) ≫ yoneda.map g))
          (f' := CostructuredArrow.mk (𝟙 (yoneda.obj W))) g (by simp)).op
        (chartFunctionsYonedaEquiv B S hS W t) :=
  (t.property (CostructuredArrow.homMk (S := yoneda) (T := yoneda.obj W)
    (f := CostructuredArrow.mk (𝟙 (yoneda.obj V) ≫ yoneda.map g))
    (f' := CostructuredArrow.mk (𝟙 (yoneda.obj W))) g (by simp)).op).symm

end AlgebraicGeometry.Space

end
