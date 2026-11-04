module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Limits.Presheaf

/-! # Maps out of a presheaf of sets, read on its site of elements

For a presheaf of sets `K` on a category `C`, the site of elements of `K` is
`C/K = CostructuredArrow yoneda K`: its objects are the pairs `(U, s)` with `s ∈ K(U)`, and its
projection to `C` is `j`. A map of presheaves `K ⟶ H` is exactly a family of elements of `H(U)`
indexed by the pairs `(U, s)`, compatibly with restriction — in other words a map from the
terminal presheaf of sets on `C/K` to `j⁻¹H`. That is `elementsHomEquiv`, and
`elementsHomEquiv_comp` says it is natural in `H`.

Equivalently: the left Kan extension along `j.op` of the terminal presheaf is `K`. The
corepresentability form stated here is what one wants in practice, because it is what feeds
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso`: composing it with the free-abelian and
sheafification adjunctions identifies extension by zero of the constant sheaf `ℤ` on `C/K` with
the free abelian sheaf on `K`. `freeObjPUnitIso`, the identification of the free abelian group on
a point with `ℤ`, is the second input to that comparison and is recorded here alongside.

## Main definitions and results

* `Stacks.Sites.Elements.elementsHomEquiv`: maps of presheaves of sets `K ⟶ H` are maps from the
  terminal presheaf on the site of elements of `K` to the restriction of `H`.
* `Stacks.Sites.Elements.elementsHomEquiv_comp`: `elementsHomEquiv` is natural in `H`.
* `Stacks.Sites.Elements.freeObjPUnitIso`: the free abelian group on a point is `ULift ℤ`.

## Implementation notes

The equivalence is written out rather than deduced from "every presheaf is a colimit of
representables", because what the consumers need is the bijection on hom-sets together with its
compatibility with composition, and both are immediate from the Yoneda bijection
`yonedaEquiv`: the element `s ∈ K(U)` corresponds to the object `CostructuredArrow.mk
(yonedaEquiv.symm s)` of `C/K`, and `elHom` is the morphism of `C/K` that restriction along
`f : U ⟶ V` induces between the objects attached to `s` and to `K(f)(s)`.

`freeObjPUnitIso` is obtained by comparing two corepresentations of the forgetful functor
`AddCommGrpCat ⥤ Type`: the one coming from the free-forgetful adjunction at a point, and
Mathlib's `AddCommGrpCat.coyonedaObjIsoForget`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.Sites.Elements

universe v u

section Elements

variable {C : Type u} [Category.{v} C] (K H : Cᵒᵖ ⥤ Type v)

/-- Restriction along `f : U ⟶ V` in `Cᵒᵖ`, read on the site of elements of `K`: the morphism of
`C/K` from the object attached to `K(f)(s)` to the object attached to `s`. -/
def elHom {U V : Cᵒᵖ} (f : U ⟶ V) (s : K.obj U) :
    CostructuredArrow.mk (yonedaEquiv.symm (K.map f s)) ⟶
      (CostructuredArrow.mk (yonedaEquiv.symm s) : CostructuredArrow (yoneda (C := C)) K) :=
  CostructuredArrow.homMk f.unop (by
    dsimp
    exact yonedaEquiv_symm_naturality_left f.unop K s)

/-- The underlying morphism of `C` of `elHom K f s` is `f.unop`. -/
@[simp]
lemma elHom_left {U V : Cᵒᵖ} (f : U ⟶ V) (s : K.obj U) :
    (elHom K f s).left = f.unop :=
  rfl

/-- **A map of presheaves of sets out of `K` is a family of elements indexed by the elements of
`K`.** Maps `K ⟶ H` correspond to maps from the terminal presheaf of sets on the site of elements
of `K` to the restriction of `H` along the projection. -/
def elementsHomEquiv :
    ((Functor.const (CostructuredArrow (yoneda (C := C)) K)ᵒᵖ).obj PUnit.{v + 1} ⟶
        (CostructuredArrow.proj (yoneda (C := C)) K).op ⋙ H) ≃ (K ⟶ H) where
  toFun θ :=
    { app := fun U => ↾fun s =>
        θ.app (op (CostructuredArrow.mk (yonedaEquiv.symm s))) PUnit.unit
      naturality := by
        intro U V f
        ext s
        have h := ConcreteCategory.congr_hom (θ.naturality (op (elHom K f s))) PUnit.unit
        dsimp at h ⊢
        exact h }
  invFun η :=
    { app := fun X => ↾fun _ => η.app (op X.unop.left) (yonedaEquiv X.unop.hom)
      naturality := by
        intro X Y g
        ext _
        dsimp
        have key : K.map g.unop.left.op (yonedaEquiv X.unop.hom) = yonedaEquiv Y.unop.hom := by
          rw [yonedaEquiv_naturality]
          exact congrArg yonedaEquiv (CostructuredArrow.w g.unop)
        rw [← key]
        exact ConcreteCategory.congr_hom (η.naturality g.unop.left.op) (yonedaEquiv X.unop.hom) }
  left_inv θ := by
    ext X x
    dsimp
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv η := by
    ext U s
    simp

/-- `elementsHomEquiv` is natural in the target presheaf. -/
lemma elementsHomEquiv_comp {H' : Cᵒᵖ ⥤ Type v} (α : H ⟶ H')
    (θ : (Functor.const (CostructuredArrow (yoneda (C := C)) K)ᵒᵖ).obj PUnit.{v + 1} ⟶
      (CostructuredArrow.proj (yoneda (C := C)) K).op ⋙ H) :
    elementsHomEquiv K H' (θ ≫ Functor.whiskerLeft
        (CostructuredArrow.proj (yoneda (C := C)) K).op α) =
      elementsHomEquiv K H θ ≫ α := by
  ext U s
  rfl

end Elements

section FreeAbelian

/-- Maps out of a point are the identity on types. -/
def coyonedaPUnitIso : coyoneda.obj (op PUnit.{u + 1}) ≅ 𝟭 (Type u) :=
  Functor.corepresentableByEquiv Functor.CorepresentableBy.id

/-- **The free abelian group on a point is `ℤ`.** Both corepresent the forgetful functor: the
first through the free-forgetful adjunction, the second through
`AddCommGrpCat.coyonedaObjIsoForget`. -/
def freeObjPUnitIso :
    AddCommGrpCat.free.obj PUnit.{u + 1} ≅ AddCommGrpCat.of (ULift.{u} ℤ) :=
  ((AddCommGrpCat.adj.corepresentableBy PUnit.{u + 1}).ofIso
      (Functor.isoWhiskerLeft _ coyonedaPUnitIso ≪≫ Functor.rightUnitor _)).uniqueUpToIso
    (Functor.corepresentableByEquiv.symm AddCommGrpCat.coyonedaObjIsoForget)

end FreeAbelian

end Stacks.Sites.Elements

end
