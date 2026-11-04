module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom

/-!
# The evaluation pairing of the internal Hom of sheaves of `A`-modules

Let `(C, K)` be a site, `A` a commutative ring and `G`, `F` sheaves of `A`-modules. A section of
the internal Hom `ℋom_A(G, F)` (`Stacks.ConstantSheaf.moduleSheafHom`) over `U` is, by
definition, a morphism of sheaves `G|_U ⟶ F|_U` on the slice site, restriction along `V ⟶ U`
being restriction to the slice over `V` (`Stacks.ConstantSheaf.moduleSheafHom_obj_map_apply`).
Evaluating at the identity of `U` gives the pairing `ℋom_A(G, F)(U) × G(U) ⟶ F(U)`, which is
`A`-bilinear and natural in `U`.

## Main definitions

* `Stacks.ModuleInternalHom.evalPairing`: the pairing `ℋom_A(G, F)(U) ⟶ Hom_A(G(U), F(U))`.

## Main results

* `Stacks.ModuleInternalHom.evalPairing_naturality`: compatibility with restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe w v u

namespace Stacks.ModuleInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (A : Type w) [CommRing A]
  (G F : Sheaf K (ModuleCat.{max u v} A))

/-- **The evaluation pairing** `ℋom_A(G, F)(U) × G(U) ⟶ F(U)`: a local morphism `α : G|_U ⟶ F|_U`
is evaluated at the identity of `U`. -/
def evalPairing (U : Cᵒᵖ) :
    ((moduleSheafHom K A G F).obj.obj U : Type (max u v)) →ₗ[A]
      (G.obj.obj U : Type (max u v)) →ₗ[A] (F.obj.obj U : Type (max u v)) :=
  LinearMap.mk₂ A
    (fun (α : (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
        (K.overPullback (ModuleCat.{max u v} A) U.unop).obj F) (g : G.obj.obj U) =>
      (α.hom.app (op (Over.mk (𝟙 U.unop)))).hom g)
    (fun _ _ _ => rfl)
    (fun _ _ _ => rfl)
    (fun α a b => (α.hom.app (op (Over.mk (𝟙 U.unop)))).hom.map_add a b)
    (fun r α g => (α.hom.app (op (Over.mk (𝟙 U.unop)))).hom.map_smul r g)

/-- The evaluation pairing sends a local morphism `α : G|_U ⟶ F|_U` and a section `g` of `G`
over `U` to the value of `α` at the identity of `U` on `g`. -/
lemma evalPairing_apply (U : Cᵒᵖ)
    (α : (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
      (K.overPullback (ModuleCat.{max u v} A) U.unop).obj F) (g : G.obj.obj U) :
    evalPairing K A G F U α g = (α.hom.app (op (Over.mk (𝟙 U.unop)))).hom g := rfl

/-- **The evaluation pairing is natural in `U`**: evaluating the restriction of `α` at the
restriction of `g` is the restriction of the evaluation. -/
lemma evalPairing_naturality {U U' : Cᵒᵖ} (f : U ⟶ U')
    (α : (moduleSheafHom K A G F).obj.obj U) (g : G.obj.obj U) :
    evalPairing K A G F U' (((moduleSheafHom K A G F).obj.map f).hom α) ((G.obj.map f).hom g) =
      (F.obj.map f).hom (evalPairing K A G F U α g) :=
  ConcreteCategory.congr_hom
    ((show (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
        (K.overPullback (ModuleCat.{max u v} A) U.unop).obj F from α).hom.naturality
      (Over.homMk (U := Over.mk (𝟙 U'.unop ≫ f.unop)) (V := Over.mk (𝟙 U.unop)) f.unop
        (by simp)).op) g

end Stacks.ModuleInternalHom
