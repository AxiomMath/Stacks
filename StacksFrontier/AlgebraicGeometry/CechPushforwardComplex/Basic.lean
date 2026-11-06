module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Čech complex commutes with a product-preserving additive functor

Let `U : ι → C` be a family of objects of a category with finite products and let
`G : A ⥤ B` be an additive functor between preadditive categories which preserves products
indexed by types in the universe `w` of `ι`.  This file constructs the canonical isomorphism

`cechComplexFunctor U ⋙ G.mapHomologicalComplex _ ≅`
`  (Functor.whiskeringRight _ _ _).obj G ⋙ cechComplexFunctor U`

i.e. applying `G` termwise to the Čech complex of a presheaf `P : Cᵒᵖ ⥤ A` gives the Čech
complex of the presheaf `P ⋙ G`, naturally in `P`.

## Main definitions

* `evalOpObjCompIso` and `evalOpCompWhiskeringRightIso`: the extension of a presheaf to formal
  coproducts commutes with `G`, because the extension is given by a product formula.
* `cosimplicialObjectFunctorCompWhiskeringIso`: hence so does the cosimplicial object attached
  to a simplicial object of formal coproducts.
* `alternatingCofaceMapComplexCompMapHomologicalComplexIso`: the *coface* analogue of Mathlib's
  `AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso`.
* `cochainComplexFunctorCompMapHomologicalComplexIso`: the same for the complex of sections
  `s(P(E))` of an arbitrary simplicial formal coproduct `E`.
* `cechComplexFunctorCompMapHomologicalComplexIso`: the isomorphism above, which is the
  previous one at the Čech nerve of `U`.

## Implementation notes

The only content is in `evalOpObjCompIso`: the degree-`n` term of the Čech complex is a product,
and a functor commutes with a product only up to the comparison map
`CategoryTheory.Limits.piComparison`.  Everything else is `Iso.refl` degreewise, exactly as in
Mathlib's chain-complex version, and the whole naturality argument is
`CategoryTheory.Limits.map_lift_piComparison`.

The hypothesis on `G` is preservation of *all* `w`-indexed products rather than only the finite
ones, because `CategoryTheory.Limits.FormalCoproduct.evalOp` is defined on formal coproducts of
arbitrary `w`-indexed families even though the ones appearing in a Čech complex are finite when
`ι` is.  For the intended application `G` is a pushforward of sheaves of modules, a right
adjoint, so it preserves every limit and the stronger hypothesis costs nothing.

`alternatingCofaceMapComplexCompMapHomologicalComplexIso` is stated here because pinned Mathlib
has the chain-complex (`alternatingFaceMapComplex`) version only, as
`AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso` and
`AlgebraicTopology.map_alternatingFaceMapComplex`; the cochain-complex one, which is what
`CategoryTheory.cechComplexFunctor` is built from, is absent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.FormalCoproduct Opposite

universe w v v' v'' u u' u''

namespace Stacks.CechPushforward

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  {B : Type u''} [Category.{v''} B]

section Flip

variable {I J J' : Type*} [Category* I] [Category* J] [Category* J']

/-- Flipping a bifunctor commutes with postcomposing one variable by `G`. -/
public theorem flip_comp_whiskeringRight (K : I ⥤ J ⥤ A) (G : A ⥤ B) :
    (K ⋙ (Functor.whiskeringRight J A B).obj G).flip =
      K.flip ⋙ (Functor.whiskeringRight I A B).obj G :=
  rfl

/-- Flipping a bifunctor turns precomposition in the second variable into precomposition of the
flip. -/
public theorem comp_whiskeringLeft_flip (K : I ⥤ J ⥤ A) (H : J' ⥤ J) :
    (K ⋙ (Functor.whiskeringLeft J' J A).obj H).flip = H ⋙ K.flip :=
  rfl

/-- The two lemmas above at once, in the shape in which a coefficient presheaf is written: a
bifunctor postcomposed by `G` in one variable and precomposed by `H` in the other, flipped. -/
public theorem flip_comp_whiskerings (K : I ⥤ J ⥤ A) (G : A ⥤ B) (H : J' ⥤ J) :
    (K ⋙ (Functor.whiskeringRight J A B).obj G ⋙
        (Functor.whiskeringLeft J' J B).obj H).flip =
      H ⋙ K.flip ⋙ (Functor.whiskeringRight I A B).obj G :=
  rfl

end Flip

section EvalOp

variable [HasProducts.{w} A] [HasProducts.{w} B] (G : A ⥤ B)
  [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G]

/-- **The extension of a presheaf to formal coproducts commutes with a product-preserving
functor.** The value of `evalOp` at a formal coproduct is a product of values of the presheaf,
so the comparison is `CategoryTheory.Limits.piComparison`. -/
public noncomputable def evalOpCompHom (P : Cᵒᵖ ⥤ A) :
    (evalOp.{w} C A).obj P ⋙ G ⟶ (evalOp.{w} C B).obj (P ⋙ G) where
  app X := piComparison G (fun i : X.unop.I ↦ P.obj (op (X.unop.obj i)))
  naturality _ _ _ := by
    dsimp [evalOp]
    refine Pi.hom_ext _ _ (fun j ↦ ?_)
    simp only [Category.assoc, piComparison_comp_π, piComparison_comp_π_assoc, Pi.lift_comp_π]
    rw [← G.map_comp, ← G.map_comp, Pi.lift_comp_π]

/-- **The extension of a presheaf to formal coproducts commutes with a product-preserving
functor.** -/
public noncomputable def evalOpObjCompIso (P : Cᵒᵖ ⥤ A) :
    (evalOp.{w} C A).obj P ⋙ G ≅ (evalOp.{w} C B).obj (P ⋙ G) :=
  NatIso.ofComponents
    (fun X ↦ PreservesProduct.iso G (fun i : X.unop.I ↦ P.obj (op (X.unop.obj i))))
    (fun {_ _} φ ↦ (evalOpCompHom.{w} G P).naturality φ)

/-- The components of `evalOpObjCompIso` are the product comparison maps of `G`. -/
@[simp]
public theorem evalOpObjCompIso_hom_app (P : Cᵒᵖ ⥤ A) (X : (FormalCoproduct.{w} C)ᵒᵖ) :
    (evalOpObjCompIso.{w} G P).hom.app X =
      piComparison G (fun i : X.unop.I ↦ P.obj (op (X.unop.obj i))) :=
  rfl

/-- The comparison of `evalOpCompHom`, as a natural transformation of functors in the
presheaf. -/
public noncomputable def evalOpCompWhiskeringRightHom :
    evalOp.{w} C A ⋙ (Functor.whiskeringRight _ A B).obj G ⟶
      (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ evalOp.{w} C B where
  app P := evalOpCompHom.{w} G P
  naturality _ _ _ := by
    refine NatTrans.ext (funext fun X ↦ ?_)
    dsimp [evalOp, evalOpCompHom]
    refine Pi.hom_ext _ _ (fun j ↦ ?_)
    simp only [Category.assoc, piComparison_comp_π, piComparison_comp_π_assoc, Pi.map_π]
    rw [← G.map_comp, ← G.map_comp, Pi.map_π]

/-- The isomorphism of `evalOpObjCompIso`, as an isomorphism of functors in the presheaf. -/
public noncomputable def evalOpCompWhiskeringRightIso :
    evalOp.{w} C A ⋙ (Functor.whiskeringRight _ A B).obj G ≅
      (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ evalOp.{w} C B :=
  NatIso.ofComponents (fun P ↦ evalOpObjCompIso.{w} G P)
    (fun {_ _} α ↦ (evalOpCompWhiskeringRightHom.{w} G).naturality α)

variable (E : SimplicialObject (FormalCoproduct.{w} C))

/-- **The cosimplicial object attached to a simplicial object of formal coproducts commutes
with a product-preserving functor.** -/
public noncomputable def cosimplicialObjectFunctorCompWhiskeringIso :
    cosimplicialObjectFunctor.{w} E ⋙ (CosimplicialObject.whiskering A B).obj G ≅
      (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ cosimplicialObjectFunctor.{w} E :=
  NatIso.ofComponents (fun P ↦ Functor.isoWhiskerLeft E.rightOp (evalOpObjCompIso G P))
    (fun {P Q} α ↦ by
      refine NatTrans.ext (funext fun n ↦ ?_)
      exact congrFun (congrArg NatTrans.app
        ((evalOpCompWhiskeringRightIso.{w} G).hom.naturality α)) (E.rightOp.obj n))

end EvalOp

section Coface

variable [Preadditive A] [Preadditive B] (G : A ⥤ B) [G.Additive]

/-- The differential of the alternating coface map complex is the alternating sum of the coface
maps.  This is the cochain analogue of Mathlib's
`AlgebraicTopology.alternatingFaceMapComplex_obj_d`, which pinned Mathlib does not state. -/
@[sga "4 XVII 5.5.3" "partial"]
public theorem alternatingCofaceMapComplex_obj_d (X : CosimplicialObject A) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex A).obj X).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD X n := by
  simp [AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]

/-- An additive functor commutes with the alternating sum of the coface maps. -/
public theorem map_objD (X : CosimplicialObject A) (n : ℕ) :
    G.map (AlgebraicTopology.AlternatingCofaceMapComplex.objD X n) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (((CosimplicialObject.whiskering A B).obj G).obj X) n := by
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [G.map_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ G.map_zsmul

/-- **The alternating coface map complex commutes with an additive functor**, the cochain
analogue of Mathlib's
`AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso`. -/
public noncomputable def alternatingCofaceMapComplexCompMapHomologicalComplexIso :
    AlgebraicTopology.alternatingCofaceMapComplex A ⋙ G.mapHomologicalComplex _ ≅
      (CosimplicialObject.whiskering A B).obj G ⋙
        AlgebraicTopology.alternatingCofaceMapComplex B :=
  NatIso.ofComponents
    (fun X ↦ HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
      (fun i j hij ↦ by
        obtain rfl : i + 1 = j := hij
        have h : ((AlgebraicTopology.alternatingCofaceMapComplex B).obj
            (((CosimplicialObject.whiskering A B).obj G).obj X)).d i (i + 1) =
              G.map (((AlgebraicTopology.alternatingCofaceMapComplex A).obj X).d i (i + 1)) :=
          (alternatingCofaceMapComplex_obj_d _ i).trans
            ((map_objD G X i).symm.trans
              (congrArg G.map (alternatingCofaceMapComplex_obj_d X i).symm))
        dsimp only [Iso.refl_hom]
        exact (Category.id_comp _).trans (h.trans (Category.comp_id _).symm)))
    (fun {X Y} _ ↦ by
      ext n
      dsimp only [HomologicalComplex.comp_f]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end Coface

section CochainComplex

variable [Preadditive A] [Preadditive B] [HasProducts.{w} A] [HasProducts.{w} B]
  (G : A ⥤ B) [G.Additive] [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G]
  (E : SimplicialObject (FormalCoproduct.{w} C))

/-- **The complex of sections of a simplicial formal coproduct commutes with a
product-preserving additive functor.**  Applying `G` termwise to `s(P(E))` gives `s((P ⋙ G)(E))`,
naturally in the presheaf `P : Cᵒᵖ ⥤ A`. -/
public noncomputable def cochainComplexFunctorCompMapHomologicalComplexIso :
    cochainComplexFunctor.{w} E ⋙ G.mapHomologicalComplex _ ≅
      (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ cochainComplexFunctor.{w} E :=
  Functor.isoWhiskerLeft (cosimplicialObjectFunctor.{w} E)
      (alternatingCofaceMapComplexCompMapHomologicalComplexIso G) ≪≫
    Functor.isoWhiskerRight (cosimplicialObjectFunctorCompWhiskeringIso.{w} G E)
      (AlgebraicTopology.alternatingCofaceMapComplex B)

end CochainComplex

section Cech

variable [HasFiniteProducts C] [Preadditive A] [Preadditive B] [HasProducts.{w} A]
  [HasProducts.{w} B] (G : A ⥤ B) [G.Additive]
  [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G] {ι : Type w} (U : ι → C)

/-- **The Čech complex commutes with a product-preserving additive functor.** Applying `G`
termwise to the Čech complex of a presheaf `P : Cᵒᵖ ⥤ A` gives the Čech complex of `P ⋙ G`,
naturally in `P`. -/
public noncomputable def cechComplexFunctorCompMapHomologicalComplexIso :
    cechComplexFunctor.{w} U ⋙ G.mapHomologicalComplex _ ≅
      (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ cechComplexFunctor.{w} U :=
  cochainComplexFunctorCompMapHomologicalComplexIso.{w} G (FormalCoproduct.mk _ U).cech

end Cech

end Stacks.CechPushforward

end
