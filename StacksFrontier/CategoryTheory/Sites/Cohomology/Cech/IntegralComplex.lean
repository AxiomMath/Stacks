module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import StacksFrontier.CategoryTheory.Adjunction.Whiskering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
import StacksCore.Tactic.StacksAttribute

/-!
# The integral Čech complex

Let `E = {U_i → U}` be a family of morphisms of a category `C` with fixed target, all of
whose finite nonempty fibre products exist. Stacks 03AS introduces the *integral Čech
complex* of `E`: the chain complex of abelian presheaves whose degree-`n` term is the direct
sum, over `(n+1)`-tuples `i` of indices, of the free abelian presheaf on the representable
presheaf of the corresponding fibre product `U_{i_0} ×_U ⋯ ×_U U_{i_n}`, with the
alternating sum of the face maps as differential. Its defining property, also part of 03AS,
is that mapping it into an abelian presheaf `F` returns the Čech cochain complex of `F`:
`Hom(ℤ_{E,•}, F) = C^•(E, F)`, naturally in `F`.

The construction is the one in the source. The free abelian Yoneda functor is extended from
objects over `U` to formal coproducts and applied to the simplicial formal coproduct of
fibre products of Stacks 03AM; its alternating face map complex is the integral Čech
complex. The comparison with the Čech cochain complex is then degreewise the fact that a map
out of a direct sum is a family of maps out of the summands, together with the fact that the
free abelian presheaf on a representable corepresents evaluation; the two differentials
agree because both are the same alternating sum of face maps.

## Main definitions

* `Stacks.CechSite.freeAbelianYoneda`: the free abelian presheaf on a representable
  presheaf, with the generators placed in an independent coefficient universe.
* `Stacks.CechSite.integralCechComplex`: the integral Čech chain complex of the family.
* `Stacks.CechSite.homComplexFunctor`: the contravariant additive Hom functor applied to a
  chain complex of abelian presheaves, as a cochain-complex-valued functor.
* `Stacks.CechSite.liftedCechComplexFunctor`: the Čech complex functor of Stacks 03AM with
  its values lifted to the universe in which natural transformations of presheaves live.

## Main results

* `Stacks.CechSite.integralCechComplex_X` and `Stacks.CechSite.integralCechComplex_d`: the
  terms and the differential of the integral Čech complex are the ones displayed in the
  source.
* `Stacks.CechSite.homIntegralCechComplexIso`: mapping the integral Čech complex into an
  abelian presheaf gives, naturally in that presheaf, its Čech cochain complex.

## Implementation notes

A family of morphisms with fixed target is a `PreZeroHypercover`, as in Stacks 03AM, and the
fibre products are products in the over category. Because the construction goes through the
simplicial formal coproduct of Stacks 03AM, the terms and the signs of the differential are
part of the definition rather than properties of an unspecified choice.

The coefficient universe `a` is independent of the morphism universe `v`: `ULift` places the
representable generators in `Type (max v a)` before their free abelian groups are formed. A
morphism of presheaves lives in `Type (max u v a)`, which is why
`Stacks.CechSite.homComplexFunctor` lands there and the Čech complex has to be lifted by
`Stacks.CechSite.liftedCechComplexFunctor` for the comparison to be stated.

## References

* [Stacks Project, Tag 03AS](https://stacks.math.columbia.edu/tag/03AS)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

universe w v u a

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology
open CategoryTheory.Preadditive

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)

/-- The free abelian representable presheaf, with its generators lifted to an
independent coefficient universe. -/
public noncomputable def freeAbelianYoneda :
    C ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) :=
  uliftYoneda.{a} ⋙
    (Functor.whiskeringRight Cᵒᵖ (Type (max v a)) AddCommGrpCat.{max v a}).obj
      AddCommGrpCat.free

/-- The lifted free abelian representable presheaf represents evaluation. -/
@[sga "4 Vbis 2.3.1" "Bijection Hom(r_D(i)"]
public noncomputable def freeAbelianYonedaEquiv (U : C)
    (A : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) :
    (freeAbelianYoneda.{v, u, a}.obj U ⟶ A) ≃ A.obj (Opposite.op U) :=
  ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (uliftYoneda.{a}.obj U) A).trans
    uliftYonedaEquiv

/-- Evaluation of a morphism from a free representable is natural in its target. -/
@[sga "4 Vbis 2.3.1" "partial"]
public theorem freeAbelianYonedaEquiv_naturality_right (U : C)
    (A B : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) (f : A ⟶ B)
    (η : freeAbelianYoneda.{v, u, a}.obj U ⟶ A) :
    freeAbelianYonedaEquiv U B (η ≫ f) =
      f.app (Opposite.op U) (freeAbelianYonedaEquiv U A η) := rfl

/-- Evaluation of a morphism from a free representable is natural in its representing object. -/
@[sga "4 Vbis 2.3.1" "partial"]
public theorem freeAbelianYonedaEquiv_naturality_left (U U' : C)
    (A : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) (f : U ⟶ U')
    (η : freeAbelianYoneda.{v, u, a}.obj U' ⟶ A) :
    freeAbelianYonedaEquiv U A (freeAbelianYoneda.{v, u, a}.map f ≫ η) =
      A.map f.op (freeAbelianYonedaEquiv U' A η) := by
  have key : (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (uliftYoneda.{a}.obj U) A
        (freeAbelianYoneda.{v, u, a}.map f ≫ η) =
      uliftYoneda.{a}.map f ≫
        (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (uliftYoneda.{a}.obj U') A η :=
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left (uliftYoneda.{a}.map f) η
  show uliftYonedaEquiv
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (uliftYoneda.{a}.obj U) A
      (freeAbelianYoneda.{v, u, a}.map f ≫ η)) = _
  rw [key]
  exact (uliftYonedaEquiv_naturality _ f.op).symm

/-- Realize a formal coproduct of objects over `X` as the corresponding coproduct of
free abelian representable presheaves. -/
public noncomputable def integralCechRealization
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})] :
    FormalCoproduct.{w} (Over X) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) :=
  (FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})).obj
    (Over.forget X ⋙ freeAbelianYoneda.{v, u, a})

/-- The simplicial abelian presheaf whose degree `n` term is the direct sum of the free
abelian presheaves represented by the `(n + 1)`-fold fibre products in the family. -/
public noncomputable def integralCechSimplicialObject
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) :=
  ((SimplicialObject.whiskering _ _).obj (integralCechRealization.{w, v, u, a} (X := X))).obj
    (cechSimplicialObject E)

/-- The canonical integral Čech chain complex. Its degree `n` term is
`\bigoplus_{i : Fin (n+1) → E.I₀} ℤ[U_i]`, with `U_i` the corresponding fibre
product over `X`. -/
@[stacks 03AS "the integral Čech complex"]
public noncomputable def integralCechComplex
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) ℕ :=
  (alternatingFaceMapComplex _).obj (integralCechSimplicialObject.{w, v, u, a} E)

/-- The degree-`n` term of the integral Čech complex is the indicated direct sum of
free abelian representable presheaves. -/
@[stacks 03AS "the terms of the integral Čech complex"]
public theorem integralCechComplex_X
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] (n : ℕ) :
    (integralCechComplex.{w, v, u, a} E).X n =
      ∐ fun i : Fin (n + 1) → E.I₀ ↦
      freeAbelianYoneda.{v, u, a}.obj ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left) := rfl

/-- The differential of the integral Čech complex is the alternating sum of the canonical maps
which omit one factor. -/
@[stacks 03AS "the differential of the integral Čech complex"]
public theorem integralCechComplex_d
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] (n : ℕ) :
    (integralCechComplex.{w, v, u, a} E).d (n + 1) n =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      (integralCechSimplicialObject.{w, v, u, a} E).δ j := AlternatingFaceMapComplex.obj_d_eq _ _

/-- Applying the contravariant additive Hom functor to a chain complex of abelian
presheaves gives a cochain-complex functor in the target presheaf. -/
public noncomputable def homComplexFunctor
    (K : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) ⥤ CochainComplex AddCommGrpCat.{max u v a} ℕ where
  obj F := ((preadditiveYoneda.obj F).mapHomologicalComplex _).obj K.op
  map {F G} f :=
    (NatTrans.mapHomologicalComplex (preadditiveYoneda.map f) _).app K.op
  map_id F := by
    simp only [preadditiveYoneda.map_id]
    rfl
  map_comp f g := by
    simp only [preadditiveYoneda.map_comp]
    rfl

/-- The Čech-complex functor with its values lifted to the universe in which natural
transformations of presheaves live. -/
public noncomputable def liftedCechComplexFunctor
    [HasProducts.{w} AddCommGrpCat.{max u v a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) ⥤ CochainComplex AddCommGrpCat.{max u v a} ℕ :=
  (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{max v a} AddCommGrpCat.{max u v a}).obj
      AddCommGrpCat.uliftFunctor.{u, max v a} ⋙
    cechComplexFunctor E

section AlternatingSums

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]

/-- An additive contravariant functor turns an alternating sum of morphisms into the
alternating sum of their images. -/
private lemma map_op_sum_zsmul {B : Type u₂} [Category.{v₂} B] [Preadditive B]
    (G : Aᵒᵖ ⥤ B) [G.Additive] {ι : Type*} [Fintype ι] {Y Z : A}
    (c : ι → ℤ) (g : ι → (Y ⟶ Z)) :
    G.map (∑ j, c j • g j).op = ∑ j, c j • G.map (g j).op := by
  simp only [op_sum, op_zsmul, Functor.map_sum, Functor.map_zsmul]

/-- A square which commutes against each morphism of a family commutes against any
`ℤ`-linear combination of them. -/
private lemma comp_sum_zsmul_comm {ι : Type*} [Fintype ι] {W Y Y' Z : A}
    (u : W ⟶ Y) (v : Y' ⟶ Z) (c : ι → ℤ) (f : ι → (Y ⟶ Z)) (g : ι → (W ⟶ Y'))
    (hcomm : ∀ j, u ≫ f j = g j ≫ v) :
    u ≫ (∑ j, c j • f j) = (∑ j, c j • g j) ≫ v := by
  simp only [comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hcomm j]

end AlternatingSums

section Comparison

/-- The differential of the lifted Čech complex is the alternating sum of the maps induced
by the face maps of the simplicial formal coproduct of fibre products. -/
private theorem liftedCechComplexFunctor_obj_d
    [HasProducts.{w} AddCommGrpCat.{max u v a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) (i : ℕ) :
    ((liftedCechComplexFunctor.{w, v, u, a} E).obj F).d i (i + 1) =
      ∑ j : Fin (i + 2), (-1 : ℤ) ^ (j : ℕ) •
        ((FormalCoproduct.evalOp (Over X) AddCommGrpCat.{max u v a}).obj
          ((Over.forget X).op ⋙ F ⋙ AddCommGrpCat.uliftFunctor.{u, max v a})).map
            ((cechSimplicialObject E).δ j).op := by
  simp only [liftedCechComplexFunctor, cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor]
  show (AlternatingCofaceMapComplex.obj
    ((FormalCoproduct.cosimplicialObjectFunctor
      (cechSimplicialObject E)).obj
        ((Over.forget X).op ⋙ F ⋙ AddCommGrpCat.uliftFunctor.{u, max v a}))).d i (i + 1) = _
  simp only [AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlternatingCofaceMapComplex.objD]
  rfl

/-- The differential of the integral Čech complex, with its face maps written as the
realizations of the face maps of the simplicial formal coproduct of fibre products. -/
private theorem integralCechComplex_d'
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] (n : ℕ) :
    (integralCechComplex.{w, v, u, a} E).d (n + 1) n =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        (integralCechRealization.{w, v, u, a} (X := X)).map
          ((cechSimplicialObject E).δ j) :=
  integralCechComplex_d.{w, v, u, a} E n

/-- The differential of the Hom complex of the integral Čech complex is the alternating sum
of the maps induced by the realized face maps. -/
private theorem homComplexFunctor_integralCechComplex_obj_d
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) (i : ℕ) :
    ((homComplexFunctor (integralCechComplex.{w, v, u, a} E)).obj F).d i (i + 1) =
      ∑ j : Fin (i + 2), (-1 : ℤ) ^ (j : ℕ) •
        (preadditiveYoneda.obj F).map
          ((integralCechRealization.{w, v, u, a} (X := X)).map
            ((cechSimplicialObject E).δ j)).op := by
  show (preadditiveYoneda.obj F).map
    ((integralCechComplex.{w, v, u, a} E).d (i + 1) i).op = _
  rw [integralCechComplex_d'.{w, v, u, a} E i]
  exact map_op_sum_zsmul (preadditiveYoneda.obj F) _ _

/-- Mapping the integral Čech chain complex into an abelian presheaf is naturally isomorphic, as a
cochain complex, to its Čech complex. -/
@[stacks 03AS "the functorial Hom identification"]
public noncomputable def homIntegralCechComplexIso
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
    [HasProducts.{w} AddCommGrpCat.{max u v a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    homComplexFunctor (integralCechComplex.{w, v, u, a} E) ≅
      liftedCechComplexFunctor.{w, v, u, a} E := by
  let homCoproductIsoProduct {J : Type w}
      (G : J → (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})) [HasCoproduct G]
      (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) :
      AddCommGrpCat.of ((∐ G) ⟶ F) ≅
        ∏ᶜ (fun j ↦ AddCommGrpCat.of (G j ⟶ F)) := {
    hom := Pi.lift fun j ↦ AddCommGrpCat.ofHom
      { toFun := fun f ↦ Sigma.ι G j ≫ f
        map_zero' := by simp
        map_add' := by simp }
    inv := AddCommGrpCat.ofHom
      { toFun := fun x ↦ Sigma.desc fun j ↦ Pi.π (fun j ↦ AddCommGrpCat.of (G j ⟶ F)) j x
        map_zero' := by ext; simp
        map_add' := by intro x y; ext; simp }
    hom_inv_id := by ext f j; simp
    inv_hom_id := by ext x j; simp }
  let ZUAddEquiv (U : C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) :
      (freeAbelianYoneda.{v, u, a}.obj U ⟶ F) ≃+ F.obj (Opposite.op U) :=
    { toEquiv := freeAbelianYonedaEquiv U F
      map_add' := fun _ _ ↦ by rfl }
  let ZUIsoUlift (U : C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) :
      AddCommGrpCat.of (freeAbelianYoneda.{v, u, a}.obj U ⟶ F) ≅
        AddCommGrpCat.uliftFunctor.{u, max v a}.obj (F.obj (Opposite.op U)) :=
    ((ZUAddEquiv U F).trans AddEquiv.ulift.symm).toAddCommGrpIso
  let e (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) (n : ℕ) :=
    homCoproductIsoProduct
      (fun i : Fin (n + 1) → E.I₀ ↦
        freeAbelianYoneda.{v, u, a}.obj ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)) F ≪≫
      Pi.mapIso (fun i ↦ ZUIsoUlift
        ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left) F)
  have e_apply (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) (n : ℕ)
      (i : Fin (n + 1) → E.I₀)
      (x : (∐ fun j : Fin (n + 1) → E.I₀ ↦
        freeAbelianYoneda.{v, u, a}.obj ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) ⟶ F) :
      ((e F n).hom ≫ Pi.π _ i) x =
        ULift.up (freeAbelianYonedaEquiv _ F
          (Sigma.ι (fun j : Fin (n + 1) → E.I₀ ↦
            freeAbelianYoneda.{v, u, a}.obj
              ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) i ≫ x)) := by
    simp [e, homCoproductIsoProduct, ZUIsoUlift, ZUAddEquiv, Category.assoc, Pi.mapIso_hom_π]
    rfl
  have e_map (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) (n m : ℕ)
      (h : (cechSimplicialObject E).obj (Opposite.op { len := m }) ⟶
        (cechSimplicialObject E).obj (Opposite.op { len := n })) :
      (e F n).hom ≫
        ((FormalCoproduct.evalOp (Over X) AddCommGrpCat.{max u v a}).obj
          ((Over.forget X).op ⋙ F ⋙ AddCommGrpCat.uliftFunctor.{u, max v a})).map h.op =
        (preadditiveYoneda.obj F).map
          ((integralCechRealization.{w, v, u, a} (X := X)).map h).op ≫ (e F m).hom := by
    let Pn : (Fin (n + 1) → E.I₀) → AddCommGrpCat.{max u v a} := fun i ↦
      AddCommGrpCat.uliftFunctor.{u, max v a}.obj
        (F.obj (Opposite.op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)))
    let Pm : (Fin (m + 1) → E.I₀) → AddCommGrpCat.{max u v a} := fun i ↦
      AddCommGrpCat.uliftFunctor.{u, max v a}.obj
        (F.obj (Opposite.op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)))
    let ψ (k : Fin (m + 1) → E.I₀) : Pn (h.f k) ⟶ Pm k :=
      AddCommGrpCat.uliftFunctor.{u, max v a}.map (F.map (h.φ k).left.op)
    let R := (integralCechRealization.{w, v, u, a} (X := X)).map h
    change (e F n).hom ≫ Pi.lift (fun k ↦ Pi.π Pn (h.f k) ≫ ψ k) =
      (preadditiveYoneda.obj F).map R.op ≫ (e F m).hom
    apply Pi.hom_ext
    intro k
    change Fin (m + 1) → E.I₀ at k
    have h₁ :
        ((e F n).hom ≫ Pi.lift (fun k ↦ Pi.π Pn (h.f k) ≫ ψ k)) ≫ Pi.π Pm k =
          (e F n).hom ≫ (Pi.π Pn (h.f k) ≫ ψ k) := by
      calc
        ((e F n).hom ≫ Pi.lift (fun k ↦ Pi.π Pn (h.f k) ≫ ψ k)) ≫ Pi.π Pm k =
            (e F n).hom ≫
              (Pi.lift (fun k ↦ Pi.π Pn (h.f k) ≫ ψ k) ≫ Pi.π Pm k) :=
          Category.assoc _ _ _
        _ = (e F n).hom ≫ (Pi.π Pn (h.f k) ≫ ψ k) :=
          congrArg (fun t ↦ (e F n).hom ≫ t)
            (Pi.lift_comp_π (fun k ↦ Pi.π Pn (h.f k) ≫ ψ k) k)
    have h₂ :
        (e F n).hom ≫ (Pi.π Pn (h.f k) ≫ ψ k) =
          (preadditiveYoneda.obj F).map R.op ≫ ((e F m).hom ≫ Pi.π Pm k) := by
      apply AddCommGrpCat.hom_ext
      ext x
      change (ψ k) (((e F n).hom ≫ Pi.π Pn (h.f k)) x) =
        ((e F m).hom ≫ Pi.π Pm k) (R ≫ x)
      rw [e_apply F n (h.f k) x, e_apply F m k (R ≫ x)]
      have hι :
          Sigma.ι (fun j : Fin (m + 1) → E.I₀ ↦
            freeAbelianYoneda.{v, u, a}.obj ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) k ≫ R =
          freeAbelianYoneda.{v, u, a}.map (h.φ k).left ≫
            Sigma.ι (fun j : Fin (n + 1) → E.I₀ ↦
              freeAbelianYoneda.{v, u, a}.obj
                ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) (h.f k) := by
        dsimp [R, integralCechRealization]
        exact Sigma.ι_desc _ _
      have hh :
          Sigma.ι (fun j : Fin (m + 1) → E.I₀ ↦
            freeAbelianYoneda.{v, u, a}.obj
              ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) k ≫ (R ≫ x) =
          freeAbelianYoneda.{v, u, a}.map (h.φ k).left ≫
            (Sigma.ι (fun j : Fin (n + 1) → E.I₀ ↦
              freeAbelianYoneda.{v, u, a}.obj
                ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) (h.f k) ≫ x) :=
        (Category.assoc _ R x).symm.trans
          ((congrArg (· ≫ x) hι).trans (Category.assoc _ _ x))
      rw [hh]
      change ULift.up (F.map (h.φ k).left.op
          (freeAbelianYonedaEquiv _ F
            (Sigma.ι (fun j : Fin (n + 1) → E.I₀ ↦
              freeAbelianYoneda.{v, u, a}.obj
                ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) (h.f k) ≫ x))) =
        ULift.up (freeAbelianYonedaEquiv _ F
          (freeAbelianYoneda.{v, u, a}.map (h.φ k).left ≫
            (Sigma.ι (fun j : Fin (n + 1) → E.I₀ ↦
              freeAbelianYoneda.{v, u, a}.obj
                ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) (h.f k) ≫ x)))
      exact congrArg ULift.up
        (freeAbelianYonedaEquiv_naturality_left _ _ F (h.φ k).left
          (Sigma.ι (fun j : Fin (n + 1) → E.I₀ ↦
            freeAbelianYoneda.{v, u, a}.obj
                ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) (h.f k) ≫ x)).symm
    have h₃ :
        (preadditiveYoneda.obj F).map R.op ≫ ((e F m).hom ≫ Pi.π Pm k) =
          ((preadditiveYoneda.obj F).map R.op ≫ (e F m).hom) ≫ Pi.π Pm k :=
      (Category.assoc _ _ _).symm
    exact h₁.trans (h₂.trans h₃)
  let eComplex (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) :
      (homComplexFunctor (integralCechComplex.{w, v, u, a} E)).obj F ≅
        (liftedCechComplexFunctor.{w, v, u, a} E).obj F :=
    HomologicalComplex.Hom.isoOfComponents (e F) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    rw [liftedCechComplexFunctor_obj_d E F i,
      homComplexFunctor_integralCechComplex_obj_d E F i]
    exact comp_sum_zsmul_comm _ _ _ _ _
      (fun j ↦ e_map F i (i + 1) ((cechSimplicialObject E).δ j))
    )
  refine NatIso.ofComponents eComplex ?_
  · intro F G f
    apply HomologicalComplex.hom_ext
    intro n
    let PF : (Fin (n + 1) → E.I₀) → AddCommGrpCat.{max u v a} :=
      fun i ↦ AddCommGrpCat.uliftFunctor.{u, max v a}.obj
        (F.obj (Opposite.op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)))
    let PG : (Fin (n + 1) → E.I₀) → AddCommGrpCat.{max u v a} :=
      fun i ↦ AddCommGrpCat.uliftFunctor.{u, max v a}.obj
        (G.obj (Opposite.op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)))
    let φ : ∀ i, PF i ⟶ PG i := fun i ↦
      AddCommGrpCat.uliftFunctor.{u, max v a}.map
        (f.app (Opposite.op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)))
    change (preadditiveYoneda.map f).app
        (Opposite.op ((integralCechComplex.{w, v, u, a} E).X n)) ≫ (e G n).hom =
      (e F n).hom ≫ Limits.Pi.map φ
    apply Pi.hom_ext
    intro k
    have h₂ :
        (preadditiveYoneda.map f).app
          (Opposite.op ((integralCechComplex.{w, v, u, a} E).X n)) ≫
          ((e G n).hom ≫ Pi.π PG k) =
        (e F n).hom ≫ (Pi.π PF k ≫ φ k) := by
      apply AddCommGrpCat.hom_ext
      ext x
      change (∐ fun j : Fin (n + 1) → E.I₀ ↦
        freeAbelianYoneda.{v, u, a}.obj ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) ⟶ F at x
      change (((e G n).hom ≫ Pi.π PG k) (x ≫ f)) =
        (φ k) (((e F n).hom ≫ Pi.π PF k) x)
      rw [e_apply G n k (x ≫ f), e_apply F n k x]
      exact congrArg ULift.up
        (freeAbelianYonedaEquiv_naturality_right _ F G f
          (Sigma.ι (fun j : Fin (n + 1) → E.I₀ ↦
            freeAbelianYoneda.{v, u, a}.obj ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)) k ≫ x))
    have h₁ :
        ((preadditiveYoneda.map f).app
          (Opposite.op ((integralCechComplex.{w, v, u, a} E).X n)) ≫ (e G n).hom) ≫ Pi.π PG k =
        (preadditiveYoneda.map f).app
          (Opposite.op ((integralCechComplex.{w, v, u, a} E).X n)) ≫
          ((e G n).hom ≫ Pi.π PG k) := Category.assoc _ _ _
    have h₃ :
        (e F n).hom ≫ (Pi.π PF k ≫ φ k) =
        ((e F n).hom ≫ Limits.Pi.map φ) ≫ Pi.π PG k := by
      calc
        (e F n).hom ≫ (Pi.π PF k ≫ φ k) =
            (e F n).hom ≫ (Limits.Pi.map φ ≫ Pi.π PG k) := by rw [Pi.map_π]
        _ = ((e F n).hom ≫ Limits.Pi.map φ) ≫ Pi.π PG k :=
          (Category.assoc _ _ _).symm
    exact h₁.trans (h₂.trans h₃)

end Comparison



end Stacks.CechSite

end
