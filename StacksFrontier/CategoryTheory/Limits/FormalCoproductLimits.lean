module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Limits and colimits of semi-representable objects

Let `C` be a category. The Stacks Project's category `SR(C)` of *semi-representable objects* of
`C` is Mathlib's `CategoryTheory.Limits.FormalCoproduct C`, whose objects are indexed families of
objects of `C`, and the functor `F : SR(C) ⥤ PSh(C)` sending a family `{U_i}` to the coproduct
`∐ h_{U_i}` of the representable presheaves is `CategoryTheory.Limits.FormalCoproduct.yoneda`.

Mathlib already constructs the arbitrary coproducts, the pullbacks and the terminal object of
`FormalCoproduct C`, and the fact that `F` commutes with coproducts, but it does so with
anonymous instances; this file restates each of them under a name, so that the corresponding
clause of Tag 01G2 has a declaration to be attached to. The one clause proved here from scratch is
that `F` commutes with *all* limits, for an arbitrary category `C`.

## Main results

* `CategoryTheory.Limits.FormalCoproduct.hasCoproducts_formalCoproduct` and
  `CategoryTheory.Limits.FormalCoproduct.preservesColimitsOfShape_yoneda`: **Stacks Project, Tag
  01G2**, coproducts clause — `SR(C)` has coproducts and `F` commutes with them.
* `CategoryTheory.Limits.FormalCoproduct.preservesLimitsOfSize_yoneda`: **Stacks Project, Tag
  01G2**, limits clause — `F : SR(C) ⥤ PSh(C)` commutes with limits.
* `CategoryTheory.Limits.FormalCoproduct.hasPullbacks_formalCoproduct`: **Stacks Project, Tag
  01G2**, fibre products clause.
* `CategoryTheory.Limits.FormalCoproduct.hasTerminal_formalCoproduct`: **Stacks Project, Tag
  01G2**, final object clause.

The two remaining clauses of the lemma about `SR(C)` are proved elsewhere:
`CategoryTheory.Limits.FormalCoproduct.instHasBinaryProducts` in
`StacksFrontier.CategoryTheory.Limits.FormalCoproductBinaryProducts` (products of pairs) and
`CategoryTheory.Limits.FormalCoproduct.instHasEqualizers` in
`StacksFrontier.CategoryTheory.Limits.FormalCoproductEqualizers` (equalizers).

## Implementation notes

The source's proof of the limits clause is that `Hom_{SR(C)}({U}, K) = F(K)(U)` together with the
fact that limits of presheaves are computed sectionwise. That is exactly the argument used here:
`yonedaCompEvaluationIso` identifies the evaluation of `F` at `U` with the corepresentable functor
`Hom_{SR(C)}(incl U, -)`, which preserves limits, and
`CategoryTheory.Limits.preservesLimits_of_evaluation` assembles the evaluations.

Universes. The clauses about `SR(C)` alone — coproducts, fibre products, products of pairs,
equalizers, final object — hold for `FormalCoproduct.{w} C` with the index universe `w`
unrelated to the universes `u`, `v` of `C`. The clauses involving `F` are different: `F` lands in
`v`-valued presheaves, so writing it as `FormalCoproduct.yoneda` forces the index universe to be
`v`. (The variant of the limits clause for the universe-lifted embedding
`FormalCoproduct.uliftYoneda : FormalCoproduct.{w} C ⥤ Cᵒᵖ ⥤ Type (max w v)`, which keeps `w`
free, is `CategoryTheory.Limits.FormalCoproduct.preservesLimitsOfSize_uliftYoneda` in
`StacksFrontier.CategoryTheory.Sites.Hypercovering.Injectives`.) No hypothesis is placed on `C` for
the coproducts and limits clauses, as in the source.

## References

* [Stacks Project, Tag 01G2](https://stacks.math.columbia.edu/tag/01G2)
-/

@[expose] public section

universe w' w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

section Coproducts

variable (C) in
/-- **Stacks Project, Tag 01G2**, coproducts clause, first half. The category of formal
coproducts of `C` — equivalently, the category `SR(C)` of semi-representable objects of `C` — has
arbitrary coproducts, indexed by types in the index universe `w`. The coproduct of a family of
families of objects is obtained by concatenating the index types. -/
@[stacks 01G2 "coproducts in SR(C)"]
theorem hasCoproducts_formalCoproduct : HasCoproducts.{w} (FormalCoproduct.{w} C) :=
  inferInstance

/-- **Stacks Project, Tag 01G2**, coproducts clause, second half. The functor
`F : SR(C) ⥤ PSh(C)`, sending a family `{U_i}` of objects of `C` to the coproduct `∐ h_{U_i}` of
the representable presheaves, commutes with coproducts. -/
@[stacks 01G2 "F commutes with coproducts"]
theorem preservesColimitsOfShape_yoneda (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (FormalCoproduct.yoneda (C := C)) :=
  inferInstance

end Coproducts

section Limits

/-- Evaluating `F : SR(C) ⥤ PSh(C)` at an object `K` of `C` gives the functor corepresented by the
one-member family `{K}`: a map `{K} ⟶ X` of semi-representable objects is an index `i` of `X`
together with a morphism `K ⟶ X i`, which is a section of `∐ h_{X i}` over `K`.

This is the source's `Mor_{SR(C)}({U}, K) = F(K)(U)`. -/
noncomputable def yonedaCompEvaluationIso (K : Cᵒᵖ) :
    FormalCoproduct.yoneda (C := C) ⋙ (evaluation Cᵒᵖ (Type v)).obj K ≅
      coyoneda.obj (op ((FormalCoproduct.incl C).obj K.unop)) :=
  NatIso.ofComponents (fun X ↦
    sigmaObjIso (CategoryTheory.yoneda.obj ∘ X.obj) K ≪≫
      Types.coproductIso (fun i : X.I ↦ ((CategoryTheory.yoneda.obj ∘ X.obj) i).obj K) ≪≫
        Equiv.toIso (FormalCoproduct.inclHomEquiv K.unop X).symm) (fun {X Y} f ↦ by
    apply (cancel_epi (sigmaObjIso (CategoryTheory.yoneda.obj ∘ X.obj) K).inv).1
    apply Sigma.hom_ext
    intro i
    unfold FormalCoproduct.yoneda FormalCoproduct.eval at *
    simp only [← Category.assoc]
    rw [ι_comp_sigmaObjIso_inv (CategoryTheory.yoneda.obj ∘ X.obj) K i]
    rw [Functor.comp_map, evaluation_obj_map]
    dsimp only
    rw [← NatTrans.comp_app, Sigma.ι_comp_desc, NatTrans.comp_app]
    ext g
    simp only [Functor.comp_obj, evaluation_obj_obj, Function.comp_apply, yoneda_obj_obj,
      yoneda_map_app, Iso.trans_hom, Category.assoc, ι_comp_sigmaObjIso_hom_assoc, comp_apply,
      Types.coproductIso_ι_comp_hom_apply, Equiv.toIso_hom_hom_apply,
      FormalCoproduct.inclHomEquiv, FormalCoproduct.Hom.fromIncl, Equiv.symm_mk,
      Equiv.coe_fn_mk, Functor.flip_obj_obj, Functor.flip_obj_map, TypeCat.Fun.toFun_apply,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
    rfl)

/-- **Stacks Project, Tag 01G2**, limits clause. The functor `F : SR(C) ⥤ PSh(C)`, sending a
family `{U_i}` of objects of `C` to the coproduct `∐ h_{U_i}` of the representable presheaves,
commutes with limits — of any shape, and for an arbitrary category `C`.

Limits of presheaves are computed sectionwise, and each section functor of `F` is corepresentable
by `yonedaCompEvaluationIso`. -/
@[stacks 01G2 "F : SR(C) → PSh(C) commutes with limits"]
noncomputable instance preservesLimitsOfSize_yoneda :
    PreservesLimitsOfSize.{w, w'} (FormalCoproduct.yoneda (C := C)) :=
  preservesLimits_of_evaluation _ fun K ↦
    (preservesLimitsOfSize_iff_of_natIso (yonedaCompEvaluationIso K)).2 inferInstance

end Limits

section FibreProducts

variable (C) in
/-- **Stacks Project, Tag 01G2**, fibre products clause. If `C` has fibre products, then so does
its category of formal coproducts — equivalently, the category `SR(C)` of semi-representable
objects of `C` has fibre products. They are computed componentwise, the index type of
`{U_i} ×_{{V_j}} {W_k}` being the set of triples `(i, j, k)` with `j` the common image of `i` and
of `k`. -/
@[stacks 01G2 "fibre products in SR(C)"]
theorem hasPullbacks_formalCoproduct [HasPullbacks C] :
    HasPullbacks (FormalCoproduct.{w} C) :=
  inferInstance

end FibreProducts

section Terminal

variable (C) in
/-- **Stacks Project, Tag 01G2**, final object clause. If `C` has a final object `X`, then the
one-member family `{X}` is a final object of the category of formal coproducts of `C` —
equivalently, of the category `SR(C)` of semi-representable objects of `C`. -/
@[stacks 01G2 "final object in SR(C)"]
theorem hasTerminal_formalCoproduct [HasTerminal C] :
    HasTerminal (FormalCoproduct.{w} C) :=
  inferInstance

end Terminal

end CategoryTheory.Limits.FormalCoproduct

end
