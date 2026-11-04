module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentPushforward
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSectionsH1
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSectionsVariable

/-!
# The comparison on `H₁` of the sections is natural along a square through a pushforward

Let `F : C₀ ⥤ C` be a continuous functor, `a : A ⟶ B` a morphism of sheaves of commutative rings
on `C`, `a₀ : A₀ ⟶ B₀` one on `C₀`, and `ψ : A₀ ⟶ F_*A`, `β : B₀ ⟶ F_*B` with
`a₀ ≫ β = ψ ≫ F_*a`.  The chain map `NL_{B₀/A₀} ⟶ F_*NL_{B/A}` of
`Stacks.SheafOfModules.naiveCotangentComplexPushforwardSquareMap` is, in degree `-1`, the map of
conormal sheaves of the canonical presentations.  This file computes it on the classes of
polynomials: the free algebras `A₀[B₀] ⟶ F_*(A[B])` on sections over `X` are the map
`A₀(X)[B₀(X)] ⟶ A(F X)[B(F X)]` of polynomial rings induced by the square, read through the
comparisons of the sections of the free algebra sheaves with polynomial rings.

## Main results

* `Stacks.SheafOfModules.pushforwardFreeAlgebraMap_freeAlgebraSectionsMap`: the free algebras.
* `Stacks.SheafOfModules.naiveCotangentComplexPushforwardMap_f_negOne`: in degree `-1` the chain
  map `NL_{F_*B/F_*A} ⟶ F_*NL_{B/A}` is the map of conormal sheaves.
* `Stacks.SheafOfModules.pushforwardConormalMap_conormalMapOfSquare_sectionsH1Comparison`: the
  degree `-1` maps carry the comparison `σ₀ : H₁(L_{B₀(X)/A₀(X)}) ⟶ NL_{B₀/A₀}^{-1}(X)` to the
  comparison `σ : H₁(L_{B(F X)/A(F X)}) ⟶ NL_{B/A}^{-1}(F X)` composed with the map of `H₁`
  induced by the square of rings on sections.
* `Stacks.SheafOfModules.naiveCotangentComplexPushforwardSquareMap_f_negOne_sectionsH1Comparison`:
  the same for the chain map `NL_{B₀/A₀} ⟶ F_*NL_{B/A}` of the square in degree `-1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Algebra Stacks.NaiveCotangent
open Stacks.Sites.Conormal Stacks.Sites.FreeAlgebra

universe v₀ u₀ v u w z

namespace Stacks.SheafOfModules

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C : Type u} [Category.{v} C]
  (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C) (F : C₀ ⥤ C)
  [F.IsContinuous J₀ J] [HasWeakSheafify J₀ CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{w}]
  (A B : Sheaf J CommRingCat.{w}) (A₀ B₀ : Sheaf J₀ CommRingCat.{w})
  (ψ : A₀ ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
  (β : B₀ ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)

/-- **The free algebras on sections.**  The map `A₀[B₀] ⟶ (F_*A)[F_*B] ⟶ F_*(A[B])` on sections
over `X`, applied to the image of a polynomial `p ∈ A₀(X)[B₀(X)]`, is the image of the polynomial
`p` with coefficients mapped along `ψ` and variables along `β`. -/
theorem pushforwardFreeAlgebraMap_freeAlgebraSectionsMap (X : C₀ᵒᵖ)
    (p : MvPolynomial (ToType (B₀.obj.obj X)) (ToType (A₀.obj.obj X))) :
    ((pushforwardFreeAlgebraMap J₀ J F A B).hom.app X).hom
        (((canonicalFreeAlgebraMapOfSquare J₀ A₀
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A) B₀
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B) ψ β).hom.app X).hom
          (freeAlgebraSectionsMap J₀ A₀ B₀ X p)) =
      freeAlgebraSectionsMap J A B (op (F.obj X.unop))
        (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (ψ.hom.app X).hom)
          (fun s => MvPolynomial.X ((β.hom.app X).hom s)) p) := by
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext
    (f := ((pushforwardFreeAlgebraMap J₀ J F A B).hom.app X).hom.comp
      (((canonicalFreeAlgebraMapOfSquare J₀ A₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A) B₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B) ψ β).hom.app X).hom.comp
        (freeAlgebraSectionsMap J₀ A₀ B₀ X)))
    (g := (freeAlgebraSectionsMap J A B (op (F.obj X.unop))).comp
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (ψ.hom.app X).hom)
        (fun s => MvPolynomial.X ((β.hom.app X).hom s)))) (fun r => ?_) (fun s => ?_)) p
  · have h₁ := ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app X)
      (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J₀ A₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        (underlyingPresheaf J₀ B₀)
        (underlyingPresheaf J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)) ψ
        (underlyingPresheafMap J₀ B₀ _ β))) r
    have h₂ := ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app X)
      (freeAlgebraSheafCoefficientMap_comp_pushforwardFreeAlgebraMap J₀ J F A B))
      ((ψ.hom.app X).hom r)
    refine ((congrArg ((pushforwardFreeAlgebraMap J₀ J F A B).hom.app X).hom h₁).trans
      h₂).trans ?_
    show _ = freeAlgebraSectionsMap J A B (op (F.obj X.unop))
      (MvPolynomial.eval₂ (MvPolynomial.C.comp (ψ.hom.app X).hom)
        (fun s => MvPolynomial.X ((β.hom.app X).hom s)) (MvPolynomial.C r))
    rw [MvPolynomial.eval₂_C]
    rfl
  · have h₃ := congrArg (fun t => t.app X ((β.hom.app X).hom s))
      (freeAlgebraSheafVariable_comp_desc J₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj
          (freeAlgebraSheaf J A (underlyingPresheaf J B)))
        (underlyingPresheaf J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B))
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)))
        (Functor.whiskerLeft F.op (freeAlgebraSheafVariable J A (underlyingPresheaf J B))))
    have h₄ := congrArg (fun t => t.app X s)
      (freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare J₀ A₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A) (underlyingPresheaf J₀ B₀)
        (underlyingPresheaf J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)) ψ
        (underlyingPresheafMap J₀ B₀ _ β))
    refine (congrArg ((pushforwardFreeAlgebraMap J₀ J F A B).hom.app X).hom h₄).trans
      (h₃.trans ?_)
    show _ = freeAlgebraSectionsMap J A B (op (F.obj X.unop))
      (MvPolynomial.eval₂ (MvPolynomial.C.comp (ψ.hom.app X).hom)
        (fun s => MvPolynomial.X ((β.hom.app X).hom s)) (MvPolynomial.X s))
    rw [MvPolynomial.eval₂_X]
    rfl

variable [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (a : A ⟶ B) (a₀ : A₀ ⟶ B₀)
  (hsq : a₀ ≫ β = ψ ≫ (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)

/-- In degree `-1`, `NL_{F_*B/F_*A} ⟶ F_*NL_{B/A}` is the map of conormal sheaves. -/
theorem naiveCotangentComplexPushforwardMap_f_negOne :
    (naiveCotangentComplexPushforwardMap.{v₀, u₀, v, u, w, z} J₀ J F A B a).f (-1) =
      eqToHom (naiveCotangentComplex_X_negOne.{v₀, u₀, w, max u v z} J₀ _ _
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)) ≫
        pushforwardConormalMap.{v₀, u₀, v, u, w, z} J₀ J F A B a ≫
        (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingSheafHom J₀ J F B)).map
          (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, max u₀ v₀ z} J A B a).symm) := by
  have : HasZeroObject (_root_.SheafOfModules.{max w u₀ v₀ u v z}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B))) :=
    hasZeroObject_of_hasTerminal_object
  have h₀ : (HomologicalComplex.doubleXIso₀
      (canonicalConormalSequence.{v₀, u₀, w, max u v z} J₀ _ _
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom =
      eqToHom (naiveCotangentComplex_X_negOne.{v₀, u₀, w, max u v z} J₀ _ _
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)) := by
    simp only [HomologicalComplex.doubleXIso₀]
    congr 1
  rw [← h₀]
  unfold naiveCotangentComplexPushforwardMap
  apply HomologicalComplex.mkHomFromDouble_f₀

/-- In degree `0`, `NL_{F_*B/F_*A} ⟶ F_*NL_{B/A}` is the map of the terms
`F_*B ⊗ Ω_{(F_*A)[F_*B]/F_*A} ⟶ F_*(B ⊗ Ω_{A[B]/A})`. -/
theorem naiveCotangentComplexPushforwardMap_f_zero :
    (naiveCotangentComplexPushforwardMap.{v₀, u₀, v, u, w, z} J₀ J F A B a).f 0 =
      eqToHom (naiveCotangentComplex_X_zero.{v₀, u₀, w, max u v z} J₀ _ _
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)) ≫
        conormalPushforwardTensorMap.{v₀, u₀, v, u, w, z} J₀ J F A B a ≫
        (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingSheafHom J₀ J F B)).map
          (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, max u₀ v₀ z} J A B a).symm) := by
  have : HasZeroObject (_root_.SheafOfModules.{max w u₀ v₀ u v z}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B))) :=
    hasZeroObject_of_hasTerminal_object
  have h₁ : (HomologicalComplex.doubleXIso₁
      (canonicalConormalSequence.{v₀, u₀, w, max u v z} J₀ _ _
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom =
      eqToHom (naiveCotangentComplex_X_zero.{v₀, u₀, w, max u v z} J₀ _ _
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)) := by
    simp only [HomologicalComplex.doubleXIso₁]
    congr 1
  rw [← h₁]
  unfold naiveCotangentComplexPushforwardMap
  apply HomologicalComplex.mkHomFromDouble_f₁

omit [HasWeakSheafify J₀ CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{w}]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hsq in
/-- The square on sections over `X`: `A₀(X) → B₀(X) → B(F X)` is `A₀(X) → A(F X) → B(F X)`. -/
theorem sectionsSquare_pushforward (X : C₀ᵒᵖ) (r : ToType (A₀.obj.obj X)) :
    (β.hom.app X).hom ((a₀.hom.app X).hom r) = (a.hom.app (op (F.obj X.unop))).hom
      ((ψ.hom.app X).hom r) :=
  ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app X) hsq) r

include hsq in
/-- **Naturality of the comparison on `H₁` of the sections along a square through a
pushforward** (degree `-1`).  The degree `-1` map of conormal sheaves of the square
`a₀ ≫ β = ψ ≫ F_*a`, followed by the degree `-1` map of `NL_{F_*B/F_*A} ⟶ F_*NL_{B/A}`, carries
the image of `z ∈ H₁(L_{B₀(X)/A₀(X)})` to the image of its image in `H₁(L_{B(F X)/A(F X)})` under
the map induced by the square of rings on sections. -/
theorem pushforwardConormalMap_conormalMapOfSquare_sectionsH1Comparison (X : C₀ᵒᵖ)
    (z : @H1Cotangent (ToType (A₀.obj.obj X)) (ToType (B₀.obj.obj X)) _ _
      (algebraSections J₀ A₀ B₀ a₀ X)) :
    ((pushforwardConormalMap.{v₀, u₀, v, u, w, z} J₀ J F A B a).val.app X)
        (((naiveCotangentConormalMapOfSquare.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) ψ β hsq).val.app X)
          (sectionsH1Comparison.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀ X z)) =
      sectionsH1Comparison.{v, u, w, max u₀ v₀ z} J A B a (op (F.obj X.unop))
        (@h1CotangentMapOfSquare _ _ _ _ _ _ _ _ (algebraSections J₀ A₀ B₀ a₀ X)
          (algebraSections J A B a (op (F.obj X.unop))) (ψ.hom.app X).hom (β.hom.app X).hom
          (sectionsSquare_pushforward J₀ J F A B A₀ B₀ ψ β a a₀ hsq X) z) := by
  let := algebraSections J₀ A₀ B₀ a₀ X
  let := algebraSections J A B a (op (F.obj X.unop))
  obtain ⟨g, hg⟩ := Extension.Cotangent.mk_surjective z.1
  rw [sectionsH1Comparison_apply.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀ X z g hg.symm]
  rw [sectionsH1Comparison_apply.{v, u, w, max u₀ v₀ z} J A B a (op (F.obj X.unop)) _
    ⟨selfRingHomOfSquare (R' := ToType (A.obj.obj (op (F.obj X.unop))))
        (S' := ToType (B.obj.obj (op (F.obj X.unop)))) (ψ.hom.app X).hom (β.hom.app X).hom g.1,
      selfRingHomOfSquare_mem_ker (R' := ToType (A.obj.obj (op (F.obj X.unop))))
        (S' := ToType (B.obj.obj (op (F.obj X.unop)))) _ _
        (sectionsSquare_pushforward J₀ J F A B A₀ B₀ ψ β a a₀ hsq X) g⟩
    (by
      show cotangentMapOfSquare (R' := ToType (A.obj.obj (op (F.obj X.unop))))
        (S' := ToType (B.obj.obj (op (F.obj X.unop)))) (ψ.hom.app X).hom (β.hom.app X).hom
        (sectionsSquare_pushforward J₀ J F A B A₀ B₀ ψ β a a₀ hsq X) z.1 = _
      rw [← hg]
      exact cotangentMapOfSquare_mk (R' := ToType (A.obj.obj (op (F.obj X.unop))))
        (S' := ToType (B.obj.obj (op (F.obj X.unop)))) (ψ.hom.app X).hom (β.hom.app X).hom
        (sectionsSquare_pushforward J₀ J F A B A₀ B₀ ψ β a a₀ hsq X) g)]
  refine (congrArg ((pushforwardConormalMap.{v₀, u₀, v, u, w, z} J₀ J F A B a).val.app X)
    (conormalSheafMapOfSquare_conormalClass _ _ _ _ _ _ _ _ _ _ _ _ _ _ X _)).trans ?_
  refine (pushforwardConormalMap_conormalClass.{v₀, u₀, v, u, w, z} J₀ J F A B a X _).trans ?_
  congr 2
  exact pushforwardFreeAlgebraMap_freeAlgebraSectionsMap J₀ J F A B A₀ B₀ ψ β X g.1

/-- The chain map `NL_{B₀/A₀} ⟶ F_*NL_{B/A}` of a square is, in each degree, the map of the square
followed by the map of the pushforward. -/
private theorem naiveCotangentComplexPushforwardSquareMap_f_eq (i : ℤ) :
    (naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀ B₀ a₀ ψ β
        hsq).f i =
      (naiveCotangentComplexMapOfSquare.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀ _ _
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) ψ β hsq).f i ≫
      (_root_.SheafOfModules.restrictScalars.{max w u₀ v₀ u v z}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite β)).map
        ((naiveCotangentComplexPushforwardMap.{v₀, u₀, v, u, w, z} J₀ J F A B a).f i) := by
  unfold naiveCotangentComplexPushforwardSquareMap
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, ← Category.assoc]
  exact Category.comp_id _

include hsq in
/-- **The chain map `NL_{B₀/A₀} ⟶ F_*NL_{B/A}` of a square in degree `-1`**: the map of conormal
sheaves of the square, followed by the map of conormal sheaves of the pushforward. -/
theorem naiveCotangentComplexPushforwardSquareMap_f_negOne :
    (naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀ B₀ a₀ ψ β
        hsq).f (-1) =
      eqToHom (naiveCotangentComplex_X_negOne.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀) ≫
        naiveCotangentConormalMapOfSquare.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) ψ β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max w u₀ v₀ u v z}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite β)).map
          (pushforwardConormalMap.{v₀, u₀, v, u, w, z} J₀ J F A B a ≫
            (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
              (pushforwardRingSheafHom J₀ J F B)).map
              (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, max u₀ v₀ z} J A B a).symm)) := by
  rw [naiveCotangentComplexPushforwardSquareMap_f_eq, naiveCotangentComplexMapOfSquare_f_negOne,
    naiveCotangentComplexPushforwardMap_f_negOne]
  simp only [Category.assoc, Functor.map_comp, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rfl

include hsq in
/-- **The chain map `NL_{B₀/A₀} ⟶ F_*NL_{B/A}` of a square in degree `0`**: the map of the
degree `0` terms of the square, followed by the map of degree `0` terms of the pushforward. -/
theorem naiveCotangentComplexPushforwardSquareMap_f_zero :
    (naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀ B₀ a₀ ψ β
        hsq).f 0 =
      eqToHom (naiveCotangentComplex_X_zero.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀) ≫
        naiveCotangentTensorMapOfSquare.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) ψ β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max w u₀ v₀ u v z}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite β)).map
          (conormalPushforwardTensorMap.{v₀, u₀, v, u, w, z} J₀ J F A B a ≫
            (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
              (pushforwardRingSheafHom J₀ J F B)).map
              (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, max u₀ v₀ z} J A B a).symm)) := by
  rw [naiveCotangentComplexPushforwardSquareMap_f_eq, naiveCotangentComplexMapOfSquare_f_zero,
    naiveCotangentComplexPushforwardMap_f_zero]
  simp only [Category.assoc, Functor.map_comp, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rfl

include hsq in
/-- **`β` in degree `-1` on the image of `H₁` of the sections.**  The chain map
`NL_{B₀/A₀} ⟶ F_*NL_{B/A}` of a square carries the image of `z ∈ H₁(L_{B₀(X)/A₀(X)})` in
`NL_{B₀/A₀}^{-1}(X)` to the image in `NL_{B/A}^{-1}(F X)` of its image in `H₁(L_{B(F X)/A(F X)})`
under the map induced by the square of rings on sections. -/
theorem naiveCotangentComplexPushforwardSquareMap_f_negOne_sectionsH1Comparison (X : C₀ᵒᵖ)
    (z : @H1Cotangent (ToType (A₀.obj.obj X)) (ToType (B₀.obj.obj X)) _ _
      (algebraSections J₀ A₀ B₀ a₀ X)) :
    ((naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀ B₀ a₀ ψ β
        hsq).f (-1)).val.app X
        ((eqToHom (naiveCotangentComplex_X_negOne.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀).symm).val.app
          X (sectionsH1Comparison.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀ X z)) =
      (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, max u₀ v₀ z} J A B a).symm).val.app
          (op (F.obj X.unop))
        (sectionsH1Comparison.{v, u, w, max u₀ v₀ z} J A B a (op (F.obj X.unop))
          (@h1CotangentMapOfSquare _ _ _ _ _ _ _ _ (algebraSections J₀ A₀ B₀ a₀ X)
            (algebraSections J A B a (op (F.obj X.unop))) (ψ.hom.app X).hom (β.hom.app X).hom
            (sectionsSquare_pushforward J₀ J F A B A₀ B₀ ψ β a a₀ hsq X) z)) := by
  have h : eqToHom (naiveCotangentComplex_X_negOne.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀).symm ≫
      (naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀ B₀ a₀ ψ β
        hsq).f (-1) =
      naiveCotangentConormalMapOfSquare.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) ψ β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max w u₀ v₀ u v z}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite β)).map
          (pushforwardConormalMap.{v₀, u₀, v, u, w, z} J₀ J F A B a ≫
            (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
              (pushforwardRingSheafHom J₀ J F B)).map
              (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, max u₀ v₀ z} J A B a).symm)) := by
    rw [naiveCotangentComplexPushforwardSquareMap_f_negOne]
    refine Eq.trans (eqToHom_trans_assoc _ _ _) ?_
    rw [eqToHom_refl]
    exact Category.id_comp _
  exact (congrArg (fun g => (g.val.app X) (sectionsH1Comparison.{v₀, u₀, w, max u v z} J₀ A₀ B₀
    a₀ X z)) h).trans (congrArg ((eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, max u₀ v₀ z}
      J A B a).symm).val.app (op (F.obj X.unop)))
    (pushforwardConormalMap_conormalMapOfSquare_sectionsH1Comparison J₀ J F A B A₀ B₀ ψ β a a₀
      hsq X z))

include hsq in
/-- **A map of kernels lifting the degree `-1` map, on the image of `H₁` of the sections.**  Let
`κ : 𝒦₀ ⟶ F_*𝒦` lift the chain map `NL_{B₀/A₀} ⟶ F_*NL_{B/A}` of a square in degree `-1` along
`ι₀ : 𝒦₀ ⟶ NL_{B₀/A₀}^{-1}` and `ι : 𝒦 ⟶ NL_{B/A}^{-1}`.  If `ι₀(m)` is the image of
`z ∈ H₁(L_{B₀(X)/A₀(X)})`, then `ι(κ(m))` is the image of the image of `z` in
`H₁(L_{B(F X)/A(F X)})` under the map induced by the square of rings on sections. -/
theorem app_of_comp_eq_naiveCotangentComplexPushforwardSquareMap_f_negOne
    {K₀ : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B₀)}
    {K : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
    (ι₀ : K₀ ⟶ (naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀).X (-1))
    (ι : K ⟶ (naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a).X (-1))
    (κ : K₀ ⟶ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
      (pushforwardRingHomOfSquare J₀ J F B B₀ β)).obj K)
    (hκ : κ ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
        (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map ι =
      ι₀ ≫ (naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀ B₀ a₀
        ψ β hsq).f (-1))
    (X : C₀ᵒᵖ) (z : @H1Cotangent (ToType (A₀.obj.obj X)) (ToType (B₀.obj.obj X)) _ _
      (algebraSections J₀ A₀ B₀ a₀ X)) (m : ToType (K₀.val.obj X))
    (hm : ι₀.val.app X m =
      (eqToHom (naiveCotangentComplex_X_negOne.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀).symm).val.app
        X (sectionsH1Comparison.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀ X z)) :
    ι.val.app (op (F.obj X.unop)) (κ.val.app X m) =
      (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, max u₀ v₀ z} J A B a).symm).val.app
          (op (F.obj X.unop))
        (sectionsH1Comparison.{v, u, w, max u₀ v₀ z} J A B a (op (F.obj X.unop))
          (@h1CotangentMapOfSquare _ _ _ _ _ _ _ _ (algebraSections J₀ A₀ B₀ a₀ X)
            (algebraSections J A B a (op (F.obj X.unop))) (ψ.hom.app X).hom (β.hom.app X).hom
            (sectionsSquare_pushforward J₀ J F A B A₀ B₀ ψ β a a₀ hsq X) z)) := by
  refine (congrArg (fun g => g.val.app X m) hκ).trans ?_
  show ((naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀ B₀ a₀
    ψ β hsq).f (-1)).val.app X (ι₀.val.app X m) = _
  rw [hm]
  exact naiveCotangentComplexPushforwardSquareMap_f_negOne_sectionsH1Comparison J₀ J F A B A₀ B₀
    ψ β a a₀ hsq X z

end Stacks.SheafOfModules

end
