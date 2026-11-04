module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence
public import StacksFrontier.CategoryTheory.Functor.FlipObjOfUncurryIso

/-!
# A tensor–internal-hom adjunction transported along an equivalence

Let `𝔢 : D ≌ M` be an equivalence of categories, `T_M` a bifunctor on `M` with, for every `Q`, an
adjunction `T_M(-, Q) ⊣ H_M(Q, -)`, and `T_D` a bifunctor on `D` identified with `T_M` through
`𝔢` by an isomorphism `τ : T_D ⋙ 𝔢 ≅ (𝔢 × 𝔢) ⋙ T_M` of uncurried bifunctors. Then

`H_D(P, C) = 𝔢⁻¹ H_M(𝔢 P, 𝔢 C)`

carries the adjunctions `T_D(-, P) ⊣ H_D(P, -)` obtained by composing the adjunction of `M` with
the two adjunctions of the equivalence and transporting along `τ`. This is how the derived
internal Hom of an algebraic space is made out of the one of its equi-universe model
(`AlgebraicGeometry.Space.smallEtaleDerivedTensorSheafHomAdjunction`, Stacks 08J8).

This file proves that the transported bijections are **dinatural in the internal-hom variable**
as soon as those of `M` are: postcomposing `ψ : A ⟶ H_D(P, C)` with `H_D(φ, C)` for
`φ : P' ⟶ P` corresponds to precomposing the transpose of `ψ` with `T_D(A, φ)`. This is the
clause of Stacks 08J8 that makes the comparison map of Stacks 08I3 natural in the perfect variable.

## Main definitions

* `CategoryTheory.TransportedTensorHom.sheafHom`: `H_D`.
* `CategoryTheory.TransportedTensorHom.rightIso`: `T_D(-, P) ≅ 𝔢⁻¹ T_M(𝔢 -, 𝔢 P)`.
* `CategoryTheory.TransportedTensorHom.adjunction`: the transported adjunction.

## Main results

* `CategoryTheory.TransportedTensorHom.adjunction_homEquiv_symm`: the transpose of `ψ` under the
  transported adjunction, in terms of the transpose under the adjunction of `M`.
* `CategoryTheory.TransportedTensorHom.adjunction_homEquiv_symm_dinatural`: dinaturality.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.TransportedTensorHom

variable {D M : Type*} [Category D] [Category M] (𝔢 : D ≌ M)
  (TD : D ⥤ D ⥤ D) (TM : M ⥤ M ⥤ M) (HM : Mᵒᵖ ⥤ M ⥤ M)
  (τ : Functor.uncurry.obj TD ⋙ 𝔢.functor ≅
    𝔢.functor.prod 𝔢.functor ⋙ Functor.uncurry.obj TM)
  (aM : ∀ Q : M, TM.flip.obj Q ⊣ HM.obj (op Q))

/-- The internal hom of `D` read through the equivalence: `H_D(P, C) = 𝔢⁻¹ H_M(𝔢 P, 𝔢 C)`. -/
abbrev sheafHom : Dᵒᵖ ⥤ D ⥤ D :=
  𝔢.functor.op ⋙ HM ⋙ (Functor.whiskeringLeft _ _ _).obj 𝔢.functor ⋙
    (Functor.whiskeringRight _ _ _).obj 𝔢.inverse

/-- Tensoring with `P` on `D` is tensoring with `𝔢 P` on `M`, read through the equivalence. -/
abbrev rightIso (P : D) :
    TD.flip.obj P ≅ 𝔢.functor ⋙ TM.flip.obj (𝔢.functor.obj P) ⋙ 𝔢.inverse :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ 𝔢.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.flipObjIsoOfUncurryIso τ P) _ ≪≫
    Functor.associator _ _ _

/-- The transported adjunction `T_D(-, P) ⊣ H_D(P, -)`. -/
abbrev adjunction (P : D) : TD.flip.obj P ⊣ (sheafHom 𝔢 HM).obj (op P) :=
  ((𝔢.toAdjunction.comp (aM (𝔢.functor.obj P))).comp 𝔢.symm.toAdjunction).ofNatIsoLeft
    (rightIso 𝔢 TD TM τ P).symm

/-- The component of `rightIso` at `A`: the unit of the equivalence followed by `𝔢⁻¹ τ`. -/
theorem rightIso_hom_app (P A : D) :
    (rightIso 𝔢 TD TM τ P).hom.app A =
      𝔢.unit.app ((TD.obj A).obj P) ≫ 𝔢.inverse.map (τ.hom.app (A, P)) := by
  simp only [rightIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_inv_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id]
  rfl

/-- `rightIso` is natural in the tensor factor `P`. -/
theorem rightIso_hom_app_naturality (A : D) {P P' : D} (φ : P' ⟶ P) :
    (TD.obj A).map φ ≫ (rightIso 𝔢 TD TM τ P).hom.app A =
      (rightIso 𝔢 TD TM τ P').hom.app A ≫
        𝔢.inverse.map ((TM.obj (𝔢.functor.obj A)).map (𝔢.functor.map φ)) := by
  rw [rightIso_hom_app, rightIso_hom_app]
  have hτ := τ.hom.naturality (X := (A, P')) (Y := (A, P)) (Prod.mkHom (𝟙 A) φ)
  simp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.comp_map,
    Functor.uncurry_obj_map, Functor.prod_obj, Functor.prod_map, Prod.mkHom,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at hτ
  have hu := 𝔢.unit.naturality ((TD.obj A).map φ)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hu
  rw [← Category.assoc, hu, Category.assoc, Category.assoc]
  congr 1
  simp only [Functor.comp_obj, ← Functor.map_comp, hτ]

/-- **The transpose under the transported adjunction**, in terms of the transpose under the
adjunction of `M`. -/
theorem adjunction_homEquiv_symm (P A C : D) (ψ : A ⟶ ((sheafHom 𝔢 HM).obj (op P)).obj C) :
    ((adjunction 𝔢 TD TM HM τ aM P).homEquiv A C).symm ψ =
      (rightIso 𝔢 TD TM τ P).hom.app A ≫
        𝔢.inverse.map (((aM (𝔢.functor.obj P)).homEquiv _ _).symm
          (𝔢.functor.map ψ ≫
            𝔢.counit.app ((HM.obj (op (𝔢.functor.obj P))).obj (𝔢.functor.obj C)))) ≫
          𝔢.unitInv.app C := by
  rw [Adjunction.homEquiv_counit, Adjunction.ofNatIsoLeft_counit]
  simp only [Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, (rightIso 𝔢 TD TM τ P).hom.naturality ψ, Category.assoc]
  congr 1
  simp only [Adjunction.comp_counit_app, Adjunction.homEquiv_counit, Functor.comp_map,
    Functor.comp_obj, Equivalence.symm_counit, Equivalence.toAdjunction, Functor.map_comp,
    Category.assoc]
  rfl

/-- **The transported bijections are dinatural in the internal-hom variable**, as soon as those of
`M` are. For `φ : P' ⟶ P` and `ψ : A ⟶ H_D(P, C)`, the transpose of `ψ ≫ H_D(φ, C)` is
`T_D(A, φ)` followed by the transpose of `ψ`. -/
theorem adjunction_homEquiv_symm_dinatural
    (hM : ∀ (A C : M) {Q Q' : M} (v : Q' ⟶ Q) (ψ : A ⟶ (HM.obj (op Q)).obj C),
      ((aM Q').homEquiv A C).symm (ψ ≫ (HM.map v.op).app C) =
        (TM.obj A).map v ≫ ((aM Q).homEquiv A C).symm ψ)
    (A C : D) {P P' : D} (φ : P' ⟶ P) (ψ : A ⟶ ((sheafHom 𝔢 HM).obj (op P)).obj C) :
    ((adjunction 𝔢 TD TM HM τ aM P').homEquiv A C).symm
        (ψ ≫ ((sheafHom 𝔢 HM).map φ.op).app C) =
      (TD.obj A).map φ ≫ ((adjunction 𝔢 TD TM HM τ aM P).homEquiv A C).symm ψ := by
  rw [adjunction_homEquiv_symm, adjunction_homEquiv_symm]
  have hε : 𝔢.functor.map (ψ ≫ ((sheafHom 𝔢 HM).map φ.op).app C) ≫
        𝔢.counit.app ((HM.obj (op (𝔢.functor.obj P'))).obj (𝔢.functor.obj C)) =
      (𝔢.functor.map ψ ≫ 𝔢.counit.app ((HM.obj (op (𝔢.functor.obj P))).obj (𝔢.functor.obj C))) ≫
        (HM.map (𝔢.functor.map φ).op).app (𝔢.functor.obj C) := by
    have h := 𝔢.counit.naturality ((HM.map (𝔢.functor.map φ).op).app (𝔢.functor.obj C))
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at h
    rw [Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (𝔢.functor.map ψ ≫ ·) h
  rw [hε, hM, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (rightIso_hom_app_naturality 𝔢 TD TM τ A φ)]

end CategoryTheory.TransportedTensorHom

end
