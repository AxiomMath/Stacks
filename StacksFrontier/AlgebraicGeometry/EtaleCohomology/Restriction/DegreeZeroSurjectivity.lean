module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction

/-!
# Restriction on étale cohomology in degree zero

Let `i : Y ⟶ X` be a morphism of schemes and `F` an abelian sheaf on the small étale site of
`X`. In degree zero the restriction map `H⁰(X, F) → H⁰(Y, i⁻¹F)` of
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` is the map on global sections induced by
the unit `F ⟶ i_* i⁻¹ F` of the adjunction `i⁻¹ ⊣ i_*`. This file records the consequence used
in the computation of `H¹(-, 𝐆_m)` on curves: restriction is surjective in degree zero as soon as
that unit is surjective on sections over a final object; and for `i` étale, as soon as the
restriction map of `F` itself from `X` to `Y` is surjective.

## Main results

* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_zero_of_surjective_unit`.
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_zero_of_etale`: for `i` étale,
  surjectivity of `F(X) → F(Y)` (the restriction of sections of `F` along the morphism of the
  small étale site of `X` given by `i`) gives surjectivity of `H⁰(X, F) → H⁰(Y, i⁻¹F)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u v w

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Restriction is surjective in degree zero when the unit of `i⁻¹ ⊣ i_*` is surjective on
sections over a final object.** A degree-zero class downstairs is a morphism
`𝐙_Y ≅ i⁻¹ 𝐙_X ⟶ i⁻¹ F`, adjoint to a morphism `𝐙_X ⟶ i_* i⁻¹ F`, that is to a section of
`i_* i⁻¹ F` over the final object; lifting that section along the unit lifts the class. -/
theorem surjective_etaleCohomologyRestrictionMap_zero_of_surjective_unit
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) {T : X.Etale}
    (hT : IsTerminal T)
    (h : Function.Surjective
      (((etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app F).hom.app (op T))) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i F 0) := by
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, v} i
  let adjC := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} hT
  let E := AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ)
  let c := (etaleAbelianInverseImageConstantIso.{u, v} i).app E
  let η := adj.unit.app F
  intro y
  let g := Ext.homEquiv₀ y
  let g'' : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E ⟶
      (etaleAbelianDirectImage.{u, v} i).obj ((etaleAbelianInverseImage.{u, v} i).obj F) :=
    adj.homEquiv _ _ (c.hom ≫ g)
  let β := adjC.homEquiv _ _ g''
  obtain ⟨b, hb⟩ := h (β (ULift.up 1))
  let β' : E ⟶ F.obj.obj (op T) := (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm b
  have hβ : β' ≫ ((sheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
      (op T)).map η = β := by
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
    simp only [AddCommGrpCat.uliftZMultiplesAddEquiv_apply, AddCommGrpCat.hom_comp,
      AddMonoidHom.coe_comp, Function.comp_apply]
    show (η.hom.app (op T)) (β' (ULift.up 1)) = β (ULift.up 1)
    rw [← hb]
    congr 1
    exact (AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj.obj (op T))).apply_symm_apply b
  let f := (adjC.homEquiv _ _).symm β'
  have hf : f ≫ η = g'' := by
    apply (adjC.homEquiv _ _).injective
    rwa [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  have hif : (etaleAbelianInverseImage.{u, v} i).map f = c.hom ≫ g := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit]
    show adj.unit.app _ ≫ (etaleAbelianDirectImage.{u, v} i).map
      ((etaleAbelianInverseImage.{u, v} i).map f) = g''
    rw [← hf]
    exact (adj.unit.naturality f).symm
  refine ⟨Ext.mk₀ f, ?_⟩
  rw [etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  show Ext.mk₀ (c.inv ≫ (etaleAbelianInverseImage.{u, v} i).map f) = y
  rw [hif, Iso.inv_hom_id_assoc]
  exact Ext.mk₀_homEquiv₀_apply y

/-- The unit of `j⁻¹ ⊣ j_*` for the restriction along an étale morphism, on sections: it is the
restriction map of `F` along the counit `j(V ×_X U) ⟶ V` of composition with `j` against base
change along `j`. -/
theorem etaleRestrictionAbelianDirectImageAdj_unit_app {U : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (V : X.Etale) :
    ((etaleRestrictionAbelianDirectImageAdj.{u, v} j).unit.app F).hom.app (op V) =
      F.obj.map ((smallEtaleComposeBaseChangeAdj j).counit.app V).op :=
  rfl

/-- **Restriction along an étale morphism is surjective in degree zero as soon as it is on
sections.** Let `j : U ⟶ X` be étale, `T` a final object of `X_étale` and `F` an abelian sheaf
on `X_étale`. If the restriction of sections `F(T) → F(j(U ×_X T))` is surjective, then so is
`H⁰(X, F) → H⁰(U, j⁻¹F)`. -/
theorem surjective_etaleCohomologyRestrictionMap_zero_of_etale {U : Scheme.{u}} (j : U ⟶ X)
    [Etale j] [HasExt.{w} (Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) {T : X.Etale}
    (hT : IsTerminal T)
    (h : Function.Surjective (F.obj.map
      (hT.from ((smallEtaleCompose j).obj ((smallEtaleBaseChange j).obj T))).op)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} j F 0) := by
  refine surjective_etaleCohomologyRestrictionMap_zero_of_surjective_unit j F hT ?_
  have key : (etaleAbelianInverseImageDirectImageAdj.{u, v} j).unit.app F ≫
      (etaleAbelianDirectImage.{u, v} j).map
        ((etaleAbelianInverseImageRestrictionIso.{u, v} j).hom.app F) =
      (etaleRestrictionAbelianDirectImageAdj.{u, v} j).unit.app F :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ F
  have hunit : (etaleAbelianInverseImageDirectImageAdj.{u, v} j).unit.app F =
      (etaleRestrictionAbelianDirectImageAdj.{u, v} j).unit.app F ≫
        (etaleAbelianDirectImage.{u, v} j).map
          ((etaleAbelianInverseImageRestrictionIso.{u, v} j).inv.app F) := by
    rw [← key, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  have hcomp : ((etaleRestrictionAbelianDirectImageAdj.{u, v} j).unit.app F ≫
        (etaleAbelianDirectImage.{u, v} j).map
          ((etaleAbelianInverseImageRestrictionIso.{u, v} j).inv.app F)).hom.app (op T) =
      ((etaleRestrictionAbelianDirectImageAdj.{u, v} j).unit.app F).hom.app (op T) ≫
        ((etaleAbelianDirectImage.{u, v} j).map
          ((etaleAbelianInverseImageRestrictionIso.{u, v} j).inv.app F)).hom.app (op T) := rfl
  rw [hunit, hcomp]
  have hc : (smallEtaleComposeBaseChangeAdj j).counit.app T =
      hT.from ((smallEtaleCompose j).obj ((smallEtaleBaseChange j).obj T)) := hT.hom_ext _ _
  intro z
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (((etaleAbelianDirectImage.{u, v} j).map
      ((etaleAbelianInverseImageRestrictionIso.{u, v} j).inv.app F)).hom.app (op T))).2 z
  rw [etaleRestrictionAbelianDirectImageAdj_unit_app, hc]
  obtain ⟨x, rfl⟩ := h y
  exact ⟨x, ConcreteCategory.comp_apply _ _ x⟩

end Stacks.EtaleCohomology

end
