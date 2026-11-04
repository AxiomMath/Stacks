module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf

/-!
# The evaluation formula for the normal sheaf of an effective Cartier divisor

Let `D ⊆ X` be an effective Cartier divisor. The normal sheaf of `D` is identified with the
restriction `𝒪_X(D)|_D` of its associated invertible sheaf, and the identification is
determined by its value on sections: a functional `φ` on the ideal sheaf `ℐ_D`, restricted to
`D` and read on the conormal sheaf through the identification, sends the restriction of a section
`x` of `ℐ_D` to the restriction of `φ(x)`.

## Main results

* `Stacks.SheafOfModules.tensorIsoUnit_hom_toSheafify_isoOfTensorIsoUnit_inv`: the canonical
  identification `Stacks.SheafOfModules.isoOfTensorIsoUnit` of two tensor inverses of an
  invertible module sheaf carries one trivializing pairing to the other, on sections.
* `Stacks.SheafOfModules.evaluation_toSheafify`: the evaluation pairing `F^∨ ⊗ F ⟶ 𝒪`, on the
  sheafification-unit image of a pure tensor, is `Stacks.SheafOfModules.evalSection`.
* `Stacks.RingedSpace.tensorIsoUnitPullback_hom_toSheafify`: a pulled-back trivializing pairing,
  on the tensor of two pullback-unit sections, is the structure map of `f` applied to the
  original pairing.
* `Stacks.Divisors.evalSection_dualPullbackIsoOfPullbackStalkFormula_inv`: the identification of
  the dual of a pullback with the pullback of the dual is compatible with evaluation.
* `Stacks.Divisors.normalSheafIsoInvertibleSheaf_eval`: the inverse of the normal-sheaf
  isomorphism sends a restricted functional `φ`, evaluated on the class of a section `x` of the
  ideal sheaf, to the restriction of `φ(x)`.

## References

* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite RingedSpaceModuleAdjunction
  TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)
open scoped TensorProduct

universe v u

namespace Stacks.SheafOfModules

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

private theorem functor_map_unit_conj {C₁ : Type*} [Category C₁] {D₁ : Type*} [Category D₁]
    (e : C₁ ≌ D₁) {A B : C₁} (g : e.functor.obj A ⟶ e.functor.obj B) :
    e.functor.map ((e.unitIso.app A).hom ≫ e.inverse.map g ≫ (e.unitIso.app B).inv) = g := by
  simp [Equivalence.fun_inv_map]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))

/-- An equation between morphisms of sheaves of modules, read on sections. -/
private theorem hom_val_app_congr {R : Sheaf J RingCat.{max u v}}
    {M N : SheafOfModules.{max u v} R} {φ ψ : M ⟶ N} (h : φ = ψ) (U : Cᵒᵖ) (x : M.val.obj U) :
    PresheafOfModules.Hom.app φ.val U x = PresheafOfModules.Hom.app ψ.val U x := by rw [h]

/-- An isomorphism of sheaves of modules, applied to a section already in the image of its
inverse, returns that section. -/
theorem app_hom_app_inv {F G : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (i : F ≅ G) (U : Cᵒᵖ) (q : G.val.obj U) :
    PresheafOfModules.Hom.app i.hom.val U (PresheafOfModules.Hom.app i.inv.val U q) = q :=
  hom_val_app_congr i.inv_hom_id U q

/-- Transporting the dual along an isomorphism is precomposition: a functional on `F'`, read on
`F` through `dualSheafIso`, evaluates a section of `F` on its image in `F'`. -/
theorem dualSheafIso_inv_evalSection
    {F F' : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)} (e : F ≅ F')
    (U : Cᵒᵖ) (ψ : (dualSheaf 𝒪 h𝒪 F').val.obj U) (y : F.val.obj U) :
    evalSection 𝒪 F.val (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val U
        (PresheafOfModules.Hom.app (dualSheafIso 𝒪 h𝒪 e).inv.val U ψ) y =
      evalSection 𝒪 F'.val (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val U ψ
        (PresheafOfModules.Hom.app e.hom.val U y) := rfl

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- The evaluation pairing, on the sheafification-unit image of a pure tensor, is
`evalSection`. -/
theorem evaluation_toSheafify
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      (U : Cᵒᵖ)
    (lam : (dualSheaf 𝒪 h𝒪 F).val.obj U) (x : F.val.obj U) :
    PresheafOfModules.Hom.app (evaluation 𝒪 h𝒪 F).val U
        (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
            ((dualSheaf 𝒪 h𝒪 F).val ⊗ F.val)) U
          (lam ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] x)) =
      evalSection 𝒪 F.val (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val U lam x := by
  have key : Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
        ((dualSheaf 𝒪 h𝒪 F).val ⊗ F.val) ≫
        (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).map
              (evaluation 𝒪 h𝒪 F) =
      evaluationPresheaf 𝒪 h𝒪 F :=
    PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm
      (M := (dualSheaf 𝒪 h𝒪 F).val ⊗ F.val)
      (N := SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)
      (evaluationPresheaf 𝒪 h𝒪 F)
  exact (PresheafOfModules.hom_congr_apply key U _).trans (evaluationPresheaf_tmul 𝒪 h𝒪 F U lam x)

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- The braiding of the tensor product sheaf, on the sheafification-unit image of a pure
tensor: it swaps the two factors. -/
theorem tensorSheafBraiding_hom_toSheafify
    (M N : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    PresheafOfModules.Hom.app (tensorSheafBraiding 𝒪 h𝒪 M N).hom.val U
        (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
          (M.val ⊗ N.val)) U
          (m ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] n)) =
      PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (N.val ⊗
        M.val)) U
        (n ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] m) :=
  (PresheafOfModules.unit_naturality_apply (α := 𝟙
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)
    (β_ M.val N.val).hom U
    (m ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] n)).trans rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- Tensoring a morphism on the left by `L`, on the sheafification-unit image of a pure
tensor. -/
theorem toSheafify_tensorLeftFunctor_map
    (L A B : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) (g : A ⟶ B)
    (U : Cᵒᵖ) (l : L.val.obj U) (a : A.val.obj U) :
    PresheafOfModules.Hom.app
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
          (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).map g).val U
        (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
          (L.val ⊗ A.val)) U
          (l ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] a)) =
      PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (L.val ⊗
        B.val)) U
        (l ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U]
          PresheafOfModules.Hom.app g.val U a) :=
  (PresheafOfModules.unit_naturality_apply (α := 𝟙
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)
    (L.val ◁ (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)).map g) U
    (l ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] a)).trans rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- The identification of two tensor inverses of `L` is the one induced by the autoequivalence
`· ⊗ L`: tensoring it with `L` conjugates the two trivializing pairings into each other. -/
theorem tensorLeftFunctor_map_isoOfTensorIsoUnit_inv
    (L A B : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪))
    [IsInvertible 𝒪 h𝒪 L]
    (hA : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
      (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (A)).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (hB : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
      (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (B)).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
          (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).map
        (isoOfTensorIsoUnit 𝒪 h𝒪 L A B hA hB).inv =
      (tensorSheafBraiding 𝒪 h𝒪 L B ≪≫ hB).hom ≫
        (tensorSheafBraiding 𝒪 h𝒪 L A ≪≫ hA).inv := by
  have hinv : (isoOfTensorIsoUnit 𝒪 h𝒪 L A B hA hB).inv =
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
          (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).asEquivalence.unitIso.app B).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
            (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).asEquivalence.inverse.map
            ((tensorSheafBraiding 𝒪 h𝒪 L B ≪≫ hB).hom ≫
              (tensorSheafBraiding 𝒪 h𝒪 L A ≪≫ hA).inv) ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
            (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).asEquivalence.unitIso.app A).inv :=
    Category.assoc _ _ _
  rw [hinv]
  exact functor_map_unit_conj ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
      (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).asEquivalence _

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- The canonical identification `A ≅ B` of two tensor inverses of an invertible `L` carries the
pairing of `B` with `L` to the pairing of `A` with `L`, section by section. -/
theorem tensorIsoUnit_hom_toSheafify_isoOfTensorIsoUnit_inv
    (L A B : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪))
    [IsInvertible 𝒪 h𝒪 L]
    (hA : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
      (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (A)).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (hB : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
      (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (B)).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (U : Cᵒᵖ) (b : B.val.obj U) (l : L.val.obj U) :
    PresheafOfModules.Hom.app hB.hom.val U
        (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
          (B.val ⊗ L.val)) U
          (b ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] l)) =
      PresheafOfModules.Hom.app hA.hom.val U
        (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
          (A.val ⊗ L.val)) U
          (PresheafOfModules.Hom.app (isoOfTensorIsoUnit 𝒪 h𝒪 L A B hA hB).inv.val U b
            ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] l)) := by
  have h := hom_val_app_congr
    (tensorLeftFunctor_map_isoOfTensorIsoUnit_inv 𝒪 h𝒪 L A B hA hB) U
    (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (L.val ⊗
      B.val)) U
      (l ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] b))
  rw [toSheafify_tensorLeftFunctor_map] at h
  have h' : PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
    (L.val ⊗ A.val)) U
        (l ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U]
          PresheafOfModules.Hom.app (isoOfTensorIsoUnit 𝒪 h𝒪 L A B hA hB).inv.val U b) =
      PresheafOfModules.Hom.app (tensorSheafBraiding 𝒪 h𝒪 L A ≪≫ hA).inv.val U
        (PresheafOfModules.Hom.app (tensorSheafBraiding 𝒪 h𝒪 L B ≪≫ hB).hom.val U
          (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
            (L.val ⊗ B.val)) U
            (l ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] b)))
              := h
  have h2 := (congrArg
    (PresheafOfModules.Hom.app (tensorSheafBraiding 𝒪 h𝒪 L A ≪≫ hA).hom.val U) h').trans
      (app_hom_app_inv 𝒪 h𝒪 (tensorSheafBraiding 𝒪 h𝒪 L A ≪≫ hA) U
        (PresheafOfModules.Hom.app (tensorSheafBraiding 𝒪 h𝒪 L B ≪≫ hB).hom.val U
          (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
            (L.val ⊗ B.val)) U
            (l ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] b))))
  have h3 : PresheafOfModules.Hom.app hA.hom.val U
        (PresheafOfModules.Hom.app (tensorSheafBraiding 𝒪 h𝒪 L A).hom.val U
          (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
            (L.val ⊗ A.val)) U
            (l ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U]
              PresheafOfModules.Hom.app
                (isoOfTensorIsoUnit 𝒪 h𝒪 L A B hA hB).inv.val U b))) =
      PresheafOfModules.Hom.app hB.hom.val U
        (PresheafOfModules.Hom.app (tensorSheafBraiding 𝒪 h𝒪 L B).hom.val U
          (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
            (L.val ⊗ B.val)) U
            (l ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] b)))
              := h2
  refine Eq.trans ?_ (h3.symm.trans (congrArg
    (PresheafOfModules.Hom.app hA.hom.val U)
    (tensorSheafBraiding_hom_toSheafify 𝒪 h𝒪 L A U l
      (PresheafOfModules.Hom.app (isoOfTensorIsoUnit 𝒪 h𝒪 L A B hA hB).inv.val U b))))
  exact (congrArg (PresheafOfModules.Hom.app hB.hom.val U)
    (tensorSheafBraiding_hom_toSheafify 𝒪 h𝒪 L B U l b)).symm

end Sheafification

end Stacks.SheafOfModules

namespace Stacks.RingedSpace

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The comparison morphism `comparison f A B`, on the sheafification-unit image of the tensor of
two pullback-unit sections, is the tensor of the two sections. -/
theorem comparison_val_app_pullbackUnit
    (A B : SheafOfModules.{u} (structureSheafRing Y)) (U : (Opens Y.carrier)ᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) :
    PresheafOfModules.Hom.app (comparison f A B).val ((opensMap f).op.obj U)
        (((modulePullbackPushforwardAdjunction f).unit.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
            Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
            ((structureSheafRing Y).property)⟩).obj (A)).obj (B)))).val.app U
            (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify
              Y.sheaf.obj
              (structureSheafRing Y).property (A.val ⊗ B.val)) U
              (a ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
                Y.sheaf.obj).obj U] b))) =
      PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify X.sheaf.obj
        (structureSheafRing X).property
          (((modulePullback f).obj A).val ⊗ ((modulePullback f).obj B).val))
          ((opensMap f).op.obj U)
        ((((modulePullbackPushforwardAdjunction f).unit.app A).val.app U a)
          ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.sheaf.obj).obj
            ((opensMap f).op.obj U)]
          (((modulePullbackPushforwardAdjunction f).unit.app B).val.app U b)) :=
  comparisonNatTrans_homEquiv_unit_tmul f A B U a b

/-- The identification of the pullback of the structure sheaf with the structure sheaf, on the
pullback-unit image of a section: it is the structure map of `f`. -/
theorem pullbackObjUnitToUnit_val_app_pullbackUnit
    [(_root_.SheafOfModules.pushforward.{u} (structureSheafHom f)).IsRightAdjoint]
    (U : (Opens Y.carrier)ᵒᵖ)
    (r : (_root_.SheafOfModules.unit (structureSheafRing Y)).val.obj U) :
    PresheafOfModules.Hom.app
        (_root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)).val
        ((opensMap f).op.obj U)
        (((modulePullbackPushforwardAdjunction f).unit.app
          (_root_.SheafOfModules.unit (structureSheafRing Y))).val.app U r) =
      ((structureSheafHom f).hom.app U) r :=
  Stacks.SheafOfModules.hom_val_app_congr
    (_root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (structureSheafHom f)) U r

/-- The pulled-back trivializing pairing, on the tensor of two pullback-unit sections, is the
structure map of `f` applied to the original pairing. -/
theorem tensorIsoUnitPullback_hom_toSheafify
    (A B : SheafOfModules.{u} (structureSheafRing Y))
    (hAB : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
      ((structureSheafRing Y).property)⟩).obj (A)).obj (B)) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        Y.sheaf.obj (structureSheafRing Y).property))
    (hcomp : IsIso (comparison f A B))
    (U : (Opens Y.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    PresheafOfModules.Hom.app (tensorIsoUnitPullback f A B hAB hcomp).hom.val
        ((opensMap f).op.obj U)
        (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify
          X.sheaf.obj (structureSheafRing X).property
            (((modulePullback f).obj A).val ⊗ ((modulePullback f).obj B).val))
            ((opensMap f).op.obj U)
          ((((modulePullbackPushforwardAdjunction f).unit.app A).val.app U a)
            ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.sheaf.obj).obj
              ((opensMap f).op.obj U)]
            (((modulePullbackPushforwardAdjunction f).unit.app B).val.app U b))) =
      ((structureSheafHom f).hom.app U)
        (PresheafOfModules.Hom.app hAB.hom.val U
          (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify
            Y.sheaf.obj
            (structureSheafRing Y).property (A.val ⊗ B.val)) U
            (a ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Y.sheaf.obj).obj
              U] b))) := by
  let _i₁ : (_root_.SheafOfModules.pushforward.{u} (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  let _i₂ : (modulePullback f).IsLeftAdjoint :=
    ⟨_, ⟨modulePullbackPushforwardAdjunction f⟩⟩
  let _i₃ : (Opens.map f.hom.base).Final := CategoryTheory.final_of_representablyFlat _
  have _i₄ := hcomp
  have hd : ∀ Z : ((modulePullback f).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _
        (Y.sheaf.obj) (forget₂ CommRingCat RingCat) ((structureSheafRing Y).property)⟩).obj (A)).obj
        (B)))).val.obj
        ((opensMap f).op.obj U),
      PresheafOfModules.Hom.app (tensorIsoUnitPullback f A B hAB hcomp).hom.val
          ((opensMap f).op.obj U)
          (PresheafOfModules.Hom.app (comparison f A B).val ((opensMap f).op.obj U) Z) =
        PresheafOfModules.Hom.app
          (_root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)).val
          ((opensMap f).op.obj U)
          (PresheafOfModules.Hom.app ((modulePullback f).map hAB.hom).val
            ((opensMap f).op.obj U)
            (PresheafOfModules.Hom.app (inv (comparison f A B)).val ((opensMap f).op.obj U)
              (PresheafOfModules.Hom.app (comparison f A B).val
                ((opensMap f).op.obj U) Z))) := fun _ => rfl
  have hci : ∀ Z : ((modulePullback f).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _
        (Y.sheaf.obj) (forget₂ CommRingCat RingCat) ((structureSheafRing Y).property)⟩).obj (A)).obj
        (B)))).val.obj
        ((opensMap f).op.obj U),
      PresheafOfModules.Hom.app (inv (comparison f A B)).val ((opensMap f).op.obj U)
          (PresheafOfModules.Hom.app (comparison f A B).val ((opensMap f).op.obj U) Z) = Z :=
    fun Z => Stacks.SheafOfModules.hom_val_app_congr (IsIso.hom_inv_id (comparison f A B))
      ((opensMap f).op.obj U) Z
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app
      (tensorIsoUnitPullback f A B hAB hcomp).hom.val ((opensMap f).op.obj U))
    (comparison_val_app_pullbackUnit f A B U a b).symm) ?_
  refine Eq.trans (hd _) ?_
  refine Eq.trans (congrArg (fun t => PresheafOfModules.Hom.app
      (_root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)).val
        ((opensMap f).op.obj U)
      (PresheafOfModules.Hom.app ((modulePullback f).map hAB.hom).val
        ((opensMap f).op.obj U) t)) (hci _)) ?_
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app
      (_root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)).val
      ((opensMap f).op.obj U))
    (pullbackUnit_naturality f hAB.hom U
      (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify Y.sheaf.obj
        (structureSheafRing Y).property (A.val ⊗ B.val)) U
        (a ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Y.sheaf.obj).obj U]
          b)))) ?_
  exact pullbackObjUnitToUnit_val_app_pullbackUnit f U _

end Stacks.RingedSpace

namespace Stacks.Divisors

open Stacks.SheafOfModules

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

section RingedSpaceLevel

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The functional on `f^* L` that `dualPullbackIso` obtains from a section of `f^* (L^∨)`
evaluates as the trivializing pairing does. -/
theorem evalSection_dualPullbackIso_inv
    [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    (L : SheafOfModules.{u} (structureSheafRing Y))
    (hpp : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
      ((structureSheafRing X).property)⟩).obj (((modulePullback f).obj
          (dualSheaf Y.sheaf.obj (structureSheafRing Y).property L)))).obj (((modulePullback f).obj
            L))) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        X.sheaf.obj (structureSheafRing X).property))
    (V : (Opens X.carrier)ᵒᵖ)
    (b : ((modulePullback f).obj
      (dualSheaf Y.sheaf.obj (structureSheafRing Y).property L)).val.obj V)
    (l : ((modulePullback f).obj L).val.obj V) :
    PresheafOfModules.Hom.app hpp.hom.val V
        (PresheafOfModules.Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify
          X.sheaf.obj (structureSheafRing X).property
            (((modulePullback f).obj
              (dualSheaf Y.sheaf.obj (structureSheafRing Y).property L)).val ⊗
              ((modulePullback f).obj L).val)) V
          (b ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.sheaf.obj).obj
            V] l)) =
      evalSection X.sheaf.obj ((modulePullback f).obj L).val
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          X.sheaf.obj
          (structureSheafRing X).property)).val V
        (PresheafOfModules.Hom.app (dualPullbackIso f L hpp).inv.val V b) l := by
  have hinv : IsInvertible X.sheaf.obj (structureSheafRing X).property ((modulePullback f).obj L) :=
    isInvertible_of_tensorIsoUnit _ _ _ _ hpp
  have hinv' : IsInvertible X.presheaf (structureSheafRing X).property
      ((modulePullback f).obj L) := hinv
  exact (tensorIsoUnit_hom_toSheafify_isoOfTensorIsoUnit_inv
    X.sheaf.obj (structureSheafRing X).property ((modulePullback f).obj L)
    (dualSheaf X.sheaf.obj (structureSheafRing X).property ((modulePullback f).obj L))
    ((modulePullback f).obj (dualSheaf Y.sheaf.obj (structureSheafRing Y).property L))
    (evaluationIsoOfIsInvertible (X := X) ((modulePullback f).obj L)) hpp V b l).trans
    (evaluation_toSheafify X.sheaf.obj (structureSheafRing X).property
      ((modulePullback f).obj L) V _ l)


/-- The identification of the dual of a pullback with the pullback of the dual is compatible with
evaluation: the functional it produces from the restriction of `φ`, evaluated on the restriction
of `x`, is the structure map of `f` applied to `φ(x)`. -/
theorem evalSection_dualPullbackIsoOfPullbackStalkFormula_inv
    [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    [∀ y : Y.carrier, IsLocalRing (ringStalk Y y)]
    (hf : Stacks.RingedSpace.PullbackStalkFormula f)
    (L : SheafOfModules.{u} (structureSheafRing Y))
    [IsInvertible Y.sheaf.obj (structureSheafRing Y).property L]
    (U : (Opens Y.carrier)ᵒᵖ)
    (φ : (dualSheaf Y.sheaf.obj (structureSheafRing Y).property L).val.obj U)
    (x : L.val.obj U) :
    evalSection X.sheaf.obj ((modulePullback f).obj L).val
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          X.sheaf.obj
          (structureSheafRing X).property)).val ((opensMap f).op.obj U)
        (PresheafOfModules.Hom.app
          (dualPullbackIsoOfPullbackStalkFormula f hf L).inv.val ((opensMap f).op.obj U)
          (((modulePullbackPushforwardAdjunction f).unit.app
            (dualSheaf Y.sheaf.obj (structureSheafRing Y).property L)).val.app U φ))
        (((modulePullbackPushforwardAdjunction f).unit.app L).val.app U x) =
      ((structureSheafHom f).hom.app U)
        (evalSection Y.sheaf.obj L.val
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
            Y.sheaf.obj
            (structureSheafRing Y).property)).val U φ x) := by
  have hL : IsInvertible Y.presheaf (structureSheafRing Y).property L := ‹_›
  refine Eq.trans (evalSection_dualPullbackIso_inv f L
    (Stacks.RingedSpace.tensorIsoUnitPullback f
      (dualSheaf Y.sheaf.obj (structureSheafRing Y).property L) L
      (evaluationIsoOfIsInvertible (X := Y) L)
      (Stacks.RingedSpace.isIso_comparison_of_pullbackStalkFormula f hf _ _))
    ((opensMap f).op.obj U) _ _).symm ?_
  refine Eq.trans (Stacks.RingedSpace.tensorIsoUnitPullback_hom_toSheafify f
    (dualSheaf Y.sheaf.obj (structureSheafRing Y).property L) L
    (evaluationIsoOfIsInvertible (X := Y) L)
    (Stacks.RingedSpace.isIso_comparison_of_pullbackStalkFormula f hf _ _) U φ x) ?_
  exact congrArg ((structureSheafHom f).hom.app U)
    (evaluation_toSheafify Y.sheaf.obj (structureSheafRing Y).property L U φ x)

end RingedSpaceLevel

section Card

/-- Let `φ` be a section of `𝒪_X(D) = ℐ_D^∨` over `U` and `x` a section of `𝒪_X(-D) = ℐ_D` over
`U`, both carried to `D` by the unit of `f^* ⊣ f_*` for the closed immersion `f` of `D`. The
functional which `Stacks.Divisors.normalSheafIsoInvertibleSheaf` produces from `φ` on the
conormal sheaf takes the image of `x` to the restriction of `φ(x)`. -/
@[stacks 0B3P "canonical evaluation"]
theorem normalSheafIsoInvertibleSheaf_eval {X : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (U : Opens X)
    (φ : (dualSheaf X.sheaf.obj (structureSheafRing X.toRingedSpace).property
      (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom)).val.obj (op U))
    (x : (Stacks.ClosedImmersion.idealSheaf
      D.subschemeι.toLRSHom.toShHom).val.obj (op U)) :
    evalSection D.subscheme.sheaf.obj
        ((modulePullback D.subschemeι.liftCoborder.toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.idealSheaf
            D.subschemeι.liftCoborder.toLRSHom.toShHom)).val
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          D.subscheme.sheaf.obj
          (structureSheafRing D.subscheme.toRingedSpace).property)).val
        (op ((opensMap D.subschemeι.toLRSHom.toShHom).obj U))
        ((normalSheafIsoInvertibleSheaf D).inv.val.app
          (op ((opensMap D.subschemeι.toLRSHom.toShHom).obj U))
          (((modulePullbackPushforwardAdjunction
              D.subschemeι.toLRSHom.toShHom).unit.app
            (dualSheaf X.sheaf.obj (structureSheafRing X.toRingedSpace).property
              (Stacks.ClosedImmersion.idealSheaf
                D.subschemeι.toLRSHom.toShHom))).val.app (op U) φ))
        ((conormalSheafIsoNegativeTwist D).inv.val.app
          (op ((opensMap D.subschemeι.toLRSHom.toShHom).obj U))
          (((modulePullbackPushforwardAdjunction
              D.subschemeι.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf
              D.subschemeι.toLRSHom.toShHom)).val.app (op U) x)) =
      ((structureSheafHom D.subschemeι.toLRSHom.toShHom).hom.app (op U)).hom
        (evalSection X.sheaf.obj
          (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom).val
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
            X.sheaf.obj
            (structureSheafRing X.toRingedSpace).property)).val (op U) φ x) := by
  have _h₁ : ∀ z : D.subscheme.toRingedSpace.carrier,
      IsLocalRing (ringStalk D.subscheme.toRingedSpace z) := fun z => D.subscheme.isLocalRing z
  have _h₂ : ∀ z : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace z) :=
    fun z => X.isLocalRing z
  have _hI : IsInvertible X.sheaf.obj (structureSheafRing X.toRingedSpace).property
      (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom) :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  refine Eq.trans (dualSheafIso_inv_evalSection D.subscheme.sheaf.obj
    (structureSheafRing D.subscheme.toRingedSpace).property (conormalSheafIsoNegativeTwist D)
    (op ((opensMap D.subschemeι.toLRSHom.toShHom).obj U)) _ _) ?_
  refine Eq.trans (congrArg (fun y => evalSection D.subscheme.sheaf.obj
      ((modulePullback D.subschemeι.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom)).val
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        D.subscheme.sheaf.obj
        (structureSheafRing D.subscheme.toRingedSpace).property)).val
      (op ((opensMap D.subschemeι.toLRSHom.toShHom).obj U))
      (PresheafOfModules.Hom.app
        (dualPullbackIsoOfPullbackStalkFormula D.subschemeι.toLRSHom.toShHom
          (Stacks.RingedSpace.pullbackStalkFormula _)
          (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom)).inv.val
        (op ((opensMap D.subschemeι.toLRSHom.toShHom).obj U))
        (((modulePullbackPushforwardAdjunction
            D.subschemeι.toLRSHom.toShHom).unit.app
          (dualSheaf X.sheaf.obj (structureSheafRing X.toRingedSpace).property
            (Stacks.ClosedImmersion.idealSheaf
              D.subschemeι.toLRSHom.toShHom))).val.app (op U) φ)) y)
    (app_hom_app_inv D.subscheme.sheaf.obj (structureSheafRing D.subscheme.toRingedSpace).property
      (conormalSheafIsoNegativeTwist D)
      (op ((opensMap D.subschemeι.toLRSHom.toShHom).obj U)) _)) ?_
  exact evalSection_dualPullbackIsoOfPullbackStalkFormula_inv
    D.subschemeι.toLRSHom.toShHom (Stacks.RingedSpace.pullbackStalkFormula _)
    (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom) (op U) φ x

end Card

end Stacks.Divisors

end
