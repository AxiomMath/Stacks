module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiReadingTensorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMapSuccessor
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Evaluation

/-!
# The inverse line of the conormal source read at a scheme point, and its evaluation

Let `ℒ` be an invertible module on an algebraic space `X` and `x : T ⟶ X` a scheme point.  The
conormal source of Stacks 0B3V read at `x` (`AlgebraicGeometry.Space.conormalSourceReadingIso`)
has the inverse-line factor

`i_x : R_T(x^*(ℒ^{⊗ -1})) ≅ R_T(x^*ℒ)^{⊗ -1}`,

the inverse image of tensor powers (`AlgebraicGeometry.Space.modulePullbackTensorPowerIso`)
followed by the Zariski reading of tensor inverses
(`AlgebraicGeometry.Space.zariskiReadingTensorPowerNegOneIso`).  This file proves the two
evaluation identities from which `i_x` is characterised by the canonical trivialisation of
`R_T(x^*ℒ)^{⊗ -1} ⊗ R_T(x^*ℒ)` (the input `hi` of
`CategoryTheory.Functor.bifunctor_baseChange_inverse`): the inverse image of tensor powers carries
the trivialisation of `ℒ^{⊗ -1} ⊗ ℒ` to that of `(x^*ℒ)^{⊗ -1} ⊗ x^*ℒ` through Stacks 03EL for
`x`, and the Zariski reading tensor isomorphism is natural at the tensor product sheaves.


## Main results

* `AlgebraicGeometry.Space.zariskiReadingTensorIso_hom_naturality`: naturality of the Zariski
  reading tensor isomorphism at the tensor product sheaf of both sides.
* `AlgebraicGeometry.Space.modulePullbackTensorPowerIso_evaluation`: **the inverse image of
  tensor powers is normalised by the evaluation.**

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Naturality

/-- A square with invertible vertical sides, read with the inverses. -/
theorem _root_.CategoryTheory.Iso.inv_comp_eq_of_comp_hom {𝒞 : Type*} [Category 𝒞]
    {A B A' B' : 𝒞} (e : A ≅ A') (e' : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

variable (T : BigFppfOver B S hS)

/-- **Naturality of the Zariski reading tensor isomorphism**, with the tensor products of both
sides written through the tensor product sheaf bifunctors. -/
theorem zariskiReadingTensorIso_hom_naturality
    {P P' Q Q' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (a : P ⟶ P') (b : Q ⟶ Q') (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (hP' : P'.IsQuasicoherentOnSite) (hQ' : Q'.IsQuasicoherentOnSite) :
    (zariskiReadingFunctor T).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS (yoneda.obj T)
              (isAlgebraicSpace_yoneda B S hS T))).map a).app Q ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).obj P').map
            b) ≫
        (zariskiReadingTensorIso T P' Q' hP' hQ').hom =
      (zariskiReadingTensorIso T P Q hP hQ).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).map
            ((zariskiReadingFunctor T).map a)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).obj _).map
            ((zariskiReadingFunctor T).map b)) := by
  have e : ∀ (P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
      (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite),
      (zariskiReadingTensorIso T P Q hP hQ).hom =
        (zariskiReadingFunctor T).map
            (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P Q).inv ≫
          (zariskiReadingTensorObjIso T P Q hP hQ).hom := fun P Q hP hQ =>
    Functor.eq_map_inv_comp_of_eq_map_hom_comp (zariskiReadingFunctor T)
      (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P Q) _ _ rfl
  have hm := modulesTensorObjIso_hom_naturality_tensorHom B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T) a b
  have hm' : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).map a).app Q ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).obj P').map
          b) ≫
        (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P' Q').inv =
      (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P Q).inv ≫
        (a ⊗ₘ b) :=
    Iso.inv_comp_eq_of_comp_hom _ _ _ _ hm
  have hn := zariskiReadingTensorObjIso_hom_naturality' T a b hP hQ hP' hQ'
  rw [e P' Q' hP' hQ']
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (zariskiReadingTensorObjIso T P' Q' hP' hQ').hom)
    (((zariskiReadingFunctor T).map_comp _ _).symm.trans
      ((congrArg (zariskiReadingFunctor T).map hm').trans
        ((zariskiReadingFunctor T).map_comp _ _)))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hn).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (e P Q hP hQ).symm

end Naturality

section Point

variable (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
  (L : Modules.{u, u} B S hS X.1 X.2)
  [hL : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property L]

/-- The successor comparison of Stacks 01CU in degree `-1` is carried by the inverse image of
tensor powers to the inverse image of the trivialisation:
`((x^*)(ℒ^{⊗ -1}) ⊗ 1) ≫ ev = 03EL⁻¹ ≫ x^*(ev) ≫ (x^*𝒪 ≅ 𝒪)`. -/
theorem modulePullbackTensorPowerIso_evaluation :
    haveI := isInvertible_modulePullback_obj B S hS (pointHom x) L hL
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).map
        (modulePullbackTensorPowerIso (pointHom x) L (-1)).hom).app
        ((modulePullback B S hS (pointHom x)).obj L) ≫
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
        (structureCommRings B S hS (yonedaSpace B S hS T))
        (structureRingSheaf B S hS (yonedaSpace B S hS T)).property
        ((modulePullback B S hS (pointHom x)).obj L) (-1)).hom =
      (modulePullbackTensorComparison (pointHom x) L
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property L (-1))).inv ≫
        (modulePullback B S hS (pointHom x)).map
          (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property L (-1)).hom ≫
        (modulePullbackUnitIso B S hS (pointHom x)).hom := by
  have hxL := isInvertible_modulePullback_obj B S hS (pointHom x) L hL
  have := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    (structureCommRings B S hS X) (structureRingSheaf B S hS X).property L
  have := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    (structureCommRings B S hS (yonedaSpace B S hS T))
    (structureRingSheaf B S hS (yonedaSpace B S hS T)).property
    ((modulePullback B S hS (pointHom x)).obj L)
  have h := Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_tensorPowerSuccIso
    (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
    (structureCommRings B S hS (yonedaSpace B S hS T))
    (structureRingSheaf B S hS (yonedaSpace B S hS T)).property
    (modulePullback B S hS (pointHom x)) L (modulePullbackTensorComparison (pointHom x) L)
    (modulePullbackUnitIso B S hS (pointHom x)) (-1)
  have h0 := Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_zero
    (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
    (structureCommRings B S hS (yonedaSpace B S hS T))
    (structureRingSheaf B S hS (yonedaSpace B S hS T)).property
    (modulePullback B S hS (pointHom x)) L (modulePullbackTensorComparison (pointHom x) L)
    (modulePullbackUnitIso B S hS (pointHom x))
  have h0' : (Stacks.SheafOfModules.TensorPower.mapTensorPowerIso
      (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      (structureCommRings B S hS (yonedaSpace B S hS T))
      (structureRingSheaf B S hS (yonedaSpace B S hS T)).property
      (modulePullback B S hS (pointHom x)) L (modulePullbackTensorComparison (pointHom x) L)
      (modulePullbackUnitIso B S hS (pointHom x)) ((-1 : ℤ) + 1)).hom =
      (modulePullbackUnitIso B S hS (pointHom x)).hom := congrArg Iso.hom h0
  exact (Iso.eq_inv_comp _).2 (h.symm.trans (congrArg (_ ≫ ·) h0'))

end Point

end AlgebraicGeometry.Space

end
