module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceInversePairing

/-!
# The evaluation characterising the inverse-line factor of the conormal source at a point

Let `ℒ` be an invertible module on an algebraic space `X` and `x : T ⟶ X` a scheme point, not
necessarily étale.  The inverse-line factor of the conormal source read at `x` is

`i_x : R_T(x^*(ℒ^{⊗ -1})) ≅ R_T(x^*ℒ)^{⊗ -1}`,

the Zariski reading of the inverse image of tensor powers
(`AlgebraicGeometry.Space.modulePullbackTensorPowerIso`) followed by the Zariski reading of
tensor inverses (`AlgebraicGeometry.Space.zariskiReadingTensorPowerNegOneIso`).  This file proves
that `i_x` is pinned by its evaluation: tensored with `R_T(x^*ℒ)` and followed by the
trivialisation of `R_T(x^*ℒ)^{⊗ -1} ⊗ R_T(x^*ℒ)`, it is the Zariski reading of the pullback of
the trivialisation of `ℒ^{⊗ -1} ⊗ ℒ` through Stacks 03EL for `x`.  This is the evaluation
hypothesis of `CategoryTheory.Functor.bifunctor_baseChange_inverse` for the base change of
`i_x`.

## Main definitions

* `AlgebraicGeometry.Space.inversePointReadingIso`: the factor `i_x`.

## Main results

* `AlgebraicGeometry.Space.zariskiReadingTensorIso_symm_naturality_left`: naturality of the
  Zariski reading tensor isomorphism in the left variable.
* `AlgebraicGeometry.Space.zariskiReadingTensorPowerNegOneIso_evaluation`: the evaluation of
  `R_T(m)` followed by the Zariski reading of tensor inverses, for any `m : ℳ ≅ ℒ^{⊗ -1}`.
* `AlgebraicGeometry.Space.inversePointReadingIso_evaluation`: **the evaluation of `i_x`.**

## Implementation notes

All identities are stated between isomorphisms, and the tensor product with a fixed module is
written as the component `(F.mapIso m).app N` of the tensor bifunctor rather than through
`F.flip`: the codomain `(F.obj _).obj N` then matches the domain of the successor isomorphism
syntactically, while `(F.flip.obj N).obj _` sends the unifier into the comparison of two large
modules before it unfolds the flip.

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

universe u w

namespace Stacks.SheafOfModules.Invertible

attribute [local implicit_reducible] TensorSheafification.structureSheaf
  TensorSheafification.sheafify Tensor.sheafTensor

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- `Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne_hom_tensor` at the level of
isomorphisms, with the tensor product with `ℒ` written as a component of the bifunctor. -/
theorem isoTensorPowerNegOne_mapIso_app_trans
    (L M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]
    (h : ((Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj L ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).mapIso
        (isoTensorPowerNegOne O hO L M h)).app L ≪≫ tensorPowerSuccIso O hO L (-1) = h :=
  Iso.ext (isoTensorPowerNegOne_hom_tensor O hO L M h)

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Naturality

variable (T : BigFppfOver B S hS)

/-- The tensor product sheaf on the represented space is functorial in the right variable at
identities. -/
theorem sheafTensor_obj_map_id_space
    (P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).obj P).map
        (𝟙 Q) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- The tensor product sheaf of the Zariski ringed site of a scheme is functorial in the right
variable at identities. -/
theorem sheafTensor_obj_map_id_scheme
    (P Q : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).obj P).map
        (𝟙 Q) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- **Naturality of the Zariski reading tensor isomorphism in the left variable, at the level of
isomorphisms.** -/
theorem zariskiReadingTensorIso_symm_naturality_left
    {P P' Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (m : P ≅ P') (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (hP' : P'.IsQuasicoherentOnSite) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat)
          ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).mapIso
        ((zariskiReadingFunctor T).mapIso m)).app ((zariskiReadingFunctor T).obj Q) ≪≫
      (zariskiReadingTensorIso T P' Q hP' hQ).symm =
    (zariskiReadingTensorIso T P Q hP hQ).symm ≪≫
      (zariskiReadingFunctor T).mapIso
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).mapIso m).app
            Q) := by
  have h := zariskiReadingTensorIso_hom_naturality T m.hom (𝟙 Q) hP hQ hP' hQ
  have e1 : (zariskiReadingFunctor T).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj T)
            (isAlgebraicSpace_yoneda B S hS T))).map m.hom).app Q ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).obj P').map
          (𝟙 Q)) =
      (zariskiReadingFunctor T).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj T)
            (isAlgebraicSpace_yoneda B S hS T))).map m.hom).app Q) :=
    congrArg (zariskiReadingFunctor T).map ((congrArg (_ ≫ ·)
      (sheafTensor_obj_map_id_space T P' Q)).trans (Category.comp_id _))
  have e2 : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).map
            ((zariskiReadingFunctor T).map m.hom)).app _ ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).obj _).map
            ((zariskiReadingFunctor T).map (𝟙 Q))) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).map
            ((zariskiReadingFunctor T).map m.hom)).app ((zariskiReadingFunctor T).obj Q) :=
    (congrArg (_ ≫ ·) ((congrArg _ ((zariskiReadingFunctor T).map_id Q)).trans
      (sheafTensor_obj_map_id_scheme T _ _))).trans (Category.comp_id _)
  have h' := ((congrArg (· ≫ (zariskiReadingTensorIso T P' Q hP' hQ).hom) e1).symm.trans h).trans
    (congrArg (_ ≫ ·) e2)
  exact Iso.ext (Iso.inv_comp_eq_of_comp_hom _ _ _ _ h')

/-- The pairing of the Zariski reading of `ℒ^{⊗ -1}` unfolded, at the level of isomorphisms. -/
theorem zariskiReadingTensorPowerNegOnePairing_eq
    (L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    [hL : IsInvertible (structureCommRings B S hS (yonedaSpace B S hS T))
      (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L] :
    zariskiReadingTensorPowerNegOnePairing T L =
      (zariskiReadingTensorIso T (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS (yonedaSpace B S hS T))
          (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L (-1)) L
        (isQuasicoherentOnSite_invertibleTensorPower (yonedaSpace B S hS T) L (-1))
        (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T) L hL)).symm ≪≫
      (zariskiReadingFunctor T).mapIso
        (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
            (structureCommRings B S hS (yonedaSpace B S hS T))
            (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L (-1) ≪≫
          Stacks.SheafOfModules.Invertible.tensorPowerReindex
            (structureCommRings B S hS (yonedaSpace B S hS T))
            (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L
            (show (-1 : ℤ) + 1 = 0 by omega)) ≪≫
      zariskiReadingUnitIso T :=
  rfl


/-- **The evaluation of the Zariski reading of an identification with `ℒ^{⊗ -1}`**: for
`m : ℳ ≅ ℒ^{⊗ -1}` on the represented space, `R_T(m)` followed by the Zariski reading of tensor
inverses, tensored with `R_T ℒ` and followed by the trivialisation, is the Zariski reading of
`(m ⊗ 1) ≫ ev` through the reading tensor isomorphism and the reading of the structure sheaf. -/
theorem zariskiReadingTensorPowerNegOneIso_evaluation
    (L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    [hL : IsInvertible (structureCommRings B S hS (yonedaSpace B S hS T))
      (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L]
    {M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (m : M ≅ Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS (yonedaSpace B S hS T))
          (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L (-1))
    (hM : M.IsQuasicoherentOnSite) :
    haveI := isInvertible_zariskiReading T L
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL)
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat)
          ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).mapIso
        ((zariskiReadingFunctor T).mapIso m ≪≫ zariskiReadingTensorPowerNegOneIso T L)).app
        ((zariskiReadingFunctor T).obj L) ≪≫
      Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
        ((BigFppfOver.toScheme B S hS).obj T).presheaf
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
        ((zariskiReadingFunctor T).obj L) (-1) =
    (zariskiReadingTensorIso T M L hM
        (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T) L hL)).symm ≪≫
      (zariskiReadingFunctor T).mapIso
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).mapIso
              m).app L ≪≫
          Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
            (structureCommRings B S hS (yonedaSpace B S hS T))
            (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L (-1) ≪≫
          Stacks.SheafOfModules.Invertible.tensorPowerReindex
            (structureCommRings B S hS (yonedaSpace B S hS T))
            (structureRingSheaf B S hS (yonedaSpace B S hS T)).property L
            (show (-1 : ℤ) + 1 = 0 by omega)) ≪≫
      zariskiReadingUnitIso T := by
  have := isInvertible_zariskiReading T L
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL)
  have hp := Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne_mapIso_app_trans
    ((BigFppfOver.toScheme B S hS).obj T).presheaf
    ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 ((zariskiReadingFunctor T).obj L) _
    (zariskiReadingTensorPowerNegOnePairing T L)
  refine (congrArg (· ≪≫ _) (congrArg (fun k => Iso.app k ((zariskiReadingFunctor T).obj L))
    (Functor.mapIso_trans _ _ _))).trans ?_
  refine (congrArg (· ≪≫ _) (NatIso.trans_app _ _ _)).trans ?_
  refine (Iso.trans_assoc _ _ _).trans ?_
  refine (congrArg (_ ≪≫ ·) (hp.trans (zariskiReadingTensorPowerNegOnePairing_eq T L))).trans ?_
  refine (Iso.trans_assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≪≫ _) (zariskiReadingTensorIso_symm_naturality_left T m hM _ _)).trans ?_
  refine (Iso.trans_assoc _ _ _).trans (congrArg (_ ≪≫ ·) ?_)
  refine (Iso.trans_assoc _ _ _).symm.trans (congrArg (· ≪≫ _) ?_)
  exact (Functor.mapIso_trans _ _ _).symm

end Naturality

section Point

variable (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
  (L : Modules.{u, u} B S hS X.1 X.2)
  [hL : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property L]

/-- **The inverse-line factor of the conormal source read at a scheme point `x`**:
`R_T(x^*(ℒ^{⊗ -1})) ≅ R_T(x^*ℒ)^{⊗ -1}`, the Zariski reading of the inverse image of tensor
powers followed by the Zariski reading of tensor inverses. -/
def inversePointReadingIso :
    haveI hxL := isInvertible_modulePullback_obj B S hS (pointHom x) L hL
    haveI := isInvertible_zariskiReading T ((modulePullback B S hS (pointHom x)).obj L)
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hxL)
    (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property L (-1))) ≅
      Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj T).presheaf
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
        ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj L)) (-1) :=
  haveI := isInvertible_modulePullback_obj B S hS (pointHom x) L hL
  (zariskiReadingFunctor T).mapIso (modulePullbackTensorPowerIso (pointHom x) L (-1)) ≪≫
    zariskiReadingTensorPowerNegOneIso T ((modulePullback B S hS (pointHom x)).obj L)

/-- **The evaluation characterising the inverse-line factor `i_x`.**  Tensored with
`R_T(x^*ℒ)` and followed by the trivialisation of `R_T(x^*ℒ)^{⊗ -1} ⊗ R_T(x^*ℒ)`, the factor
`i_x` is the Zariski reading of the pullback of the trivialisation of `ℒ^{⊗ -1} ⊗ ℒ`, through
Stacks 03EL for `x`, the Zariski reading tensor isomorphism and the identifications of the
structure sheaves. -/
theorem inversePointReadingIso_evaluation :
    haveI hxL := isInvertible_modulePullback_obj B S hS (pointHom x) L hL
    haveI := isInvertible_zariskiReading T ((modulePullback B S hS (pointHom x)).obj L)
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hxL)
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat)
          ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).mapIso
        (inversePointReadingIso X T x L)).app
        ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj L)) ≪≫
      Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
        ((BigFppfOver.toScheme B S hS).obj T).presheaf
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
        ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj L)) (-1) =
    (zariskiReadingTensorIso T _ _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
          (isQuasicoherentOnSite_invertibleTensorPower X L (-1)))
        (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T) _ hxL)).symm ≪≫
      (zariskiReadingFunctor T).mapIso
        ((modulePullbackTensorComparison (pointHom x) L
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property L (-1))).symm ≪≫
          (modulePullback B S hS (pointHom x)).mapIso
            (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property L (-1)) ≪≫
          modulePullbackUnitIso B S hS (pointHom x)) ≪≫
      zariskiReadingUnitIso T := by
  have hxL := isInvertible_modulePullback_obj B S hS (pointHom x) L hL
  have := isInvertible_zariskiReading T ((modulePullback B S hS (pointHom x)).obj L)
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hxL)
  have he : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).mapIso
          (modulePullbackTensorPowerIso (pointHom x) L (-1))).app
          ((modulePullback B S hS (pointHom x)).obj L) ≪≫
      Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
        (structureCommRings B S hS (yonedaSpace B S hS T))
        (structureRingSheaf B S hS (yonedaSpace B S hS T)).property
        ((modulePullback B S hS (pointHom x)).obj L) (-1) =
      (modulePullbackTensorComparison (pointHom x) L
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property L (-1))).symm ≪≫
        (modulePullback B S hS (pointHom x)).mapIso
          (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property L (-1)) ≪≫
        modulePullbackUnitIso B S hS (pointHom x) :=
    Iso.ext (modulePullbackTensorPowerIso_evaluation X T x L)
  refine (zariskiReadingTensorPowerNegOneIso_evaluation T _
    (modulePullbackTensorPowerIso (pointHom x) L (-1))
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
      (isQuasicoherentOnSite_invertibleTensorPower X L (-1)))).trans ?_
  refine congrArg (_ ≪≫ ·) (congrArg (· ≪≫ _) (congrArg (zariskiReadingFunctor T).mapIso ?_))
  refine (Iso.trans_assoc _ _ _).symm.trans ?_
  refine (congrArg (_ ≪≫ ·) (Stacks.SheafOfModules.Invertible.tensorPowerReindex_neg_one_add_one
    (structureCommRings B S hS (yonedaSpace B S hS T))
    (structureRingSheaf B S hS (yonedaSpace B S hS T)).property
    ((modulePullback B S hS (pointHom x)).obj L))).trans ?_
  exact (Iso.trans_refl _).trans he

end Point

end AlgebraicGeometry.Space

end
