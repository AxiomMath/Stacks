module

public import StacksFrontier.Deformation.RingedSpaceThickening.FlatLiftExistence
public import StacksFrontier.CategoryTheory.Functor.IsIsoMapOfHypothesis
public import StacksFrontier.Deformation.ToposThickening.FlatLiftFlatnessEquivalence
public import StacksFrontier.Deformation.ToposThickening.FlatLiftIdealFactors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCancelTensorModule

/-!
# The two spellings of the first factor of the canonical map of Stacks 08MQ

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `𝒥 = Ker(t^♯) ⊂ O_{ℬ'}`, and let `ℱ` be an
`O`-module presented on the thickened topos as an `i_*O`-module.

The first factor `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of the canonical map of Stacks 08MQ is carried by this
tree in two inequivalent spellings: as `Deformation.ToposThickening.canonicalFirstFactor`,
formed over `f⁻¹O_ℬ` in the `f⁻¹` presentation Stacks 08MQ is proved in, and as
`Deformation.ToposThickening.idealTensorComparison`, formed over `O'` on the thickened topos,
which is the presentation the statements of Stacks 08MV and Stacks 08VW use. This file provides
the comparisons of the two sides of the square relating them.

## Main results

* `Deformation.ToposThickening.isIso_reductionTensorMapStructureRestrict`: **`I ⊗_{O'} i_*ℱ` is
  `I ⊗_{i_*O} ℱ`**, the target side of the square. Tensoring with the square-zero ideal does not
  see the difference between an `O'`-module and its reduction, and `i_*ℱ` is its own reduction.
* `Deformation.ToposThickening.isIso_reductionTensorMapBaseStructureRestrict`:
  **`f⁻¹𝒥 ⊗_{f⁻¹O_{ℬ'}} i_*ℱ` is `f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`**, the source side of the square read over
  the base.
* `Deformation.ToposThickening.pullbackBaseIdealMap_unit_apply`: **the `f⁻¹O_ℬ`-linear map of
  ideals `f⁻¹𝒥 ⟶ I` of Situation 08M7 is the canonical map `f^*𝒥 ⟶ I` precomposed with the unit
  of the extension of scalars**, on sections. This is what makes the square commute on pure
  tensors.

## Implementation notes

Both reduction comparisons are instances of
`Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_isIso` at a reduction map which is
*invertible*: the identity of `i_*ℱ` in the first, and the transport
`Deformation.ToposThickening.baseReductionMap` of that identity around the square of structure
maps in the second. The cokernel datum that lemma consumes is then free — an isomorphism is a
cokernel of any map it kills — and no ideal product has to be computed.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap multiplicationMap reductionTensorMap
  multiplicationMap_eq_of_tmul reductionTensorMap_tmul tensorRight_map_tmul)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

section Reflect

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **Restriction of scalars reflects isomorphisms.** It is faithful, so it reflects both
monomorphisms and epimorphisms, and the categories of sheaves of modules are abelian. -/
theorem isIso_of_isIso_restrictScalars_map {R₀ R : Sheaf J RingCat.{w}} (m : R₀ ⟶ R)
    {M N : SheafOfModules.{w} R} (g : M ⟶ N)
    (h : IsIso ((SheafOfModules.restrictScalars m).map g)) : IsIso g := by
  have := h
  have : Mono g := mono_of_mono_restrictScalars_map m g inferInstance
  have : Epi g := epi_of_epi_restrictScalars_map m g inferInstance
  exact isIso_of_mono_of_epi g

end Reflect

section Thickening

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (hi : FirstOrderThickening i)
  (F : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **Multiplication by the square-zero ideal is zero on `i_*ℱ`.** The ideal acts through the
structure map `i^♯`, which kills it. -/
theorem multiplicationMap_structureRestrict_eq_zero :
    multiplicationMap i.fSharp hi.I
        ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) hi.incl = 0 := by
  refine (multiplicationMap_eq_of_tmul i.fSharp hi.I
    ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) hi.incl 0 ?_).symm
  intro U a x
  have hz : (show (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U from
      i.fSharp.hom.app U
        (show (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.obj U from hi.incl.val.app U a)) =
            0 :=
    (hi.kernel U _).2 ⟨a, rfl⟩
  show (0 : F.val.obj U) = _
  have h : (show (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.obj U from hi.incl.val.app U a) •
      (show ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F).val.obj U from x) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U from
          i.fSharp.hom.app U
            (show (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.obj U from hi.incl.val.app U
                a)) •
        (show F.val.obj U from x) := rfl
  rw [h, hz, zero_smul]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- The composite with the identity, the form the flatness criterion consumes. -/
theorem multiplicationMap_structureRestrict_comp_id_eq_zero :
    multiplicationMap i.fSharp hi.I
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) hi.incl ≫
        𝟙 ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) = 0 := by
  rw [Category.comp_id, multiplicationMap_structureRestrict_eq_zero]

/-- The identity of `i_*ℱ` is a cokernel of multiplication by the square-zero ideal, that
multiplication being zero. -/
noncomputable def isColimitCokernelCoforkStructureRestrict :
    IsColimit (CokernelCofork.ofπ
      (𝟙 ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F))
      (multiplicationMap_structureRestrict_comp_id_eq_zero i hi F)) :=
  CokernelCofork.IsColimit.ofπ' _ _ fun {_} k _ ↦ ⟨k, Category.id_comp k⟩

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **`I ⊗_{O'} i_*ℱ = I ⊗_{i_*O} ℱ`**: the reduction comparison of Stacks 08M4 for the
thickening `i` at the module `i_*ℱ`, whose reduction is itself. -/
theorem isIso_reductionTensorMapStructureRestrict :
    IsIso (reductionTensorMap i.fSharp hi.I
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) F (𝟙 _)) :=
  Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_isIso i.fSharp hi.surjective
    hi.I hi.I ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) F hi.incl
    (fun U a ↦ (hi.kernel U _).2 ⟨a, rfl⟩) (𝟙 _)
    (multiplicationMap_structureRestrict_comp_id_eq_zero i hi F)
    (isColimitCokernelCoforkStructureRestrict i hi F)

end Thickening

section Square

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))

include comm

/-- **The reduction of `i_*ℱ` to `ℱ`, read over `f⁻¹O_{ℬ'}`, is invertible**: it is the transport
of the identity around the square of structure maps. -/
theorem isIso_baseReductionMap_structureRestrict :
    IsIso (baseReductionMap i t f f' comm F
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _)) := by
  have h : baseReductionMap i t f f' comm F
        ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _) =
      squareTransportSymm f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
        (inverseImageReducedStructureMap i t f f' comm)
        (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) F := by
    have hid := (SheafOfModules.restrictScalars
      (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map_id
        ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)
    rw [baseReductionMap, hid, Category.id_comp]
  rw [h]
  exact isIso_squareTransportSymm _ _ _ _ _ F

/-- The reduction of `i_*ℱ` is a cokernel of multiplication by `f⁻¹𝒥`, being invertible. -/
noncomputable def isColimitCokernelCoforkBaseReductionStructureRestrict :
    IsColimit (CokernelCofork.ofπ
      (baseReductionMap i t f f' comm F
        ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _))
      (multiplicationMap_comp_baseReductionMap i t f f' ht comm F
        ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _))) := by
  haveI := isIso_baseReductionMap_structureRestrict i t f f' comm F
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {_} k _ ↦ ⟨inv (baseReductionMap i t f f' comm F
    ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _)) ≫ k, ?_⟩
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- **`f⁻¹𝒥 ⊗_{f⁻¹O_{ℬ'}} i_*ℱ = f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`**: the reduction comparison of Stacks 08M4
for the inverse image of the thickening of the base, at the module `i_*ℱ`. -/
theorem isIso_reductionTensorMapBaseStructureRestrict :
    IsIso (reductionTensorMap (inverseImageBaseReduction t f')
      (inverseImageBaseIdeal t f' ht)
      (baseModule f' ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F))
      (reducedBaseModule i t f f' comm F)
      (baseReductionMap i t f f' comm F
        ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _))) :=
  Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_isIso
    (inverseImageBaseReduction t f')
    (isLocallySurjective_inverseImageBaseReduction t f' ht)
    (inverseImageBaseIdeal t f' ht) (inverseImageBaseIdeal t f' ht)
    (baseModule f' ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F))
    (reducedBaseModule i t f f' comm F)
    (inverseImageBaseIdealIncl t f' ht)
    (inverseImageBaseReduction_inverseImageBaseIdealIncl t f' ht)
    (baseReductionMap i t f f' comm F
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _))
    (multiplicationMap_comp_baseReductionMap i t f f' ht comm F
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _))
    (isColimitCokernelCoforkBaseReductionStructureRestrict i t f f' ht comm F)

/-- **The two readings of the map of ideals `f⁻¹𝒥 ⟶ I` of Situation 08M7 agree on sections**: the
canonical map of ideals `f^*𝒥 ⟶ I` applied to the image of a section `j` of `f⁻¹𝒥` under the unit
of the extension of scalars is the `f⁻¹O_ℬ`-linear map of ideals applied to `j`.

Both sections of `I` have the same image `(f')^♯(j)` in `O'`, and the inclusion of `I` is
injective on sections. -/
theorem pullbackBaseIdealMap_unit_apply (U : X'.Cᵒᵖ)
    (z : (inverseImageBaseIdeal t f' ht).val.obj U) :
    (pullbackBaseIdealMap i t f f' hi ht comm).val.app U
        ((pullbackBaseIdealUnit t f' ht).val.app U z) =
      (inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U z := by
  refine hi.injective U ?_
  refine Eq.trans ?_ (incl_inverseImageBaseIdealToIdeal_apply i t f f' hi ht comm U z).symm
  refine Eq.trans (congrArg (fun m ↦ m.val.app U ((pullbackBaseIdealUnit t f' ht).val.app U z))
    (pullbackBaseIdealMap_comp_incl i t f f' hi ht comm)) ?_
  exact pullbackBaseIdealToStructure_unit_apply t f' ht U z


omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The `O'`-side of the square on a pure tensor**: the canonical map of ideals tensored with
`i_*ℱ`, followed by the reduction comparison `I ⊗_{O'} i_*ℱ ⟶ I ⊗_O ℱ`, carries `p ⊗ m` to
`λ(p) ⊗ m`. -/
theorem idealTensorComparisonBase_comp_reductionTensorMap_tmul (U : X'.Cᵒᵖ)
    (p : (pullbackBaseIdeal t f' ht).val.obj U) (b : F.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj ((SheafOfModules.restrictScalars
        (ringMap i.fSharp)).obj F)).map
          (pullbackBaseIdealMap i t f f' hi ht comm) ≫
        reductionTensorMap i.fSharp hi.I
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) F (𝟙 _)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X'.O) (𝟙
              (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj)).unit.app
          (PresheafOfModules.tensorObj (pullbackBaseIdeal t f' ht).val
              ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F).val)).app U
          (p ⊗ₜ[X'.O.obj.obj U] b)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O)) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val F.val)).app U
        ((pullbackBaseIdealMap i t f f' hi ht comm).val.app U p
          ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] b) := by
  refine Eq.trans (congrArg (fun y ↦ (reductionTensorMap i.fSharp hi.I
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) F (𝟙 _)).val.app U y)
    (tensorRight_map_tmul X'.O
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)
      (pullbackBaseIdealMap i t f f' hi ht comm) U p b)) ?_
  exact reductionTensorMap_tmul i.fSharp hi.I
    ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) F (𝟙 _) U
    ((pullbackBaseIdealMap i t f f' hi ht comm).val.app U p) b

/-- **The base side of the square on a pure tensor**: the reduction comparison
`f⁻¹𝒥 ⊗_{f⁻¹O_{ℬ'}} i_*ℱ ⟶ f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`, followed by the first factor of the canonical
map of Stacks 08MQ and the transport around the square of structure maps, carries `z ⊗ m` to
`λ(z) ⊗ m`. -/
theorem reductionTensorMapBase_comp_canonicalFirstFactor_tmul (U : X'.Cᵒᵖ)
    (z : (inverseImageBaseIdeal t f' ht).val.obj U) (b : F.val.obj U) :
    (reductionTensorMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
            (baseModule f' ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F))
            (reducedBaseModule i t f f' comm F)
            (baseReductionMap i t f f' comm F
              ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _)) ≫
          (SheafOfModules.restrictScalars
              (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).map
            (canonicalFirstFactor i t f f' hi ht comm F) ≫
            squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
              (inverseImageReducedStructureMap i t f f' comm)
              (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
              (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor
                  i.toToposHom).obj X.O)).flip.obj F).obj
                hi.I)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')) (𝟙
              (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj)).unit.app
          (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars
              (ringMap (inverseImageBaseReduction t f'))).obj (inverseImageBaseIdeal t f' ht)).val
                  (baseModule f' ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
                  F)).val)).app U
          (z ⊗ₜ[(inverseImageBaseRing f').obj.obj U] b)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O)) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val F.val)).app U
        ((inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U z
          ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] b) := by
  have hbr : (baseReductionMap i t f f' comm F
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _)).val.app U b = b :=
    baseReductionMap_val_app i t f f' comm F
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _) U b
  refine Eq.trans (congrArg (fun y ↦ (squareTransport f'.fSharpInverseImage i.fSharp
      (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
      (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor i.toToposHom).obj
          X.O)).flip.obj F).obj hi.I)).val.app
        U ((canonicalFirstFactor i t f f' hi ht comm F).val.app U y))
    ((reductionTensorMap_tmul (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
        (baseModule f' ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F))
        (reducedBaseModule i t f f' comm F)
        (baseReductionMap i t f f' comm F
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _)) U z b).trans
      (congrArg (fun y ↦ ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f')) (𝟙
              (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t
              f')).obj)).unit.app
          (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val (reducedBaseModule i t f
              f' comm F).val)).app U
          (z ⊗ₜ[(inverseImageReducedBaseRing t f').obj.obj U] y)) hbr))) ?_
  refine Eq.trans (congrArg (fun y ↦ (squareTransport f'.fSharpInverseImage i.fSharp
      (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
      (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor i.toToposHom).obj
          X.O)).flip.obj F).obj hi.I)).val.app
        U y) (canonicalFirstFactor_tmul i t f f' hi ht comm F U z b)) ?_
  exact squareTransport_val_app f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
    (inverseImageReducedStructureMap i t f f' comm)
    (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
    (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor i.toToposHom).obj
        X.O)).flip.obj F).obj hi.I) U _



/-- **The square relating the two spellings of the first factor of the canonical map of
Stacks 08MQ commutes.**

Going right and down: the identity `f⁻¹𝒥 ⊗_{f⁻¹O_{ℬ'}} i_*ℱ = f^*𝒥 ⊗_{O'} i_*ℱ` of
`Stacks.FlatChangeOfRings.cancelExtendScalarsTensorMap`, then the canonical map of ideals
`f^*𝒥 ⟶ I` tensored with `i_*ℱ`, then the reduction comparison `I ⊗_{O'} i_*ℱ = I ⊗_O ℱ`.
Going down and right: the reduction comparison
`f⁻¹𝒥 ⊗_{f⁻¹O_{ℬ'}} i_*ℱ = f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`, then the first factor of Stacks 08MQ, then the
transport around the square of structure maps. Both routes carry `j ⊗ m` to `λ(j) ⊗ m`, `λ`
being the map of ideals `f⁻¹𝒥 ⟶ I` of Situation 08M7. -/
theorem cancelExtendScalarsTensorMap_comp_idealTensorComparisonBase :
    Stacks.FlatChangeOfRings.cancelExtendScalarsTensorMap f'.fSharpInverseImage
          ((SheafOfModules.restrictScalars
            (ringMap (inverseImageBaseReduction t f'))).obj (inverseImageBaseIdeal t f' ht))
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) ≫
        (SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
              ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)).map
              (pullbackBaseIdealMap i t f f' hi ht comm) ≫
            reductionTensorMap i.fSharp hi.I
              ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) F (𝟙 _)) =
      reductionTensorMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
            (baseModule f' ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F))
            (reducedBaseModule i t f f' comm F)
            (baseReductionMap i t f f' comm F
              ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _)) ≫
        (SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).map
            (canonicalFirstFactor i t f f' hi ht comm F) ≫
          squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
            (inverseImageReducedStructureMap i t f f' comm)
            (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
            (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor
                i.toToposHom).obj X.O)).flip.obj F).obj
              hi.I) := by
  refine Stacks.SheafOfModules.FlatSquareZero.tensorSheaf_hom_ext (inverseImageBaseRing f')
    ((SheafOfModules.restrictScalars
      (ringMap (inverseImageBaseReduction t f'))).obj (inverseImageBaseIdeal t f' ht))
    ((SheafOfModules.restrictScalars
      (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).obj
        ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)) _ fun U z b ↦ ?_
  refine Eq.trans (congrArg (fun y ↦ (((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)).map
          (pullbackBaseIdealMap i t f f' hi ht comm) ≫
        reductionTensorMap i.fSharp hi.I
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) F (𝟙 _)).val.app U y)
    (Stacks.FlatChangeOfRings.cancelExtendScalarsTensorMap_tmul f'.fSharpInverseImage
      ((SheafOfModules.restrictScalars
        (ringMap (inverseImageBaseReduction t f'))).obj (inverseImageBaseIdeal t f' ht))
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) U z b)) ?_
  refine Eq.trans (idealTensorComparisonBase_comp_reductionTensorMap_tmul i t f f' hi ht comm F U
    ((pullbackBaseIdealUnit t f' ht).val.app U z) b) ?_
  refine Eq.trans (congrArg (fun α ↦ ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O)) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val F.val)).app U
      (α ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] b))
    (pullbackBaseIdealMap_unit_apply i t f f' hi ht comm U z)) ?_
  exact (reductionTensorMapBase_comp_canonicalFirstFactor_tmul i t f f' hi ht comm F U z b).symm

/-- The square transport of the tensor product of the ideal of `i` with `F` is invertible. -/
private theorem isIso_squareTransport_idealTensor :
    IsIso (squareTransport f'.fSharpInverseImage i.fSharp
      (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
      (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor i.toToposHom).obj
          X.O)).flip.obj F).obj hi.I)) :=
  ⟨⟨squareTransportSymm f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
      (inverseImageReducedStructureMap i t f f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) _,
    squareTransport_comp_squareTransportSymm _ _ _ _ _ _,
    squareTransportSymm_comp_squareTransport _ _ _ _ _ _⟩⟩

/-- The canonical first factor is invertible iff the right route of the square is. -/
private theorem isIso_canonicalFirstFactor_iff_isIso_right_route :
    IsIso (canonicalFirstFactor i t f f' hi ht comm F) ↔
      IsIso (reductionTensorMap (inverseImageBaseReduction t f')
        (inverseImageBaseIdeal t f' ht)
        (baseModule f' ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F))
        (reducedBaseModule i t f f' comm F)
        (baseReductionMap i t f f' comm F
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) (𝟙 _)) ≫
      (SheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).map
          (canonicalFirstFactor i t f f' hi ht comm F) ≫
        squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
          (inverseImageReducedStructureMap i t f f' comm)
          (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
          (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O)).flip.obj F).obj
            hi.I)) :=
  ⟨fun h ↦ IsIso.comp_isIso' (isIso_reductionTensorMapBaseStructureRestrict i t f f' ht comm F)
      (IsIso.comp_isIso' (Functor.isIso_map_of_isIso (SheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))) _ h)
        (isIso_squareTransport_idealTensor i t f f' hi comm F)),
    fun h ↦ isIso_of_isIso_restrictScalars_map
      (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f')) _
      (AlgebraicGeometry.RingedSpaceThickening.isIso_of_isIso_comp_right _ _
        (isIso_squareTransport_idealTensor i t f f' hi comm F)
        (AlgebraicGeometry.RingedSpaceThickening.isIso_of_isIso_comp_left _ _
          (isIso_reductionTensorMapBaseStructureRestrict i t f f' ht comm F) h))⟩

/-- **The two spellings of the first factor of the canonical map of Stacks 08MQ are invertible
together.** Every comparison in the square is an isomorphism, so the two first factors differ by
isomorphisms on both sides.

Each invertibility step is taken through a lemma carrying its hypotheses explicitly
(`CategoryTheory.isIso_of_isIso_comp_left` and its companions): at the size of
these terms instance search on a composite does not terminate. -/
theorem isIso_tensor_pullbackBaseIdealMap_iff_isIso_canonicalFirstFactor :
    IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
        ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)).map
        (pullbackBaseIdealMap i t f f' hi ht comm)) ↔
      IsIso (canonicalFirstFactor i t f f' hi ht comm F) := by
  have left :
      IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)).map
          (pullbackBaseIdealMap i t f f' hi ht comm)) ↔
        IsIso (Stacks.FlatChangeOfRings.cancelExtendScalarsTensorMap
          f'.fSharpInverseImage
          ((SheafOfModules.restrictScalars
            (ringMap (inverseImageBaseReduction t f'))).obj (inverseImageBaseIdeal t f' ht))
          ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) ≫
        (SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
              ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)).map
              (pullbackBaseIdealMap i t f f' hi ht comm) ≫
            reductionTensorMap i.fSharp hi.I
              ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F) F (𝟙 _))) :=
  ⟨fun h ↦ IsIso.comp_isIso'
        (Stacks.FlatChangeOfRings.isIso_cancelExtendScalarsTensorMap f'.fSharpInverseImage _ _)
        (Functor.isIso_map_of_isIso (SheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)) _
          (IsIso.comp_isIso' h (isIso_reductionTensorMapStructureRestrict i hi F))),
      fun h ↦ AlgebraicGeometry.RingedSpaceThickening.isIso_of_isIso_comp_right _ _
        (isIso_reductionTensorMapStructureRestrict i hi F)
        (isIso_of_isIso_restrictScalars_map
          (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage) _
          (AlgebraicGeometry.RingedSpaceThickening.isIso_of_isIso_comp_left _ _
            (Stacks.FlatChangeOfRings.isIso_cancelExtendScalarsTensorMap
              f'.fSharpInverseImage _ _) h))⟩
  exact left.trans
    ((iff_of_eq (congrArg IsIso
      (cancelExtendScalarsTensorMap_comp_idealTensorComparisonBase i t f f' hi ht comm F))).trans
    (isIso_canonicalFirstFactor_iff_isIso_right_route i t f f' hi ht comm F).symm)

end Square

end Deformation.ToposThickening

end
