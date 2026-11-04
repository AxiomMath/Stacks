module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCancelTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsImageProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MultiplicationIdealProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposUnitStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseFactorisation
public import StacksFrontier.Deformation.ToposThickening.BaseThickeningInverseImage
public import StacksFrontier.Deformation.ToposThickening.IdealProductSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of Stacks 08MQ and the ideal of the base pulled back

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `𝒥 = Ker(t^♯) ⊂ O_{B'}`. This file builds, out
of the ideal datum of
`StacksFrontier/Deformation/ToposThickening/BaseThickeningInverseImage.lean`, the pullback
`f^*𝒥 = O' ⊗_{f⁻¹O_{ℬ'}} f⁻¹𝒥` and the canonical map of ideals `f^*𝒥 ⟶ I` of Situation 08M7,
whose surjectivity is strictness in the sense of Stacks 08M9.

## Main definitions

* `Deformation.ToposThickening.pullbackBaseIdeal`: `f^*𝒥`.
* `Deformation.ToposThickening.pullbackBaseIdealToStructure`: the composite `f^*𝒥 ⟶ O'`, which
  on the image of a local section `j` of `f⁻¹𝒥` is `(f')^♯(j)`.
* `Deformation.ToposThickening.pullbackBaseIdealMap`: **the canonical map `f^*𝒥 ⟶ I`.**

## Main results

* `Deformation.ToposThickening.pullbackBaseIdealMap_comp_incl`: the canonical map of ideals is
  the unique map whose composite into `O'` is `Deformation.ToposThickening.
  pullbackBaseIdealToStructure`, which is the normalisation Situation 08M7 pins it down by.
* `Deformation.ToposThickening.mul_eq_zero_of_inverseImageBaseIdeal`: the local sections of
  `f⁻¹𝒥`, read in `f⁻¹O_{ℬ'}`, multiply to zero — the square-zero hypothesis of Stacks 08M4,
  which is a consequence of the ideal being a module over the quotient.

## Implementation notes

The square-zero hypothesis of Stacks 08M4 is not extra data. That criterion already asks for
its ideal to be a sheaf of modules over the *quotient* ring, included `O'`-linearly into the
ring being thickened; `O'`-linearity of the inclusion then forces the product of two sections
of the ideal to be the image of a section multiplied by its own image in the quotient, which is
zero. So `mul_eq_zero_of_inverseImageBaseIdeal` needs nothing about inverse images.

That `f^*𝒥 ⟶ O'` lands in `I` is checked through
`Stacks.SheafOfModules.restrictScalars_unit_cancel_zero`: a morphism out of an extension of
scalars vanishes as soon as its restriction along the unit does, and on the image of a section
`j` of `f⁻¹𝒥` the composite into `i_*O` is `i^♯((f')^♯(j))`, which the commuting square of
structure maps rewrites as `f^♯` of the reduction of `j` — and the reduction kills `f⁻¹𝒥`.

## References

* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)
open Stacks.SheafOfModules.ChangeOfRings (unitToRestrictScalarsUnit
  unitToRestrictScalarsUnit_val_app)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u v' u' w vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

section Canonical

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
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)

omit [HasWeakSheafify X'.J AddCommGrpCat] [X'.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The local sections of `f⁻¹𝒥`, read in `f⁻¹O_{ℬ'}`, multiply to zero.**

Nothing about inverse images is used: the ideal is a sheaf of modules over the quotient
`f⁻¹O_ℬ` and its inclusion is linear over `f⁻¹O_{ℬ'}`, so the product of two sections is the
image of one of them scaled by the *reduction* of the other, and the reduction kills the
ideal. -/
theorem mul_eq_zero_of_inverseImageBaseIdeal (U : X'.Cᵒᵖ)
    (a b : (inverseImageBaseIdeal t f' ht).val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
        (inverseImageBaseIdealIncl t f' ht).val.app U a) *
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
        (inverseImageBaseIdealIncl t f' ht).val.app U b) = 0 := by
  have hz : (ringMap (inverseImageBaseReduction t f')).hom.app U
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
        (inverseImageBaseIdealIncl t f' ht).val.app U a) = 0 :=
    inverseImageBaseReduction_inverseImageBaseIdealIncl t f' ht U a
  have h0 : (show ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          (inverseImageBaseRing f')).obj.obj U from
        (inverseImageBaseIdealIncl t f' ht).val.app U a) •
      (show ((SheafOfModules.restrictScalars ((sheafCompose X'.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map (inverseImageBaseReduction t f'))).obj
          (inverseImageBaseIdeal t f' ht)).val.obj U from b) = 0 :=
    (congrArg (fun s ↦ s • b) hz).trans (zero_smul _ _)
  have hmul : (show ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          (inverseImageBaseRing f')).obj.obj U from
        (inverseImageBaseIdealIncl t f' ht).val.app U
          ((show ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
                (inverseImageBaseRing f')).obj.obj U from
              (inverseImageBaseIdealIncl t f' ht).val.app U a) •
            (show ((SheafOfModules.restrictScalars ((sheafCompose X'.J
                (forget₂ CommRingCat.{w} RingCat.{w})).map
                (inverseImageBaseReduction t f'))).obj
                (inverseImageBaseIdeal t f' ht)).val.obj U from b))) =
      (show ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
            (inverseImageBaseRing f')).obj.obj U from
          (inverseImageBaseIdealIncl t f' ht).val.app U a) *
        (show ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
            (inverseImageBaseRing f')).obj.obj U from
          (inverseImageBaseIdealIncl t f' ht).val.app U b) :=
    map_smul _ _ _
  exact hmul.symm.trans ((congrArg _ h0).trans (map_zero _))

/-- **`f^*𝒥 = O' ⊗_{f⁻¹O_{ℬ'}} f⁻¹𝒥`**, the pullback along `f'` of the square-zero ideal of the
thickening of the base. For a morphism of *first order* thickenings this is the source's
`f^*𝒥`, the two pullbacks `(f')^*𝒥` and `f^*𝒥` agreeing by Situation 08M7. -/
noncomputable abbrev pullbackBaseIdeal :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O) :=
  (Stacks.FlatChangeOfRings.extendScalars f'.fSharpInverseImage).obj
    ((SheafOfModules.restrictScalars (ringMap (inverseImageBaseReduction t f'))).obj
      (inverseImageBaseIdeal t f' ht))

/-- **The composite `f^*𝒥 ⟶ O'`**: the adjoint transpose of the inclusion of `f⁻¹𝒥` into
`f⁻¹O_{ℬ'}` followed by the structure map of `f'`. On the image of a local section `j` of
`f⁻¹𝒥` it is `(f')^♯(j)`, which is the source's description of the map of ideals. -/
noncomputable def pullbackBaseIdealToStructure :
    pullbackBaseIdeal t f' ht ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X'.O) :=
  ((Stacks.FlatChangeOfRings.extendScalarsAdjunction f'.fSharpInverseImage).homEquiv _ _).symm
    (inverseImageBaseIdealIncl t f' ht ≫
      unitToRestrictScalarsUnit (ringMap f'.fSharpInverseImage))

include comm

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **The composite `f^*𝒥 ⟶ O'` is killed by `i^♯`.** A morphism out of an extension of scalars
vanishes as soon as its restriction along the unit does, and on the image of a local section `j`
of `f⁻¹𝒥` the composite into `i_*O` is `i^♯((f')^♯(j))`, which the commuting square of structure
maps turns into `f^♯` of the reduction of `j`; the reduction kills `f⁻¹𝒥`. -/
theorem pullbackBaseIdealToStructure_comp_eq_zero :
    pullbackBaseIdealToStructure t f' ht ≫
        unitToRestrictScalarsUnit (ringMap i.fSharp) = 0 := by
  refine Stacks.SheafOfModules.restrictScalars_unit_cancel_zero
    (Stacks.FlatChangeOfRings.extendScalarsAdjunction f'.fSharpInverseImage) _ _ _ ?_
  have hhe := (Adjunction.homEquiv_unit
    (adj := Stacks.FlatChangeOfRings.extendScalarsAdjunction f'.fSharpInverseImage)
    (f := pullbackBaseIdealToStructure t f' ht)).symm.trans
      (Equiv.apply_symm_apply ((Stacks.FlatChangeOfRings.extendScalarsAdjunction
        f'.fSharpInverseImage).homEquiv _ _) (inverseImageBaseIdealIncl t f' ht ≫
          unitToRestrictScalarsUnit (ringMap f'.fSharpInverseImage)))
  rw [Functor.map_comp, ← Category.assoc, hhe]
  have hfinal : ∀ (U : X'.Cᵒᵖ) (k : (inverseImageBaseIdeal t f' ht).val.obj U),
      (ringMap i.fSharp).hom.app U ((ringMap f'.fSharpInverseImage).hom.app U
        (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
          (inverseImageBaseIdealIncl t f' ht).val.app U k)) = 0 := by
    intro U k
    change (f'.fSharpInverseImage ≫ i.fSharp).hom.app U
        (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
          (inverseImageBaseIdealIncl t f' ht).val.app U k) = 0
    rw [← inverseImageBaseReduction_comp_inverseImageReducedStructureMap i t f f' comm]
    change (inverseImageReducedStructureMap i t f f' comm).hom.app U
      ((inverseImageBaseReduction t f').hom.app U _) = 0
    rw [inverseImageBaseReduction_inverseImageBaseIdealIncl t f' ht U k]
    exact map_zero _
  exact SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun k ↦
      (unitToRestrictScalarsUnit_val_app (ringMap i.fSharp) U _).trans
        ((congrArg ((ringMap i.fSharp).hom.app U)
            (unitToRestrictScalarsUnit_val_app (ringMap f'.fSharpInverseImage) U _)).trans
          (hfinal U k))))

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **The composite `f^*𝒥 ⟶ O'` lands in `I`**, on sections: every local section of `f^*𝒥`,
read in `O'`, is killed by `i^♯`. -/
theorem fSharp_pullbackBaseIdealToStructure_apply (U : X'.Cᵒᵖ)
    (z : (pullbackBaseIdeal t f' ht).val.obj U) :
    i.fSharp.hom.app U (show (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.obj U from
      (pullbackBaseIdealToStructure t f' ht).val.app U z) = 0 :=
  (unitToRestrictScalarsUnit_val_app (ringMap i.fSharp) U _).symm.trans
    (congrArg (fun m : pullbackBaseIdeal t f' ht ⟶
        (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) ↦ m.val.app U z)
      (pullbackBaseIdealToStructure_comp_eq_zero i t f f' ht comm))

/-- **The canonical map of ideals `f^*𝒥 ⟶ I` of Situation 08M7**: the unique map of
`O'`-modules whose composite with the inclusion `I ⊆ O'` is
`Deformation.ToposThickening.pullbackBaseIdealToStructure`, that is, the structure map of `f'`
applied to the sections of `𝒥`. Strictness of `(f, f')` in the sense of Stacks 08M9 is the
assertion that this map is an epimorphism. -/
noncomputable def pullbackBaseIdealMap :
    pullbackBaseIdeal t f' ht ⟶ hi.idealOfThickening.I :=
  (Stacks.SheafOfModules.existsUnique_factorThrough hi.incl hi.injective
    (pullbackBaseIdealToStructure t f' ht)
    (fun U z ↦ (hi.kernel U _).1
      (fSharp_pullbackBaseIdealToStructure_apply i t f f' ht comm U z))).choose

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **The canonical map of ideals has the normalisation that characterises it**: its composite
with the inclusion of `I` into `O'` is the structure map of `f'` applied to the inclusion of
`𝒥`. This is the normalisation Situation 08M7 pins the map of ideals down by. -/
theorem pullbackBaseIdealMap_comp_incl :
    pullbackBaseIdealMap i t f f' hi ht comm ≫ hi.incl =
      pullbackBaseIdealToStructure t f' ht :=
  (Stacks.SheafOfModules.existsUnique_factorThrough hi.incl hi.injective
    (pullbackBaseIdealToStructure t f' ht)
    (fun U z ↦ (hi.kernel U _).1
      (fSharp_pullbackBaseIdealToStructure_apply i t f f' ht comm U z))).choose_spec.1

/-- **Strictness, in the sense of Stacks 08M9**: the canonical map of ideals `f^*𝒥 ⟶ I` is an
epimorphism. -/
def IsStrictPullbackIdealMap : Prop := Epi (pullbackBaseIdealMap i t f f' hi ht comm)

end Canonical

end Deformation.ToposThickening

end
