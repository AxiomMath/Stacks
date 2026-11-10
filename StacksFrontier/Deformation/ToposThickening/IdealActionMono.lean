module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftFlatnessEquivalence
public import StacksFrontier.Deformation.ToposThickening.FlatLiftPullbackIdealComparison
public import StacksFrontier.Deformation.ToposThickening.RelativeModuleMapObstruction

/-!
# The square-zero ideal acts injectively on a flat module

Let `(f, f')` be a morphism of first order thickenings of ringed topoi as in Situation 08M7

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `𝒥 = Ker(t^♯) ⊂ O_{ℬ'}`, and let `ℱ'` be an
`O'`-module. Stacks 08MQ says that for a strict square and `ℱ'` flat over `O_{ℬ'}` the second
factor `I ⊗_O ℱ ⟶ I·ℱ'` of its canonical map is an isomorphism; read as a statement about the
action `I ⊗_{O'} ℱ' ⟶ ℱ'` of the square-zero ideal, this says that the action is injective.

That reading is the hypothesis `Deformation.ToposThickening.IsIdealActionMono` which the proof of
Stacks 08MT consumes for its source module. This file discharges it.

## Main results

* `Deformation.ToposThickening.isIdealActionMono`:
  **`Deformation.ToposThickening.IsIdealActionMono` holds**, i.e. the action of the square-zero
  ideal on a module flat over `O_{ℬ'}` is injective for a strict square.
* `Deformation.ToposThickening.exists_relativeModuleMapObstruction`: the statement of
  `StacksFrontier/Deformation/ToposThickening/RelativeModuleMapObstruction.lean` with that
  hypothesis discharged, stated here because that module cannot see this one.
* `Deformation.ToposThickening.relativeModuleMapObstructionClass`: the obstruction class
  `o(φ) ∈ Ext¹_O(ℱ, 𝒢 ⊗_O f^*𝒥)` of Stacks 08MT, the boundary class of the source's proof.
* `Deformation.ToposThickening.relativeModuleMapObstructionClass_eq_zero_iff`: **Stacks 08MT**,
  that class vanishes exactly when `φ` lifts.

## How the proof goes

The action `I ⊗_{O'} ℱ' ⟶ ℱ'` is the multiplication map of Stacks 08M4, and
`Deformation.ToposThickening.reductionTensorMap_comp_canonicalSecondFactor` factors it as the
reduction comparison `I ⊗_{O'} ℱ' ⟶ I ⊗_O ℱ`, which is invertible because the ideal is square
zero, followed by the second factor `I ⊗_O ℱ ⟶ I·ℱ'` of the canonical map of Stacks 08MQ and the
inclusion of `I·ℱ'`. The inclusion is a monomorphism, so the whole composite is one as soon as
the second factor is invertible — and that is the "moreover" clause of Stacks 08MQ,
`Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap`.

Stacks 08MQ asks for `ℱ = i^*ℱ'` as a cokernel of the inclusion of the ideal product `I·ℱ'`, and
for the flatness of `ℱ` over `O_ℬ`. The first is the sequence of Stacks 08MP,
`Deformation.ToposThickening.idealProductShortComplex_shortExact`, whose last term is the direct
image of `i^*ℱ'`; the second is the other half of the criterion of Stacks 08M4,
`Deformation.ToposThickening.isFlat_baseModule_iff`, which produces it from the flatness of `ℱ'`
that is assumed.

The last step is that the two spellings of strictness that the library carries agree — the
epimorphism of `(f')^*𝒥 ⟶ I` of Stacks 08M9 in the presentation of Situation 08M7, and the one of
`f^*𝒥 ⟶ I` that Stacks 08MQ is stated in. That bridge is
`Deformation.ToposThickening.isStrictPullbackIdealMap_iff_isStrict` in
`StacksFrontier/Deformation/ToposThickening/FlatLiftPullbackIdealComparison.lean`.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08MT](https://stacks.math.columbia.edu/tag/08MT)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (multiplicationMap)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)

universe v u w v' u' vS uS wS vS' uS' wS' e

namespace Deformation.ToposThickening

section Relative

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
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)

/-- `ℱ = i^*ℱ'`, read on the thickened topos as a module over the direct image `i_*O` before its
scalars are restricted along `i^♯`. This is the last term of the ideal-product sequence of
Stacks 08MP, and the presentation of `ℱ` that Stacks 08MQ consumes. -/
private noncomputable abbrev pullbackModuleOverThickened
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)) :=
  (pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      i.toRingedToposModulesHom).obj F')

omit [HasWeakSheafify S.J AddCommGrpCat] [S.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J AddCommGrpCat] in
/-- **The consequence of Stacks 08MQ that the proof of Stacks 08MT consumes for the source
module.** For a strict morphism of first order thickenings of ringed topoi and an `O'`-module `ℱ'`
flat over `O_{ℬ'}`, the action `I ⊗_{O'} ℱ' ⟶ ℱ'` of the square-zero ideal is injective.

The action is the multiplication map of Stacks 08M4, which factors as the reduction comparison
`I ⊗_{O'} ℱ' ⟶ I ⊗_O ℱ`, the second factor `I ⊗_O ℱ ⟶ I·ℱ'` of the canonical map of
Stacks 08MQ, and the inclusion of `I·ℱ'`. The reduction comparison is invertible because the
ideal is square zero, the inclusion is a monomorphism, and the second factor is invertible by the
final statement of Stacks 08MQ. Flatness of `ℱ` over `O_ℬ`, which Stacks 08MQ asks for, is the
other half of the criterion of Stacks 08M4 applied to the pulled-back thickening of the base, so
it comes from the flatness of `ℱ'` that is assumed; and `ℱ` is presented as the cokernel of the
inclusion of `I·ℱ'` by the sequence of Stacks 08MP. -/
theorem isIdealActionMono (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    IsIdealActionMono i t f f' hi ht comm F' := by
  intro hD hflat
  have hstrict := (isStrictPullbackIdealMap_iff_isStrict i t f f' hi ht comm).mpr hD
  have hq := idealProductSubmodule_unit_comp_zero hi F'
  have hqex := idealProductShortComplex_shortExact hi F'
  have hF := ((isFlat_baseModule_iff i t f f' hi ht comm (pullbackModuleOverThickened i F') F'
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app F') hq hqex hstrict).mp hflat).1
  have key := isFlat_iff_isIso_canonicalMap i t f f' hi ht comm
    (pullbackModuleOverThickened i F') F'
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app F') hq hqex hstrict hF
  have : IsIso (canonicalSecondFactor i hi (pullbackModuleOverThickened i F') F'
      (i.pullbackAdjPushforwardModulesViaComparison.unit.app F') hq hqex) :=
    (key.2 (key.1.mp hflat)).2
  have := isIso_reductionTensorMap_thickening i hi (pullbackModuleOverThickened i F') F'
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app F') hq hqex
  change Mono (multiplicationMap i.fSharp hi.I F' hi.incl)
  rw [← reductionTensorMap_comp_canonicalSecondFactor i hi (pullbackModuleOverThickened i F') F'
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app F') hq hqex]
  infer_instance

/-- **Stacks 08MT, in existential form.** Let `(f, f')` be a strict morphism of first order
thickenings of ringed topoi as in Situation 08M7, let `ℱ'` and `𝒢'` be `O'`-modules flat over
`O_{ℬ'}`, set `ℱ = i^*ℱ'` and `𝒢 = i^*𝒢'`, and let `φ : ℱ ⟶ 𝒢` be an `O`-linear map. There is
an element `o(φ)` of `Ext¹_O(ℱ, f^*𝒥 ⊗_O 𝒢)` whose vanishing is necessary and sufficient for
`φ` to lift to an `O'`-linear map `φ' : ℱ' ⟶ 𝒢'`.

This is `Deformation.ToposThickening.relativeModuleMapObstruction` with its
`Deformation.ToposThickening.IsIdealActionMono` hypothesis supplied by
`Deformation.ToposThickening.isIdealActionMono`. It is stated here rather than there because
that module does not import this one: the proof of the hypothesis uses Stacks 08MT's own
situation. The class itself is `Deformation.ToposThickening.relativeModuleMapObstructionClass`,
and the tagged form is
`Deformation.ToposThickening.relativeModuleMapObstructionClass_eq_zero_iff`. -/
theorem exists_relativeModuleMapObstruction (F' G' : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj G'))
    (φ : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶
      (pullbackModules i.toRingedToposModulesHom).obj G') :
    ∃ o : Abelian.Ext.{e} ((pullbackModules i.toRingedToposModulesHom).obj F')
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
            (basePullbackIdeal t f ht)).obj
          ((pullbackModules i.toRingedToposModulesHom).obj G')) 1,
      o = 0 ↔ Nonempty (ModuleMapLift F' G' φ) :=
  relativeModuleMapObstruction i t f f' hi ht comm F' G' hstrict hF hG
    (isIdealActionMono i t f f' hi ht comm F') φ

/-- **The obstruction class `o(φ)` of Stacks 08MT.** For a strict morphism of first order
thickenings of ringed topoi, `O'`-modules `ℱ'`, `𝒢'` flat over `O_{ℬ'}` and an `O`-linear map
`φ : ℱ = i^*ℱ' ⟶ 𝒢 = i^*𝒢'`, the class `o(φ) ∈ Ext¹_O(ℱ, 𝒢 ⊗_O f^*𝒥)`.

It is the boundary of `φ`, as in the source's proof: pull the defining sequence
`0 ⟶ I·𝒢' ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0` of `𝒢'` back along the adjoint transpose `ℱ' ⟶ i_*𝒢` of `φ`; the
resulting short exact sequence of `O'`-modules stays short exact after `i^*` (this is where the
flatness of `ℱ'` enters, through the final assertion of Stacks 08MQ,
`Deformation.ToposThickening.isIdealActionMono`), and its class in
`Ext¹_O(ℱ, i^*(I·𝒢'))` is carried to `Ext¹_O(ℱ, 𝒢 ⊗_O f^*𝒥)` by the canonical identification
`i^*(I·𝒢') = I·𝒢' ≅ f^*𝒥 ⊗_O 𝒢 ≅ 𝒢 ⊗_O f^*𝒥` of Stacks 08MQ
(`Deformation.ToposThickening.idealProductTensorIso`) and the symmetry of the tensor product. -/
noncomputable def relativeModuleMapObstructionClass
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj G'))
    (φ : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶
      (pullbackModules i.toRingedToposModulesHom).obj G') :
    Abelian.Ext.{e} ((pullbackModules i.toRingedToposModulesHom).obj F')
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
          (basePullbackIdeal t f ht)).obj
        ((pullbackModules i.toRingedToposModulesHom).obj G')) 1 :=
  let L := pullbackModules i.toRingedToposModulesHom
  let R := i.pushforwardModules
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  let ff := (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  letI : R.Faithful := ff.faithful
  letI : R.Full := ff.full
  let Ki := (idealProductModule hi G').val
  let eG : R.obj Ki ≅ (idealProductSubmodule hi G').toSheafOfModules :=
    (idealProductModule hi G').property.some
  have hSq := shortExact_isoComp_f (idealProductShortComplex_shortExact hi G') eG
  let u := adj.homEquiv F' (L.obj G') φ
  have hP := pullback_shortExact hSq u
  letI : IsIso (adj.unit.app (R.obj Ki)) :=
    adj.isIso_unit_app_iff_mem_essImage.2 (R.obj_mem_essImage Ki)
  letI : Mono ((idealAction hi).app F') := isIdealActionMono i t f f' hi ht comm F' hstrict hF
  have hLP := shortExact_map_pullbackModules hi _ hP
  letI : IsIso (adj.counit.app Ki) := inferInstance
  hLP.extClass.comp (Abelian.Ext.mk₀ (asIso (adj.counit.app Ki) ≪≫
    (idealProductTensorIso i t f f' hi ht comm G' hstrict hG).symm ≪≫
    (Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight X.O
      (basePullbackIdeal t f ht)).app (L.obj G')).hom) (add_zero 1)

/-- **Stacks 08MT.** Let `(f, f')` be a strict morphism of first order thickenings of ringed
topoi as in Situation 08M7, let `ℱ'` and `𝒢'` be `O'`-modules flat over `O_{ℬ'}`, set
`ℱ = i^*ℱ'` and `𝒢 = i^*𝒢'`, and let `φ : ℱ ⟶ 𝒢` be an `O`-linear map. The element
`o(φ) ∈ Ext¹_O(ℱ, 𝒢 ⊗_O f^*𝒥)` of `Deformation.ToposThickening.relativeModuleMapObstructionClass`
vanishes if and only if `φ` lifts to an `O'`-linear map `φ' : ℱ' ⟶ 𝒢'`.

The class vanishes exactly when the pulled-back sequence it is the class of splits after `i^*`;
a splitting descends to one before `i^*`, the unit of the adjunction being invertible on a direct
image, and a splitting of the pulled-back sequence is a factorization of the transpose of `φ`
through `𝒢' ⟶ i_*𝒢`, which is a lift of `φ`. -/
@[stacks 08MT]
theorem relativeModuleMapObstructionClass_eq_zero_iff
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj G'))
    (φ : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶
      (pullbackModules i.toRingedToposModulesHom).obj G') :
    relativeModuleMapObstructionClass.{_, _, _, _, _, _, _, _, _, _, _, e} i t f f' hi ht comm F' G'
        hstrict hF hG φ = 0 ↔
      Nonempty (ModuleMapLift F' G' φ) := by
  let L := pullbackModules i.toRingedToposModulesHom
  let R := i.pushforwardModules
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  let ff := (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  let : R.Faithful := ff.faithful
  let : R.Full := ff.full
  let Ki := (idealProductModule hi G').val
  let eG : R.obj Ki ≅ (idealProductSubmodule hi G').toSheafOfModules :=
    (idealProductModule hi G').property.some
  have hSq := shortExact_isoComp_f (idealProductShortComplex_shortExact hi G') eG
  let u := adj.homEquiv F' (L.obj G') φ
  have hP := pullback_shortExact hSq u
  let : IsIso (adj.unit.app (R.obj Ki)) :=
    adj.isIso_unit_app_iff_mem_essImage.2 (R.obj_mem_essImage Ki)
  let : Mono ((idealAction hi).app F') := isIdealActionMono i t f f' hi ht comm F' hstrict hF
  have hLP := shortExact_map_pullbackModules hi _ hP
  let : IsIso (adj.counit.app Ki) := inferInstance
  let ξ : L.obj (R.obj Ki) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
        (basePullbackIdeal t f ht)).obj (L.obj G') :=
    asIso (adj.counit.app Ki) ≪≫
      (idealProductTensorIso i t f f' hi ht comm G' hstrict hG).symm ≪≫
      (Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight X.O
        (basePullbackIdeal t f ht)).app (L.obj G')
  change hLP.extClass.comp (Abelian.Ext.mk₀ ξ.hom) (add_zero 1) = 0 ↔ _
  rw [extClass_comp_mk₀_eq_zero_iff hLP ξ.hom]
  exact (exists_comp_eq_iso_iff_exists_retraction _ ξ).trans
    ((exists_retraction_map_iff adj _).trans
      ((pullback_retraction_iff hSq u).trans
        (nonempty_moduleMapLift_iff_exists_factorization F' G' φ).symm))

end Relative

end Deformation.ToposThickening

end
