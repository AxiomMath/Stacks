module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedToposPullbackLeftExact
public import StacksFrontier.Deformation.ToposThickening.FlatLiftIdealTensorBridge
public import StacksFrontier.Deformation.ToposThickening.FlatLiftPullbackIdealComparison
public import StacksFrontier.Deformation.ToposThickening.FlatLiftTorsors
public import StacksFrontier.Deformation.ToposThickening.IdealProductSequence

/-!
# The ideal product of a flat module is the coefficient module of Stacks 08MR

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`, let the square be
strict (Stacks 08M9) and let `𝒢'` be an `O'`-module flat over `O_{ℬ'}`. This file proves

`f^*J ⊗_O i^*𝒢' ≅ I·𝒢'`,

the identification of the two coefficient modules that the source's one-line proof of
Stacks 08MR — "combine Lemmas 08MP and 08MQ" — appeals to. This is
`Deformation.ToposThickening.IsIdealProductTensorIso`, the argument that
`Deformation.ToposThickening.moduleMapLift_torsor_of_isFlat` takes, proved here.

## Main results

* `Deformation.ToposThickening.idealProductTensorIso`: the canonical isomorphism
  `f^*J ⊗_O i^*𝒢' ≅ I·𝒢'`, built from the canonical maps of Stacks 08MQ.
* `Deformation.ToposThickening.isIdealProductTensorIso`: **the predicate
  `Deformation.ToposThickening.IsIdealProductTensorIso` holds**, with no hypothesis beyond its
  own.
* `Deformation.ToposThickening.exists_addTorsor_moduleMapLift`: **Stacks 08MR** — the lifts of
  a map are a principal homogeneous set under `Hom_O(i^*ℱ', i^*𝒢' ⊗_O f^*J)`, with the action of
  the source: `α` adds the map `ℱ' ⟶ I·𝒢' ⊂ 𝒢'` corresponding to `α` under the canonical
  identification.
* `Deformation.ToposThickening.moduleMapLift_torsor_of_isFlat'`: the statement of
  `StacksFrontier/Deformation/ToposThickening/FlatLiftTorsors.lean` with its 08MQ hypothesis
  discharged; it only asserts that some principal homogeneous structure exists.

## Implementation notes

The two sides of the isomorphism live on the *unthickened* topos `Sh(C)`: the coefficient module
of Stacks 08MR is `f^*J ⊗_O i^*𝒢'` with `f^*J` the module
`Deformation.ToposThickening.basePullbackIdeal` obtained by pulling `J` back along `t` and then
along `f`, and the ideal product is the descent
`Deformation.ToposThickening.idealProductModule` of `I·𝒢'` along the thickening. Stacks 08MQ, on
the other hand, is formalized on the thickened topos `Sh(D)`. The proof therefore pushes the
whole statement forward along `i` and uses that the direct image of modules along a thickening is
fully faithful (Stacks 08M3), so that an isomorphism of direct images descends.

Three inputs carry the passage.

* The direct image along a closed immersion is monoidal in the form
  `𝒢' ⊗_{O'} i_*N ≅ i_*(i^*𝒢' ⊗_O N)`, which is
  `Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isClosedImmersion`. It is applied at
  `N = f^*J`, with the first factor `(f')^*J`: the comparison
  `Deformation.ToposThickening.MorphismOfThickenings.pullbackComparison` of the two iterated
  pullbacks around the square identifies `i^*((f')^*J)` with `f^*J`, so no pullback has to be
  recomputed.
* On the thickened topos, tensoring with `i_*i^*𝒢'` turns the canonical map of defining ideals
  `(f')^*J ⟶ I` into an isomorphism. This is the "moreover" clause of Stacks 08MQ for its first
  factor, transported to the `Stacks.Sheaves.RingedToposModules.pullbackModules` spelling by
  `Deformation.ToposThickening.isIso_tensor_pullbackBaseIdealMap_iff_isIso_canonicalFirstFactor`
  and `Deformation.ToposThickening.pullbackIdealIso_hom_comp_pullbackBaseIdealMap`.
* The second factor `I ⊗_O i^*𝒢' ⟶ I·𝒢'` of the canonical map of Stacks 08MQ is the other
  "moreover" clause, and `I ⊗_{O'} i_*i^*𝒢' = I ⊗_O i^*𝒢'` is
  `Deformation.ToposThickening.isIso_reductionTensorMapStructureRestrict`.

The presentation of `i^*𝒢'` as a module over the direct image `i_*O` that Stacks 08MQ consumes is
the one the unit of `i^* ⊣ i_*` supplies: the sequence `0 ⟶ I·𝒢' ⟶ 𝒢' ⟶ i_*i^*𝒢' ⟶ 0` is short
exact by `Deformation.ToposThickening.idealProductShortComplex_shortExact`, which is exactly the
datum `(q, hq, hqex)` of Stacks 08MQ. Flatness of `i^*𝒢'` over `O_ℬ`, the remaining hypothesis of
08MQ, is not assumed: it is the first half of the flatness criterion of Stacks 08M4,
`Deformation.ToposThickening.isFlat_baseModule_iff`, applied to the flatness of `𝒢'` itself.

## References

* [Stacks Project, Tag 08MR](https://stacks.math.columbia.edu/tag/08MR)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules (pushforwardModules)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u w v' u' vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

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
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]

/-! ### The comparison `f^*J = i^*((f')^*J)`

The pullback along `f'` needs only the weak sheafification of abelian sheaves on `Sh(D)`, which
these declarations take as an instance argument. -/

section PullbackComparison

variable [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S')
  (f : RingedToposHom X S) (f' : RingedToposHom X' S')
  (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))

/-- `i^*𝒢'`, presented on the thickened topos as a module over the direct image `i_*O`. This is
the presentation of the reduction that the extension theory of Stacks 08MB and the flatness
criterion of Stacks 08MQ are stated in. -/
noncomputable abbrev reducedPullbackModule : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)) :=
  (pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
    ((pullbackModules i.toRingedToposModulesHom).obj G')

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The two spellings of `f^*t^*J`: `Deformation.ToposThickening.basePullbackIdeal`, the pullback
along `t.toRingedToposModulesHom` and `f.toRingedToposModulesHom`, is the pullback along
`t.toModulesHom` and `f.toModulesHom`. -/
theorem basePullbackIdeal_eq_pullbackModules_toModulesHom :
    basePullbackIdeal t f ht = (pullbackModules f.toModulesHom).obj
      ((pullbackModules t.toModulesHom).obj ht.idealOfThickening.I) := by
  rw [f.toModulesHom_eq_toRingedToposModulesHom, t.toModulesHom_eq_toRingedToposModulesHom]
  rfl

include comm in
/-- **`f^*J = i^*((f')^*J)`**, the comparison of the two iterated pullbacks of `J` around the
square of Stacks 08M7, read in the spelling
`Stacks.Sheaves.RingedToposModules.pullbackModules` that
`Deformation.ToposThickening.basePullbackIdeal` and the direct-image monoidal comparison use.

`Deformation.ToposThickening.MorphismOfThickenings.pullbackComparison` is the same comparison
over the pullback of the four-field morphism `f'.toModulesHom`; the two pullback functors are
equal, by `AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`. -/
noncomputable def basePullbackIdealIsoPullback :
    basePullbackIdeal t f ht ≅ (pullbackModules i.toRingedToposModulesHom).obj
      ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I) := by
  have key := (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht
    comm).pullbackComparison.app ht.idealOfThickening.I
  rw [← i.toModulesHom_eq_toRingedToposModulesHom]
  exact eqToIso (basePullbackIdeal_eq_pullbackModules_toModulesHom t f ht) ≪≫ key.symm

end PullbackComparison

/-! ### Stacks 08MQ and 08MR

The flatness criteria of Stacks 08M4 and 08MQ applied here assume `HasSheafify` on `Sh(D)`. -/

section LeftExact

variable [HasSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S')
  (f : RingedToposHom X S) (f' : RingedToposHom X' S')
  (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))

include comm in
omit [HasWeakSheafify S.J AddCommGrpCat] [S.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The two "moreover" clauses of Stacks 08MQ for `𝒢'`**, read through the presentation of
`i^*𝒢'` by the unit of `i^* ⊣ i_*`: granting that the square is strict and that `𝒢'` is flat
over `O_{ℬ'}`, each of the two factors `f^*J ⊗_O i^*𝒢' ⟶ I ⊗_O i^*𝒢' ⟶ I·𝒢'` of the canonical
map of Stacks 08MQ is an isomorphism.

The hypothesis of 08MQ that `i^*𝒢'` is flat over `O_ℬ` is not assumed: it is the first half of
the flatness criterion of Stacks 08M4 applied to the flatness of `𝒢'`. -/
theorem isIso_canonicalFactors_of_isFlat
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars (ringMap f'.fSharpInverseImage)).obj G')) :
    IsIso (canonicalFirstFactor i t f f' hi ht comm (reducedPullbackModule i G')) ∧
      IsIso (canonicalSecondFactor i hi (reducedPullbackModule i G') G'
        (i.pullbackAdjPushforwardModulesViaComparison.unit.app G')
        (idealProductSubmodule_unit_comp_zero hi G')
        (idealProductShortComplex_shortExact hi G')) := by
  have hstrictP := (isStrictPullbackIdealMap_iff_isStrict i t f f' hi ht comm).mpr hstrict
  have hq := idealProductSubmodule_unit_comp_zero hi G'
  have hqex := idealProductShortComplex_shortExact hi G'
  have hF := ((isFlat_baseModule_iff i t f f' hi ht comm (reducedPullbackModule i G') G'
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app G') hq hqex hstrictP).mp hflat).1
  have key := isFlat_iff_isIso_canonicalMap i t f f' hi ht comm (reducedPullbackModule i G') G'
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app G') hq hqex hstrictP hF
  exact key.2 (key.1.mp hflat)

include comm in
omit [HasWeakSheafify S.J AddCommGrpCat] [S.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The canonical map `f^*J ⊗ ℱ ⟶ I ⊗ ℱ` of condition (1) of Stacks 08MV is invertible** for
`ℱ = i^*𝒢'`, when the square is strict and `𝒢'` is flat over `O_{ℬ'}`.

It is the map of defining ideals of Stacks 08M7 tensored with `i_*i^*𝒢'`, and the comparison of
its two spellings with the first factor of the canonical map of Stacks 08MQ is
`Deformation.ToposThickening.isIso_tensor_pullbackBaseIdealMap_iff_isIso_canonicalFirstFactor`. -/
theorem isIso_idealTensorComparison_of_isFlat
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars (ringMap f'.fSharpInverseImage)).obj G')) :
    IsIso (idealTensorComparison i t f f' hi ht comm (reducedPullbackModule i G')) := by
  have := (isIso_tensor_pullbackBaseIdealMap_iff_isIso_canonicalFirstFactor i t f f' hi ht comm
    (reducedPullbackModule i G')).mpr
      (isIso_canonicalFactors_of_isFlat i t f f' hi ht comm G' hstrict hflat).1
  have w := Functor.map_comp ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
    ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj (reducedPullbackModule i G')))
    (pullbackIdealIso t f' ht).hom (pullbackBaseIdealMap i t f f' hi ht comm)
  rw [pullbackIdealIso_hom_comp_pullbackBaseIdealMap] at w
  exact cast (congrArg IsIso w.symm) inferInstance

include comm in
/-- **The coefficient module of Stacks 08MR is the ideal product, canonically.** For a strict
morphism of first order thickenings of ringed topoi and an `O'`-module `𝒢'` flat over `O_{ℬ'}`,
the isomorphism `f^*J ⊗_O i^*𝒢' ≅ I·𝒢'` (the target being the descent
`Deformation.ToposThickening.idealProductModule` of `I·𝒢'` to `Sh(C)`) built from the canonical
maps of the source: the direct image along `i` of this isomorphism is the composite of

* the comparison `f^*J = i^*((f')^*J)` of the two iterated pullbacks around the square,
* the monoidal comparison `(f')^*J ⊗_{O'} i_*i^*𝒢' ≅ i_*((f')^*J|_C ⊗_O i^*𝒢')` of the direct
  image along a closed immersion,
* the canonical map `(f')^*J ⊗ i_*i^*𝒢' ⟶ I ⊗ i_*i^*𝒢'` of defining ideals, the reduction
  comparison `I ⊗_{O'} i_*i^*𝒢' = I ⊗_O i^*𝒢'`, and the second factor `I ⊗_O i^*𝒢' ⟶ I·𝒢'` of
  the canonical map of Stacks 08MQ,

and the direct image of modules along the thickening is fully faithful (Stacks 08M3), so this
determines the isomorphism. The maps of defining ideals and the second factor are invertible by
the two "moreover" clauses of Stacks 08MQ, which is where strictness and flatness enter. -/
noncomputable def idealProductTensorIso
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars (ringMap f'.fSharpInverseImage)).obj G')) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
        (basePullbackIdeal t f ht)).obj
      ((pullbackModules i.toRingedToposModulesHom).obj G') ≅ (idealProductModule hi G').val :=
  have ff := (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  have hC := isIso_idealTensorComparison_of_isFlat i t f f' hi ht comm G' hstrict hflat
  have hB := (isIso_canonicalFactors_of_isFlat i t f f' hi ht comm G' hstrict hflat).2
  have hM := isIso_reductionTensorMapStructureRestrict i hi (reducedPullbackModule i G')
  have hP := Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isClosedImmersion i
    hi.isClosedImmersion ⟨hi.surjective.imageSieve_mem⟩
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f'.toModulesHom).obj
      ht.idealOfThickening.I)
    ((pullbackModules i.toRingedToposModulesHom).obj G')
  ff.preimageIso <|
    (i.pushforwardModulesIso.app _).symm ≪≫
    (pushforwardModules i.toRingedToposModulesHom).mapIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
        ((pullbackModules i.toRingedToposModulesHom).obj G')).mapIso
          (basePullbackIdealIsoPullback i t f f' hi ht comm)) ≪≫
    (@asIso _ _ _ _ _ hP).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).obj
      ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f'.toModulesHom).obj
        ht.idealOfThickening.I)).mapIso (i.pushforwardModulesIso.app _) ≪≫
    (@asIso _ _ _ _ _ hC) ≪≫ (@asIso _ _ _ _ _ hM) ≪≫ (@asIso _ _ _ _ _ hB) ≪≫
    ((idealProductModule hi G').property.some).symm

include comm in
/-- **The consequence of Stacks 08MQ that the proof of Stacks 08MR consumes.** For a strict
morphism of first order thickenings of ringed topoi and an `O'`-module `𝒢'` flat over
`O_{ℬ'}`, the coefficient module `f^*J ⊗_O i^*𝒢'` of Stacks 08MR is the ideal product `I·𝒢'`.

The isomorphism is `Deformation.ToposThickening.idealProductTensorIso`. -/
theorem isIdealProductTensorIso : IsIdealProductTensorIso i t f f' hi ht comm G' :=
  fun hstrict hflat => ⟨idealProductTensorIso i t f f' hi ht comm G' hstrict hflat⟩

include comm in
/-- **The bare form of Stacks 08MR.** Let `(f, f')` be a strict morphism of first order
thickenings of ringed topoi as in Situation 08M7, let `ℱ'` and `𝒢'` be `O'`-modules with `𝒢'`
flat over `O_{ℬ'}`, and let `φ : i^*ℱ' ⟶ i^*𝒢'` be a map of `O`-modules. If `φ` has at least one
lift to an `O'`-linear map `ℱ' ⟶ 𝒢'`, then its lifts form a principal homogeneous set under
`Hom_O(i^*ℱ', f^*J ⊗_O i^*𝒢')`.

This is `Deformation.ToposThickening.moduleMapLift_torsor_of_isFlat` with its
`Deformation.ToposThickening.IsIdealProductTensorIso` hypothesis supplied by
`Deformation.ToposThickening.isIdealProductTensorIso`. It is stated here rather than in
`StacksFrontier/Deformation/ToposThickening/FlatLiftTorsors.lean` because that module cannot see
this one. It only asserts that *some* principal homogeneous structure exists; Stacks 08MR with
the action of the source is `Deformation.ToposThickening.exists_addTorsor_moduleMapLift`. -/
theorem moduleMapLift_torsor_of_isFlat'
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj G'))
    (φ : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶
      (pullbackModules i.toRingedToposModulesHom).obj G')
    (hne : Nonempty (ModuleMapLift F' G' φ)) :
    Nonempty (AddTorsor
      ((pullbackModules i.toRingedToposModulesHom).obj F' ⟶
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
            (basePullbackIdeal t f ht)).obj
          ((pullbackModules i.toRingedToposModulesHom).obj G'))
      (ModuleMapLift F' G' φ)) :=
  moduleMapLift_torsor_of_isFlat i t f f' hi ht comm F' G' hstrict hG
    (isIdealProductTensorIso i t f f' hi ht comm G') φ hne

include comm in
/-- **Stacks 08MR.** Let `(f, f')` be a strict morphism of first order thickenings of ringed
topoi as in Situation 08M7, let `ℱ'` and `𝒢'` be `O'`-modules with `𝒢'` flat over `O_{ℬ'}`, set
`ℱ = i^*ℱ'` and `𝒢 = i^*𝒢'`, and let `φ : ℱ ⟶ 𝒢` be a map of `O`-modules. If `φ` has at least
one lift to an `O'`-linear map `φ' : ℱ' ⟶ 𝒢'`, then its lifts form a principal homogeneous set
under `Hom_O(ℱ, 𝒢 ⊗_O f^*J)`.

The action is the one of the source's proof, "combine Lemmas 08MP and 08MQ": an element
`α : ℱ ⟶ 𝒢 ⊗_O f^*J` sends a lift `φ'` to `φ' + ι ∘ α`, where `ι ∘ α : ℱ' ⟶ 𝒢'` is the
`O'`-linear map corresponding to `α` followed by the symmetry `𝒢 ⊗_O f^*J ≅ f^*J ⊗_O 𝒢`, the
canonical identification `f^*J ⊗_O 𝒢 ≅ I·𝒢'` of Stacks 08MQ
(`Deformation.ToposThickening.idealProductTensorIso`) and the inclusion `I·𝒢' ⊂ 𝒢'`.
Concretely, `α` composed with those identifications is a map into the descent of `I·𝒢'`, which
`Deformation.ToposThickening.idealProductHomEquiv` (the adjunction `i^* ⊣ i_*`) reads as a map
`ℱ' ⟶ I·𝒢'`. -/
@[stacks 08MR "The whole statement, under exactly the source's hypotheses (Situation 08M7, \
strict morphism, G' flat over O_{B'}), with the action of the source pinned: α sends φ' to \
φ' + ι ∘ α, read in I·G' through the canonical isomorphism of 08MQ."]
theorem exists_addTorsor_moduleMapLift
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars (ringMap f'.fSharpInverseImage)).obj G'))
    (φ : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶
      (pullbackModules i.toRingedToposModulesHom).obj G')
    (hne : Nonempty (ModuleMapLift F' G' φ)) :
    ∃ T : AddTorsor
        ((pullbackModules i.toRingedToposModulesHom).obj F' ⟶
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).flip.obj
              (basePullbackIdeal t f ht)).obj
            ((pullbackModules i.toRingedToposModulesHom).obj G'))
        (ModuleMapLift F' G' φ),
      ∀ (α : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).flip.obj
              (basePullbackIdeal t f ht)).obj
            ((pullbackModules i.toRingedToposModulesHom).obj G'))
        (φ' : ModuleMapLift F' G' φ),
        (T.vadd α φ').val = φ'.val +
          idealProductHomEquiv hi F' G'
              (α ≫ ((Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight X.O
                  (basePullbackIdeal t f ht)).app
                  ((pullbackModules i.toRingedToposModulesHom).obj G')).inv ≫
                (idealProductTensorIso i t f f' hi ht comm G' hstrict hG).hom) ≫
            (idealProductSubmodule hi G').ι := by
  obtain ⟨T, hT⟩ := moduleMapLift_torsor hi F' G' φ hne
  let := T
  exact ⟨addTorsorCongr
    (homAddEquivOfIso (((Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight X.O
        (basePullbackIdeal t f ht)).app
        ((pullbackModules i.toRingedToposModulesHom).obj G')).symm ≪≫
      idealProductTensorIso i t f f' hi ht comm G' hstrict hG))
    (Equiv.refl _), fun α φ' => hT _ φ'⟩

end LeftExact

end Deformation.ToposThickening

end
