module

public import StacksFrontier.Deformation.ToposThickening.FixedActionFlatness
public import StacksFrontier.Deformation.ToposThickening.FlatLiftFixedActionExtension
public import StacksFrontier.Deformation.ToposThickening.FlatLiftIdealTensorBridge
public import StacksFrontier.Deformation.ToposThickening.FlatLiftBaseRingComparison
public import StacksFrontier.Deformation.ToposThickening.FlatLiftPullbackIdealComparison
public import StacksFrontier.Deformation.ToposThickening.IdealComparisonIsoOfFlat

/-!
# The flat-lift dictionary of Stacks 08MQ

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `𝒥 = Ker(t^♯) ⊂ O_{ℬ'}`, and let `ℱ` be an
`O`-module presented on the thickened topos as an `i_*O`-module. For a strict `(f, f')` and `ℱ`
flat over `O_ℬ`, Stacks 08MQ says that a flat lift of `ℱ` forces the canonical map
`f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of condition (1) of Stacks 08MV to be an isomorphism, and that once it
is one the flat lifts of `ℱ` are exactly the extensions of `ℱ` by `I ⊗_O ℱ` of Stacks 08MB whose
canonical action of the square-zero ideal is the identity.

That dictionary is `Deformation.ToposThickening.IsFlatLiftCorrespondence`, and this file
**proves** it, so that it is no longer a hypothesis of Stacks 08MV or of Stacks 08VW.

## Main results

* `Deformation.ToposThickening.isFlat_baseModule_of_fixedActionIdentity`: **the "if" half of
  Stacks 08MQ read per module** — an extension whose canonical action map is the identity has
  flat middle term, granting strictness, flatness of `ℱ` over `O_ℬ` and invertibility of the
  first factor. Unlike
  `Deformation.ToposThickening.isFlatOfFixedActionIdentity_of_comparisons` it does not ask `f'`
  to be flat, which `IsFlatLiftCorrespondence` does not provide.
* `Deformation.ToposThickening.isFlatLiftCorrespondence`: **the dictionary itself.**
* `Deformation.ToposThickening.hasFlatLift_iff_isIso_and_obstruction_eq_zero'`: **Stacks 08MV,
  unconditionally** — the two-condition criterion for the existence of a flat lift, with the
  dictionary supplied rather than assumed.
* `Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero'`: the criterion of
  Stacks 08VW part (1) in the situation of Stacks 08VV, likewise, with the class written for
  `I ⊗_O ℱ`; the tagged form, for `f^*J ⊗_O ℱ`, is
  `Deformation.ToposThickening.hasFlatLift_iff_basePullbackIdeal_obstruction_eq_zero`.

The last two are the statements of
`StacksFrontier/Deformation/ToposThickening/FlatLiftObstruction.lean` with their
`IsFlatLiftCorrespondence` binder discharged. They are stated here rather than there because that
module cannot see this one: the dictionary's proof needs
`Deformation.ToposThickening.shortExact_idealProduct`, which is downstream of it.

## How the proof goes

Stacks 08MQ is `Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap`, stated in the `f⁻¹`
presentation it is proved in; `IsFlatLiftCorrespondence` is stated over `O'` on the thickened
topos. Three comparisons cross between the two presentations, and each is proved elsewhere:

* strictness, `Deformation.ToposThickening.isStrictPullbackIdealMap_iff_isStrict`;
* flatness of `ℱ` over the base,
  `Deformation.ToposThickening.isFlat_reducedBaseModule_of_isFlatOverBase`;
* the canonical map of condition (1),
  `Deformation.ToposThickening.isIso_tensor_pullbackBaseIdealMap_iff_isIso_canonicalFirstFactor`
  together with `Deformation.ToposThickening.pullbackIdealIso_hom_comp_pullbackBaseIdealMap`,
  which identifies `Deformation.ToposThickening.idealTensorComparison` with the first factor of
  Stacks 08MQ.

What remains here is the three clauses themselves. The "moreover" clause of Stacks 08MQ gives
both factors of the canonical map from a flat lift: the first factor is condition (1), and the
second turns the ideal-product sequence of the lift into an extension with action map the
identity (`Deformation.ToposThickening.exists_fixedAction_of_isIso_canonicalSecondFactor`).
Conversely an extension with action map the identity has its ideal-product sequence short exact
(`Deformation.ToposThickening.shortExact_idealProduct`), which is the presentation Stacks 08MQ
consumes, and condition (1) supplies the remaining comparison.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08MV](https://stacks.math.columbia.edu/tag/08MV)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' vS uS wS vS' uS' wS' e

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
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))

include comm

/-- **The "if" half of Stacks 08MQ, read per module.** Granting that the square is strict, that
`ℱ` is flat over `O_ℬ` and that the first factor `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of the canonical map is
an isomorphism, an extension of `ℱ` by `I ⊗_O ℱ` over the thickening whose canonical action of
the square-zero ideal is the identity has middle term flat over `O_{ℬ'}`.

The ideal-product sequence of such an extension is short exact with the extension's own
reduction for its quotient map, which is the presentation Stacks 08MQ consumes, and its second
factor `I ⊗_O ℱ ⟶ I·ℱ'` is invertible; so the canonical map of Stacks 08MQ, being the first
factor followed by the transport around the square and the second factor, is invertible too.

`Deformation.ToposThickening.isFlatOfFixedActionIdentity_of_comparisons` is the same deduction,
but stated through a predicate which also asks `f'` to be flat; that hypothesis is unavailable
in `Deformation.ToposThickening.IsFlatLiftCorrespondence` and is not used here. -/
theorem isFlat_baseModule_of_fixedActionIdentity
    (hstrictP : IsStrictPullbackIdealMap i t f f' hi ht comm)
    (hFred : AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule i t f f' comm F))
    (hcff : IsIso (canonicalFirstFactor i t f f' hi ht comm F))
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0)
    (hE : (extensionActionMap hi E).1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I)) :
    AlgebraicGeometry.SheafOfModules.IsFlat (baseModule f' E.Z.left) := by
  refine ((isFlat_iff_isIso_canonicalMap i t f f' hi ht comm F E.Z.left E.g
    (idealProduct_ι_comp_g_eq_zero hi F E hE) (shortExact_idealProduct hi F E hE)
    hstrictP hFred).1).mpr ?_
  have := hcff
  have := isIso_canonicalSecondFactor hi F E hE
  have := isIso_squareTransportSymm f'.fSharpInverseImage i.fSharp
    (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
    (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
    (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor i.toToposHom).obj
        X.O)).flip.obj F).obj hi.I)
  have : IsIso (squareTransport f'.fSharpInverseImage i.fSharp
      (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
      (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor i.toToposHom).obj
          X.O)).flip.obj F).obj hi.I)) :=
    ⟨⟨squareTransportSymm f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
        (inverseImageReducedStructureMap i t f f' comm)
        (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) _,
      squareTransport_comp_squareTransportSymm _ _ _ _ _ _,
      squareTransportSymm_comp_squareTransport _ _ _ _ _ _⟩⟩
  rw [canonicalMap]
  infer_instance


/-- **The consequence of Stacks 08MQ that the proof of Stacks 08MV consumes.** Granting that the
square is strict and that `ℱ` is flat over `O_ℬ`, a flat lift of `ℱ` forces the canonical map
`f^*𝒥 ⊗ ℱ ⟶ I ⊗ ℱ` to be an isomorphism, and once that map is an isomorphism the flat lifts of
`ℱ` are exactly the extensions of `ℱ` by `I ⊗_O ℱ` of Stacks 08MB whose canonical action of the
square-zero ideal is the identity.

This discharges `Deformation.ToposThickening.IsFlatLiftCorrespondence`, which was carried as a
hypothesis at every consumer of Stacks 08MV and Stacks 08VW. -/
theorem isFlatLiftCorrespondence :
    IsFlatLiftCorrespondence i t f f' hi ht comm F := by
  intro hstrictD hflat
  have hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm :=
    (isStrictPullbackIdealMap_iff_isStrict i t f f' hi ht comm).mpr hstrictD
  have hF : AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule i t f f' comm F) :=
    isFlat_reducedBaseModule_of_isFlatOverBase i t f f' hi ht comm F hflat
  have hITC : IsIso (idealTensorComparison i t f f' hi ht comm F) ↔
      IsIso (canonicalFirstFactor i t f f' hi ht comm F) := by
    have hfac : idealTensorComparison i t f f' hi ht comm F =
        ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj ((SheafOfModules.restrictScalars
            (ringMap i.fSharp)).obj F)).map
            (pullbackIdealIso t f' ht).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
              ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)).map
            (pullbackBaseIdealMap i t f f' hi ht comm) := by
      rw [idealTensorComparison, ← Functor.map_comp,
        pullbackIdealIso_hom_comp_pullbackBaseIdealMap i t f f' hi ht comm]
    have hiso : IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
        ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)).map
          (pullbackIdealIso t f' ht).hom) :=
      Functor.isIso_map_of_isIso _ _ (pullbackIdealIso t f' ht).isIso_hom
    rw [hfac]
    refine Iff.trans
      ⟨fun h ↦ AlgebraicGeometry.RingedSpaceThickening.isIso_of_isIso_comp_left _ _ hiso h,
        fun h ↦ ?_⟩
      (isIso_tensor_pullbackBaseIdealMap_iff_isIso_canonicalFirstFactor i t f f' hi ht comm F)
    exact IsIso.comp_isIso' hiso h
  have hfactors := fun F' q hq hqex (hflat' : AlgebraicGeometry.SheafOfModules.IsFlat
      (baseModule f' F')) ↦
    let h := isFlat_iff_isIso_canonicalMap i t f f' hi ht comm F F' q hq hqex hstrict hF
    h.2 (h.1.mp hflat')
  refine ⟨?_, fun hiso ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨F', q, hq, hflat', hqex⟩
    exact hITC.mpr (hfactors F' q hq hqex hflat').1
  · rintro ⟨F', q, hq, hflat', hqex⟩
    exact exists_fixedAction_of_isIso_canonicalSecondFactor i hi F F' q hq hqex
      (hfactors F' q hq hqex hflat').2
  · rintro ⟨E, hE⟩
    exact ⟨E.Z.left, E.g, idealProduct_ι_comp_g_eq_zero hi F E hE,
      isFlat_baseModule_of_fixedActionIdentity i t f f' hi ht comm F hstrict hF
        (hITC.mp hiso) E hE,
      shortExact_idealProduct hi F E hE⟩

/-- **Stacks 08MV, unconditionally.** Let `(f, f')` be a morphism of first order thickenings of
ringed topoi as in Situation 08M7, strict, and let `ℱ` be an `O`-module flat over `O_ℬ`. Then
`ℱ` has a lift to an `O'`-module flat over `O_{ℬ'}` if and only if the canonical map
`f^*J ⊗ ℱ ⟶ I ⊗ ℱ` is an isomorphism and the obstruction class `o(ℱ, I ⊗_O ℱ, 1)` of
Stacks 08MF vanishes.

This is `Deformation.ToposThickening.hasFlatLift_iff_isIso_and_obstruction_eq_zero` with its
`Deformation.ToposThickening.IsFlatLiftCorrespondence` hypothesis supplied by
`Deformation.ToposThickening.isFlatLiftCorrespondence`. -/
@[stacks 08MV]
theorem hasFlatLift_iff_isIso_and_obstruction_eq_zero'
    [HasExt.{e} (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : IsFlatOverBase i f F) :
    HasFlatLift i f' hi F ↔
      IsIso (idealTensorComparison i t f f' hi ht comm F) ∧
        existenceObstructionClass hi F
            (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor
                i.toToposHom).obj X.O)).flip.obj F).obj hi.I)
            (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor
                i.toToposHom).obj X.O)).flip.obj F).obj
              hi.I)) = 0 :=
  hasFlatLift_iff_isIso_and_obstruction_eq_zero i t f f' hi ht comm F hstrict hflat
    (isFlatLiftCorrespondence i t f f' hi ht comm F)

/-- **Stacks 08VW, part (1), unconditionally.** In the situation of Stacks 08VV — a strict
morphism `(f, f')` of first order thickenings of ringed topoi with `f'` flat, and an `O`-module
`ℱ` flat over `O_ℬ` — the module `ℱ` has a lift to an `O'`-module flat over `O_{ℬ'}` if and only
if the obstruction class `o(ℱ, f^*J ⊗_O ℱ, 1)` of Stacks 08MF vanishes. The class is written
here for `I ⊗_O ℱ`, the two agreeing because `I = f^*J` under these hypotheses.

This is `Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero` with its
`Deformation.ToposThickening.IsFlatLiftCorrespondence` hypothesis supplied by
`Deformation.ToposThickening.isFlatLiftCorrespondence`. -/
theorem hasFlatLift_iff_obstruction_eq_zero'
    [HasExt.{e} (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hf' : f'.IsFlat) (hflat : IsFlatOverBase i f F) :
    HasFlatLift i f' hi F ↔
      existenceObstructionClass hi F
          (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O)).flip.obj F).obj hi.I)
          (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O)).flip.obj F).obj
            hi.I)) = 0 :=
  hasFlatLift_iff_obstruction_eq_zero i t f f' hi ht comm F hstrict hf' hflat
    (isFlatLiftCorrespondence i t f f' hi ht comm F)
    (isIdealComparisonIsoOfFlat i t f f' hi ht comm F)

end Deformation.ToposThickening

end
