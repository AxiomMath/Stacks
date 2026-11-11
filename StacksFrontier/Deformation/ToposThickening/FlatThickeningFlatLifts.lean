module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftClassTorsor
public import StacksFrontier.Deformation.ToposThickening.FlatLiftClassesAndAutomorphisms
public import StacksFrontier.Deformation.ToposThickening.FlatLiftCorrespondence

/-!
# Flat lifts of a module over a flat thickening (Stacks 08VW)

Consider Situation 08VV: a commutative square of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

whose horizontal arrows are first order thickenings, with `I = Ker(i^♯)` and `J = Ker(t^♯)`,
such that `(f, f')` is strict, `f'` is flat, and an `O`-module `ℱ` flat over `O_ℬ`. Then
`I = f^*J`, and Stacks 08VW says:

1. `ℱ` has a lift to an `O'`-module flat over `O_{ℬ'}` iff the class
   `o(ℱ, f^*J ⊗_O ℱ, 1) ∈ Ext²_O(ℱ, f^*J ⊗_O ℱ)` of Stacks 08MF vanishes;
2. if a lift exists, the isomorphism classes of lifts form a principal homogeneous set under
   `Ext¹_O(ℱ, f^*J ⊗_O ℱ)`;
3. the automorphisms of a lift `ℱ'` pulling back to `id_ℱ` are canonically
   `Ext⁰_O(ℱ, f^*J ⊗_O ℱ)`.

This file states the three parts with the coefficient module `f^*J ⊗_O ℱ` of the source.

## Main definitions

* `Deformation.ToposThickening.basePullbackIdealOverThickened`: the `O`-module `f^*J`, presented
  on the thickened topos as a module over `i_*O`.
* `Deformation.ToposThickening.basePullbackIdealIsoIdeal`: the identification `f^*J ≅ I` of
  Situation 08VV, as modules over `i_*O`, built from the canonical map of defining ideals.
* `Deformation.ToposThickening.basePullbackIdealTensorIso`: its tensor product with `ℱ`,
  `f^*J ⊗_O ℱ ≅ I ⊗_O ℱ`.
* `Deformation.ToposThickening.autOverIdentityExtZeroEquiv`: the canonical bijection of part (3).

## Main results

* `Deformation.ToposThickening.hasFlatLift_iff_basePullbackIdeal_obstruction_eq_zero`:
  **Stacks 08VW, part (1)**.
* `Deformation.ToposThickening.exists_addTorsor_flatLiftClass_basePullbackIdeal`:
  **Stacks 08VW, part (2)**, with the action pinned down.
* `Deformation.ToposThickening.autOverIdentityExtZeroEquiv_spec`: **Stacks 08VW, part (3)**: the
  bijection is `α ↦ 1 + α` and carries addition to composition.

## Implementation notes

The source's proof is "part (1) follows from 08MV as `I = f^*J`, part (2) from 08MU, part (3)
from 08MR", and that is how the proofs go.

* The identification `I = f^*J` is the canonical map of defining ideals `(f')^*J ⟶ I` of
  Situation 08M7, which is invertible for a strict square with flat `f'`
  (`Deformation.ToposThickening.MorphismOfThickenings.isIso_idealMap`), carried across
  `f^*J = i^*((f')^*J)` (`Deformation.ToposThickening.basePullbackIdealIsoPullback`) and the
  unit of `i^* ⊣ i_*`, which is invertible at `I` because the ideal annihilates `I`
  (Stacks 08M3). Restriction of scalars along `O' ⟶ i_*O` is fully faithful, so the resulting
  isomorphism of `O'`-modules is one of `i_*O`-modules.
* In part (1) the class `o(ℱ, f^*J ⊗_O ℱ, 1)` of the source is the class of Stacks 08MF for the
  coefficient module `f^*J ⊗_O ℱ` and the action `I ⊗_O ℱ ⟶ f^*J ⊗_O ℱ` that is the identity
  under `I = f^*J`, i.e. the inverse of `basePullbackIdealTensorIso`. The class is natural in the
  coefficient module (`Deformation.ToposThickening.existenceObstructionClass_comp`), so it is the
  image of the class `o(ℱ, I ⊗_O ℱ, 1)` of Stacks 08MV, whose vanishing is the existence of a
  flat lift once `I = f^*J`: that is
  `Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero'`, Stacks 08MV
  (`Deformation.ToposThickening.hasFlatLift_iff_isIso_and_obstruction_eq_zero'`) with its
  condition (1) supplied by `Deformation.ToposThickening.isIdealComparisonIsoOfFlat`.
* In part (2) the torsor of Stacks 08MU
  (`Deformation.ToposThickening.exists_addTorsor_flatLiftClass`) is transported along the
  isomorphism of `Ext¹` groups induced by `f^*J ⊗_O ℱ ≅ I ⊗_O ℱ`.
* In part (3) the identification is Stacks 08MP at the identity, `α ↦ 1 + α`
  (`Deformation.ToposThickening.autOverIdentityEquiv`), composed with the canonical
  identification `f^*J ⊗_O ℱ ≅ I·ℱ'` of Stacks 08MQ
  (`Deformation.ToposThickening.idealProductTensorIso`); this is Stacks 08MR
  (`Deformation.ToposThickening.exists_addTorsor_moduleMapLift`) at `φ = id_ℱ`, with every lift
  of the identity an automorphism by the square-zero argument
  (`Deformation.ToposThickening.isIso_of_pullbackModules_map_eq_id`). The module `ℱ` of the
  source is written `i^*ℱ'`, which the lift identifies with `ℱ`.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08VV](https://stacks.math.columbia.edu/tag/08VV)
* [Stacks Project, Tag 08MV](https://stacks.math.columbia.edu/tag/08MV)
* [Stacks Project, Tag 08MU](https://stacks.math.columbia.edu/tag/08MU)
* [Stacks Project, Tag 08MR](https://stacks.math.columbia.edu/tag/08MR)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)

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
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)

/-- The `O`-module `f^*J` (`Deformation.ToposThickening.basePullbackIdeal`), read on the thickened
topos as a module over the direct image `i_*O`. -/
noncomputable abbrev basePullbackIdealOverThickened : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)) :=
  (pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
    (basePullbackIdeal t f ht)

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The unit of `i^* ⊣ i_*` is invertible at the square-zero ideal `I`.** The ideal acts by
zero on `I`, so `I` lies in the essential image of the direct image of modules along the
thickening (Stacks 08M3), which is fully faithful. -/
theorem isIso_unit_app_ideal :
    IsIso (i.pullbackAdjPushforwardModulesViaComparison.unit.app hi.idealOfThickening.I) := by
  let Sc := hi.closedRingedImmersion
  have ff := (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful Sc).some
  have : i.pushforwardModules.Full := ff.full
  have : i.pushforwardModules.Faithful := ff.faithful
  refine i.pullbackAdjPushforwardModulesViaComparison.isIso_unit_app_iff_mem_essImage.2
    ((AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates
      Sc _).2 ?_)
  intro U a ha m
  have haKer : a ∈ RingHom.ker ((Sc.hom.fSharp.hom.app U).hom) := by
    rwa [← AlgebraicGeometry.ClosedRingedImmersion.ideal_obj Sc U]
  have hker : i.fSharp.hom.app U a = 0 := (RingHom.mem_ker).mp haKer
  change (show (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U from
      i.fSharp.hom.app U a) • (show hi.I.val.obj U from m) = 0
  rw [hker]
  exact zero_smul _ _

include comm in
/-- **`f^*J = I` in Situation 08VV.** For a strict morphism of first order thickenings whose
vertical arrow `f'` is flat, the canonical isomorphism `f^*J ≅ I` of modules over `i_*O`: after
restriction of scalars to `O'` it is the direct image of `f^*J = i^*((f')^*J) ≅ i^*I`, the
second map being the canonical map of defining ideals of Situation 08M7 (invertible by
`Deformation.ToposThickening.MorphismOfThickenings.isIso_idealMap`), followed by the inverse of
the unit `I ⟶ i_*i^*I`. Restriction of scalars along `O' ⟶ i_*O` is fully faithful, which
determines the isomorphism. -/
noncomputable def basePullbackIdealIsoIdeal (hf' : f'.IsFlat)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict) :
    basePullbackIdealOverThickened i t f ht ≅ hi.I :=
  have hJ := (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).isIso_idealMap
    hf' hstrict
  have hu := isIso_unit_app_ideal i hi
  hi.restrictScalarsFullyFaithful.preimageIso <|
    i.pushforwardModules.mapIso (basePullbackIdealIsoPullback i t f f' hi ht comm ≪≫
      (pullbackModules i.toRingedToposModulesHom).mapIso (@asIso _ _ _ _ _ hJ)) ≪≫
    (@asIso _ _ _ _ _ hu).symm

include comm in
/-- **`f^*J ⊗_O ℱ = I ⊗_O ℱ` in Situation 08VV**: the identification
`Deformation.ToposThickening.basePullbackIdealIsoIdeal` tensored with `ℱ`. -/
noncomputable def basePullbackIdealTensorIso (hf' : f'.IsFlat)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
        (basePullbackIdealOverThickened i t f ht) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).mapIso
      (basePullbackIdealIsoIdeal i t f f' hi ht comm hf' hstrict)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The obstruction class of Stacks 08MF is natural in the coefficient module.** Composing the
prescribed action `c : I ⊗_O ℱ ⟶ K` with `g : K ⟶ L` composes the class with `g`: both classes
are computed from one presentation, as the Yoneda product of its universal class with the
action (`Deformation.ToposThickening.existenceObstructionClass_eq_obstruction`). -/
theorem existenceObstructionClass_comp
    [HasExt.{e} (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (F K L : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : idealTensorModule hi F ⟶ K) (g : K ⟶ L) :
    existenceObstructionClass hi F L (c ≫ g) =
      (existenceObstructionClass hi F K c).comp (Abelian.Ext.mk₀ g) (add_zero 2) := by
  obtain ⟨Q, E, ⟨P⟩⟩ := exists_extension_monoActionPresentation hi F
  rw [existenceObstructionClass_eq_obstruction hi F L _ P,
    existenceObstructionClass_eq_obstruction hi F K c P]
  change P.universalClass.comp (Abelian.Ext.mk₀ (c ≫ g)) (add_zero 2) =
    (P.universalClass.comp (Abelian.Ext.mk₀ c) (add_zero 2)).comp (Abelian.Ext.mk₀ g) (add_zero 2)
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

/-- Composition with the morphism underlying an isomorphism is an additive equivalence of `Ext`
groups. -/
private noncomputable def extCompIsoAddEquiv {C : Type*} [Category C] [Abelian C]
    [HasExt.{e} C] {K L : C} (ι : K ≅ L) (F : C) (n : ℕ) :
    Abelian.Ext.{e} F K n ≃+ Abelian.Ext.{e} F L n where
  toFun x := x.comp (Abelian.Ext.mk₀ ι.hom) (add_zero n)
  invFun x := x.comp (Abelian.Ext.mk₀ ι.inv) (add_zero n)
  left_inv x := by
    simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id, Abelian.Ext.comp_mk₀_id]
  right_inv x := by
    simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id, Abelian.Ext.comp_mk₀_id]
  map_add' x y := Abelian.Ext.add_comp _ _ _ _

include comm in
/-- **Stacks 08VW, part (1).** In Situation 08VV — `(f, f')` a strict morphism of first order
thickenings of ringed topoi with `f'` flat, and `ℱ` an `O`-module flat over `O_ℬ` — there is an
`O'`-module `ℱ'` flat over `O_{ℬ'}` with `i^*ℱ' ≅ ℱ` if and only if the class
`o(ℱ, f^*J ⊗_O ℱ, 1) ∈ Ext²_O(ℱ, f^*J ⊗_O ℱ)` of Stacks 08MF vanishes.

Here `1` is the action `I ⊗_O ℱ ⟶ f^*J ⊗_O ℱ` which is the identity under the identification
`I = f^*J` of Situation 08VV, i.e. the inverse of
`Deformation.ToposThickening.basePullbackIdealTensorIso`. -/
@[stacks 08VW "part (1): a flat lift exists iff o(ℱ, f^*J ⊗_O ℱ, 1) vanishes"]
theorem hasFlatLift_iff_basePullbackIdeal_obstruction_eq_zero
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasExt.{e} (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hf' : f'.IsFlat) (hflat : IsFlatOverBase i f F) :
    HasFlatLift i f' hi F ↔
      existenceObstructionClass hi F
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
          (basePullbackIdealOverThickened i t f ht))
        (basePullbackIdealTensorIso i t f f' hi ht comm hf' hstrict F).inv = 0 := by
  rw [hasFlatLift_iff_obstruction_eq_zero' i t f f' hi ht comm F hstrict hf' hflat,
    ← Category.id_comp (basePullbackIdealTensorIso i t f f' hi ht comm hf' hstrict F).inv,
    existenceObstructionClass_comp]
  exact (map_eq_zero_iff (extCompIsoAddEquiv (basePullbackIdealTensorIso i t f f' hi ht comm
    hf' hstrict F).symm F 2) (EquivLike.injective _)).symm

include comm in
/-- **Stacks 08VW, part (2).** In Situation 08VV, if `ℱ` has a lift to an `O'`-module flat over
`O_{ℬ'}`, then the isomorphism classes of such lifts form a principal homogeneous set under
`Ext¹_O(ℱ, f^*J ⊗_O ℱ)`.

The action is the one of Stacks 08MU, read through the identification `f^*J ⊗_O ℱ ≅ I ⊗_O ℱ`
(`Deformation.ToposThickening.basePullbackIdealTensorIso`): a lift `ℱ'` gives the extension
`0 ⟶ I ⊗_O ℱ ⟶ ℱ' ⟶ ℱ ⟶ 0` of `O'`-modules
(`Deformation.ToposThickening.FlatLift.fixedActionExtension`), and `a` sends the class of `ℱ'` to
the class of `𝒢'` exactly when the `Ext¹_{O'}` class of the extension of `𝒢'` is that of `ℱ'` plus
the image of `a` in `Ext¹_{O'}(ℱ, I ⊗_O ℱ)`. -/
@[stacks 08VW "part (2): the lift classes are a torsor under Ext¹_O(ℱ, f^*J ⊗_O ℱ)"]
theorem exists_addTorsor_flatLiftClass_basePullbackIdeal
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasExt.{e} (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hf' : f'.IsFlat) (hflat : IsFlatOverBase i f F) (hne : Nonempty (FlatLift i f' hi F)) :
    ∃ T : AddTorsor
        (Abelian.Ext.{e} F
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
            (basePullbackIdealOverThickened i t f ht)) 1)
        (FlatLiftClass i f' hi F),
      ∀ (a : Abelian.Ext.{e} F
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
            (basePullbackIdealOverThickened i t f ht)) 1)
        (A B : FlatLift i f' hi F),
        T.vadd a (Quotient.mk (flatLiftSetoid i f' hi F) A) =
            Quotient.mk (flatLiftSetoid i f' hi F) B ↔
          extensionClass F
              (((Stacks.SheafOfModules.Tensor.sheafTensor
                ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I)
              (B.fixedActionExtension i t f f' hi ht comm F
                ((isStrictPullbackIdealMap_iff_isStrict i t f f' hi ht comm).mpr hstrict)
                (isFlat_reducedBaseModule_of_isFlatOverBase i t f f' hi ht comm F hflat)) =
            (SheafOfModules.restrictScalars (structureRingMap i)).mapExtAddHom F
                (((Stacks.SheafOfModules.Tensor.sheafTensor
                  ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I) 1
                (a.comp (Abelian.Ext.mk₀
                  (basePullbackIdealTensorIso i t f f' hi ht comm hf' hstrict F).hom)
                  (add_zero 1)) +
              extensionClass F
                (((Stacks.SheafOfModules.Tensor.sheafTensor
                  ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I)
                (A.fixedActionExtension i t f f' hi ht comm F
                  ((isStrictPullbackIdealMap_iff_isStrict i t f f' hi ht comm).mpr hstrict)
                  (isFlat_reducedBaseModule_of_isFlatOverBase i t f f' hi ht comm F hflat)) := by
  obtain ⟨T, hT⟩ := exists_addTorsor_flatLiftClass i t f f' hi ht comm F hstrict hflat hne
  let ι := basePullbackIdealTensorIso i t f f' hi ht comm hf' hstrict F
  let g := extCompIsoAddEquiv ι F 1
  let := T
  exact ⟨addTorsorCongr g (Equiv.refl _), fun a A B => hT (g a) A B⟩

section FlatLiftAutomorphisms

include comm in
/-- **The canonical identification of part (3) of Stacks 08VW.** For a lift `ℱ'` of `ℱ` flat
over `O_{ℬ'}`, the bijection from `Ext⁰_O(i^*ℱ', f^*J ⊗_O i^*ℱ')` to the automorphisms of `ℱ'`
pulling back to the identity, `α ↦ 1 + α`: the map `α : i^*ℱ' ⟶ f^*J ⊗_O i^*ℱ'` is carried by
the canonical identification `f^*J ⊗_O i^*ℱ' ≅ I·ℱ'` of Stacks 08MQ
(`Deformation.ToposThickening.idealProductTensorIso`) to a map into the ideal product, read as a
map `ℱ' ⟶ I·ℱ' ⊂ ℱ'` by the adjunction, and added to the identity
(`Deformation.ToposThickening.autOverIdentityEquiv`, Stacks 08MP at the identity). -/
noncomputable def autOverIdentityExtZeroEquiv
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (L : FlatLift i f' hi F) :
    Abelian.Ext.{e} ((pullbackModules i.toRingedToposModulesHom).obj L.module')
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
            ((pullbackModules i.toRingedToposModulesHom).obj L.module')).obj
            (basePullbackIdeal t f ht)) 0 ≃
      AutOverIdentity i L.module' :=
  (Abelian.Ext.addEquiv₀.trans (homAddEquivOfIso
    (T := (pullbackModules i.toRingedToposModulesHom).obj L.module')
    (idealProductTensorIso i t f f' hi ht comm L.module' hstrict L.isFlat))).toEquiv.trans
    (autOverIdentityEquiv hi L.module')

/-- **Stacks 08VW, part (3).** In Situation 08VV, given a lift `ℱ'` of `ℱ` to an `O'`-module flat
over `O_{ℬ'}`, the set of automorphisms of `ℱ'` which pull back to the identity of `ℱ` is
canonically isomorphic to `Ext⁰_O(ℱ, f^*J ⊗_O ℱ)` (with `ℱ` written as `i^*ℱ'`): the bijection
`Deformation.ToposThickening.autOverIdentityExtZeroEquiv` sends `α` to `1 + α`, and it carries
addition to composition, so it is an isomorphism of groups. -/
@[stacks 08VW "part (3): automorphisms of a lift over id_ℱ are Ext⁰_O(ℱ, f^*J ⊗_O ℱ)"]
theorem autOverIdentityExtZeroEquiv_spec
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (L : FlatLift i f' hi F) :
    (∀ α, (autOverIdentityExtZeroEquiv.{_, _, _, _, _, _, _, _, _, _, _, e} i t f f' hi ht comm F
        hstrict L α).val.hom =
      𝟙 L.module' + idealProductHomEquiv hi L.module' L.module'
          (Abelian.Ext.addEquiv₀ α ≫
            (idealProductTensorIso i t f f' hi ht comm L.module' hstrict L.isFlat).hom) ≫
        (idealProductSubmodule hi L.module').ι) ∧
    ∀ α β, autOverIdentityExtZeroEquiv i t f f' hi ht comm F hstrict L (α + β) =
      autOverIdentityExtZeroEquiv i t f f' hi ht comm F hstrict L α *
        autOverIdentityExtZeroEquiv i t f f' hi ht comm F hstrict L β := by
  let B := Abelian.Ext.addEquiv₀.trans (homAddEquivOfIso
    (T := (pullbackModules i.toRingedToposModulesHom).obj L.module')
    (idealProductTensorIso i t f f' hi ht comm L.module' hstrict L.isFlat))
  refine ⟨fun α => rfl, fun α β => Subtype.ext ?_⟩
  change (autOverIdentityEquiv hi L.module' (B (α + β))).val =
    (autOverIdentityEquiv hi L.module' (B α)).val ≪≫
      (autOverIdentityEquiv hi L.module' (B β)).val
  rw [map_add, autOverIdentityEquiv_add]

end FlatLiftAutomorphisms

end Deformation.ToposThickening

end
