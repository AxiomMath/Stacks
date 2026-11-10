module

public import StacksFrontier.Deformation.ToposThickening.StrictFlatIdealMap
public import StacksFrontier.Deformation.ToposThickening.FlatLiftClassCorrespondence
public import StacksFrontier.Deformation.ToposThickening.FlatLiftTorsors
public import StacksFrontier.Deformation.ToposThickening.IdealProductTensorIso

/-!
# The flat lifts of a module over a flat thickening: classes and automorphisms

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`, suppose the square is
strict and `f'` flat, and let `ℱ` be an `O`-module flat over `O_ℬ`. This is Situation 08VV, and
this file records the parts (2) and (3) of Stacks 08VW for it: the isomorphism classes of flat
lifts of `ℱ` form a principal homogeneous set under `Ext¹_O(ℱ, f^*J ⊗_O ℱ)`, and the
automorphisms of a given lift that pull back to the identity of `ℱ` are `Ext⁰_O(ℱ, f^*J ⊗_O ℱ)`.
Part (1), the existence criterion, is
`Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero'` in
`StacksFrontier/Deformation/ToposThickening/FlatLiftCorrespondence.lean`.

## Main definitions

* `Deformation.ToposThickening.AutOverIdentity`: the automorphisms of an `O'`-module that pull
  back to the identity across the thickening.
* `Deformation.ToposThickening.AutOverIdentity.instGroup`: they are a group under composition,
  which is the group the source's part (3) identifies with `Ext⁰`.
* `Deformation.ToposThickening.autOverIdentityHom`: the endomorphism `1 + α` attached to a map
  `α : i^*ℱ' ⟶ I·ℱ'`.
* `Deformation.ToposThickening.autOverIdentityEquiv`: those maps are exactly those
  automorphisms.

## Main results

* `Deformation.ToposThickening.idealProduct_ι_comp_eq_zero`: every map into an ideal product
  `I·𝒢'` kills the ideal product `I·ℱ'` of its source.
* `Deformation.ToposThickening.isIso_of_pullbackModules_map_eq_id`: an endomorphism of an
  `O'`-module whose pullback across the thickening is the identity is an automorphism.
* `Deformation.ToposThickening.autOverIdentityEquiv_add`: that identification carries addition
  to composition.
* `Deformation.ToposThickening.flatLiftClass_torsor_of_isFlat`: Stacks 08VW, part (2), with the
  coefficient group written for `I ⊗_O ℱ` and only the existence of some principal homogeneous
  structure.
* `Deformation.ToposThickening.autOverIdentity_equiv_extZero`: Stacks 08VW, part (3), with the
  bijection existentially quantified.

The tagged forms of parts (2) and (3), with the action and the bijection of the source and the
coefficient module `f^*J ⊗_O ℱ`, are in
`StacksFrontier/Deformation/ToposThickening/FlatThickeningFlatLifts.lean`.

## Implementation notes

The vocabulary is the one of
`StacksFrontier/Deformation/ToposThickening/FlatLiftObstruction.lean` and
`StacksFrontier/Deformation/ToposThickening/FlatLiftTorsors.lean` and no second copy of it is
introduced: the square is
`Deformation.ToposThickening.MorphismOfThickenings.ofFirstOrderThickenings`, modules over `O` are
presented on the thickened topos `Sh(D)` as modules over the direct image `i_*O`, a flat lift is
`Deformation.ToposThickening.FlatLift`, and its isomorphism classes are
`Deformation.ToposThickening.FlatLiftClass`.

Part (2) is part (2) of the source, which is Stacks 08MU read in Situation 08VV. Stacks 08MU is
`Deformation.ToposThickening.flatLiftClass_torsor` and gives the principal homogeneous structure
under `Ext¹_O(ℱ, I ⊗_O ℱ)`; what Situation 08VV adds is the identification `I = f^*J`, which is
recorded here as the first two parts of the conclusion: in the ideals themselves, as
invertibility of `Deformation.ToposThickening.MorphismOfThickenings.idealMap`, and in the
tensored form `Deformation.ToposThickening.idealTensorComparison` that the development uses
throughout. So the coefficient group is written for `I ⊗_O ℱ` and the conclusion says in the
same breath that this module is `f^*J ⊗_O ℱ`; this is the reading of part (1) in
`Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero'`, whose obstruction class is
written for `I ⊗_O ℱ` for the same reason.

Part (3) is stated with its coefficient module in the source's own form: `f^*J` is
`Deformation.ToposThickening.basePullbackIdeal`, an `O`-module on `Sh(C)`, and the module `ℱ` of
the source is `i^*ℱ'`, which the lift identifies with `ℱ`. The source's proof of part (3) quotes
Stacks 08MR, whose own proof is "combine Stacks 08MP and Stacks 08MQ"; both steps are taken here,
the 08MQ step through the proved `Deformation.ToposThickening.isIdealProductTensorIso`, and 08MP
is used at the identity rather than through
`Deformation.ToposThickening.moduleMapLift_torsor_of_isFlat`, because the identity is a base point
and what the source claims is a *canonical* identification, not the existence of a principal
homogeneous structure.

* `Deformation.ToposThickening.autOverIdentityEquiv` is that identification:
  `α ↦ 1 + α`, where a map `α : i^*ℱ' ⟶ I·ℱ'` is read as a map `ℱ' ⟶ I·ℱ'` by
  `Deformation.ToposThickening.idealProductHomEquiv`, the dictionary Stacks 08MP is proved
  through, and then included into `ℱ'`. It is a bijection onto
  `Deformation.ToposThickening.AutOverIdentity` because the inclusion of the ideal product is a
  monomorphism and because the difference of a lift of the identity and the identity factors
  through that inclusion, by
  `Deformation.ToposThickening.idealProductSubmodule_factors_through`. It carries addition to
  composition, `Deformation.ToposThickening.autOverIdentityEquiv_add`, so it is an isomorphism of
  groups, and `Ext⁰` is the group of maps by `CategoryTheory.Abelian.Ext.addEquiv₀`.
* That the lifts of `id_{i^*ℱ'}` really are *automorphisms* is
  `Deformation.ToposThickening.isIso_of_pullbackModules_map_eq_id`, the square-zero nilpotence
  argument: such a lift is `1 + ε` with `ε` factoring through the inclusion `I·ℱ' ⟶ ℱ'`, and
  `ε ≫ ε = 0` because the factoring map `ℱ' ⟶ I·ℱ'` kills `I·ℱ'`. The last point is
  `Deformation.ToposThickening.idealProduct_ι_comp_eq_zero`: the ideal product is a direct image,
  so a map into it factors through the unit of the adjunction of Stacks 03D7, and the unit kills
  the ideal product by `Deformation.ToposThickening.idealProductSubmodule_unit_comp_zero`. Hence
  `1 + ε` has the inverse `1 - ε`.

## Scope

Neither result below carries a hypothesis standing in for Stacks 08MQ: every consequence of
08MQ that the two proofs consume is now proved in the library, without 08MQ itself, and is
supplied here rather than assumed.

* The class-level flat-lift dictionary that part (2) consumes,
  `Deformation.ToposThickening.IsFlatLiftClassCorrespondence`, is proved by
  `Deformation.ToposThickening.isFlatLiftClassCorrespondence`, and is supplied at Stacks 08MU
  itself, `Deformation.ToposThickening.flatLiftClass_torsor`, which therefore carries no 08MQ
  hypothesis either.
* The identification `I = f^*J` of Situation 08VV, also consumed by part (2), is proved by
  `Deformation.ToposThickening.MorphismOfThickenings.isIso_idealMap` in the ideals and by
  `Deformation.ToposThickening.isIdealComparisonIsoOfFlat` on the coefficient module.
* The consequence that part (3) consumes,
  `Deformation.ToposThickening.IsIdealProductTensorIso`, is proved by
  `Deformation.ToposThickening.isIdealProductTensorIso`.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08VV](https://stacks.math.columbia.edu/tag/08VV)
* [Stacks Project, Tag 08MU](https://stacks.math.columbia.edu/tag/08MU)
* [Stacks Project, Tag 08MR](https://stacks.math.columbia.edu/tag/08MR)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)
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
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]

/-! ### Stacks 08VW, part (2): the isomorphism classes of flat lifts -/

section FlatLiftClassTorsor

variable [HasSheafify X'.J AddCommGrpCat.{w}]

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}] in
/-- **Stacks 08VW, part (2).** In the situation of Stacks 08VV — a strict morphism `(f, f')` of
first order thickenings of ringed topoi with `f'` flat, and an `O`-module `ℱ` flat over `O_ℬ` — if
`ℱ` has at least one lift to an `O'`-module flat over `O_{ℬ'}`, then the isomorphism classes of
such lifts form a principal homogeneous set under `Ext¹_O(ℱ, f^*J ⊗_O ℱ)`.

The conclusion has three parts, and the first two are the identification `I = f^*J` that
Situation 08VV makes: the canonical map of defining ideals `f^*J ⟶ I` is an isomorphism, and so
is the map `f^*J ⊗_O ℱ ⟶ I ⊗_O ℱ` it induces on the coefficient module. The third is the
principal homogeneous structure, whose coefficient group is written for `I ⊗_O ℱ`; that is the
convention of part (1) in
`Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero'`, and the first two parts are
what license the source's substitution of `f^*J ⊗_O ℱ` for it. The principal homogeneous
structure itself is Stacks 08MU, `Deformation.ToposThickening.flatLiftClass_torsor`, which is
what the source's proof of part (2) quotes. -/
theorem flatLiftClass_torsor_of_isFlat (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasExt.{e} (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hf' : f'.IsFlat) (hflat : IsFlatOverBase i f F)
    (hne : Nonempty (FlatLift i f' hi F)) :
    IsIso (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap ∧
      IsIso (idealTensorComparison i t f f' hi ht comm F) ∧
        Nonempty (AddTorsor
          (Abelian.Ext.{e} F
            (((Stacks.SheafOfModules.Tensor.sheafTensor
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I) 1)
          (FlatLiftClass i f' hi F)) :=
  ⟨(MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).isIso_idealMap hf' hstrict,
    isIdealComparisonIsoOfFlat i t f f' hi ht comm F hf' hstrict,
    flatLiftClass_torsor i t f f' hi ht comm F hstrict hflat
      (isFlatLiftClassCorrespondence.{_, _, _, _, _, _, _, _, _, _, _, e}
        i t f f' hi ht comm F) hne⟩

end FlatLiftClassTorsor

/-! ### Endomorphisms lifting the identity -/

section LiftAutomorphisms

variable {i : RingedToposHom X X'}

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **A map into an ideal product kills the ideal product of its source.** The ideal product
`I·𝒢'` is a direct image, `Deformation.ToposThickening.idealProductModule`, so a map
`ℱ' ⟶ I·𝒢'` is the unit of the adjunction of Stacks 03D7 followed by a direct image, and the
unit kills `I·ℱ'`. -/
theorem idealProduct_ι_comp_eq_zero (hi : FirstOrderThickening i)
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (g : F' ⟶ (idealProductSubmodule hi G').toSheafOfModules) :
    (idealProductSubmodule hi F').ι ≫ g = 0 := by
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  let K := (idealProductModule hi G').val
  let κ := (idealProductModule hi G').property.some
  have key : ∀ β : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶ K,
      adj.homEquiv F' K β = adj.unit.app F' ≫ i.pushforwardModules.map β := fun β => by
    rw [Adjunction.homEquiv_unit]
  have hfac : g ≫ κ.inv =
      adj.unit.app F' ≫ i.pushforwardModules.map ((adj.homEquiv F' K).symm (g ≫ κ.inv)) :=
    (Equiv.apply_symm_apply (adj.homEquiv F' K) (g ≫ κ.inv)).symm.trans
      (key ((adj.homEquiv F' K).symm (g ≫ κ.inv)))
  have h0 : ((idealProductSubmodule hi F').ι ≫ g) ≫ κ.inv = 0 := by
    rw [Category.assoc, hfac, ← Category.assoc,
      idealProductSubmodule_unit_comp_zero hi F', zero_comp]
  have h1 := congrArg (fun m => m ≫ κ.hom) h0
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using h1

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- An endomorphism whose pullback across the thickening vanishes is the one whose composite with
the unit of the adjunction of Stacks 03D7 vanishes. -/
theorem pullbackModules_map_eq_zero_iff
    {F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)} (g : F' ⟶ G') :
    (pullbackModules i.toRingedToposModulesHom).map g = 0 ↔
      g ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app G' = 0 := by
  let L := pullbackModules i.toRingedToposModulesHom
  let : L.Additive := pullbackModules_additive
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  have heta : adj.homEquiv F' (L.obj G') (L.map g) = g ≫ adj.unit.app G' := by
    rw [adj.homEquiv_unit]
    exact adj.unit_naturality g
  rw [← heta]
  exact (adj.homAddEquiv F' (L.obj G')).map_eq_zero_iff.symm

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
  /-- Two corrections factoring through the inclusion of the ideal product compose to zero. -/
  private theorem comp_ι_comp_comp_ι_eq_zero (hi : FirstOrderThickening i)
    {F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)}
    (g h : F' ⟶ (idealProductSubmodule hi F').toSheafOfModules) :
    (g ≫ (idealProductSubmodule hi F').ι) ≫ (h ≫ (idealProductSubmodule hi F').ι) = 0 := by
  rw [Category.assoc, ← Category.assoc (idealProductSubmodule hi F').ι h,
    idealProduct_ι_comp_eq_zero hi F' F' h, zero_comp, comp_zero]

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
  /-- A lift of the identity is the identity plus a map factoring through the ideal product. -/
  private theorem exists_sub_id_eq_comp_ι (hi : FirstOrderThickening i)
    {F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)} (θ : F' ⟶ F')
    (hθ : (pullbackModules i.toRingedToposModulesHom).map θ =
      𝟙 ((pullbackModules i.toRingedToposModulesHom).obj F')) :
    ∃ g, θ - 𝟙 F' = g ≫ (idealProductSubmodule hi F').ι := by
  let : (pullbackModules i.toRingedToposModulesHom).Additive := pullbackModules_additive
  exact idealProductSubmodule_factors_through hi F' F' (θ - 𝟙 F')
    ((pullbackModules_map_eq_zero_iff (θ - 𝟙 F')).1
      (by rw [CategoryTheory.Functor.map_sub, hθ, CategoryTheory.Functor.map_id, sub_self]))

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **An endomorphism lifting the identity is an automorphism.** If the pullback of
`θ : ℱ' ⟶ ℱ'` across the first order thickening `i` is the identity, then `θ = 1 + ε` with `ε`
factoring through the inclusion of the ideal product `I·ℱ'`, and the factoring map kills `I·ℱ'`,
so `ε ≫ ε = 0` and `1 - ε` inverts `θ`. -/
theorem isIso_of_pullbackModules_map_eq_id (hi : FirstOrderThickening i)
    {F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)} (θ : F' ⟶ F')
    (hθ : (pullbackModules i.toRingedToposModulesHom).map θ =
      𝟙 ((pullbackModules i.toRingedToposModulesHom).obj F')) :
    IsIso θ := by
  obtain ⟨g, hg⟩ := exists_sub_id_eq_comp_ι hi θ hθ
  have hεε : (θ - 𝟙 F') ≫ (θ - 𝟙 F') = 0 := by
    rw [hg, comp_ι_comp_comp_ι_eq_zero]
  refine ⟨𝟙 F' - (θ - 𝟙 F'), ?_, ?_⟩
  · have h : θ ≫ (𝟙 F' - (θ - 𝟙 F')) =
        θ - (θ - 𝟙 F') - (θ - 𝟙 F') ≫ (θ - 𝟙 F') := by
      rw [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp, Category.id_comp]
      abel
    rw [h, hεε, sub_zero]
    abel
  · have h : (𝟙 F' - (θ - 𝟙 F')) ≫ θ =
        θ - (θ - 𝟙 F') - (θ - 𝟙 F') ≫ (θ - 𝟙 F') := by
      rw [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub, Category.comp_id]
      abel
    rw [h, hεε, sub_zero]
    abel

/-- The automorphisms of an `O'`-module that pull back to the identity across the thickening `i`.
For a flat lift `ℱ'` of `ℱ`, whose restriction `i^*ℱ'` is identified with `ℱ`, these are the
source's automorphisms of `ℱ'` which pull back to `id_ℱ`. -/
def AutOverIdentity (i : RingedToposHom X X')
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) : Type _ :=
  { θ : F' ≅ F' // (pullbackModules i.toRingedToposModulesHom).map θ.hom =
      𝟙 ((pullbackModules i.toRingedToposModulesHom).obj F') }

/-- **The automorphisms over the identity are a group.** They are closed under composition,
contain the identity and are closed under inverses, because the pullback across the thickening
is a functor. The product is written in diagrammatic order: `θ * σ` is `θ` followed by `σ`, so
that it matches `Iso.trans`. -/
noncomputable instance AutOverIdentity.instGroup
    {F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)} :
    Group (AutOverIdentity i F') where
  mul θ σ := ⟨θ.1 ≪≫ σ.1, by
    rw [Iso.trans_hom, CategoryTheory.Functor.map_comp, θ.2, σ.2, Category.id_comp]⟩
  one := ⟨Iso.refl F', by rw [Iso.refl_hom, CategoryTheory.Functor.map_id]⟩
  inv θ := ⟨θ.1.symm, by
    have h : (pullbackModules i.toRingedToposModulesHom).map θ.1.inv ≫
        (pullbackModules i.toRingedToposModulesHom).map θ.1.hom =
        𝟙 ((pullbackModules i.toRingedToposModulesHom).obj F') := by
      rw [← CategoryTheory.Functor.map_comp, θ.1.inv_hom_id,
        CategoryTheory.Functor.map_id]
    rw [θ.2, Category.comp_id] at h
    exact h⟩
  mul_assoc θ σ τ := Subtype.ext (Iso.ext (Category.assoc θ.1.hom σ.1.hom τ.1.hom))
  one_mul θ := Subtype.ext (Iso.ext (Category.id_comp θ.1.hom))
  mul_one θ := Subtype.ext (Iso.ext (Category.comp_id θ.1.hom))
  inv_mul_cancel θ := Subtype.ext (Iso.ext θ.1.inv_hom_id)

variable [HasSheafify X'.J AddCommGrpCat.{w}]

/-- The endomorphism `1 + α` of `ℱ'` attached to a map `α : i^*ℱ' ⟶ I·ℱ'` into the descent of the
ideal product: the correction `α` is read as a map `ℱ' ⟶ I·ℱ'` by
`Deformation.ToposThickening.idealProductHomEquiv`, the dictionary of Stacks 08MP, and then
included into `ℱ'`. -/
noncomputable def autOverIdentityHom (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (α : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶ (idealProductModule hi F').val) :
    F' ⟶ F' :=
  𝟙 F' + idealProductHomEquiv hi F' F' α ≫ (idealProductSubmodule hi F').ι

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- `Deformation.ToposThickening.autOverIdentityHom` is `1 + α`, by definition. -/
theorem autOverIdentityHom_eq (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (α : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶ (idealProductModule hi F').val) :
    autOverIdentityHom hi F' α =
      𝟙 F' + idealProductHomEquiv hi F' F' α ≫ (idealProductSubmodule hi F').ι :=
  rfl

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- `1 + α` lifts the identity: the correction factors through the ideal product, which the unit
of the adjunction of Stacks 03D7 kills, so its pullback across the thickening vanishes. -/
theorem pullbackModules_map_autOverIdentityHom (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (α : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶ (idealProductModule hi F').val) :
    (pullbackModules i.toRingedToposModulesHom).map (autOverIdentityHom hi F' α) =
      𝟙 ((pullbackModules i.toRingedToposModulesHom).obj F') := by
  let : (pullbackModules i.toRingedToposModulesHom).Additive := pullbackModules_additive
  have hz : (pullbackModules i.toRingedToposModulesHom).map
      (idealProductHomEquiv hi F' F' α ≫ (idealProductSubmodule hi F').ι) = 0 :=
    (pullbackModules_map_eq_zero_iff _).2 (by
      rw [Category.assoc, idealProductSubmodule_unit_comp_zero hi F', comp_zero])
  rw [autOverIdentityHom_eq, CategoryTheory.Functor.map_add,
    CategoryTheory.Functor.map_id, hz, add_zero]

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- `1 + α` is an automorphism of `ℱ'`, being a lift of the identity. -/
theorem isIso_autOverIdentityHom (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (α : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶ (idealProductModule hi F').val) :
    IsIso (autOverIdentityHom hi F' α) :=
  isIso_of_pullbackModules_map_eq_id hi _ (pullbackModules_map_autOverIdentityHom hi F' α)

/-- **The automorphisms over the identity, canonically.** The maps `i^*ℱ' ⟶ I·ℱ'` into the descent
of the ideal product are the automorphisms of `ℱ'` that pull back to the identity, by
`α ↦ 1 + α`: such an `α` gives a lift of the identity, every lift of the identity is an
automorphism by `Deformation.ToposThickening.isIso_of_pullbackModules_map_eq_id`, and the
difference of a lift and the identity determines `α` because the inclusion of the ideal product is
a monomorphism. This is Stacks 08MP read at the identity, with its base point, rather than as a
bare principal homogeneous set. -/
noncomputable def autOverIdentityEquiv (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    ((pullbackModules i.toRingedToposModulesHom).obj F' ⟶ (idealProductModule hi F').val) ≃
      AutOverIdentity i F' :=
  Equiv.ofBijective
    (fun α =>
      letI := isIso_autOverIdentityHom hi F' α
      (⟨asIso (autOverIdentityHom hi F' α),
        pullbackModules_map_autOverIdentityHom hi F' α⟩ : AutOverIdentity i F'))
    (by
      constructor
      · intro α β h
        have h1 : autOverIdentityHom hi F' α = autOverIdentityHom hi F' β :=
          congrArg (fun θ : AutOverIdentity i F' => θ.val.hom) h
        rw [autOverIdentityHom_eq, autOverIdentityHom_eq] at h1
        exact (idealProductHomEquiv hi F' F').injective
          ((cancel_mono (idealProductSubmodule hi F').ι).1 (add_left_cancel h1))
      · intro θ
        let : (pullbackModules i.toRingedToposModulesHom).Additive := pullbackModules_additive
        have hL : (pullbackModules i.toRingedToposModulesHom).map (θ.val.hom - 𝟙 F') = 0 := by
          rw [CategoryTheory.Functor.map_sub, θ.property, CategoryTheory.Functor.map_id,
            sub_self]
        obtain ⟨g, hg⟩ := idealProductSubmodule_factors_through hi F' F' (θ.val.hom - 𝟙 F')
          ((pullbackModules_map_eq_zero_iff (θ.val.hom - 𝟙 F')).1 hL)
        refine ⟨(idealProductHomEquiv hi F' F').symm g, Subtype.ext (Iso.ext ?_)⟩
        change autOverIdentityHom hi F' ((idealProductHomEquiv hi F' F').symm g) = θ.val.hom
        rw [autOverIdentityHom_eq, AddEquiv.apply_symm_apply, ← hg]
        abel)

omit [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The identification of the automorphisms over the identity is multiplicative.** Two
corrections compose to zero, so `(1 + α) ∘ (1 + β) = 1 + (α + β)`: the bijection
`Deformation.ToposThickening.autOverIdentityEquiv` carries addition to composition. -/
theorem autOverIdentityEquiv_add (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (α β : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶
      (idealProductModule hi F').val) :
    (autOverIdentityEquiv hi F' (α + β)).val =
      (autOverIdentityEquiv hi F' α).val ≪≫ (autOverIdentityEquiv hi F' β).val := by
  refine Iso.ext ?_
  change autOverIdentityHom hi F' (α + β) =
    autOverIdentityHom hi F' α ≫ autOverIdentityHom hi F' β
  have hab : (idealProductHomEquiv hi F' F' α ≫ (idealProductSubmodule hi F').ι) ≫
      (idealProductHomEquiv hi F' F' β ≫ (idealProductSubmodule hi F').ι) = 0 :=
    comp_ι_comp_comp_ι_eq_zero hi _ _
  rw [autOverIdentityHom_eq, autOverIdentityHom_eq, autOverIdentityHom_eq, map_add]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.comp_id, Category.id_comp, hab]
  abel

end LiftAutomorphisms

/-! ### Stacks 08VW, part (3): the automorphisms of a flat lift -/

section FlatLiftAutomorphisms

variable [HasSheafify X'.J AddCommGrpCat.{w}]

/-- **Stacks 08VW, part (3).** In the situation of Stacks 08VV, given a lift `ℱ'` of `ℱ` to an
`O'`-module flat over `O_{ℬ'}`, the automorphisms of `ℱ'` which pull back to the identity of `ℱ`
are canonically `Ext⁰_O(ℱ, f^*J ⊗_O ℱ)`: the identification carries the addition of `Ext⁰` to
the multiplication of `Deformation.ToposThickening.AutOverIdentity.instGroup`, which is
composition, so it is an isomorphism of groups.

The module `ℱ` of the source is written `i^*ℱ'`, which the lift identifies with `ℱ`, and `f^*J`
is `Deformation.ToposThickening.basePullbackIdeal`. The source's proof quotes Stacks 08MR, whose
proof is "combine Stacks 08MP and Stacks 08MQ"; both steps appear here, the first as
`Deformation.ToposThickening.autOverIdentityEquiv` — which is Stacks 08MP at the identity, with
the identity as its base point, so that the identification is canonical and multiplicative, and
with `Deformation.ToposThickening.isIso_of_pullbackModules_map_eq_id` to see that the lifts of the
identity really are automorphisms — and the second as
`Deformation.ToposThickening.isIdealProductTensorIso`, which identifies the two coefficient
modules. `Ext⁰` is the group of maps by
`CategoryTheory.Abelian.Ext.addEquiv₀`. -/
theorem autOverIdentity_equiv_extZero (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasSheafify X.J AddCommGrpCat.{w}]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (L : FlatLift i f' hi F) :
    ∃ Ψ : Abelian.Ext.{e} ((pullbackModules i.toRingedToposModulesHom).obj L.module')
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
              ((pullbackModules i.toRingedToposModulesHom).obj L.module')).obj
              (basePullbackIdeal t f ht)) 0 ≃
        AutOverIdentity i L.module',
      ∀ α β, Ψ (α + β) = Ψ α * Ψ β := by
  obtain ⟨κ⟩ := isIdealProductTensorIso i t f f' hi ht comm L.module' hstrict L.isFlat
  let B := Abelian.Ext.addEquiv₀.trans
    (homAddEquivOfIso (T := (pullbackModules i.toRingedToposModulesHom).obj L.module') κ)
  refine ⟨B.toEquiv.trans (autOverIdentityEquiv hi L.module'), fun α β => Subtype.ext ?_⟩
  change (autOverIdentityEquiv hi L.module' (B (α + β))).val =
    (autOverIdentityEquiv hi L.module' (B α)).val ≪≫
      (autOverIdentityEquiv hi L.module' (B β)).val
  rw [map_add, autOverIdentityEquiv_add]

end FlatLiftAutomorphisms

end Deformation.ToposThickening

end
