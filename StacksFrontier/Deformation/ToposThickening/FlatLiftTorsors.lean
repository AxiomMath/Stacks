module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.ModuleMapLifts

/-!
# Flat deformations of modules across a strict morphism of first order thickenings

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`, and suppose the square
is strict. This file records the two *principal homogeneous space* statements of Section 08MN
for this situation.

* Stacks 08MU: for an `O`-module `ℱ` flat over `O_ℬ`, the isomorphism classes of pairs
  `(ℱ', α)` with `ℱ'` an `O'`-module flat over `O_{ℬ'}` and `α : i^*ℱ' ≅ ℱ` form, as soon as
  there is one, a principal homogeneous set under `Ext¹_O(ℱ, I ⊗_O ℱ)`.
* Stacks 08MR: for `O'`-modules `ℱ'` and `𝒢'` with `𝒢'` flat over `O_{ℬ'}`, and a map
  `φ : i^*ℱ' ⟶ i^*𝒢'`, the lifts of `φ` to an `O'`-linear map `ℱ' ⟶ 𝒢'` form, as soon as there
  is one, a principal homogeneous set under `Hom_O(i^*ℱ', f^*J ⊗_O i^*𝒢')`.

Both are obtained the way the source obtains them: from an *absolute* principal homogeneous
statement over the upper thickening alone — Stacks 08ME for 08MU, Stacks 08MP for 08MR — by
transporting it along the identification that Stacks 08MQ supplies for a strict square and a
relatively flat module. See the scope section for how the 08MQ input enters.

## Main definitions

* `Deformation.ToposThickening.addTorsorCongr`: transport of a principal homogeneous space
  along an isomorphism of acting groups and a bijection of underlying sets.
* `Deformation.ToposThickening.homAddEquivOfIso`: post-composition with an isomorphism, as an
  isomorphism of the groups of morphisms out of a fixed object.
* `Deformation.ToposThickening.FlatLift`: a flat lift of `ℱ` over the thickening, as data; its
  mere existence is `Deformation.ToposThickening.HasFlatLift`.
* `Deformation.ToposThickening.FlatLiftClass`: the isomorphism classes of flat lifts.
* `Deformation.ToposThickening.basePullbackIdeal`: the `O`-module `f^*J`.
* `Deformation.ToposThickening.IsFlatLiftClassCorrespondence` and
  `Deformation.ToposThickening.IsIdealProductTensorIso`: the two consequences of Stacks 08MQ
  that the proofs below consume. See the scope section.

## Main results

* `Deformation.ToposThickening.hasFlatLift_iff_nonempty_flatLift`: a flat lift exists exactly
  when the type of flat lifts is nonempty, so that `FlatLift` is the data behind `HasFlatLift`.
* `Deformation.ToposThickening.flatLiftClass_torsor`: the principal homogeneous set of Stacks 08MU
  from the class-level dictionary of Stacks 08MQ, taken as an argument. The dictionary is proved
  by `Deformation.ToposThickening.isFlatLiftClassCorrespondence`; Stacks 08MU itself, with only
  the source's hypotheses, is `Deformation.ToposThickening.nonempty_addTorsor_flatLiftClass`, and
  with the action pinned down `Deformation.ToposThickening.exists_addTorsor_flatLiftClass`.
* `Deformation.ToposThickening.moduleMapLift_torsor_of_isFlat`: Stacks 08MR from a given
  identification of its coefficient module with the ideal product. Stacks 08MR itself is
  `Deformation.ToposThickening.exists_addTorsor_moduleMapLift`.

## Implementation notes

The vocabulary is the one already in place and no second copy of it is introduced.

For Stacks 08MU the square is the one of
`Deformation.ToposThickening.MorphismOfThickenings.ofFirstOrderThickenings`, built from two
`Deformation.ToposThickening.FirstOrderThickening` structures of Stacks 08MB rather than from
the predicate `Deformation.ToposThickening.IsFirstOrderThickening`, because the obstruction
theory of Stacks 08MF and the extension theory of Stacks 08MB are constructions on a thickening
whose square-zero ideal is *named*. Modules over `O` are therefore presented on the thickened
topos `Sh(D)` as modules over the direct image `i_*O`, a flat lift is an `O'`-module `ℱ'` flat
over `O_{ℬ'}` sitting in a short exact sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*ℱ ⟶ 0`, and
`Deformation.ToposThickening.FlatLift` is exactly the data that
`Deformation.ToposThickening.HasFlatLift` asserts to exist; `hasFlatLift_iff_nonempty_flatLift`
records that. Two flat lifts are isomorphic when an isomorphism of the two modules commutes
with the two maps to `i_*ℱ`, which is the source's "isomorphism of pairs `(ℱ', α)`", and
`Deformation.ToposThickening.FlatLiftClass` is the quotient by that relation. The coefficient
group is `Ext¹` over `i_*O`, which is `Ext¹_O`, so the statement is the source's.

For Stacks 08MR the lifts are those of
`Deformation.ToposThickening.ModuleMapLift`, the fibre of `φ ↦ i^*φ`, and the pullback used
throughout is the one Stacks 08MP is stated for,
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` of the four-field morphism of
ringed topoi attached to `i`. The coefficient module is written `f^*J ⊗_O i^*𝒢'`, the source's
`𝒢 ⊗_O f^*J` with its two factors in the other order; the two are canonically isomorphic and
the statement asserts only that a principal homogeneous structure exists, as the source does.
`f^*J` is `Deformation.ToposThickening.basePullbackIdeal`: the square-zero ideal `J` is
annihilated by itself, hence is an `O_ℬ`-module — in the formalization, the pullback `t^*J` —
and that module is pulled back along `f`.

`Deformation.ToposThickening.addTorsorCongr` is what makes "transport" precise: the acting
group is carried by an additive isomorphism and the underlying set by a bijection, so a
principal homogeneous structure on one pair gives one on the other. Both results use it with
one of the two components the identity.

## Scope

Stacks 08MQ — the characterization of the `O'`-modules flat over `O_{ℬ'}` — is in the
library, as `Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap`, but in modules this one
cannot import. Each result below therefore takes the consequence of 08MQ that its proof consumes
as an explicit argument, stated with 08MQ's own hypotheses as antecedents so that 08MQ
discharges it. Both arguments are proved downstream —
`Deformation.ToposThickening.isFlatLiftClassCorrespondence` and
`Deformation.ToposThickening.isIdealProductTensorIso` — and the unconditional statements are
`Deformation.ToposThickening.nonempty_addTorsor_flatLiftClass` (Stacks 08MU) and
`Deformation.ToposThickening.exists_addTorsor_moduleMapLift` (Stacks 08MR). This is the treatment of
`Deformation.ToposThickening.IsFlatLiftCorrespondence` in
`StacksFrontier/Deformation/ToposThickening/FlatLiftObstruction.lean`, and the hypothesis for
Stacks 08MU below is that one with its second clause strengthened from an equivalence of
propositions to a bijection of isomorphism classes, which is what a principal homogeneous
statement needs.

* `Deformation.ToposThickening.IsFlatLiftClassCorrespondence`, for Stacks 08MU, is 08MQ
  specialized to the extensions with `K = I ⊗_O ℱ` and `c = 1`: granting strictness and
  flatness of `ℱ` over `O_ℬ`, a flat lift forces the canonical map of Stacks 08MV condition (1)
  to be an isomorphism, which is the "moreover" clause of 08MQ, and once it is one the
  isomorphism classes of flat lifts of `ℱ` are in bijection with the isomorphism classes of
  extensions of `ℱ` by `I ⊗_O ℱ` whose canonical action of the square-zero ideal is the
  identity. The source's proof of 08MU appeals to precisely this dictionary before applying
  Stacks 08ME, and the bijection is the bookkeeping of Section 08MN that the source treats as
  implicit: an `O'`-module flat over `O_{ℬ'}` is, by 08MQ, one whose ideal product is
  `I ⊗_O ℱ`, so its defining sequence is such an extension, normalized by Stacks 08MJ to have
  action map the identity.
* `Deformation.ToposThickening.IsIdealProductTensorIso`, for Stacks 08MR, is 08MQ for `𝒢'`:
  granting strictness and flatness of `𝒢'` over `O_{ℬ'}`, the two factors
  `f^*J ⊗_O 𝒢 ⟶ I ⊗_O 𝒢 ⟶ I·𝒢'` of the canonical map are isomorphisms, so `f^*J ⊗_O 𝒢` is
  `I·𝒢'`. That identification of the two coefficient groups is the whole of the source's
  one-line proof "combine Lemmas 08MP and 08MQ".

Nothing below asserts the content of 08MQ, and neither result is weaker than its source
statement once the argument is supplied.

## References

* [Stacks Project, Tag 08MU](https://stacks.math.columbia.edu/tag/08MU)
* [Stacks Project, Tag 08MR](https://stacks.math.columbia.edu/tag/08MR)
* [Stacks Project, Tag 08ME](https://stacks.math.columbia.edu/tag/08ME)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' vS uS wS vS' uS' wS' e

namespace Deformation.ToposThickening

/-! ### Transport of a principal homogeneous space -/

/-- **Transport of a principal homogeneous space.** A principal homogeneous structure on `Q`
under `H` gives one on `P` under `G`, along an additive isomorphism `G ≃+ H` of acting groups
and a bijection `P ≃ Q` of underlying sets: `a` acts on `x` by carrying `x` over, acting by
`g a`, and coming back. -/
@[instance_reducible]
noncomputable def addTorsorCongr {G H P Q : Type*} [AddGroup G] [AddGroup H] [AddTorsor H Q]
    (g : G ≃+ H) (p : P ≃ Q) : AddTorsor G P where
  vadd a x := p.symm (g a +ᵥ p x)
  vsub x y := g.symm (p x -ᵥ p y)
  zero_vadd x := by
    change p.symm (g 0 +ᵥ p x) = x
    rw [map_zero, zero_vadd, Equiv.symm_apply_apply]
  add_vadd a b x := by
    change p.symm (g (a + b) +ᵥ p x) = p.symm (g a +ᵥ p (p.symm (g b +ᵥ p x)))
    rw [Equiv.apply_symm_apply, map_add, add_vadd]
  nonempty := ⟨p.symm (Classical.choice (inferInstance : Nonempty Q))⟩
  vsub_vadd' x y := by
    change p.symm (g (g.symm (p x -ᵥ p y)) +ᵥ p y) = x
    rw [AddEquiv.apply_symm_apply, vsub_vadd, Equiv.symm_apply_apply]
  vadd_vsub' a x := by
    change g.symm (p (p.symm (g a +ᵥ p x)) -ᵥ p x) = a
    rw [Equiv.apply_symm_apply, vadd_vsub, AddEquiv.symm_apply_apply]

/-- **Post-composition with an isomorphism, additively.** In a preadditive category an
isomorphism `A ≅ B` induces an isomorphism of the additive groups of morphisms out of a fixed
object. -/
def homAddEquivOfIso {C : Type u} [Category.{v} C] [Preadditive C] {T A B : C} (κ : A ≅ B) :
    (T ⟶ A) ≃+ (T ⟶ B) where
  toFun φ := φ ≫ κ.hom
  invFun φ := φ ≫ κ.inv
  left_inv φ := by
    change (φ ≫ κ.hom) ≫ κ.inv = φ
    rw [Category.assoc, κ.hom_inv_id, Category.comp_id]
  right_inv φ := by
    change (φ ≫ κ.inv) ≫ κ.hom = φ
    rw [Category.assoc, κ.inv_hom_id, Category.comp_id]
  map_add' φ ψ := Preadditive.add_comp _ _ _ φ ψ κ.hom

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

/-! ### Stacks 08MU: the flat lifts of a module -/

section FlatLiftTorsor

/-- A *flat lift* of `ℱ` over the thickening `i` along `f'`: an `O'`-module `ℱ'`, flat over
`O_{ℬ'}`, together with a short exact sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*ℱ ⟶ 0`, that is, with an
identification `i^*ℱ' ≅ ℱ`. This is the data whose existence is
`Deformation.ToposThickening.HasFlatLift`, and the source's pair `(ℱ', α)`. -/
structure FlatLift (i : RingedToposHom X X') (f' : RingedToposHom X' S')
    (hi : FirstOrderThickening i)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) where
  /-- The lifted module, an `O'`-module. -/
  module' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)
  /-- The map to `i_*ℱ` identifying `i^*ℱ'` with `ℱ`. -/
  π : module' ⟶ (SheafOfModules.restrictScalars
    (show Stacks.SheafOfModules.Tensor.ringSheaf X'.O ⟶
        Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)
      from (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp)).obj F
  /-- The ideal product is killed by that map. -/
  idealProduct_comp : (idealProductSubmodule hi module').ι ≫ π = 0
  /-- The lifted module is flat over `O_{ℬ'}`. -/
  isFlat : AlgebraicGeometry.SheafOfModules.IsFlat
    ((SheafOfModules.restrictScalars
      ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        f'.fSharpInverseImage)).obj module')
  /-- The sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*ℱ ⟶ 0` is short exact. -/
  shortExact :
    (ShortComplex.mk (idealProductSubmodule hi module').ι π idealProduct_comp).ShortExact

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] in
/-- `Deformation.ToposThickening.FlatLift` is the data behind
`Deformation.ToposThickening.HasFlatLift`: a flat lift exists exactly when the type of flat
lifts is nonempty. -/
theorem hasFlatLift_iff_nonempty_flatLift (i : RingedToposHom X X')
    (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) :
    HasFlatLift i f' hi F ↔ Nonempty (FlatLift i f' hi F) := by
  constructor
  · rintro ⟨M, q, hq, hflat, hse⟩
    exact ⟨⟨M, q, hq, hflat, hse⟩⟩
  · rintro ⟨⟨M, q, hq, hflat, hse⟩⟩
    exact ⟨M, q, hq, hflat, hse⟩

/-- Two flat lifts are *isomorphic* when an isomorphism of the two modules commutes with their
maps to `i_*ℱ`, which is the source's isomorphism of pairs `(ℱ', α)`. -/
def FlatLift.IsIsomorphic {i : RingedToposHom X X'} {f' : RingedToposHom X' S'}
    {hi : FirstOrderThickening i}
    {F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (A B : FlatLift i f' hi F) : Prop :=
  ∃ κ : A.module' ≅ B.module', κ.hom ≫ B.π = A.π

/-- Isomorphism of flat lifts is an equivalence relation. -/
def flatLiftSetoid (i : RingedToposHom X X') (f' : RingedToposHom X' S')
    (hi : FirstOrderThickening i)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) :
    Setoid (FlatLift i f' hi F) where
  r := FlatLift.IsIsomorphic
  iseqv :=
    { refl := fun A => ⟨Iso.refl A.module', Category.id_comp A.π⟩
      symm := fun {A B} ⟨κ, hκ⟩ => ⟨κ.symm, by rw [← hκ, Iso.symm_hom, Iso.inv_hom_id_assoc]⟩
      trans := fun {A B D} ⟨κ, hκ⟩ ⟨μ, hμ⟩ =>
        ⟨κ ≪≫ μ, by rw [Iso.trans_hom, Category.assoc, hμ, hκ]⟩ }

/-- The isomorphism classes of flat lifts of `ℱ`. -/
abbrev FlatLiftClass (i : RingedToposHom X X') (f' : RingedToposHom X' S')
    (hi : FirstOrderThickening i)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) :
    Type _ :=
  Quotient (flatLiftSetoid i f' hi F)

variable [HasSheafify X'.J AddCommGrpCat.{w}]

/-- **The consequence of Stacks 08MQ that the proof of Stacks 08MU consumes**, as a
proposition (proved by `Deformation.ToposThickening.isFlatLiftClassCorrespondence`): granting
that the square is strict and that `ℱ` is flat over `O_ℬ`, which are the hypotheses of 08MQ,

* a flat lift of `ℱ` forces the canonical map `f^*J ⊗ ℱ ⟶ I ⊗ ℱ` to be an isomorphism, which
  is the "moreover" clause of 08MQ, and
* once that map is an isomorphism, the isomorphism classes of flat lifts of `ℱ` are in
  bijection with the isomorphism classes of extensions of `ℱ` by `I ⊗_O ℱ` of Stacks 08MB whose
  canonical action of the square-zero ideal is the identity.

This is `Deformation.ToposThickening.IsFlatLiftCorrespondence` with its second clause
strengthened from an equivalence of propositions to a bijection of isomorphism classes, which
is what the principal homogeneous statement needs; see the scope section of the module
docstring. -/
def IsFlatLiftClassCorrespondence (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))] : Prop :=
  (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict →
    IsFlatOverBase i f F →
      (HasFlatLift i f' hi F → IsIso (idealTensorComparison i t f f' hi ht comm F)) ∧
        (IsIso (idealTensorComparison i t f f' hi ht comm F) →
          Nonempty (FlatLiftClass i f' hi F ≃
            FixedActionExtensionClass hi F
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
                ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F)
              (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
                ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F))))

/-- **Stacks 08MU, from the dictionary of Stacks 08MQ.** Let `(f, f')` be a strict morphism of
first order thickenings of ringed topoi as in Situation 08M7 and let `ℱ` be an `O`-module flat
over `O_ℬ`. If `ℱ` has at least one lift to an `O'`-module flat over `O_{ℬ'}`, then the
isomorphism classes of such lifts form a principal homogeneous set under `Ext¹_O(ℱ, I ⊗_O ℱ)`.

The source proves this by applying Stacks 08MQ to see that the canonical map
`f^*J ⊗ ℱ ⟶ I ⊗ ℱ` is an isomorphism, which identifies the lifts with the extensions of `ℱ` by
`I ⊗_O ℱ` whose action map is the identity, and then quoting Stacks 08ME for those. Here the
first step is the argument `hMQ`, which `Deformation.ToposThickening.isFlatLiftClassCorrespondence`
supplies, and the second is `Deformation.ToposThickening.fixedActionExtensionClass_torsor`.
Stacks 08MU itself, with no such argument, is
`Deformation.ToposThickening.nonempty_addTorsor_flatLiftClass`. -/
theorem flatLiftClass_torsor (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasExt.{e} (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : IsFlatOverBase i f F)
    (hMQ : IsFlatLiftClassCorrespondence.{_, _, _, _, _, _, _, _, _, _, _, e}
      i t f f' hi ht comm F)
    (hne : Nonempty (FlatLift i f' hi F)) :
    Nonempty (AddTorsor
      (Abelian.Ext.{e} F
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F) 1)
      (FlatLiftClass i f' hi F)) := by
  obtain ⟨hnec, hdict⟩ := hMQ hstrict hflat
  obtain ⟨p⟩ := hdict (hnec ((hasFlatLift_iff_nonempty_flatLift i f' hi F).2 hne))
  obtain ⟨T⟩ := fixedActionExtensionClass_torsor hi F
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F)
    (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F))
    ⟨p (Quotient.mk (flatLiftSetoid i f' hi F) hne.some)⟩
  let := T
  exact ⟨addTorsorCongr (AddEquiv.refl _) p⟩

end FlatLiftTorsor

/-! ### Stacks 08MR: the lifts of a map of modules -/

section ModuleMapLiftTorsor

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}]
  [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]

/-- The `O`-module `f^*J`: the square-zero ideal `J ⊂ O_{B'}` of the lower thickening is
annihilated by itself, hence comes from the `O_ℬ`-module `t^*J`, and that module is pulled back
along `f`. -/
noncomputable def basePullbackIdeal (t : RingedToposHom S S') (f : RingedToposHom X S)
    (ht : FirstOrderThickening t) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (f.toRingedToposModulesHom.pullbackModules).obj
    ((t.toRingedToposModulesHom.pullbackModules).obj ht.idealOfThickening.I)

/-- **The consequence of Stacks 08MQ that the proof of Stacks 08MR consumes**, carried as a
hypothesis: granting that the square is strict and that `𝒢'` is flat over `O_{ℬ'}`, which are
the hypotheses of 08MQ, the coefficient module `f^*J ⊗_O 𝒢` is the ideal product `I·𝒢'`. The
source obtains this from the two "moreover" clauses of 08MQ, which make each factor of
`f^*J ⊗_O 𝒢 ⟶ I ⊗_O 𝒢 ⟶ I·𝒢'` an isomorphism. -/
def IsIdealProductTensorIso (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) : Prop :=
  (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict →
    AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            f'.fSharpInverseImage)).obj G') →
      Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
            (basePullbackIdeal t f ht)).obj
          ((pullbackModules i.toRingedToposModulesHom).obj G') ≅ (idealProductModule hi G').val)

/-- **Stacks 08MR, from a given identification of the coefficient module.** Let `(f, f')` be a
strict morphism of first order thickenings of ringed topoi as in Situation 08M7, let `ℱ'` and
`𝒢'` be `O'`-modules with `𝒢'` flat over `O_{ℬ'}`, and let `φ : i^*ℱ' ⟶ i^*𝒢'` be a map of
`O`-modules. If `φ` has at least one lift to an `O'`-linear map `ℱ' ⟶ 𝒢'`, then its lifts form a
principal homogeneous set under `Hom_O(i^*ℱ', f^*J ⊗_O i^*𝒢')`.

The source's proof is "combine Lemmas 08MP and 08MQ": Stacks 08MP makes the lifts a principal
homogeneous set under `Hom_O(i^*ℱ', I·𝒢')`, and Stacks 08MQ identifies `I·𝒢'` with
`f^*J ⊗_O i^*𝒢'`. Here the second step is taken as the argument `hMQ`, which
`Deformation.ToposThickening.isIdealProductTensorIso` proves. Stacks 08MR itself, with no such
argument and with the action of the source, is
`Deformation.ToposThickening.exists_addTorsor_moduleMapLift` in
`StacksFrontier/Deformation/ToposThickening/IdealProductTensorIso.lean`. -/
theorem moduleMapLift_torsor_of_isFlat (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj G'))
    (hMQ : IsIdealProductTensorIso i t f f' hi ht comm G')
    (φ : (i.toRingedToposModulesHom.pullbackModules).obj F' ⟶
      (i.toRingedToposModulesHom.pullbackModules).obj G')
    (hne : Nonempty (ModuleMapLift F' G' φ)) :
    Nonempty (AddTorsor
      ((pullbackModules i.toRingedToposModulesHom).obj F' ⟶
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
            (basePullbackIdeal t f ht)).obj
          ((pullbackModules i.toRingedToposModulesHom).obj G'))
      (ModuleMapLift F' G' φ)) := by
  obtain ⟨κ⟩ := hMQ hstrict hG
  obtain ⟨T, _⟩ := moduleMapLift_torsor hi F' G' φ hne
  let := T
  exact ⟨addTorsorCongr (homAddEquivOfIso κ) (Equiv.refl _)⟩

end ModuleMapLiftTorsor

end Deformation.ToposThickening

end
