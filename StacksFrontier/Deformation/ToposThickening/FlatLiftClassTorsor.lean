module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftClassCorrespondence
public import StacksFrontier.Deformation.ToposThickening.FlatLiftTorsors

/-!
# The flat lifts of a module across a strict morphism of thickenings form a torsor

Let `(f, f')` be a morphism of first order thickenings of ringed topoi as in Situation 08M7

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`, suppose `(f, f')` is
strict, and let `ℱ` be an `O`-module flat over `O_ℬ`. Stacks 08MU says that if there is a pair
`(ℱ', α)` with `ℱ'` an `O'`-module flat over `O_{ℬ'}` and `α : i^*ℱ' ≅ ℱ`, then the isomorphism
classes of such pairs form a principal homogeneous set under `Ext¹_O(ℱ, I ⊗_O ℱ)`.

## Main results

* `Deformation.ToposThickening.exists_addTorsor_flatLiftClass`: **Stacks 08MU**, with no
  hypothesis beyond the source's and with the action of the source's proof.

## Implementation notes

The vocabulary is that of `StacksFrontier/Deformation/ToposThickening/FlatLiftTorsors.lean`: a pair
`(ℱ', α)` is `Deformation.ToposThickening.FlatLift` (the module `ℱ'` with its reduction
`ℱ' ⟶ i_*ℱ` and the short exact sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*ℱ ⟶ 0`, which is the
identification `i^*ℱ' ≅ ℱ`), and its isomorphism classes are
`Deformation.ToposThickening.FlatLiftClass`.

The proof is the source's. By Stacks 08MQ a flat lift forces the canonical map
`f^*J ⊗_O ℱ ⟶ I ⊗_O ℱ` to be an isomorphism
(`Deformation.ToposThickening.isFlatLiftCorrespondence`), and then the flat lifts are, up to
isomorphism, the extensions of `ℱ` by `I ⊗_O ℱ` whose action map is the identity
(`Deformation.ToposThickening.flatLiftClassEquivFixedActionExtensionClass`, which sends a lift to
the class of `Deformation.ToposThickening.FlatLift.fixedActionExtension`). Those form the coset of
Stacks 08ME
(`Deformation.ToposThickening.exists_extensionActionMap_eq_iff_exists_add_mapExtAddHom`), a
principal homogeneous set under `Ext¹_O(ℱ, I ⊗_O ℱ)` acting by adding the image in `Ext¹_{O'}`
(`AddTorsor.ofAddMonoidHomTranslate`), and the structure is carried over along the bijection by
`Deformation.ToposThickening.addTorsorCongr`. The conclusion pins the action down: it is not just
the existence of some principal homogeneous structure.

## References

* [Stacks Project, Tag 08MU](https://stacks.math.columbia.edu/tag/08MU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08ME](https://stacks.math.columbia.edu/tag/08ME)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
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
  [HasSheafify X'.J AddCommGrpCat.{w}]

/-- **Stacks 08MU.** Let `(f, f')` be a strict morphism of first order thickenings of ringed
topoi as in Situation 08M7 and let `ℱ` be an `O`-module flat over `O_ℬ`. If there is a pair
`(ℱ', α)` consisting of an `O'`-module `ℱ'` flat over `O_{ℬ'}` and an isomorphism
`α : i^*ℱ' ≅ ℱ`, then the isomorphism classes of such pairs form a principal homogeneous set
under `Ext¹_O(ℱ, I ⊗_O ℱ)`.

The action is the one of the source's proof. A pair `(ℱ', α)` gives the extension
`0 ⟶ I ⊗_O ℱ ⟶ ℱ' ⟶ ℱ ⟶ 0` of `O'`-modules whose first map is the canonical map
`I ⊗_O ℱ ≅ I·ℱ' ⊂ ℱ'` (`Deformation.ToposThickening.FlatLift.fixedActionExtension`; the canonical
map is an isomorphism onto `I·ℱ'` by Stacks 08MQ), and `a ∈ Ext¹_O(ℱ, I ⊗_O ℱ)` sends the class
of `(ℱ', α)` to the class of `(𝒢', β)` exactly when the `Ext¹_{O'}` class of the extension of
`𝒢'` is that of `ℱ'` plus the image of `a`, which is the action of Stacks 08ME. -/
@[stacks 08MU]
theorem exists_addTorsor_flatLiftClass (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasExt.{e} (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : IsFlatOverBase i f F) (hne : Nonempty (FlatLift i f' hi F)) :
    ∃ T : AddTorsor
        (Abelian.Ext.{e} F
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I) 1)
        (FlatLiftClass i f' hi F),
      ∀ (a : Abelian.Ext.{e} F
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I) 1)
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
                  ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I) 1 a +
              extensionClass F
                (((Stacks.SheafOfModules.Tensor.sheafTensor
                  ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I)
                (A.fixedActionExtension i t f f' hi ht comm F
                  ((isStrictPullbackIdealMap_iff_isStrict i t f f' hi ht comm).mpr hstrict)
                  (isFlat_reducedBaseModule_of_isFlatOverBase i t f f' hi ht comm F hflat)) := by
  classical
  have hs := (isStrictPullbackIdealMap_iff_isStrict i t f f' hi ht comm).mpr hstrict
  have hF := isFlat_reducedBaseModule_of_isFlatOverBase i t f f' hi ht comm F hflat
  have hiso := (isFlatLiftCorrespondence i t f f' hi ht comm F hstrict hflat).1
    ((hasFlatLift_iff_nonempty_flatLift i f' hi F).2 hne)
  have hcff := (isIso_idealTensorComparison_iff_isIso_canonicalFirstFactor
    i t f f' hi ht comm F).mp hiso
  -- the flat lifts, up to isomorphism, are the extensions with action map the identity (08MQ)
  let eqv := flatLiftClassEquivFixedActionExtensionClass.{_, _, _, _, _, _, _, _, _, _, _, e}
    i t f f' hi ht comm F hs hF hcff
  let R := SheafOfModules.restrictScalars.{w} (structureRingMap i)
  let ff := hi.restrictScalarsFullyFaithful
  have : R.Full := ff.full
  have : R.Faithful := ff.faithful
  -- the torsor of Stacks 08ME on those extensions, with `a` acting by adding its image
  let b := eqv (Quotient.mk (flatLiftSetoid i f' hi F) hne.some)
  let T₀ := AddTorsor.ofAddMonoidHomTranslate (R.mapExtAddHom F _ 1)
    (Functor.mapExtAddHom_injective_of_fullyFaithful R F _) b.val _
    (exists_extensionActionMap_eq_iff_exists_add_mapExtAddHom hi b)
  refine ⟨addTorsorCongr (AddEquiv.refl _) eqv, fun a A B => ?_⟩
  change eqv.symm (a +ᵥ eqv (Quotient.mk _ A)) = Quotient.mk _ B ↔ _
  rw [Equiv.symm_apply_eq, Subtype.ext_iff, eq_comm]
  rfl

end Deformation.ToposThickening

end
