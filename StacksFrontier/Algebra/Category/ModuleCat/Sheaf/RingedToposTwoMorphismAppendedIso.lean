module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesCompAssoc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoIsoPullbackCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModulesMap

/-!
# A 2-morphism that becomes invertible after appending a morphism

Let `t : f ⟶ g` be a 2-morphism of morphisms of ringed topoi `X ⟶ Y`, and `k : Y ⟶ Z` a morphism
of ringed topoi such that `t` becomes invertible after `k_*` is appended. Then `t` whiskered by
`k` is a 2-isomorphism `s : k ∘ f ≅ k ∘ g`, and the transformation of pullbacks of modules
induced by `t`, prepended with `k^*`, is the pullback isomorphism of `s` read through the
composition isomorphisms of Stacks 03D8:
`k^* ⋙ g^* ≅ (k ∘ g)^* ≅ (k ∘ f)^* ≅ k^* ⋙ f^*`.

## Main results

* `TwoMorphism.whiskerRight_pushforwardModulesMap_eq_pushforwardModulesIso`: the transformation of
  direct images of modules induced by `t`, with `k_*` appended, is the direct-image isomorphism
  of `s` read through the composition isomorphisms.
* `TwoMorphism.whiskerLeft_pullbackModulesMap_eq_pullbackModulesIso`: the transformation of
  pullbacks of modules induced by `t`, prepended with `k^*`, is the inverse pullback isomorphism of
  `s` read through the composition isomorphisms.

## References

* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom.TwoMorphism

universe v u w v' u' w' v'' u'' w''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  {f g : RingedToposHom X Y} (t : TwoMorphism f g) (k : RingedToposHom Y Z)
  (h : IsIso (t.whiskerRight k).t)

/-- On direct images of modules, the transformation induced by `t` with `k_*` appended is the
direct-image isomorphism of the 2-isomorphism `s = (t ∘ k)`, read through the composition
isomorphisms. -/
theorem whiskerRight_pushforwardModulesMap_eq_pushforwardModulesIso :
    Functor.whiskerRight t.pushforwardModulesMap k.pushforwardModules =
      (pushforwardModulesCompIso f k).inv ≫
        ((t.whiskerRight k).toTwoIso h).pushforwardModulesIso.hom ≫
          (pushforwardModulesCompIso g k).hom := by
  refine NatTrans.ext (funext fun M => hom_ext_moduleSheafFunctor ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp, Functor.map_comp]
  rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]

/-- **A 2-morphism invertible after appending `k` induces, after `k^*`, the pullback isomorphism
of the whiskered 2-isomorphism.** With `s = (t ∘ k) : k ∘ f ≅ k ∘ g`,
`k^* ⋙ t^* = (k ∘ g)^*-comparison⁻¹ ≫ s^*⁻¹ ≫ (k ∘ f)^*-comparison`. -/
theorem whiskerLeft_pullbackModulesMap_eq_pullbackModulesIso :
    Functor.whiskerLeft k.toModulesHom.pullbackModules t.pullbackModulesMap =
      (pullbackModulesCompIso g k).inv ≫
        ((t.whiskerRight k).toTwoIso h).pullbackModulesIso.inv ≫
          (pullbackModulesCompIso f k).hom := by
  apply (conjugateEquiv ((pullbackAdjPushforwardModules k).comp (pullbackAdjPushforwardModules f))
    ((pullbackAdjPushforwardModules k).comp (pullbackAdjPushforwardModules g))).injective
  have hs : conjugateEquiv (pullbackAdjPushforwardModules (k.comp f))
      (pullbackAdjPushforwardModules (k.comp g))
      ((t.whiskerRight k).toTwoIso h).pullbackModulesIso.inv =
        ((t.whiskerRight k).toTwoIso h).pushforwardModulesIso.hom :=
    congrArg Iso.inv
      (Iso.ext (TwoIso.conjugateEquiv_pullbackModulesIso_hom ((t.whiskerRight k).toTwoIso h)) :
        conjugateIsoEquiv (pullbackAdjPushforwardModules (k.comp g))
            (pullbackAdjPushforwardModules (k.comp f))
            ((t.whiskerRight k).toTwoIso h).pullbackModulesIso =
          ((t.whiskerRight k).toTwoIso h).pushforwardModulesIso.symm)
  have hconj : conjugateEquiv (pullbackAdjPushforwardModules f)
      (pullbackAdjPushforwardModules g) t.pullbackModulesMap = t.pushforwardModulesMap :=
    (conjugateEquiv _ _).apply_symm_apply _
  rw [conjugateEquiv_whiskerLeft, hconj,
    ← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (k.comp g)),
    ← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (k.comp f)),
    conjugateEquiv_pullbackModulesCompIso_hom, hs, conjugateEquiv_pullbackModulesCompIso_inv]
  exact whiskerRight_pushforwardModulesMap_eq_pushforwardModulesIso t k h

end AlgebraicGeometry.RingedToposHom.TwoMorphism

end
