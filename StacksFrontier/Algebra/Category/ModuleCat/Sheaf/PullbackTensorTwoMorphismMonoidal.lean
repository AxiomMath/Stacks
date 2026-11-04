module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorMateMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModulesMap
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality

/-! # The comparison of Stacks 03EL against a 2-morphism of morphisms of ringed topoi

`StacksDraft.…​.PullbackTensorMateMonoidal` proves that the comparison of **Stacks 03EL** is
monoidal in the mate of a transformation of direct images, for the *four-field* morphism of ringed
topoi `Stacks.Sheaves.RingedToposModules.RingedToposHom` — the one the chain of bijections of
Stacks 03EL is stated for. This file transfers that law to the **two-field** morphism of ringed
topoi of Stacks 01D3 part (2) and its 2-morphisms of Stacks 04IC, which is the form a consumer
has: `AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap` is the transformation of
pullbacks whose compatibility with the comparison is wanted.

The transfer is not a restatement. The two-field morphism of ringed topoi has its own direct image
of sheaves of modules and its own adjunction of Stacks 03D7, the latter being the four-field one
with the right adjoint transported along `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`
— so the mate of a 2-morphism, taken for the two-field adjunctions, is *a priori* a different
transformation from the four-field mate of anything. What makes it the same is that conjugation
commutes with a change of right adjoints along isomorphisms
(`Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight`): the two-field mate is the four-field mate
of the 2-morphism's transformation of direct images conjugated by the two comparisons. And the
hypothesis the four-field law asks for — that the transformation of direct images of modules is
the 2-morphism on underlying sheaves of sets — holds by `Eq.refl`, because the comparison of the
two direct images is the identity there
(`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id`).

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoMorphism.conjugateEquiv_pullbackModulesMap` and
  `.pullbackModulesMap_eq`: the transformation of pullbacks induced by a 2-morphism is the
  four-field mate of its transformation of direct images, conjugated by the two comparisons of the
  two direct images.
* `AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackTensorIso_hom_app_comp_pullbackModulesMap`:
  **the comparison of Stacks 03EL is compatible with a 2-morphism of morphisms of ringed topoi.**

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom.TwoMorphism

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {f g : RingedToposHom X Y} (t : TwoMorphism f g)

/-- **The four-field conjugate of the transformation of pullbacks induced by a 2-morphism** is its
transformation of direct images, conjugated by the two comparisons of the two direct images of
sheaves of modules.

`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap` is by definition the mate of
`.pushforwardModulesMap` under the *two-field* adjunctions of Stacks 03D7, and those are the
four-field ones with the right adjoint transported along
`AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`; so this is
`Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight`, solved for the four-field conjugate. -/
lemma conjugateEquiv_pullbackModulesMap :
    conjugateEquiv
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom)
        t.pullbackModulesMap =
      f.toModulesPushforwardIso.hom ≫ t.pushforwardModulesMap ≫
        g.toModulesPushforwardIso.inv := by
  have key : f.toModulesPushforwardIso.inv ≫
      conjugateEquiv
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom)
          t.pullbackModulesMap ≫
        g.toModulesPushforwardIso.hom = t.pushforwardModulesMap :=
    (Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight _ _ _ _ _).symm.trans
      ((conjugateEquiv (pullbackAdjPushforwardModules f)
        (pullbackAdjPushforwardModules g)).apply_symm_apply t.pushforwardModulesMap)
  rw [← key]
  simp

/-- **The transformation of pullbacks induced by a 2-morphism is a four-field mate**, namely the
mate of the conjugated transformation of direct images. This is
`conjugateEquiv_pullbackModulesMap` read through the bijection, and it is what lets the law of
`StacksDraft.…​.PullbackTensorMateMonoidal` — stated for a four-field mate — be applied to it. -/
lemma pullbackModulesMap_eq :
    t.pullbackModulesMap =
      (conjugateEquiv
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom)).symm
        (f.toModulesPushforwardIso.hom ≫ t.pushforwardModulesMap ≫
          g.toModulesPushforwardIso.inv) :=
  (Equiv.eq_symm_apply _).mpr t.conjugateEquiv_pullbackModulesMap

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The conjugated transformation of direct images of sheaves of modules is the 2-morphism on
underlying sheaves of sets.** True by `Eq.refl`: the induced transformation of direct images of
modules is the 2-morphism there
(`AlgebraicGeometry.RingedToposHom.TwoMorphism.moduleSheafFunctor_map_pushforwardModulesMap`) and
each of the two comparisons of the two direct images is the identity there
(`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id`).

This is the hypothesis the law of `StacksDraft.…​.PullbackTensorMateMonoidal` asks for, and the
reason the two-field and four-field pictures agree at the level the law's proof works at. -/
lemma moduleSheafFunctor_map_modulesPushforwardMap_app
    (N : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        ((f.toModulesPushforwardIso.hom ≫ t.pushforwardModulesMap ≫
          g.toModulesPushforwardIso.inv).app N) =
      t.t.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) N) :=
  rfl

/-- **The comparison of Stacks 03EL is compatible with a 2-morphism of morphisms of ringed
topoi.**

Let `f, g : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be two morphisms of ringed topoi in the sense of
Stacks 01D3 part (2), let `t : f ⟶ g` be a 2-morphism between them in the sense of Stacks 04IC,
and write `β := t.pullbackModulesMap : g^* ⟶ f^*` for the induced transformation of the pullbacks
of sheaves of modules of Stacks 03D6 part (2). Then for all sheaves of `O_D`-modules `F` and `G`

`β_{F ⊗ G} ≫ c_f = c_g ≫ (β_F ⊗ β_G)`,

where `c_h : h^*(F ⊗_{O_D} G) ⟶ h^*F ⊗_{O_C} h^*G` is the comparison of Stacks 03EL for `h`. The
2-morphism is not assumed invertible.

This is `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_mate` applied to the four-field mate
that `pullbackModulesMap_eq` identifies `β` with, the hypothesis of that law being
`moduleSheafFunctor_map_modulesPushforwardMap_app`. -/
theorem pullbackTensorIso_hom_app_comp_pullbackModulesMap
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    (F G : SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    t.pullbackModulesMap.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (F, G) =
      (Stacks.SheafOfModules.pullbackTensorIso g.toModulesHom).hom.app (F, G) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          ((t.pullbackModulesMap.app F, t.pullbackModulesMap.app G) :
            ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                g.toModulesHom).obj F,
                (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  g.toModulesHom).obj G) ⟶
              ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  f.toModulesHom).obj F,
                (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  f.toModulesHom).obj G)) := by
  rw [t.pullbackModulesMap_eq]
  exact Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_mate f.toModulesHom g.toModulesHom
    t.t _ F G t.moduleSheafFunctor_map_modulesPushforwardMap_app

end AlgebraicGeometry.RingedToposHom.TwoMorphism

end
