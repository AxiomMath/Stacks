module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules

/-!
# `f^{-1}ℐ · 𝒪_X` is invariant under a 2-isomorphism

Let `f, g : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be two morphisms of ringed topoi and let `t` be a
2-isomorphism between them in the sense of [Stacks, Tag 04IC] — an isomorphism of the direct
image functors compatible with the two structure maps. Then `f` and `g` build the same ideal
sheaf `ℐ' = f^{-1}ℐ · 𝒪_X` out of a sheaf of ideals `ℐ ⊂ 𝒪`.

This is what carries a sheaf of ideals across a square of ringed topoi that commutes only up to
a 2-isomorphism — the square of [Stacks, Tag 03CR] in particular, which is how [Stacks, Tag 099J]
and [Stacks, Tag 0A0G] are reduced to morphisms of ringed *sites*.

## The route

A 2-isomorphism is data about the direct images only, so it reaches the pullback — over which
`ℐ'` is built — through `AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso`, which is
`CategoryTheory.Adjunction.leftAdjointUniq` applied to the two pullback/pushforward adjunctions.
The two steps are:

* the compatibility of `AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardModulesIso` with
  `AlgebraicGeometry.RingedToposHom.unitStructureMap`, which is the `commutes` field of the
  2-isomorphism read on sheaves of modules;
* its transpose, the compatibility of `pullbackModulesIso` with
  `AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap`. This is proved exactly as
  `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso_hom_app_comp_pullbackUnitStructureMap`
  proves the composite law: a `leftAdjointUniq` is transposed by
  `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app`, and the `ofNatIsoRight` factor it
  is taken over is removed by cancelling the monomorphism
  `pushforwardModulesIso`.

With that, the canonical map `f^*ℐ ⟶ 𝒪'` of `f` is the one of `g` precomposed with an
isomorphism, and an image subsheaf is insensitive to that, by
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp`. No automorphism of `𝒪'` is
left over — unlike in the comparison of the site-level and topos-level constructions — because
the 2-isomorphism's `commutes` field pins the two comparisons `f^*𝒪 ⟶ 𝒪'` against each other
exactly.

## Main results

* `RingedToposHom.TwoIso.unitStructureMap_comp_pushforwardModulesIso_hom_app`
* `RingedToposHom.TwoIso.pullbackModulesIso_hom_app_comp_pullbackUnitStructureMap`
* `AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIdealSheaf_eq`: **`f^{-1}ℐ · 𝒪_X` depends
  on the morphism of ringed topoi only through its 2-isomorphism class**, with no hypothesis on
  `ℐ` and none on either morphism.

## Deliberately untagged

Section 52.7 introduces `f^{-1}ℐ · 𝒪_X` in passing rather than as a numbered statement, and
neither `AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf` nor its functoriality
`AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_comp` carries an attribute.

## References

* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom.TwoIso

section UnitComparison

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  {f g : RingedToposHom X Y} (t : TwoIso f g)

/-- **The structure map `𝒪 ⟶ f_*𝒪'` of a morphism of ringed topoi is 2-isomorphism invariant**,
read on sheaves of modules: the unit-module structure map of `f` followed by the comparison of
direct images of a 2-isomorphism is the unit-module structure map of `g`.

Both sides are determined by their underlying morphisms of sheaves of sets, where the
unit-module structure map is the structure map itself
(`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_unitStructureMap`) and the comparison is
the 2-isomorphism itself; so this is precisely the `commutes` field of the 2-isomorphism. -/
theorem unitStructureMap_comp_pushforwardModulesIso_hom_app :
    unitStructureMap f ≫ t.pushforwardModulesIso.hom.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      unitStructureMap g := by
  refine Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor ?_
  rw [CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_unitStructureMap,
    moduleSheafFunctor_map_unitStructureMap]
  exact t.commutes

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The comparison `f^*𝒪 ⟶ 𝒪'` of a morphism of ringed topoi is 2-isomorphism invariant**, read
through `AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso`: the comparison of pullbacks
of a 2-isomorphism followed by the comparison map of `g` is the comparison map of `f`.

This is the transpose of
`AlgebraicGeometry.RingedToposHom.TwoIso.unitStructureMap_comp_pushforwardModulesIso_hom_app`
under [Stacks, Tag 03D7]. `pullbackModulesIso` is a `CategoryTheory.Adjunction.leftAdjointUniq`
taken over `CategoryTheory.Adjunction.ofNatIsoRight` of `pushforwardModulesIso`, so transposing
it produces that factor, and it is removed by cancelling it as a monomorphism. -/
theorem pullbackModulesIso_hom_app_comp_pullbackUnitStructureMap :
    t.pullbackModulesIso.hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        pullbackUnitStructureMap g =
      pullbackUnitStructureMap f := by
  apply ((pullbackAdjPushforwardModules f).homEquiv _ _).injective
  refine Eq.trans ?_ (homEquiv_pullbackUnitStructureMap f).symm
  rw [← cancel_mono (t.pushforwardModulesIso.hom.app
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))]
  refine Eq.trans ?_ (unitStructureMap_comp_pushforwardModulesIso_hom_app t).symm
  rw [← Adjunction.homEquiv_ofNatIsoRight_apply,
    show t.pullbackModulesIso.hom.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) =
      (Adjunction.leftAdjointUniq
        ((pullbackAdjPushforwardModules f).ofNatIsoRight t.pushforwardModulesIso)
        (pullbackAdjPushforwardModules g)).hom.app _ from rfl,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit, homEquiv_pullbackUnitStructureMap]

end UnitComparison

section Ideal

open Stacks.SheafOfModules.ImageSubsheaf

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {f g : RingedToposHom X Y} (t : TwoIso f g)
  (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-- **The canonical map `f^*ℐ ⟶ 𝒪'` of a morphism of ringed topoi is 2-isomorphism invariant**,
through the comparison of pullbacks: the canonical map of `f` is the comparison of pullbacks
followed by the canonical map of `g`. -/
theorem inverseImageIdealMap_eq_comp :
    inverseImageIdealMap.{u} f I =
      t.pullbackModulesIso.hom.app I.toSheafOfModules ≫ inverseImageIdealMap.{u} g I := by
  change (f.toModulesHom.pullbackModules).map I.ι ≫ pullbackUnitStructureMap f =
    t.pullbackModulesIso.hom.app I.toSheafOfModules ≫
      ((g.toModulesHom.pullbackModules).map I.ι ≫ pullbackUnitStructureMap g)
  rw [← pullbackModulesIso_hom_app_comp_pullbackUnitStructureMap t]
  simp only [← Category.assoc]
  rw [t.pullbackModulesIso.hom.naturality I.ι]

include t in
/-- **`ℐ' = f^{-1}ℐ · 𝒪_X` depends on the morphism of ringed topoi only through its
2-isomorphism class.** Two 2-isomorphic morphisms of ringed topoi build the same ideal sheaf out
of the same sheaf of ideals `ℐ ⊂ 𝒪`. No hypothesis on `ℐ`, and none on either morphism.

Together with the functoriality
`AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_comp` this is what matches the sheaves
of ideals along a square of ringed topoi that commutes only up to a 2-isomorphism, as the square
of [Stacks, Tag 03CR] does.

The canonical map of `f` is the canonical map of `g` precomposed with an isomorphism, by
`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIdealMap_eq_comp`, and the image subsheaf is
insensitive to that, by
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp`. -/
theorem inverseImageIdealSheaf_eq :
    inverseImageIdealSheaf.{u} f I = inverseImageIdealSheaf.{u} g I := by
  refine Eq.trans (congrArg (fun m ↦ imageSubmodule m) (inverseImageIdealMap_eq_comp t I)) ?_
  exact imageSubmodule_iso_hom_comp (t.pullbackModulesIso.app I.toSheafOfModules)
    (inverseImageIdealMap.{u} g I)

end Ideal

end AlgebraicGeometry.RingedToposHom.TwoIso

end
