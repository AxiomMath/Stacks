module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.ObstructionCompatibility

/-!
# Compatibility of the flat lifting obstructions with coefficients `Iₖ ⊗_O ℱ`

For a morphism of first order thickenings `O'₂ ⟶ O'₁` of a ringed topos `(Sh(C), O)` presented on
one site, with defining ideals `I₂ ⟶ I₁`, and an `O`-module `ℱ`, the map
`Ext²_O(ℱ, I₂ ⊗_O ℱ) ⟶ Ext²_O(ℱ, I₁ ⊗_O ℱ)` induced by `I₂ ⟶ I₁` carries `o(ℱ, I₂ ⊗_O ℱ, 1)`
to `o(ℱ, I₁ ⊗_O ℱ, 1)`.

## Main results

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings`
  `.existenceObstructionClass_first_tensorIdeal`: the comparison above, which is Stacks 0CYC at
  `Kₖ = Iₖ ⊗_O ℱ`, `cₖ = 1` and `κ = (I₂ ⟶ I₁) ⊗_O ℱ`.

Stacks 0CYE, the same comparison in Situation 0CYD with the coefficients `f^*𝒥ₖ ⊗_O ℱ` and the
map induced by `f^*𝒥₂ ⟶ f^*𝒥₁`, is in
`StacksFrontier/Deformation/ToposThickening/FlatObstructionCompatibilityBaseIdeal.lean`.

## References

* [Stacks Project, Tag 0CYC](https://stacks.math.columbia.edu/tag/0CYC)
* [Stacks Project, Tag 0CYE](https://stacks.math.columbia.edu/tag/0CYE)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe v u w v₂ u₂ w₂ vS uS wS vS₁ uS₁ wS₁ vS₂ uS₂ wS₂ e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, w₂}}
  {S : RingedTopos.{vS, uS, wS}} {S₁ : RingedTopos.{vS₁, uS₁, wS₁}}
  {S₂ : RingedTopos.{vS₂, uS₂, wS₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [S.J.HasSheafCompose (forget RingCat.{wS})]
  [S₁.J.HasSheafCompose (forget RingCat.{wS₁})]
  [S₂.J.HasSheafCompose (forget RingCat.{wS₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S₁.J.HasSheafCompose (forget₂ CommRingCat.{wS₁} RingCat.{wS₁})]
  [S₂.J.HasSheafCompose (forget₂ CommRingCat.{wS₂} RingCat.{wS₂})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S₁.J.HasSheafCompose (forget AddCommGrpCat.{wS₁})]
  [S₂.J.HasSheafCompose (forget AddCommGrpCat.{wS₂})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [HasSheafify Y.J AddCommGrpCat.{w₂}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w₂}]
  {i : RingedToposHom X Y}

namespace MorphismOfFirstOrderThickenings

variable (D : MorphismOfFirstOrderThickenings i)
  [HasExt.{e} (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
  [HasExt.{e} (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasExt.{e} (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂))]
  (F : SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})] in
/-- **The comparison of the obstruction classes with coefficients `Iₖ ⊗_O ℱ`.** For a morphism of
first order thickenings presented on one site, the map `Ext²_O(ℱ, I₂ ⊗_O ℱ) ⟶ Ext²_O(ℱ, I₁ ⊗_O ℱ)`
induced by `I₂ ⟶ I₁` carries `o(ℱ, I₂ ⊗_O ℱ, 1)` to `o(ℱ, I₁ ⊗_O ℱ, 1)`.

This is Stacks 0CYC at `Kₖ = Iₖ ⊗_O ℱ` and `cₖ = 1`. Stacks 0CYE itself, with the coefficients
`f^*𝒥ₖ ⊗_O ℱ` and the map induced by `f^*𝒥₂ ⟶ f^*𝒥₁`, is
`MorphismOfFirstOrderThickenings.existenceObstructionClass_first_basePullbackIdeal` in
`StacksFrontier/Deformation/ToposThickening/FlatObstructionCompatibilityBaseIdeal.lean`.
-/
theorem existenceObstructionClass_first_tensorIdeal :
    existenceObstructionClass D.first F
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj D.first.I).obj F)
        (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj D.first.I).obj F)) =
      (existenceObstructionClass D.second F
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj D.second.I).obj F)
          (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj D.second.I).obj F))).comp
        (Abelian.Ext.mk₀
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).map D.idealMap).app F))
        (add_zero 2) :=
  D.existenceObstructionClass_first F _ _ _ _ _
    ((Category.id_comp _).trans (Category.comp_id _).symm)

end MorphismOfFirstOrderThickenings

end Deformation.ToposThickening

end
