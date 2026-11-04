module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.ObstructionCompatibility

/-!
# Compatibility of the flat lifting obstructions under a morphism of first order thickenings

Let `f : (Sh(C), O) ⟶ (Sh(B), O_ℬ)` be a morphism of ringed topoi deformed in two ways by strict
flat first order thickenings, and let the two deformations be related by a morphism of
thickenings, as in Stacks 0CYD:

```
  (Sh(C), O)  --i₁-->  (Sh(C'₁), O'₁)   <--h--   (Sh(C'₂), O'₂)
      |                     |                        |
      f                     f'₁                      f'₂
      v                     v                        v
  (Sh(B), O_ℬ) --t₁--> (Sh(B'₁), O_{ℬ'₁})         (Sh(B'₂), O_{ℬ'₂})
```

Each column carries the obstruction class of Stacks 08VW, the class `o(ℱ, f^*Jₖ ⊗_O ℱ, 1)` of
Stacks 08MF whose vanishing is the existence of a lift of `ℱ` to the `k`-th thickening flat over
the `k`-th thickening of the base. Stacks 0CYE says that the canonical map
`Ext²_O(ℱ, f^*J₂ ⊗_O ℱ) ⟶ Ext²_O(ℱ, f^*J₁ ⊗_O ℱ)` carries the class of the second column to the
class of the first.

## Main results

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings`
  `.existenceObstructionClass_first_tensorIdeal` (**Stacks 0CYE**): the comparison of the two
  obstruction classes, with the coefficient module of the `k`-th column written as `Iₖ ⊗_O ℱ`.

## Implementation notes

The upper row of the diagram is
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings`, the data of Stacks 08MJ: two
first order thickenings of `(Sh(C), O)` presented on one site together with
`h^♯ : O'₂ ⟶ O'₁` over `(Sh(C), O)`. Presenting both on one site is what puts the two `Ext²`
groups in one category, as in
`StacksFrontier/Deformation/ToposThickening/ObstructionCompatibility.lean`; it is also what the
source means by the underlying topoi of a thickening being identified. The second column's
thickening is `Deformation.ToposThickening.reshapeHom`, the same morphism of topoi with `O'₂` in
place of `O'₁`, so the two columns share the reduced source topos, the base topos `(Sh(B), O_ℬ)`
and the restriction `f`, and differ in their thickened topoi and thickenings of the base.

The whole content of Stacks 0CYE is the main result, and it is Stacks 0CYC —
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.existenceObstructionClass_first` —
instantiated at `Kₖ = Iₖ ⊗_O ℱ`, `cₖ = 1` and `κ = (I₂ ⟶ I₁) ⊗_O ℱ`; the commutation hypothesis
of 0CYC becomes `1 ∘ κ = κ ∘ 1`. Two readings are involved.

* The coefficient module of the `k`-th column is written `Iₖ ⊗_O ℱ`, with `Iₖ` the square-zero
  ideal of the `k`-th thickening, where the source writes `f^*Jₖ ⊗_O ℱ`. The two agree under the
  hypotheses of Stacks 0CYD, the map `f^*Jₖ ⟶ Iₖ` being an isomorphism by Stacks 08MQ; this is
  the same convention under which
  `Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero` states Stacks 08VW, so the
  two classes compared here are exactly the two classes that tag's criterion is about.
* The map on `Ext²` is taken to be the one induced by the map `I₂ ⟶ I₁` of square-zero ideals of
  the upper row, `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.idealMap`, where
  the source takes the one induced by the lower horizontal arrow through `J₂ ⟶ J₁`. Under the
  same identification `f^*Jₖ = Iₖ` these are the same map. Identifying them as terms would ask
  for the commutative square relating the two comparisons `f^*Jₖ ⊗ ℱ ⟶ Iₖ ⊗ ℱ` of
  `Deformation.ToposThickening.idealTensorComparison` with the two horizontal maps; those
  comparisons are formed over `O'` on the thickened topos while the classes live over `i_*O`, and
  the descent of a map of ideals from the one presentation to the other is not in the library —
  the same gap recorded in the scope section of
  `StacksFrontier/Deformation/ToposThickening/FlatLiftObstruction.lean` for parts (2) and (3) of
  Stacks 08VW. The lower horizontal arrow `k` of Stacks 0CYD is therefore not among the
  hypotheses: it enters the statement only through that identification, and assuming it without
  using it would be assuming nothing.

The two upper topoi share their section universe, as they must, both being presented on the site
of the first; that universe is arbitrary, as Stacks 0CYC holds for any thickened topos. The two
thickenings of the base keep independent sites and independent
section universes, and so do their structure sheaves.

## References

* [Stacks Project, Tag 0CYE](https://stacks.math.columbia.edu/tag/0CYE)
* [Stacks Project, Tag 0CYD](https://stacks.math.columbia.edu/tag/0CYD)
* [Stacks Project, Tag 0CYC](https://stacks.math.columbia.edu/tag/0CYC)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
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
/-- **Stacks 0CYE.** In the situation of Stacks 0CYD the canonical map
`Ext²_O(ℱ, f^*J₂ ⊗_O ℱ) ⟶ Ext²_O(ℱ, f^*J₁ ⊗_O ℱ)` carries the obstruction class
`o(ℱ, f^*J₂ ⊗_O ℱ, 1)` of the second column to the obstruction class `o(ℱ, f^*J₁ ⊗_O ℱ, 1)` of
the first.

The coefficient module of the `k`-th column is written `Iₖ ⊗_O ℱ` and the map on `Ext²` is the
one induced by the map `I₂ ⟶ I₁` of square-zero ideals of the upper row; under the hypotheses of
Stacks 0CYD the comparison `f^*Jₖ ⟶ Iₖ` is an isomorphism, which is the reading under which
`Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero` states Stacks 08VW. See the
implementation notes.

This is Stacks 0CYC at `Kₖ = Iₖ ⊗_O ℱ` and `cₖ = 1`. -/
@[stacks 0CYE "coefficients and Ext map written through the ideals Iₖ, which are f^*Jₖ by 08MQ"]
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
