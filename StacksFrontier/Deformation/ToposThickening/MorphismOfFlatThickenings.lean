module

public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickeningsIdealMap
import StacksCore.Tactic.StacksAttribute

/-!
# A morphism of flat first order thickenings of a morphism of ringed topoi

Let `f : (Sh(C), O) ⟶ (Sh(B), O_B)` be a morphism of ringed topoi. Stacks 0CYD fixes a
commutative diagram

```
  (Sh(C'₁), O'₁)      --h-->  (Sh(C'₂), O'₂)
      |                           |
      f'₁                         f'₂
      v                           v
  (Sh(B'₁), O_{B'₁})  --k-->  (Sh(B'₂), O_{B'₂})
```

in which `h` is a morphism of first order thickenings of `(Sh(C), O)`, `k` is a morphism of
first order thickenings of `(Sh(B), O_B)`, both `f'ᵢ` restrict to `f`, both pairs `(f, f'ᵢ)`
are strict morphisms of thickenings, and both `f'ᵢ` are flat; together with an `O`-module `ℱ`
flat over `O_B`.

This is the standing hypothesis of the comparison of obstruction classes of Stacks 0CYE: the
two thickenings deform `f` and the morphism between them compares the two deformation
problems for `ℱ`.

## Main definitions

* `Deformation.ToposThickening.FlatThickeningMorphismSituation`: **Stacks 0CYD**, the whole
  situation.

## Implementation notes

The two vertical squares are `Deformation.ToposThickening.MorphismOfThickenings` of Stacks
08M7, which already carry the thickening conditions on their horizontal arrows and their two
defining ideals; the first order conditions upgrade those, and strictness is
`Deformation.ToposThickening.MorphismOfThickenings.IsStrict` of Stacks 08M9. "Both `f'ᵢ`
restrict to `f`" is the single equation `D₂.f = D₁.f` rather than a parameter `f` together
with two equations identifying it with `D₁.f` and `D₂.f`; the two readings carry the same
information and the one chosen here lets the first square be used without rewriting.

The morphism `h` of the upper thickenings is recorded by the equation `h ∘ i₁ = i₂` and the
morphism `k` of the lower ones by `k ∘ t₁ = t₂`, which is what it means for them to be
morphisms of thickenings of the fixed `(Sh(C), O)` and `(Sh(B), O_B)`; that `h` and `k` are
again thickenings is not part of the source's hypothesis and is not assumed.

Flatness of a morphism of ringed topoi is `AlgebraicGeometry.RingedToposHom.IsFlat` of Stacks
04JB, and flatness of `ℱ` over `O_B` is flatness in the sense of Stacks 03ER of `ℱ` with its
scalars restricted along the inverse-image form `f⁻¹O_B ⟶ O` of the structure map of `f`.

The section universes of the six structure sheaves and the section universe of `ℱ` are
independent, as are the universes of the six sites; the sheafification hypotheses are imposed
only on the two upper thickened topoi, where the pullback of sheaves of modules computing the
map of defining ideals is formed, and on `(Sh(C), O)` at the section universe of `ℱ`, where
the tensor product testing flatness is formed.

## References

* [Stacks Project, Tag 0CYD](https://stacks.math.columbia.edu/tag/0CYD)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe v u w v₁ u₁ w₁ v₂ u₂ w₂ vS uS wS vS₁ uS₁ wS₁ vS₂ uS₂ wS₂ z

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {X₁ : RingedTopos.{v₁, u₁, w₁}}
  {X₂ : RingedTopos.{v₂, u₂, w₂}} {S : RingedTopos.{vS, uS, wS}}
  {S₁ : RingedTopos.{vS₁, uS₁, wS₁}} {S₂ : RingedTopos.{vS₂, uS₂, wS₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X₁.J.HasSheafCompose (forget RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget RingCat.{w₂})] [S.J.HasSheafCompose (forget RingCat.{wS})]
  [S₁.J.HasSheafCompose (forget RingCat.{wS₁})] [S₂.J.HasSheafCompose (forget RingCat.{wS₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S₁.J.HasSheafCompose (forget₂ CommRingCat.{wS₁} RingCat.{wS₁})]
  [S₂.J.HasSheafCompose (forget₂ CommRingCat.{wS₂} RingCat.{wS₂})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S₁.J.HasSheafCompose (forget AddCommGrpCat.{wS₁})]
  [S₂.J.HasSheafCompose (forget AddCommGrpCat.{wS₂})]
  [HasWeakSheafify X₁.J AddCommGrpCat.{w₁}]
  [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify X₂.J AddCommGrpCat.{w₂}]
  [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [HasWeakSheafify X.J AddCommGrpCat.{z}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- **Stacks 0CYD.** Two strict flat morphisms of first order thickenings of one morphism of
ringed topoi `f : (Sh(C), O) ⟶ (Sh(B), O_B)`, related by a morphism of the thickenings they
deform `f` by, together with an `O`-module flat over `O_B`. -/
@[stacks 0CYD "the situation"]
structure FlatThickeningMorphismSituation
    (D₁ : MorphismOfThickenings X X₁ S S₁) (D₂ : MorphismOfThickenings X X₂ S S₂) where
  /-- The morphism of the two thickenings of `(Sh(C), O)`. -/
  h : RingedToposHom X₁ X₂
  /-- The morphism of the two thickenings of `(Sh(B), O_B)`. -/
  k : RingedToposHom S₁ S₂
  /-- `h` is a morphism of thickenings of `(Sh(C), O)`: it is compatible with the two
  thickening maps out of `(Sh(C), O)`. -/
  source_comm : h.comp D₁.i = D₂.i
  /-- `k` is a morphism of thickenings of `(Sh(B), O_B)`: it is compatible with the two
  thickening maps out of `(Sh(B), O_B)`. -/
  base_comm : k.comp D₁.t = D₂.t
  /-- Both deformations restrict to the same morphism `f` on `(Sh(C), O)`. -/
  reduction_eq : D₂.f = D₁.f
  /-- The square of the two deformations and the two morphisms of thickenings commutes. -/
  ambient_comm : D₂.f'.comp h = k.comp D₁.f'
  /-- The first thickening of `(Sh(C), O)` is of first order. -/
  source₁_firstOrder : IsFirstOrderThickening D₁.i
  /-- The second thickening of `(Sh(C), O)` is of first order. -/
  source₂_firstOrder : IsFirstOrderThickening D₂.i
  /-- The first thickening of `(Sh(B), O_B)` is of first order. -/
  base₁_firstOrder : IsFirstOrderThickening D₁.t
  /-- The second thickening of `(Sh(B), O_B)` is of first order. -/
  base₂_firstOrder : IsFirstOrderThickening D₂.t
  /-- The first square is a strict morphism of thickenings. -/
  first_strict : D₁.IsStrict
  /-- The second square is a strict morphism of thickenings. -/
  second_strict : D₂.IsStrict
  /-- The first deformation of `f` is flat. -/
  first_flat : D₁.f'.IsFlat
  /-- The second deformation of `f` is flat. -/
  second_flat : D₂.f'.IsFlat
  /-- The `O`-module being deformed. -/
  F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  /-- The module is flat over `O_B`, that is, flat for its `f⁻¹O_B`-module structure. -/
  F_isFlat : AlgebraicGeometry.SheafOfModules.IsFlat
    ((SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        D₁.f.fSharpInverseImage)).obj F)

end Deformation.ToposThickening

end
