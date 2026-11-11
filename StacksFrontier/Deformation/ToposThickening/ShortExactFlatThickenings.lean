module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.Deformation.ToposThickening.FirstOrderThickeningSequence
public import StacksFrontier.Deformation.ToposThickening.Trivialization.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# A short exact sequence of flat thickenings of a morphism of ringed topoi

Let `f : (Sh(C), O) ⟶ (Sh(B), O_B)` be a morphism of ringed topoi. Stacks 08VX fixes a
commutative diagram

```
  (Sh(C'₁), O'₁)     --h-->  (Sh(C'₂), O'₂)     ------>  (Sh(C'₃), O'₃)
      |                          |                           |
      f'₁                        f'₂                         f'₃
      v                          v                           v
  (Sh(B'₁), O_{B'₁}) ------->  (Sh(B'₂), O_{B'₂}) ------>  (Sh(B'₃), O_{B'₃})
```

in which the upper row is a short exact sequence of first order thickenings of `(Sh(C), O)`,
the lower row is a short exact sequence of first order thickenings of `(Sh(B), O_B)`, each
`f'ᵢ` restricts to `f`, each pair `(f, f'ᵢ)` is a strict morphism of thickenings and each
`f'ᵢ` is flat; together with an `O'₂`-module `ℱ'₂` flat over `O_{B'₂}`, its restriction
`ℱ = ℱ'₂ ⊗ O` to `(Sh(C), O)`, and the canonical splitting
`π : (Sh(C'₁), O'₁) ⟶ (Sh(C), O)` of the upper row.

The faithful formalization of that situation is
`Deformation.ToposThickening.FlatThickeningComplexSituation`, in the one-site presentation of
`Deformation.ToposThickening.FirstOrderThickeningComplex`. This file records a three-site variant
of it whose exactness condition on the rows is a different one, see below.

This is the standing hypothesis of the comparison, in the deformation theory of `ℱ`, between
the difference of the two flat lifts `π^*ℱ` and `h^*ℱ'₂` over `(Sh(C'₁), O'₁)` and the
obstruction to lifting `ℱ` over `(Sh(C'₃), O'₃)`.

## Main definitions

* `Deformation.ToposThickening.MorphismOfThickenings.ofFirstOrder`: the commutative square of
  Stacks 08M7 assembled from two first order thickenings, their defining ideals and a morphism
  between them.
* `Deformation.ToposThickening.ShortExactFlatThickeningSituation`: a variant of the situation
  of Stacks 08VX whose rows satisfy a pullback-based exactness condition different from the
  short exactness of Stacks 08ML; see its docstring. Situation 08VX itself is
  `Deformation.ToposThickening.FlatThickeningComplexSituation`.
* `Deformation.ToposThickening.ShortExactFlatThickeningSituation.F`: the `O`-module
  `ℱ = ℱ'₂ ⊗ O` of the variant.

## Implementation notes

The two rows are `Deformation.ToposThickening.FirstOrderThickeningSequence` of Stacks 08ML, which
carries the three first order thickenings of a fixed ringed topos, their defining ideals and the two
morphisms between them; the exactness imposed on a row is
`Deformation.ToposThickening.FirstOrderThickeningSequence.IsShortExactSequence`, exactness of the
sequence `f₁₂^*f₂₃^*I₃ ⟶ f₁₂^*I₂ ⟶ I₁` of module pullbacks. That is not the short exactness of
`0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` as `O`-modules asked for by Stacks 08ML: the module pullbacks are not exact
and change the modules involved (see the docstring of
`Deformation.ToposThickening.ShortExactFlatThickeningSituation`). The three vertical squares are not
recorded separately: each is the square of Stacks 08M7 cut out of the two rows at one index by
`MorphismOfThickenings.ofFirstOrder`, so that the defining ideals entering strictness are the rows'
own ideals and not a second copy of them. Strictness is
`Deformation.ToposThickening.MorphismOfThickenings.IsStrict` of Stacks 08M9, flatness of `f'ᵢ` is
`AlgebraicGeometry.RingedToposHom.IsFlat` of Stacks 04JB, and flatness of `ℱ'₂` over `O_{B'₂}` is
flatness in the sense of Stacks 03ER of `ℱ'₂` with its scalars restricted along the inverse-image
form `(f'₂)⁻¹O_{B'₂} ⟶ O'₂` of the structure map of `f'₂`.

`ℱ` is not a field: it is defined, as the pullback `i₂^*ℱ'₂ = ℱ'₂ ⊗_{O'₂} O` of Stacks 03D6
along the middle thickening of the upper row, which is what `ℱ'₂ ⊗ O` abbreviates.

The canonical splitting `π` is a field, of type
`Deformation.ToposThickening.Trivialization upper.i₁` of Stacks 08MG, together with the
equation that makes it *the* canonical splitting of Stacks 08ML rather than an arbitrary
retraction of `i₁`: the composite `(Sh(C'₁), O'₁) ⟶ (Sh(C'₃), O'₃)` of the upper row factors
through it. That equation is the invertible 2-morphism of Stacks 04IC, which is what it means
for a diagram of ringed topoi to commute, and it is the form in which Stacks 08ML produces the
splitting; the retraction property of `π` itself is already carried by `Trivialization`.
Carrying `π` with its characterising equation is not a choice of splitting: any two splittings
satisfying it agree up to the canonical 2-isomorphism, and no section of an existence statement
is taken.

The section universes of the eight structure sheaves and the universes of the eight sites are
independent. The sheafification hypotheses are imposed where a pullback of sheaves of modules
is formed: on the three thickened topoi of the upper row, where the maps of defining ideals of
the three squares live, on the first two thickened topoi of the lower row, where the maps of
defining ideals of that row live, and on `(Sh(C), O)`, where `ℱ` is formed.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG)
* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
* [Stacks Project, Tag 08VX](https://stacks.math.columbia.edu/tag/08VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe v u w v₁ u₁ w₁ v₂ u₂ w₂ v₃ u₃ w₃
universe vS uS wS vS₁ uS₁ wS₁ vS₂ uS₂ wS₂ vS₃ uS₃ wS₃

namespace Deformation.ToposThickening

section Square

variable {A : RingedTopos.{v, u, w}} {A' : RingedTopos.{v₁, u₁, w₁}}
  {B : RingedTopos.{vS, uS, wS}} {B' : RingedTopos.{vS₁, uS₁, wS₁}}
  [A.J.HasSheafCompose (forget RingCat.{w})] [A'.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{wS})] [B'.J.HasSheafCompose (forget RingCat.{wS₁})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [A'.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wS₁} RingCat.{wS₁})]

/-- The morphism of thickenings of Stacks 08M7 assembled from a first order thickening `i` of
`A`, a first order thickening `t` of `B`, their defining ideals, and a morphism `f'` of the two
thickened ringed topoi lying over a morphism `f : A ⟶ B`. -/
def MorphismOfThickenings.ofFirstOrder (i : RingedToposHom A A') (t : RingedToposHom B B')
    (f : RingedToposHom A B) (f' : RingedToposHom A' B') (hi : IsFirstOrderThickening i)
    (ht : IsFirstOrderThickening t) (Ii : IdealOfThickening i) (It : IdealOfThickening t)
    (comm : f'.comp i = t.comp f) : MorphismOfThickenings A A' B B' where
  i := i
  t := t
  f := f
  f' := f'
  i_isThickening := hi.isThickening
  t_isThickening := ht.isThickening
  comm := comm
  idealI := Ii
  idealJ := It

end Square

section Situation

variable {X : RingedTopos.{v, u, w}} {X₁ : RingedTopos.{v₁, u₁, w₁}}
  {X₂ : RingedTopos.{v₂, u₂, w₂}} {X₃ : RingedTopos.{v₃, u₃, w₃}}
  {S : RingedTopos.{vS, uS, wS}} {S₁ : RingedTopos.{vS₁, uS₁, wS₁}}
  {S₂ : RingedTopos.{vS₂, uS₂, wS₂}} {S₃ : RingedTopos.{vS₃, uS₃, wS₃}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X₁.J.HasSheafCompose (forget RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget RingCat.{w₂})] [X₃.J.HasSheafCompose (forget RingCat.{w₃})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S₁.J.HasSheafCompose (forget RingCat.{wS₁})]
  [S₂.J.HasSheafCompose (forget RingCat.{wS₂})] [S₃.J.HasSheafCompose (forget RingCat.{wS₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X₃.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S₁.J.HasSheafCompose (forget₂ CommRingCat.{wS₁} RingCat.{wS₁})]
  [S₂.J.HasSheafCompose (forget₂ CommRingCat.{wS₂} RingCat.{wS₂})]
  [S₃.J.HasSheafCompose (forget₂ CommRingCat.{wS₃} RingCat.{wS₃})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [X₃.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S₁.J.HasSheafCompose (forget AddCommGrpCat.{wS₁})]
  [S₂.J.HasSheafCompose (forget AddCommGrpCat.{wS₂})]
  [S₃.J.HasSheafCompose (forget AddCommGrpCat.{wS₃})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X₁.J AddCommGrpCat.{w₁}]
  [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify X₂.J AddCommGrpCat.{w₂}]
  [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [HasWeakSheafify X₃.J AddCommGrpCat.{w₃}]
  [X₃.J.WEqualsLocallyBijective AddCommGrpCat.{w₃}]
  [HasWeakSheafify S₁.J AddCommGrpCat.{wS₁}]
  [S₁.J.WEqualsLocallyBijective AddCommGrpCat.{wS₁}]
  [HasWeakSheafify S₂.J AddCommGrpCat.{wS₂}]
  [S₂.J.WEqualsLocallyBijective AddCommGrpCat.{wS₂}]

/-- A variant of the situation of Stacks 08VX in the three-site presentation: a sequence of
first order thickenings of a ringed topos `(Sh(C), O)` mapping to a sequence of first order
thickenings of a ringed topos `(Sh(B), O_B)`, by three strict flat deformations of one morphism
`f : (Sh(C), O) ⟶ (Sh(B), O_B)`, together with an `O'₂`-module flat over `O_{B'₂}` and the
canonical splitting of the upper row.

This is not Situation 08VX itself, whose faithful formalization is
`Deformation.ToposThickening.FlatThickeningComplexSituation`. The exactness imposed on each row
here is `Deformation.ToposThickening.FirstOrderThickeningSequence.IsShortExactSequence`, the
exactness of `f₁₂^*f₂₃^*I₃ ⟶ f₁₂^*I₂ ⟶ I₁` with the module pullbacks `f^* = O'₁ ⊗ f⁻¹(-)`,
whereas Stacks 08ML asks for exactness of `0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` as `O`-modules. The two
differ: for `O'₃ = k[x]/(x²) ⟶ O'₂ = k[x, y]/(x, y)² ⟶ O'₁ = k[y]/(y²)` over `O = k` the
sequence of ideals `0 ⟶ k ⟶ k² ⟶ k ⟶ 0` is exact, but `f₁₂^*f₂₃^*I₃ = k[y]/(y²)` maps to
`f₁₂^*I₂ = k²` with a nonzero kernel, so this structure excludes that basic instance. -/
structure ShortExactFlatThickeningSituation
    (upper : FirstOrderThickeningSequence X X₁ X₂ X₃)
    (lower : FirstOrderThickeningSequence S S₁ S₂ S₃) where
  /-- The upper row is a short exact sequence of first order thickenings of `(Sh(C), O)`. -/
  upper_shortExact : upper.IsShortExactSequence
  /-- The lower row is a short exact sequence of first order thickenings of
  `(Sh(B), O_B)`. -/
  lower_shortExact : lower.IsShortExactSequence
  /-- The morphism `f : (Sh(C), O) ⟶ (Sh(B), O_B)` being deformed. -/
  f : RingedToposHom X S
  /-- The deformation of `f` over the first thickenings. -/
  f'₁ : RingedToposHom X₁ S₁
  /-- The deformation of `f` over the second thickenings. -/
  f'₂ : RingedToposHom X₂ S₂
  /-- The deformation of `f` over the third thickenings. -/
  f'₃ : RingedToposHom X₃ S₃
  /-- The first deformation restricts to `f`. -/
  restrict₁ : f'₁.comp upper.i₁ = lower.i₁.comp f
  /-- The second deformation restricts to `f`. -/
  restrict₂ : f'₂.comp upper.i₂ = lower.i₂.comp f
  /-- The third deformation restricts to `f`. -/
  restrict₃ : f'₃.comp upper.i₃ = lower.i₃.comp f
  /-- The left square of the diagram commutes: the first morphism of the upper row lies over
  the first morphism of the lower row. -/
  comm₁₂ : f'₂.comp upper.f₁₂ = lower.f₁₂.comp f'₁
  /-- The right square of the diagram commutes: the second morphism of the upper row lies over
  the second morphism of the lower row. -/
  comm₂₃ : f'₃.comp upper.f₂₃ = lower.f₂₃.comp f'₂
  /-- The pair `(f, f'₁)` is a strict morphism of thickenings. -/
  strict₁ : (MorphismOfThickenings.ofFirstOrder upper.i₁ lower.i₁ f f'₁ upper.firstOrder₁
    lower.firstOrder₁ upper.ideal₁ lower.ideal₁ restrict₁).IsStrict
  /-- The pair `(f, f'₂)` is a strict morphism of thickenings. -/
  strict₂ : (MorphismOfThickenings.ofFirstOrder upper.i₂ lower.i₂ f f'₂ upper.firstOrder₂
    lower.firstOrder₂ upper.ideal₂ lower.ideal₂ restrict₂).IsStrict
  /-- The pair `(f, f'₃)` is a strict morphism of thickenings. -/
  strict₃ : (MorphismOfThickenings.ofFirstOrder upper.i₃ lower.i₃ f f'₃ upper.firstOrder₃
    lower.firstOrder₃ upper.ideal₃ lower.ideal₃ restrict₃).IsStrict
  /-- The first deformation of `f` is flat. -/
  flat₁ : f'₁.IsFlat
  /-- The second deformation of `f` is flat. -/
  flat₂ : f'₂.IsFlat
  /-- The third deformation of `f` is flat. -/
  flat₃ : f'₃.IsFlat
  /-- The `O'₂`-module `ℱ'₂` being deformed. -/
  F' : SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)
  /-- The module `ℱ'₂` is flat over `O_{B'₂}`, that is, flat for its
  `(f'₂)⁻¹O_{B'₂}`-module structure. -/
  F'_isFlat : AlgebraicGeometry.SheafOfModules.IsFlat
    ((SheafOfModules.restrictScalars
      ((sheafCompose X₂.J (forget₂ CommRingCat.{w₂} RingCat.{w₂})).map
        f'₂.fSharpInverseImage)).obj F')
  /-- The canonical splitting `π : (Sh(C'₁), O'₁) ⟶ (Sh(C), O)` of the upper row, as a
  retraction of its first thickening. -/
  π : Trivialization upper.i₁
  /-- The splitting is the canonical one: the composite
  `(Sh(C'₁), O'₁) ⟶ (Sh(C'₃), O'₃)` of the upper row factors through it. -/
  π_factorization :
    RingedToposHom.TwoIso (upper.i₃.comp π.retraction) (upper.f₂₃.comp upper.f₁₂)

namespace ShortExactFlatThickeningSituation

variable {upper : FirstOrderThickeningSequence X X₁ X₂ X₃}
  {lower : FirstOrderThickeningSequence S S₁ S₂ S₃}

/-- The `O`-module `ℱ = ℱ'₂ ⊗ O` of the variant
`Deformation.ToposThickening.ShortExactFlatThickeningSituation`: the pullback of `ℱ'₂` along
the middle thickening of the upper row. -/
noncomputable def F (D : ShortExactFlatThickeningSituation upper lower) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (upper.i₂.toModulesHom.pullbackModules).obj D.F'

end ShortExactFlatThickeningSituation

end Situation

end Deformation.ToposThickening

end
