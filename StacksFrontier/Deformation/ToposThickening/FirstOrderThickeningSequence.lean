module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickeningsIdealMap
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposId

/-!
# Sequences of first order thickenings of a ringed topos

Let `(Sh(C), O)` be a ringed topos. A *sequence of morphisms of first order thickenings* of it
is a pair of composable morphisms

```
  (Sh(D₁), O'₁) --f₁₂--> (Sh(D₂), O'₂) --f₂₃--> (Sh(D₃), O'₃)
```

each `(Sh(Dₖ), O'ₖ)` being a first order thickening `iₖ` of `(Sh(C), O)`, and each `fₖ` being a
morphism of thickenings over the identity of `(Sh(C), O)`. Writing `Iₖ = Ker(iₖ^♯)` for the
defining ideals, the induced maps of defining ideals of Stacks 08M7 give maps
`f₁₂^*I₂ ⟶ I₁` and `f₂₃^*I₃ ⟶ I₂`. The sequence is a *complex* when the composite of the two is
zero, and a *short exact sequence* when the resulting short complex

```
  0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0
```

is short exact.

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickeningSequence`: a sequence of morphisms of first
  order thickenings of a fixed ringed topos.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.idealSequenceMap`: the composite
  `f₁₂^*f₂₃^*I₃ ⟶ I₁` of the two induced maps of defining ideals.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.IsComplex`: **Stacks 08ML**, the
  condition that the two maps of defining ideals compose to zero.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.IsShortExactSequence`:
  **Stacks 08ML**, the condition that they form a short exact sequence of ideal sheaves.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningSequence.isComplex_of_isShortExactSequence`:
  a short exact sequence is in particular a complex.

## Implementation notes

The two conditions are equations and exactness statements about morphisms of sheaves of
`O'₁`-modules on the topos of the smallest thickening `(Sh(D₁), O'₁)`, rather than about
morphisms of `O`-modules on `Sh(C)`. This is where the induced maps of defining ideals of
`Deformation.ToposThickening.MorphismOfThickenings.idealMap` already live, and it is the same
condition: the underlying topoi of a thickening and of its base are identified by the
thickening, and each `Iₖ` is annihilated by every ideal and so is an `O`-module and not merely
an `O'ₖ`-module. Transporting the equation along those identifications to `Sh(C)`, which is the
literal reading of the source, would require naming the reduction of each ideal to the base
topos; that is not part of
`StacksFrontier/Deformation/ToposThickening/MorphismOfThickeningsIdealMap.lean`, and nothing is
gained by it, the pullback functors involved being equivalences on the ideals.

To form the sequence at all, the outer two ideals have to be carried to the topos where the
innermost one lives, which is what the pullbacks `f₁₂^*` and `f₁₂^*f₂₃^*` in the displayed maps
do. The source leaves this transport implicit, writing `I₃ ⟶ I₂ ⟶ I₁` as if the three ideals
were objects of one category.

The three first order thickenings and their defining ideals are fields, while the four ringed
topoi are parameters, as in `Deformation.ToposThickening.MorphismOfThickenings`: the
sheafification hypotheses needed to form the pullbacks of sheaves of modules are then stated
once as instance arguments.

## Scope

This file formalizes the two *definitions* of the remark. The consequence drawn in its first
paragraph — that for a complex the composite `(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)` factors through
`(Sh(C), O)`, so that `(Sh(D₁), O'₁)` is a trivial first order thickening of `(Sh(C), O)` and
carries a canonical trivialization `π` — is not here.

## References

* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe v u w v₁ u₁ w₁ v₂ u₂ w₂ v₃ u₃ w₃

namespace Deformation.ToposThickening

section Sequence

variable (X : RingedTopos.{v, u, w}) (X₁ : RingedTopos.{v₁, u₁, w₁})
  (X₂ : RingedTopos.{v₂, u₂, w₂}) (X₃ : RingedTopos.{v₃, u₃, w₃})
  [X.J.HasSheafCompose (forget RingCat.{w})] [X₁.J.HasSheafCompose (forget RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget RingCat.{w₂})] [X₃.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X₃.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]

/-- **Stacks 08ML.** A sequence of morphisms of first order thickenings of a ringed topos
`X`: three first order thickenings `i₁`, `i₂`, `i₃` of `X`, with their defining ideals, and two
composable morphisms `f₁₂`, `f₂₃` between them lying over the identity of `X`. -/
@[stacks 08ML "the sequence of morphisms of first order thickenings being classified"]
structure FirstOrderThickeningSequence where
  /-- The first thickening of `X`. -/
  i₁ : RingedToposHom X X₁
  /-- The second thickening of `X`. -/
  i₂ : RingedToposHom X X₂
  /-- The third thickening of `X`. -/
  i₃ : RingedToposHom X X₃
  /-- The first thickening is first order. -/
  firstOrder₁ : IsFirstOrderThickening i₁
  /-- The second thickening is first order. -/
  firstOrder₂ : IsFirstOrderThickening i₂
  /-- The third thickening is first order. -/
  firstOrder₃ : IsFirstOrderThickening i₃
  /-- The defining ideal `I₁ = Ker(i₁^♯)`. -/
  ideal₁ : IdealOfThickening i₁
  /-- The defining ideal `I₂ = Ker(i₂^♯)`. -/
  ideal₂ : IdealOfThickening i₂
  /-- The defining ideal `I₃ = Ker(i₃^♯)`. -/
  ideal₃ : IdealOfThickening i₃
  /-- The first morphism of the sequence. -/
  f₁₂ : RingedToposHom X₁ X₂
  /-- The second morphism of the sequence. -/
  f₂₃ : RingedToposHom X₂ X₃
  /-- The first morphism lies over the identity of `X`. -/
  comm₁₂ : f₁₂.comp i₁ = i₂.comp (RingedToposHom.id X)
  /-- The second morphism lies over the identity of `X`. -/
  comm₂₃ : f₂₃.comp i₂ = i₃.comp (RingedToposHom.id X)

namespace FirstOrderThickeningSequence

variable {X X₁ X₂ X₃}

/-- The first morphism of the sequence, read as a morphism of thickenings of Stacks 08M7: the
commutative square with `i₁` above, `i₂` below, the identity of `X` on the left and `f₁₂` on the
right. -/
noncomputable def square₁₂ (S : FirstOrderThickeningSequence X X₁ X₂ X₃) :
    MorphismOfThickenings X X₁ X X₂ where
  i := S.i₁
  t := S.i₂
  f := RingedToposHom.id X
  f' := S.f₁₂
  i_isThickening := S.firstOrder₁.isThickening
  t_isThickening := S.firstOrder₂.isThickening
  comm := S.comm₁₂
  idealI := S.ideal₁
  idealJ := S.ideal₂

/-- The second morphism of the sequence, read as a morphism of thickenings of Stacks 08M7. -/
noncomputable def square₂₃ (S : FirstOrderThickeningSequence X X₁ X₂ X₃) :
    MorphismOfThickenings X X₂ X X₃ where
  i := S.i₂
  t := S.i₃
  f := RingedToposHom.id X
  f' := S.f₂₃
  i_isThickening := S.firstOrder₂.isThickening
  t_isThickening := S.firstOrder₃.isThickening
  comm := S.comm₂₃
  idealI := S.ideal₂
  idealJ := S.ideal₃

section IdealMaps

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [X₃.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasWeakSheafify X₁.J AddCommGrpCat.{w₁}]
  [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify X₂.J AddCommGrpCat.{w₂}]
  [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  (S : FirstOrderThickeningSequence X X₁ X₂ X₃)

/-- The map `I₃ ⟶ I₂` of the sequence, carried to the topos of `X₁`: the induced map of
defining ideals `f₂₃^*I₃ ⟶ I₂` of the second square, pulled back along `f₁₂`. -/
noncomputable def idealMap₃₂ :
    (S.f₁₂.toModulesHom.pullbackModules).obj ((S.f₂₃.toModulesHom.pullbackModules).obj S.ideal₃.I) ⟶
      (S.f₁₂.toModulesHom.pullbackModules).obj S.ideal₂.I :=
  (S.f₁₂.toModulesHom.pullbackModules).map S.square₂₃.idealMap

/-- The map `I₂ ⟶ I₁` of the sequence: the induced map of defining ideals `f₁₂^*I₂ ⟶ I₁` of the
first square. -/
noncomputable def idealMap₂₁ :
    (S.f₁₂.toModulesHom.pullbackModules).obj S.ideal₂.I ⟶ S.ideal₁.I :=
  S.square₁₂.idealMap

/-- The composite `I₃ ⟶ I₂ ⟶ I₁` of the two maps of defining ideals of the sequence, carried to
the topos of `X₁`. -/
noncomputable def idealSequenceMap :
    (S.f₁₂.toModulesHom.pullbackModules).obj
        ((S.f₂₃.toModulesHom.pullbackModules).obj S.ideal₃.I) ⟶ S.ideal₁.I :=
  S.idealMap₃₂ ≫ S.idealMap₂₁

/-- **Stacks 08ML.** A sequence of morphisms of first order thickenings of a ringed topos is a
*complex* when the induced maps of its defining ideals compose to zero, so that
`I₃ ⟶ I₂ ⟶ I₁` is a complex of modules. -/
@[stacks 08ML "paragraph (1), the definition: the complex condition on the ideal maps"]
def IsComplex : Prop := S.idealSequenceMap = 0

/-- A sequence of morphisms of first order thickenings is a complex exactly when the composite
of its two maps of defining ideals vanishes. This is the definition, restated with the
composite written out. -/
theorem isComplex_iff :
    S.IsComplex ↔ S.idealMap₃₂ ≫ S.idealMap₂₁ = 0 := Iff.rfl

/-- The short complex `I₃ ⟶ I₂ ⟶ I₁` of defining ideals attached to a complex of first order
thickenings. -/
noncomputable def shortComplex (hS : S.IsComplex) :
    ShortComplex
      (SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X₁.J)) X₁.O)) :=
  ShortComplex.mk S.idealMap₃₂ S.idealMap₂₁ hS

/-- **Stacks 08ML.** A sequence of morphisms of first order thickenings of a ringed topos is a
*short exact sequence* when its induced maps of defining ideals form a short exact sequence
`0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` of modules: the sequence is a complex, the map `I₃ ⟶ I₂` is a
monomorphism, the map `I₂ ⟶ I₁` is an epimorphism, and the complex is exact in the middle. -/
@[stacks 08ML "paragraph (2): the short exact sequence condition on the ideal maps"]
def IsShortExactSequence : Prop := ∃ hS : S.IsComplex, (S.shortComplex hS).ShortExact

/-- A short exact sequence of first order thickenings is in particular a complex. -/
theorem isComplex_of_isShortExactSequence (hS : S.IsShortExactSequence) : S.IsComplex :=
  hS.choose

end IdealMaps

end FirstOrderThickeningSequence

end Sequence

end Deformation.ToposThickening

end
