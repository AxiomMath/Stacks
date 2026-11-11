module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickeningsIdealMap
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposCompId
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
zero, and a *short exact sequence* when the resulting sequence

```
  0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0
```

is a short exact sequence of `O`-modules.

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickeningSequence`: a sequence of morphisms of first
  order thickenings of a fixed ringed topos.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.idealSequenceMap`: the composite
  `f₁₂^*f₂₃^*I₃ ⟶ I₁` of the two induced maps of defining ideals.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.IsComplex`: **Stacks 08ML**, the
  condition that the two maps of defining ideals compose to zero.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.baseIdealMap₃₂` and
  `Deformation.ToposThickening.FirstOrderThickeningSequence.baseIdealMap₂₁`: the maps
  `I₃ ⟶ I₂ ⟶ I₁` of the source, as maps of `O`-modules on `(Sh(C), O)`.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.IsShortExactOnBase`:
  **Stacks 08ML**, the condition that `0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` is a short exact sequence of
  `O`-modules.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.IsShortExactSequence`: the
  stronger condition that the maps of pulled-back ideals `f₁₂^*f₂₃^*I₃ ⟶ f₁₂^*I₂ ⟶ I₁` form a
  short exact sequence of `O'₁`-modules. This is not the notion of the source.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningSequence.isComplex_of_isShortExactSequence`:
  a short exact sequence is in particular a complex.

## Implementation notes

Each defining ideal `Iₖ` of a first order thickening `iₖ` is killed by itself, so it is an
`O = O'ₖ/Iₖ`-module. As an `O`-module on `(Sh(C), O)` it is the pullback
`iₖ^*Iₖ = Iₖ ⊗_{O'ₖ} O = Iₖ/Iₖ²`, which is `baseIdeal₁`, `baseIdeal₂`, `baseIdeal₃`. Pulling
back the map `f₂₃^*I₃ ⟶ I₂` of Stacks 08M7 along `i₂` and composing with the comparison
`i₂^*f₂₃^* ≅ (f₂₃ ∘ i₂)^* = i₃^*` gives the `O`-linear map `I₃ ⟶ I₂` induced by `f₂₃^♯`, and
likewise for `I₂ ⟶ I₁`; this is `baseIdealMap₃₂` and `baseIdealMap₂₁`, and
`IsShortExactOnBase` asks that they form a short exact sequence of `O`-modules, as in the
source.

`IsComplex` and `IsShortExactSequence` are instead stated on the topos of the smallest
thickening `(Sh(D₁), O'₁)`, where the maps of
`Deformation.ToposThickening.MorphismOfThickenings.idealMap` live, with the outer two ideals
carried there by the pullbacks `f₁₂^*` and `f₁₂^*f₂₃^*`. For the complex condition this changes
nothing: `I₁` is an `O`-module, so by adjunction an `O'₁`-linear map `f₁₂^*f₂₃^*I₃ ⟶ I₁`
vanishes exactly when the corresponding map `I₃ ⟶ I₁` does. For short exactness it is a
strictly stronger condition, because the pullback `f^*M = f⁻¹M ⊗ O'₁` is only right exact and
does not return the ideals: `f₁₂^*f₂₃^*I₃ = I₃ ⊗_{O'₃} O'₁` can be bigger than `I₃`. On a
one-point site over a field `k`, with `O'₃ = k[x]/(x²)`, `O'₂ = k[x,y]/(x,y)²`,
`O'₁ = k[y]/(y²)`, `O = k` and the maps `x ↦ x` and `x ↦ 0, y ↦ y`, the sequence
`0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` is `0 ⟶ k ⟶ k² ⟶ k ⟶ 0`, short exact, but
`f₁₂^*f₂₃^*I₃ = k[y]/(y²)` maps to `f₁₂^*I₂ = k²`, which `y` kills, by a map that is not
injective.

The three first order thickenings and their defining ideals are fields, while the four ringed
topoi are parameters, as in `Deformation.ToposThickening.MorphismOfThickenings`: the
sheafification hypotheses needed to form the pullbacks of sheaves of modules are then stated
once as instance arguments.

## Scope

This file formalizes the two *definitions* of the remark. The consequence drawn in the first
paragraph of the remark — that for a complex the composite `(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)`
factors through `(Sh(C), O)`, so that `(Sh(D₁), O'₁)` is a trivial first order thickening of
`(Sh(C), O)` and carries a canonical trivialization `π` — is not here. That `IsComplex` is
equivalent to the vanishing of `baseIdealMap₃₂ ≫ baseIdealMap₂₁` is not proved here either.

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

/-- The maps of pulled-back defining ideals `f₁₂^*f₂₃^*I₃ ⟶ f₁₂^*I₂ ⟶ I₁` form a short exact
sequence of `O'₁`-modules on the topos of the smallest thickening.

This is **not** the short exact sequence condition of Stacks 08ML, which is
`IsShortExactOnBase`: it is strictly stronger, since the pullback `f₁₂^*f₂₃^*I₃` of
`I₃` can be bigger than `I₃` and then fails to inject into `f₁₂^*I₂` even when
`0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` is short exact (see the implementation notes of this file). -/
def IsShortExactSequence : Prop := ∃ hS : S.IsComplex, (S.shortComplex hS).ShortExact

/-- A short exact sequence of first order thickenings is in particular a complex. -/
theorem isComplex_of_isShortExactSequence (hS : S.IsShortExactSequence) : S.IsComplex :=
  hS.choose

section Base

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The defining ideal `I₁`, as an `O`-module on `(Sh(C), O)`: its pullback
`i₁^*I₁ = I₁ ⊗_{O'₁} O = I₁/I₁²`, which is `I₁` since the thickening is first order. -/
noncomputable def baseIdeal₁ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (S.i₁.toModulesHom.pullbackModules).obj S.ideal₁.I

/-- The defining ideal `I₂`, as an `O`-module on `(Sh(C), O)`: its pullback `i₂^*I₂`. -/
noncomputable def baseIdeal₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (S.i₂.toModulesHom.pullbackModules).obj S.ideal₂.I

/-- The defining ideal `I₃`, as an `O`-module on `(Sh(C), O)`: its pullback `i₃^*I₃`. -/
noncomputable def baseIdeal₃ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (S.i₃.toModulesHom.pullbackModules).obj S.ideal₃.I

/-- The comparison `i₂^*f₂₃^*I₃ ≅ (f₂₃ ∘ i₂)^*I₃ = i₃^*I₃`, the second morphism lying over the
identity of `X`. -/
noncomputable def basePullbackIso₃₂ :
    (S.i₂.toModulesHom.pullbackModules).obj
        ((S.f₂₃.toModulesHom.pullbackModules).obj S.ideal₃.I) ≅ S.baseIdeal₃ :=
  ((RingedToposHom.pullbackModulesCompIso S.i₂ S.f₂₃).app S.ideal₃.I).symm ≪≫
    eqToIso (congrArg (fun m : RingedToposHom X X₃ ↦ (m.toModulesHom.pullbackModules).obj
      S.ideal₃.I) (S.comm₂₃.trans (RingedToposHom.comp_id S.i₃)))

/-- The comparison `i₁^*f₁₂^*I₂ ≅ (f₁₂ ∘ i₁)^*I₂ = i₂^*I₂`, the first morphism lying over the
identity of `X`. -/
noncomputable def basePullbackIso₂₁ :
    (S.i₁.toModulesHom.pullbackModules).obj
        ((S.f₁₂.toModulesHom.pullbackModules).obj S.ideal₂.I) ≅ S.baseIdeal₂ :=
  ((RingedToposHom.pullbackModulesCompIso S.i₁ S.f₁₂).app S.ideal₂.I).symm ≪≫
    eqToIso (congrArg (fun m : RingedToposHom X X₂ ↦ (m.toModulesHom.pullbackModules).obj
      S.ideal₂.I) (S.comm₁₂.trans (RingedToposHom.comp_id S.i₂)))

/-- **Stacks 08ML.** The map `I₃ ⟶ I₂` of `O`-modules induced by the second morphism: the map
`f₂₃^*I₃ ⟶ I₂` of Stacks 08M7 pulled back to `(Sh(C), O)` along `i₂`. -/
noncomputable def baseIdealMap₃₂ : S.baseIdeal₃ ⟶ S.baseIdeal₂ :=
  S.basePullbackIso₃₂.inv ≫ (S.i₂.toModulesHom.pullbackModules).map S.square₂₃.idealMap

/-- **Stacks 08ML.** The map `I₂ ⟶ I₁` of `O`-modules induced by the first morphism: the map
`f₁₂^*I₂ ⟶ I₁` of Stacks 08M7 pulled back to `(Sh(C), O)` along `i₁`. -/
noncomputable def baseIdealMap₂₁ : S.baseIdeal₂ ⟶ S.baseIdeal₁ :=
  S.basePullbackIso₂₁.inv ≫ (S.i₁.toModulesHom.pullbackModules).map S.square₁₂.idealMap

/-- The sequence `I₃ ⟶ I₂ ⟶ I₁` of `O`-modules on `(Sh(C), O)`, given that it is a complex. -/
noncomputable def baseShortComplex (h : S.baseIdealMap₃₂ ≫ S.baseIdealMap₂₁ = 0) :
    ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  ShortComplex.mk S.baseIdealMap₃₂ S.baseIdealMap₂₁ h

/-- **Stacks 08ML.** A sequence of morphisms of first order thickenings of a ringed topos
`(Sh(C), O)` is a *short exact sequence* when the induced maps of defining ideals form a short
exact sequence `0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` of `O`-modules: the composite `I₃ ⟶ I₁` is zero, the
map `I₃ ⟶ I₂` is a monomorphism, the map `I₂ ⟶ I₁` is an epimorphism, and the sequence is
exact in the middle. Each ideal is read as an `O`-module through its pullback `iₖ^*Iₖ`. -/
@[stacks 08ML "paragraph (2): the short exact sequence `0 → I₃ → I₂ → I₁ → 0` of `O`-modules,
each ideal `Iₖ` read as the `O`-module `iₖ^*Iₖ = Iₖ/Iₖ²`"]
def IsShortExactOnBase : Prop :=
  ∃ h : S.baseIdealMap₃₂ ≫ S.baseIdealMap₂₁ = 0, (S.baseShortComplex h).ShortExact

/-- In a short exact sequence of first order thickenings the maps `I₃ ⟶ I₂ ⟶ I₁` of
`O`-modules compose to zero. -/
theorem baseIdealMap₃₂_comp_baseIdealMap₂₁_of_isShortExactOnBase (hS : S.IsShortExactOnBase) :
    S.baseIdealMap₃₂ ≫ S.baseIdealMap₂₁ = 0 :=
  hS.choose

end Base

end IdealMaps

end FirstOrderThickeningSequence

end Sequence

end Deformation.ToposThickening

end
