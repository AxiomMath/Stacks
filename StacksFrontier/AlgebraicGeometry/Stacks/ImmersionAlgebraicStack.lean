module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionFppfLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFpqcLocalAtTarget

/-!
# Immersions of algebraic stacks (Stacks 04YL, 0502)

Following Stacks 04YL, a 1-morphism of algebraic stacks over `S` *is an open immersion*,
respectively *a closed immersion*, respectively *an immersion*, when it is representable by
algebraic spaces and is an open immersion, respectively a closed immersion, respectively an
immersion, in the sense of Stacks 04XB: every algebraic space representing its base change
along a scheme-valued point of the target has structural morphism of that kind, read as a
morphism of algebraic spaces over `S`.

The Stacks definition reads "representable, and an open immersion in the sense of Section
04XB"; the source then replaces "representable" by "representable by algebraic spaces" and
says the two notions are equivalent and that it will use the second without further mention.
The second is the form taken here.

## Main definitions

* `AlgebraicGeometry.Stack.IsOpenImmersion`, `AlgebraicGeometry.Stack.IsClosedImmersion`: the
  Stacks 04XB notions at `AlgebraicGeometry.Space.IsOpenImmersion` and
  `AlgebraicGeometry.Space.IsClosedImmersion`, for a 1-morphism of categories fibred in
  groupoids. They complete the pair `AlgebraicGeometry.Stack.IsImmersion` and
  `AlgebraicGeometry.Stack.IsLocallySeparated` of
  `StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMorphism`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsOpenImmersion`: **Stacks 04YL**, part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsClosedImmersion`: **Stacks 04YL**, part (2).
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsImmersion`: **Stacks 04YL**, part (3).

## Main results

* `AlgebraicGeometry.Stack.isOpenImmersion_iff_hasRelativeProperty` and
  `AlgebraicGeometry.Stack.isClosedImmersion_iff_hasRelativeProperty`: the two new predicates
  are the relative property of Stacks 03YK at `AlgebraicGeometry.Space.openImmersionProperty`
  and `AlgebraicGeometry.Space.closedImmersionProperty`, as soon as those properties are known
  to be local at the target for the fppf precoverage.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_iff_forall_hasRelativeProperty` and
  its two companions: the same identification for the three predicates of Stacks 04YL, in the
  form that quantifies over the proof of representability by algebraic spaces rather than using
  the one it has.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_comp`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isClosedImmersion_comp` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_comp`: **Stacks 0502**, composites of
  immersions of algebraic stacks are immersions of the same kind.

## Implementation notes

The three predicates are written out rather than expressed through
`AlgebraicGeometry.Stack.HasRelativeProperty`, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMorphism`:
`AlgebraicGeometry.Stack.HasRelativeProperty` carries two instance hypotheses on the property —
stability under base change and locality at the target for the fppf precoverage — and while
`AlgebraicGeometry.Spaces.ImmersionBaseChange` supplies the first for all three immersion
properties, the second is Stacks 041X, 0420 and 042U. Those hypotheses do not occur in the body
of `AlgebraicGeometry.Stack.HasRelativeProperty`, so writing the quantifier out gives *the same*
proposition with no hypothesis on the property; the five bridge lemmas certify that, taking the
locality instance as a hypothesis rather than looking it up, so that each is stated at the free
index universe of the precoverage.

The three composition results of Stacks 0502 carry no such hypothesis: they are
`AlgebraicGeometry.Stack.hasRelativeProperty_comp` (**Stacks 045B**) at the three immersion
properties, and all three of the instances that theorem asks for are supplied. Stability under
base change is **Stacks 02YW** and stability under composition is **Stacks 02YV**, both
instances of `StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange`. Locality at the target
for the fppf precoverage is, for open immersions,
`AlgebraicGeometry.Space.openImmersion_isLocalAtTarget_fpqc` (**Stacks 041X**) and, for closed
immersions, `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fpqc` (**Stacks 0420**),
each transported from the fpqc precoverage along
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage` (**Stacks 0DFQ**); for immersions
it is `AlgebraicGeometry.Space.isImmersion_isLocalAtTarget_fppf` (**Stacks 042U**), which is an
fppf statement to begin with, being an immersion of schemes not being known to be fpqc local on
the base. Representability of the composite is
`AlgebraicGeometry.isRepresentableByAlgebraicSpaces_comp` (**Stacks 0301**).

The three modules carrying those locality results are imported non-publicly, so that nothing
downstream of this one acquires them. Two things leak through a `public import` of them and
neither is wanted here. `AlgebraicGeometry.Space.openImmersion_isLocalAtTarget_fpqc` is an
`instance` whose index universe is a free parameter, so once it is in scope typeclass inference
can close a locality goal with that universe still a metavariable, which is an error in the
declaration that triggered the search and not in this file. And the closure of
`StacksFrontier.AlgebraicGeometry.Spaces.ImmersionFppfLocalAtTarget` reserves `over` as a token, so
every module downstream of this one would lose `over` as an identifier —
`AlgebraicGeometry.Stack.ThickeningMorphismOver` of
`StacksFrontier.AlgebraicGeometry.Stacks.Thickening` has a field of that name. Only the proofs in
this file need the three results, and a proof is all a non-public import has to support.

As in `AlgebraicGeometry.Stack.HasRelativeProperty`, a scheme-valued point of `𝒴` is a functor
from the big fppf site of a scheme `U` over `S` to the total category of `𝒴` lying over
`CategoryTheory.Over.map U.hom`, and quantifying over *all* algebraic spaces representing the
base change makes the condition independent of the choice made in Stacks 0402. The passage from
an algebraic space over `U` to one over `S` is the forward functor
`AlgebraicGeometry.spacesOverSmallerBaseFunctor` of Stacks 04SG, whose structural morphism is
read off by `AlgebraicGeometry.algebraicSpaceMap`.

The tag sits on the three predicates in the `AlgebraicGeometry.Stack.AlgebraicStacks`
namespace, which are the notions of Stacks 04YL as properties of a 1-morphism of *algebraic
stacks*; the two predicates in `AlgebraicGeometry.Stack` are the Stacks 04XB notions they are
built from, and Stacks 04XB's general definition is already tagged, as
`AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**), so they are untagged.

## References

* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 042U](https://stacks.math.columbia.edu/tag/042U)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0502](https://stacks.math.columbia.edu/tag/0502)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

section FiberedInGroupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is an open immersion* when every algebraic space representing
its base change along a scheme-valued point of the target has open immersion structural
morphism, read as a morphism of algebraic spaces over `S`. This is the notion of Stacks 04XB for
`AlgebraicGeometry.Space.IsOpenImmersion`; together with representability by algebraic spaces it
is part (1) of Stacks 04YL. -/
abbrev IsOpenImmersion (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsOpenImmersion B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is a closed immersion* when every algebraic space
representing its base change along a scheme-valued point of the target has closed immersion
structural morphism, read as a morphism of algebraic spaces over `S`. This is the notion of
Stacks 04XB for `AlgebraicGeometry.Space.IsClosedImmersion`; together with representability by
algebraic spaces it is part (2) of Stacks 04YL. -/
abbrev IsClosedImmersion (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsClosedImmersion B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- `AlgebraicGeometry.Stack.IsOpenImmersion` is the relative property of Stacks 03YK at
`AlgebraicGeometry.Space.openImmersionProperty`. The locality instance is a hypothesis rather
than a looked-up instance, because it is Stacks 041X, a Chapter 67 result this library does not
yet have. -/
theorem isOpenImmersion_iff_hasRelativeProperty
    [(Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    (f : 𝒳 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    IsOpenImmersion B S hS f ↔
      HasRelativeProperty B S hS (Space.openImmersionProperty B S hS) f hf :=
  Iff.rfl

/-- `AlgebraicGeometry.Stack.IsClosedImmersion` is the relative property of Stacks 03YK at
`AlgebraicGeometry.Space.closedImmersionProperty`. The locality instance is a hypothesis rather
than a looked-up instance, because it is Stacks 0420, a Chapter 67 result this library does not
yet have. -/
theorem isClosedImmersion_iff_hasRelativeProperty
    [(Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    (f : 𝒳 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    IsClosedImmersion B S hS f ↔
      HasRelativeProperty B S hS (Space.closedImmersionProperty B S hS) f hf :=
  Iff.rfl

end FiberedInGroupoids

namespace AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04YL**, part (1). A 1-morphism of algebraic stacks over `S` is an *open immersion*
when it is representable by algebraic spaces and is an open immersion in the sense of Stacks
04XB. -/
@[stacks 04YL "part (1): open immersions"]
abbrev IsOpenImmersion (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧ Stack.IsOpenImmersion B S hS f.hom

/-- **Stacks 04YL**, part (2). A 1-morphism of algebraic stacks over `S` is a *closed immersion*
when it is representable by algebraic spaces and is a closed immersion in the sense of Stacks
04XB. -/
@[stacks 04YL "part (2): closed immersions"]
abbrev IsClosedImmersion (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧ Stack.IsClosedImmersion B S hS f.hom

/-- **Stacks 04YL**, part (3). A 1-morphism of algebraic stacks over `S` is an *immersion* when
it is representable by algebraic spaces and is an immersion in the sense of Stacks 04XB. -/
@[stacks 04YL "part (3): immersions"]
abbrev IsImmersion (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧ Stack.IsImmersion B S hS f.hom

/-- Part (1) of Stacks 04YL, in the form that quantifies over the proof of representability
instead of using the one it has: the relative property of Stacks 03YK does not depend on that
proof, so the two forms agree. The locality instance is a hypothesis rather than a looked-up
instance, because it is Stacks 041X. -/
theorem isOpenImmersion_iff_forall_hasRelativeProperty
    [(Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (f : 𝒳 ⟶ 𝒴) :
    IsOpenImmersion B S hS f ↔
      (IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧
        ∀ hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom,
          HasRelativeProperty B S hS (Space.openImmersionProperty B S hS) f.hom hf) :=
  ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩

/-- Part (2) of Stacks 04YL, in the form that quantifies over the proof of representability
instead of using the one it has. The locality instance is a hypothesis rather than a looked-up
instance, because it is Stacks 0420. -/
theorem isClosedImmersion_iff_forall_hasRelativeProperty
    [(Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (f : 𝒳 ⟶ 𝒴) :
    IsClosedImmersion B S hS f ↔
      (IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧
        ∀ hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom,
          HasRelativeProperty B S hS (Space.closedImmersionProperty B S hS) f.hom hf) :=
  ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩

/-- Part (3) of Stacks 04YL, in the form that quantifies over the proof of representability
instead of using the one it has. The locality instance is a hypothesis rather than a looked-up
instance, because it is Stacks 042U. -/
theorem isImmersion_iff_forall_hasRelativeProperty
    [(Space.immersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (f : 𝒳 ⟶ 𝒴) :
    IsImmersion B S hS f ↔
      (IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧
        ∀ hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom,
          HasRelativeProperty B S hS (Space.immersionProperty B S hS) f.hom hf) :=
  ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩

variable {𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- Representability by algebraic spaces and the relative property of Stacks 03YK both pass to
composites of 1-morphisms of algebraic stacks (Stacks 045B and 0301). -/
private theorem comp_and_hasRelativeProperty
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsStableUnderComposition] (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hPf : HasRelativeProperty B S hS P f.hom hf) (hPg : HasRelativeProperty B S hS P g.hom hg) :
    IsRepresentableByAlgebraicSpaces B S hS (f ≫ g).hom.hom ∧
      Stack.HasRelativeProperty B S hS P (f ≫ g).hom
        (isRepresentableByAlgebraicSpaces_comp B S hS f.hom g.hom hf hg) :=
  ⟨isRepresentableByAlgebraicSpaces_comp B S hS f.hom g.hom hf hg,
    hasRelativeProperty_comp B S hS P f.hom g.hom hf hg hPf hPg⟩

/-- **Stacks 0502** for open immersions: a composite of open immersions of algebraic stacks
over `S` is an open immersion. -/
@[stacks 0502 "open immersions", ega "I 4.2.5" "open immersions"]
theorem isOpenImmersion_comp
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsOpenImmersion B S hS f) (hg : IsOpenImmersion B S hS g) :
    IsOpenImmersion B S hS (f ≫ g) :=
  have _hloc : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  comp_and_hasRelativeProperty B S hS (Space.openImmersionProperty B S hS) f g hf.1 hg.1 hf.2 hg.2

/-- **Stacks 0502** for closed immersions: a composite of closed immersions of algebraic
stacks over `S` is a closed immersion. -/
@[stacks 0502 "closed immersions", ega "I 4.2.5" "closed immersions"]
theorem isClosedImmersion_comp
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsClosedImmersion B S hS f) (hg : IsClosedImmersion B S hS g) :
    IsClosedImmersion B S hS (f ≫ g) :=
  have _hfpqc : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.precoverage.{u, u} .fpqc B S hS) :=
    Space.isClosedImmersion_isLocalAtTarget_fpqc B S hS
  have _hloc : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  comp_and_hasRelativeProperty B S hS (Space.closedImmersionProperty B S hS) f g hf.1 hg.1 hf.2 hg.2

/-- **Stacks 0502**: a composite of immersions of algebraic stacks over `S` is an
immersion. -/
@[stacks 0502 "immersions", ega "I 4.2.5" "immersions"]
theorem isImmersion_comp
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsImmersion B S hS f) (hg : IsImmersion B S hS g) :
    IsImmersion B S hS (f ≫ g) :=
  have _hloc : (Space.immersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isImmersion_isLocalAtTarget_fppf B S hS
  comp_and_hasRelativeProperty B S hS (Space.immersionProperty B S hS) f g hf.1 hg.1 hf.2 hg.2

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
