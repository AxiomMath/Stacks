module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRelativeConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismSurjectiveDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal

/-!
# Unramified 1-morphisms of algebraic stacks and their diagonal (Stacks 0CJ0)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is unramified (**Stacks 0CIT**) exactly
when it is locally of finite type (**Stacks 06FS**, part (1)) and its relative diagonal
`Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is étale (**Stacks 0CIL**).

Both directions are read off one diagram of algebraic spaces over `f`

```
U ---h---> V
|          |
a          b
v          v
𝒳 ---f---> 𝒴
```

with `b` smooth, `a` smooth and surjective, and every comparison 1-morphism from the diagram's
cone to a 2-fibre product of `(b, f)` étale. On such a diagram unramifiedness of `f` is
unramifiedness of `h`, local finite type of `f` is local finite type of `h`, and étaleness of
`Δ_f` is étaleness of `Δ_{U/V}`; the equivalence is then **Stacks 05W1** for morphisms of
algebraic spaces, which says that `h` is unramified exactly when it is locally of finite type
and `Δ_{U/V}` is an open immersion.

## Main definitions

* `AlgebraicGeometry.Stack.HasDiagonalDescentChart`: the diagram above together with the
  identification of the relative property of `Δ_f` with that property of `Δ_{U/V}`.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_diagonal_of_isEtale_diagonal`: a relative diagonal
  of a morphism of algebraic spaces over `S` which is étale is an open immersion.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isUnramified_iff_isLocallyOfFiniteType_and_isEtale_relativeDiagonal`: **Stacks 0CJ0**.

## Implementation notes

`AlgebraicGeometry.Stack.HasDiagonalDescentChart` is a hypothesis of the main theorem, and both
halves of it are general statements about `f` alone.

Its diagram clauses are `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram` — the diagram
**Stacks 0CIA** produces for a Deligne–Mumford 1-morphism — together with smoothness of the left
vertical 1-morphism and its surjectivity on objects. Those two are also part of what Stacks 0CIA
delivers: there the left vertical 1-morphism is a surjective étale 1-morphism onto `𝒳 ×_𝒴 V`
followed by the base change of the smooth `V ⟶ 𝒴`, so it is smooth, and a surjective étale
1-morphism is surjective on objects. They are named separately because the existential
smooth-diagram criterion of **Stacks 06FM**, which is how local finite type of `f` is read off
the diagram, asks for exactly these two. Stacks 0CIA itself is proved here only under the
structure theorem **Stacks 06N3**, taken as the hypothesis
`AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`.

Its last clause is the identification, for an arbitrary property of morphisms of algebraic spaces
which is stable under base change, local at the target for the fppf precoverage and local at the
source for the étale precoverage, of the Stacks 03YK relative property of `Δ_f` with that
property of `Δ_{U/V}`: the relative diagonal of `𝒳 ×_𝒴 V ⟶ V` is a base change of `Δ_f` along
the surjective smooth `V ⟶ 𝒴` (**Stacks 04YR**,
`AlgebraicGeometry.Stack.isTwoFibreProduct_diagonalBaseChangeSquare`), so the two agree by
**Stacks 06TY**, and over `𝒳 ×_𝒴 V` the comparison with `U ⟶ U ×_V U` is **Stacks 06M2** against
locality on the source. These are `AlgebraicGeometry.Stack.hasRelativeProperty_iff_of_fppfCover`
and `AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_cover`, but neither applies to a chart
as it is: the first consumes surjectivity, flatness and local finite presentation of the cover in
the smooth-diagram form of **Stacks 04ZS**, **06PW** and **06Q2** while a chart is recorded in
the Section 04XB relative form (the same passage between the two forms is what the hypothesis
`AlgebraicGeometry.Stack.IsAbsolutelyDMOfExistsEtalePresentation` stands for), and the second
needs the 1-morphism `U ×_V U ⟶ (𝒳 ×_𝒴 V) ×_V (𝒳 ×_𝒴 V)`. The clause is stated for an arbitrary
property and mentions neither unramifiedness nor local finite type.

`AlgebraicGeometry.Space.isOpenImmersion_diagonal_of_isEtale_diagonal` is one step of
**Stacks 05W5**, whose statement is an equivalence concluding more. It follows the argument
of `AlgebraicGeometry.Space.isOpenImmersion_diagonal_of_isUnramified`: a relative diagonal is a
representable monomorphism (**Stacks 03HK**), hence universally injective on every represented
base change, and a morphism of schemes which is étale and universally injective is an open
immersion (**Stacks 025G**).

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 042B](https://stacks.math.columbia.edu/tag/042B)
* [Stacks Project, Tag 04XX](https://stacks.math.columbia.edu/tag/04XX)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 05VZ](https://stacks.math.columbia.edu/tag/05VZ)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06M2](https://stacks.math.columbia.edu/tag/06M2)
* [Stacks Project, Tag 06TY](https://stacks.math.columbia.edu/tag/06TY)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CJ0](https://stacks.math.columbia.edu/tag/0CJ0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_UnramifiedDiagonalCriterion :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_UnramifiedDiagonalCriterion
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace Space

/-- **Stacks 042B at the fppf precoverage.** Étaleness of a morphism of algebraic spaces over
`S` is local on the base for the fppf precoverage of Stacks 03YH. The content is the fpqc
statement `AlgebraicGeometry.Space.isEtale_isLocalAtTarget_fpqc`; this is the form the relative
properties of Stacks 03YK take as an instance argument. -/
instance isEtale_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => IsEtale B S hS g.hom)
      (Topology.fppf.precoverage.{u, v} B S hS) :=
  (isEtale_isLocalAtTarget_fpqc.{u, v} B S hS).of_le
    (fppfPrecoverage_le_fpqcPrecoverage.{u, v} B S hS)

/-- **An étale relative diagonal of a morphism of algebraic spaces over `S` is an open
immersion.** The relative diagonal is a representable monomorphism by Stacks 03HK, so each of
its represented base changes is a monomorphism of schemes, hence universally injective; an
étale universally injective morphism of schemes is an open immersion. -/
theorem isOpenImmersion_diagonal_of_isEtale_diagonal
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsEtale B S hS (pullback.diagonal f)) :
    IsOpenImmersion B S hS (pullback.diagonal f) := by
  have hXX : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback B S hS f f hX hX hY
  have hmono := monomorphisms_diagonal B S hS hX f
  have hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.diagonal f) :=
    (holdsOnEveryEtaleChart_iff_relative B S hS
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      etale_isEtaleLocalOnSourceAndTarget hX hXX (pullback.diagonal f) hmono.rep).1
      ((isEtale_iff_holdsOnEveryEtaleChart B S hS hX hXX (pullback.diagonal f)).1 hf)
  refine ⟨hetale.rep, fun a b gg fst snd hsq => ?_⟩
  have _ : Mono ((BigFppfOver.toScheme B S hS).map snd) := hmono.property gg fst snd hsq
  have he : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map snd) :=
    hetale.property gg fst snd hsq
  have h2 : AlgebraicGeometry.UniversallyInjective ((BigFppfOver.toScheme B S hS).map snd) ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map snd) := ⟨inferInstance, he⟩
  show AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map snd)
  exact ((AlgebraicGeometry.tfae_isOpenImmersion
    ((BigFppfOver.toScheme B S hS).map snd)).out 2 1).mp h2

end Space

namespace Stack

/-- **A diagram of algebraic spaces over `f` on which the relative diagonal is computed.** There
are algebraic spaces `U`, `V` over `S`, a smooth 1-morphism `b : V ⟶ 𝒴`, a smooth 1-morphism
`a : U ⟶ 𝒳` which is surjective and surjective on objects, a morphism `h : U ⟶ V` of algebraic
spaces and an invertible 2-cell making the square 2-commute, such that every comparison
1-morphism from the square's cone to a 2-fibre product of `(b, f)` is étale and such that, for
every property `P` of morphisms of algebraic spaces over `S` which is stable under base change,
local at the target for the fppf precoverage and local at the source for the étale precoverage,
the Stacks 03YK relative property `P` of the relative diagonal of `f` holds exactly when `P`
holds for the relative diagonal of `h`. -/
abbrev HasDiagonalDescentChart {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom),
      IsSurjective B S hS a ∧
      IsSurjectiveOnObjects B S hS (fibredCategory B S hS U).val.p 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor a.hom) ∧
      IsRelativelySmooth B S hS a.hom ∧
      IsRelativelySmooth B S hS b.hom ∧
      (∀ (Q : Bicategory.TwoCommSq b.hom f.hom)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f.hom a.hom b.hom h η) Q),
          IsRelativelyEtale B S hS k.hom) ∧
      ∀ (P : MorphismProperty (AlgebraicSpaces B S hS))
        [P.IsStableUnderBaseChange]
        [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
        [P.IsLocalAtSource (Space.Topology.etale.precoverage.{u, u} B S hS)],
        (HasRelativeProperty.{u, u, u + 1, u} B S hS P
            (AlgebraicStacks.relativeDiagonal B S hS f).hom
            (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f) ↔
          P (ObjectProperty.homMk (pullback.diagonal h) :
            (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨pullback h h, isAlgebraicSpace_pullback B S hS h h hU hU hV⟩))

namespace AlgebraicStacks

/-- **Stacks 0CJ0.** A 1-morphism of algebraic stacks over `S` admitting a diagram of algebraic
spaces as in `AlgebraicGeometry.Stack.HasDiagonalDescentChart` is unramified exactly when it is
locally of finite type and its relative diagonal is étale.

Unramifiedness and local finite type are tested on the diagram's top morphism `h` of algebraic
spaces, and étaleness of the relative diagonal is tested on the relative diagonal of `h`; the
equivalence is then Stacks 05W1. Deligne–Mumfordness in the converse direction comes from
étaleness of the relative diagonal, étale morphisms of algebraic spaces being unramified by
Stacks 06CR. -/
@[stacks 0CJ0 "both implications: unramified iff locally of finite type with etale diagonal"]
theorem isUnramified_iff_isLocallyOfFiniteType_and_isEtale_relativeDiagonal
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hchart : Stack.HasDiagonalDescentChart.{u, w} B S hS f) :
    Stack.IsUnramified B S hS f ↔
      (IsLocallyOfFiniteType B S hS f ∧
        Stack.IsEtale B S hS (relativeDiagonal B S hS f)) := by
  obtain ⟨U, V, hU, hV, a, b, h, η, hasurj, hasuobj, hasm, hbsm, hcomp, hcrit⟩ := hchart
  have hΔ : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal B S hS f).hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hcritE := hcrit (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
    Space.IsEtale B S hS g.hom)
  constructor
  · rintro ⟨-, hevery⟩
    have hun : Space.IsUnramified B S hS h := hevery U V hU hV a b h η hbsm hcomp
    exact ⟨Stack.hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram B S hS
        (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS) f.hom
        ⟨U, V, hU, hV, a.hom, b.hom, h, ⟨η⟩, hasm, hasuobj, hbsm,
          Space.isLocallyOfFiniteType_of_isUnramified B S hS hun⟩,
      isEtale_of_isRelativelyEtale B S hS _ ⟨hΔ, hcritE.2 (Space.isEtale_of_isOpenImmersion B S hS
          (Space.isOpenImmersion_diagonal_of_isUnramified B S hS hU hV h hun))⟩⟩
  · rintro ⟨hlftf, hΔet⟩
    have hΔrel : Stack.HasRelativeProperty.{u, u, u + 1, u} B S hS
        (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsEtale B S hS g.hom)
        (relativeDiagonal B S hS f).hom hΔ := by
      refine Stack.hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram.{u, u, w} B S hS _
        (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS) _ hΔ ?_
      refine Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram
        B S hS _ _ ?_ hΔet.2
      obtain ⟨U', V', hU', hV', a', b', h', η', hsu', hbsm', hcomp', -⟩ :=
        Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty.{u, u, w} B S hS
          (⊤ : MorphismProperty (AlgebraicSpaces B S hS)) _ hΔ
          (fun _ _ _ _ _ _ => trivial)
      exact ⟨U', V', hU', hV', a', b', h', η', hsu', hbsm', hcomp'⟩
    have hoi : Space.IsOpenImmersion B S hS (pullback.diagonal h) :=
      Space.isOpenImmersion_diagonal_of_isEtale_diagonal B S hS hU hV h
        (hcritE.1 hΔrel)
    have hlfth : Space.IsLocallyOfFiniteType B S hS h :=
      hlftf U V hU hV a.hom b.hom h η hasm hbsm
        (fun Q hQ k => Stack.isRelativelySmooth_of_isRelativelyEtale B S hS _ (hcomp Q hQ k))
    refine ⟨⟨hΔ, fun U₀ y hy F hF he =>
      Space.isUnramified_of_isEtale B S hS (hΔrel U₀ y hy F hF he)⟩, ?_⟩
    exact Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram
      B S hS _ (Space.isUnramified_isEtaleSmoothLocalOnSourceAndTarget B S hS) f
      ⟨U, V, hU, hV, a, b, h, η, hasurj, hbsm, hcomp,
        Space.isUnramified_of_isOpenImmersion_diagonal B S hS h hlfth hoi⟩

end AlgebraicStacks

end Stack

end AlgebraicGeometry

end
