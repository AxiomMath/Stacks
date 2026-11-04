module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotientTorsor
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCharacterTwistTorsor
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistLocalFreeness

/-!
# Stacks 0727 for the quotient of an object of a big fppf site by a free action

Let a group `G` act freely on an object `V` of a big fppf site over a scheme `S`, let
`U = V/G` be the quotient algebraic space and let `χ : G → {±1}` be a character.  The chart
`h_V ⟶ U` is a `G`-torsor over the final object of the spaces-étale site of `U`
(`AlgebraicGeometry.Space.isTorsorObject_freeActionChartAut`), and [Stacks, Tag 0727] holds for
any such torsor: the twist `ℤ(χ)` is locally free of rank one, and its tensor product with an
abelian sheaf `ℱ` on `U_étale` has global sections the `χ`-semi-invariant sections of `ℱ` over
the chart.

This file reads those two statements off at the geometric situation.  Both are instances of the
site-level development — `CategoryTheory.IsTorsorObject.twistTensorSectionsEquiv` and
`CategoryTheory.characterTwistOverIso` — which had no geometric inhabitant of their torsor
hypothesis before `AlgebraicGeometry.Space.isTorsorObject_freeActionChartAut`, and so no
geometric consumer.

## Main results

* `AlgebraicGeometry.Space.freeActionChartSectionsEquiv`: **[Stacks, Tag 0727], the sections
  half**, for the quotient of an object of a big fppf site by a free action —
  `H⁰(V, ℱ|_V)^χ = H⁰(U, ℱ ⊗_ℤ ℤ(χ))`.
* `AlgebraicGeometry.Space.freeActionChartTwistOverIso`: **[Stacks, Tag 0727], the local
  freeness half** — the twist restricts to the constant sheaf `ℤ` on the localized site over the
  chart.

## Implementation notes

**The group is not assumed finite.**  The source takes `G` finite, and uses finiteness to make
the quotient morphism `V ⟶ V/G` étale.  Here the hypothesis is `Small.{u} G` — what the
quotient construction itself needs — and finiteness is not used: the three conditions of
`CategoryTheory.IsTorsorObject` already carry everything the sections identification consumes.
The statement is therefore stronger than the source's on this point.

**Which `characterSections` this is.**  The subgroup is `CategoryTheory.characterSections` of
the chart as an object of the spaces-étale site of the quotient, with the action of `G` by the
automorphisms of `AlgebraicGeometry.Space.freeActionChartAut`.  This is *not*
`AlgebraicGeometry.Space.characterSections`, the subgroup indexed by an étale invariant morphism
out of a presheaf of points that the hypothesis package
`AlgebraicGeometry.Space.SignTwistSetup` uses; the two spellings of the `χ`-semi-invariant
sections are unbridged, and this file does not bridge them.  What this file settles is that the
site-level spelling of [Stacks, Tag 0727] is available for an actual quotient, which the
`SignTwistSetup` spelling is not: its only producer,
`AlgebraicGeometry.Space.signTwistSetupOfSwap`, is the split double cover with `G = ℤˣ`.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (G : Type v) [Group G] [Small.{u} G] (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (V : BigFppfOver B S hS) (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a) (χ : G →* ℤˣ)

/-- **[Stacks, Tag 0727], the sections half, for the quotient of an object of a big fppf site by
a free action.**  The `χ`-semi-invariant sections of an abelian sheaf `ℱ` on the spaces-étale
site of the quotient `U = V/G` over the chart `h_V` are the global sections over `U` of the
twist `ℱ ⊗_ℤ ℤ(χ)`.

The chart is a `G`-torsor over the final object of that site, which is what
`CategoryTheory.IsTorsorObject.twistTensorSectionsEquiv` asks for; the final object is terminal
by `AlgebraicGeometry.Space.SpacesEtale.final_isTerminal`. -/
@[stacks 0727 "the identification of the chi-semi-invariant sections over the chart with the \
global sections of the twist, for the quotient of an object of a big fppf site by a free action \
of a u-small group. The source's group is finite; finiteness is not used here. The locally free \
rank one half is freeActionChartTwistOverIso"]
def freeActionChartSectionsEquiv
    (F : Sheaf (SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha))
      AddCommGrpCat.{u + 1}) :
    characterSections (freeActionQuotientChart G B S hS V a ha)
        (freeActionChartAut G B S hS V a ha) χ F.obj ≃+
      (characterTwistTensor F.obj (freeActionChartAut G B S hS V a ha) χ
        (SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha))).obj.obj
        (op (SpacesEtale.final B S hS (actionQuotientSpace G B S hS V a ha))) :=
  (isTorsorObject_freeActionChartAut G B S hS V a ha).twistTensorSectionsEquiv χ
    (SpacesEtale.final_isTerminal B S hS (actionQuotientSpace G B S hS V a ha)) F

/-- **[Stacks, Tag 0727], the local freeness half, for the quotient of an object of a big fppf
site by a free action.**  The twist `ℤ(χ)` on the spaces-étale site of the quotient `U = V/G`
restricts to the constant sheaf `ℤ` on the site localized at the chart `h_V`, which is the
sheaf-theoretic form of being locally free of rank one. -/
@[stacks 0727 "the twist is locally free of rank one, for the quotient of an object of a big \
fppf site by a free action of a u-small group: it restricts to the constant sheaf Z on the site \
localized at the chart. The sections half is freeActionChartSectionsEquiv"]
def freeActionChartTwistOverIso :
    (constantSheaf ((SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha)).over
        (freeActionQuotientChart G B S hS V a ha)) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅
      ((SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha)).overPullback
          AddCommGrpCat.{u + 1} (freeActionQuotientChart G B S hS V a ha)).obj
        (characterTwist (freeActionQuotientChart G B S hS V a ha)
          (freeActionChartAut G B S hS V a ha) χ
          (SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha))) :=
  characterTwistOverIso (isTorsorObject_freeActionChartAut G B S hS V a ha) χ

end AlgebraicGeometry.Space

end
