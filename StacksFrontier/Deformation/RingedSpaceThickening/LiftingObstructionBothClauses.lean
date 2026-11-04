module

public import StacksFrontier.Deformation.RingedSpaceThickening.LiftingObstructionClauseOneCanonical
public import StacksFrontier.Deformation.ToposThickening.LiftingDerivationGroup
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08U8 in one statement

Let

```
X₂ --i₂--> X'₂                   X₁ --i₁--> X'₁
|          |                     |          |
f₂         f'₂        --g-->      f₁         f'₁
v          v                     v          v
S₂ --t₂--> S'₂                   S₁ --t₁--> S'₁
```

be the commutative diagram of morphisms of ringed spaces of **Stacks 08U9** whose horizontal
maps are first order thickenings, let `𝒢_j = ker(i_j^♯)`, let `ν : 𝒢₁ ⟶ 𝒢₂` be a `g`-map of
modules, and assume the resulting diagram of exact ideal rows of **Stacks 08UA** has front and
back solutions to the extension problem of **Stacks 08U7**. **Stacks 08U8** then asserts two
things.

1. There is a canonical element of `Ext¹_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)` whose vanishing is
   necessary and sufficient for the existence of a morphism of ringed spaces `X'₂ ⟶ X'₁`
   fitting into the diagram compatibly with `ν`.
2. If such a morphism exists, then the set of them is a principal homogeneous space under

   `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂) = Hom_{𝒪_{X₂}}(g^*Ω_{X₁/S₁}, 𝒢₂)
      = Ext⁰_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)`.

Both clauses are available in this library, in the same situation — the source's diagram with
its underlying spaces identified as the source's own proof identifies them, which is
`Deformation.ToposThickening.FirstOrderLiftDiagram`. This file states the two together, as one
theorem about one diagram.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.liftDiagramObstruction_and_principalHomogeneousSpace`:
  **Stacks 08U8**, both clauses in one statement, with nothing assumed.

## Implementation notes

**Nothing is proved here.** The two clauses are
`AlgebraicGeometry.RingedSpaceThickening.liftDiagramObstructionClass_eq_zero_iff`
(`StacksFrontier/Deformation/RingedSpaceThickening/LiftingObstructionClauseOneCanonical.lean`) and
`Deformation.ToposThickening.FirstOrderLiftDiagram.translateHom_zero`,
`Deformation.ToposThickening.FirstOrderLiftDiagram.translateHom_add`,
`Deformation.ToposThickening.FirstOrderLiftDiagram.existsUnique_translateHom`
(`StacksFrontier/Deformation/ToposThickening/LiftingDerivationGroup.lean`), each of them already
unconditional. What this file adds is that one hypothesis set carries both: the diagram `D`,
and the instances making sheafification and the sheaves of modules available on the site. The
hypotheses of the clause (2) carriers are a subset of those of the clause (1) carrier, so the
joint statement needs nothing that clause (1) did not already need, and in particular no
hypothesis the source does not have.

**Why the principal homogeneous space is three conjuncts and not a torsor structure.** A
principal homogeneous space under an additive group is an action which is simply transitive.
The action is `Deformation.ToposThickening.FirstOrderLiftDiagram.translateHom` — on a morphism
`φ : 𝒪_{X'₁} ⟶ 𝒪_{X'₂}` it is `x ↦ φ(x) + δ(x)` for the derivation `δ` corresponding to the
homomorphism — and the three conjuncts below are the two action axioms and the simple
transitivity. The library states this through those laws rather than through Mathlib's
`AddTorsor` class, as
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentLiftingObstruction.lean` and
`StacksFrontier/Deformation/RingedSpaceThickening/MapLift.lean` both record, and the laws carry
more than an `AddTorsor` structure would: an `AddTorsor` could be twisted by an automorphism
of the acting group, whereas `Deformation.ToposThickening.FirstOrderLiftDiagram.translateHom` is
a named operation and `Deformation.ToposThickening.FirstOrderLiftDiagram.existsUnique_translateHom`
says that the unique homomorphism carrying one morphism to another acts by it.

**The acting group is the first of the source's three spellings.**
`Deformation.ToposThickening.FirstOrderLiftDiagram.frontDifferentials` is `Ω_{X₁/S₁}` and
`Deformation.ToposThickening.FirstOrderLiftDiagram.pushedIdeal` is `g_*𝒢₂`, so the group acting
below is literally `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`, the group the source's display names
first and the only one of the three mentioning no pullback. Its re-spellings as
`Hom_{𝒪_{X₂}}(g^*Ω_{X₁/S₁}, 𝒢₂)` and as an `Ext⁰` group — which the source calls immediate
from the definitions — are
`AlgebraicGeometry.RingedSpaceThickening.actingGroupEquivPushforward`,
`AlgebraicGeometry.RingedSpaceThickening.actingGroupEquivPullback` and
`AlgebraicGeometry.RingedSpaceThickening.extZeroPulledNaiveCotangentAddEquiv` of
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentActingGroup.lean`, together with
`Stacks.SheafOfModules.presentationNaiveCotangentExtZeroAddEquiv` of
`StacksFrontier/CategoryTheory/Sites/Modules/InternalHomAndFlatness/NaiveCotangentExtZero.lean`.

**The set of morphisms, and the canonical element.**
`Deformation.ToposThickening.FirstOrderLiftDiagram.Lift` is a homomorphism `𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of
sheaves of commutative rings together with the three compatibilities the source displays — over
the two reductions, under the two structure maps from the thickened bases, and inducing `ν` on
the two ideals — so the set acted on is the source's own.
`AlgebraicGeometry.RingedSpaceThickening.liftDiagramObstructionClass` is the class in
`Ext¹(𝖭𝖫(α), g_*𝒢₂)` of the difference homomorphism `ξ` of Step 1 of the source's proof, taken
at the canonical two-term structure of `𝖭𝖫(α)`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08U9](https://stacks.math.columbia.edu/tag/08U9), the diagram
* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA), the ideal rows
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7), the extension problem
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG), the ringed-topos twin
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening

universe v u w

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (D : FirstOrderLiftDiagram.{v, u, max u v w} J)

/-- **Stacks 08U8 on one site** (the ringed-space statement, with the underlying spaces not
identified, is `DeformationIdealDiagram.lifting_obstruction_and_torsor`). In the situation of the
source's diagram — the two layers of
**Stacks 08U9** with first order thickenings for horizontal maps, the ideal modules
`𝒢_j = ker(i_j^♯)`, a `g`-map `ν : 𝒢₁ ⟶ 𝒢₂`, and front and back solutions to the extension
problem of **Stacks 08U7** — with the underlying spaces identified as the source's own proof
identifies them:

1. the canonical element
   `AlgebraicGeometry.RingedSpaceThickening.liftDiagramObstructionClass` of
   `Ext¹(𝖭𝖫_{X₁/S₁}, g_*𝒢₂)` vanishes if and only if there is a morphism `X'₂ ⟶ X'₁` fitting
   into the diagram compatibly with `ν`; and

2. those morphisms are a principal homogeneous space under
   `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`: the zero homomorphism fixes each of them, translation is
   additive in the translating homomorphism, and any one of them is carried to any other by
   exactly one homomorphism.

The first conjunct is
`AlgebraicGeometry.RingedSpaceThickening.liftDiagramObstructionClass_eq_zero_iff`; the last
three are `Deformation.ToposThickening.FirstOrderLiftDiagram.translateHom_zero`,
`Deformation.ToposThickening.FirstOrderLiftDiagram.translateHom_add` and
`Deformation.ToposThickening.FirstOrderLiftDiagram.existsUnique_translateHom`. The action is
pinned to `Deformation.ToposThickening.FirstOrderLiftDiagram.translateHom`, translation of a
morphism by the derivation the homomorphism corresponds to; pinning it is part of the statement,
since a principal homogeneous structure left abstract could be twisted by an automorphism of the
acting group.

Clause (2) of the source is prefaced by "suppose given a morphism"; the statement here drops
that supposition, which is a strengthening and not a weakening — with no such morphism the
three conjuncts hold vacuously. -/
@[ega "0 20.1.3" "Clause (2), special case"]
theorem liftDiagramObstruction_and_principalHomogeneousSpace :
    (liftDiagramObstructionClass D = 0 ↔ Nonempty (FirstOrderLiftDiagram.Lift D)) ∧
      (∀ p : FirstOrderLiftDiagram.Lift D, FirstOrderLiftDiagram.translateHom D p 0 = p) ∧
      (∀ (p : FirstOrderLiftDiagram.Lift D)
          (a b : FirstOrderLiftDiagram.frontDifferentials D ⟶ FirstOrderLiftDiagram.pushedIdeal D),
        FirstOrderLiftDiagram.translateHom D (FirstOrderLiftDiagram.translateHom D p a) b =
          FirstOrderLiftDiagram.translateHom D p (a + b)) ∧
      ∀ p q : FirstOrderLiftDiagram.Lift D,
        ∃! a : FirstOrderLiftDiagram.frontDifferentials D ⟶ FirstOrderLiftDiagram.pushedIdeal D,
          FirstOrderLiftDiagram.translateHom D p a = q :=
  ⟨liftDiagramObstructionClass_eq_zero_iff D, FirstOrderLiftDiagram.translateHom_zero D,
    FirstOrderLiftDiagram.translateHom_add D, FirstOrderLiftDiagram.existsUnique_translateHom D⟩

end AlgebraicGeometry.RingedSpaceThickening

end
