module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackSeparated
public import StacksFrontier.Deformation.Artin.FormalObject.AlgebraicStackEffective
public import StacksFrontier.Examples.Stacks.HomStackSeparatedTargetCriterion

/-!
# The separated-target criterion for algebraicity of a Hom-stack is false, with its inputs derived

The example of Stacks 0AF8 refutes more than the assertion it was aimed at. Stacks 0AFC says
that the Hom-stack `𝒳 = Mor_S(X, [S/A])` over `S = Spec k⟦t⟧` is not algebraic, the obstruction
being the non-effectivity of its formal objects. The target `[S/A]` of that Hom-stack is the
quotient of `S` by the trivial action of the abelian scheme `A`, and such a quotient is
*separated*: by Stacks 0DTY part (6) the separation properties of a quotient stack are read off
the source and target of a presenting groupoid, and for the trivial action both are the
structural morphism `A ⟶ S`, which is proper because `A` is an abelian scheme.

So the example also refutes the criterion that a Hom-stack is algebraic as soon as its *target*
is separated: `[S/A]` is a separated target whose Hom-stack out of `X` is not algebraic. That
refutation is what this file proves. Unlike
`Stacks.Examples.NonAlgebraicHomStack.not_forall_isAlgebraicStack_of_isAbsolutelySeparated_target`
of `StacksFrontier.Examples.Stacks.HomStackSeparatedTargetCriterion`, it takes neither Stacks 07X8
nor the separatedness of the base as an input: both are derived here.

## Main results

* `not_forall_isAlgebraicStack_of_isAbsolutelySeparated_of_not_isEffective`
  is **Stacks 0AFD**: for no assignment `Mor` of a based category to a pair of algebraic stacks
  over `S = Spec k⟦t⟧` for which `Mor 𝒴 [S/A]` has a non-effective formal object is it the case
  that `Mor 𝒴' 𝒵'` is an algebraic stack for every `𝒴'` and every separated `𝒵'`.

## What is proved and what is assumed

The two legs of the remark's argument are both *derived*, not assumed.

* **The target is separated.** `𝒵` is tied to the quotient stack of the action groupoid of the
  trivial action of a group algebraic space `A` on the terminal algebraic space over `S` — that
  is, to `[S/A]` — and its separatedness is
  `AlgebraicGeometry.Stack.isAbsolutelySeparated_quotientStack_trivialAction`, which is
  Stacks 0DTY part (6) read at that groupoid. The geometric input is properness of `A ⟶ S`,
  which for the source's abelian scheme is one of the defining conditions of
  `AlgebraicGeometry.IsAbelianScheme`; it is taken here as the hypothesis `hproper`, alongside
  flatness and local finite presentation, the other two conditions 0DTY part (6) needs.
* **The Hom-stack of the example is not algebraic.** If `Mor 𝒴 𝒵` were algebraic, every
  formal object of it would be effective by Stacks 07X8 of this library,
  `Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack_of_isFiberedInGroupoids`;
  the input `hξ` is a formal object of `Mor 𝒴 𝒵` that is not effective.

Nothing among the inputs asserts that the criterion fails, that `𝒵` is separated, or that any
Hom-stack is non-algebraic.

This library defines the Hom-stack `Mor_S(X, 𝒵)` from an object `X` of the site
(`AlgebraicGeometry.Stack.homStack`, whose instance `Mor_S(X, [S/A])` is the subject of
Stacks 0AFB and Stacks 0AFC in `StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.Main`), but no
Hom-stack `Mor_S(𝒴, 𝒵)` of two algebraic stacks. The criterion is therefore stated for an
arbitrary assignment `Mor` of a based category over the site to a pair of algebraic stacks, and
the input `hξ` is what pins that assignment to the source's example; for `Mor_S(X, [S/A])` such a
non-effective formal object is produced by the proof of Stacks 0AFB,
`Stacks.Examples.NonAlgebraicHomStack.Situation.exists_not_restriction_homStackClassifyingStack`,
from the identification of the fibre categories of the Hom-stack with groupoids of fppf
`A₀`-torsors. See the module documentation of `StacksFrontier.Examples.Stacks.NonAlgebraicHomStack`.

The bibliographic content of the remark — that Stacks 0AFC contradicts [Theorem 1.1,
AokiHomStacks], that the same problem is mentioned in the Erratum, and that it is the Erratum
which goes on to assert the separated-target criterion — is not formalized. Only the
mathematical assertion the remark makes about that criterion is, and the citation is recorded
here.

## Which separatedness

The source's *separated* is unqualified, which is the absolute notion of Stacks 050D part (7),
and that is the notion used here: it makes the refuted criterion weaker and so the refutation
stronger than it would be with separatedness over the base. Reaching the absolute notion from
the one over the base needs separatedness of the algebraic stack of the base scheme of the site,
which holds because `S = Spec k⟦t⟧` is affine
(`AlgebraicGeometry.Stack.isAbsolutelySeparated_schemeStack_of_isAffine`).

## References

* [Stacks Project, Tag 0AFC](https://stacks.math.columbia.edu/tag/0AFC)
* [Stacks Project, Tag 0AFD](https://stacks.math.columbia.edu/tag/0AFD)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
* [Stacks Project, Tag 0DTY](https://stacks.math.columbia.edu/tag/0DTY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u w v

namespace Stacks.Examples.NonAlgebraicHomStack

/-- **Stacks 0AFD**, the mathematical assertion of the remark: the criterion that a Hom-stack is
algebraic whenever its target is separated is false.

Let `S = Spec k⟦t⟧`, let `A` be a group algebraic space over `S` which is proper, flat and locally
of finite presentation, and let `𝒵` be an algebraic stack equivalent over the site to the quotient
stack `[S/A]` of the trivial action of `A`. Let `Mor` assign a category over the site to a pair of
algebraic stacks, let `𝒴` be an algebraic stack and suppose `Mor 𝒴 𝒵` has a formal object that is
not effective. Then it is not the case that `Mor 𝒴' 𝒵'` is an algebraic stack for every `𝒴'` and
every separated `𝒵'`.

* `[S/A]` is separated by Stacks 0DTY part (6) at the trivial-action groupoid
  (`AlgebraicGeometry.Stack.isAbsolutelySeparated_quotientStack_trivialAction`), the algebraic
  stack of the affine scheme `S` being separated by
  `AlgebraicGeometry.Stack.isAbsolutelySeparated_schemeStack_of_isAffine`.
* An algebraic `Mor 𝒴 𝒵` would have every formal object effective by Stacks 07X8,
  `Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack_of_isFiberedInGroupoids`.

**The group `A`.** The source's `A = A₀ × S` is an abelian scheme over `S`, and properness, flatness
and local finite presentation of `A ⟶ S` are among the defining conditions of an abelian scheme
(`AlgebraicGeometry.IsAbelianScheme` extends `IsProper`, `Flat` and
`LocallyOfFinitePresentation`). They are the only part of that assumption the remark uses, so they
are stated, on the algebraic-space side, as `hproper`, `hflat` and `hlfp`; the statement therefore
covers every such group algebraic space, the source's abelian scheme among them.

**The universes of `Mor`.** The fibre of the source's Hom-stack `Mor_S(𝒴, 𝒵)` over an `S`-scheme
`T` consists of 1-morphisms `(Sch/T)_{fppf} ×_S 𝒴 ⟶ 𝒵` between categories whose objects lie in the
universe `u + 1` of the site's schemes; so its total category has objects in `u + 1`, and its
morphisms (natural transformations) in `u + 1` as well. `Mor` is accordingly a based category with
objects in `u + 1` and morphisms in an arbitrary universe `v`, which contains the source's case.

**The input `hξ`.** This library defines no Hom-stack of two algebraic stacks, so `Mor` is an
arbitrary assignment and the non-effectivity of a formal object of `Mor 𝒴 [S/A]` — the source's
Lemma 0AFB, read through its identification of the fibres of `Mor_S(X, [S/A])` with groupoids of
`A₀`-torsors — is the input `hξ`. Lemma 0AFB and Proposition 0AFC belong to item C6003 of
lane rb-201 (`StacksFrontier.Examples.Stacks.NonAlgebraicHomStack`). -/
@[stacks 0AFD "the mathematical assertion of the remark and not its bibliography: the criterion \
the Erratum asserts -- that a Hom-stack is algebraic as soon as its target is separated -- is \
false, because the target [S/A] of a Hom-stack with a non-effective formal object is separated. \
Separatedness of [S/A] is derived from Stacks 0DTY part (6) read at the groupoid of the trivial \
action and from separatedness of the stack of the affine base Spec k[[t]]; A is any group \
algebraic space over S that is proper, flat and locally of finite presentation, the clauses of \
the source's abelian scheme that the remark uses. Non-algebraicity is derived from Stacks 07X8 \
of this library. The Hom-stack Mor_S(X, [S/A]) is not defined in this library, so Mor is an \
arbitrary assignment and the source's Lemma 0AFB for it -- a formal object of Mor Y Z that is \
not effective -- is the input hξ (0AFB and 0AFC: item C6003). The bibliographic claims about \
AokiHomStacks and its Erratum are cited in the docstring only"]
public theorem not_forall_isAlgebraicStack_of_isAbsolutelySeparated_of_not_isEffective
    {k : Type u} [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (A : Over (Space.terminalSpace B (base k) hS).obj) [GrpObj A]
    (hA : IsAlgebraicSpace B (base k) hS A.left)
    (Agpd : Space.ActionGroupoidConstruction (Space.terminalSpace B (base k) hS) A
      (𝟙_ (Over (Space.terminalSpace B (base k) hS).obj)) hA
      (Space.terminalSpace B (base k) hS).property)
    (𝒵 : Stack.AlgebraicStacks.{u, w} B (base k) hS)
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (Stack.quotientStack Agpd.groupoid).p 𝒵.val.val.p))
    (hproper : Space.IsProper B (base k) hS A.hom)
    (hflat : Space.IsFlat B (base k) hS A.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation B (base k) hS A.hom)
    (Mor : Stack.AlgebraicStacks.{u, w} B (base k) hS →
      Stack.AlgebraicStacks.{u, w} B (base k) hS →
      BasedCategory.{v, u + 1} (BigFppfOver B (base k) hS))
    (𝒴 : Stack.AlgebraicStacks.{u, w} B (base k) hS)
    (hp : (Mor 𝒴 𝒵).p.IsFiberedInGroupoids)
    (hξ : ∃ ξ : Deformation.Artin.FormalObject B (base k) hS (Mor 𝒴 𝒵).p,
      ¬ Deformation.Artin.FormalObject.IsEffective B (base k) hS (Mor 𝒴 𝒵).p hp ξ) :
    ¬ ∀ 𝒴' 𝒵' : Stack.AlgebraicStacks.{u, w} B (base k) hS,
        Stack.AlgebraicStacks.IsAbsolutelySeparated.{u, w} B (base k) hS hZ 𝒵' →
          Stack.IsAlgebraicStack.{u, w} B (base k) hS (Mor 𝒴' 𝒵') := by
  intro hcriterion
  obtain ⟨ξ, hξ⟩ := hξ
  have hBase : Stack.AlgebraicStacks.IsAbsolutelySeparated.{u, w} B (base k) hS hZ
      (Stack.schemeStack.{u, w} B (base k) hS (Over.mk (𝟙 (B.obj hS)))) :=
    Stack.isAbsolutelySeparated_schemeStack_of_isAffine.{u, w} B (base k) hS hZ
      (Over.mk (𝟙 (B.obj hS))) (inferInstanceAs (IsAffine (base k)))
  exact hξ (Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack_of_isFiberedInGroupoids
    B (base k) hS (Mor 𝒴 𝒵) (hcriterion 𝒴 𝒵
      (Stack.isAbsolutelySeparated_quotientStack_trivialAction.{u, w}
        A hA Agpd hZ hBase 𝒵 hequiv hproper hflat hlfp)) hp ξ)

end Stacks.Examples.NonAlgebraicHomStack

end
