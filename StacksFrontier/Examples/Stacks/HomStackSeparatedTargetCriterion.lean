module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack

/-!
# The separated-target criterion for algebraicity of a Hom-stack is false

The example of Stacks 0AF8 refutes more than the assertion it was aimed at. Stacks 0AFC says
that the Hom-stack `𝒳 = Mor_S(X, [S/A])` over `S = Spec k⟦t⟧` is not algebraic, the obstruction
being the non-effectivity of its formal objects. The target `[S/A]` of that Hom-stack is the
quotient of `S` by the trivial action of the abelian scheme `A`, and such a quotient is
*separated*: by Stacks 0DTY part (6) the separation properties of a quotient stack are read off
the source and target of a presenting groupoid, and for the trivial action both are the
structural morphism `A ⟶ S`, which is proper because `A` is an abelian scheme.

So the example also refutes the criterion that a Hom-stack is algebraic as soon as its *target*
is separated: `[S/A]` is a separated target whose Hom-stack out of `X` is not algebraic. That
refutation is what this file proves.

## Main results

* `Stacks.Examples.NonAlgebraicHomStack.not_forall_isAlgebraicStack_of_isAbsolutelySeparated_target`
  is **Stacks 0AFD**: for no assignment `Mor` of a Hom-stack to a pair of algebraic stacks over
  `S = Spec k⟦t⟧` is it the case that `Mor 𝒴 𝒵` is an algebraic stack for every `𝒴` and every
  separated `𝒵`.

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
* **The Hom-stack of the example is not algebraic.** This is
  `Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_powerSeriesBase`, the
  Stacks 0AFC of the neighbouring module, applied to `Mor 𝒴 𝒵`. Its inputs are Stacks 07X8 as
  the named hypothesis `h07X8` and a formal object of `Mor 𝒴 𝒵` that is not effective as the
  named hypothesis `h0AFB`.

Neither hypothesis is the conclusion in disguise: `h0AFB` asserts non-effectivity of a formal
object, which becomes non-algebraicity only through `h07X8`, and nothing among the hypotheses
asserts that the criterion fails, that `𝒵` is separated, or that any Hom-stack is non-algebraic.

The subject of the criterion cannot be named, exactly as for Stacks 0AFC: this library defines
no Hom-stack `Mor_S(𝒴, 𝒵)` of two algebraic stacks. The criterion is therefore stated for an
arbitrary assignment `Mor` of a based category over the site to a pair of algebraic stacks, and
the hypothesis `h0AFB` is what pins that assignment to the source's example — it is the source's
unformalized identification of the Hom-stack's fibre categories with groupoids of fppf
`A₀`-torsors, by which the failure of surjectivity of `H¹(X, A) ⟶ lim H¹(Xₙ, A)` proved in the
neighbouring module becomes a non-effective formal object. See the module documentation of
`StacksFrontier.Examples.Stacks.NonAlgebraicHomStack`.

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
which is the hypothesis `hBase`, exactly as in the absolute clauses of Stacks 0DTY.

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

universe u w v t

namespace Stacks.Examples.NonAlgebraicHomStack

/-- **Stacks 0AFD**, the mathematical assertion the remark makes: the criterion that a Hom-stack
is algebraic whenever its target is separated is false.

Let `S = Spec k⟦t⟧`, let `A` be a group algebraic space over the terminal algebraic space over
`S` which is proper, flat and locally of finite presentation — the source's abelian scheme — and
let `𝒵` be an algebraic stack equivalent over the site to the quotient stack of the trivial
action of `A`, that is to `[S/A]`. Let `Mor` be any assignment of a based category over the site
to a pair of algebraic stacks over `S`, let `𝒴` be an algebraic stack and suppose, as the source
computes, that `Mor 𝒴 𝒵` has a formal object which is not effective. Then, assuming Stacks 07X8,
it is *not* the case that `Mor 𝒴' 𝒵'` is an algebraic stack for every `𝒴'` and every separated
`𝒵'`.

The two legs are derived: `[S/A]` is separated by Stacks 0DTY part (6) at the trivial-action
groupoid, and `Mor 𝒴 𝒵` is not algebraic by Stacks 0AFC of the neighbouring module.
See the module documentation. -/
@[stacks 0AFD "the mathematical assertion of the remark and not its bibliography: the criterion \
the Erratum asserts -- that a Hom-stack is algebraic as soon as its target is separated -- is \
false, because the target [S/A] of the non-algebraic Hom-stack of Stacks 0AFC is separated. \
Both legs are derived, not hypothesised: separatedness of [S/A] from Stacks 0DTY part (6) read \
at the groupoid of the trivial action, and non-algebraicity from Stacks 0AFC of \
StacksFrontier.Examples.Stacks.NonAlgebraicHomStack. NOT carried: the bibliographic claims (that \
Stacks 0AFC contradicts Theorem 1.1 of AokiHomStacks, and that the criterion is the Erratum's), \
which are cited in the docstring only. The tag's subject, the Hom-stack Mor_S(Y, Z), cannot be \
named -- this library defines no Hom-stack of two algebraic stacks -- so the criterion is \
stated for an arbitrary assignment Mor of a based category to a pair of algebraic stacks, and \
the source's unformalized identification of the Hom-stack's fibre categories with groupoids of \
torsors is the hypothesis h0AFB, a non-effective formal object of Mor Y Z. Stacks 07X8 is the \
hypothesis h07X8 and is not a result of this library; separatedness inherits from Stacks 0DTY, \
for the source's unqualified (absolute) separatedness, the hypothesis hBase on the algebraic \
stack of the base scheme"]
public theorem not_forall_isAlgebraicStack_of_isAbsolutelySeparated_target
    {k : Type u} [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hBase : Stack.AlgebraicStacks.IsAbsolutelySeparated.{u, w} B (base k) hS hZ
      (Stack.schemeStack.{u, w} B (base k) hS (Over.mk (𝟙 (B.obj hS)))))
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
      BasedCategory.{v, t} (BigFppfOver B (base k) hS))
    (𝒴 : Stack.AlgebraicStacks.{u, w} B (base k) hS)
    (hp : (Mor 𝒴 𝒵).p.IsFiberedInGroupoids)
    (h07X8 : ∀ 𝒲 : BasedCategory.{v, t} (BigFppfOver B (base k) hS),
        Stack.IsAlgebraicStack.{u, w} B (base k) hS 𝒲 →
          ∀ hq : 𝒲.p.IsFiberedInGroupoids,
            (Deformation.Artin.approximationFunctor B (base k) hS 𝒲.p hq).IsEquivalence)
    (h0AFB : ∃ ξ : Deformation.Artin.FormalObject B (base k) hS (Mor 𝒴 𝒵).p,
      ¬ Deformation.Artin.FormalObject.IsEffective B (base k) hS (Mor 𝒴 𝒵).p hp ξ) :
    ¬ ∀ 𝒴' 𝒵' : Stack.AlgebraicStacks.{u, w} B (base k) hS,
        Stack.AlgebraicStacks.IsAbsolutelySeparated.{u, w} B (base k) hS hZ 𝒵' →
          Stack.IsAlgebraicStack.{u, w} B (base k) hS (Mor 𝒴' 𝒵') := by
  intro hcriterion
  exact not_isAlgebraicStack_powerSeriesBase.{u, w} B hS (Mor 𝒴 𝒵) hp h07X8 h0AFB
    (hcriterion 𝒴 𝒵
      (Stack.isAbsolutelySeparated_quotientStack_trivialAction.{u, w}
        A hA Agpd hZ hBase 𝒵 hequiv hproper hflat hlfp))

end Stacks.Examples.NonAlgebraicHomStack

end
