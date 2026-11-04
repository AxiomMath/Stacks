module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.AlgebraizationLocalCohomologyIIIBootstrapCriterion
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences

/-!
# Higher formal sections on a punctured spectrum: the adic limit in degrees at most `s`

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `F` be a coherent module on
`U = Spec(A) ∖ V(𝔞)`, and let `s ≥ 0`. Stacks 0EG4 asserts, under its three numbered
hypotheses, that `H^i(U, F) ⟶ lim H^i(U, F/IⁿF)` is an isomorphism for `i < s`, and that
`colim_V H^s(V, F) ⟶ lim H^s(U, F/IⁿF)` is an isomorphism, the colimit being over the opens
`V ⊆ U` containing `U ∩ V(I)`.

Pick a finite `A`-module `M` restricting to `F` on `U`. The source's proof produces the
conclusion in degrees `0 < i < s` from the single clause

`H^i_{V(𝔞)}(M) = lim_n H^i_{V(𝔞)}(M/IⁿM)` for `i ≤ s`,

read through the identification `H^i(U, F) = H^{i+1}_{V(𝔞)}(M)` of Stacks 0BK0; the degree shift
is what makes `i > 0` easier than `i = 0` there. That clause is what this file proves. In the
source it is Theorem 0EIE applied to the bootstrap Situation 0EFU for the data
`A, I, V(𝔞), M, s, cd(A, I)`, the situation being verified by Lemma 0EFW; here the verification
is `Stacks.Algebraization.exists_bootstrapSituation_of_depth_gt_or_depth_add_dim_gt` and the
three consequences of Theorem 0EIE are
`Stacks.LocalCohomology.Bootstrap.isLimit` and its companions. The theorem of this file is the
composite: hypotheses (1) and (2) of Stacks 0EG4, in the shape the source states them, give the
clause.

## What is covered and what is not

The clause above is the proposition's conclusion in degrees `0 < i < s` *after* the
identification `H^i(U, F) = H^{i+1}_{V(𝔞)}(M)` of Stacks 0BK0, which is not performed here: no
statement below mentions a scheme, a sheaf or a cohomology group of `U`. Neither the degree-zero
isomorphism (which the source takes from Proposition 0EG2) nor the final `colim`/`lim`
isomorphism in degree `s` (which the source takes from Lemma 0EG0) is established.

Of the source's numbered hypotheses the clause proved here uses (1) only through its
dualizing-complex half and uses (2) in full. The `I`-adic completeness half of (1) is *not*
used: the route to the clause is Lemma 0EFW followed by Theorem 0EIE, and neither mentions
completeness. Hypothesis (3) is *not* used either: in the source it enters only through Lemma
0EFL, which the source invokes for the ideal `J₀` and for degree `s + 1`, both of which belong
to the parts of the proposition not established here. Both omissions strengthen the statement
rather than weaken it, so neither hypothesis appears as a binder below.

## Carried hypothesis

One input is a hypothesis rather than a library result, quantified over arbitrary data so that it
does not mention `A`, `I`, `𝔞`, `M` or `s`: `h0EIE` is the essential-constancy assertion of
Theorem 0EIE itself, for an arbitrary bootstrap situation. The library proves the three
*consequences* of that assertion from it but not the assertion, so it is carried here.

It is satisfiable, being Tag 0EIE of the Stacks project, and it is not the conclusion below: it
is the essential-constancy datum for an arbitrary situation, from which the limit statement for
the situation attached to `A, I, V(𝔞), M, s` still has to be extracted.

## Implementation notes

The cohomological-dimension bound `d` of Lemma 0EFW is taken to be `cd(A, I)` itself, so that
bound is `le_rfl` and no `d` appears in the statement; hypothesis (2) of the source is stated
against `cd(A, I) + s + 1`, which is one more than the `d + s` that Lemma 0EFW asks for.

Hypothesis (2) of the source quantifies over `z ∈ V(𝔞) ∩ closure {x}` *inside* its disjunction,
whereas Lemma 0EFW quantifies over the specialization outside it. The shape here is the source's,
which is the stronger of the two, and the weaker shape is derived from it.

Lemma 0EFW returns the situation as an existential pinned to the given data by equalities and
`HEq`s between its fields and that data; the situation is destructured and those equalities are
substituted, which turns the field carrying assumption (6) into a statement about `A`, `I`, `M`
and `s`, and the situation is then rebuilt syntactically from the given data so that its
`Stacks.LocalCohomology.Bootstrap.cone` is the cone of the conclusion.

The module universe is the ring universe, which is what the `Bootstrap` section of Theorem 0EIE
asks for; the dualizing complex keeps its own universe.

## References

* [Stacks Project, Tag 0EG4](https://stacks.math.columbia.edu/tag/0EG4)
* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EFW](https://stacks.math.columbia.edu/tag/0EFW)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)

## Tags

local cohomology, algebraization, formal sections, adic completion, depth
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite
open Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Algebraization

/-- Hypothesis (2) of Stacks 0EG4, in the shape the source states it: for a prime `𝔭` outside
`V(I)`, either the depth of `M_𝔭` exceeds `s`, or `depth(M_𝔭) + dim((A/𝔭)_𝔮) > cd(A, I) + s + 1`
for every `𝔮 ∈ V(𝔭) ∩ V(𝔞)`.

The quantifier over `𝔮` sits inside the disjunction, as in the source. -/
public def SourceDepthHypothesis {A : Type u} [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] (s : ℤ) : Prop :=
  ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
    (enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) > (s : EInt)) ∨
    (∀ q : PrimeSpectrum A, p.asIdeal ≤ q.asIdeal →
      q ∈ PrimeSpectrum.zeroLocus (a : Set A) →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
        ((Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing + s + 1 :
          ℤ) : EInt))

end Stacks.Algebraization

end
