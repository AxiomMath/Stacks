module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.RingTheory.LocalCohomology.UniformCohomologyBound

/-!
# Algebraization over a complete Noetherian local base, globally

Let `(R, 𝔪)` be a complete Noetherian local ring, let `X → Spec(R)` be proper, let `Z` be a
closed subset of the special fibre `X_1`, let `U = X ∖ Z` and let `j : U → X` be the inclusion.
Stacks 0EJV sketches the global counterpart of Stacks 0EJU: given an object `(F_n)` of
`Coh(U, 𝔪𝒪_U)` which is flat over `R` and for which `j_*F_1` and `R¹j_*F_1` are coherent, the
system `(F_n)` is *algebraizable* — it is the completion of a coherent `𝒪_U`-module.

The sketch has four steps:

1. affine locally on `X` the system extends canonically, by Stacks 0EJU;
2. the extension commutes with localization (Stacks 0DXW), so the local extensions glue to a
   global object `(G_n)` of `Coh(X, 𝔪𝒪_X)` whose restriction to `U` is `(F_n)`;
3. Grothendieck's existence theorem (Stacks 088C) produces a coherent `𝒪_X`-module `G` whose
   completion is `(G_n)`;
4. hence `(F_n)` is the completion of the coherent `𝒪_U`-module `G|_U`.

Steps 3 and 4 are what this file carries out. Step 4 is the one piece of mathematics the sketch
leaves to the reader: it is the identification of the restriction of the completion of `G` with
the completion of `G|_U`, which is `Stacks.Algebraization.completionRestrictOpenIso`. Step 3 is a
citation and is the hypothesis `h088C` below, stated for every complete Noetherian ring, every
ideal of it and every proper scheme over it. Steps 1 and 2 are the hypothesis `hextend`, that
`(F_n)` is the restriction of a coherent `𝔪𝒪_X`-adic system on `X` — which is the shape of Tag
0EIM, `Stacks.Algebraization.ExtendsToX`, read on a general `X` instead of on an affine
algebraization situation.

## Main definitions

* `Stacks.Algebraization.IsCompletionOfCoherent` — a coherent adic system is the completion of a
  coherent module, i.e. it is algebraizable.

## What is commentary and what is mathematics

The remark opens by recording that Proposition 0EJU is a local version of [Baranovsky, Theorem
2.10 (i)] and that the global results follow from it without difficulty. That is a bibliographic
comparison with the literature and an appraisal of the argument's difficulty: there is no
mathematical assertion in it for a Lean declaration to carry, and none is formalized here. What
the remark then goes on to state — the global algebraization statement above, with its explicit
hypotheses — is mathematics, and is what `@[stacks 0EJV]` is attached to.

## The hypotheses of the remark

`R` is complete Noetherian local, `X → Spec(R)` is proper, `Z` is closed in `X_1`, `U = X ∖ Z`,
and `(F_n)` is an object of `Coh(U, 𝔪𝒪_U)`; all of that is in the statement below.

The thickening `X_n = X ×_{Spec R} Spec(R/𝔪ⁿ)` is the closed subscheme of `X` cut out by
`𝔪ⁿ𝒪_X`, which is `(Stacks.Cohomology.FormalFunctions.baseIdealSheaf R (𝔪 ^ n) p).subscheme` by
`Stacks.Cohomology.FormalFunctions.baseIdealSheaf_pow`. Only `X_1` enters the statement, through
its underlying closed subset `(baseIdealSheaf R 𝔪 p).support`; by
`AlgebraicGeometry.Scheme.IdealSheafData.support_pow` the thickenings all have that same
underlying set, so "closed subset of the special fibre" does not depend on which of them is
meant. The ideal sheaf `𝔪𝒪_U` is the restriction `(𝔪𝒪_X)|_U`, written `.comap j` — the spelling
of `Stacks.Algebraization.idealOnOpen`, which `idealOnOpen_eq_comap_idealOnX` identifies with the
comap of `I𝒪_X` on the nose.

Two of the remark's hypotheses are *absent* from the statement, which is therefore more general
than the remark: flatness of `(F_n)` over `R`, and coherence of `j_*F_1` and `R¹j_*F_1`. Both are
consumed by the remark only inside steps 1 and 2, to invoke Stacks 0EJU affine locally; here
those steps are the hypothesis `hextend`, and once a global formal object exists the conclusion
follows from steps 3 and 4 with no flatness and no coherence of direct images anywhere. Dropping
them strengthens the statement rather than weakening it. This library has no spelling for either
condition on a general `X` in any case: flatness appears only as
`Stacks.Algebraization.FlatCompletedStalks`, which is stalkwise over `R` in an affine
algebraization situation, and coherence of `R¹j_*` is not available at all (Tag 02O5 is unproved
in this library), the nearest statement being `Module.Finite` of
`Stacks.LocalCohomology.cohomologyOverBase`.

`hZ` and `hU` are carried but not consumed, as `hf : f ∈ a` is in
`Stacks.Algebraization.completionFullyFaithful_of_isAdicComplete_of_annihilated`: they are what
makes the statement recognizably the remark's, and the conclusion holds for any open `U`.

## On the two carried inputs

`h088C` is stated about *every* ring `A`, every ideal `J ⊆ A` with `A` `J`-adically complete and
every proper `q : Y ⟶ Spec(A)` — none of them `R`, `𝔪`, `p` — so it is a general cited result and
not this theorem's conclusion in disguise; compare `hEKP` of
`Stacks.Algebraization.completionFullyFaithful_of_isAdicComplete_of_annihilated` and `hscheme` of
`AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections`. It is also the
*weakest* half of Tag 088C: only essential surjectivity of the completion functor is asked for,
which is exactly the form the remark quotes ("there exists a coherent `𝒪_X`-module `𝒢` whose
completion is `(𝒢_n)`"), rather than the equivalence Tag 088C asserts. Tag 088C is not proved in
this library.

`hextend` is a hypothesis on this theorem's own data, in the manner of `hdec` of
`Stacks.Algebraization.canonicallyExtends_of_isoDirectSum`: it stands in for the two steps of the
sketch that this library cannot carry out, and the tag clause says so. It is not the conclusion
pre-instantiated — a formal object on `X` restricting to `(F_n)` is not an algebraization of
`(F_n)`, and the chapter's own counterexample
`Stacks.Algebraization.NonAlgebraizableExample` shows the conclusion is not automatic.

Neither carry is vacuous. `hextend` holds, with `Iso.refl`, for every `X`, every `U` and every
system restricted from `X`, so it is satisfiable for arbitrary geometric data; `h088C` has an
existential conclusion, so it imposes no bound that could fail to be met, and it is Tag 088C,
a theorem. The rest of the hypothesis bundle is satisfiable concretely: for a field `k`, with
`X = Spec(k)`, `p = 𝟙`, `Z = ⊥` and `U = ⊤`, every instance and both of `hZ`, `hU` hold
(`IsAdicComplete (𝔪) k` because `𝔪 = ⊥`).

## What is not covered

The remark's closing paragraph asserts two further things, neither of which is delivered here:
that `j_*F_1 = j_{1,*}F_1` and `R¹j_*F_1 = R¹j_{1,*}F_1` for the special fibre `j_1 : U_1 → X_1`
of `j`, so that the coherence hypothesis is a condition on the special fibre; and that it holds
when `X_1` is `(S_2)` and irreducible, `dim(X_1) - dim(Z) ≥ 3` and `F_1` is locally free. Both
are statements about higher direct images along `j_1`, of which this library has none: Tag 02O5
is unproved here, and there is no `(S_2)` hypothesis available for a scheme either.

## References

* [Stacks Project, Tag 0EJV](https://stacks.math.columbia.edu/tag/0EJV)
* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
* [Stacks Project, Tag 0EIM](https://stacks.math.columbia.edu/tag/0EIM)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.FormalFunctions
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- A coherent `J`-adic system on a locally Noetherian scheme `W` is **algebraizable** when it is
isomorphic, as an inverse system, to the completion along `J` of a coherent `𝒪_W`-module.

This is the conclusion of Stacks 0EJV. It is the counterpart on `W` itself of
`Stacks.Algebraization.IsRestrictionOfCompletion`, which asks instead for a coherent module on an
ambient scheme whose completion restricts to the system. -/
def IsCompletionOfCoherent {W : Scheme.{u}} [IsLocallyNoetherian W] (J : W.IdealSheafData)
    (F : Stacks.Coherent.CoherentAdicSystems J) : Prop :=
  ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules W.ringCatSheaf,
    Nonempty (((completionFunctor W J).obj G).obj ≅ F.obj)

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p] [IsLocallyNoetherian X]

end Stacks.Algebraization

end
