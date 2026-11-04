module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Trace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleCanonicalWeighting
public import StacksCore.Tactic.StacksAttribute

/-!
# The trace map of an étale morphism with its canonical weighting

Let `j : U ⟶ X` be an étale morphism of schemes, presented as an object of the small étale site
of `X` inside a big étale site. By
`AlgebraicGeometry.flatQuasiFiniteWeight_eq_one_of_etale` the canonical weighting of `j` — the
weighting of Stacks 0F3D with which Example 0GKI builds its trace — is the constant function
`1`. The trace map `Tr_{j, w} : j_! j^{-1}ℱ ⟶ ℱ` of Stacks 0GKG acts on the stalk at a
geometric point `x̄` of `X` by

`(j_! j^{-1}ℱ)_x̄ = ⨁_{j(ū) = x̄} ℱ_x̄ ⟶ ℱ_x̄`, multiplication by `w(ū)` on the `ū` summand,

so for `w = 1` it is the sum map. That is the counit of the adjunction `j_! ⊣ j^{-1}` — the
content of Remark 0GL4, proved as
`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounit`. This file
takes the counit as the trace map of an étale morphism with its canonical weighting, proves
the functoriality in the sheaf that Stacks 0GKH part (1) asserts for it, and identifies it with
the trace map for which the terminology "trace" was already used in Étale Cohomology, Section
03SH — the second half of Remark 0GL4.

## Main definitions

* `AlgebraicGeometry.etaleCanonicalTrace` — the trace `j_! j^{-1} ⟶ 𝟭` on abelian étale
  sheaves: the counit of `AlgebraicGeometry.abelianExtensionByZeroAdjunction`.
* `AlgebraicGeometry.moduleEtaleCanonicalTrace` — the same for étale sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.etaleCanonicalTrace_naturality` and
  `AlgebraicGeometry.moduleEtaleCanonicalTrace_naturality` — the trace is functorial in the
  sheaf, which is part (1) of Stacks 0GKH.
* `AlgebraicGeometry.etaleCanonicalTrace_eq_comparison_comp_abelianTrace` and
  `AlgebraicGeometry.moduleEtaleCanonicalTrace_eq_comparison_comp_moduleTrace` — for a finite
  étale `j` the trace is the trace map of Stacks 03SE read through the comparison `j_! ⟶ j_*`.
  This is the Étale Cohomology, Section 03SH half of Remark 0GL4: the counit is exactly the
  morphism already called the trace there.

## Implementation notes

The trace is taken as the counit rather than being constructed from the weighting, which is
exactly the identification Remark 0GL4 asserts and which
`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit` establishes. The finite étale
comparison statements are equalities between two separately defined morphisms:
`AlgebraicGeometry.abelianTrace` of Stacks 03SE is built from the comparison isomorphism
`j_! ≅ j_*` of Stacks 03S7 and the counit, and the equality holds because the comparison cancels
against its inverse.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0GL4](https://stacks.math.columbia.edu/tag/0GL4)
* [Stacks Project, Tag 03SE](https://stacks.math.columbia.edu/tag/03SE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- **The trace map of Stacks 0GKG for an étale morphism with its canonical weighting.** The
canonical weighting of an étale `j : U ⟶ X` is the constant function `1`
(`AlgebraicGeometry.flatQuasiFiniteWeight_eq_one_of_etale`), for which the prescribed stalk
behaviour of the trace is the sum map `⨁_{j(ū) = x̄} ℱ_x̄ ⟶ ℱ_x̄`; that map is the counit of
`j_! ⊣ j^{-1}`, and the counit is what is taken here. -/
@[stacks 0GKG "The trace map `Tr_{f, w} : f_! f^{-1}ℱ ⟶ ℱ` in the single case of an étale
morphism carrying its canonical weighting, where by Remark 0GL4 it is the counit of
`j_! ⊣ j^{-1}`; it is defined here to be that counit. The general construction, for a locally
quasi-finite morphism and an arbitrary weighting, is a separate matter. That the counit does
satisfy the stalk characterisation `AlgebraicGeometry.SmallEtale.HasWeightedTraceStalks` of
Lemma 0GKG for the canonical weighting, so that by
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_unique` it is the trace map of Lemma 0GKG
in the étale case, is `AlgebraicGeometry.hasWeightedTraceStalks_counit` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounit`. The
substantive fact licensing this case is the companion
`AlgebraicGeometry.flatQuasiFiniteWeight_eq_one_of_etale`."]
def etaleCanonicalTrace :
    abelianRestriction B X hX U ⋙ abelianExtensionByZero B X hX U ⟶
      𝟭 (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :=
  (abelianExtensionByZeroAdjunction B X hX U).counit

/-- The trace is the counit of the extension-by-zero adjunction, by construction. -/
theorem etaleCanonicalTrace_eq_counit :
    etaleCanonicalTrace B X hX U = (abelianExtensionByZeroAdjunction B X hX U).counit :=
  rfl

/-- The trace map is functorial in the abelian sheaf: for `φ : ℱ ⟶ 𝒢` the square formed by
`Tr_ℱ`, `Tr_𝒢` and `j_! j^{-1}φ` commutes. -/
@[stacks 0GKH "Part (1) only — functoriality of the trace map in the sheaf — for an étale
morphism with its canonical weighting, the case of Remark 0GL4, where the trace is the counit of
`j_! ⊣ j^{-1}`. Part (1) for an ARBITRARY locally quasi-finite morphism and an arbitrary weight
is `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_naturality`, stated for the morphisms
with the characterising stalk behaviour of Lemma 0GKG. Part (2), compatibility with arbitrary
base change, and part (3), the version for `K` in the unbounded derived category
`D(Y_étale, Λ)`, are NOT carried by this declaration. The general weighted trace of Lemma 0GKG
that parts (1)-(3) are about is
`AlgebraicGeometry.SmallEtale.weightedTrace` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceExistence`; see the
clause on `AlgebraicGeometry.etaleCanonicalTrace`."]
theorem etaleCanonicalTrace_naturality
    {F G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (abelianRestriction B X hX U ⋙ abelianExtensionByZero B X hX U).map φ ≫
        (etaleCanonicalTrace B X hX U).app G =
      (etaleCanonicalTrace B X hX U).app F ≫ φ :=
  (etaleCanonicalTrace B X hX U).naturality φ

section Finite

variable [IsFinite (B.inclusion.map U.obj.hom)]

/-- For a finite étale `j` the trace map of Stacks 03SE is defined on `j_* j^{-1}` rather than on
`j_! j^{-1}`, through the comparison isomorphism `j_! ≅ j_*`. Composing the comparison with it
returns the counit: the morphism for which the terminology "trace" was already used in Étale
Cohomology, Section 03SH is the counit of `j_! ⊣ j^{-1}`. -/
@[stacks 0GL4 "The Étale Cohomology, Section 03SH half of the remark: the counit of
`j_! ⊣ j^{-1}` is the morphism already called the trace there, namely the trace map of Stacks
03SE read through the comparison `j_! ⟶ j_*`. Stated for a FINITE étale `j`, because that is
where the 03SE trace is defined in this library. The remark's own equality — counit versus the
trace map of Example 0GKI — is
`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounit`."]
theorem etaleCanonicalTrace_eq_comparison_comp_abelianTrace :
    etaleCanonicalTrace B X hX U =
      Functor.whiskerLeft (abelianRestriction B X hX U)
        (abelianExtensionByZeroToPushforward B X hX U) ≫ abelianTrace B X hX U :=
  (abelianExtensionByZeroToPushforward_comp_abelianTrace B X hX U).symm

end Finite

section Modules

variable (Λ : Type v) [Ring Λ]

/-- **The trace map of Stacks 0GKG for an étale morphism with its canonical weighting, on
sheaves of `Λ`-modules.** As in the abelian case, this is the counit of `j_! ⊣ j^{-1}`. -/
@[stacks 0GKG "The trace map on étale sheaves of `Λ`-modules, in the single case of an étale
morphism carrying its canonical weighting, where by Remark 0GL4 it is the counit of
`j_! ⊣ j^{-1}`; it is defined here to be that counit. Same scope as
`AlgebraicGeometry.etaleCanonicalTrace`: the general weighted construction of Lemma 0GKG, for a
locally quasi-finite morphism and an arbitrary weighting, is a separate matter, and the stalk
characterisation `AlgebraicGeometry.SmallEtale.HasWeightedTraceStalks` under which it is unique
is verified for the counit with abelian coefficients in
`AlgebraicGeometry.hasWeightedTraceStalks_counit`."]
def moduleEtaleCanonicalTrace :
    moduleRestriction B X hX U Λ ⋙ moduleExtensionByZero B X hX U Λ ⟶
      𝟭 (Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ)) :=
  (moduleExtensionByZeroAdjunction B X hX U Λ).counit

/-- The trace on sheaves of `Λ`-modules is the counit of the extension-by-zero adjunction, by
construction. -/
theorem moduleEtaleCanonicalTrace_eq_counit :
    moduleEtaleCanonicalTrace B X hX U Λ =
      (moduleExtensionByZeroAdjunction B X hX U Λ).counit :=
  rfl

/-- The trace map is functorial in the sheaf of `Λ`-modules. -/
@[stacks 0GKH "Part (1) with `Λ`-module coefficients — functoriality of the trace map in the
sheaf of `Λ`-modules — for an étale morphism with its canonical weighting. This is the
coefficient half of part (3); the DERIVED half of part (3), for `K` in `D(Y_étale, Λ)`, is NOT
carried, and neither is part (2), compatibility with arbitrary base change. For part (1) with
abelian coefficients but an arbitrary locally quasi-finite morphism and arbitrary weight, see
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_naturality`. The general weighted trace of
Lemma 0GKG is `AlgebraicGeometry.SmallEtale.weightedTrace`; see the clause on
`AlgebraicGeometry.moduleEtaleCanonicalTrace`."]
theorem moduleEtaleCanonicalTrace_naturality
    {F G : Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ)} (φ : F ⟶ G) :
    (moduleRestriction B X hX U Λ ⋙ moduleExtensionByZero B X hX U Λ).map φ ≫
        (moduleEtaleCanonicalTrace B X hX U Λ).app G =
      (moduleEtaleCanonicalTrace B X hX U Λ).app F ≫ φ :=
  (moduleEtaleCanonicalTrace B X hX U Λ).naturality φ

section Finite

variable [IsFinite (B.inclusion.map U.obj.hom)]

/-- On sheaves of `Λ`-modules: for a finite étale `j`, composing the comparison `j_! ⟶ j_*` with
the trace map of Stacks 03SE returns the counit of `j_! ⊣ j^{-1}`. -/
@[stacks 0GL4 "The Étale Cohomology, Section 03SH half of the remark on sheaves of
`Λ`-modules: the counit of `j_! ⊣ j^{-1}` is the morphism already called the trace there,
namely the trace map of Stacks 03SE read through the comparison `j_! ⟶ j_*`. Stated for a
FINITE étale `j`, where the 03SE trace is defined. The remark's own equality against the trace
map of Example 0GKI, with abelian coefficients, is
`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit`."]
theorem moduleEtaleCanonicalTrace_eq_comparison_comp_moduleTrace :
    moduleEtaleCanonicalTrace B X hX U Λ =
      Functor.whiskerLeft (moduleRestriction B X hX U Λ)
        (moduleExtensionByZeroToPushforward B X hX U Λ) ≫ moduleTrace B X hX U Λ :=
  (moduleExtensionByZeroToPushforward_comp_moduleTrace B X hX U Λ).symm

end Finite

end Modules

end AlgebraicGeometry

end
