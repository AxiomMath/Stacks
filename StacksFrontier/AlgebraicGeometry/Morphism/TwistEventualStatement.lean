module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistEventual
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tags 07ZI, 07ZJ and 07ZK, each in one statement

Let `S` be a scheme, let `A` and `B` be quasi-coherent graded `𝒪_S`-algebras and let `ψ : A ⟶ B`
be a homomorphism between them. Write `X = Proj_S(A)` and `Y = Proj_S(B)`, let `U(ψ) ⊆ Y` be the
open on which `ψ` induces a morphism, let `r_ψ : U(ψ) ⟶ X` be that morphism and let

`θ_n : r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)|_{U(ψ)}`

be the map of Tag 07ZG's assertion (3).

Each of Tags 07ZI, 07ZJ and 07ZK is a list of three assertions about `U(ψ)`, `r_ψ` and the family
`θ_n` under one hypothesis on the degreewise maps `A_d → B_d`. All nine assertions are proved, in
`StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualSurjective`,
`StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualBijective` and
`StacksFrontier.AlgebraicGeometry.Morphism.TwistEventual`, each on its own declaration. This file
puts the three assertions of each tag into a single theorem, so that one declaration states what
the tag states.

The three carriers take exactly the hypotheses of their sources and nothing else: eventual
surjectivity for Tag 07ZI, eventual invertibility for Tag 07ZJ, and eventual surjectivity
together with generation in degree one for Tag 07ZK. Each proof is the anonymous-constructor
tuple of the three component declarations, which are left exactly where they are.

The parenthetical of Tag 07ZI — that the maps `θ_n` are surjective but in general not
isomorphisms — is a remark asking for a counterexample, not a conjunct, and is not formalized
here or in `StacksFrontier.AlgebraicGeometry.Morphism.TwistEventual`; the positive content of
Tag 07ZK is the hypothesis under which those maps do become isomorphisms.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwistStatement.domain_closedImmersion_twistEpi_of_eventually_epi`:
  **the three assertions of Tag 07ZI in one statement.**
* `Stacks.AlgebraicGeometry.Tag07ZGTwistStatement.domain_isIso_twistIsIso_of_eventually_isIso`:
  **the three assertions of Tag 07ZJ in one statement.**
* `Stacks.AlgebraicGeometry.Tag07ZGTwistStatement.domain_closedImmersion_twistIsIso_of_generatedInDegreeOne`:
  **the three assertions of Tag 07ZK in one statement.**

## References

* [Stacks Project, Tag 07ZI](https://stacks.math.columbia.edu/tag/07ZI)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 07ZK](https://stacks.math.columbia.edu/tag/07ZK)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.Tag07ZGTwist

namespace Stacks.AlgebraicGeometry.Tag07ZGTwistStatement

universe u

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- **[Stacks, Tag 07ZI].** Let `S` be a scheme, let `A` and `B` be quasi-coherent graded
`𝒪_S`-algebras and let `ψ : A ⟶ B` be a homomorphism between them. If `A_d → B_d` is surjective
for all sufficiently large `d`, then `U(ψ) = Y`, the morphism `r_ψ : U(ψ) ⟶ X` of Tag 07ZG is a
closed immersion, and every map `θ_n : r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)|_{U(ψ)}` is an epimorphism.

The three conjuncts are, in order:

1. The open of `Y = Proj_S(B)` on which `ψ` induces a morphism is all of `Y`.
2. That morphism is a closed immersion.
3. For every `n : ℤ` the comparison map on the `n`-th twist is an epimorphism.

Each is the corresponding component declaration:
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.relativeMapDomain_eq_top_of_eventually_epi`,
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.isClosedImmersion_relativeMapHom_of_eventually_epi`
and `Stacks.AlgebraicGeometry.Tag07ZGTwist.epi_relativeTwistMap_of_eventually_epi`. The only
hypothesis is the source's, degreewise surjectivity in all large degrees. -/
@[stacks 07ZI "the tag's three assertions in one statement: under degreewise surjectivity in all
large degrees the domain of definition is all of `Proj_S(B)`, the induced morphism `r_ψ` is a
closed immersion, and every comparison map `θ_n` on twists is an epimorphism",
  ega "II 2.9.2" "more general"]
theorem domain_closedImmersion_twistEpi_of_eventually_epi
    (hsurj : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ))) :
    ψ.relativeMapDomain = ⊤ ∧
      IsClosedImmersion (relativeMapHom ψ) ∧
      ∀ n : ℤ, Epi (relativeTwistMap ψ n) :=
  ⟨relativeMapDomain_eq_top_of_eventually_epi ψ hsurj,
    isClosedImmersion_relativeMapHom_of_eventually_epi ψ hsurj,
    fun n => epi_relativeTwistMap_of_eventually_epi ψ hsurj n⟩

/-- **[Stacks, Tag 07ZJ].** Let `S` be a scheme, let `A` and `B` be quasi-coherent graded
`𝒪_S`-algebras and let `ψ : A ⟶ B` be a homomorphism between them. If `A_d → B_d` is an
isomorphism for all sufficiently large `d`, then `U(ψ) = Y`, the morphism `r_ψ : U(ψ) ⟶ X` of
Tag 07ZG is an isomorphism, and every map `θ_n : r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)|_{U(ψ)}` is an
isomorphism.

The three conjuncts are, in order:

1. The open of `Y = Proj_S(B)` on which `ψ` induces a morphism is all of `Y`.
2. That morphism is an isomorphism.
3. For every `n : ℤ` the comparison map on the `n`-th twist is an isomorphism.

Each is the corresponding component declaration:
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.relativeMapDomain_eq_top_of_eventually_isIso`,
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.isIso_relativeMapHom_of_eventually_isIso` and
`Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_relativeTwistMap_of_eventually_isIso`. The only
hypothesis is the source's, degreewise invertibility in all large degrees. -/
@[stacks 07ZJ "the tag's three assertions in one statement: under degreewise invertibility in all
large degrees the domain of definition is all of `Proj_S(B)`, the induced morphism `r_ψ` is an
isomorphism, and every comparison map `θ_n` on twists is an isomorphism",
  ega "II 3.6.1" "TN-bijective clause"]
theorem domain_isIso_twistIsIso_of_eventually_isIso
    (hbij : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ))) :
    ψ.relativeMapDomain = ⊤ ∧
      IsIso (relativeMapHom ψ) ∧
      ∀ n : ℤ, IsIso (relativeTwistMap ψ n) :=
  ⟨relativeMapDomain_eq_top_of_eventually_isIso ψ hbij,
    isIso_relativeMapHom_of_eventually_isIso ψ hbij,
    fun n => isIso_relativeTwistMap_of_eventually_isIso ψ hbij n⟩

/-- **[Stacks, Tag 07ZK].** Let `S` be a scheme, let `A` and `B` be quasi-coherent graded
`𝒪_S`-algebras and let `ψ : A ⟶ B` be a homomorphism between them. If `A_d → B_d` is surjective
for all sufficiently large `d` and `A` is generated by `A_1` over `A_0`, then `U(ψ) = Y`, the
morphism `r_ψ : U(ψ) ⟶ X` of Tag 07ZG is a closed immersion, and every map
`θ_n : r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)|_{U(ψ)}` is an isomorphism.

The three conjuncts are, in order:

1. The open of `Y = Proj_S(B)` on which `ψ` induces a morphism is all of `Y`.
2. That morphism is a closed immersion.
3. For every `n : ℤ` the comparison map on the `n`-th twist is an isomorphism.

The first two are the two component declarations of Tag 07ZI,
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.relativeMapDomain_eq_top_of_eventually_epi` and
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.isClosedImmersion_relativeMapHom_of_eventually_epi`,
which need only the surjectivity hypothesis; the third is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_relativeTwistMap_of_generatedInDegreeOne`, which
uses both. Generation in degree one is read over the affine opens of the base, which is where the
graded algebras have graded rings of sections. -/
@[stacks 07ZK "the tag's three assertions in one statement: under degreewise surjectivity in all
large degrees and generation in degree one the domain of definition is all of `Proj_S(B)`, the
induced morphism `r_ψ` is a closed immersion, and every comparison map `θ_n` on twists is an
isomorphism", ega "II 3.5.1" "special case"]
theorem domain_closedImmersion_twistIsIso_of_generatedInDegreeOne
    (hsurj : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ)))
    (hgen : ∀ U : S.Opens, IsAffineOpen U → A.IsGeneratedInDegreeOneAt U) :
    ψ.relativeMapDomain = ⊤ ∧
      IsClosedImmersion (relativeMapHom ψ) ∧
      ∀ n : ℤ, IsIso (relativeTwistMap ψ n) :=
  ⟨relativeMapDomain_eq_top_of_eventually_epi ψ hsurj,
    isClosedImmersion_relativeMapHom_of_eventually_epi ψ hsurj,
    fun n => isIso_relativeTwistMap_of_generatedInDegreeOne ψ hsurj hgen n⟩

end Stacks.AlgebraicGeometry.Tag07ZGTwistStatement

end
