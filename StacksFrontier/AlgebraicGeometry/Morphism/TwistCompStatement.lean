module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistComp

/-!
# Tag 07ZH in one statement

Let `S` be a scheme, let `A`, `B` and `C` be quasi-coherent graded `𝒪_S`-algebras and let
`φ : A ⟶ B` and `ψ : B ⟶ C` be homomorphisms between them. Write `X = Proj_S(A)`,
`Y = Proj_S(B)` and `Z = Proj_S(C)`. Tag 07ZG attaches to each such homomorphism an open on
which it induces a morphism, that morphism, and a family of comparison maps on the twists.
Tag 07ZH makes three assertions about how those three data behave under composition: the open of
the composite is the inverse image under `r_ψ` of the open of `φ`; the morphism of the composite
is the restriction of `r_ψ` followed by `r_φ`; and the comparison maps compose,
`θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ∘φ}`.

All three are proved — `Stacks.AlgebraicGeometry.RelativeProjMapComp.relativeMapDomain_comp`,
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeMapHomRestrict_comp_relativeMapHom` and
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_comp` — each on its own declaration.
This file states the three together, so that one declaration says what the tag says. The source
has no hypotheses beyond the data, and neither does the statement below: its binders are the
scheme, the three graded algebras and the two homomorphisms.

The second and third conjuncts are taken at
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeMapHomRestrict`, the canonical name for the
restriction `r_ψ|_{U(ψ ∘ φ)}` as a morphism into `U(φ)`. Stating both at the same morphism is
what makes the conjunction a single assertion about one restriction rather than two assertions
about two incidentally equal ones; the alternative form of the second conjunct,
`Stacks.AlgebraicGeometry.RelativeProjMapComp.relativeMapHom_comp`, says the same thing with the
restriction spelled out inline as a `let`-bound transport of `r_ψ` along the first conjunct.

## Implementation notes

As recorded in `StacksFrontier.AlgebraicGeometry.Morphism.Composition`, the first assertion is
printed in the source as `U(ψ ∘ φ) = r_φ^{-1}(U(ψ))`, which does not typecheck: `r_φ` is defined
on `U(φ) ⊆ Proj_S(B)` and so takes inverse images of opens of `Proj_S(A)`, whereas `U(ψ)` is an
open of `Proj_S(C)`. The two names have been interchanged, and the intended reading, which the
rest of the tag uses and which is what appears below, is `U(ψ ∘ φ) = r_ψ^{-1}(U(φ))` — an
equality of opens of `Proj_S(C)`, written as the image under the inclusion of `U(ψ)` of the
inverse image of `U(φ)` along `r_ψ`.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwistStatement.relativeMapDomain_mapHom_twistMap_comp`:
  **the three assertions of Tag 07ZH in one statement.**

## References

* [Stacks Project, Tag 07ZH](https://stacks.math.columbia.edu/tag/07ZH)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapComp
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.Tag07ZGTwist

namespace Stacks.AlgebraicGeometry.Tag07ZGTwistStatement

universe u

variable {S : Scheme.{u}} {A B C : SheafGradedAlgebra S} (φ : SheafGradedAlgebraHom A B)
  (ψ : SheafGradedAlgebraHom B C)

/-- **[Stacks, Tag 07ZH].** Let `S` be a scheme, let `A`, `B` and `C` be quasi-coherent graded
`𝒪_S`-algebras and let `φ : A ⟶ B` and `ψ : B ⟶ C` be homomorphisms between them. Then the open,
the morphism and the maps on twists that Tag 07ZG attaches to the composite `ψ ∘ φ` are
determined by those of `φ` and of `ψ`.

The three conjuncts are, in order:

1. `U(ψ ∘ φ) = r_ψ^{-1}(U(φ))`: the open attached to the composite is the inverse image under
  `r_ψ` of the open attached to the inner factor, read inside `Proj_S(C)` as the image of that
  inverse image under the inclusion of `U(ψ)`. (This is the intended reading of a source
  statement that is type-incorrect as printed; see the implementation notes above.)
2. `r_{ψ ∘ φ} = r_φ ∘ r_ψ|_{U(ψ ∘ φ)}`: the morphism attached to the composite is the
  restriction `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeMapHomRestrict` of `r_ψ` to
  `U(ψ ∘ φ)`, followed by the morphism attached to the inner factor.
3. `θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}`: for every `n` the `n`-th map on twists of the composite is the
  inverse image along that same restriction of the `n`-th map on twists of `φ`, followed by the
  inverse image along the inclusion of `U(ψ ∘ φ)` into `U(ψ)` of the `n`-th map on twists of
  `ψ`. The isomorphisms of inverse-image functors that identify the source and the target of the
  two sides are the ones named by conjuncts 1 and 2 and by
  `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeMapHomRestrict_comp_ι`.

Each conjunct is the corresponding component declaration:
`Stacks.AlgebraicGeometry.RelativeProjMapComp.relativeMapDomain_comp`,
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeMapHomRestrict_comp_relativeMapHom` and
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_comp`. The source states the tag for
arbitrary `A`, `B`, `C`, `φ` and `ψ`, and those are the only binders here. -/
@[stacks 07ZH "the tag's three assertions in one statement: the domain of the composite is the
inverse image of the inner factor's domain along `r_ψ`, the morphism of the composite is the
restriction of `r_ψ` followed by `r_φ`, and the maps on twists compose. The first conjunct is
the intended reading `U(psi.comp phi) = r_psi^{-1}(U(phi))` of a source statement printed as
`U(psi.comp phi) = r_phi^{-1}(U(psi))`, which is TYPE-INCORRECT -- `r_phi` is defined on
`U(phi)` in `Proj_S(B)` and so accepts opens of `Proj_S(A)`, whereas `U(psi)` is an open of
`Proj_S(C)`, the two names having been interchanged; the deviation is documented in the module
docstring"]
theorem relativeMapDomain_mapHom_twistMap_comp :
    (ψ.comp φ).relativeMapDomain =
        ψ.relativeMapDomain.ι ''ᵁ (relativeMapHom ψ ⁻¹ᵁ φ.relativeMapDomain) ∧
      relativeMapHomRestrict φ ψ ≫ relativeMapHom φ = relativeMapHom (ψ.comp φ) ∧
      ∀ n : ℤ,
        (Scheme.Modules.pullbackCongr
              (relativeMapHomRestrict_comp_relativeMapHom φ ψ)).inv.app
            (relativeTwist A n) ≫
            (Scheme.Modules.pullbackComp (relativeMapHomRestrict φ ψ)
              (relativeMapHom φ)).inv.app (relativeTwist A n) ≫
            (Scheme.Modules.pullback (relativeMapHomRestrict φ ψ)).map
              (relativeTwistMap φ n) ≫
            (Scheme.Modules.pullbackComp (relativeMapHomRestrict φ ψ)
              φ.relativeMapDomain.ι).hom.app (relativeTwist B n) ≫
            (Scheme.Modules.pullbackCongr
              (relativeMapHomRestrict_comp_ι φ ψ)).hom.app (relativeTwist B n) ≫
            (Scheme.Modules.pullbackComp
              ((relativeProj C).scheme.homOfLE (relativeMapDomain_comp_le φ ψ))
              (relativeMapHom ψ)).inv.app (relativeTwist B n) ≫
            (Scheme.Modules.pullback ((relativeProj C).scheme.homOfLE
              (relativeMapDomain_comp_le φ ψ))).map (relativeTwistMap ψ n) ≫
            (Scheme.Modules.pullbackComp
              ((relativeProj C).scheme.homOfLE (relativeMapDomain_comp_le φ ψ))
              ψ.relativeMapDomain.ι).hom.app (relativeTwist C n) ≫
            (Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι (relativeProj C).scheme
              (relativeMapDomain_comp_le φ ψ))).hom.app (relativeTwist C n) =
          relativeTwistMap (ψ.comp φ) n :=
  ⟨relativeMapDomain_comp φ ψ, relativeMapHomRestrict_comp_relativeMapHom φ ψ,
    fun n => relativeTwistMap_comp φ ψ n⟩

end Stacks.AlgebraicGeometry.Tag07ZGTwistStatement

end
