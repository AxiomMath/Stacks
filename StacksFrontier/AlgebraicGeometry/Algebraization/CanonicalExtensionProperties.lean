module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CanonicalExtensionMittagLeffler
public import StacksFrontier.AlgebraicGeometry.Algebraization.CanonicalExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.Algebraization.GradedAlgebraization

/-!
# The four properties of a canonically extending coherent adic system

In the algebraization situation of a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with
`X = Spec(A)` and `U = X ∖ V(𝔞)`, let `(ℱₙ)` be a coherent `I`-adic system on `U` which
canonically extends to `X`. [Stacks, Tag 0EIR] asserts that

1. `(H⁰(U, ℱₙ)^~)` is pro-isomorphic to an object `(𝒢ₙ)` of `Coh(X, I𝒪_X)`, unique up to unique
   isomorphism;
2. the restriction of `(𝒢ₙ)` to `U` is isomorphic to `(ℱₙ)`, so that `(ℱₙ)` extends to `X`;
3. the inverse system `{H⁰(U, ℱₙ)}` satisfies the Mittag-Leffler condition;
4. the module `M = limₙ H⁰(U, ℱₙ)` is finite over the `I`-adic completion of `A`, and its limit
   topology is its `I`-adic topology.

This file states part (2) for the extension of part (1) itself, and collects the four parts into
one statement.

## Main results

* `Stacks.Algebraization.nonempty_restrictionIso_canonicalExtension` — part (2) for the
  extension `Stacks.Algebraization.canonicalExtension` of part (1).
* `Stacks.Algebraization.canonicallyExtends_properties` — parts (1) to (4) of Tag 0EIR.

## Implementation notes

Part (2) holds for every coherent adic system on `X` presenting the pro-object of
`(H⁰(U, ℱₙ)^~)`, which is `Stacks.Algebraization.nonempty_restrictionIso_of_proIso` applied to the
comparison `Stacks.Algebraization.tildeGlobalSectionsPullbackIso`: on the quasi-affine `U` the
sheaf associated to `H⁰(U, ℱₙ)` restricts to `ℱₙ` (Properties, Lemma 0EHM).

Finiteness over the completion `Â` is stated, as in
`Stacks.Algebraization.isAdicComplete_and_finite_adicCompletion_of_canonicallyExtends`, through
the canonical identification of `M` with its `I`-adic completion: `M` is `I`-adically complete,
and its completion is a finite `Â`-module.

## References

* [Stacks Project, Tag 0EIR](https://stacks.math.columbia.edu/tag/0EIR)
* [Stacks Project, Tag 0EIP](https://stacks.math.columbia.edu/tag/0EIP), canonical extension.
* [Stacks Project, Tag 0EIM](https://stacks.math.columbia.edu/tag/0EIM), extension to `X`.
* [Stacks Project, Tag 0EIQ](https://stacks.math.columbia.edu/tag/0EIQ), full faithfulness.
* [Stacks Project, Tag 0EHD](https://stacks.math.columbia.edu/tag/0EHD), the module `M`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **Part (2) of Stacks Project, Tag 0EIR.** If a coherent `I`-adic system `(ℱₙ)` on the open
complement `U` canonically extends to `X`, then the restriction to `U` of its canonical extension
`(𝒢ₙ)`, the coherent `I`-adic system on `X` of part (1), is isomorphic to `(ℱₙ)` as an inverse
system. -/
@[stacks 0EIR "part (2): the restriction to the open complement U of the canonical extension \
(G_n) of part (1) is isomorphic to (F_n) as an inverse system"]
public theorem nonempty_restrictionIso_canonicalExtension (h : CanonicallyExtends S F) :
    Nonempty ((canonicalExtension S F h).1.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι ≅
      F.obj) :=
  nonempty_restrictionIso_of_proIso S F (tildeGlobalSectionsPullbackIso S F)
    (canonicalExtension S F h).1 (canonicalExtension S F h).2

/-- **Stacks Project, Tag 0EIR.** Let `(ℱₙ)` be a coherent `I`-adic system on the open
complement `U` of an algebraization situation which canonically extends to `X`. Then

1. the system `(H⁰(U, ℱₙ)^~)` is pro-isomorphic to a coherent `I`-adic system `(𝒢ₙ)` on `X`, and
   any two such systems, each with a chosen pro-isomorphism, are isomorphic by exactly one
   isomorphism compatible with the two choices;
2. the restriction to `U` of any such `(𝒢ₙ)` is isomorphic to `(ℱₙ)`, so `(ℱₙ)` extends to `X`;
3. the inverse system `{H⁰(U, ℱₙ)}` satisfies the Mittag-Leffler condition;
4. the module `M = limₙ H⁰(U, ℱₙ)` is `I`-adically complete with its `I`-adic completion finite
   over the `I`-adic completion `Â` of `A` (that is, `M` is a finite `Â`-module), and the limit
   topology on `M` is the `I`-adic topology. -/
@[stacks 0EIR "parts (1) to (4): existence and uniqueness up to unique isomorphism of the \
coherent adic system (G_n) on X pro-isomorphic to the sheaves of global sections, its restriction \
to U isomorphic to (F_n), the Mittag-Leffler condition, and finiteness of M over the completion \
of A with limit topology equal to the I-adic topology"]
public theorem canonicallyExtends_properties (h : CanonicallyExtends S F) :
    -- (1), existence
    (∃ G : Stacks.Coherent.CoherentAdicSystems (idealOnX S),
      Nonempty (Stacks.Coherent.diagramToPro (tildeGlobalSectionsSystem S F) ≅
        (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj G)) ∧
    -- (1), uniqueness up to unique isomorphism
    (∀ (G H : Stacks.Coherent.CoherentAdicSystems (idealOnX S))
      (φ : Stacks.Coherent.diagramToPro (tildeGlobalSectionsSystem S F) ≅
        (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj G)
      (ψ : Stacks.Coherent.diagramToPro (tildeGlobalSectionsSystem S F) ≅
        (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj H),
      ∃! e : G ≅ H,
        φ ≪≫ (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).mapIso e = ψ) ∧
    -- (2)
    (∀ (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S))
      (_ : Stacks.Coherent.diagramToPro (tildeGlobalSectionsSystem S F) ≅
        (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj G),
      Nonempty (G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι ≅ F.obj)) ∧
    ExtendsToX S (kerComapSystem S F) ∧
    -- (3)
    IsMittagLefflerCategorical (globalSectionsSystem S F) ∧
    -- (4)
    (IsAdicComplete S.I (limitGlobalSections S F) ∧
      Module.Finite (AdicCompletion S.I S.A)
        (AdicCompletion S.I (limitGlobalSections S F : Type u))) ∧
    LimitTopologyAgrees S F :=
  ⟨h, existsUnique_compatibleIso S _,
    fun G e => nonempty_restrictionIso_of_proIso S F (tildeGlobalSectionsPullbackIso S F) G e,
    extendsToX_kerComapSystem_of_canonicallyExtends S F h,
    isMittagLefflerCategorical_of_canonicallyExtends S F h,
    isAdicComplete_and_finite_adicCompletion_of_canonicallyExtends S F h,
    limitTopologyAgrees_of_canonicallyExtends S F h⟩

end Stacks.Algebraization

end
