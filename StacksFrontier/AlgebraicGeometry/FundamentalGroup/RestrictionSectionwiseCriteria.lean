module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme

/-!
# Sectionwise criteria for fully faithful restriction of finite étale covers

Let `Y ⊆ X` be a closed subscheme of a Noetherian scheme and let `Y_n ⊆ X` be the infinitesimal
neighbourhoods of `Y` in `X`. [Stacks, Tag 0EJZ] asserts that restriction of finite étale covers
`FÉt_X ⟶ FÉt_Y` is fully faithful as soon as one of three sectionwise conditions holds:

1. `X` is quasi-affine and `Γ(X, 𝒪_X) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism;
2. `X` carries an ample invertible module `L` and `Γ(X, L^{⊗ m}) → lim Γ(Y_n, L^{⊗ m}|_{Y_n})` is
   an isomorphism for all `m ≫ 0`;
3. `Γ(X, ℰ) → lim Γ(Y_n, ℰ|_{Y_n})` is an isomorphism for every finite locally free module `ℰ`.

The source proves this "formally" by combining [Stacks, Tag 0EL8] — full faithfulness of
restriction from full faithfulness of the completion functor on finite locally free coherent
modules — with [Stacks, Tag 0EKP], the chain of implications `(1) ⇒ (2) ⇒ (3) ⇒ (4)` where `(4)`
is that full faithfulness of completion. Both of those tags are carried by this library, but
Tag 0EKP only in part: `Stacks.Algebraization.quasiAffine_sectionsComplete_implies_amplePower_`
`sectionsComplete` is `(1) ⇒ (2)` and the two remaining implications have no carrier (the
reasons are catalogued in the module documentation of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic`). Tag 0EJZ itself,
all three cases with none of those implications assumed, is
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_sectionsComplete_of_or` in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionSectionwiseComplete`, which takes the
chain from `Stacks.Algebraization.sectionsComplete_chain`. Tag 0EL9 carries neither of
the two hypotheses `h0GN2`/`halgebra` of Tag 0EL8: `h0GN2` is proved below as
`Stacks.FundamentalGroup.dualSectionsHypothesis`, and `halgebra` — whose statement is
*false* as it stands, see its documentation — is replaced by the corrected criterion
`Stacks.RelativeSpec.AlgebraSheaf.exists_hom_of_jointlyInjective_of_isLocallyNoetherian`
through `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completion`
`FullyFaithful_of_dualSections`.

## Main definitions

* `Stacks.FundamentalGroup.SectionsCompleteQuasiAffine`,
  `Stacks.FundamentalGroup.SectionsCompleteAmplePowers`,
  `Stacks.FundamentalGroup.SectionsCompleteFiniteLocallyFree` — conditions (1), (2) and (3)
  above, spelled exactly as the statement of Tag 0EKP spells them, so that its
  `(1) ⇒ (2)` applies to them directly.
* `Stacks.FundamentalGroup.DualSectionsHypothesis`,
  `Stacks.FundamentalGroup.AlgebraMultiplicativityHypothesis` — the two auxiliary hypotheses
  `h0GN2` and `halgebra` of
  `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful`,
  named so that they can be stated once and quoted.

## Main results

* `Stacks.FundamentalGroup.dualSectionsHypothesis` — the hypothesis `h0GN2`, proved.
* `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completionEquivalence` — the
  fully faithful half of the conclusion of [Stacks, Tag 0EL9], with no auxiliary hypothesis. The
  whole of that tag, essential surjectivity included, is
  `Stacks.FundamentalGroup.finiteEtaleBaseChange_isEquivalence_of_completion` in
  `StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionEquivalenceOfCompletion`.

## Implementation notes

The index `n` of `Stacks.Algebraization.nthInfinitesimalNeighbourhood` is the source's `n + 1`,
so the family of neighbourhoods swept out by `IsInfinitesimalSectionsComplete` is exactly the
source's `Y_1, Y_2, …`; the inverse limit is unchanged because the index set is cofinal. The
isomorphism in (1)–(3) is expressed by the universal property of that limit, as
`Stacks.Algebraization.IsInfinitesimalSectionsComplete` expresses it: every compatible family of
sections on the neighbourhoods has a unique antecedent in `Γ(X, ℰ)`.

Condition (2) is stated with the invertibility of `L` as a bound `∃`-witness followed by `letI`,
rather than as an instance argument, because that is the shape in which the carrier of
`(1) ⇒ (2)` concludes it; the two are then literally the same proposition and no transport is
needed.

[Stacks, Tag 0EL9] assumes that the completion functor is an *equivalence* on the finite locally
free objects and concludes that restriction is an *equivalence*. The fully faithful half of the
conclusion uses only the fully faithful half of the hypothesis, and that is what is recorded here.
The whole tag, whose essential surjectivity is the source's construction of a finite étale cover
of `X` from a tower of covers of the infinitesimal neighbourhoods, is proved in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionEquivalenceOfCompletion`.

Tag 0EL9 does *not* go through the carrier of Tag 0EL8, although its mathematical content is
exactly that argument. The carrier of Tag 0EL8 takes the multiplicativity criterion as a
hypothesis in a shape that is false as stated, so a declaration applying it is conditional on a
false premise; the correction is a coherence condition on the structure sheaf of the base, which
is an amendment to that carrier's interface. The argument is therefore run again, with the
corrected criterion in place, by
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful_of_`
`dualSections`. The correction costs nothing here: the condition holds on a locally Noetherian
scheme, and `X` is Noetherian by the tag's own hypothesis.

## References

* [Stacks Project, Tag 0EJZ](https://stacks.math.columbia.edu/tag/0EJZ)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 0EL9](https://stacks.math.columbia.edu/tag/0EL9)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence Stacks.Thickenings

universe u

namespace Stacks.FundamentalGroup

/-! ### The three sectionwise conditions -/

/-- **Condition (1) of [Stacks, Tag 0EJZ]:** `X` is quasi-affine and `Γ(X, 𝒪_X)` is the inverse
limit of the sections of the structure sheaves of the infinitesimal neighbourhoods of `Y`. -/
public def SectionsCompleteQuasiAffine {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] : Prop :=
  Scheme.IsQuasiAffine X ∧
    Stacks.Algebraization.IsInfinitesimalSectionsComplete i
      (SheafOfModules.unit X.ringCatSheaf)

/-- **Condition (2) of [Stacks, Tag 0EJZ]:** `X` carries an ample invertible module `L` such that
for all large `m` the sections of `L^{⊗ m}` are the inverse limit of their restrictions to the
infinitesimal neighbourhoods of `Y`. -/
public def SectionsCompleteAmplePowers {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] : Prop :=
  ∃ (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L),
    letI := hL
    AlgebraicGeometry.Scheme.Modules.IsAmple X L ∧
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        Stacks.Algebraization.IsInfinitesimalSectionsComplete i
          (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (m : ℤ))

/-- **Condition (3) of [Stacks, Tag 0EJZ]:** the sections of every finite locally free module are
the inverse limit of their restrictions to the infinitesimal neighbourhoods of `Y`. -/
public def SectionsCompleteFiniteLocallyFree {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] : Prop :=
  ∀ E : X.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E →
    Stacks.Algebraization.IsInfinitesimalSectionsComplete i E

/-! ### The two auxiliary hypotheses inherited from Tag 0EL8 -/

/-- The hypothesis `h0GN2` of
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful`, named.

It is the shape in which [Stacks, Tag 0GN2] — invertibility of the canonical comparison
`v^*(M^∨) ⟶ (v^* M)^∨` of [Stacks, Tag 0GMX] — is used there: for a finite locally free module
`N` on a scheme `Z` with a closed subscheme, granted infinitesimal section completeness of the
dual `N^∨`, the module maps `N ⟶ 𝒪_Z` are exactly the compatible systems of maps into the direct
images of the structure sheaves of the infinitesimal neighbourhoods. Besides Tag 0GN2 it
packages the identification of the global sections of an internal hom with the morphisms it
parametrises, and the pullback–pushforward adjunction. -/
public def DualSectionsHypothesis : Prop :=
  ∀ {Z Z' : Scheme.{u}} (κ : Z' ⟶ Z) [IsClosedImmersion κ] (N : Z.Modules),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N →
    Stacks.Algebraization.IsInfinitesimalSectionsComplete κ
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) →
    (∀ φ ψ : N ⟶ SheafOfModules.unit Z.ringCatSheaf,
        (∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = ψ ≫ nthOrderUnitMap κ n) → φ = ψ) ∧
      ∀ α : ∀ n : ℕ, N ⟶ AlgebraSheaf.underlyingModule (nthOrderAlgebra κ n),
        (∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap κ n = α n) →
        ∃ φ : N ⟶ SheafOfModules.unit Z.ringCatSheaf,
          ∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = α n

/-- **The hypothesis `h0GN2` holds.** Its two clauses are
`Stacks.FundamentalGroup.nthOrderUnitMap_jointly_injective` and
`Stacks.FundamentalGroup.exists_hom_of_nthOrderUnitMap_compatible`.

This is deliberately left untagged. It is not Tag 0GN2, which asserts that the canonical
comparison `v^*(M^∨) ⟶ (v^* M)^∨` of Tag 0GMX is invertible; that statement has its own carrier,
and this is a packaged consequence of it together with the identification of the global sections
of an internal hom with the morphisms it parametrises and the pullback–pushforward adjunction. -/
public theorem dualSectionsHypothesis : DualSectionsHypothesis.{u} := by
  intro Z Z' κ _ N hN hc
  exact ⟨nthOrderUnitMap_jointly_injective κ N hN hc,
    exists_hom_of_nthOrderUnitMap_compatible κ N hN hc⟩

/-- The hypothesis `halgebra` of
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful`, named.

It is the criterion detecting multiplicativity of a morphism of the underlying modules of two
sheaves of algebras on the tensor square: a morphism of the underlying modules of `B` and `C`,
with that of `B` coherent and finite locally free, which becomes a morphism of algebra sheaves
after composition with each member of a family of morphisms of algebra sheaves that is jointly
injective on the morphisms out of coherent finite locally free modules, is itself a morphism of
algebra sheaves.

**This statement is false as written, and the true form carries a coherence condition on
`𝒪_Z`.** Multiplicativity follows from joint injectivity on the tensor square, but unitality
needs joint injectivity at `𝒪_Z` itself, which the hypothesis supplies only when `𝒪_Z` is
coherent; nothing here constrains `C` over opens where `B` vanishes. For a counterexample take
`Z` the one-point `Spec k[y₁, y₂, …]/(yᵢyⱼ)`, whose structure sheaf is coherent on no nonempty
open, with `B` and each `D n` the zero sheaf of rings — an algebra sheaf, since the zero ring is
terminal — and `C = 𝒪_Z`, `φ = 0`. Every hypothesis holds, because the only coherent finite
locally free module is `0` by [Stacks, Tag 01BY] part (1), while a map of sheaves of rings
`0 ⟶ 𝒪_Z` would force `1 = 0` in `Γ(Z, 𝒪_Z)`.

The corrected statement is proved: `Stacks.RelativeSpec.AlgebraSheaf.exists_hom_of_jointlyInjective`
adds `SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf)`, and
`exists_hom_of_jointlyInjective_of_isLocallyNoetherian` assumes `[IsLocallyNoetherian Z]`
instead. Consumers of this predicate are therefore conditional on a false premise until they
are restated with that condition, which is an amendment to their own signatures. -/
public def AlgebraMultiplicativityHypothesis : Prop :=
  ∀ {Z : Scheme.{u}} (B C : AlgebraSheaf Z) (D : ℕ → AlgebraSheaf Z) (r : ∀ n : ℕ, C ⟶ D n)
    (φ : AlgebraSheaf.underlyingModule B ⟶ AlgebraSheaf.underlyingModule C),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (AlgebraSheaf.underlyingModule B) →
    _root_.SheafOfModules.IsCoherent (AlgebraSheaf.underlyingModule B) →
    (∀ n : ℕ, ∃ ψ : B ⟶ D n,
      AlgebraSheaf.underlyingModuleMap ψ = φ ≫ AlgebraSheaf.underlyingModuleMap (r n)) →
    (∀ P : Z.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} P →
      _root_.SheafOfModules.IsCoherent P →
      ∀ a b : P ⟶ AlgebraSheaf.underlyingModule C,
        (∀ n : ℕ, a ≫ AlgebraSheaf.underlyingModuleMap (r n) =
          b ≫ AlgebraSheaf.underlyingModuleMap (r n)) → a = b) →
    ∃ ψ : B ⟶ C, AlgebraSheaf.underlyingModuleMap ψ = φ

/-! ### Tag 0EL9, fully faithful half -/

/-- **[Stacks, Tag 0EL9], the fully faithful half of the conclusion.** Let `X` be a Noetherian
scheme and `Y ⊆ X` a closed subscheme with ideal sheaf `I`. The source assumes that the
completion functor `Coh(𝒪_X) ⟶ Coh(X, I)` is an *equivalence* on the full subcategories of
finite locally free objects and concludes that `FÉt_X ⟶ FÉt_Y` is an *equivalence*. Full
faithfulness of restriction uses only full faithfulness of completion, and that is what is
proved here, by [Stacks, Tag 0EL8].

The essential surjectivity half of the conclusion is the source's construction of a finite étale
cover of `X` out of the tower of covers of the infinitesimal neighbourhoods; the whole tag is
`Stacks.FundamentalGroup.finiteEtaleBaseChange_isEquivalence_of_completion`.

Nothing is assumed beyond the tag's own hypothesis. The argument is that of Tag 0EL8, run again
through
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful_of_`
`dualSections` rather than through the carrier of Tag 0EL8 itself: that carrier takes the
multiplicativity criterion as a hypothesis in a form that is false as stated, and amending it
would change its interface. The hypothesis about duals is
`Stacks.FundamentalGroup.dualSectionsHypothesis`. -/
public theorem fullyFaithful_finiteEtaleBaseChange_of_completionEquivalence
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsNoetherian X] [IsClosedImmersion i]
    (hcompletion : Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree X i.ker) :
    Nonempty (finiteEtaleBaseChange i).FullyFaithful :=
  fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful_of_dualSections i hcompletion
    dualSectionsHypothesis.{u}

end Stacks.FundamentalGroup

end

end
