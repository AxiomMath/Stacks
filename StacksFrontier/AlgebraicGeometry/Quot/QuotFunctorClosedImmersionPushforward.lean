module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforwardConjugation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange

/-!
# The direct image along a closed immersion as an isomorphism of Quot functors

Let `B` be an algebraic space, let `π : X ⟶ Y` be a closed immersion of algebraic spaces which
are separated and of finite presentation over `B`, and let `F` be a quasi-coherent `𝒪_X`-module.
Stacks 0DP4 asserts that the morphism `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` of Stacks 0DP1 is an
isomorphism.

Over a test scheme `T` of `B` the base change `π_T : X_T ⟶ Y_T` is again a closed immersion, so
by Stacks 04CJ the direct image `π_{T,*}` identifies the `𝒪_{X_T}`-modules with the
`𝒪_{Y_T}`-modules annihilated by the ideal cutting out `X_T`; every quotient of
`G_T = (π_*F)_T = π_{T,*}F_T` is annihilated by that ideal, so the map
`Quot_{F/X/B}(T) ⟶ Quot_{π_*F/Y/B}(T)` is a bijection for every `T`, and the morphism of Quot
functors is an isomorphism.

The two halves of that bijectivity come apart.  Injectivity is *full faithfulness* of `π_{T,*}`;
surjectivity uses the *essential-image* half of Stacks 04CJ, part (3), and the descent of the four
conditions of Stacks 09TR along `π_{T,*}`.  This file proves the bijectivity from those two inputs,
taken as a structure; both are constructed in
`StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorClosedImmersionPushforwardUnconditional.lean`, and
Stacks 0DP4 itself is `isIso_pushforwardQuotFunctorMap_ofIsClosedImmersion`, in the namespace
`AlgebraicGeometry.Space.QuotPushforwardSituation`, in
`StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorClosedImmersionDirectImageIso.lean`.

## Main definitions

* `AlgebraicGeometry.Space.QuotPushforwardSituation.ClosedImmersionQuotInputs`: the two inputs of
  the surjectivity half of the source's proof, each field naming the result it stands for.

## Main results

* `AlgebraicGeometry.Space.QuotPushforwardSituation.isClosedImmersion_baseChangeOfMap`: the base
  change `π_T : X_T ⟶ Y_T` of a closed immersion is a closed immersion, by Stacks 02YW.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.fullyFaithfulPushforwardBaseChangeOfMap`:
  **Stacks 04CJ** for that base change — `π_{T,*}` is fully faithful.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotient_injective`: the direct
  image of quotients of `F_T` is injective.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.exists_pushforwardQuotient_eq`: every member
  of `Quot_{π_*F/Y/B}(T)` is the direct image of a member of `Quot_{F/X/B}(T)`.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.isIso_quotFunctorMap`: the morphism of Quot
  functors induced by a closed immersion is an isomorphism, given the two inputs.

## Implementation notes

**Two inputs are taken as a structure.**  Injectivity of the map on `T`-points needs only full
faithfulness of `π_{T,*}`, which is
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward` — Stacks 04CJ, part (2) — applied to the
base change of the closed immersion.  Surjectivity needs two further assertions, the fields of
`AlgebraicGeometry.Space.QuotPushforwardSituation.ClosedImmersionQuotInputs`:

* that every quotient of `G_T` is itself a direct image along `π_T`, which follows from the
  essential-image assertion of Stacks 04CJ, part (3),
  `AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal`;
* that the four conditions of Stacks 09TR descend along `π_{T,*}`, that is, that a module whose
  direct image is quasi-coherent, of finite presentation, flat over `T` and properly supported
  over `T` is itself so.

Both are constructed, for every closed immersion, by
`AlgebraicGeometry.Space.QuotPushforwardSituation.closedImmersionQuotInputs`.

**The closed immersion is an extra hypothesis on the standing data of Stacks 0DP1.**  That
standing data asks `π` to be affine and quasi-finite, which a closed immersion is; being a closed
immersion is asked here in addition, as the hypothesis `hπ`, since it is what Stacks 04CJ
consumes.

## References

* [Stacks Project, Tag 0DP4](https://stacks.math.columbia.edu/tag/0DP4)
* [Stacks Project, Tag 0DP1](https://stacks.math.columbia.edu/tag/0DP1)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotPushforwardSituation

variable (D : QuotPushforwardSituation B S hS)

/-! ### The base change of the closed immersion -/

/-- **The base change of a closed immersion is a closed immersion**, by Stacks 02YW, applied to
the base change `π_T : X_T ⟶ Y_T` of the morphism of the situation. -/
theorem isClosedImmersion_baseChangeOfMap (hπ : IsClosedImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) : IsClosedImmersion B S hS (D.baseChangeOfMap T).hom :=
  isClosedImmersion_of_isPullback B S hS (D.isPullback_baseChangeOfMap T).flip hπ

/-- **Stacks 04CJ for the base change of the closed immersion**: the direct image `π_{T,*}` of
`𝒪_{X_T}`-modules is fully faithful. -/
def fullyFaithfulPushforwardBaseChangeOfMap (hπ : IsClosedImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) :
    (modulePushforward B S hS (D.baseChangeOfMap T)).FullyFaithful :=
  fullyFaithfulModulePushforward B S hS (D.baseChangeOfMap T)
    (D.isClosedImmersion_baseChangeOfMap hπ T)

/-! ### The two inputs of the surjectivity half of the source's proof -/

/-- **The two inputs of the surjectivity half of the proof of Stacks 0DP4**, bundled.

The first field is the *essential-image* assertion of Stacks 04CJ, part (3), in the form the
argument consumes: every quotient of `G_T = π_{T,*}F_T` is a direct image along `π_T`.  In the
source this is the statement that `π_{T,*}` is an equivalence onto the `𝒪_{Y_T}`-modules
annihilated by the ideal cutting out `X_T`, applied to a quotient of `G_T`, which is so
annihilated because `G_T` is.

The second field is the reverse direction of the morphism of stacks `Coh_{X/B} ⟶ Coh_{Y/B}` of
Stacks 0DN9: the four conditions of Stacks 09TR descend along `π_{T,*}`.

Both fields are constructed for every closed immersion by
`AlgebraicGeometry.Space.QuotPushforwardSituation.closedImmersionQuotInputs`. -/
structure ClosedImmersionQuotInputs (D : QuotPushforwardSituation B S hS)
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS) where
  /-- **The essential-image assertion of Stacks 04CJ, part (3) for the situation**: a quotient of
  `G_T` is a direct image along `π_T`. -/
  essImage_quotientModule : ∀ (T : SchemesOver D.base)
      (K : Subobject ((D.targetSituation h).baseChangeModule T)),
    (modulePushforward B S hS (D.baseChangeOfMap T)).essImage
      ((D.targetSituation h).quotientModule T K)
  /-- **Stacks 0DN9 for the situation, in the reverse direction**: a module whose direct image
  along `π_T` satisfies the four conditions of Stacks 09TR over `T` satisfies them itself. -/
  isQuotModule_of_pushforward : ∀ (T : SchemesOver D.base)
      (Q : Modules.{u, u} B S hS (D.sourceSituation.space T).1 (D.sourceSituation.space T).2),
    (D.targetSituation h).IsQuotModule T
        ((modulePushforward B S hS (D.baseChangeOfMap T)).obj Q) →
      D.sourceSituation.IsQuotModule T Q

/-! ### The direct image of quotients is a bijection -/

/-- **The direct image of quotients along a closed immersion is injective**, by full faithfulness
of `π_{T,*}` (Stacks 04CJ). -/
theorem pushforwardQuotient_injective (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (c : PushforwardComparison D) (hπ : IsClosedImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) :
    Function.Injective (D.pushforwardQuotient h c T) :=
  D.pushforwardQuotient_injective_of_fullyFaithful h c T
    (D.fullyFaithfulPushforwardBaseChangeOfMap hπ T)

/-- **Every member of `Quot_{G/Y/B}(T)` is the direct image of a member of
`Quot_{F/X/B}(T)`.**  The quotient of `G_T` by it is a direct image along `π_T` by the first
input, so it is the direct image of a quotient of `F_T`; the four conditions of
Stacks 09TR for that quotient of `F_T` are the second input. -/
theorem exists_pushforwardQuotient_eq (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) (J : D.ClosedImmersionQuotInputs h)
    (hπ : IsClosedImmersion B S hS D.π.hom) (T : SchemesOver D.base)
    (K' : Subobject ((D.targetSituation h).baseChangeModule T))
    (hK' : K' ∈ (D.targetSituation h).properlySupportedQuotients T) :
    ∃ K ∈ D.sourceSituation.properlySupportedQuotients T,
      D.pushforwardQuotient h I.comparison T K = K' := by
  obtain ⟨K, hconj, ⟨ι⟩⟩ := Functor.exists_conjSubobject_eq (I.comparison.iso T)
    (D.fullyFaithfulPushforwardBaseChangeOfMap hπ T) K' (J.essImage_quotientModule T K')
  refine ⟨K, ?_, hconj⟩
  exact (D.sourceSituation.mem_properlySupportedQuotients_iff T K).mpr
    (J.isQuotModule_of_pushforward T (D.sourceSituation.quotientModule T K)
      (QuotSituation.IsQuotModule.of_iso ι.symm
        (((D.targetSituation h).mem_properlySupportedQuotients_iff T K').mp hK')))

/-- The morphism of Quot functors `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` induced by the direct image
along a closed immersion is an isomorphism: over every test scheme it is a bijection, injectively
by full faithfulness of `π_{T,*}` (Stacks 04CJ) and surjectively by the two inputs `J`.  Stacks
0DP4 itself is `isIso_pushforwardQuotFunctorMap_ofIsClosedImmersion`. -/
theorem isIso_quotFunctorMap (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) (J : D.ClosedImmersionQuotInputs h)
    (hπ : IsClosedImmersion B S hS D.π.hom) :
    IsIso (D.quotFunctorMap h I) := by
  have happ : ∀ T, IsIso ((D.quotFunctorMap h I).app T) := by
    intro T
    rw [isIso_iff_bijective]
    constructor
    · intro x y hxy
      refine Subtype.ext (D.pushforwardQuotient_injective h I.comparison hπ T.unop ?_)
      exact congrArg Subtype.val hxy
    · intro y
      obtain ⟨K, hK, hconj⟩ := D.exists_pushforwardQuotient_eq h I J hπ T.unop y.1 y.2
      exact ⟨⟨K, hK⟩, Subtype.ext hconj⟩
  exact NatIso.isIso_of_isIso_app _

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
