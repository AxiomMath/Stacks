module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowDerivedDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived direct image of a bounded below coherent complex with proper support

Let `S` be a Noetherian scheme, let `f : X ⟶ S` be a morphism locally of finite type and let `E`
be an object of `D^+_Coh(𝒪_X)` such that the support of every `H^i(E)` is proper over `S`. Then
`Rf_*E` is an object of `D^+_Coh(𝒪_S)`. This is [Stacks, Tag 0D0B], with no hypothesis.

`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/BoundedBelowDerivedDirectImage.lean` runs
the source's argument — apply `Rf_*` to the truncation triangle at each degree, use left
`t`-exactness to kill the third vertex and read off `H^n(Rf_*E) ≅ H^n(Rf_*τ_{≤n}E)`, then the
dévissage of [Stacks, Tag 08E2] on the bounded complex `τ_{≤n}E` — leaving [Stacks, Tag 02O5] as
the single hypothesis `haff`, in the named form
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`. That
hypothesis is a theorem:
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase` asserts
exactly the coherence of the higher direct images of a coherent module along a proper morphism to
an affine locally Noetherian base, with no hypothesis of its own. This file composes the two.

## Main results

* `derivedCategoryBPlus_derivedPushforward_of_properSupp`, in the namespace
  `Stacks.AlgebraicGeometry.ProperSupportCoherent`: **[Stacks, Tag 0D0B]**, with no hypothesis.
* `derivedCategoryBPlus_derivedPushforward_of_properSupp_of_isGE`, in the same namespace: the
  same with the lower bound of `E` given explicitly, which is the form a caller that already has
  a bound wants.

## Implementation notes

The discharge happens in a module of its own, as it does for [Stacks, Tag 08DS] in
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/Unconditional.lean`, because
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase` is proved by
dévissage over Chow's lemma, a development independent of the truncation argument above. The
import cone of Chow's lemma contributes a competing `CategoryTheory.HasDerivedCategory` instance,
so the precedence of the standard model is raised here, exactly as it is there, to keep the
statements below in the same derived category as the ones they consume.

## References

* [Stacks Project, Tag 0D0B](https://stacks.math.columbia.edu/tag/0D0B)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 0D0B] with the lower bound of `E` named.** For `S` Noetherian, `f` locally of
finite type and `E` an object of `D(𝒪_X)` lying in degrees `≥ b` whose cohomology sheaves are
coherent with support proper over `S`, the object `Rf_*E` of `D(𝒪_S)` is bounded below with
coherent cohomology sheaves.

This is `derivedCategoryBPlus_derivedPushforward_of_isGE` with its appeal to [Stacks, Tag 02O5]
supplied by `AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`,
a theorem. -/
@[ega "III 3.2.4" "special case", sga "6 III 2.2.1" "first assertion"]
theorem derivedCategoryBPlus_derivedPushforward_of_properSupp_of_isGE [IsNoetherian S]
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (b : ℤ) (hGE : E.IsGE b) :
    DerivedCategoryB.derivedCategoryBPlus (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) :=
  derivedCategoryBPlus_derivedPushforward_of_isGE f E hcoh hsupp
    _root_.AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase b hGE

/-- **[Stacks, Tag 0D0B].** Let `S` be a Noetherian scheme, let `f : X ⟶ S` be a morphism of
schemes which is locally of finite type and let `E` be an object of `D^+_Coh(𝒪_X)` such that the
support of `H^i(E)` is proper over `S` for all `i`. Then `Rf_*E` is an object of `D^+_Coh(𝒪_S)`.

This is `derivedCategoryBPlus_derivedPushforward_of_isProperOver_supp` with its appeal to
[Stacks, Tag 02O5] supplied by
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`, a
theorem. -/
@[stacks 0D0B,
  ega "III 3.2.1" "Noetherian target",
  ega "III 3.2.4" "special case",
  ega "III 4.1.10" "more general"]
theorem derivedCategoryBPlus_derivedPushforward_of_properSupp [IsNoetherian S]
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hE : DerivedCategoryB.derivedCategoryBPlus (fun M : X.Modules => M.IsCoherent) E)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hE.2 j).isFiniteType⟩) :
    DerivedCategoryB.derivedCategoryBPlus (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) :=
  derivedCategoryBPlus_derivedPushforward_of_isProperOver_supp f E hE hsupp
    _root_.AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
