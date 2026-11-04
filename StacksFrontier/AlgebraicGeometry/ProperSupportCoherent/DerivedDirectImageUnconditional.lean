module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived direct image of a bounded coherent complex with proper support, unconditionally

Let `S` be a Noetherian scheme, let `f : X ⟶ S` be a morphism locally of finite type and let `E`
be an object of `D^b_Coh(𝒪_X)` such that the support of every `H^i(E)` is proper over `S`. Then
`Rf_*E` is an object of `D^b_Coh(𝒪_S)`. This is [Stacks, Tag 08E2], with no hypothesis.

`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/DerivedDirectImage.lean` carries out the
dévissage along the canonical truncation triangles of `E`, leaving [Stacks, Tag 02O5] as the
single hypothesis `haff`, in the named form
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`. That
hypothesis is already a theorem:
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase` asserts the
coherence of the higher direct images of a coherent module along a proper morphism over an affine
base, with no hypothesis of its own. This file supplies it to the dévissage.

## Main results

* `derivedCategoryBBounded_derivedPushforward_of_properSupp`:
  **[Stacks, Tag 08E2]** — `Rf_*E` is an object of `D^b_Coh(𝒪_S)`.

## Implementation notes

The discharge happens in a module of its own because
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent` is proved by dévissage
over Chow's lemma, a development independent of the truncation dévissage above, and the statement
of that dévissage is consumed with `haff` still open by
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/PerfectDirectImage.lean` and
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/BoundedBelowDerivedDirectImage.lean`. This
is the arrangement of
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/Unconditional.lean`, which discharges the
same hypothesis in [Stacks, Tag 08DS].

The statements below spell out `Rf_*E` and `D^b_Coh`, so they have to be elaborated at the same
derived category as the dévissage, namely `CategoryTheory.HasDerivedCategory.standard`. The
import cone of Chow's lemma contributes a competing `HasDerivedCategory` instance, so the
precedence is raised here, as it is in
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/Unconditional.lean`.

## References

* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 08DS](https://stacks.math.columbia.edu/tag/08DS)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **[Stacks, Tag 08E2].** Let `S` be a Noetherian scheme, let `f : X ⟶ S` be locally of finite
type and let `E` be a bounded object of `D(𝒪_X)` whose cohomology sheaves are coherent with
support proper over `S`. Then `Rf_*E` is an object of `D^b_Coh(𝒪_S)`.

The dévissage `derivedCategoryBBounded_derivedPushforward_of_isProperOver_supp` asks for
[Stacks, Tag 02O5] in the affine-base form
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`, which
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase` supplies. -/
@[stacks 08E2,
  ega "III 3.2.1" "Noetherian target",
  ega "III 3.2.4" "special case",
  ega "III 4.1.10" "more general", sga "6 0 3.1" "partial", sga "6 III 2.2.1" "special case"]
theorem derivedCategoryBBounded_derivedPushforward_of_properSupp {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) :=
  derivedCategoryBBounded_derivedPushforward_of_isProperOver_supp f E hcoh hsupp
    _root_.AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase
    a b hGE hLE

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
