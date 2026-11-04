module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import
  StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImageSupplement

/-!
# Further results on `PerfectDirectImage`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectDirectImage` that need imports beyond
those of that module.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section DerivedPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 08EV], the pseudo-coherence half of the conclusion.** Let `S` be a Noetherian
scheme, `f : X ⟶ S` locally of finite type and `E` a bounded object of `D(𝒪_X)` whose cohomology
sheaves are coherent with support proper over `S`. Then `Rf_*E` is a pseudo-coherent object of
`D(𝒪_S)`.

By [Stacks, Tag 08CQ] perfectness is pseudo-coherence together with locally finite Tor
dimension; this is the first of the two, obtained from [Stacks, Tag 08E2] and
[Stacks, Tag 08E8]. -/
@[stacks 08EV "the pseudo-coherence half of the conclusion only: Rf_*E is a pseudo-coherent \
object of D(𝒪_S). Perfectness is pseudo-coherence together with locally finite Tor dimension \
by Tag 08CQ, and the Tor-dimension half is not proved here: it needs the clause (2) implies \
(1) of Tag 08EA and the projection formula of Tag 08EU at a general target complex, neither of \
which is in the tree. Rf_*E is nowhere asserted here to be of locally finite Tor dimension, \
nor to be perfect", sga "6 IV 2.11.1" "partial", sga "6 XIV 2.2" "special case"]
theorem isPseudoCoherent_derivedPushforward_of_isProperOver_supp_unconditional [IsNoetherian S]
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  isPseudoCoherent_of_derivedCategoryBBounded_isCoherent S _
    (derivedCategoryBBounded_derivedPushforward_of_isProperOver_supp_unconditional f E hcoh hsupp
      a b hGE hLE)

/-- **What is left of [Stacks, Tag 08EV] once the Tor-dimension half is granted.** With the
hypotheses of the tag, if `Rf_*E` is locally of finite Tor dimension then it is a perfect object
of `D(𝒪_S)`.

This is the converse implication of [Stacks, Tag 08CQ] applied to the pseudo-coherence proved
above. The hypothesis `htor` is exactly the half of the source's proof that the tree cannot yet
carry out, so no label is attached: the tag asserts perfectness unconditionally. -/
theorem isPerfect_derivedPushforward_of_locallyHasFiniteTorDimension_unconditional [IsNoetherian S]
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b)
    (htor : Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension S.toRingedSpace
      ((derivedPushforwardModules f).obj E)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)
    ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
        (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)).2
      (isPseudoCoherent_derivedPushforward_of_isProperOver_supp_unconditional f E hcoh hsupp a b
        hGE hLE))
    htor

end DerivedPushforward

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
