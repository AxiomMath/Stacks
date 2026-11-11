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

/-- **The pseudo-coherence half of the conclusion of [Stacks, Tag 08EV].** Let `S` be a
Noetherian scheme, `f : X ⟶ S` locally of finite type and `E` a bounded object of `D(𝒪_X)` whose
cohomology sheaves are coherent with support proper over `S`. Then `Rf_*E` is a pseudo-coherent
object of `D(𝒪_S)`.

By [Stacks, Tag 08CQ] perfectness is pseudo-coherence together with locally finite Tor
dimension; this is the first of the two, obtained from [Stacks, Tag 08E2] and
[Stacks, Tag 08E8]. It is a step of the proof of the tag, not the tag: [Stacks, Tag 08EV] itself
is
`Stacks.AlgebraicGeometry.ProperSupportCoherent.isPerfect_derivedPushforward_of_isProperOver_supp`,
whose proof establishes this half as well. -/
@[sga "6 IV 2.11.1" "partial", sga "6 XIV 2.2" "special case"]
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

/-- **Perfectness of `Rf_*E` from its locally finite Tor dimension.** With the boundedness,
coherence and proper-support hypotheses of [Stacks, Tag 08EV], if `Rf_*E` is locally of finite
Tor dimension then it is a perfect object of `D(𝒪_S)`.

This is the converse implication of [Stacks, Tag 08CQ] applied to the pseudo-coherence proved
above. The hypothesis `htor` is the other half of the source's proof; it is proved from the
Tor-dimension clause of the tag as
`AlgebraicGeometry.locallyHasFiniteTorDimension_derivedPushforward_of_isProperOver`, and the tag
itself is
`Stacks.AlgebraicGeometry.ProperSupportCoherent.isPerfect_derivedPushforward_of_isProperOver_supp`.
No label is attached here. -/
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
