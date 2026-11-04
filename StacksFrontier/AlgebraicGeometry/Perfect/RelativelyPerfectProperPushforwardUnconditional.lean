module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedBelowCompact
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TorDimensionDirectImage
public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Further results

Results complementing `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforward`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProperSupportCoherent

universe u

namespace Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S)

section Certificates

variable [Flat f] [LocallyOfFinitePresentation f]

end Certificates

section ProperSupport

end ProperSupport

section Hypotheses

variable [IsNoetherian S] [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

omit [AlgebraicGeometry.IsNoetherian S] [IsProper f] in
/-- **An `S`-perfect object has quasi-coherent cohomology sheaves**, being pseudo-coherent
([Stacks, Tag 08E5], `AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`). -/
theorem isQuasicoherent_homology_of_isPerfectRelativeTo (D : TensorFamily f)
    (E : DerivedCategory X.Modules) (hE : f.IsPerfectRelativeTo D E) (j : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X E hE.1 j

/-- **What [Stacks, Tag 08EV] asks of its source complex, for an `S`-perfect complex.** Let `S` be
a Noetherian scheme, let `f : X ⟶ S` be proper, flat and locally of finite presentation and let
`E` be an `S`-perfect object of `D(𝒪_X)`. Then the cohomology sheaves of `E` are coherent and `E`
is bounded.

`X` is Noetherian, being quasi-compact and locally of finite type over a Noetherian scheme.
Coherence and the bound above are then [Stacks, Tag 08E8] applied to the pseudo-coherence clause
of relative perfectness, and the bound below comes from the Tor clause through
`AlgebraicGeometry.exists_isGE_of_isPerfectRelativeTo`. -/
theorem isCoherent_homology_and_bounds_of_isPerfectRelativeTo_unconditional (D : TensorFamily f)
    (hD : IsGenuineTensorFamily f D) (E : DerivedCategory X.Modules)
    (hE : f.IsPerfectRelativeTo D E) :
    (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent) ∧
      ∃ a b : ℤ, E.IsGE a ∧ E.IsLE b := by
  have hXnoeth : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨⟨b, hb⟩, hcoh⟩ :=
    (AlgebraicGeometry.isPseudoCoherent_iff_boundedAbove_coherent_homology X
      ⟨E, isQuasicoherent_homology_of_isPerfectRelativeTo f D E hE⟩).1 hE.1
  obtain ⟨a, hGE⟩ := AlgebraicGeometry.exists_isGE_of_isPerfectRelativeTo f D hD E hE
  exact ⟨hcoh, a, b, hGE, (DerivedCategory.isLE_iff E b).2 fun j hj => hb j hj⟩

/-- **The pseudo-coherence half of the conclusion of [Stacks, Tag 0DJT].** Let `S` be a Noetherian
scheme, let `f : X ⟶ S` be proper, flat and locally of finite presentation and let `E` be an
`S`-perfect object of `D(𝒪_X)`. Then `Rf_*E` is a pseudo-coherent object of `D(𝒪_S)`.

By [Stacks, Tag 08CQ] perfectness is pseudo-coherence together with locally finite Tor dimension;
this is the first of the two. Everything the pseudo-coherence half of [Stacks, Tag 08EV] asks of
`E` is supplied by `isCoherent_homology_and_bounds_of_isPerfectRelativeTo_unconditional`, and its
support hypothesis by `isProperOver_of_isProper`, and [Stacks, Tag 02O5] by
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`. -/
@[sga "6 0 3.1" "partial",
  sga "6 III 2.1" "special case",
  sga "6 III 4.8" "(a)",
  sga "6 XIV 2.2" "special case"]
theorem isPseudoCoherent_derivedPushforward_of_isPerfectRelativeTo_unconditional
    (D : TensorFamily f) (hD : IsGenuineTensorFamily f D) (E : DerivedCategory X.Modules)
    (hE : f.IsPerfectRelativeTo D E) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) := by
  obtain ⟨hcoh, a, b, hGE, hLE⟩ :=
    isCoherent_homology_and_bounds_of_isPerfectRelativeTo_unconditional f D hD E hE
  exact isPseudoCoherent_derivedPushforward_of_isProperOver_supp f E hcoh
    (fun _ => isProperOver_of_isProper f _)
    _root_.AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase
    a b hGE hLE

end Hypotheses

end Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

end
