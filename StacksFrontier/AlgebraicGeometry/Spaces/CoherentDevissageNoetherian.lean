module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIrreducibleIdealInjection

/-!
# The higher-rank dévissage principle on a Noetherian algebraic space, unconditionally

Stacks 08AN: on a Noetherian algebraic space `X`, a property `P` of coherent `𝒪_X`-modules which
satisfies two-out-of-three on short exact sequences, descends from a finite direct sum of `r ≥ 1`
copies of a module to the module, and holds for some coherent module with scheme-theoretic
support `Z` for every reduced closed subspace `Z ⊆ X` with `|Z|` irreducible, holds for every
coherent module.

`StacksFrontier/AlgebraicGeometry/Spaces/CoherentDevissageHigherRank.lean` carries out the
Noetherian induction of the source, from three statements of other tags taken as hypotheses:
the conclusion of Stacks 07UR, the coherence of the direct image of a quasi-coherent sheaf of
ideals along the inclusion of a closed subspace, and the two inputs of Stacks 07UQ.  All three
are now theorems of this library, the last one in the stronger form of Stacks 07UQ itself:

* Stacks 07UR is `AlgebraicGeometry.Space.hasIdealDevissage_of_isCoherent`;
* the direct image `i_*I` is coherent by
  `AlgebraicGeometry.Space.isCoherent_modulePushforward_quasicoherentIdeal`, a quasi-coherent
  submodule of the coherent `i_*𝒪_Z`;
* Stacks 07UQ is
  `AlgebraicGeometry.Space.exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport`,
  and `AlgebraicGeometry.Space.existsIdealInjectionDevissageStep_of_isNoetherian` (in
  `StacksFrontier/AlgebraicGeometry/Spaces/CoherentDevissageUnconditional.lean`) puts it in the
  shape
  `AlgebraicGeometry.Space.ExistsIdealInjectionDevissageStep` that the step at a minimal subspace
  consumes.

The step at a minimal subspace and the Noetherian induction with that shape as their input,
`AlgebraicGeometry.Space.forall_property_idealPushforward_of_coherentWitness`, are in the same
file, and Stacks 08AN follows with no hypothesis beyond the source's.

## Main results

* `AlgebraicGeometry.Space.property_of_coherent_of_isNoetherian`: the dévissage of Stacks 08AN
  for a property holding on zero modules.  Stacks 08AN itself, with the errata's correction,
  is registered at `AlgebraicGeometry.Space.property_of_isCoherent_of_integralWitness`.

## Implementation notes

**The zero module.**  The hypothesis `hzero`, that `P` holds for zero modules, is a correction
of the source and cannot be dropped: on an algebraic space with no points the property
`fun _ => False` satisfies the three conditions of the source vacuously — there is no closed
subspace with irreducible space of points — while the zero module is coherent.  On a space with a
point it is a consequence of the three conditions (the witness `G` on an irreducible component
and the exact sequence `0 → G → G → 0 → 0`), so nothing is lost there.  This is the same
correction as the one recorded at Stacks 07US.

## References

* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 07UR](https://stacks.math.columbia.edu/tag/07UR)
* [Stacks Project, Tag 07US](https://stacks.math.columbia.edu/tag/07US)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 08AN -/

/-- **The dévissage of Stacks 08AN for a property holding on zero modules.**  Let `X` be a
Noetherian algebraic space over a scheme `S` and let `P` be a property of coherent
`𝒪_X`-modules such that

1. for a short exact sequence of coherent modules, if two out of three terms have `P` then so
   does the third;
2. if `P` holds for the direct sum of `r ≥ 1` copies of a coherent module then it holds for that
   module;
3. for every reduced closed subspace `Z ⊆ X` with `|Z|` irreducible there is a coherent module
   on `X` whose scheme-theoretic support is `Z` and which has `P`.

Then `P` holds for every coherent module on `X`.

The hypothesis `hzero`, that `P` holds for zero modules, corrects the source, whose statement
fails on an algebraic space with no points; see the module documentation.  Condition (2) is asked
only of coherent modules, as in the source, where `P` is a property of coherent sheaves; the proof
runs the dévissage for the property `M ↦ (M coherent → P M)`, for which condition (2) holds at
every module.  The three inputs that
`AlgebraicGeometry.Space.property_of_integralWitness_and_twoOutOfThree` carries are discharged:
Stacks 07UR by `AlgebraicGeometry.Space.hasIdealDevissage_of_isCoherent`, coherence of `i_*I` by
`AlgebraicGeometry.Space.isCoherent_modulePushforward_quasicoherentIdeal`, and Stacks 07UQ by
`AlgebraicGeometry.Space.existsIdealInjectionDevissageStep_of_isNoetherian`. -/
theorem property_of_coherent_of_isNoetherian (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (h1 : TwoOutOfThreeCoherent B S hS X P)
    (h2 : ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F → ∀ r : ℕ, 1 ≤ r →
      P (⨁ fun _ : Fin r => F) → P F)
    (h3 : HasCoherentWitnessOnIntegralSubspaces B S hS X P)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) : P M := by
  let P' : Modules.{u, u} B S hS X.1 X.2 → Prop := fun N => IsCoherent B S hS X.1 X.2 N → P N
  have hdev : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N →
      HasIdealDevissage B S hS X N :=
    hasIdealDevissage_of_isCoherent B S hS hZtop X hX
  have h07UH : IdealPushforwardCoherent B S hS X := fun Z hZ I =>
    isCoherent_modulePushforward_quasicoherentIdeal B S hS hX.2.2 (closedSubfunctorι B S hS hZ)
      hZ.2 I
  have h1' : TwoOutOfThreeCoherent B S hS X P' := fun E hE c₁ c₂ c₃ =>
    let ⟨t₁, t₂, t₃⟩ := h1 E hE c₁ c₂ c₃
    ⟨fun a b _ => t₁ (a c₁) (b c₃), fun a b _ => t₂ (a c₂) (b c₃),
      fun a b _ => t₃ (a c₁) (b c₂)⟩
  have h2' : ClosedUnderDirectSumDescent B S hS X P' := fun F r hr hP hF =>
    h2 F hF r hr (hP (isCoherent_biproductConst B S hS X.1 X.2 F hF r))
  have h3' : HasCoherentWitnessOnIntegralSubspaces B S hS X P' := fun Z hZ hint => by
    obtain ⟨G, hG, hsupp, hP⟩ := h3 Z hZ hint
    exact ⟨G, hG, hsupp, fun _ => hP⟩
  have hzero' : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsZero N → P' N := fun N hN _ => hzero N hN
  exact property_of_forall_hasIdealDevissage B S hS X hdev P' hzero'
    (closedUnderCoherentExtensions_of_twoOutOfThreeCoherent B S hS X P' h1')
    (fun Z hZ hint I =>
      forall_property_idealPushforward_of_coherentWitness B S hS hZtop X hX hdev h07UH
        (existsIdealInjectionDevissageStep_of_isNoetherian B S hS hZtop X hX) P' hzero'
        h1' h2' h3' Z hZ hint I)
    M hM hM

end AlgebraicGeometry.Space

end
