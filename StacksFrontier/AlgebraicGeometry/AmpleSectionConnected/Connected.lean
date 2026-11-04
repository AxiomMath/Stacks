module

public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.StructureSheafDepth
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.TwistSpellings
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.VanishingToConnected
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Basic
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.H1Vanishing
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison

/-!
# Connectedness of an ample divisor

**[Stacks, Tag 0FD9].** Let `k` be a field, let `X` be a proper scheme over `k`, let `ℒ` be an
ample invertible `𝒪_X`-module and let `s ∈ Γ(X, ℒ)`. Assume

1. `s` is a regular section — multiplication by `s` is a monomorphism `𝒪_X ⟶ ℒ`, which is
   [Stacks, Tag 01WY] and is exactly what `AlgebraicGeometry.IsRegularSection` abbreviates,
2. `depth(𝒪_{X,x}) ≥ 2` for every closed point `x ∈ X`, and
3. `X` is connected.

Then the zero scheme `Z(s)` of `s` ([Stacks, Tag 02OQ]) is connected.

## Main results

* `Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple`: **the tag.**

## The proof, and where each piece lives

The argument is the source's, split across this directory.
`connectedSpace_zeroScheme_of_isZero_negative_twists` (`VanishingToConnected.lean`) is everything
except the two vanishing theorems: it chooses `n ≥ 1` below both vanishing bounds, replaces `s` by
`s^n` — still regular, and with a homeomorphic zero scheme — reads the ideal sequence of `Z(s^n)`,
whose first term is `ℒ^{⊗ -n}`, through the long exact cohomology sequence to make `Γ(X, 𝒪_X) →
Γ(Z(s^n), 𝒪)` bijective, and concludes by the idempotent dichotomy. Hypotheses (1) and (3) are
consumed there.

All that is added here is hypothesis (2) and the two vanishing theorems it feeds, both applied at
`ℱ = 𝒪_X`:

* [Stacks, Tag 0FD7] gives `Γ(X, 𝒪_X ⊗ ℒ^{⊗ n}) = 0` for `n ≪ 0`, its hypothesis "no closed
  associated point" supplied by `notMem_associatedPoints_unit_of_two_le_depth`;
* [Stacks, Tag 0FD8] gives `H¹(X, 𝒪_X ⊗ ℒ^{⊗ m}) = 0` for `m ≪ 0`, its depth hypothesis — stated
  at the module stalk — supplied by `two_le_depth_stalk_unit_of_two_le_depth`.

Both are taken at the twisted-graded-module spelling of the twist, and
`twistedGradedUnitIso` (`TwistSpellings.lean`) identifies that twist of `𝒪_X` with `ℒ^{⊗ m}`.

## Implementation notes

Nothing in the statement is an added hypothesis. Ampleness is written over the tensor powers
`AlgebraicGeometry.Scheme.Modules.IsAmple` is stated for, and
`Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple` carries it to the predicate Tags 0FD7 and
0FD8 ask for; the invertibility predicate they need is produced from the one in the binder by
`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry`; and coherence of `𝒪_X` is
`Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit`, from properness over the field. The
depth condition is the source's, on the local ring at each closed point along its maximal ideal,
not on a module stalk — the translation is `depth_stalk_unit_eq`.

The two vanishing theorems conclude in `AlgebraicGeometry.cohomologyOverField`, the `k`-vector
space; `AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup` moves that to the
`Hgroup` form the long exact sequence is stated over.

## References

* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AmpleSectionConnected

/-- **[Stacks, Tag 0FD9].** Let `k` be a field, let `X` be a proper scheme over `k`, let `ℒ` be
an ample invertible `𝒪_X`-module and let `s ∈ Γ(X, ℒ)`. If `s` is a regular section
([Stacks, Tag 01WY]), if `depth(𝒪_{X,x}) ≥ 2` for every closed point `x ∈ X`, and if `X` is
connected, then the zero scheme `Z(s)` is connected. -/
@[stacks 0FD9]
theorem connectedSpace_zeroScheme_of_isAmple (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [inst : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) (s : L.sections)
    (hs : Mono (L.unitHomEquiv.symm s))
    (hdepth : ∀ x : X, IsClosed ({x} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    [ConnectedSpace X] :
    ConnectedSpace (zeroScheme X L (s.eval (op ⊤))).subscheme := by
  let : Stacks.Ample.IsInvertibleModule X L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inst
  have hL' : Stacks.Ample.IsAmple X L :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).1 hL
  have : (Stacks.Ample.unitModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  obtain ⟨n₀, hn₀⟩ :=
    EnriquesSeveriZariski.exists_forall_le_isZero_cohomologyOverField_zero_twistedGradedModuleTwist
      L k f hL' (Stacks.Ample.unitModule X)
      (notMem_associatedPoints_unit_of_two_le_depth X hdepth)
  obtain ⟨m₀, hm₀⟩ :=
    EnriquesSeveriZariski.exists_forall_le_isZero_cohomologyOverField_one_twistedGradedModuleTwist
      k f L hL' (Stacks.Ample.unitModule X)
      (two_le_depth_stalk_unit_of_two_le_depth X hdepth)
  refine connectedSpace_zeroScheme_of_isZero_negative_twists L s hs
    ⟨n₀, fun m hm => ?_⟩ ⟨m₀, fun m hm => ?_⟩
  · exact (isZero_secF_of_isZero_hgroup_zero X ⊤ _
      ((isZero_cohomologyOverField_iff_isZero_hgroup k f _ 0).1 (hn₀ m hm))).of_iso
      (((secF X.ringCatSheaf ⊤).mapIso (twistedGradedUnitIso X L m)).symm)
  · exact ((isZero_cohomologyOverField_iff_isZero_hgroup k f _ 1).1 (hm₀ m hm)).of_iso
      (((Hfunctor X.ringCatSheaf ⊤ 1).mapIso (twistedGradedUnitIso X L m)).symm)

end Stacks.AmpleSectionConnected

end
