module

public import StacksFrontier.RingTheory.Depth.Defs
public import StacksFrontier.RingTheory.Depth.UnqualifiedDepth
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.LocalCohomology.HartshorneConnectedness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hartshorne connectedness for a henselization and a strict henselization

Let `A` be a Noetherian local ring whose depth is at least two. Then the punctured spectra of a
henselization `A^h` and of a strict henselization `A^{sh}` of `A` are connected.

Both assertions reduce to the case of `A` itself. A henselization `A^h` is again a Noetherian
local ring, and depth is unchanged along `A → A^h` and `A → A^{sh}`: the henselizations are flat
local `A`-algebras with `𝔪 A^h = 𝔪_{A^h}`, so the fibre contributes nothing to the depth
formula for a flat local homomorphism. Hartshorne's lemma for the Noetherian local ring `A^h`
(resp. `A^{sh}`) of depth at least two then gives the conclusion directly.

## Main results

* `Stacks.PuncturedSpectrum.isConnected_puncturedSpectrum_henselization_of_two_le_depth` — the
  punctured spectrum of a henselization of a Noetherian local ring of depth at least two is
  connected.
* `Stacks.PuncturedSpectrum.isConnected_puncturedSpectrum_strictHenselization_of_two_le_depth` —
  the same for a strict henselization.

## Implementation notes

The two clauses are stated *hypothetically*: the henselization is an abstract ring `A^h` carrying
`IsLocalRing.IsHenselization A (ResidueField A) A^h`, and likewise the strict henselization
carries `IsLocalRing.IsHenselization A κsep A^{sh}` for a separable closure `κsep` of the residue
field. This is the shape used by the depth, dimension and Cohen–Macaulay transfer results of
`StacksFrontier/RingTheory/Henselian/PermanenceOfProperties.lean`, so the statements compose with
them without a comparison isomorphism, and they apply to whichever model of the henselization a
caller has at hand rather than to a chosen one. The existence form would have to name a
henselization produced by `IsLocalRing.exists_henselization`, which is weaker (it is the special
case of the hypothetical form applied to that ring) and makes the statement depend on a choice.
Inside the proofs the *companion* henselization that the transfer results require as a second
argument is obtained from `IsLocalRing.exists_isHenselization_residueField` and
`IsLocalRing.exists_isHenselization_separableClosure` by `Exists.elim` into the `Prop`-valued
goal, so no ring is chosen.

The depth hypothesis is `Module.depth A (maximalIdeal A) A`, the depth of Stacks 00LI, matching
the statement for `A` itself. The transfer result for depth, Stacks 06LL, is stated for
`ringDepth`; the identification of the two is `ringDepth_eq_depth_maximalIdeal`, which lives in
`StacksFrontier/RingTheory/Depth/UnqualifiedDepth.lean`, upstream of every ring that needs it.

## References

* [Stacks Project, Tag 0BLR](https://stacks.math.columbia.edu/tag/0BLR)
* [Stacks Project, Tag 06LL](https://stacks.math.columbia.edu/tag/06LL), the depth of a
  henselization
* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ), Noetherianness of a
  henselization
* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI), depth
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Stacks.PuncturedSpectrum

/-- Hartshorne's lemma transported along an equality of ring depths: a Noetherian local ring
whose depth equals that of a local ring of depth at least two has connected punctured
spectrum. -/
@[ega "IV 5.10.7" "special case"]
private theorem isConnected_compl_closedPoint_of_ringDepth_eq
    (A S : Type u) [CommRing A] [IsLocalRing A]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (hringDepth : ringDepth A = ringDepth S) :
    IsConnected ({closedPoint S}ᶜ : Set (PrimeSpectrum S)) :=
  isConnected_puncturedSpectrum_of_two_le_depth S <| by
    rw [← ringDepth_eq_depth_maximalIdeal, ← hringDepth, ringDepth_eq_depth_maximalIdeal]
    exact hdepth

/-- **Stacks Project, Tag 0BLR (second assertion).** The punctured spectrum of a henselization of
a Noetherian local ring of depth at least two is connected. -/
@[stacks 0BLR "the punctured spectrum of `A^h`"]
theorem isConnected_puncturedSpectrum_henselization_of_two_le_depth
    (A Ah : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A) :
    IsConnected ({closedPoint Ah}ᶜ : Set (PrimeSpectrum Ah)) := by
  obtain ⟨Ash, _, _, _, _⟩ := IsLocalRing.exists_isHenselization_separableClosure A
  have : IsNoetherianRing Ah :=
    (isNoetherianRing_iff_henselizations A Ah Ash
      (SeparableClosure (ResidueField A))).1.mp inferInstance
  exact isConnected_compl_closedPoint_of_ringDepth_eq A Ah hdepth
    (ringDepth_eq_henselization_eq_strictHenselization A Ah Ash
      (SeparableClosure (ResidueField A))).1

/-- **Stacks Project, Tag 0BLR (third assertion).** The punctured spectrum of a strict
henselization of a Noetherian local ring of depth at least two is connected. -/
@[stacks 0BLR "the punctured spectrum of `A^sh`"]
theorem isConnected_puncturedSpectrum_strictHenselization_of_two_le_depth
    (A Ash : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep] [IsHenselization A κsep Ash]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A) :
    IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)) := by
  obtain ⟨Ah, _, _, _, _⟩ := IsLocalRing.exists_isHenselization_residueField A
  have : IsNoetherianRing Ash :=
    (isNoetherianRing_iff_henselizations A Ah Ash κsep).2.mp inferInstance
  obtain ⟨hAh, hAsh⟩ := ringDepth_eq_henselization_eq_strictHenselization A Ah Ash κsep
  exact isConnected_compl_closedPoint_of_ringDepth_eq A Ash hdepth (hAh.trans hAsh)

end Stacks.PuncturedSpectrum

end
