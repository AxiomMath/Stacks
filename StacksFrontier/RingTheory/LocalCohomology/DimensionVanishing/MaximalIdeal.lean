module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimensionBounds
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local cohomology at the closed point vanishes above the dimension

Let `(B, m)` be a Noetherian local ring of dimension at most `n` and let `J ⊆ B` be an ideal
cutting out the closed point, that is with `V(J) = V(m) = {m}`. Then `H^i_{V(J)}(M) = 0` for
every `B`-module `M` and every `i > n`.

This is Grothendieck's vanishing theorem in the shape in which the local ring contributes to
Hartshorne–Lichtenbaum vanishing, and it is proved here from Krull's height theorem rather than
from any cohomological input: the maximal ideal of a Noetherian local ring has a system of
parameters, so `{m}` is cut out by `height m ≤ n` equations, and local cohomology supported on a
closed subset cut out by `r` equations vanishes above degree `r` for a module placed in degree
zero. The hypothesis is on the zero locus and not on `J` itself because the subcategory of
`D(B)` whose cohomology is `J`-power torsion depends only on `V(J)`.

## Main results

* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_zeroLocus_eq_maximalIdeal` — the
  vanishing above the dimension, for every module.

## Implementation notes

No `@[stacks]` attribute is placed. The vanishing of Stacks 0DXC is `H^i_{V(I)}(M) = 0` for
`i > dim(Supp M)` for an arbitrary finitely generated ideal `I` of an arbitrary ring, together
with the bound `cd(A, I) ≤ dim(A)`; what is proved here is the special case of a local ring and
an ideal cutting out its closed point, so it is one input to that tag and not any clause of it.
The reduction of the general case to this one is the part that is still missing, and the module
docstring of `StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing` names what it needs.

The dimension enters as a natural-number bound on `ringKrullDim B` rather than as the height of
the maximal ideal, since that is the form the Krull dimension of a localization is available in.

## References

* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
* [Stacks Project, Tag 0DX9](https://stacks.math.columbia.edu/tag/0DX9)
* [Stacks Project, Tag 00KQ](https://stacks.math.columbia.edu/tag/00KQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- **Grothendieck vanishing at the closed point.** Let `(B, m)` be a Noetherian local ring with
`dim B ≤ n` and let `J` be an ideal with the same zero locus as `m`. Then the local cohomology of
any `B`-module supported on `V(J)` vanishes in every degree above `n`.

Krull's height theorem provides `height m` elements of `B` whose zero locus is `{m}`, and the
cohomological dimension of a closed subset cut out by `r` equations is at most `r`. -/
@[sga "2 V 3.1" "(i), special case"]
theorem isZero_localCohomologyModule_of_zeroLocus_eq_maximalIdeal
    (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (J : Ideal B) (hJ : J.FG)
    (hJm : PrimeSpectrum.zeroLocus (J : Set B) =
      PrimeSpectrum.zeroLocus ((maximalIdeal B : Ideal B) : Set B))
    {n : ℕ} (hn : ringKrullDim B ≤ (n : WithBot ℕ∞))
    (M : ModuleCat.{u} B) (i : ℤ) (hi : (n : ℤ) < i) :
    IsZero (localCohomologyModule B J hJ M i) := by
  classical
  obtain ⟨s, hmin, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal B)
  -- In a local ring the maximal ideal is the only prime containing `span s`.
  have hzl : PrimeSpectrum.zeroLocus ((Ideal.span (s : Set B) : Ideal B) : Set B) =
      PrimeSpectrum.zeroLocus ((maximalIdeal B : Ideal B) : Set B) := by
    refine le_antisymm (fun q hq => ?_) (PrimeSpectrum.zeroLocus_anti_mono ?_)
    · have hqs : Ideal.span (s : Set B) ≤ q.asIdeal :=
        Ideal.span_le.mpr (by simpa [PrimeSpectrum.mem_zeroLocus] using hq)
      have hqm : q.asIdeal ≤ maximalIdeal B := le_maximalIdeal q.isPrime.ne_top
      simpa [PrimeSpectrum.mem_zeroLocus] using hmin.2 ⟨q.isPrime, hqs⟩ hqm
    · simpa using hmin.1.2
  -- `height m ≤ dim B ≤ n`, so there are at most `n` equations.
  have hcard' : (s.card : ℤ) ≤ (n : ℤ) := by
    have hle : ((maximalIdeal B).height : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
      le_trans (Ideal.height_le_ringKrullDim_of_isPrime) hn
    have : (maximalIdeal B).height ≤ (n : ℕ∞) := by exact_mod_cast hle
    have : (s.card : ℕ∞) ≤ (n : ℕ∞) := hcard ▸ this
    exact_mod_cast this
  exact isZero_homology_localCohomologyFunctor_of_zeroLocus_eq.{u, u} J hJ
    (Ideal.span (s : Set B)) ⟨s, rfl⟩ (hJm.trans hzl.symm) s rfl _ 0
    (fun j hj => isZero_homology_singleFunctor_obj _ j (by omega)) i (by omega)

end Stacks.LocalCohomology

end
