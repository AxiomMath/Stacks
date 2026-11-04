module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedDirectSums
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwistDivisor
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twist short exact sequence of a blowup

Let `R` be a commutative ring, `I ⊆ R` an ideal and `X = Proj (⨁ₙ Iⁿ)` the blowup of `Spec R` in
`I`, with exceptional divisor `E` and inclusion `i : E ⟶ X`. This file proves that

`0 ⟶ 𝒪_X(n + 1) ⟶ 𝒪_X(n) ⟶ i_* i^* 𝒪_X(n) ⟶ 0`

is short exact for every `n : ℤ`. This is the sequence the proofs of parts (4) and (5) of
[Stacks, Tag 0AGS] run their descending induction along; there it is written
`0 → 𝒪_X(n) → 𝒪_X(n-1) → i_*𝒪_E(n-1) → 0`, which is the shape
`Stacks.Blowup.shortExact_twist_exceptional` below at `(m, n) = (n, n - 1)`.

## The two inputs

The sequence is the twisted sequence of [Stacks, Tag 0C6K] at the exceptional divisor,
`Stacks.Divisors.isShortExactTwistSequence_canonicalSections`, whose middle term is
`𝒪_X(n+1) ⊗ 𝒪_X(E)`. What identifies that with `𝒪_X(n)` is the composite of the two facts the
source quotes as `𝒪_X(-E) = 𝒪_X(1)`:

* `Stacks.Blowup.twistOneIsoExceptionalIdealSheafOfIdealTop`, part (3) of [Stacks, Tag 02OS] for
  the affine blowup: the twist `𝒪_X(1)` is the ideal sheaf `ℐ_E`;
* `Stacks.AlgebraicGeometry.ProjTwistPowers.twistMulIso`, the multiplication
  `𝒪_X(n) ⊗ 𝒪_X(1) ≅ 𝒪_X(n + 1)`, available because the Rees algebra is generated in degree one
  (`Stacks.Blowup.adjoin_reesGradingZero_reesGrading_one_eq_top`).

Neither is used in the direction of a duality computation: `𝒪_X(n+1) ⊗ 𝒪_X(E) ≅ 𝒪_X(n)` is
obtained by tensoring both sides with `𝒪_X(1)`, where the evaluation pairing
`𝒪_X(E) ⊗ ℐ_E ≅ 𝒪_X` (`Stacks.Divisors.invertibleSheafPairing`) collapses the left-hand side to
`𝒪_X(n+1)` and the multiplication collapses the right-hand side to the same, and then taking the
preimage of the resulting isomorphism under the equivalence `- ⊗ 𝒪_X(1)`.

## Main definitions

* `Stacks.Blowup.exceptionalIdealData`: the exceptional divisor of the affine blowup, the inverse
  image of the centre, as a quasi-coherent sheaf of ideals on `X`.
* `Stacks.Blowup.twistTensorDivisorSheafIso`: **`𝒪_X(n + 1) ⊗ 𝒪_X(E) ≅ 𝒪_X(n)`.**

## Main results

* `Stacks.Blowup.shortExact_twist_exceptional`: **the twist short exact sequence**
  `0 ⟶ 𝒪_X(n+1) ⟶ 𝒪_X(n) ⟶ i_* i^* 𝒪_X(n) ⟶ 0`, with `i` the inclusion of the exceptional
  divisor. The upper degree is carried as a variable `m` with `m = n + 1`, so that the sequence
  can be read at `(n, n - 1)` as the source writes it.

## Implementation notes

**No `stacks` attribute is attached.** The sequence is an internal step of the proof of
[Stacks, Tag 0AGS] and of the proof of [Stacks, Tag 0AGQ]; it is not an assertion of either tag,
nor of [Stacks, Tag 02OS]. The twisted sequence of [Stacks, Tag 0C6K] it specializes carries that
tag already, in
`StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemeExactSequenceTwist.lean`.

**The second map is the unit at `𝒪_X(n)`, not a conjugate of the unit at
`𝒪_X(n+1) ⊗ 𝒪_X(E)`.** Transporting the twisted sequence along an isomorphism `e` of its middle
term replaces the unit `η` at the old middle term by `e⁻¹ ≫ η ≫ i_*i^*e`, and naturality of the
unit of the adjunction rewrites that as the unit at the new middle term, so no conjugation
survives in the statement. The transport itself is `CategoryTheory.ShortComplex.isoMk` followed
by `CategoryTheory.ShortComplex.shortExact_of_iso`.

**The monoidal structure is needed at two spellings of the sheaf of rings**, because the twists
state their own type over the `sheafCompose` spelling `Stacks.AlgebraicGeometry.projRingSheaf`
while the divisor sheaf and the tensor product are written over
`AlgebraicGeometry.Scheme.ringCatSheaf`; the two are equal by `rfl` but instance search is
syntactic.

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric

universe u

namespace Stacks.Blowup

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **The exceptional divisor of the affine blowup**, as a quasi-coherent sheaf of ideals on
`Proj (⨁ₙ Iⁿ)`: the inverse image of the centre, the centre being the ideal sheaf on `Spec R`
that `I` determines through `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
@[ega "IV 19.4.1" "special case"]
def exceptionalIdealData : (blowUpSpec I).IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop
    (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).comap (toSpec I)

/-- The exceptional divisor `Stacks.Blowup.exceptionalIdealData I` of the affine blowup is an
effective Cartier divisor. -/
instance isEffectiveCartierDivisor_exceptionalIdealData :
    Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalIdealData I) :=
  isEffectiveCartierDivisor_comap_toSpec_ofIdealTop I

/-- **`𝒪_X(m) ⊗ 𝒪_X(E) ≅ 𝒪_X(n)` for `m = n + 1`** on the affine blowup `X = Proj (⨁ₙ Iⁿ)`, with
`E` the exceptional divisor. -/
def twistTensorDivisorSheafIso {m n : ℤ} (hmn : m = n + 1) :
    (blowUpTwist I m ⊗
        Stacks.Divisors.modulesInvertibleSheaf (exceptionalIdealData I)) ≅
      blowUpTwist I n := by
  subst hmn
  have hgen := adjoin_reesGradingZero_reesGrading_one_eq_top I
  have heq : (Stacks.AlgebraicGeometry.ProjTwistPowers.twistRight
      (reesGrading I)).IsEquivalence :=
    Stacks.AlgebraicGeometry.ProjTwistPowers.isEquivalence_twistRight (reesGrading I) hgen
  set M : (blowUpSpec I).Modules := blowUpTwist I (n + 1) with hM
  set L : (blowUpSpec I).Modules :=
    Stacks.Divisors.modulesInvertibleSheaf (exceptionalIdealData I) with hL
  set O1 : (blowUpSpec I).Modules := blowUpTwist I 1 with hO1
  refine (Stacks.AlgebraicGeometry.ProjTwistPowers.twistRight (reesGrading I)).preimageIso
    (show ((M ⊗ L) ⊗ O1 : (blowUpSpec I).Modules) ≅
      (blowUpTwist I n ⊗ O1) from ?_)
  refine α_ M L O1 ≪≫ whiskerLeftIso M ?_ ≪≫ ρ_ M ≪≫
    (Stacks.AlgebraicGeometry.ProjTwistPowers.twistMulIso (reesGrading I) hgen n).symm
  exact whiskerLeftIso L (twistOneIsoExceptionalIdealSheafOfIdealTop I) ≪≫
    Stacks.Divisors.invertibleSheafPairing (exceptionalIdealData I)

/-- **The twist short exact sequence of a blowup.** For `X = Proj (⨁ₙ Iⁿ)` the blowup of
`Spec R` in `I`, with exceptional divisor `E` and inclusion `i : E ⟶ X`, and for `m = n + 1`,
the sequence

`0 ⟶ 𝒪_X(m) ⟶ 𝒪_X(n) ⟶ i_* i^* 𝒪_X(n) ⟶ 0`

is short exact. The first map is multiplication by the canonical section of `𝒪_X(E)` followed by
the identification `𝒪_X(n+1) ⊗ 𝒪_X(E) ≅ 𝒪_X(n)`, that is, the inclusion
`𝒪_X(n+1) = ℐ_E · 𝒪_X(n) ⊆ 𝒪_X(n)`; the second is the unit of `i^* ⊣ i_*`, that is, restriction
to `E`.

At `(m, n) = (n, n - 1)`, with `hmn` supplied by `sub_add_cancel`, this is the sequence
`0 → 𝒪_X(n) → 𝒪_X(n-1) → i_*𝒪_E(n-1) → 0` of the proofs of parts (4) and (5) of
[Stacks, Tag 0AGS]. -/
@[sga "6 VII 3.5" "partial"]
theorem shortExact_twist_exceptional {m n : ℤ} (hmn : m = n + 1) :
    let i := (exceptionalIdealData I).subschemeι
    let f : blowUpTwist I m ⟶ blowUpTwist I n :=
      ((ρ_ (blowUpTwist I m)).inv ≫
          blowUpTwist I m ◁
            (Stacks.Divisors.modulesInvertibleSheaf (exceptionalIdealData I)).unitHomEquiv.symm
              (Stacks.Divisors.canonicalSections (exceptionalIdealData I))) ≫
        (twistTensorDivisorSheafIso I hmn).hom
    let g : blowUpTwist I n ⟶
        (Scheme.Modules.pushforward i).obj
          ((Scheme.Modules.pullback i).obj (blowUpTwist I n)) :=
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (blowUpTwist I n)
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact := by
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (blowUpSpec I).sheaf.obj
      (blowUpSpec I).ringCatSheaf.property (blowUpTwist I m) :=
    Stacks.Blowup.isInvertible_blowUpTwist I m
  obtain ⟨h₀, hSE⟩ := Stacks.Divisors.isShortExactTwistSequence_canonicalSections
    (exceptionalIdealData I) (blowUpTwist I m)
  set i := (exceptionalIdealData I).subschemeι with hi
  set e := twistTensorDivisorSheafIso I hmn with he
  set F := Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i with hF
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality e.hom
  simp only [Functor.id_map] at hnat
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hnat, ← Category.assoc, h₀, zero_comp]
  · refine ShortComplex.shortExact_of_iso ?_ hSE
    exact ShortComplex.isoMk (Iso.refl _) e (F.mapIso e) (by simp) hnat

end Stacks.Blowup

end
