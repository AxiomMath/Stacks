module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AsSubring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reading a section of the structure sheaf of an integral affine scheme as a fraction

Let `A` be a domain with fraction field `K` and let `X = Spec A`. Every nonempty open of `X`
contains the generic point, so a section of `𝒪_X` over an open has a well-defined value in `K`,
namely its germ at the generic point. This file defines that value, `genericValue`, and shows
that it is a ring homomorphism, that it is a fraction whose denominator is invertible at any
prescribed point of the open, and that every such fraction is the value of a section on a basic
open neighbourhood.

## Main definitions

* `Stacks.FractionValue.genericPt`: the generic point of `Spec A`, the prime `(0)`.
* `Stacks.FractionValue.Sect`: the sections of `𝒪_X` over an open.
* `Stacks.FractionValue.genericValue`: the value in `K` of such a section.

## Main results

* `Stacks.FractionValue.mem_of_le_of_mem`: an open meeting the zero locus of a prime `𝔭` contains
  `𝔭`; so the generic point of an irreducible closed set lies in every open meeting it.
* `Stacks.FractionValue.genericPt_mem`: a nonempty open contains the generic point.
* `Stacks.FractionValue.genericValue_mul`, `genericValue_add`, `genericValue_one`,
  `genericValue_zero`, `genericValue_res`: the value is a ring homomorphism, and is unchanged by
  restriction to a smaller nonempty open.
* `Stacks.FractionValue.exists_fraction_genericValue`: a section has value `a / b` with `b`
  outside any prescribed point of its open.
* `Stacks.FractionValue.exists_section_genericValue`: conversely `a / b` is the value of a section
  on the basic open `D(b)`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open PrimeSpectrum (basicOpen)

universe u

namespace Stacks.FractionValue

attribute [local instance] Classical.propDecidable

variable (A : Type u) [CommRing A] [IsDomain A]

/-- The generic point of `Spec A` for `A` a domain: the prime ideal `(0)`. -/
public def genericPt : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩

/-- The multiplicative set of nonzero elements, the complement of the generic point. -/
public abbrev genericCompl : Submonoid A := (genericPt A).asIdeal.primeCompl

/-- Sections of the structure sheaf of `Spec A` over an open. -/
public abbrev Sect (W : Opens (PrimeSpectrum.Top A)) : Type u :=
  (Spec.structureSheaf A).presheaf.obj (op W)

variable {A}

/-- A nonzero element of `A` lies in the complement of the generic point. -/
public lemma mem_genericCompl {b : A} (hb : b ≠ 0) : b ∈ genericCompl A := by
  simpa [genericPt] using hb

omit [IsDomain A] in
/-- An open subset of `Spec A` which meets the zero locus of a prime `𝔭` contains `𝔭`. -/
public lemma mem_of_le_of_mem {W : Opens (PrimeSpectrum.Top A)} {q p : PrimeSpectrum A}
    (hq : q ∈ W) (hp : p.asIdeal ≤ q.asIdeal) : p ∈ W := by
  obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hqb, hbW⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hq W.2
  exact hbW (show p ∈ basicOpen b from fun hb => hqb (hp hb))

/-- A nonempty open subset of `Spec A` contains the generic point. -/
@[ega "I 7.1.10" "special case"]
public lemma genericPt_mem {W : Opens (PrimeSpectrum.Top A)} {q : PrimeSpectrum A} (hq : q ∈ W) :
    genericPt A ∈ W :=
  mem_of_le_of_mem hq bot_le

variable (A) in
/-- The canonical ring homomorphism from the localization of `A` at the generic point to the
fraction field of `A`. -/
public def toFrac : LocalizedModule (genericCompl A) A →+* FractionRing A :=
  IsLocalization.lift (M := genericCompl A) (g := algebraMap A (FractionRing A)) fun y => by
    refine isUnit_iff_ne_zero.2 fun h => y.2 ?_
    have hy : (y : A) = 0 := IsFractionRing.injective A (FractionRing A) (by simpa using h)
    simp [hy, genericPt]

private lemma algebraMap_eq_mk (a : A) :
    algebraMap A (LocalizedModule (genericCompl A) A) a = LocalizedModule.mk a 1 := by
  have h1 : (1 : LocalizedModule (genericCompl A) A) = LocalizedModule.mk (1 : A) 1 := by
    with_unfolding_all rfl
  rw [Algebra.algebraMap_eq_smul_one, h1, LocalizedModule.smul'_mk, smul_eq_mul, mul_one]

private lemma toFrac_algebraMap (a : A) :
    toFrac A (algebraMap A (LocalizedModule (genericCompl A) A) a) =
      algebraMap A (FractionRing A) a :=
  IsLocalization.lift_eq _ _

/-- The defining property of `toFrac`: it carries `a / b` to `a / b`. -/
public lemma toFrac_mk (a : A) (b : genericCompl A) :
    toFrac A (LocalizedModule.mk a b) * algebraMap A (FractionRing A) (b : A) =
      algebraMap A (FractionRing A) a := by
  have hmul : LocalizedModule.mk a b * LocalizedModule.mk (b : A) 1 =
      LocalizedModule.mk (a * (b : A)) (1 * b) := rfl
  have key : LocalizedModule.mk a b *
      algebraMap A (LocalizedModule (genericCompl A) A) (b : A) =
      algebraMap A (LocalizedModule (genericCompl A) A) a := by
    rw [algebraMap_eq_mk, algebraMap_eq_mk, hmul, LocalizedModule.mk_eq]
    exact ⟨1, by simp [Submonoid.smul_def, mul_comm]⟩
  rw [← toFrac_algebraMap (b : A), ← toFrac_algebraMap a, ← map_mul, key]

/-- The value in the fraction field of a section of the structure sheaf of `Spec A` over an open
`W`: its germ at the generic point. Sections over the empty open are given the value `0`. -/
public def genericValue {W : Opens (PrimeSpectrum.Top A)} (s : Sect A W) : FractionRing A :=
  if hW : genericPt A ∈ W then toFrac A (s.1 ⟨genericPt A, hW⟩) else 0

/-- On an open containing the generic point, the value of a section is the image of its germ
there under `toFrac`. -/
public lemma genericValue_eq {W : Opens (PrimeSpectrum.Top A)} (hW : genericPt A ∈ W)
    (s : Sect A W) : genericValue s = toFrac A (s.1 ⟨genericPt A, hW⟩) :=
  dif_pos hW

/-- Two sections with the same germ at the generic point have the same value. -/
public lemma genericValue_congr {W W' : Opens (PrimeSpectrum.Top A)} (hW : genericPt A ∈ W)
    (hW' : genericPt A ∈ W') (s : Sect A W) (s' : Sect A W')
    (h : s.1 ⟨genericPt A, hW⟩ = s'.1 ⟨genericPt A, hW'⟩) : genericValue s = genericValue s' := by
  rw [genericValue_eq hW, genericValue_eq hW', h]

/-- The value of a section which is the constant fraction `a / b` at the generic point. -/
public lemma genericValue_mul_eq {W : Opens (PrimeSpectrum.Top A)} (hW : genericPt A ∈ W)
    (s : Sect A W) (a : A) (b : genericCompl A)
    (h : s.1 ⟨genericPt A, hW⟩ = LocalizedModule.mk a b) :
    genericValue s * algebraMap A (FractionRing A) (b : A) = algebraMap A (FractionRing A) a := by
  rw [genericValue_eq hW, h]
  exact toFrac_mk a b

/-- On an open containing the generic point, the value of a product is the product of the
values. -/
public lemma genericValue_mul {W : Opens (PrimeSpectrum.Top A)} (hW : genericPt A ∈ W)
    (s t : Sect A W) : genericValue (s * t) = genericValue s * genericValue t := by
  rw [genericValue_eq hW, genericValue_eq hW, genericValue_eq hW, ← map_mul]
  rfl

/-- On an open containing the generic point, the value of a sum is the sum of the values. -/
public lemma genericValue_add {W : Opens (PrimeSpectrum.Top A)} (hW : genericPt A ∈ W)
    (s t : Sect A W) : genericValue (s + t) = genericValue s + genericValue t := by
  rw [genericValue_eq hW, genericValue_eq hW, genericValue_eq hW, ← map_add]
  rfl

/-- On an open containing the generic point, the value of `1` is `1`. -/
public lemma genericValue_one {W : Opens (PrimeSpectrum.Top A)} (hW : genericPt A ∈ W) :
    genericValue (1 : Sect A W) = 1 := by
  rw [genericValue_eq hW, show (1 : Sect A W).1 ⟨genericPt A, hW⟩ = 1 from rfl, map_one]

/-- The value of `0` is `0`. -/
public lemma genericValue_zero {W : Opens (PrimeSpectrum.Top A)} :
    genericValue (0 : Sect A W) = 0 := by
  by_cases hW : genericPt A ∈ W
  · rw [genericValue_eq hW, show (0 : Sect A W).1 ⟨genericPt A, hW⟩ = 0 from rfl, map_zero]
  · exact dif_neg hW

/-- The value of a section is unchanged by restriction to a smaller nonempty open. -/
public lemma genericValue_res {W W' : Opens (PrimeSpectrum.Top A)} (hle : W' ≤ W)
    (hW' : genericPt A ∈ W') (s : Sect A W) :
    genericValue ((Spec.structureSheaf A).presheaf.map (homOfLE hle).op s) = genericValue s :=
  genericValue_congr hW' (hle hW') _ s rfl

/-- A section over `W` is, in the fraction field, a fraction `a / b` whose denominator is
invertible at any prescribed point of `W`. -/
public lemma exists_fraction_genericValue {W : Opens (PrimeSpectrum.Top A)} (s : Sect A W)
    {q : PrimeSpectrum A} (hq : q ∈ W) :
    ∃ a b : A, b ∉ q.asIdeal ∧
      genericValue s * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a := by
  obtain ⟨b, hqb, i, a, hconst⟩ :=
    AlgebraicGeometry.StructureSheaf.exists_const (R := A) (M := A) W s q hq
  have hb0 : b ∈ genericCompl A :=
    mem_genericCompl fun hb => hqb (hb ▸ q.asIdeal.zero_mem)
  have hgen : genericPt A ∈ basicOpen b := hb0
  refine ⟨a, b, hqb, genericValue_mul_eq (i hgen) s a ⟨b, hb0⟩ ?_⟩
  have h := congrArg (fun t => t.1 ⟨genericPt A, hgen⟩) hconst
  exact h.symm

/-- Conversely, a fraction `a / b` is the value of a section of the structure sheaf on the basic
open `D(b)`. -/
public lemma exists_section_genericValue (a b : A) (hb : b ≠ 0) :
    ∃ s : Sect A (basicOpen b), genericValue s * algebraMap A (FractionRing A) b =
      algebraMap A (FractionRing A) a := by
  have hb0 : b ∈ genericCompl A := mem_genericCompl hb
  refine ⟨AlgebraicGeometry.StructureSheaf.const (R := A) (M := A) a b (basicOpen b) le_rfl,
    genericValue_mul_eq (show genericPt A ∈ basicOpen b from hb0) _ a ⟨b, hb0⟩ rfl⟩

end Stacks.FractionValue

end
