module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequence
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequenceExact
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberIntersectionForm
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant

/-!
# Invertible modules on a regular model with trivial tensor power

Let `X ⟶ Spec(R)` be a regular proper model of a smooth projective curve `C` over the fraction
field of a discrete valuation ring, and write the special fibre as `X_k = Σ mᵢ Cᵢ`; put
`d = gcd(m₁, …, mₙ)`. [Stacks, Tag 0CAB] says that an invertible `𝒪_X`-module `ℒ` which is
trivial on `C` and has degree `0` on every `Cᵢ` satisfies `ℒ^{⊗d} ≅ 𝒪_X`.

The arithmetic heart of the matter is that a coefficient vector `(a₁, …, aₙ)` which is a rational
multiple `q(m₁, …, mₙ)` of the multiplicity vector becomes an *integral* multiple of it after
scaling by `d`: the greatest common divisor of the `mᵢ` is an integral combination of them, so
`dq = Σ cᵢ(qmᵢ) = Σ cᵢaᵢ` is an integer. Since `Σ mᵢ Cᵢ` is the special fibre, whose invertible
sheaf is trivial, `d · Σ aᵢ[𝒪_X(Cᵢ)] = l · Σ mᵢ[𝒪_X(Cᵢ)] = 0` in `Pic(X)`.

## Main results

* `Stacks.Models.exists_intCast_eq_gcd_mul`: if `aᵢ = q mᵢ` for all `i` with `aᵢ` integral and
  `q` rational, then `d q` is an integer, where `d = gcd(mᵢ)`.
* `Stacks.Models.exists_gcd_mul_eq_mul`: the same read off coordinatewise, `d aᵢ = l mᵢ`.
* `Stacks.Models.exists_gcd_zsmul_eq_multiplicityHom`: the same again, as
  `d • a = multiplicityHom m l`, putting `d • a` in the image of the first map of the sequence
  of [Stacks, Tag 0C63].
* `Stacks.Models.gcd_zsmul_componentPicardHom_eq_zero`: `d • Σ aᵢ[𝒪_X(Cᵢ)] = 0` in `Pic(X)`.
* `Stacks.Models.nonempty_tensorPower_gcd_iso_unit`: Tag 0CAB for an invertible module whose
  Picard class is `Σ aᵢ[𝒪_X(Cᵢ)]` with `(aᵢ)` a rational multiple of `(mᵢ)`.
* `Stacks.Models.nonempty_tensorPower_gcd_iso_unit_of_form`: the same with the rational
  multiplicity replaced by the vanishing of a symmetric form with the properties that
  [Stacks, Tag 0C66] establishes for the intersection form, through [Stacks, Tag 0C5X].
* `Stacks.Models.exists_eq_mul_specialFiberMultiplicity_of_componentDegree_eq_zero`: at the
  irreducible components of the special fibre, the vanishing of the degrees of `ℒ` makes the
  coefficient vector a rational multiple of the multiplicity vector, by part (4) of
  [Stacks, Tag 0C66].
* `Stacks.Models.nonempty_tensorPower_gcd_iso_unit_of_componentDegree_eq_zero`: **Tag 0CAB at
  both of its own hypotheses**, at the irreducible components of the special fibre.

## Implementation notes

**Relative to a decomposition.** As in
`StacksFrontier/AlgebraicGeometry/Curves/Models/PicardSequence.lean`, the components `C₁, …, Cₙ` of
the special fibre and their multiplicities enter as hypotheses: a finite index type `ι`, a family
`C` of effective Cartier divisors, multiplicities `m`, and `X_k = ∏ i, C i ^ m i`. This is the
phrase "write `X_k = Σ mᵢ Cᵢ`" with which the standing situation of [Stacks, Tag 0C61] opens.
Divisor sums are written multiplicatively, since `Add` on `AlgebraicGeometry.Scheme.IdealSheafData`
is `⊔`, scheme-theoretic intersection, and not divisor addition.

**The Bézout step is binary.** `Stacks.Models.exists_intCast_eq_gcd_mul` inducts over the index
set and uses `Nat.gcd_eq_gcd_ab` at each step, rather than a Bézout identity for a finite family.

### Tag 0CAB at its own hypotheses, and at an abstract family

Tag 0CAB has two hypotheses, and its proof uses each of them through one inference. Both
inferences are available, so the tag is proved as it stands, at the irreducible components of the
special fibre, in
`Stacks.Models.nonempty_tensorPower_gcd_iso_unit_of_componentDegree_eq_zero`.

* "`ℒ` restricts to the trivial invertible module on `C`" gives `ℒ ≅ 𝒪_X(Σ aᵢCᵢ)` by exactness of
  the sequence of [Stacks, Tag 0C63] at `Pic(X)`, which is the sixth conjunct of
  `Stacks.Models.picardSequence_exact` in
  `StacksFrontier/AlgebraicGeometry/Curves/Models/PicardSequenceExact.lean`.
* "`ℒ` has degree `0` on each `Cᵢ`" gives `(aᵢ) = q(mᵢ)` by part (4) of [Stacks, Tag 0C66]. All
  four parts of that tag are proved in
  `StacksFrontier/AlgebraicGeometry/Curves/Models/SpecialFiberIntersectionForm.lean`, resting on the
  symmetry of the intersection product [Stacks, Tag 0C64] in
  `StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean` and on the
  connectedness of the special fibre [Stacks, Tag 0C62] in
  `StacksFrontier/AlgebraicGeometry/Curves/Models/SpecialFiberConnected.lean`. The step itself is
  `Stacks.Models.exists_eq_mul_specialFiberMultiplicity_of_componentDegree_eq_zero`, whose
  bilinear expansion `deg(𝒪_X(Σ bᵢCᵢ)|_{Cⱼ}) = Σᵢ bᵢ(Cⱼ · Cᵢ)` is
  `Stacks.Models.RegularProperModelSituation.specialFiberDivisorDegree_eq_sum`, the invertible
  case of [Stacks, Tag 0AYX].

The two statements at an abstract family of components keep the rational multiplicity as a
hypothesis, because they are stated before the components are known to be the irreducible ones:
directly in `Stacks.Models.nonempty_tensorPower_gcd_iso_unit`, and in
`Stacks.Models.nonempty_tensorPower_gcd_iso_unit_of_form` through the linear algebra of
[Stacks, Tag 0C5X] applied to an abstract symmetric form with the properties that Tag 0C66
establishes for the intersection form. Their attributes record that restriction. The appeal to
[Stacks, Tag 0C67] that the source makes at the end is not needed for the statement proved here.

## References

* [Stacks Project, Tag 0CAB](https://stacks.math.columbia.edu/tag/0CAB)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C63](https://stacks.math.columbia.edu/tag/0C63)
* [Stacks Project, Tag 0C66](https://stacks.math.columbia.edu/tag/0C66)
* [Stacks Project, Tag 0C67](https://stacks.math.columbia.edu/tag/0C67)
* [Stacks Project, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)
* [Stacks Project, Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Divisors
open Stacks.Picard (ofScheme)
open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules (IsInvertible picardClass)
open Stacks.SheafOfModules.TensorPower (tensorPower isInvertible_tensorPower)

universe u

namespace Stacks.Models

/-! ### A rational multiple of the multiplicity vector, scaled by the greatest common divisor -/

section Arithmetic

variable {ι : Type*} (s : Finset ι) (m : ι → ℕ) (a : ι → ℤ) (q : ℚ)

/-- **A rational multiple of a vector of natural numbers becomes integral after scaling by their
greatest common divisor.** If `aᵢ = q mᵢ` with every `aᵢ` an integer, then `dq` is an integer for
`d = gcd(mᵢ)`: the greatest common divisor is an integral combination `Σ cᵢ mᵢ`, so
`dq = Σ cᵢ aᵢ`. The induction over the index set uses the binary Bézout identity
`Nat.gcd_eq_gcd_ab` at each step. -/
theorem exists_intCast_eq_gcd_mul (ha : ∀ i ∈ s, (a i : ℚ) = q * (m i : ℚ)) :
    ∃ l : ℤ, (l : ℚ) = ((s.gcd m : ℕ) : ℚ) * q := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact ⟨0, by simp⟩
  | cons i s hi ih =>
      obtain ⟨l, hl⟩ := ih fun j hj => ha j (Finset.mem_cons_of_mem hj)
      have hai : (a i : ℚ) = q * (m i : ℚ) := ha i (Finset.mem_cons_self ..)
      have hgcd : (Finset.cons i s hi).gcd m = Nat.gcd (m i) (s.gcd m) := by
        rw [Finset.cons_eq_insert, Finset.gcd_insert]
        rfl
      refine ⟨Nat.gcdA (m i) (s.gcd m) * a i + Nat.gcdB (m i) (s.gcd m) * l, ?_⟩
      have hbezout : ((Nat.gcd (m i) (s.gcd m) : ℕ) : ℚ) =
          (m i : ℚ) * (Nat.gcdA (m i) (s.gcd m) : ℚ) +
            ((s.gcd m : ℕ) : ℚ) * (Nat.gcdB (m i) (s.gcd m) : ℚ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (Nat.gcd_eq_gcd_ab (m i) (s.gcd m))
      rw [hgcd, hbezout]
      push_cast
      rw [hl, hai]
      ring

/-- **A rational multiple of a vector of natural numbers becomes an integral multiple of it after
scaling by their greatest common divisor**, `d aᵢ = l mᵢ`: the scalar `l = dq` is an integer by
`Stacks.Models.exists_intCast_eq_gcd_mul`. -/
theorem exists_gcd_mul_eq_mul (ha : ∀ i ∈ s, (a i : ℚ) = q * (m i : ℚ)) :
    ∃ l : ℤ, ∀ i ∈ s, ((s.gcd m : ℕ) : ℤ) * a i = l * (m i : ℤ) := by
  obtain ⟨l, hl⟩ := exists_intCast_eq_gcd_mul s m a q ha
  refine ⟨l, fun i hi => ?_⟩
  have hrat : (((s.gcd m : ℕ) : ℤ) * a i : ℚ) = (l * (m i : ℤ) : ℚ) := by
    push_cast
    rw [ha i hi, hl]
    ring
  exact_mod_cast hrat

/-- **A rational multiple of the multiplicity vector, scaled by the gcd, is in the image of the
first map of the Picard sequence**: `d • a = multiplicityHom m l` for some integer `l`. -/
theorem exists_gcd_zsmul_eq_multiplicityHom [Fintype ι]
    (ha : ∀ i, (a i : ℚ) = q * (m i : ℚ)) :
    ∃ l : ℤ, ((Finset.univ.gcd m : ℕ) : ℤ) • a = multiplicityHom m l := by
  obtain ⟨l, hl⟩ := exists_gcd_mul_eq_mul Finset.univ m a q fun i _ => ha i
  refine ⟨l, funext fun i => ?_⟩
  simpa only [Pi.smul_apply, zsmul_eq_mul, Int.cast_id, multiplicityHom_apply] using
    hl i (Finset.mem_univ i)

end Arithmetic

/-! ### Tag 0CAB: triviality of the `d`-th tensor power -/

section Model

variable (S : RegularProperModelSituation.{u}) {ι : Type*} [Fintype ι]
  (C : ι → S.X.IdealSheafData) (m : ι → ℕ) [∀ i, IsEffectiveCartierDivisor (C i)]
  (hdec : S.specialFiberIdeal = ∏ i, C i ^ m i) (a : ι → ℤ)

include hdec

/-- **A rational multiple of the multiplicity vector has `d`-torsion class in `Pic(X)`**,
`d • Σ aᵢ[𝒪_X(Cᵢ)] = 0`: after scaling by `d = gcd(mᵢ)` the vector `a` becomes an integral
multiple `l(m₁, …, mₙ)` of the multiplicity vector, and `Σ mᵢ Cᵢ` is the special fibre, whose
invertible sheaf is trivial. -/
theorem gcd_zsmul_componentPicardHom_eq_zero (q : ℚ) (ha : ∀ i, (a i : ℚ) = q * (m i : ℚ)) :
    ((Finset.univ.gcd m : ℕ) : ℤ) • componentPicardHom S C a = 0 := by
  obtain ⟨l, hl⟩ := exists_gcd_zsmul_eq_multiplicityHom m a q ha
  rw [← map_zsmul (componentPicardHom S C), hl]
  exact componentPicardHom_multiplicityHom S C m hdec l

/-- **[Stacks, Tag 0CAB] with both hypotheses replaced by the conclusions its proof draws
from them.** Let `ℒ` be an invertible `𝒪_X`-module on a regular proper model whose Picard class is
the combination `Σ aᵢ[𝒪_X(Cᵢ)]` of the classes of the components of the special fibre, and suppose
the coefficient vector `(aᵢ)` is a rational multiple of the multiplicity vector `(mᵢ)`. Then
`ℒ^{⊗d} ≅ 𝒪_X` for `d = gcd(m₁, …, mₙ)`. -/
theorem nonempty_tensorPower_gcd_iso_unit
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      S.X.presheaf (structureIsSheaf S.X.toRingedSpace)))
    (hL : IsInvertible S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L)
    (hclass : picardClass S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L hL =
      componentPicardHom S C a)
    (q : ℚ) (ha : ∀ i, (a i : ℚ) = q * (m i : ℚ)) :
    Nonempty (tensorPower S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L
        ((Finset.univ.gcd m : ℕ) : ℤ) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        S.X.presheaf (structureIsSheaf S.X.toRingedSpace))) := by
  have hzero : ((Finset.univ.gcd m : ℕ) : ℤ) •
      picardClass S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L hL = 0 := by
    rw [hclass]
    exact gcd_zsmul_componentPicardHom_eq_zero S C m hdec a q ha
  have := hL
  refine (Stacks.SheafOfModules.picardClass_eq_iff S.X.presheaf
    (structureIsSheaf S.X.toRingedSpace) _ _
    (isInvertible_tensorPower S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L _)
    (Stacks.SheafOfModules.isInvertible_unit _ _)).1 ?_
  rw [Stacks.Picard.classOf_tensorPower, hzero,
    Stacks.SheafOfModules.picardClass_zero S.X.presheaf (structureIsSheaf S.X.toRingedSpace)]

/-- **[Stacks, Tag 0CAB] with the rational multiplicity of the coefficient vector
obtained from the vanishing of a symmetric form.** Let `A` be a symmetric form on `ℤⁿ` with
nonnegative off-diagonal entries which kills the multiplicity vector and has no proper nonempty
set of indices disconnected from its complement — the three properties [Stacks, Tag 0C66]
establishes for the intersection form `(Cᵢ · Cⱼ)`. If the class of an invertible `𝒪_X`-module `ℒ`
is `Σ aᵢ[𝒪_X(Cᵢ)]` and `a` is isotropic for `A`, then `ℒ^{⊗d} ≅ 𝒪_X` for `d = gcd(m₁, …, mₙ)`. -/
theorem nonempty_tensorPower_gcd_iso_unit_of_form
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      S.X.presheaf (structureIsSheaf S.X.toRingedSpace)))
    (hL : IsInvertible S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L)
    (hclass : picardClass S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L hL =
      componentPicardHom S C a)
    (A : Matrix ι ι ℚ) (hA : A.IsSymm) (hoffDiag : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hm : ∀ i, 0 < m i) (hAm : A.mulVec (fun i => (m i : ℚ)) = 0)
    (hconnected : ∀ I : Set ι, I.Nonempty → I ≠ Set.univ →
      ¬ ∀ i ∈ I, ∀ j ∉ I, A i j = 0)
    (hself : dotProduct (fun i => (a i : ℚ)) (A.mulVec fun i => (a i : ℚ)) = 0) :
    Nonempty (tensorPower S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L
        ((Finset.univ.gcd m : ℕ) : ℤ) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        S.X.presheaf (structureIsSheaf S.X.toRingedSpace))) := by
  have hmQ : ∀ i, (0 : ℚ) < (m i : ℚ) := fun i => by exact_mod_cast hm i
  obtain ⟨q, hq⟩ := (Matrix.dotProduct_mulVec_eq_zero_iff_of_positive_kernel hA hoffDiag
    hmQ hAm hconnected).1 hself
  exact nonempty_tensorPower_gcd_iso_unit S C m hdec a L hL hclass q fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hq i

end Model

/-! ### Tag 0CAB at the irreducible components of the special fibre -/

section Canonical

variable (S : RegularProperModelSituation.{u})
  [DecidableEq (irreducibleComponents S.specialFiber)]

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **The coefficient vector is a rational multiple of the multiplicity vector.** If the class of
an invertible `𝒪_X`-module `ℒ` is the combination `Σ a_Z[𝒪_X(C_Z)]` of the classes of the
irreducible components of the special fibre, and `ℒ` has degree `0` on every component, then
`a_Z = q m_Z` for a single rational `q`.

This is the inference the source of [Stacks, Tag 0CAB] draws from the vanishing of the degrees,
through part (4) of [Stacks, Tag 0C66]. Adding a multiple of `(m_Z)`, whose class vanishes because
`Σ m_Z C_Z` is the special fibre, makes the coefficients nonnegative, so that
`ℒ ≅ 𝒪_X(Σ b_Z C_Z)` and
`0 = deg(ℒ|_{C_Z}) = Σ_Y b_Y (C_Z · C_Y)` by the bilinear expansion of [Stacks, Tag 0C64]. The
intersection matrix therefore kills `b`, so the quadratic form vanishes at `b`, and the equality
case of part (4) of [Stacks, Tag 0C66] identifies `b`, and with it `a`, as a rational multiple of
`(m_Z)`. -/
theorem exists_eq_mul_specialFiberMultiplicity_of_componentDegree_eq_zero
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      S.X.presheaf (structureIsSheaf S.X.toRingedSpace)))
    (hL : IsInvertible S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L)
    (a : irreducibleComponents S.specialFiber → ℤ)
    (hclass : picardClass S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L hL =
      componentPicardHom S S.specialFiberComponentIdeal a)
    (hdeg : ∀ Z, S.specialFiberComponentDegree Z L hL = 0) :
    ∃ q : ℚ, ∀ Z, (a Z : ℚ) = q * (S.specialFiberMultiplicity Z : ℚ) := by
  classical
  set C := S.specialFiberComponentIdeal with hCdef
  set m := S.specialFiberMultiplicity with hmdef
  have hdec : S.specialFiberIdeal = ∏ Z, C Z ^ m Z := S.specialFiberIdeal_eq_prod
  have hCe : ∀ Z, Stacks.Divisors.IsEffectiveCartierDivisor (C Z) := fun Z =>
    S.isEffectiveCartierDivisor_specialFiberComponent Z
  -- shift the coefficients to be nonnegative
  set t : ℕ := ∑ Z, (a Z).natAbs with htdef
  have hb0 : ∀ Z, 0 ≤ a Z + (t : ℤ) * (m Z : ℤ) := fun Z => by
    have h1 : (a Z).natAbs ≤ t :=
      Finset.single_le_sum (f := fun Z => (a Z).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ Z)
    have h2 : 1 ≤ m Z := S.specialFiberMultiplicity_pos Z
    have h3 : (t : ℤ) ≤ (t : ℤ) * (m Z : ℤ) := by
      have : (1 : ℤ) ≤ (m Z : ℤ) := by exact_mod_cast h2
      nlinarith
    have h4 : -((a Z).natAbs : ℤ) ≤ a Z := by
      have := Int.natAbs_neg (a Z) ▸ Int.le_natAbs (a := -a Z)
      omega
    have h5 : ((a Z).natAbs : ℤ) ≤ (t : ℤ) := by exact_mod_cast h1
    linarith
  set b : irreducibleComponents S.specialFiber → ℕ :=
    fun Z => (a Z + (t : ℤ) * (m Z : ℤ)).toNat with hbdef
  have hb : ∀ Z, (b Z : ℤ) = a Z + (t : ℤ) * (m Z : ℤ) := fun Z => Int.toNat_of_nonneg (hb0 Z)
  -- the class of L is the class of O_X(sum b_Z C_Z)
  have hclassb : picardClass S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L hL =
      Stacks.Divisors.picardClass (∏ Z, C Z ^ b Z) := by
    rw [hclass, picardClass_prod_pow]
    have hsum : (fun Z => (b Z : ℤ)) = a + multiplicityHom m (t : ℤ) := funext fun Z => by
      rw [hb Z, Pi.add_apply, multiplicityHom_apply]
    have hcp : componentPicardHom S C a = componentPicardHom S C (fun Z => (b Z : ℤ)) := by
      rw [hsum, map_add, componentPicardHom_multiplicityHom S C m hdec, add_zero]
    rw [hcp, componentPicardHom_apply]
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff S.X.presheaf
    (structureIsSheaf S.X.toRingedSpace) _ _ hL
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard _)).1 hclassb
  -- the matrix kills b, by 0C64's bilinear expansion and the vanishing of the degrees
  have hbN : ∀ Z, ∑ Y, (b Y : ℤ) * S.specialFiberIntersectionMatrix Z Y = 0 := fun Z => by
    rw [← S.specialFiberDivisorDegree_eq_sum Z b]
    rw [show S.specialFiberDivisorDegree Z b =
        S.specialFiberComponentDegree Z (Stacks.Divisors.invertibleSheaf' (∏ Y, C Y ^ b Y))
          (Stacks.Divisors.isInvertible_invertibleSheaf_picard _) from rfl]
    rw [← hdeg Z]
    exact (componentDegree_eq_of_iso S.k (C Z) _ _ _ L _ hL _ e).symm
  -- so the quadratic form vanishes at b, and part (4) of 0C66 applies
  have hzero : ∑ Z, ∑ Y, (b Z : ℚ) * (b Y : ℚ) *
      (S.specialFiberIntersectionMatrix Z Y : ℚ) = 0 := by
    refine Finset.sum_eq_zero fun Z _ => ?_
    have h : ((∑ Y, (b Y : ℤ) * S.specialFiberIntersectionMatrix Z Y : ℤ) : ℚ) = 0 := by
      rw [hbN Z, Int.cast_zero]
    push_cast at h
    calc ∑ Y, (b Z : ℚ) * (b Y : ℚ) * (S.specialFiberIntersectionMatrix Z Y : ℚ)
        = (b Z : ℚ) * ∑ Y, (b Y : ℚ) * (S.specialFiberIntersectionMatrix Z Y : ℚ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun Y _ => by ring
      _ = 0 := by rw [h, mul_zero]
  obtain ⟨q, hq⟩ := (S.specialFiberIntersectionForm_nonpos_and_eq_zero_iff
    (fun Z => (b Z : ℚ))).2.1 hzero
  refine ⟨q - (t : ℚ), fun Z => ?_⟩
  have h := hq Z
  have hbZ : ((b Z : ℤ) : ℚ) = (a Z : ℚ) + (t : ℚ) * (m Z : ℚ) := by
    rw [hb Z]; push_cast; ring
  push_cast at hbZ h
  linarith

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **Stacks Project, Tag 0CAB.** Let `X ⟶ Spec(R)` be a regular proper model of a smooth
projective curve `C` over the fraction field of a discrete valuation ring, write the special fibre
as `X_k = Σ m_Z C_Z` over its irreducible components and put `d = gcd(m_Z)`. An invertible
`𝒪_X`-module `ℒ` whose restriction to the generic fibre `C` is trivial and which has degree `0` on
every component of the special fibre satisfies `ℒ^{⊗d} ≅ 𝒪_X`.

Both hypotheses are the tag's own. Triviality on `C` is the vanishing of the class of `ℒ` in
`Pic(C)`, and exactness of the sequence `0 ⟶ ℤ ⟶ ℤ^{⊕n} ⟶ Pic(X) ⟶ Pic(C) ⟶ 0` at `Pic(X)`,
[Stacks, Tag 0C63], writes the class of `ℒ` as a combination `Σ a_Z[𝒪_X(C_Z)]`. The vanishing of
the degrees then makes `(a_Z)` a rational multiple `q(m_Z)` by part (4) of [Stacks, Tag 0C66]. The
greatest common divisor of the `m_Z` is an integral combination of them, so `dq` is an integer and
`d · Σ a_Z[𝒪_X(C_Z)]` is an integral multiple of `Σ m_Z[𝒪_X(C_Z)]`, which vanishes because
`Σ m_Z C_Z` is the special fibre and its invertible module is trivial. -/
@[stacks 0CAB "at the irreducible components of the special fibre: an invertible module trivial \
on the generic fibre C and of degree zero on every component has trivial d-th tensor power, for d \
the greatest common divisor of the multiplicities"]
theorem nonempty_tensorPower_gcd_iso_unit_of_componentDegree_eq_zero
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      S.X.presheaf (structureIsSheaf S.X.toRingedSpace)))
    (hL : IsInvertible S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L)
    (hgen : genericFiberPicardRestriction S
      (picardClass S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L hL) = 0)
    (hdeg : ∀ Z, S.specialFiberComponentDegree Z L hL = 0) :
    Nonempty (tensorPower S.X.presheaf (structureIsSheaf S.X.toRingedSpace) L
        ((Finset.univ.gcd S.specialFiberMultiplicity : ℕ) : ℤ) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        S.X.presheaf (structureIsSheaf S.X.toRingedSpace))) := by
  classical
  have : ∀ Z, IsEffectiveCartierDivisor (S.specialFiberComponentIdeal Z) := fun Z =>
    S.isEffectiveCartierDivisor_specialFiberComponent Z
  obtain ⟨-, -, -, -, -, -, hexact, -⟩ := picardSequence_exact S
  obtain ⟨a, ha⟩ := (hexact _).1 hgen
  obtain ⟨q, hq⟩ := exists_eq_mul_specialFiberMultiplicity_of_componentDegree_eq_zero S L hL a
    ha.symm hdeg
  exact nonempty_tensorPower_gcd_iso_unit S S.specialFiberComponentIdeal
    S.specialFiberMultiplicity S.specialFiberIdeal_eq_prod a L hL ha.symm q hq

end Canonical

end Stacks.Models

end
