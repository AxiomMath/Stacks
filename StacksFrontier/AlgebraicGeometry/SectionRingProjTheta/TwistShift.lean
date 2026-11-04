module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.Grading
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.SheafMapIsIso

/-!
# `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})` against `Γ_*(X, 𝓛, 𝓕)(n)`: the identification and the level it holds at

Stacks Tag 01QK uses, without comment, "the obvious identification
`M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})`", where `M = Γ_*(X, 𝓛, 𝓕)` and `M(n)` is the degree shift
`M(n)_i = M_{i + n}`. **As a statement about graded modules it is false for the graded module this
repository builds**, and this file proves both halves of that: the exact sense in which the two
differ, and the level at which the identification nevertheless holds.

`Stacks.TwistedSections.twistModule F L = ⨁ m : ℕ, twistSections F L m` is the *nonnegative
truncation* of Tag 01CV's graded module: its internal grading
`Stacks.TwistedSections.moduleGrading` is the trivial subgroup in every negative degree. The
shift `M(n)` of such a module is **not** nonnegatively concentrated: for `n ≥ 1` its degree
`-1` piece is `M_{n - 1} = Γ(X, 𝓕 ⊗ 𝓛^{⊗ (n-1)})`, which is in general nonzero, whereas the
degree `-1` piece of `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})` is trivial by construction. So no isomorphism of
graded modules can exist, and `Stacks.Monoidal.ModuleSystem.powShiftEquiv` — which is a true
`ℤ`-indexed statement in its own home — cannot be instantiated here to supply one.

**The identification holds, exactly, on the associated sheaves on `Proj`.** The comparison is a
degree-preserving `S`-linear map, injective in *every* degree and surjective in every degree
`≥ 0`; the failure is confined to the finitely many degrees `-n ≤ i ≤ -1`. Eventual bijectivity
is the hypothesis of
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections`
`.isIso_associatedModuleSheafMap_of_eventually_bijective`,
so the induced morphism `(Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n}))~ ⟶ (Γ_*(X, 𝓛, 𝓕)(n))~` is an isomorphism.

Everything is proved in an arbitrary braided preadditive monoidal category, since that is where
`Stacks.TwistedSections` lives; `𝓕 ⊗ 𝓛^{⊗ n}` is written in the repository's recursive spelling
`Stacks.TwistedSections.twistPow F L n`, which is the object the graded module is actually built
from.

## Main definitions

All in the namespace `Stacks.SectionRingProjTheta`.

* `twistShiftSection`: the comparison in a single degree,
  `Γ(X, (𝓕 ⊗ 𝓛^{⊗ m}) ⊗ 𝓛^{⊗ n}) ⟶ Γ(X, 𝓕 ⊗ 𝓛^{⊗ (m + n)})`. It is composition with an
  `eqToHom`, because the two objects are *equal*, not merely isomorphic: both tensor powers
  recurse on the same step.
* `twistShiftHom` and `twistShiftLinearMap`: the comparison of graded modules
  `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ m}) ⟶ Γ_*(X, 𝓛, 𝓕)`, additively and then `Γ_*(X, 𝓛)`-linearly.

## Main results

* `twistPow_twistPow`: `(𝓕 ⊗ 𝓛^{⊗ m}) ⊗ 𝓛^{⊗ n} = 𝓕 ⊗ 𝓛^{⊗ (m + n)}` on the nose.
* `twistPow_unit`: `𝒪_X ⊗ 𝓛^{⊗ n} = 𝓛^{⊗ n}` on the nose, so that the result below read at
  `𝓕 = 𝒪_X` is about `Γ_*(X, 𝓛, 𝓛^{⊗ n})`, the Remark's own instance.
* `twistShiftLinearMap_mem`: the comparison carries degree `i` into degree `i + m`, i.e. it is
  degree-preserving into the shift `Stacks.GradedModule.shiftedGrading`.
* `twistShiftLinearMap_injective_of_mem`: it is injective on homogeneous elements of **every**
  degree.
* `exists_mem_twistShiftLinearMap_eq`: it is surjective onto the homogeneous elements of every
  degree `≥ 0` of the shift.
* `isIso_twistShiftSheafMap`: **the identification, at the level the Remark's "obvious" claim is
  true at.** The induced morphism of associated sheaves on `Proj Γ_*(X, 𝓛)` is an isomorphism.
* `twistShiftSheafIso`: that isomorphism, packaged.
* `moduleGrading_shift_neg_one`: **the graded-module statement is false.** For `m ≥ 1` the
  degree `-1` piece of `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ m})` is trivial while the degree `-1` piece of the
  shift of `Γ_*(X, 𝓛, 𝓕)` is not, as soon as one twisted section of degree `m - 1` is nonzero.

## Implementation notes

**The comparison is `eqToHom`, and that is the point.** `Stacks.TwistedSections.twistPow F L`
is defined by `twistPow F L 0 = F`, `twistPow F L (m + 1) = twistPow F L m ⊗ L`, so
`twistPow (twistPow F L m) L n` and `twistPow F L (m + n)` are built by the same recursion from
the same base and are *equal* objects. No associator and no comparison of tensor powers appears
anywhere below. The cost is paid instead in the transport lemmas
`actMap_twistShiftSection` and `twistShiftSection_gsmul`, which are the two inductions that make
the comparison `Γ_*(X, 𝓛)`-linear; both are `eqToHom` bookkeeping closed by proof irrelevance.

**Why the degree indices are `m + n` on one side and `i + m` on the other.**
`Stacks.TwistedSections.gsmul` adds the scalar's degree on the *left*
(`gsmul : powSections L j → twistSections F L n → twistSections F L (j + n)`), while
`Stacks.GradedModule.shiftedGrading 𝒨 m i = 𝒨 (i + m)` adds the shift on the *right*. The two
conventions meet in `twistShiftSection_gsmul`, where the degree equality
`j + (m + n) = m + (j + n)` is `Nat.add_left_comm`, and in `twistShiftLinearMap_mem`, where
`(n : ℤ) + m = ((m + n : ℕ) : ℤ)`.

**The injectivity is unconditional, the surjectivity is not.** The comparison's source is
trivial in negative degrees, so injectivity there is vacuous and holds for free; surjectivity in
degree `i` needs the shift's degree `i` piece, which is the original module's degree `i + m`
piece, to be hit, and for `-m ≤ i < 0` it is a nonzero group with nothing mapping to it. That is
exactly the discrepancy, and `N₀ = 0` in the eventual-bijectivity hypothesis.

**No `@[stacks]` attribute is attached here.** The identification is a parenthetical step inside
Stacks Tag 01QK, not one of that Remark's two assertions; assertion (ii) is registered once, at
`Stacks.SectionRingProjTheta.pullbackComparison_tensorHom` of
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistSquare.lean`, and nothing here is a
second registration of it.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 0AG2](https://stacks.math.columbia.edu/tag/0AG2)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)

## What is not done here

**Nothing here produces Tag 0B5I's comparison family, and nothing here discharges Tag 01QJ's
binder.** The isomorphism proved below lives entirely on `Proj Γ_*(X, 𝓛)`: it compares two
associated sheaves. Tag 01QJ's binder is a natural transformation
`tildeFunctor L ⟶ Scheme.Modules.pushforward f` — a morphism out of `M̃` for *every* `𝓕`,
naturally — and this file supplies none. See the "What is not done" section of
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistNormalization.lean`.

**The identification is not transported to the `𝒪_Y(n)` spelling.** `𝒪_Y(n)` in this repository
is `associatedModuleSheaf 𝒮 (Stacks.GradedModule.shiftedGrading (integerGrading 𝒮) n)`
(`Stacks.AlgebraicGeometry.ProjLargeDegreeSections`
`.twistingSheaf_eq_associatedModuleSheaf_shiftedGrading`),
whose graded module is the section *ring* with its integer grading, not
`Stacks.TwistedSections.twistModule (𝟙_ C) L`. Identifying those two is a further step, and it
is the one that would read the result below at `𝓕 = 𝒪_X` as `Γ_*(X, 𝓛, 𝓛^{⊗ n})~ ≅ 𝒪_Y(n)`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections sectionRing HasTrivialSelfBraiding)
open Stacks.TwistedSections

universe v u

namespace Stacks.SectionRingProjTheta

section Algebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] {F L : C}

/-! ### The two tensor powers are equal -/

omit [Preadditive C] in
/-- **Twisting by `m` and then by `n` is twisting by `m + n`, on the nose.**
`Stacks.TwistedSections.twistPow` recurses by tensoring with `L` on the right, and `m + n`
recurses on `n`, so the two objects are built by the same steps from the same base. -/
theorem twistPow_twistPow (F L : C) (m n : ℕ) :
    twistPow (twistPow F L m) L n = twistPow F L (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (· ⊗ L) ih

omit [Preadditive C] in
/-- **Twisting the monoidal unit by `n` copies of `L` is the `n`-th tensor power of `L`**, on the
nose. `Stacks.TensorPowers.natTensorPow` is the same recursion started at `𝟙_ C`, which is what
`Stacks.TwistedSections.twistPow (𝟙_ C) L` starts at.

So the graded module `Γ_*(X, 𝓛, 𝒪_X)` and the section ring `Γ_*(X, 𝓛)` have *equal* graded
pieces, degree by degree: `Stacks.GradedSections.powSections L n` is
`𝟙_ C ⟶ natTensorPow L n` and `Stacks.TwistedSections.twistSections (𝟙_ C) L n` is
`𝟙_ C ⟶ twistPow (𝟙_ C) L n`. Read at `𝓕 = 𝒪_X`, `twistShiftSheafIso` is therefore a statement
about `Γ_*(X, 𝓛, 𝓛^{⊗ n})`, which is the Remark's own instance; what it compares that with is
the shift of `Γ_*(X, 𝓛, 𝒪_X)`, and identifying *that* with `𝒪_Y(n)` is the step recorded as not
done above. -/
theorem twistPow_unit (L : C) (n : ℕ) :
    twistPow (𝟙_ C) L n = Stacks.TensorPowers.natTensorPow L n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (· ⊗ L) ih

/-! ### The comparison in a single degree -/

/-- **The comparison in degree `n`**: a twisted section of `𝓕 ⊗ 𝓛^{⊗ m}` of degree `n` read as a
twisted section of `𝓕` of degree `m + n`. By `twistPow_twistPow` the two types differ only by
the `eqToHom` of an equality of objects. -/
def twistShiftSection (m n : ℕ) (t : twistSections (twistPow F L m) L n) :
    twistSections F L (m + n) :=
  t ≫ eqToHom (twistPow_twistPow F L m n)

/-- The comparison in degree `n` sends the zero section to zero. -/
@[simp] theorem twistShiftSection_zero (m n : ℕ) :
    twistShiftSection (F := F) (L := L) m n 0 = 0 := by
  rw [twistShiftSection, Limits.zero_comp]

/-- The comparison in degree `n` is additive. -/
theorem twistShiftSection_add (m n : ℕ) (t t' : twistSections (twistPow F L m) L n) :
    twistShiftSection m n (t + t') =
      twistShiftSection (F := F) (L := L) m n t + twistShiftSection m n t' := by
  rw [twistShiftSection, twistShiftSection, twistShiftSection, Preadditive.add_comp]

/-- The comparison in degree `n`, as an additive map. -/
def twistShiftSectionHom (m n : ℕ) :
    twistSections (twistPow F L m) L n →+ twistSections F L (m + n) where
  toFun := twistShiftSection m n
  map_zero' := twistShiftSection_zero m n
  map_add' := twistShiftSection_add m n

/-- The additive map `twistShiftSectionHom m n` is given by `twistShiftSection m n`. -/
@[simp] theorem twistShiftSectionHom_apply (m n : ℕ)
    (t : twistSections (twistPow F L m) L n) :
    twistShiftSectionHom (F := F) (L := L) m n t = twistShiftSection m n t := rfl

/-- The comparison in degree `n` is injective: it is composition with an isomorphism. -/
theorem twistShiftSection_eq_zero_iff (m n : ℕ)
    (t : twistSections (twistPow F L m) L n) :
    twistShiftSection (F := F) (L := L) m n t = 0 ↔ t = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, twistShiftSection_zero]⟩
  have h' := congrArg (· ≫ eqToHom (twistPow_twistPow F L m n).symm) h
  simpa [twistShiftSection] using h'

/-! ### Transport of the action -/

omit [Preadditive C] in
/-- **The comparison commutes with the right action by tensor powers of `L`.** Both
`Stacks.TwistedSections.actMap` recursions whisker on the right by `L`, so the single `eqToHom`
of `twistPow_twistPow` passes through all of them at once. -/
theorem actMap_twistShiftSection (m n : ℕ) (t : twistSections (twistPow F L m) L n) :
    ∀ k : ℕ, actMap (twistShiftSection m n t) k =
      actMap t k ≫ eqToHom ((twistPow_twistPow F L m (n + k)).trans
        (congrArg (twistPow F L) (Nat.add_assoc m n k).symm))
  | 0 => rfl
  | k + 1 => by
      rw [actMap_succ, actMap_twistShiftSection m n t k, comp_whiskerRight,
        eqToHom_whiskerRight]
      rfl

/-- **The comparison is compatible with the action of the section ring on homogeneous
elements.** The two degree conventions — `Stacks.TwistedSections.gsmul` adds the scalar degree on
the left, the comparison adds the twist on the left of what is already there — differ by
`Nat.add_left_comm`, and that is the `Stacks.TwistedSections.twistCongr` in the statement. -/
theorem twistShiftSection_gsmul [(tensorRight L).Additive] [BraidedCategory C]
    [HasTrivialSelfBraiding L] {j n : ℕ} (m : ℕ) (a : powSections L j)
    (t : twistSections (twistPow F L m) L n) :
    twistShiftSection m (j + n) (gsmul a t) =
      twistCongr (Nat.add_left_comm j m n) (gsmul a (twistShiftSection m n t)) := by
  simp only [gsmul_def, twistCongr, actMap_twistShiftSection]
  simp only [twistShiftSection, Category.assoc, eqToHom_trans]

/-! ### The comparison of graded modules -/

/-- **The comparison `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ m}) ⟶ Γ_*(X, 𝓛, 𝓕)`, additively.** In degree `n` it is
`twistShiftSection`, landing in degree `m + n`. -/
def twistShiftHom (F L : C) (m : ℕ) :
    twistModule (twistPow F L m) L →+ twistModule F L :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (twistSections F L) (m + n)).comp (twistShiftSectionHom m n)

/-- On a homogeneous element of degree `n`, `twistShiftHom` is `twistShiftSection` in degree `n`,
landing in degree `m + n`. -/
@[simp] theorem twistShiftHom_of (m n : ℕ) (t : twistSections (twistPow F L m) L n) :
    twistShiftHom F L m (DirectSum.of (twistSections (twistPow F L m) L) n t) =
      DirectSum.of (twistSections F L) (m + n) (twistShiftSection m n t) :=
  DirectSum.toAddMonoid_of _ _ _

/-- Reindexing a twisted section along an equality of degrees does not change the element of the
direct sum it names. -/
theorem of_twistCongr {p q : ℕ} (h : p = q) (t : twistSections F L p) :
    DirectSum.of (twistSections F L) q (twistCongr h t) =
      DirectSum.of (twistSections F L) p t := by
  subst h
  rw [twistCongr_rfl]

variable [(tensorRight L).Additive] [BraidedCategory C] [HasTrivialSelfBraiding L]

/-- The comparison `twistShiftHom F L m` commutes with scalar multiplication by the section ring
`sectionRing L`. -/
theorem twistShiftHom_smul (m : ℕ) (r : sectionRing L)
    (x : twistModule (twistPow F L m) L) :
    twistShiftHom F L m (r • x) = r • twistShiftHom F L m x := by
  induction r using DirectSum.induction_on with
  | zero => rw [zero_smul, zero_smul, map_zero]
  | of j a =>
      induction x using DirectSum.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | of n t =>
          rw [of_smul_of, twistShiftHom_of, twistShiftHom_of, of_smul_of,
            twistShiftSection_gsmul, of_twistCongr]
      | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
  | add r s hr hs => rw [add_smul, map_add, hr, hs, add_smul]

/-- **The comparison `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ m}) ⟶ Γ_*(X, 𝓛, 𝓕)`, as a map of
`Γ_*(X, 𝓛)`-modules.** -/
def twistShiftLinearMap (F L : C) [(tensorRight L).Additive]
    [HasTrivialSelfBraiding L] (m : ℕ) :
    twistModule (twistPow F L m) L →ₗ[sectionRing L] twistModule F L where
  toFun := twistShiftHom F L m
  map_add' := map_add _
  map_smul' := twistShiftHom_smul m

/-- The underlying function of `twistShiftLinearMap F L m` is `twistShiftHom F L m`. -/
@[simp] theorem twistShiftLinearMap_apply (m : ℕ) (x : twistModule (twistPow F L m) L) :
    twistShiftLinearMap F L m x = twistShiftHom F L m x := rfl

/-! ### Degreewise behaviour -/

omit [BraidedCategory C] in
/-- The graded module of twisted sections is the nonnegative truncation: its grading is the
trivial subgroup in every negative degree, not only at `Int.negSucc`. -/
theorem moduleGrading_eq_bot_of_neg (F L : C) {i : ℤ} (hi : i < 0) :
    moduleGrading F L i = ⊥ := by
  obtain ⟨k⟩ | ⟨k⟩ := i
  · exact absurd hi (not_lt.mpr (Int.ofNat_nonneg k))
  · exact moduleGrading_negSucc k

/-- A homogeneous element of negative degree is zero. -/
private theorem eq_zero_of_mem_moduleGrading_neg {D : Type u} [Category.{v} D]
    [MonoidalCategory D] [Preadditive D] {G M : D} {i : ℤ} (hi : i < 0) {x : twistModule G M}
    (hx : x ∈ moduleGrading G M i) : x = 0 := by
  rwa [moduleGrading_eq_bot_of_neg _ _ hi, AddSubgroup.mem_bot] at hx

/-- Degree `n` of the shift by `m` is degree `k` when `m + n = k`. -/
private theorem shiftedGrading_moduleGrading_eq {D : Type u} [Category.{v} D]
    [MonoidalCategory D] [Preadditive D] {G M : D} {m n k : ℕ} (h : m + n = k) :
    Stacks.GradedModule.shiftedGrading (moduleGrading G M) (m : ℤ) (n : ℤ) =
      moduleGrading G M (k : ℤ) :=
  congrArg (moduleGrading G M) (by push_cast [← h]; ring)

/-- **The comparison is degree-preserving into the shift.** Degree `i` of
`Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ m})` goes to degree `i` of `Γ_*(X, 𝓛, 𝓕)(m)`, which is degree `i + m` of
`Γ_*(X, 𝓛, 𝓕)`. -/
theorem twistShiftLinearMap_mem (m : ℕ) (i : ℤ) (x : twistModule (twistPow F L m) L)
    (hx : x ∈ moduleGrading (twistPow F L m) L i) :
    twistShiftLinearMap F L m x ∈
      Stacks.GradedModule.shiftedGrading (moduleGrading F L) (m : ℤ) i := by
  rcases lt_or_ge i 0 with hneg | hpos
  · rw [eq_zero_of_mem_moduleGrading_neg hneg hx, map_zero]
    exact zero_mem _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    rw [moduleGrading_natCast] at hx
    obtain ⟨t, rfl⟩ := hx
    rw [twistShiftLinearMap_apply, twistShiftHom_of, shiftedGrading_moduleGrading_eq rfl,
      moduleGrading_natCast]
    exact Stacks.ExternalGrading.of_mem_summand _ _

/-- **The comparison is injective on homogeneous elements of every degree.** In a negative degree
the source is trivial, so there is nothing to prove; in degree `n ≥ 0` it is
`twistShiftSection_eq_zero_iff`. -/
theorem twistShiftLinearMap_injective_of_mem (m : ℕ) (i : ℤ)
    (x : twistModule (twistPow F L m) L) (hx : x ∈ moduleGrading (twistPow F L m) L i)
    (h : twistShiftLinearMap F L m x = 0) : x = 0 := by
  rcases lt_or_ge i 0 with hneg | hpos
  · exact eq_zero_of_mem_moduleGrading_neg hneg hx
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    rw [moduleGrading_natCast] at hx
    obtain ⟨t, rfl⟩ := hx
    rw [twistShiftLinearMap_apply, twistShiftHom_of] at h
    have ht : twistShiftSection (F := F) (L := L) m n t = 0 := by
      have := congrArg (fun z : twistModule F L => z (m + n)) h
      simpa using this
    rw [(twistShiftSection_eq_zero_iff m n t).mp ht, map_zero]

/-- **The comparison is surjective onto the homogeneous elements of every nonnegative degree of
the shift.** Degree `i = n ≥ 0` of the shift is degree `n + m` of `Γ_*(X, 𝓛, 𝓕)`, and every
twisted section of that degree is the image of one of degree `n` for `𝓕 ⊗ 𝓛^{⊗ m}`. -/
theorem exists_mem_twistShiftLinearMap_eq (m : ℕ) (i : ℤ) (hi : 0 ≤ i) (y : twistModule F L)
    (hy : y ∈ Stacks.GradedModule.shiftedGrading (moduleGrading F L) (m : ℤ) i) :
    ∃ x : twistModule (twistPow F L m) L,
      x ∈ moduleGrading (twistPow F L m) L i ∧ twistShiftLinearMap F L m x = y := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rw [shiftedGrading_moduleGrading_eq (Nat.add_comm m n), moduleGrading_natCast] at hy
  obtain ⟨s, rfl⟩ := hy
  refine ⟨DirectSum.of (twistSections (twistPow F L m) L) n
    (twistCongr (Nat.add_comm n m) s ≫ eqToHom (twistPow_twistPow F L m n).symm),
    Stacks.ExternalGrading.of_mem_summand _ _, ?_⟩
  rw [twistShiftLinearMap_apply, twistShiftHom_of]
  refine .trans (congrArg (DirectSum.of (twistSections F L) (m + n)) ?_)
    (of_twistCongr (Nat.add_comm n m) s)
  rw [twistShiftSection, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-! ### The graded-module statement is false -/

omit [(tensorRight L).Additive] [BraidedCategory C] [HasTrivialSelfBraiding L] in
/-- **The identification fails as a statement about graded modules, and exactly where.** For
`m + 1 ≥ 1` the degree `-1` piece of `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ (m+1)})` is trivial — the module is
the nonnegative truncation — while the degree `-1` piece of the shift of `Γ_*(X, 𝓛, 𝓕)` is the
degree `m` piece of `Γ_*(X, 𝓛, 𝓕)`, which contains the nonzero element named by any nonzero
twisted section of degree `m`. So the two graded modules are not isomorphic in degree `-1`, and
`Stacks.Monoidal.ModuleSystem.powShiftEquiv` cannot be instantiated to say that they are. -/
theorem moduleGrading_shift_neg_one (m : ℕ) (t : twistSections F L m) (ht : t ≠ 0) :
    moduleGrading (twistPow F L (m + 1)) L (-1) = ⊥ ∧
      Stacks.GradedModule.shiftedGrading (moduleGrading F L) ((m : ℤ) + 1) (-1) ≠ ⊥ := by
  refine ⟨moduleGrading_negSucc 0, fun hbot => ht ?_⟩
  have hidx : (-1 : ℤ) + ((m : ℤ) + 1) = ((m : ℕ) : ℤ) := by ring
  have hmem : DirectSum.of (twistSections F L) m t ∈
      Stacks.GradedModule.shiftedGrading (moduleGrading F L) ((m : ℤ) + 1) (-1) := by
    show DirectSum.of (twistSections F L) m t ∈
      moduleGrading F L ((-1 : ℤ) + ((m : ℤ) + 1))
    rw [hidx, moduleGrading_natCast]
    exact Stacks.ExternalGrading.of_mem_summand _ _
  rw [hbot, AddSubgroup.mem_bot] at hmem
  have := congrArg (fun z : twistModule F L => z m) hmem
  simpa using this

end Algebra

/-! ### The identification at the level it holds at: the associated sheaves on `Proj` -/

section Sheaf

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] {F L : C}
  [(tensorRight L).Additive] [BraidedCategory C] [HasTrivialSelfBraiding L]

/-- **The morphism of associated sheaves on `Proj Γ_*(X, 𝓛)` induced by the comparison.** Its
source is `(Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ m}))~` and its target is `(Γ_*(X, 𝓛, 𝓕)(m))~`. -/
def twistShiftSheafMap (F L : C) [(tensorRight L).Additive]
    [HasTrivialSelfBraiding L] (m : ℕ) :
    _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf
        (Stacks.TwistedSections.sectionGrading L) (moduleGrading (twistPow F L m) L) ⟶
      _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf
        (Stacks.TwistedSections.sectionGrading L)
        (Stacks.GradedModule.shiftedGrading (moduleGrading F L) (m : ℤ)) :=
  Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap
    (Stacks.TwistedSections.sectionGrading L) (moduleGrading (twistPow F L m) L)
    (Stacks.GradedModule.shiftedGrading (moduleGrading F L) (m : ℤ))
    (twistShiftLinearMap F L m) (twistShiftLinearMap_mem m)

open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
  (isIso_associatedModuleSheafMap_of_eventually_bijective) in
/-- **Stacks Tag 01QK's "obvious identification", at the level at which it is true.** The
comparison `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ m}) ⟶ Γ_*(X, 𝓛, 𝓕)(m)` is bijective in every degree `≥ 0` — it
is injective in every degree whatever, and surjective from degree `0` on — so the morphism it
induces on associated sheaves over `Proj Γ_*(X, 𝓛)` is an isomorphism. The finitely many degrees
`-m ≤ i ≤ -1` where it is not surjective are invisible to the associated sheaf. -/
theorem isIso_twistShiftSheafMap (m : ℕ) : IsIso (twistShiftSheafMap F L m) :=
  isIso_associatedModuleSheafMap_of_eventually_bijective
    (Stacks.TwistedSections.sectionGrading L) (moduleGrading (twistPow F L m) L)
    (Stacks.GradedModule.shiftedGrading (moduleGrading F L) (m : ℤ))
    (twistShiftLinearMap F L m) (twistShiftLinearMap_mem m) (N₀ := 0)
    (fun j _ x hx h => twistShiftLinearMap_injective_of_mem m j x hx h)
    (fun j hj y hy => exists_mem_twistShiftLinearMap_eq m j hj y hy)

/-- `isIso_twistShiftSheafMap` as an isomorphism:
`(Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ m}))~ ≅ (Γ_*(X, 𝓛, 𝓕)(m))~` on `Proj Γ_*(X, 𝓛)`. -/
def twistShiftSheafIso (F L : C) [(tensorRight L).Additive]
    [HasTrivialSelfBraiding L] (m : ℕ) :
    _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf
        (Stacks.TwistedSections.sectionGrading L) (moduleGrading (twistPow F L m) L) ≅
      _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf
        (Stacks.TwistedSections.sectionGrading L)
        (Stacks.GradedModule.shiftedGrading (moduleGrading F L) (m : ℤ)) :=
  haveI := isIso_twistShiftSheafMap (F := F) (L := L) m
  asIso (twistShiftSheafMap F L m)

end Sheaf

end Stacks.SectionRingProjTheta

end
