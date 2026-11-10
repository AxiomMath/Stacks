module

import Mathlib.Tactic.Push
import Mathlib.Tactic.LinearCombination

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Degree-zero localization of a graded ring and of a graded module

Let `R` be a commutative ring, let `S = ⨁_{d ≥ 0} S_d` be a graded `R`-algebra (a graded ring
together with a structure map `R → S_0`, so that each `S_d` is an `R`-module), and fix a
homogeneous element `f ∈ S_+` of degree `d ≥ 1`.  Then `S_(f)` denotes the degree-`0` part of
the localization `S_f = S[1/f]`, and for a graded `S`-module `M = ⨁_{n ∈ ℤ} M_n` the object
`M_(f)` denotes the degree-`0` part of `M_f = M ⊗_S S_f`, i.e. the set of fractions `x / f^n`
with `x ∈ M` homogeneous of degree `n * d`.

## Main statements

* `homogeneousLocalization_away_finiteType`: if `S` is of finite type over `R`, then so is `S_(f)`.
* `moduleLocalization_away_finite`: if moreover `M` is a finite graded `S`-module, then `M_(f)` is
  a finite `S_(f)`-module.

## Conventions

* "Ring" means commutative ring with `1`; "of finite type over `R`" means finitely generated as an
  `R`-algebra (`Algebra.FiniteType R _`), and a "finite `S`-module" means finitely generated as an
  `S`-module (`Module.Finite S _`).
* The graded ring `S` is graded by `ℕ` (degrees `≥ 0`) while a graded module `M` is graded by `ℤ`
  (all integers).  This matches the index convention of `HomogeneousLocalization` in Mathlib.
* The hypothesis that `f ∈ S_+` is homogeneous guarantees `deg f = d ≥ 1`.

## Formalization notes

The grading of the `R`-algebra `S` is a family `𝒜 : ℕ → Submodule R S` carrying a `GradedAlgebra 𝒜`
instance, which packages `S = ⨁_d 𝒜 d`, `1 ∈ 𝒜 0` and `𝒜 i * 𝒜 j ⊆ 𝒜 (i + j)`.  Because each `𝒜 i`
is an `R`-submodule and `1 ∈ 𝒜 0`, the structure map `r ↦ algebraMap R S r` automatically lands in
`𝒜 0 = S_0`.

A graded `S`-module `M = ⨁_{n ∈ ℤ} M_n` is a family `ℳ : ℤ → Submodule R M` together with
`DirectSum.Decomposition ℳ` (expressing `M = ⨁_n ℳ n`) and `SetLike.GradedSMul 𝒜 ℳ` (the
compatibility `𝒜 i · ℳ j ⊆ ℳ (i +ᵥ j)`); this is the setup used by Mathlib's
`HomogeneousSubmodule 𝒜 ℳ`.  Since `𝒜` is indexed by `ℕ` and `ℳ` by `ℤ`, `SetLike.GradedSMul`
requires a `VAdd ℕ ℤ`, which Mathlib does not provide; we supply the canonical one,
`n +ᵥ z = (n : ℤ) + z`, as a `local instance`, so that the compatibility reads
`S_i · M_j ⊆ M_{i + j}`.

`S_(f)` is `HomogeneousLocalization.Away 𝒜 f`, which carries a canonical
`Algebra (𝒜 0) (Away 𝒜 f)` structure (`g ↦ g/1`); composing the structure map `R → 𝒜 0` with it
gives the `R`-algebra structure on `S_(f)`.  `M_f` is `LocalizedModule (Submonoid.powers f) M`,
which Mathlib equips with a module structure over `Localization (powers f) = S_f`; since `S_(f)` is
a subring of `S_f`, restriction of scalars makes `M_f` a module over `S_(f)`.

`M_(f)` is realized as `MLoc`, the `S_(f)`-submodule of `M_f` *spanned* by the degree-`0` fractions
`x / f^n` with `x ∈ ℳ (n • d)`.  Taking the span makes `MLoc` a well-formed `S_(f)`-submodule for
any choice of `f` and `d`, with no closure proof needed in the definition.  When `f` really is
homogeneous of degree `d ≥ 1` the span is faithful: the set of such fractions is then already an
`S_(f)`-submodule — closed under addition via common denominators,
`x/f^n + y/f^m = (x f^m + y f^n)/f^{n+m}`, with the degrees adding up precisely because
`deg f = d`, and closed under multiplication by the degree-`0` ring `S_(f)` — so its span equals
itself.  That faithfulness, which holds only under `f ∈ 𝒜 d` and `1 ≤ d`, is recorded as
`mem_MLoc_iff`.
-/

@[expose] public section

open DirectSum

/-- The `VAdd ℕ ℤ` used to express the grading compatibility
`S_i · M_j ⊆ M_{i + j}`: `n +ᵥ z = (n : ℤ) + z`.  We make this a `local instance`
(Mathlib does not provide a `VAdd ℕ ℤ`), so it is in scope only within this file
and does not pollute the global instance database. -/
local instance instVAddNatInt : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

@[simp]
theorem vadd_nat_int (n : ℕ) (z : ℤ) : n +ᵥ z = (n : ℤ) + z :=
  rfl

section GradedSetup

variable {R S M : Type*}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
-- The grading family of the graded `R`-algebra `S`.
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
-- The grading family of the graded `S`-module `M`: `DirectSum.Decomposition ℳ`
-- gives `M = ⨁_n ℳ n`, and `SetLike.GradedSMul 𝒜 ℳ` gives
-- `𝒜 i · ℳ j ⊆ ℳ (i +ᵥ j) = ℳ ((i : ℤ) + j)`.
variable (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
-- A homogeneous element `f ∈ S_d` of degree `d = deg f ≥ 1`.
variable (f : S) (d : ℕ)

/-- The structure map `R → S_0 = 𝒜 0` of the graded `R`-algebra `S`.  It sends
`r ↦ algebraMap R S r`, which lands in `𝒜 0` because `1 ∈ 𝒜 0` and `𝒜 0` is an
`R`-submodule. -/
@[ega "II 2.4.5" "partial"]
noncomputable def algMapRtoA0 : R →+* (𝒜 0) where
  toFun r :=
    ⟨algebraMap R S r, by
      rw [Algebra.algebraMap_eq_smul_one]
      exact (𝒜 0).smul_mem r SetLike.GradedOne.one_mem⟩
  map_one' := by
    ext; simp
  map_mul' a b := by
    ext; simp
  map_zero' := by
    ext; simp
  map_add' a b := by
    ext; simp

/-- The degree-zero localization `S_(f)`: for a graded ring `S` and a homogeneous
element `f` of degree `d ≥ 1`, the degree-`0` part of the localization
`S_f = S[1/f]`, which is Mathlib's `HomogeneousLocalization.Away 𝒜 f`. -/
@[ega "II 2.2.1",
  ega "II 2.2.7" "S_(f), special case",
  ega "II 8.2.1" "special case",
  sga "6 VI 2.3.2" "special case"]
abbrev SLoc : Type _ :=
  HomogeneousLocalization.Away 𝒜 f

-- The `R`-algebra structure on `S_(f)` is `HomogeneousLocalization.instAlgebra`, in
-- `StacksFrontier/RingTheory/HomogeneousLocalization/BaseAlgebra.lean`: the composite of the
-- structure map `R → 𝒜 0` with the canonical algebra map `𝒜 0 → S_(f)`, `g ↦ g/1`, which is the
-- unique `R`-algebra structure on `S_(f)` compatible with the canonical `𝒜 0`-algebra structure
-- (`HomogeneousLocalization.algebraMap_eq_fromZeroRingHom_comp`). It is stated there for an
-- arbitrary submonoid rather than only the powers of `f`, and its scalar action is Mathlib's
-- `HomogeneousLocalization.instSMul` definitionally, which a `RingHom.toAlgebra` here was not.

/-- The structure map `R → 𝒜 0` of `algMapRtoA0` agrees with Mathlib's canonical
`algebraMap R (𝒜 0)` (the `SetLike.GradeZero.instAlgebra` algebra map): both send
`r ↦ algebraMap R S r` (lifted to the subtype `𝒜 0`).  This lets us transfer
finite-type facts between the two descriptions. -/
theorem algMapRtoA0_eq : algMapRtoA0 𝒜 = algebraMap R (𝒜 0) := by
  ext r; rfl

/-- The scalar tower `R → 𝒜 0 → S`.  The `𝒜 0`-action on `S` is `x • s = ↑x * s`
(the subring action), and `r • x` in `𝒜 0` has carrier `algebraMap R S r * ↑x`,
so associativity is just `mul_assoc`/`smul_mul_assoc`. -/
instance instTowerRA0S : IsScalarTower R (𝒜 0) S := by
  refine ⟨fun r x s => ?_⟩
  have e1 : (r • x) • s = ((r • x : 𝒜 0) : S) * s := smul_eq_mul _ _
  have e2 : x • s = (x : S) * s := smul_eq_mul _ _
  rw [e1, e2]
  have e3 : ((r • x : 𝒜 0) : S) = r • (x : S) := rfl
  rw [e3, smul_mul_assoc]

/-- The localized module `M_f = M[1/f]` (localization of `M` at the powers of
`f`); Mathlib makes it a module over `Localization (powers f) = S_f`. -/
@[ega "0 1.2.3", ega "I 1.3.1"]
abbrev MLocAll : Type _ :=
  LocalizedModule (Submonoid.powers f) M

/-- `M_f` is a module over `S_(f)`, by restriction of scalars along the
canonical ring homomorphism `S_(f) → S_f` (`HomogeneousLocalization.Away 𝒜 f` is
a subring of `Localization (powers f)`).  This uses Mathlib's existing module
instance `Module (Localization (powers f)) (LocalizedModule (powers f) M)`. -/
noncomputable instance instModuleSLocMLocAll : Module (SLoc 𝒜 f) (MLocAll f (M := M)) :=
  Module.compHom (LocalizedModule (Submonoid.powers f) M)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization (Submonoid.powers f)))

/-- The degree-`0` fraction `x / f^n` of `M_f`, for `x : M`. -/
noncomputable def deg0frac (n : ℕ) (x : M) : MLocAll f (M := M) :=
  LocalizedModule.mk x (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f)

/-- The degree-zero localization `M_(f)`: the degree-`0` part of `M_f`, i.e. the
set of fractions `x / f^n` with `x ∈ M` homogeneous of degree `n * d`
(`x ∈ ℳ (n • d)`).  It is defined as the `S_(f)`-submodule of `M_f` *spanned* by
these degree-`0` fractions, so that it is a well-formed submodule for any `f, d`.

When `f` is genuinely homogeneous of degree `d ≥ 1`, this span is faithful: it
equals exactly the set of such fractions.  That faithfulness — which holds only
under those homogeneity hypotheses — is recorded by `mem_MLoc_iff`. -/
@[ega "II 2.2.1",
  ega "II 2.2.7" "M_(T) for T = {f^n",
  ega "II 2.5.1",
  ega "II 8.2.1" "special case", sga "6 VI 2.3.2" "special case"]
noncomputable def MLoc : Submodule (SLoc 𝒜 f) (MLocAll f (M := M)) :=
  Submodule.span (SLoc 𝒜 f) {y | ∃ (n : ℕ) (x : M), x ∈ ℳ (n • (d : ℤ)) ∧ y = deg0frac f n x}

set_option linter.unusedSectionVars false in
/-- The defining degree-`0` fractions belong to `M_(f)`. -/
theorem deg0frac_mem_MLoc (n : ℕ) (x : M) (hx : x ∈ ℳ (n • (d : ℤ))) :
    deg0frac f n x ∈ MLoc 𝒜 ℳ f d :=
  Submodule.subset_span ⟨n, x, hx, rfl⟩

/-- **Correctness characterization of `M_(f)`.**
Assuming `f` is homogeneous of degree `d` (`hf : f ∈ 𝒜 d`) with `d ≥ 1`
(`hd : 1 ≤ d`), an element of `M_f` lies in `M_(f)` if and only if it is a
degree-`0` fraction `x / f^n` with `x` homogeneous of degree `n * d`.  This
records that under the intended homogeneity hypotheses the `S_(f)`-span used to
define `MLoc` is faithful: the set of such fractions is then already an
`S_(f)`-submodule (closed under common-denominator addition and under
scalar multiplication by the degree-`0` ring `S_(f)`), so its span equals
itself.  The hypotheses `hf`, `hd` are necessary: faithfulness can fail when `f`
is not homogeneous of degree `d ≥ 1`. -/
@[ega "II 2.2.1", ega "II 2.2.7" "special case", ega "II 2.5.1", ega "II 8.2.1" "partial"]
theorem mem_MLoc_iff (hf : f ∈ 𝒜 d) (y : MLocAll f (M := M)) :
    y ∈ MLoc 𝒜 ℳ f d ↔ ∃ (n : ℕ) (x : M), x ∈ ℳ (n • (d : ℤ)) ∧ y = deg0frac f n x := by
  have hsmul_mem {a : S} {x : M} {m n : ℕ} (ha : a ∈ 𝒜 (m • d)) (hx : x ∈ ℳ (n • (d : ℤ))) :
      a • x ∈ ℳ ((m + n) • (d : ℤ)) := by
    have := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ha hx
    rwa [show (m • d : ℕ) +ᵥ (n • (d : ℤ)) = (m + n) • (d : ℤ) by
      simp only [vadd_nat_int, nsmul_eq_mul]
      push_cast
      ring] at this
  refine ⟨fun hy => ?_, fun ⟨n, x, hx, h⟩ => h ▸ deg0frac_mem_MLoc 𝒜 ℳ f d n x hx⟩
  refine Submodule.span_induction (p := fun z _ =>
    ∃ (n : ℕ) (x : M), x ∈ ℳ (n • (d : ℤ)) ∧ z = deg0frac f n x) (fun _ hz => hz) ?_ ?_ ?_ hy
  · exact ⟨0, 0, zero_mem _, by simp [deg0frac]⟩
  · rintro z w _ _ ⟨n, x, hx, rfl⟩ ⟨m, y', hy', rfl⟩
    refine ⟨n + m, (f ^ m) • x + (f ^ n) • y', add_mem ?_
      (hsmul_mem (SetLike.pow_mem_graded n hf) hy'), ?_⟩
    · rw [add_comm n m]
      exact hsmul_mem (SetLike.pow_mem_graded m hf) hx
    · change deg0frac f n x + deg0frac f m y' = deg0frac f (n + m) _
      unfold deg0frac
      rw [LocalizedModule.mk_add_mk]
      exact congrArg _ (Subtype.ext (pow_add f _ _).symm)
  · rintro c z _ ⟨n, x, hx, rfl⟩
    obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf c
    refine ⟨m + n, a • x, hsmul_mem ha hx, ?_⟩
    change (HomogeneousLocalization.Away.mk 𝒜 hf m a ha).val • deg0frac f n x =
      deg0frac f (m + n) (a • x)
    rw [HomogeneousLocalization.Away.val_mk]
    unfold deg0frac
    rw [LocalizedModule.mk_smul_mk]
    exact congrArg _ (Subtype.ext (pow_add f _ _).symm)

/-- The degree-`0` subring `S_0 = 𝒜 0` of a graded `R`-algebra of finite type is
itself of finite type over `R`.

*Informal proof.*  Since `S` is a finitely generated `R`-algebra, by
`GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous` we may choose a finite
set of **homogeneous** generators `g₁, …, gₙ`, with `gᵢ ∈ 𝒜 δᵢ`, that generate
`S` as an `𝒜 0`-algebra (and a fortiori, together with the image of `R`, as an
`R`-algebra).  A monomial `g₁^{a₁} ⋯ gₙ^{aₙ}` is homogeneous of degree
`Σ aᵢ δᵢ`, and lies in `𝒜 0` iff `Σ aᵢ δᵢ = 0`.  Because every `δᵢ ≥ 0`, this
forces `aᵢ = 0` for every `i` with `δᵢ > 0`.  Hence the degree-`0` part `𝒜 0` is
spanned over `R` by the monomials in the generators of degree `0` alone, i.e.
`𝒜 0 = R[gᵢ : δᵢ = 0]`, the `R`-subalgebra generated by the finitely many
degree-`0` generators.  Therefore `𝒜 0` is a finitely generated `R`-algebra. -/
theorem gradeZero_finiteType [Algebra.FiniteType R S] : Algebra.FiniteType R (𝒜 0) := by
  -- The degree-0 projection `S →+* 𝒜 0` is a *surjective ring homomorphism*
  -- precisely because the grading is ℕ-indexed (`CanonicallyOrderedAdd`): a
  -- product of positive-degree elements has no degree-0 component.  Composing the
  -- finite-type structure map `R → S` with this surjection gives a finite-type map
  -- `R → 𝒜 0`, and that composite is exactly `algebraMap R (𝒜 0)`.
  have hRS : (algebraMap R S).FiniteType := RingHom.finiteType_algebraMap.mpr ‹_›
  have hsurj : Function.Surjective (GradedRing.projZeroRingHom' 𝒜) :=
    GradedRing.projZeroRingHom'_surjective 𝒜
  have hcomp : ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap R S)).FiniteType :=
    RingHom.FiniteType.comp_surjective hRS hsurj
  have heq : (GradedRing.projZeroRingHom' 𝒜).comp (algebraMap R S) = algebraMap R (𝒜 0) := by
    ext r
    change
      (GradedRing.projZeroRingHom' 𝒜 (algebraMap R S r) : S) = ((algebraMap R (𝒜 0) r : 𝒜 0) : S)
    rw [GradedRing.coe_projZeroRingHom'_apply]
    have hmem : algebraMap R S r ∈ 𝒜 0 := SetLike.algebraMap_mem_graded 𝒜 r
    have hproj : GradedRing.projZeroRingHom 𝒜 (algebraMap R S r) = algebraMap R S r := by
      rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_same 𝒜 hmem]
    rw [hproj]
    rfl
  rw [heq] at hcomp
  exact RingHom.finiteType_algebraMap.mp hcomp

end GradedSetup
