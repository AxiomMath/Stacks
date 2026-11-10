module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientTwistMap

/-!
# The twisting-down maps `𝒪_X(q) ⟶ 𝒪_X(q')` of the blowup, for all `q' ≤ q`

Let `A` be a commutative ring, `I ⊆ A` an ideal, `S = ⨁_{n ≥ 0} Iⁿ` the Rees algebra and
`X = Proj(S)` the blowup of `Spec(A)` in `I`. `BitUniformityIII/AmbientTwistMap.lean` builds the
single step `𝒪_X(q+1) ⟶ 𝒪_X(q)`, which is division by `X` on the Rees model. The cohomological
clauses of [Stacks, Tag 0GAA] need the map for an arbitrary pair `q' ≤ q` of *integers*, together
with its functoriality.

## Why the family is not built by iterating the single step

`Stacks.Blowup.twistShiftMap I t : 𝒪_X(t+1) ⟶ 𝒪_X(t)` has `t + 1` in its source, so a chain of
`k` of them has source `𝒪_X(q' + k)` with `k` a numeral or a variable *added to `q'`*: there is
no chain whose source is a free variable `q`. Passing from `q' ≤ q` to `q = q' + k` therefore
needs a transport along an equation between the integers indexing the twisting sheaves, and
`eqToHom` is not usable at this category — the unifier does not reconcile
`TopCat.Sheaf CommRingCat (ProjectiveSpectrum.top (reesGrading I))` with
`CategoryTheory.Sheaf (Opens.grothendieckTopology _) CommRingCat` inside the heartbeat budget.
An `ℕ`-indexed chain fares no better: `Nat.add` is not associative definitionally, so no general
composition law can even be stated for one.

So the family is built in one shot instead, and the integer arithmetic is confined to the
degree-preservation `Prop`s, where it is discharged by `omega` and nothing is transported:

* `Stacks.Blowup.reesTruncationDown I q q'` is the truncation of `S(q)` above `-q'` — the
  generalisation of `Stacks.Blowup.reesTruncation I t`, which it reproduces on the nose at
  `q = t + 1`, `q' = t` (`Stacks.Blowup.reesTruncationDown_succ`);
* `Stacks.Blowup.reesShiftDown I q q'` is `Polynomial.divX` iterated `(q - q').toNat` times — the
  generalisation of `Stacks.Blowup.reesShift I t`, which it reproduces at the same arguments
  (`Stacks.Blowup.reesShiftDown_succ`).

The truncation above `-q'` is exactly what makes the iterate `S`-linear: its elements are the
elements of `S` divisible by `X^{q-q'}` (`Stacks.Blowup.X_pow_dvd_of_mem_reesTruncationDown`),
and `divX^{k}` is `A[X]`-linear on the multiples of `X^k`.

## Main definitions

* `Stacks.Blowup.reesTruncationDown`: the truncation of `S(q)` above degree `-q'`.
* `Stacks.Blowup.reesShiftDown`: `divX^{q-q'}`, as an `S`-linear map out of that truncation.
* `Stacks.Blowup.twistDownMap`: **the map `𝒪_X(q) ⟶ 𝒪_X(q')` for `q' ≤ q`.**

## Main results

* `Stacks.Blowup.twistDownMap_succ`: **the family extends the single step** — at `q = t + 1`,
  `q' = t` it is `Stacks.Blowup.twistShiftMap I t`, so everything already proved about the
  ambient sequence of [Stacks, Tag 0GA7] applies to it.
* `Stacks.Blowup.twistDownMap_self`: the family is the identity at `q' = q`.
* `Stacks.Blowup.twistDownMap_comp`: **the family is functorial** —
  `twistDownMap q q' ≫ twistDownMap q' q'' = twistDownMap q q''`.

## Implementation notes

The composition law is proved by cancelling the comparison isomorphism of the truncation of
`S(q)` above `-q''` — the *smallest* of the three truncations involved — against both sides. Over
that truncation the two routes from `S(q)` to `S(q'')` become a square of honest degree-preserving
`S`-linear maps between submodules of `S`, namely the inclusion
`S(q)_{≥ -q''} ⊆ S(q)_{≥ -q'}` and the restriction of `divX^{q-q'}` to
`S(q)_{≥ -q''} → S(q')_{≥ -q''}`, and the law reduces by
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_comp` to
`divX^{q'-q''} ∘ divX^{q-q'} = divX^{q-q''}`, i.e. to `Function.iterate_add_apply` and one
`omega`. No morphism of sheaves is ever transported.

`associatedModuleSheafMap` takes the degree-preservation proof as an explicit argument, so
rewriting the linear map inside one needs a congruence lemma;
`Stacks.Blowup.associatedModuleSheafMap_congr_map` is it, and it is proved by `subst` followed by
proof irrelevance rather than by `eqToHom`.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGrading integerGrading
  homogeneousSubmodule associatedModuleSheaf)
open Stacks.GradedModule
open Stacks.GradedLocalization
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap
  associatedModuleSheafMap_comp)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
  (isIso_associatedModuleSheafMap_of_eventually_bijective)

universe u v w t

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace Stacks.Blowup

/-! ### Rewriting the linear map inside an induced sheaf morphism -/

section Congr

variable {S : Type u} {M : Type v} {N : Type v} {σ : Type w} {τ : Type t} {ρ : Type t}
  [CommRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [AddCommGroup M] [Module S M] [SetLike τ M] [AddSubgroupClass τ M]
  [AddCommGroup N] [Module S N] [SetLike ρ N] [AddSubgroupClass ρ N]
  (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]
  (𝒩 : ℤ → ρ) [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒮 𝒩]

omit [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] in
/-- The sheaf morphism induced by a degree-preserving linear map depends on the map alone: the
degree-preservation hypothesis is a `Prop`, so two proofs of it give the same morphism. This is
what lets a linear map be rewritten underneath `associatedModuleSheafMap` without an
`eqToHom`. -/
theorem associatedModuleSheafMap_congr_map {φ ψ : M →ₗ[S] N}
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (hψ : ∀ i (m : M), m ∈ 𝒨 i → ψ m ∈ 𝒩 i)
    (h : φ = ψ) :
    associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ = associatedModuleSheafMap 𝒮 𝒨 𝒩 ψ hψ := by
  subst h
  rfl

end Congr

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### Iterated division by `X` -/

/-- The coefficients of `divX^{k} p` are those of `p`, shifted by `k`. -/
theorem coeff_divX_iterate (k : ℕ) (p : A[X]) (m : ℕ) :
    (divX^[k] p).coeff m = p.coeff (m + k) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, ih, coeff_divX, Nat.add_assoc]

/-- Iterated division by `X` is additive. -/
theorem divX_iterate_add (k : ℕ) (p r : A[X]) :
    divX^[k] (p + r) = divX^[k] p + divX^[k] r := by
  ext m
  simp [coeff_divX_iterate]

/-- Iterated division by `X` sends the zero polynomial to zero. -/
@[simp]
theorem divX_iterate_zero (k : ℕ) : divX^[k] (0 : A[X]) = 0 := by
  ext m
  simp [coeff_divX_iterate]

/-- Dividing by `X` repeatedly keeps an element inside the Rees algebra. -/
theorem divX_iterate_mem_reesAlgebra (k : ℕ) {f : A[X]} (hf : f ∈ reesAlgebra I) :
    divX^[k] f ∈ reesAlgebra I := by
  induction k generalizing f with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (divX_mem_reesAlgebra I hf)

/-- A multiple of `X^{k+1}` has a quotient by `X` that is a multiple of `X^k`. -/
theorem X_pow_dvd_divX {k : ℕ} {p : A[X]} (hp : (X : A[X]) ^ (k + 1) ∣ p) :
    (X : A[X]) ^ k ∣ divX p := by
  rw [X_pow_dvd_iff] at hp ⊢
  intro d hd
  rw [coeff_divX]
  exact hp (d + 1) (by omega)

/-- **`divX^{k}` is `A[X]`-linear on the multiples of `X^k`.** This is the generalisation of
`Stacks.Blowup.divX_mul_of_coeff_zero` that the whole twisting-down family rests on: the single
step needs a vanishing constant term, and the `k`-fold step needs `k` vanishing coefficients,
which is divisibility by `X^k`. -/
theorem divX_iterate_mul_of_X_pow_dvd (k : ℕ) (c : A[X]) {p : A[X]}
    (hp : (X : A[X]) ^ k ∣ p) : divX^[k] (c * p) = c * divX^[k] p := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    have h0 : p.coeff 0 = 0 := X_pow_dvd_iff.mp hp 0 (by omega)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      divX_mul_of_coeff_zero c h0]
    exact ih (X_pow_dvd_divX hp)

/-- Iterated division by `X`, as a map of the Rees algebra to itself. It is additive always, and
`S`-linear on the truncations below. -/
def reesDivXIter (k : ℕ) (f : reesAlgebra I) : reesAlgebra I :=
  ⟨divX^[k] ((f : A[X])), divX_iterate_mem_reesAlgebra I k f.2⟩

/-- The underlying polynomial of `reesDivXIter I k f` is `divX^{k}` applied to that of `f`. -/
@[simp]
theorem coe_reesDivXIter (k : ℕ) (f : reesAlgebra I) :
    ((reesDivXIter I k f : reesAlgebra I) : A[X]) = divX^[k] ((f : A[X])) := rfl

/-! ### The truncation of `S(q)` above `-q'` -/

variable (q q' q'' : ℤ)

/-- **The truncation of the twist `S(q)` of the Rees algebra above degree `-q'`.** Its elements
are the elements of `S` divisible by `X^{q-q'}`, and it is where `divX^{q-q'}` becomes
`S`-linear.

At `q = t + 1`, `q' = t` this is `Stacks.Blowup.reesTruncation I t` on the nose. -/
abbrev reesTruncationDown : Submodule (reesAlgebra I) (reesAlgebra I) :=
  truncationAbove (reesGrading I) (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q')

/-- The grading of the truncation of `S(q)` above `-q'`. -/
abbrev reesTruncationDownGrading : ℤ → AddSubgroup (reesTruncationDown I q q') :=
  truncationAboveGrading (reesGrading I)
    (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q')

/-- **The generalisation is faithful**: at `q = t + 1` and `q' = t` the truncation of `S(q)`
above `-q'` is the truncation `Stacks.Blowup.reesTruncation I t` of `S(t+1)` above `-t` that the
single twisting-down step is built from — definitionally, not up to an isomorphism. -/
theorem reesTruncationDown_succ (t : ℤ) :
    reesTruncationDown I (t + 1) t = reesTruncation I t := rfl

/-- The grading of the truncation is faithful to the single step's too. -/
theorem reesTruncationDownGrading_succ (t : ℤ) :
    reesTruncationDownGrading I (t + 1) t = reesTruncationGrading I t := rfl

/-- **The truncation is the `S`-span of the homogeneous elements of degree `≥ -q'`.** This is
`Stacks.GradedModule.truncationAbove_eq_span` at the arguments the family uses; it is stated
separately because the truncation appears through the abbreviation, which `rw` does not see
through. -/
theorem reesTruncationDown_eq_span :
    reesTruncationDown I q q' = Submodule.span (reesAlgebra I) (⋃ j ∈ Set.Ici (-q'),
      (twistGrading (S := reesAlgebra I) (reesGrading I) q j : Set (reesAlgebra I))) :=
  truncationAbove_eq_span (reesGrading I)
    (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q')

/-- Truncating higher gives a smaller submodule: `S(q)_{≥ -q''} ⊆ S(q)_{≥ -q'}` for
`q'' ≤ q'`. -/
theorem reesTruncationDown_le (h : q'' ≤ q') :
    reesTruncationDown I q q'' ≤ reesTruncationDown I q q' :=
  fun _ hx i hi => hx i (by omega)

/-- **An element of the truncation of `S(q)` above `-q'` is divisible by `X^{q-q'}`.** The
homogeneous generators of degree `≥ -q'` have Rees degree `≥ q - q'`, so all their coefficients
below `q - q'` vanish, and divisibility survives the `S`-span. -/
theorem X_pow_dvd_of_mem_reesTruncationDown {f : reesAlgebra I}
    (hf : f ∈ reesTruncationDown I q q') :
    (X : A[X]) ^ (q - q').toNat ∣ ((f : A[X])) := by
  rcases le_or_gt (q - q') 0 with hk | hk
  · rw [show (q - q').toNat = 0 by omega, pow_zero]
    exact one_dvd _
  rw [reesTruncationDown_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, hj : -q' ≤ j, hzj⟩ := Set.mem_iUnion₂.mp hz
    have hzj' : z ∈ reesGrading I (j + q).toNat :=
      (mem_twistGrading_iff I (by omega) z).mp hzj
    exact X_pow_dvd_iff.mpr fun d hd => hzj' d (by omega)
  | zero => simp
  | add x y _ _ hx hy =>
    change (X : A[X]) ^ (q - q').toNat ∣ ((x : A[X]) + (y : A[X]))
    exact dvd_add hx hy
  | smul c x _ hx =>
    change (X : A[X]) ^ (q - q').toNat ∣ ((c : A[X]) * (x : A[X]))
    exact hx.mul_left _

/-- Below the cut `-q''` the truncation of `S(q)` is cut off at `q'`: `X^{q-q'}` still divides. -/
private theorem X_pow_dvd_of_mem_reesTruncationDown_of_le (h : q'' ≤ q') {f : reesAlgebra I}
    (hf : f ∈ reesTruncationDown I q q'') : (X : A[X]) ^ (q - q').toNat ∣ ((f : A[X])) :=
  dvd_trans (pow_dvd_pow (X : A[X]) (by omega)) (X_pow_dvd_of_mem_reesTruncationDown I q q'' hf)

/-! ### The iterate as an `S`-linear map out of the truncation -/

/-- **`divX^{q-q'}` as an `S`-linear map from the truncation of `S(q)` above `-q'` into `S`.**
This is the family of inclusions `I^{m} ⊆ I^{m-(q-q')}` read in the Rees model; it is linear
because its source consists of the multiples of `X^{q-q'}`.

At `q = t + 1`, `q' = t` it is `Stacks.Blowup.reesShift I t`. -/
def reesShiftDown : reesTruncationDown I q q' →ₗ[reesAlgebra I] reesAlgebra I where
  toFun f := reesDivXIter I (q - q').toNat (f : reesAlgebra I)
  map_add' _ _ := Subtype.ext (divX_iterate_add _ _ _)
  map_smul' _ f := Subtype.ext
    (divX_iterate_mul_of_X_pow_dvd _ _ (X_pow_dvd_of_mem_reesTruncationDown I q q' f.2))

/-- The underlying polynomial of `reesShiftDown I q q' f` is `divX^{(q - q').toNat}` applied to
that of `f`. -/
@[simp]
theorem coe_reesShiftDown (f : reesTruncationDown I q q') :
    ((reesShiftDown I q q' f : reesAlgebra I) : A[X]) =
      divX^[(q - q').toNat] (((f : reesAlgebra I) : A[X])) := rfl

/-- **The generalisation is faithful**: at `q = t + 1` and `q' = t` the iterate is the single
division by `X` that `Stacks.Blowup.reesShift I t` is. -/
theorem reesShiftDown_succ (t : ℤ) : reesShiftDown I (t + 1) t = reesShift I t := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  change divX^[((t + 1) - t).toNat] (((f : reesAlgebra I) : A[X])) =
    divX (((f : reesAlgebra I) : A[X]))
  rw [show ((t + 1) - t).toNat = 1 by omega]
  rfl

/-- `divX^{q-q'}` carries a homogeneous element of `S(q)` of degree `i` to a homogeneous element
of `S(q')` of the same degree: both pieces are the Rees pieces of degrees `i + q` and `i + q'`,
and the iterate drops the monomial degree by exactly `q - q'`. -/
theorem reesDivXIter_mem_twistGrading (hq : q' ≤ q) {i : ℤ} (hi : 0 ≤ i + q')
    {z : reesAlgebra I} (hz : z ∈ twistGrading (S := reesAlgebra I) (reesGrading I) q i) :
    reesDivXIter I (q - q').toNat z ∈
      twistGrading (S := reesAlgebra I) (reesGrading I) q' i := by
  have hz' : z ∈ reesGrading I (i + q).toNat := (mem_twistGrading_iff I (by omega) z).mp hz
  refine (mem_twistGrading_iff I hi _).mpr fun m hm => ?_
  rw [coe_reesDivXIter, coeff_divX_iterate]
  exact hz' (m + (q - q').toNat) (by omega)

/-- `divX^{q-q'}` carries the degree-`i` piece of the truncation of `S(q)` above `-q''` into the
degree-`i` piece of `S(q')`, for `q'' ≤ q' ≤ q`: in a kept degree `i ≥ -q''` the source piece is
`S_{i+q}`; below the cut it is zero. -/
private theorem reesDivXIter_mem_twistGrading_of_mem_truncationAboveGrading (hq'' : q'' ≤ q')
    (hq : q' ≤ q) (i : ℤ) (f : reesTruncationDown I q q'')
    (hf : f ∈ reesTruncationDownGrading I q q'' i) :
    reesDivXIter I (q - q').toNat (f : reesAlgebra I) ∈
      twistGrading (S := reesAlgebra I) (reesGrading I) q' i := by
  have hf₀ : f ∈ truncationAboveGrading (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q'') i := hf
  rcases lt_or_ge i (-q'') with hi | hi
  · rw [truncationAboveGrading_eq_bot (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q'') hi, AddSubgroup.mem_bot] at hf₀
    rw [hf₀, Submodule.coe_zero, show reesDivXIter I (q - q').toNat (0 : reesAlgebra I) = 0 from
      Subtype.ext (divX_iterate_zero _)]
    exact zero_mem _
  · exact reesDivXIter_mem_twistGrading I q q' hq (by omega)
      ((mem_truncationAboveGrading_iff (reesGrading I)
        (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q'') i f).mp hf₀)

/-- **`divX^{q-q'}` is degree-preserving**, from the grading of the truncation of `S(q)` above
`-q'` into that of `S(q')`. -/
theorem reesShiftDown_mem_twistGrading (hq : q' ≤ q) (i : ℤ) (f : reesTruncationDown I q q')
    (hf : f ∈ reesTruncationDownGrading I q q' i) :
    reesShiftDown I q q' f ∈ twistGrading (S := reesAlgebra I) (reesGrading I) q' i :=
  reesDivXIter_mem_twistGrading_of_mem_truncationAboveGrading I q q' q' le_rfl hq i f hf

/-! ### The twisting-down map -/

/-- **The inclusion of the truncation into `S(q)` induces an isomorphism of associated
sheaves.** It is bijective in every degree `≥ -q'`: injective because it is an inclusion, and
surjective because a homogeneous element of a kept degree already lies in the truncation. -/
theorem isIso_reesTruncationDownComparison :
    IsIso (associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q')
      (twistGrading (S := reesAlgebra I) (reesGrading I) q) (reesTruncationDown I q q').subtype
      (truncationAbove_subtype_mem (reesGrading I)
        (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q'))) :=
  isIso_associatedModuleSheafMap_of_eventually_bijective
    (reesGrading I) (reesTruncationDownGrading I q q')
    (twistGrading (S := reesAlgebra I) (reesGrading I) q) (reesTruncationDown I q q').subtype
    (truncationAbove_subtype_mem (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q'))
    (N₀ := -q')
    (fun _ _ _ _ h => eq_zero_of_truncationAbove_subtype_eq_zero (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q') h)
    (fun _j hj _ hm => exists_mem_truncationAboveGrading (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q') hj hm)

/-- **The comparison `(S(q)_{≥ -q'})~ ≅ 𝒪_X(q)`.** -/
def reesTruncationDownComparison :
    associatedModuleSheaf (reesGrading I) (reesTruncationDownGrading I q q') ≅
      twistingSheaf (reesGrading I) q :=
  haveI := isIso_reesTruncationDownComparison I q q'
  asIso (associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q')
    (twistGrading (S := reesAlgebra I) (reesGrading I) q) (reesTruncationDown I q q').subtype
    (truncationAbove_subtype_mem (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q')))

/-- The forward direction of the comparison isomorphism is the induced map itself. -/
theorem reesTruncationDownComparison_hom :
    (reesTruncationDownComparison I q q').hom =
      associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q')
        (twistGrading (S := reesAlgebra I) (reesGrading I) q)
        (reesTruncationDown I q q').subtype
        (truncationAbove_subtype_mem (reesGrading I)
          (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q')) := rfl

/-- **The canonical map `𝒪_X(q) ⟶ 𝒪_X(q')` on the blowup, for any pair of integers
`q' ≤ q`**: the comparison `(S(q)_{≥ -q'})~ ≅ 𝒪_X(q)` inverted, followed by the map
`divX^{q-q'}` induces. No generator of the centre is chosen anywhere. -/
def twistDownMap (hq : q' ≤ q) :
    twistingSheaf (reesGrading I) q ⟶ twistingSheaf (reesGrading I) q' :=
  (reesTruncationDownComparison I q q').inv ≫
    associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q')
      (twistGrading (S := reesAlgebra I) (reesGrading I) q') (reesShiftDown I q q')
      (reesShiftDown_mem_twistGrading I q q' hq)

/-- The defining factorisation of `twistDownMap`. The definition is `irreducible`, for the reason
`Stacks.Blowup.twistShiftMap` is: with the comparison isomorphism exposed, the unifier spends its
whole heartbeat budget on `isDefEq` in any goal mentioning the map inside a `≫`. This lemma is
the only way in. -/
theorem twistDownMap_eq (hq : q' ≤ q) :
    twistDownMap I q q' hq =
      (reesTruncationDownComparison I q q').inv ≫
        associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q')
          (twistGrading (S := reesAlgebra I) (reesGrading I) q') (reesShiftDown I q q')
          (reesShiftDown_mem_twistGrading I q q' hq) := rfl

attribute [irreducible] twistDownMap

/-- Precomposing `twistDownMap` with the comparison isomorphism leaves the map `divX^{q-q'}`
induces; this avoids ever computing the inverse of the comparison. -/
theorem comparison_hom_comp_twistDownMap (hq : q' ≤ q) :
    (reesTruncationDownComparison I q q').hom ≫ twistDownMap I q q' hq =
      associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q')
        (twistGrading (S := reesAlgebra I) (reesGrading I) q') (reesShiftDown I q q')
        (reesShiftDown_mem_twistGrading I q q' hq) := by
  simp only [twistDownMap_eq, Iso.hom_inv_id_assoc]

/-- **The family extends the single step of [Stacks, Tag 0GA7]**: at `q = t + 1`, `q' = t` the
twisting-down map is `Stacks.Blowup.twistShiftMap I t`. Both the truncation and its grading agree
definitionally, and the two linear maps agree by `Stacks.Blowup.reesShiftDown_succ`; the
degree-preservation proofs are `Prop`s, so they need no comparison. -/
theorem twistDownMap_succ (t : ℤ) (hq : t ≤ t + 1) :
    twistDownMap I (t + 1) t hq = twistShiftMap I t :=
  (twistDownMap_eq I (t + 1) t hq).trans
    ((whisker_eq (reesTruncationDownComparison I (t + 1) t).inv
        (associatedModuleSheafMap_congr_map (reesGrading I)
          (reesTruncationDownGrading I (t + 1) t)
          (twistGrading (S := reesAlgebra I) (reesGrading I) t)
          (reesShiftDown_mem_twistGrading I (t + 1) t hq)
          (reesShift_mem_twistGrading I t) (reesShiftDown_succ I t))).trans
      (twistShiftMap_eq I t).symm)

/-- The twisting-down map at `q' = q` is the identity: `divX^{0}` is the identity and the
truncation of `S(q)` above `-q` is the whole of `S(q)`, so both factors of the definition are the
same isomorphism. -/
theorem twistDownMap_self : twistDownMap I q q le_rfl = 𝟙 _ := by
  have hmap : (reesShiftDown I q q) = (reesTruncationDown I q q).subtype := by
    refine LinearMap.ext fun f => Subtype.ext ?_
    rw [coe_reesShiftDown, show (q - q).toNat = 0 by omega]
    rfl
  have h1 : associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q) (reesShiftDown I q q)
      (reesShiftDown_mem_twistGrading I q q le_rfl) =
      (reesTruncationDownComparison I q q).hom :=
    (associatedModuleSheafMap_congr_map (reesGrading I) (reesTruncationDownGrading I q q)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q)
      (reesShiftDown_mem_twistGrading I q q le_rfl)
      (truncationAbove_subtype_mem (reesGrading I)
        (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q)) hmap).trans
      (reesTruncationDownComparison_hom I q q).symm
  exact (twistDownMap_eq I q q le_rfl).trans
    ((whisker_eq (reesTruncationDownComparison I q q).inv h1).trans
      (reesTruncationDownComparison I q q).inv_hom_id)

/-! ### Functoriality -/

/-- `divX^{q-q'}` carries the truncation of `S(q)` above `-q''` into the truncation of `S(q')`
above `-q''`. The homogeneous generators of degree `≥ -q''` are carried to homogeneous elements
of `S(q')` of the same degree, which lie above the cut; the `S`-span is reached because the
generators' span consists of multiples of `X^{q-q'}`, where the iterate is linear. -/
theorem reesDivXIter_mem_reesTruncationDown (hq'' : q'' ≤ q') (hq : q' ≤ q)
    {f : reesAlgebra I} (hf : f ∈ reesTruncationDown I q q'') :
    reesDivXIter I (q - q').toNat f ∈ reesTruncationDown I q' q'' := by
  rw [reesTruncationDown_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, hj : -q'' ≤ j, hzj⟩ := Set.mem_iUnion₂.mp hz
    exact mem_truncationAbove_of_mem (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q') (-q'') hj
      (reesDivXIter_mem_twistGrading I q q' hq (by omega) hzj)
  | zero =>
    rw [show reesDivXIter I (q - q').toNat (0 : reesAlgebra I) = 0 from
      Subtype.ext (divX_iterate_zero _)]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [show reesDivXIter I (q - q').toNat (x + y) =
        reesDivXIter I (q - q').toNat x + reesDivXIter I (q - q').toNat y from
      Subtype.ext (divX_iterate_add _ _ _)]
    exact add_mem hx hy
  | smul c x hx hxt =>
    have hdvd := X_pow_dvd_of_mem_reesTruncationDown_of_le I q q' q'' hq''
      ((reesTruncationDown_eq_span I q q'').ge hx)
    rw [show reesDivXIter I (q - q').toNat (c • x) = c • reesDivXIter I (q - q').toNat x from
      Subtype.ext (divX_iterate_mul_of_X_pow_dvd _ _ hdvd)]
    exact Submodule.smul_mem _ c hxt

/-- The inclusion `S(q)_{≥ -q''} ⊆ S(q)_{≥ -q'}`, as a degree-preserving `S`-linear map. -/
def reesTruncationDownInclusion (hq'' : q'' ≤ q') :
    reesTruncationDown I q q'' →ₗ[reesAlgebra I] reesTruncationDown I q q' :=
  Submodule.inclusion (reesTruncationDown_le I q q' q'' hq'')

/-- The restriction of `divX^{q-q'}` to a map of truncations
`S(q)_{≥ -q''} → S(q')_{≥ -q''}`. -/
def reesShiftDownRestrict (hq'' : q'' ≤ q') (hq : q' ≤ q) :
    reesTruncationDown I q q'' →ₗ[reesAlgebra I] reesTruncationDown I q' q'' where
  toFun f := ⟨reesDivXIter I (q - q').toNat (f : reesAlgebra I),
    reesDivXIter_mem_reesTruncationDown I q q' q'' hq'' hq f.2⟩
  map_add' f g := Subtype.ext (Subtype.ext (divX_iterate_add _ _ _))
  map_smul' c f := Subtype.ext (Subtype.ext (divX_iterate_mul_of_X_pow_dvd _ _
    (dvd_trans (pow_dvd_pow (X : A[X]) (by omega))
      (X_pow_dvd_of_mem_reesTruncationDown I q q'' f.2))))

/-- The inclusion of the smaller truncation is degree-preserving: both gradings are membership of
the coercion in the grading of `S(q)`. -/
theorem reesTruncationDownInclusion_mem (hq'' : q'' ≤ q') (i : ℤ)
    (f : reesTruncationDown I q q'') (hf : f ∈ reesTruncationDownGrading I q q'' i) :
    reesTruncationDownInclusion I q q' q'' hq'' f ∈ reesTruncationDownGrading I q q' i := hf

/-- The restriction of the iterate is degree-preserving between the two truncations. -/
theorem reesShiftDownRestrict_mem (hq'' : q'' ≤ q') (hq : q' ≤ q) (i : ℤ)
    (f : reesTruncationDown I q q'') (hf : f ∈ reesTruncationDownGrading I q q'' i) :
    reesShiftDownRestrict I q q' q'' hq'' hq f ∈ reesTruncationDownGrading I q' q'' i :=
  reesDivXIter_mem_twistGrading_of_mem_truncationAboveGrading I q q' q'' hq'' hq i f hf

/-- The inclusion of the smaller truncation into `S(q)` factors the larger one's. -/
theorem subtype_comp_reesTruncationDownInclusion (hq'' : q'' ≤ q') :
    (reesTruncationDown I q q').subtype.comp
        (reesTruncationDownInclusion I q q' q'' hq'') =
      (reesTruncationDown I q q'').subtype := rfl

/-- **The square**: following the inclusion `S(q)_{≥ -q''} ⊆ S(q)_{≥ -q'}` by `divX^{q-q'}` is
the same as restricting `divX^{q-q'}` to a map of truncations and then including. -/
theorem reesShiftDown_comp_inclusion (hq'' : q'' ≤ q') (hq : q' ≤ q) :
    (reesShiftDown I q q').comp (reesTruncationDownInclusion I q q' q'' hq'') =
      (reesTruncationDown I q' q'').subtype.comp
        (reesShiftDownRestrict I q q' q'' hq'' hq) := rfl

/-- **The iterates compose**: `divX^{q'-q''} ∘ divX^{q-q'} = divX^{q-q''}`. This is the only
place the integer arithmetic of the family appears, and it is a `Nat` equation inside
`Function.iterate` — no morphism and no type is transported. -/
theorem reesShiftDown_comp_restrict (hq'' : q'' ≤ q') (hq : q' ≤ q) :
    (reesShiftDown I q' q'').comp (reesShiftDownRestrict I q q' q'' hq'' hq) =
      reesShiftDown I q q'' := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  change divX^[(q' - q'').toNat] (divX^[(q - q').toNat] (((f : reesAlgebra I) : A[X]))) =
    divX^[(q - q'').toNat] (((f : reesAlgebra I) : A[X]))
  rw [← Function.iterate_add_apply, show (q' - q'').toNat + (q - q').toNat = (q - q'').toNat by
    omega]

/-! #### The four steps of the composition law

Each step is its own declaration: the chain is long enough that proving it as one theorem
exhausts the heartbeat budget on `isDefEq` alone, the identification of `twistingSheaf` with the
associated sheaf of the twist grading being re-derived at every composition. -/

/-- **`C₂.hom ≫ C₁.inv` is the map the inclusion of the smaller truncation induces.** The two
comparisons are both induced by inclusions into `S(q)`, and the smaller one factors through the
larger. -/
theorem comparison_hom_comp_comparison_inv (hq'' : q'' ≤ q') :
    (reesTruncationDownComparison I q q'').hom ≫
      (reesTruncationDownComparison I q q').inv =
        associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q'')
          (reesTruncationDownGrading I q q') (reesTruncationDownInclusion I q q' q'' hq'')
          (reesTruncationDownInclusion_mem I q q' q'' hq'') := by
  refine (Iso.comp_inv_eq (reesTruncationDownComparison I q q')).mpr ?_
  refine (reesTruncationDownComparison_hom I q q'').trans ?_
  refine Eq.trans ?_ (whisker_eq
    (associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q'')
      (reesTruncationDownGrading I q q') (reesTruncationDownInclusion I q q' q'' hq'')
      (reesTruncationDownInclusion_mem I q q' q'' hq''))
    (reesTruncationDownComparison_hom I q q')).symm
  refine Eq.trans ?_ (associatedModuleSheafMap_comp (reesGrading I)
    (reesTruncationDownGrading I q q'') (reesTruncationDownGrading I q q')
    (twistGrading (S := reesAlgebra I) (reesGrading I) q)
    (reesTruncationDownInclusion I q q' q'' hq'')
    (reesTruncationDownInclusion_mem I q q' q'' hq'')
    (reesTruncationDown I q q').subtype
    (truncationAbove_subtype_mem (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q) (-q')))
  exact associatedModuleSheafMap_congr_map (reesGrading I)
    (reesTruncationDownGrading I q q'')
    (twistGrading (S := reesAlgebra I) (reesGrading I) q) _ _
    (subtype_comp_reesTruncationDownInclusion I q q' q'' hq'').symm

/-- **The square, at the level of induced sheaf morphisms**: the inclusion of the smaller
truncation followed by `divX^{q-q'}` is the restricted iterate followed by the comparison of the
truncation of `S(q')`. -/
theorem inclusion_comp_reesShiftDown_sheafMap (hq'' : q'' ≤ q') (hq : q' ≤ q) :
    associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q'')
        (reesTruncationDownGrading I q q') (reesTruncationDownInclusion I q q' q'' hq'')
        (reesTruncationDownInclusion_mem I q q' q'' hq'') ≫
      associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q')
        (twistGrading (S := reesAlgebra I) (reesGrading I) q') (reesShiftDown I q q')
        (reesShiftDown_mem_twistGrading I q q' hq) =
    associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q'')
        (reesTruncationDownGrading I q' q'') (reesShiftDownRestrict I q q' q'' hq'' hq)
        (reesShiftDownRestrict_mem I q q' q'' hq'' hq) ≫
      (reesTruncationDownComparison I q' q'').hom := by
  refine Eq.trans (associatedModuleSheafMap_comp (reesGrading I)
    (reesTruncationDownGrading I q q'') (reesTruncationDownGrading I q q')
    (twistGrading (S := reesAlgebra I) (reesGrading I) q')
    (reesTruncationDownInclusion I q q' q'' hq'')
    (reesTruncationDownInclusion_mem I q q' q'' hq'')
    (reesShiftDown I q q') (reesShiftDown_mem_twistGrading I q q' hq)).symm ?_
  have hmid : associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q'')
        (twistGrading (S := reesAlgebra I) (reesGrading I) q')
        ((reesShiftDown I q q').comp (reesTruncationDownInclusion I q q' q'' hq''))
        (fun i m hm => reesShiftDown_mem_twistGrading I q q' hq i _
          (reesTruncationDownInclusion_mem I q q' q'' hq'' i m hm)) =
      associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q'')
        (twistGrading (S := reesAlgebra I) (reesGrading I) q')
        ((reesTruncationDown I q' q'').subtype.comp
          (reesShiftDownRestrict I q q' q'' hq'' hq))
        (fun i m hm => truncationAbove_subtype_mem (reesGrading I)
          (twistGrading (S := reesAlgebra I) (reesGrading I) q') (-q'') i _
          (reesShiftDownRestrict_mem I q q' q'' hq'' hq i m hm)) :=
    associatedModuleSheafMap_congr_map (reesGrading I) (reesTruncationDownGrading I q q'')
      (twistGrading (S := reesAlgebra I) (reesGrading I) q') _ _
      (reesShiftDown_comp_inclusion I q q' q'' hq'' hq)
  refine Eq.trans hmid ?_
  refine Eq.trans (associatedModuleSheafMap_comp (reesGrading I)
    (reesTruncationDownGrading I q q'') (reesTruncationDownGrading I q' q'')
    (twistGrading (S := reesAlgebra I) (reesGrading I) q')
    (reesShiftDownRestrict I q q' q'' hq'' hq)
    (reesShiftDownRestrict_mem I q q' q'' hq'' hq)
    (reesTruncationDown I q' q'').subtype
    (truncationAbove_subtype_mem (reesGrading I)
      (twistGrading (S := reesAlgebra I) (reesGrading I) q') (-q''))) ?_
  exact whisker_eq _ (reesTruncationDownComparison_hom I q' q'').symm

/-- **The iterates compose, at the level of induced sheaf morphisms.** -/
theorem restrict_comp_reesShiftDown_sheafMap (hq'' : q'' ≤ q') (hq : q' ≤ q) (h : q'' ≤ q) :
    associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q'')
        (reesTruncationDownGrading I q' q'') (reesShiftDownRestrict I q q' q'' hq'' hq)
        (reesShiftDownRestrict_mem I q q' q'' hq'' hq) ≫
      associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q' q'')
        (twistGrading (S := reesAlgebra I) (reesGrading I) q'') (reesShiftDown I q' q'')
        (reesShiftDown_mem_twistGrading I q' q'' hq'') =
    associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q'')
      (twistGrading (S := reesAlgebra I) (reesGrading I) q'') (reesShiftDown I q q'')
      (reesShiftDown_mem_twistGrading I q q'' h) := by
  refine Eq.trans (associatedModuleSheafMap_comp (reesGrading I)
    (reesTruncationDownGrading I q q'') (reesTruncationDownGrading I q' q'')
    (twistGrading (S := reesAlgebra I) (reesGrading I) q'')
    (reesShiftDownRestrict I q q' q'' hq'' hq)
    (reesShiftDownRestrict_mem I q q' q'' hq'' hq)
    (reesShiftDown I q' q'') (reesShiftDown_mem_twistGrading I q' q'' hq'')).symm ?_
  exact associatedModuleSheafMap_congr_map (reesGrading I)
    (reesTruncationDownGrading I q q'')
    (twistGrading (S := reesAlgebra I) (reesGrading I) q'') _ _
    (reesShiftDown_comp_restrict I q q' q'' hq'' hq)

/-- **The first leg, read over the smallest truncation**: `C₂.hom ≫ twistDownMap q q'` is the
restricted iterate followed by the comparison of the truncation of `S(q')`. -/
theorem comparison_hom_comp_twistDownMap_restrict (hq'' : q'' ≤ q') (hq : q' ≤ q) :
    (reesTruncationDownComparison I q q'').hom ≫ twistDownMap I q q' hq =
      associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q'')
          (reesTruncationDownGrading I q' q'') (reesShiftDownRestrict I q q' q'' hq'' hq)
          (reesShiftDownRestrict_mem I q q' q'' hq'' hq) ≫
        (reesTruncationDownComparison I q' q'').hom :=
  (whisker_eq (reesTruncationDownComparison I q q'').hom
    (twistDownMap_eq I q q' hq)).trans
    (((Category.assoc _ _ _).symm.trans
      (eq_whisker (comparison_hom_comp_comparison_inv I q q' q'' hq'')
        (associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q')
          (twistGrading (S := reesAlgebra I) (reesGrading I) q') (reesShiftDown I q q')
          (reesShiftDown_mem_twistGrading I q q' hq)))).trans
      (inclusion_comp_reesShiftDown_sheafMap I q q' q'' hq'' hq))

/-- **The composite, read over the smallest truncation.** -/
theorem comparison_hom_comp_twistDownMap_comp (hq'' : q'' ≤ q') (hq : q' ≤ q) (h : q'' ≤ q) :
    (reesTruncationDownComparison I q q'').hom ≫
        (twistDownMap I q q' hq ≫ twistDownMap I q' q'' hq'') =
      associatedModuleSheafMap (reesGrading I) (reesTruncationDownGrading I q q'')
        (twistGrading (S := reesAlgebra I) (reesGrading I) q'') (reesShiftDown I q q'')
        (reesShiftDown_mem_twistGrading I q q'' h) :=
  ((Category.assoc _ _ _).symm.trans
    (eq_whisker (comparison_hom_comp_twistDownMap_restrict I q q' q'' hq'' hq)
      (twistDownMap I q' q'' hq''))).trans
    ((Category.assoc _ _ _).trans
      ((whisker_eq _ (comparison_hom_comp_twistDownMap I q' q'' hq'')).trans
        (restrict_comp_reesShiftDown_sheafMap I q q' q'' hq'' hq h)))

/-- **The twisting-down maps are functorial**: `𝒪_X(q) → 𝒪_X(q') → 𝒪_X(q'')` is
`𝒪_X(q) → 𝒪_X(q'')`.

The proof cancels the comparison isomorphism of the *smallest* truncation `S(q)_{≥ -q''}` against
both sides. Over it the two routes become the square
`Stacks.Blowup.reesShiftDown_comp_inclusion` followed by
`Stacks.Blowup.reesShiftDown_comp_restrict`, and the law is the functoriality of the
associated-sheaf construction together with `divX^{q'-q''} ∘ divX^{q-q'} = divX^{q-q''}`. -/
theorem twistDownMap_comp (hq'' : q'' ≤ q') (hq : q' ≤ q) (h : q'' ≤ q) :
    twistDownMap I q q' hq ≫ twistDownMap I q' q'' hq'' = twistDownMap I q q'' h :=
  (Iso.cancel_iso_hom_left (reesTruncationDownComparison I q q'') _ _).mp
    ((comparison_hom_comp_twistDownMap_comp I q q' q'' hq'' hq h).trans
      (comparison_hom_comp_twistDownMap I q q'' h).symm)


end Stacks.Blowup

end
