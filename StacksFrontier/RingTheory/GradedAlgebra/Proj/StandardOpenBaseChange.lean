module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.RingTheory.HomogeneousLocalization.DegreeZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change on standard opens of Proj

Let `A` be a graded algebra over a commutative ring `R`, with grading `𝒜 : ℕ → Submodule R A`,
and let `R'` be an `R`-algebra. Extension of scalars commutes with taking the degree-zero part of
the localization at a homogeneous element `f` of degree `d`: the canonical map

`R' ⊗[R] A₍f₎ → (R' ⊗[R] A)₍1 ⊗ f₎`,  `r ⊗ x ↦ r * (1 ⊗ x)`,

is an isomorphism of `R'`-algebras, and the same formula gives an isomorphism for every twist
`A(n)₍f₎` of the graded algebra. The two families of isomorphisms are compatible: the one on
twists is linear over the one on degree-zero rings.

Both maps are shown to be bijective by the same argument. Every element of a degree-zero
localization is a fraction `x / f ^ k` with `x` homogeneous, so after base change every element
comes from a numerator in a single homogeneous piece `R' ⊗[R] 𝒜 e`; surjectivity is then the
surjectivity of `Submodule.toBaseChange` onto the base-changed piece, and injectivity is the fact
that an element of `R' ⊗[R] 𝒜 e` killed by a power of `1 ⊗ f` is already zero after multiplying
by that power, which `DirectSum.IsInternal.toBaseChange_injective` reads back inside the piece.

## Main definitions

* `Stacks.ProjStandardOpenBaseChange.twistAway` is the degree-zero localization of a twist.
* `Stacks.ProjStandardOpenBaseChange.gradedBaseChangeMap` is the graded ring map `a ↦ 1 ⊗ a`
  into the base change.
* `Stacks.ProjStandardOpenBaseChange.StandardOpenBaseChange` bundles the canonical compatible
  base-change isomorphisms on a standard open.

## Main results

* `Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange` constructs those compatible
  canonical isomorphisms, for the graded ring and for all of its twists at once.

## Implementation notes

The base-changed graded ring is the literal tensor product `R' ⊗[R] A`, graded by the scalar
extensions of the homogeneous pieces. The twist `A(n)₍f₎` is represented inside `A[1/f]` as the
span, over the degree-zero ring `A₍f₎`, of the fractions whose numerator has degree `k * d + n`
and whose denominator is `f ^ k`. Writing that degree condition in `ℤ` permits arbitrary twists
while the ring itself remains nonnegatively graded. The formulas on pure tensors make both
isomorphisms canonical, and `twistEquiv_smul` records their compatibility.

`Stacks.ProjBaseChange.includeRight`, with the grading `Stacks.ProjBaseChange.grading`, is the
same graded map when `R`, `A` and `R'` lie in one universe; here the three universes are
independent.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
-/

@[expose] public section

open Algebra TensorProduct
open HomogeneousLocalization

universe u v w

namespace Stacks.ProjStandardOpenBaseChange

variable {R : Type u} {R' : Type v} {A : Type w}
variable [CommRing R] [CommRing R'] [CommRing A]
variable [Algebra R R'] [Algebra R A]

/-- The degree-zero localization of the twist `A(n)` at a homogeneous element
`f` of degree `d`.  It is the submodule of `A[1/f]` spanned over `A_(f)` by
the fractions `x / f^k` with `x` homogeneous of degree `k * d + n`.

Writing the degree condition in `ℤ` permits arbitrary twists while the ring
itself remains nonnegatively graded. -/
@[ega "II 8.2.1" "partial"]
noncomputable def twistAway (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (n : ℤ) :
    Submodule (Away 𝒜 f) (Localization (Submonoid.powers f)) :=
  Submodule.span (Away 𝒜 f)
    {z | ∃ (k e : ℕ) (x : A), (e : ℤ) = (k * d : ℕ) + n ∧ x ∈ 𝒜 e ∧
      z = Localization.mk x
        ⟨f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers f) k⟩}

/-- The restriction of scalars which makes a localized twist an `R`-module. -/
noncomputable instance instModuleTwistAway (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (n : ℤ) : Module R (twistAway 𝒜 f d n) :=
  Module.compHom _ (algebraMap R (Away 𝒜 f))

/-- The graded map `A → R' ⊗[R] A`, `a ↦ 1 ⊗ a`, used in base change. -/
noncomputable def gradedBaseChangeMap (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    𝒜 →+*ᵍ (fun i ↦ (𝒜 i).baseChange R') where
  __ := Algebra.TensorProduct.includeRight (R := R) (A := R') (B := A)
  map_mem hx := Submodule.tmul_mem_baseChange_of_mem 1 hx

/-- The compatible base-change isomorphisms on a standard open.  The two
formula fields characterize the isomorphisms on pure tensors, while
`twistEquiv_smul` records compatibility of the twist isomorphisms with the
degree-zero ring isomorphism. -/
structure StandardOpenBaseChange (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) where
  /-- Base change commutes with the degree-zero localized ring. -/
  ringEquiv :
    R' ⊗[R] Away 𝒜 f ≃ₐ[R']
      Away (fun i ↦ (𝒜 i).baseChange R') (gradedBaseChangeMap (R' := R') 𝒜 f)
  /-- Base change commutes with the degree-zero localization of every twist. -/
  twistEquiv : (n : ℤ) →
    R' ⊗[R] twistAway 𝒜 f d n ≃ₗ[R']
      twistAway (fun i ↦ (𝒜 i).baseChange R')
        (gradedBaseChangeMap (R' := R') 𝒜 f) d n
  /-- The ring isomorphism is induced by `a ↦ 1 ⊗ a`. -/
  ringEquiv_tmul (r : R') (x : Away 𝒜 f) :
    ringEquiv (r ⊗ₜ[R] x) =
      algebraMap R' _ r * Away.map (gradedBaseChangeMap (R' := R') 𝒜) f x
  /-- The twist isomorphism is induced by the corresponding map of ordinary
  localizations. -/
  twistEquiv_tmul_val (n : ℤ) (r : R') (k e : ℕ) (x : A)
      (he : (e : ℤ) = (k * d : ℕ) + n) (hx : x ∈ 𝒜 e) :
    ((twistEquiv n (r ⊗ₜ[R]
        (⟨Localization.mk x
          ⟨f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers f) k⟩,
            Submodule.subset_span ⟨k, e, x, he, hx, rfl⟩⟩ :
            twistAway 𝒜 f d n)) :
        twistAway (fun i ↦ (𝒜 i).baseChange R')
          (gradedBaseChangeMap (R' := R') 𝒜 f) d n) :
      Localization (Submonoid.powers (gradedBaseChangeMap (R' := R') 𝒜 f))) =
      algebraMap R' _ r * Localization.mk (1 ⊗ₜ[R] x)
        ⟨(gradedBaseChangeMap (R' := R') 𝒜 f) ^ k, Submonoid.pow_mem _
          (Submonoid.mem_powers (gradedBaseChangeMap (R' := R') 𝒜 f)) k⟩
  /-- The isomorphisms on twists are linear over the isomorphism on the
  degree-zero localized rings. -/
  twistEquiv_smul (n : ℤ) (r : R') (a : Away 𝒜 f)
      (x : twistAway 𝒜 f d n) :
    twistEquiv n (r ⊗ₜ[R] (a • x)) =
      ringEquiv (r ⊗ₜ[R] a) • twistEquiv n (1 ⊗ₜ[R] x)

/-- The structure map of a degree-zero localization sends `s` to the fraction `algebraMap s / 1`. -/
private lemma algebraMap_away_eq_mk {S : Type*} [CommRing S] [Algebra S A]
    (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜] {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (s : S) :
    algebraMap S (Away 𝒜 f) s =
      Away.mk 𝒜 hf 0 (algebraMap S A s) (by
        simp only [zero_nsmul]
        rw [Algebra.algebraMap_eq_smul_one]
        exact (𝒜 0).smul_mem s SetLike.GradedOne.one_mem) := by
  ext
  change (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)
    (algMapRtoA0 𝒜 s)).val = _
  simp only [HomogeneousLocalization.fromZeroRingHom, Away.val_mk]
  change Localization.mk (↑(algMapRtoA0 𝒜 s) : A)
    (⟨1, Submonoid.one_mem _⟩ : Submonoid.powers f) = _
  simp [algMapRtoA0]

private noncomputable def awayBaseChangeAlgHom
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) :
    R' ⊗[R] Away 𝒜 f →ₐ[R']
      Away (fun i ↦ (𝒜 i).baseChange R') (gradedBaseChangeMap (R' := R') 𝒜 f) := by
  let B := Away (fun i ↦ (𝒜 i).baseChange R')
      (gradedBaseChangeMap (R' := R') 𝒜 f)
  let bAlg : Algebra R B := ((algebraMap R' B).comp (algebraMap R R')).toAlgebra
  letI : Algebra R B := bAlg
  let g : Away 𝒜 f →+* B := Away.map (gradedBaseChangeMap (R' := R') 𝒜) f
  have hg : (algebraMap R B) = g.comp (algebraMap R (Away 𝒜 f)) := by
    ext r
    change ((algebraMap R' B) (algebraMap R R' r)).val =
      (Away.map (gradedBaseChangeMap (R' := R') 𝒜) f
        ((algebraMap R (Away 𝒜 f)) r)).val
    rw [algebraMap_away_eq_mk _ _ (gradedBaseChangeMap 𝒜 |>.map_mem hf),
      algebraMap_away_eq_mk 𝒜 f hf, Away.map_mk]
    simp only [Away.val_mk]
    congr 1
    simp [gradedBaseChangeMap]
  exact @Algebra.TensorProduct.lift R R' R' (Away 𝒜 f) B
    _ _ _ _ _ _ _ _ _ _ _ bAlg
    (@IsScalarTower.of_algebraMap_eq' R R' B _ _ _ _ _ bAlg rfl)
    (Algebra.ofId R' B)
    ({ g with commutes' := fun r ↦ congrFun (congrArg DFunLike.coe hg) r |>.symm } :
      Away 𝒜 f →ₐ[R] B) (fun _ _ ↦ Commute.all _ _)

private lemma awayBaseChangeAlgHom_tmul
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A) (d : ℕ) (hf : f ∈ 𝒜 d)
    (r : R') (x : Away 𝒜 f) :
    awayBaseChangeAlgHom (R' := R') 𝒜 f d hf (r ⊗ₜ[R] x) =
      algebraMap R' _ r * Away.map (gradedBaseChangeMap (R' := R') 𝒜) f x := by
  simp only [awayBaseChangeAlgHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
  rfl

private lemma awayMk_add (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n : ℕ) (hf : f ∈ 𝒜 d) (x y : A)
    (hx : x ∈ 𝒜 (n • d)) (hy : y ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n (x + y) ((𝒜 (n • d)).add_mem hx hy) =
      Away.mk 𝒜 hf n x hx + Away.mk 𝒜 hf n y hy := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_add]
  exact (Localization.add_mk_self _ _ _).symm

private lemma awayMk_zero (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n : ℕ) (hf : f ∈ 𝒜 d) :
    Away.mk 𝒜 hf n 0 (𝒜 (n • d)).zero_mem = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_zero]
  exact Localization.mk_zero _

private lemma awayMk_smul (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n : ℕ) (hf : f ∈ 𝒜 d) (r : R) (x : A)
    (hx : x ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n (r • x) ((𝒜 (n • d)).smul_mem r hx) =
      (algebraMap R (Away 𝒜 f) r) * Away.mk 𝒜 hf n x hx := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.val_mul, Away.val_mk]
  change Localization.mk (r • x) _ =
    Localization.mk (algebraMap R A r)
      (⟨1, Submonoid.one_mem _⟩ : Submonoid.powers f) * Localization.mk x _
  simp [Algebra.smul_def, Localization.mk_mul]

private noncomputable def awayNumeratorMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n : ℕ) (hf : f ∈ 𝒜 d) :
    𝒜 (n • d) →ₗ[R] Away 𝒜 f where
  toFun x := Away.mk 𝒜 hf n x x.property
  map_add' x y := awayMk_add 𝒜 f d n hf x y x.property y.property
  map_smul' r x := (awayMk_smul 𝒜 f d n hf r x x.property).trans (Algebra.smul_def r _).symm

private noncomputable def awayNumeratorBaseChangeMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n : ℕ) (hf : f ∈ 𝒜 d) :
    R' ⊗[R] 𝒜 (n • d) →ₗ[R'] R' ⊗[R] Away 𝒜 f :=
  (awayNumeratorMap 𝒜 f d n hf).baseChange R'

private lemma localizationMk_eq_zero_iff
    {B : Type*} [CommRing B] (g x : B) (k : ℕ) :
    (Localization.mk x
      ⟨g ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers g) k⟩ :
      Localization (Submonoid.powers g)) = 0 ↔
      ∃ m : ℕ, g ^ m * x = 0 := by
  rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨m, hm⟩ := s.property
    exact ⟨m, by simpa [hm] using hs⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨g ^ m, Submonoid.pow_mem _ (Submonoid.mem_powers g) m⟩, hm⟩

/-- Multiplying numerator and denominator of a fraction by `g ^ m` does not change it. -/
private lemma localizationMk_mul_pow {B : Type*} [CommRing B] (g x : B) (k m : ℕ) :
    (Localization.mk x ⟨g ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers g) k⟩ :
      Localization (Submonoid.powers g)) =
      Localization.mk (x * g ^ m)
        ⟨g ^ (k + m), Submonoid.pow_mem _ (Submonoid.mem_powers g) (k + m)⟩ := by
  simp only [Localization.mk_eq_mk'_apply]
  rw [IsLocalization.mk'_eq_iff_eq']
  congr 1
  simp [pow_add, mul_comm, mul_left_comm]

private lemma awayMk_eq_zero_iff
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n : ℕ) (hf : f ∈ 𝒜 d) (x : A) (hx : x ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n x hx = 0 ↔ ∃ k : ℕ, f ^ k * x = 0 := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk, HomogeneousLocalization.val_zero]
  exact localizationMk_eq_zero_iff f x n

private lemma awayMk_add_cross
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n m : ℕ) (hf : f ∈ 𝒜 d)
    (x y : A) (hx : x ∈ 𝒜 (n • d)) (hy : y ∈ 𝒜 (m • d)) :
    Away.mk 𝒜 hf n x hx + Away.mk 𝒜 hf m y hy =
      Away.mk 𝒜 hf (n + m) (x * f ^ m + y * f ^ n) (by
        have h₁ : x * f ^ m ∈ 𝒜 (n • d + m • d) :=
          SetLike.mul_mem_graded hx (SetLike.pow_mem_graded m hf)
        have h₂ : y * f ^ n ∈ 𝒜 (m • d + n • d) :=
          SetLike.mul_mem_graded hy (SetLike.pow_mem_graded n hf)
        have h₂' : y * f ^ n ∈ 𝒜 (n • d + m • d) := by
          simpa only [add_comm] using h₂
        simpa only [add_nsmul] using (𝒜 (n • d + m • d)).add_mem h₁ h₂') := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, Away.val_mk]
  rw [Localization.add_mk]
  simp only [pow_add]
  congr 1
  ring

private lemma awayMk_mul_pow
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n m : ℕ) (hf : f ∈ 𝒜 d)
    (x : A) (hx : x ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n x hx =
      Away.mk 𝒜 hf (n + m) (x * f ^ m) (by
        have h : x * f ^ m ∈ 𝒜 (n • d + m • d) :=
          SetLike.mul_mem_graded hx (SetLike.pow_mem_graded m hf)
        simpa only [add_nsmul] using h) := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk]
  exact localizationMk_mul_pow f x n m

private noncomputable def multiplyPowMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n m : ℕ) (hf : f ∈ 𝒜 d) :
    𝒜 (n • d) →ₗ[R] 𝒜 ((n + m) • d) where
  toFun x := ⟨x * f ^ m, by
    have h : (x : A) * f ^ m ∈ 𝒜 (n • d + m • d) :=
      SetLike.mul_mem_graded x.property (SetLike.pow_mem_graded m hf)
    simpa only [add_nsmul] using h⟩
  map_add' x y := by
    ext
    simp [add_mul]
  map_smul' r x := by
    ext
    simp

private lemma awayNumeratorBaseChangeMap_mul_pow
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n m : ℕ) (hf : f ∈ 𝒜 d)
    (q : R' ⊗[R] 𝒜 (n • d)) :
    awayNumeratorBaseChangeMap (R' := R') 𝒜 f d n hf q =
      awayNumeratorBaseChangeMap (R' := R') 𝒜 f d (n + m) hf
        ((multiplyPowMap 𝒜 f d n m hf).baseChange R' q) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
      simp only [awayNumeratorBaseChangeMap, LinearMap.baseChange_tmul]
      congr 1
      exact awayMk_mul_pow 𝒜 f d n m hf x x.property
  | add q₁ q₂ h₁ h₂ => simpa only [map_add] using congrArg₂ (· + ·) h₁ h₂

private lemma awayNumeratorBaseChangeMap_surjective
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) :
    ∀ z : R' ⊗[R] Away 𝒜 f,
      ∃ (n : ℕ) (q : R' ⊗[R] 𝒜 (n • d)),
        awayNumeratorBaseChangeMap 𝒜 f d n hf q = z := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      exact ⟨0, 0, by simp⟩
  | tmul r x =>
      obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf x
      exact ⟨n, r ⊗ₜ[R] (⟨a, ha⟩ : 𝒜 (n • d)), rfl⟩
  | add z₁ z₂ h₁ h₂ =>
      obtain ⟨n, q₁, rfl⟩ := h₁
      obtain ⟨m, q₂, rfl⟩ := h₂
      let q₁' := (multiplyPowMap 𝒜 f d n m hf).baseChange R' q₁
      let q₂' : R' ⊗[R] 𝒜 ((n + m) • d) :=
        cast (congrArg (fun k : ℕ => R' ⊗[R] 𝒜 (k • d)) (Nat.add_comm m n))
          ((multiplyPowMap 𝒜 f d m n hf).baseChange R' q₂)
      refine ⟨n + m, q₁' + q₂', ?_⟩
      rw [map_add]
      have h₁' := awayNumeratorBaseChangeMap_mul_pow (R' := R') 𝒜 f d n m hf q₁
      have h₂' := awayNumeratorBaseChangeMap_mul_pow (R' := R') 𝒜 f d m n hf q₂
      have hcast {i j : ℕ} (h : i = j) (q : R' ⊗[R] 𝒜 (i • d)) :
          awayNumeratorBaseChangeMap 𝒜 f d j hf
            (cast (congrArg (fun k : ℕ => R' ⊗[R] 𝒜 (k • d)) h) q) =
          awayNumeratorBaseChangeMap 𝒜 f d i hf q := by
        cases h
        rfl
      have h₂'' : awayNumeratorBaseChangeMap 𝒜 f d m hf q₂ =
          awayNumeratorBaseChangeMap 𝒜 f d (n + m) hf q₂' := by
        calc
          _ = awayNumeratorBaseChangeMap 𝒜 f d (m + n) hf
              ((multiplyPowMap 𝒜 f d m n hf).baseChange R' q₂) := h₂'
          _ = _ := (hcast (Nat.add_comm m n)
            ((multiplyPowMap 𝒜 f d m n hf).baseChange R' q₂)).symm
      exact congrArg₂ (· + ·) h₁'.symm h₂''.symm

private lemma awayBaseChangeAlgHom_numerator
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d n : ℕ) (hf : f ∈ 𝒜 d)
    (q : R' ⊗[R] 𝒜 (n • d)) :
    awayBaseChangeAlgHom (R' := R') 𝒜 f d hf
      (awayNumeratorBaseChangeMap 𝒜 f d n hf q) =
    Away.mk (fun i ↦ (𝒜 i).baseChange R')
      ((gradedBaseChangeMap (R' := R') 𝒜).map_mem hf) n
      (((𝒜 (n • d)).toBaseChange R' q : (𝒜 (n • d)).baseChange R') :
        R' ⊗[R] A)
      (((𝒜 (n • d)).toBaseChange R' q).property) := by
  let 𝓑 := fun i ↦ (𝒜 i).baseChange R'
  let ψ := gradedBaseChangeMap (R' := R') 𝒜
  have hfB : ψ f ∈ 𝓑 d := ψ.map_mem hf
  induction q using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero]
      exact (awayMk_zero 𝓑 (ψ f) d n hfB).symm
  | tmul r x =>
      simp only [awayNumeratorBaseChangeMap, LinearMap.baseChange_tmul]
      rw [awayBaseChangeAlgHom_tmul]
      change _ * Away.map (gradedBaseChangeMap (R' := R') 𝒜) f
        (Away.mk 𝒜 hf n (x : A) x.property) = _
      rw [Away.map_mk]
      simp only [Submodule.coe_toBaseChange_tmul]
      have htmul : (r ⊗ₜ[R] (x : A)) = r • ψ (x : A) := by
        simp [ψ, gradedBaseChangeMap, TensorProduct.smul_tmul']
      apply HomogeneousLocalization.val_injective
      have h := congrArg HomogeneousLocalization.val
        ((awayMk_smul 𝓑 (ψ f) d n hfB r (ψ x) (ψ.map_mem x.property)).symm)
      simp only [Away.val_mk] at h ⊢
      change _ = Localization.mk (r ⊗ₜ[R] (x : A))
        (⟨ψ f ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers (ψ f)) n⟩ :
          Submonoid.powers (ψ f))
      rw [htmul]
      exact h
  | add q₁ q₂ h₁ h₂ =>
      rw [map_add, map_add, h₁, h₂]
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_add]
      change Localization.mk
        (((𝒜 (n • d)).toBaseChange R' q₁ : (𝒜 (n • d)).baseChange R') :
          R' ⊗[R] A) _ +
        Localization.mk
        (((𝒜 (n • d)).toBaseChange R' q₂ : (𝒜 (n • d)).baseChange R') :
          R' ⊗[R] A) _ =
        Localization.mk
        (((𝒜 (n • d)).toBaseChange R' (q₁ + q₂) : (𝒜 (n • d)).baseChange R') :
          R' ⊗[R] A) _
      rw [map_add]
      exact Localization.add_mk_self _ _ _

/-- If `φ` multiplies by `f ^ m` and `q` is killed by `1 ⊗ f ^ m` in `R' ⊗[R] A`, then
`φ` kills `q` after base change. -/
private lemma baseChange_eq_zero_of_mul_pow
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A) {i j : ℕ} (m : ℕ)
    (φ : 𝒜 i →ₗ[R] 𝒜 j) (hφ : ∀ x, (φ x : A) = x * f ^ m) (q : R' ⊗[R] 𝒜 i)
    (hm : (gradedBaseChangeMap (R' := R') 𝒜 f) ^ m *
      (((𝒜 i).toBaseChange R' q : (𝒜 i).baseChange R') : R' ⊗[R] A) = 0) :
    φ.baseChange R' q = 0 := by
  have key : ∀ q : R' ⊗[R] 𝒜 i,
      (((𝒜 j).toBaseChange R' (φ.baseChange R' q) : (𝒜 j).baseChange R') : R' ⊗[R] A) =
        (gradedBaseChangeMap (R' := R') 𝒜 f) ^ m *
          (((𝒜 i).toBaseChange R' q : (𝒜 i).baseChange R') : R' ⊗[R] A) := by
    intro q
    induction q using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
        simp only [LinearMap.baseChange_tmul, Submodule.coe_toBaseChange_tmul, hφ]
        change (r ⊗ₜ[R] ((x : A) * f ^ m)) =
          (1 ⊗ₜ[R] f) ^ m * (r ⊗ₜ[R] (x : A))
        simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
    | add q₁ q₂ h₁ h₂ =>
        simpa only [map_add, Submodule.coe_add, mul_add] using congrArg₂ (· + ·) h₁ h₂
  apply DirectSum.IsInternal.toBaseChange_injective 𝒜
    (DirectSum.Decomposition.isInternal 𝒜) j
  apply Subtype.ext
  rw [key q, hm]
  rfl

private lemma awayBaseChangeAlgHom_surjective
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) :
    Function.Surjective (awayBaseChangeAlgHom (R' := R') 𝒜 f d hf) := by
  intro y
  let 𝓑 := fun i ↦ (𝒜 i).baseChange R'
  let ψ := gradedBaseChangeMap (R' := R') 𝒜
  have hfB : ψ f ∈ 𝓑 d := ψ.map_mem hf
  obtain ⟨n, t, ht, rfl⟩ := Away.mk_surjective 𝓑 hfB y
  obtain ⟨q, hq⟩ := (𝒜 (n • d)).toBaseChange_surjective' (A := R') ht
  exact ⟨awayNumeratorBaseChangeMap 𝒜 f d n hf q, by
    simpa only [hq] using awayBaseChangeAlgHom_numerator (R' := R') 𝒜 f d n hf q⟩

private lemma awayBaseChangeAlgHom_eq_zero
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d)
    (z : R' ⊗[R] Away 𝒜 f)
    (hz : awayBaseChangeAlgHom (R' := R') 𝒜 f d hf z = 0) : z = 0 := by
  obtain ⟨n, q, rfl⟩ :=
    awayNumeratorBaseChangeMap_surjective (R' := R') 𝒜 f d hf z
  let 𝓑 := fun i ↦ (𝒜 i).baseChange R'
  let ψ := gradedBaseChangeMap (R' := R') 𝒜
  have hfB : ψ f ∈ 𝓑 d := ψ.map_mem hf
  have hzero :
      Away.mk 𝓑 hfB n
        (((𝒜 (n • d)).toBaseChange R' q : (𝒜 (n • d)).baseChange R') :
          R' ⊗[R] A)
        (((𝒜 (n • d)).toBaseChange R' q).property) = 0 := by
    rwa [← awayBaseChangeAlgHom_numerator]
  obtain ⟨m, hm⟩ := (awayMk_eq_zero_iff 𝓑 (ψ f) d n hfB
    _ ((𝒜 (n • d)).toBaseChange R' q).property).mp hzero
  have hqzero := baseChange_eq_zero_of_mul_pow (R' := R') 𝒜 f m
    (multiplyPowMap 𝒜 f d n m hf) (fun _ ↦ rfl) q hm
  rw [awayNumeratorBaseChangeMap_mul_pow (R' := R') 𝒜 f d n m hf q,
    hqzero, map_zero]

private lemma awayBaseChangeAlgHom_injective
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) :
    Function.Injective (awayBaseChangeAlgHom (R' := R') 𝒜 f d hf) :=
  (injective_iff_map_eq_zero _).mpr (awayBaseChangeAlgHom_eq_zero 𝒜 f d hf)

private noncomputable def awayBaseChangeAlgEquiv
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) :
    R' ⊗[R] Away 𝒜 f ≃ₐ[R']
      Away (fun i ↦ (𝒜 i).baseChange R')
        (gradedBaseChangeMap (R' := R') 𝒜 f) :=
  AlgEquiv.ofBijective (awayBaseChangeAlgHom 𝒜 f d hf)
    ⟨awayBaseChangeAlgHom_injective 𝒜 f d hf,
      awayBaseChangeAlgHom_surjective 𝒜 f d hf⟩

private noncomputable def localizationBaseChangeMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A) :
    Localization (Submonoid.powers f) →+*
      Localization (Submonoid.powers (gradedBaseChangeMap (R' := R') 𝒜 f)) :=
  IsLocalization.map (M := Submonoid.powers f)
    (T := Submonoid.powers (gradedBaseChangeMap (R' := R') 𝒜 f))
    _ (gradedBaseChangeMap (R' := R') 𝒜).toRingHom (by
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    exact ⟨k, by simp⟩)

private lemma localizationBaseChangeMap_mk
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f x : A) (k : ℕ) :
    localizationBaseChangeMap (R' := R') 𝒜 f
      (Localization.mk x
        ⟨f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers f) k⟩) =
      Localization.mk (gradedBaseChangeMap (R' := R') 𝒜 x)
        ⟨(gradedBaseChangeMap (R' := R') 𝒜 f) ^ k,
          Submonoid.pow_mem _
            (Submonoid.mem_powers (gradedBaseChangeMap (R' := R') 𝒜 f)) k⟩ := by
  simp [localizationBaseChangeMap, Localization.mk_eq_mk'_apply,
    IsLocalization.map_mk']

private lemma localizationBaseChangeMap_away_val
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (a : Away 𝒜 f) :
    localizationBaseChangeMap (R' := R') 𝒜 f a.val =
      (Away.map (gradedBaseChangeMap (R' := R') 𝒜) f a).val := by
  obtain ⟨k, x, hx, rfl⟩ := Away.mk_surjective 𝒜 hf a
  rw [Away.val_mk, Away.map_mk, Away.val_mk]
  exact localizationBaseChangeMap_mk 𝒜 f x k

private lemma localizationBaseChangeMap_mem_twistAway
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (n : ℤ)
    (z : Localization (Submonoid.powers f))
    (hz : z ∈ twistAway 𝒜 f d n) :
    localizationBaseChangeMap (R' := R') 𝒜 f z ∈
      twistAway (fun i ↦ (𝒜 i).baseChange R')
        (gradedBaseChangeMap (R' := R') 𝒜 f) d n := by
  let 𝓑 := fun i ↦ (𝒜 i).baseChange R'
  let ψ := gradedBaseChangeMap (R' := R') 𝒜
  let L := localizationBaseChangeMap (R' := R') 𝒜 f
  change z ∈ Submodule.span (Away 𝒜 f) _ at hz
  refine Submodule.span_induction (p := fun z _ => L z ∈ twistAway 𝓑 (ψ f) d n)
    ?_ ?_ ?_ ?_ hz
  · rintro z ⟨k, e, x, he, hx, rfl⟩
    change L (Localization.mk x _) ∈ twistAway 𝓑 (ψ f) d n
    rw [localizationBaseChangeMap_mk]
    exact Submodule.subset_span ⟨k, e, ψ x, he, ψ.map_mem hx, rfl⟩
  · simpa only [map_zero] using (twistAway 𝓑 (ψ f) d n).zero_mem
  · intro x y _ _ hx hy
    simpa only [map_add] using (twistAway 𝓑 (ψ f) d n).add_mem hx hy
  · intro a x _ hx
    change L (a.val * x) ∈ twistAway 𝓑 (ψ f) d n
    rw [map_mul, localizationBaseChangeMap_away_val 𝒜 f d hf]
    change (Away.map ψ f a) • L x ∈ twistAway 𝓑 (ψ f) d n
    exact (twistAway 𝓑 (ψ f) d n).smul_mem _ hx

private noncomputable def fullLocalizationBaseChangeEquiv
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A) :
    R' ⊗[R] Localization (Submonoid.powers f) ≃ₗ[R']
      Localization (Submonoid.powers (gradedBaseChangeMap (R' := R') 𝒜 f)) :=
  (IsLocalization.Away.tensorProductEquivTMulRight R R' f
    (Localization (Submonoid.powers f))).toLinearEquiv

private noncomputable def twistAwaySubtypeLinearMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (n : ℤ) :
    twistAway 𝒜 f d n →ₗ[R] Localization (Submonoid.powers f) where
  toFun x := x
  map_add' x y := rfl
  map_smul' r x := by
    change (((algebraMap R (Away 𝒜 f)) r • x : twistAway 𝒜 f d n) :
      Localization (Submonoid.powers f)) = _
    rw [Submodule.coe_smul]
    simp only [Algebra.smul_def]
    congr 1

/-- The `R`-action on a localized twist is the `A₍f₎`-action through the structure map, so it
agrees with the `R`-action on the ambient localization. -/
private lemma coe_smul_twistAway (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (n : ℤ) (r : R) (y : twistAway 𝒜 f d n) :
    ((r • y : twistAway 𝒜 f d n) : Localization (Submonoid.powers f)) =
      r • (y : Localization (Submonoid.powers f)) :=
  (twistAwaySubtypeLinearMap 𝒜 f d n).map_smul r y

private noncomputable def twistFullBaseChangeMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (n : ℤ) :
    R' ⊗[R] twistAway 𝒜 f d n →ₗ[R']
      Localization (Submonoid.powers (gradedBaseChangeMap (R' := R') 𝒜 f)) :=
  (fullLocalizationBaseChangeEquiv (R' := R') 𝒜 f).toLinearMap.comp
    ((twistAwaySubtypeLinearMap 𝒜 f d n).baseChange R')

private lemma gradedBaseChangeMap_apply
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (x : A) :
    gradedBaseChangeMap (R' := R') 𝒜 x = 1 ⊗ₜ[R] x := rfl

private lemma fullLocalizationBaseChangeEquiv_one_tmul
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (z : Localization (Submonoid.powers f)) :
    fullLocalizationBaseChangeEquiv (R' := R') 𝒜 f (1 ⊗ₜ[R] z) =
      localizationBaseChangeMap (R' := R') 𝒜 f z := by
  let E := IsLocalization.Away.tensorProductEquivTMulRight R R' f
    (Localization (Submonoid.powers f))
  let L := localizationBaseChangeMap (R' := R') 𝒜 f
  have hE : (E.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := R')
        (B := Localization (Submonoid.powers f)))) = L := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    change E (1 ⊗ₜ[R] (algebraMap A (Localization (Submonoid.powers f)) x)) =
      L (algebraMap A (Localization (Submonoid.powers f)) x)
    rw [IsLocalization.Away.tensorProductEquivTMulRight_tmul]
    unfold L localizationBaseChangeMap
    rw [IsLocalization.map_eq]
    rfl
  exact congrArg (fun g : _ →+* _ => g z) hE

private lemma fullLocalizationBaseChangeEquiv_tmul_raw
    (f : A) (r : R') (z : Localization (Submonoid.powers f)) :
    (IsLocalization.Away.tensorProductEquivTMulRight R R' f
      (Localization (Submonoid.powers f))) (r ⊗ₜ[R] z) =
      algebraMap R' (Localization.Away ((1 : R') ⊗ₜ[R] f)) r *
        (IsLocalization.Away.tensorProductEquivTMulRight R R' f
          (Localization (Submonoid.powers f))) (1 ⊗ₜ[R] z) := by
  let E := IsLocalization.Away.tensorProductEquivTMulRight R R' f
    (Localization (Submonoid.powers f))
  have ht : (r ⊗ₜ[R] z) = (r ⊗ₜ[R] (1 : Localization (Submonoid.powers f))) *
      ((1 : R') ⊗ₜ[R] z) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp only [mul_one, one_mul]
  rw [ht, map_mul]
  congr 1
  exact E.commutes r

private lemma twistFullBaseChangeMap_one_tmul
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (n : ℤ) (x : twistAway 𝒜 f d n) :
    twistFullBaseChangeMap (R' := R') 𝒜 f d n (1 ⊗ₜ[R] x) =
      localizationBaseChangeMap (R' := R') 𝒜 f x := by
  simp only [twistFullBaseChangeMap, LinearMap.comp_apply,
    LinearMap.baseChange_tmul]
  change fullLocalizationBaseChangeEquiv (R' := R') 𝒜 f
    (1 ⊗ₜ[R] (x : Localization (Submonoid.powers f))) = _
  exact fullLocalizationBaseChangeEquiv_one_tmul 𝒜 f x

private lemma twistFullBaseChangeMap_tmul
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (n : ℤ) (r : R') (x : twistAway 𝒜 f d n) :
    twistFullBaseChangeMap (R' := R') 𝒜 f d n (r ⊗ₜ[R] x) =
      r • localizationBaseChangeMap (R' := R') 𝒜 f x := by
  have ht : (r ⊗ₜ[R] x) = r • ((1 : R') ⊗ₜ[R] x) := by
    simp [TensorProduct.smul_tmul']
  rw [ht, map_smul, twistFullBaseChangeMap_one_tmul]

private lemma twistFullBaseChangeMap_mem
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (n : ℤ)
    (z : R' ⊗[R] twistAway 𝒜 f d n) :
    twistFullBaseChangeMap (R' := R') 𝒜 f d n z ∈
      twistAway (fun i ↦ (𝒜 i).baseChange R')
        (gradedBaseChangeMap (R' := R') 𝒜 f) d n := by
  let 𝓑 := fun i ↦ (𝒜 i).baseChange R'
  let ψ := gradedBaseChangeMap (R' := R') 𝒜
  have hfB : ψ f ∈ 𝓑 d := ψ.map_mem hf
  induction z using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (twistAway 𝓑 (ψ f) d n).zero_mem
  | tmul r x =>
      rw [twistFullBaseChangeMap_tmul]
      let y : twistAway 𝓑 (ψ f) d n :=
        ⟨localizationBaseChangeMap (R' := R') 𝒜 f x,
          localizationBaseChangeMap_mem_twistAway 𝒜 f d hf n x x.property⟩
      exact coe_smul_twistAway 𝓑 (ψ f) d n r y ▸ (r • y).property
  | add z₁ z₂ h₁ h₂ =>
      simpa only [map_add] using (twistAway 𝓑 (ψ f) d n).add_mem h₁ h₂

private noncomputable def twistBaseChangeLinearMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (n : ℤ) :
    R' ⊗[R] twistAway 𝒜 f d n →ₗ[R']
      twistAway (fun i ↦ (𝒜 i).baseChange R')
        (gradedBaseChangeMap (R' := R') 𝒜 f) d n where
  toFun z := ⟨twistFullBaseChangeMap 𝒜 f d n z,
    twistFullBaseChangeMap_mem 𝒜 f d hf n z⟩
  map_add' x y := Subtype.ext (map_add (twistFullBaseChangeMap 𝒜 f d n) x y)
  map_smul' r x := by
    apply Subtype.ext
    simp only [RingHom.id_apply, map_smul]
    exact (coe_smul_twistAway (fun i ↦ (𝒜 i).baseChange R')
      (gradedBaseChangeMap (R' := R') 𝒜 f) d n r
      ⟨twistFullBaseChangeMap 𝒜 f d n x,
        twistFullBaseChangeMap_mem 𝒜 f d hf n x⟩).symm

private lemma twistIndex_step (d : ℕ) (n : ℤ) (k e m : ℕ)
    (he : (e : ℤ) = (k * d : ℕ) + n) :
    ((e + m * d : ℕ) : ℤ) = ((k + m) * d : ℕ) + n := by
  simp only [Nat.cast_add, Nat.cast_mul, Nat.add_mul] at *
  omega

/-- Every twist has a numerator degree `e` over some power `f ^ k`. -/
private lemma exists_twist_index (d : ℕ) (hd : 0 < d) (n : ℤ) :
    ∃ k e : ℕ, (e : ℤ) = (k * d : ℕ) + n := by
  have hk : (-n) ≤ (n.natAbs : ℤ) := Lean.Omega.Int.neg_le_natAbs
  have hkd : n.natAbs ≤ n.natAbs * d := Nat.le_mul_of_pos_right _ hd
  exact ⟨n.natAbs, _, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (n.natAbs * d : ℕ) + n)⟩

/-- Two numerator degrees of the same twist differ by the corresponding powers of `d`. -/
private lemma twistIndex_swap (d : ℕ) (n : ℤ) (k e l j : ℕ)
    (he : (e : ℤ) = (k * d : ℕ) + n) (hj : (j : ℤ) = (l * d : ℕ) + n) :
    e + l * d = j + k * d := by
  simp only [Nat.cast_mul] at he hj
  omega

private lemma twistAway_fraction_surjective
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (n : ℤ)
    (z : twistAway 𝒜 f d n) :
    ∃ (k e : ℕ) (x : A), (e : ℤ) = (k * d : ℕ) + n ∧
      x ∈ 𝒜 e ∧
      (z : Localization (Submonoid.powers f)) = Localization.mk x
        ⟨f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers f) k⟩ := by
  let P : Localization (Submonoid.powers f) → Prop :=
    fun z => ∃ (k e : ℕ) (x : A), (e : ℤ) = (k * d : ℕ) + n ∧
      x ∈ 𝒜 e ∧ z = Localization.mk x
        ⟨f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers f) k⟩
  change P z
  have hz : (z : Localization (Submonoid.powers f)) ∈ twistAway 𝒜 f d n := z.property
  refine Submodule.span_induction (p := fun z _ => P z) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨k, e, x, he, hx, rfl⟩
    exact ⟨k, e, x, he, hx, rfl⟩
  · obtain ⟨k, e, he⟩ := exists_twist_index d hd n
    refine ⟨k, e, 0, he, (𝒜 e).zero_mem, ?_⟩
    exact (Localization.mk_zero _).symm
  · rintro x y _ _ ⟨k, e, a, he, ha, rfl⟩ ⟨l, j, b, hj, hb, rfl⟩
    let E := e + l * d
    have hE : (E : ℤ) = ((k + l) * d : ℕ) + n := twistIndex_step d n k e l he
    have hej := twistIndex_swap d n k e l j he hj
    have h₁ : a * f ^ l ∈ 𝒜 E :=
      SetLike.mul_mem_graded ha (SetLike.pow_mem_graded l hf)
    have h₂ : b * f ^ k ∈ 𝒜 E := by
      have h := SetLike.mul_mem_graded hb (SetLike.pow_mem_graded k hf)
      change b * f ^ k ∈ 𝒜 (j + k * d) at h
      simpa only [E, hej] using h
    refine ⟨k + l, E, a * f ^ l + b * f ^ k, hE,
      (𝒜 E).add_mem h₁ h₂, ?_⟩
    rw [Localization.add_mk]
    congr 1 <;> simp [pow_add, mul_comm, add_comm]
  · rintro c z _ ⟨k, e, a, he, ha, rfl⟩
    obtain ⟨m, b, hb, rfl⟩ := Away.mk_surjective 𝒜 hf c
    let E := m * d + e
    have hE : (E : ℤ) = ((m + k) * d : ℕ) + n := by
      simp only [E, Nat.cast_add, Nat.cast_mul, Nat.add_mul] at *
      omega
    have hba : b * a ∈ 𝒜 E :=
      SetLike.mul_mem_graded hb ha
    refine ⟨m + k, E, b * a, hE, hba, ?_⟩
    change (Away.mk 𝒜 hf m b hb).val * Localization.mk a _ = _
    rw [Away.val_mk, Localization.mk_mul]
    congr 1
    simp [pow_add, mul_comm]

private noncomputable def twistNumeratorMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (n : ℤ) (k e : ℕ)
    (he : (e : ℤ) = (k * d : ℕ) + n) :
    𝒜 e →ₗ[R] twistAway 𝒜 f d n where
  toFun x := ⟨Localization.mk (x : A)
      ⟨f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers f) k⟩,
    Submodule.subset_span ⟨k, e, (x : A), he, x.property, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change Localization.mk ((x : A) + y) _ =
      Localization.mk (x : A) _ + Localization.mk (y : A) _
    exact (Localization.add_mk_self _ _ _).symm
  map_smul' r x := by
    apply Subtype.ext
    simp only [RingHom.id_apply]
    rw [coe_smul_twistAway 𝒜 f d n r ⟨Localization.mk (x : A)
      ⟨f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers f) k⟩,
      Submodule.subset_span ⟨k, e, (x : A), he, x.property, rfl⟩⟩]
    change Localization.mk (r • (x : A)) _ =
      r • Localization.mk (x : A) _
    simp only [Algebra.smul_def]
    rw [IsScalarTower.algebraMap_apply R A (Localization (Submonoid.powers f)) r]
    simpa only [Localization.mk_eq_mk'_apply, Algebra.smul_def] using
      (IsLocalization.smul_mk' (S := Localization (Submonoid.powers f))
        (algebraMap R A r) (x : A)
        ⟨f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers f) k⟩).symm

private noncomputable def twistNumeratorBaseChangeMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (n : ℤ) (k e : ℕ)
    (he : (e : ℤ) = (k * d : ℕ) + n) :
    R' ⊗[R] 𝒜 e →ₗ[R'] R' ⊗[R] twistAway 𝒜 f d n :=
  (twistNumeratorMap 𝒜 f d n k e he).baseChange R'

private lemma twistBaseChangeLinearMap_numerator
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (n : ℤ) (k e : ℕ)
    (he : (e : ℤ) = (k * d : ℕ) + n)
    (q : R' ⊗[R] 𝒜 e) :
    ((twistBaseChangeLinearMap (R' := R') 𝒜 f d hf n
      (twistNumeratorBaseChangeMap 𝒜 f d n k e he q) :
      twistAway (fun i ↦ (𝒜 i).baseChange R')
        (gradedBaseChangeMap (R' := R') 𝒜 f) d n) :
      Localization (Submonoid.powers (gradedBaseChangeMap (R' := R') 𝒜 f))) =
      Localization.mk
        (((𝒜 e).toBaseChange R' q : (𝒜 e).baseChange R') : R' ⊗[R] A)
        ⟨(gradedBaseChangeMap (R' := R') 𝒜 f) ^ k,
          Submonoid.pow_mem _
            (Submonoid.mem_powers (gradedBaseChangeMap (R' := R') 𝒜 f)) k⟩ := by
  let ψ := gradedBaseChangeMap (R' := R') 𝒜
  induction q using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, Submodule.coe_zero]
      exact (Localization.mk_zero _).symm
  | tmul r x =>
      simp only [twistNumeratorBaseChangeMap, LinearMap.baseChange_tmul,
        Submodule.coe_toBaseChange_tmul]
      change twistFullBaseChangeMap (R' := R') 𝒜 f d n
          (r ⊗ₜ[R] (twistNumeratorMap 𝒜 f d n k e he x)) =
        Localization.mk (r ⊗ₜ[R] (x : A)) _
      rw [twistFullBaseChangeMap_tmul]
      change r • localizationBaseChangeMap (R' := R') 𝒜 f
        (Localization.mk (x : A) _) = _
      rw [localizationBaseChangeMap_mk]
      have ht : (r ⊗ₜ[R] (x : A)) = r • ψ (x : A) := by
        simp [ψ, gradedBaseChangeMap_apply, TensorProduct.smul_tmul']
      rw [ht]
      simp only [Algebra.smul_def]
      rw [IsScalarTower.algebraMap_apply R' (R' ⊗[R] A)
        (Localization (Submonoid.powers (ψ f))) r]
      simpa only [Localization.mk_eq_mk'_apply, Algebra.smul_def] using
        (IsLocalization.smul_mk' (S := Localization (Submonoid.powers (ψ f)))
          (algebraMap R' (R' ⊗[R] A) r) (ψ x)
          ⟨ψ f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers (ψ f)) k⟩)
  | add q₁ q₂ h₁ h₂ =>
      simp only [map_add, Submodule.coe_add]
      rw [h₁, h₂]
      exact Localization.add_mk_self _ _ _

private lemma twistBaseChangeLinearMap_surjective
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (n : ℤ) :
    Function.Surjective (twistBaseChangeLinearMap (R' := R') 𝒜 f d hf n) := by
  let 𝓑 := fun i ↦ (𝒜 i).baseChange R'
  let ψ := gradedBaseChangeMap (R' := R') 𝒜
  have hfB : ψ f ∈ 𝓑 d := ψ.map_mem hf
  intro y
  obtain ⟨k, e, x, he, hx, hy⟩ :=
    twistAway_fraction_surjective 𝓑 (ψ f) d hfB hd n y
  obtain ⟨q, hq⟩ := (𝒜 e).toBaseChange_surjective' (A := R') hx
  refine ⟨twistNumeratorBaseChangeMap 𝒜 f d n k e he q, ?_⟩
  apply Subtype.ext
  rw [twistBaseChangeLinearMap_numerator, hq]
  exact hy.symm

private noncomputable def twistMultiplyPowMap
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d e m : ℕ) (hf : f ∈ 𝒜 d) :
    𝒜 e →ₗ[R] 𝒜 (e + m * d) where
  toFun x := ⟨(x : A) * f ^ m, by
    have h := SetLike.mul_mem_graded x.property (SetLike.pow_mem_graded m hf)
    change (x : A) * f ^ m ∈ 𝒜 (e + m * d) at h
    exact h⟩
  map_add' x y := by ext; simp [add_mul]
  map_smul' r x := by ext; simp

private lemma twistNumeratorBaseChangeMap_mul_pow
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (n : ℤ) (k e m : ℕ)
    (he : (e : ℤ) = (k * d : ℕ) + n)
    (q : R' ⊗[R] 𝒜 e) :
    twistNumeratorBaseChangeMap 𝒜 f d n k e he q =
      twistNumeratorBaseChangeMap 𝒜 f d n (k + m) (e + m * d)
        (twistIndex_step d n k e m he)
        ((twistMultiplyPowMap 𝒜 f d e m hf).baseChange R' q) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
      simp only [twistNumeratorBaseChangeMap, LinearMap.baseChange_tmul]
      congr 1
      apply Subtype.ext
      exact localizationMk_mul_pow f x k m
  | add q₁ q₂ h₁ h₂ =>
      simpa only [map_add] using congrArg₂ (· + ·) h₁ h₂

private lemma twistNumeratorBaseChangeMap_surjective
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (n : ℤ) :
    ∀ z : R' ⊗[R] twistAway 𝒜 f d n,
      ∃ (k e : ℕ) (he : (e : ℤ) = (k * d : ℕ) + n)
        (q : R' ⊗[R] 𝒜 e),
        twistNumeratorBaseChangeMap 𝒜 f d n k e he q = z := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      obtain ⟨k, e, he⟩ := exists_twist_index d hd n
      exact ⟨k, e, he, 0, by simp⟩
  | tmul r x =>
      obtain ⟨k, e, a, he, ha, hx⟩ :=
        twistAway_fraction_surjective 𝒜 f d hf hd n x
      let a' : 𝒜 e := ⟨a, ha⟩
      have hxa : (twistNumeratorMap 𝒜 f d n k e he a') = x := Subtype.ext hx.symm
      refine ⟨k, e, he, r ⊗ₜ[R] a', ?_⟩
      simp only [twistNumeratorBaseChangeMap, LinearMap.baseChange_tmul]
      exact congrArg (fun y => r ⊗ₜ[R] y) hxa
  | add z₁ z₂ h₁ h₂ =>
      obtain ⟨k, e, he, q₁, rfl⟩ := h₁
      obtain ⟨l, j, hj, q₂, rfl⟩ := h₂
      let E := e + l * d
      have hE : (E : ℤ) = ((k + l) * d : ℕ) + n :=
        twistIndex_step d n k e l he
      have hej := twistIndex_swap d n k e l j he hj
      let q₁' : R' ⊗[R] 𝒜 E :=
        (twistMultiplyPowMap 𝒜 f d e l hf).baseChange R' q₁
      let q₂' : R' ⊗[R] 𝒜 E :=
        cast (congrArg (fun a : ℕ => R' ⊗[R] 𝒜 a) hej.symm)
          ((twistMultiplyPowMap 𝒜 f d j k hf).baseChange R' q₂)
      have hcast {a b c h : ℕ} (hab : a = b) (hch : c = h)
          (hc : (c : ℤ) = (a * d : ℕ) + n)
          (hh : (h : ℤ) = (b * d : ℕ) + n)
          (q : R' ⊗[R] 𝒜 c) :
          twistNumeratorBaseChangeMap 𝒜 f d n a c hc q =
          twistNumeratorBaseChangeMap 𝒜 f d n b h hh
            (cast (congrArg (fun t : ℕ => R' ⊗[R] 𝒜 t) hch) q) := by
        cases hab
        cases hch
        rfl
      have h₁' := twistNumeratorBaseChangeMap_mul_pow
        (R' := R') 𝒜 f d hf n k e l he q₁
      have h₂' : twistNumeratorBaseChangeMap 𝒜 f d n l j hj q₂ =
          twistNumeratorBaseChangeMap 𝒜 f d n (k + l) E hE q₂' := by
        calc
          _ = twistNumeratorBaseChangeMap 𝒜 f d n (l + k) (j + k * d)
              (twistIndex_step d n l j k hj)
              ((twistMultiplyPowMap 𝒜 f d j k hf).baseChange R' q₂) :=
            twistNumeratorBaseChangeMap_mul_pow (R' := R')
              𝒜 f d hf n l j k hj q₂
          _ = _ := hcast (Nat.add_comm l k) hej.symm
            (twistIndex_step d n l j k hj) hE _
      refine ⟨k + l, E, hE, q₁' + q₂', ?_⟩
      rw [map_add]
      exact congrArg₂ (· + ·) h₁'.symm h₂'.symm

private lemma twistBaseChangeLinearMap_eq_zero
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (n : ℤ)
    (z : R' ⊗[R] twistAway 𝒜 f d n)
    (hz : twistBaseChangeLinearMap (R' := R') 𝒜 f d hf n z = 0) :
    z = 0 := by
  obtain ⟨k, e, he, q, rfl⟩ :=
    twistNumeratorBaseChangeMap_surjective (R' := R') 𝒜 f d hf hd n z
  let ψ := gradedBaseChangeMap (R' := R') 𝒜
  have hzero : (Localization.mk
      (((𝒜 e).toBaseChange R' q : (𝒜 e).baseChange R') : R' ⊗[R] A)
      ⟨(ψ f) ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers (ψ f)) k⟩ :
      Localization (Submonoid.powers (ψ f))) = 0 := by
    rw [← twistBaseChangeLinearMap_numerator (R' := R') 𝒜 f d hf n k e he q]
    exact congrArg (fun y : twistAway (fun i ↦ (𝒜 i).baseChange R') (ψ f) d n =>
      (y : Localization (Submonoid.powers (ψ f)))) hz
  obtain ⟨m, hm⟩ := (localizationMk_eq_zero_iff (ψ f)
    (((𝒜 e).toBaseChange R' q : (𝒜 e).baseChange R') : R' ⊗[R] A) k).mp hzero
  have hqzero := baseChange_eq_zero_of_mul_pow (R' := R') 𝒜 f m
    (twistMultiplyPowMap 𝒜 f d e m hf) (fun _ ↦ rfl) q hm
  rw [twistNumeratorBaseChangeMap_mul_pow (R' := R') 𝒜 f d hf n k e m he q,
    hqzero, map_zero]

private lemma twistBaseChangeLinearMap_injective
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (n : ℤ) :
    Function.Injective (twistBaseChangeLinearMap (R' := R') 𝒜 f d hf n) :=
  (injective_iff_map_eq_zero _).mpr (twistBaseChangeLinearMap_eq_zero 𝒜 f d hf hd n)

private noncomputable def twistBaseChangeLinearEquiv
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (n : ℤ) :
    R' ⊗[R] twistAway 𝒜 f d n ≃ₗ[R']
      twistAway (fun i ↦ (𝒜 i).baseChange R')
        (gradedBaseChangeMap (R' := R') 𝒜 f) d n :=
  LinearEquiv.ofBijective (twistBaseChangeLinearMap 𝒜 f d hf n)
    ⟨twistBaseChangeLinearMap_injective 𝒜 f d hf hd n,
      twistBaseChangeLinearMap_surjective 𝒜 f d hf hd n⟩

private lemma twistFullBaseChangeMap_smul
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (n : ℤ)
    (r : R') (a : Away 𝒜 f) (x : twistAway 𝒜 f d n) :
    twistFullBaseChangeMap (R' := R') 𝒜 f d n (r ⊗ₜ[R] (a • x)) =
      algebraMap R' (Localization (Submonoid.powers
        (gradedBaseChangeMap (R' := R') 𝒜 f))) r *
        (Away.map (gradedBaseChangeMap (R' := R') 𝒜) f a).val *
          localizationBaseChangeMap (R' := R') 𝒜 f x := by
  rw [twistFullBaseChangeMap_tmul]
  have hax : ((a • x : twistAway 𝒜 f d n) :
      Localization (Submonoid.powers f)) =
      a.val * (x : Localization (Submonoid.powers f)) := by
    rw [Submodule.coe_smul]
    rfl
  rw [hax, map_mul, localizationBaseChangeMap_away_val 𝒜 f d hf, Algebra.smul_def r
    ((Away.map (gradedBaseChangeMap (R' := R') 𝒜) f a).val *
      localizationBaseChangeMap (R' := R') 𝒜 f x)]
  ring

private lemma awayAlgebraMap_val
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (r : R) :
    ((algebraMap R (Away 𝒜 f)) r).val =
      algebraMap R (Localization (Submonoid.powers f)) r := by
  rfl

/-- Scalar extension commutes canonically with degree-zero localization at a
homogeneous element, simultaneously for the graded ring and all its twists. -/
noncomputable opaque standardOpenBaseChange (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    StandardOpenBaseChange (R' := R') 𝒜 f d := by
  refine ⟨awayBaseChangeAlgEquiv 𝒜 f d hf,
    (fun n => twistBaseChangeLinearEquiv 𝒜 f d hf hd n), ?_, ?_, ?_⟩
  · intro r x
    change awayBaseChangeAlgHom (R' := R') 𝒜 f d hf (r ⊗ₜ[R] x) = _
    exact awayBaseChangeAlgHom_tmul 𝒜 f d hf r x
  · intro n r k e x he hx
    change ((twistBaseChangeLinearMap (R' := R') 𝒜 f d hf n
      (r ⊗ₜ[R]
        (⟨Localization.mk x
          ⟨f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers f) k⟩,
            Submodule.subset_span ⟨k, e, x, he, hx, rfl⟩⟩ :
          twistAway 𝒜 f d n))) :
      Localization (Submonoid.powers (gradedBaseChangeMap (R' := R') 𝒜 f))) = _
    change twistFullBaseChangeMap (R' := R') 𝒜 f d n
      (r ⊗ₜ[R] (⟨Localization.mk x
        ⟨f ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers f) k⟩,
          Submodule.subset_span ⟨k, e, x, he, hx, rfl⟩⟩ :
          twistAway 𝒜 f d n)) = _
    rw [twistFullBaseChangeMap_tmul, localizationBaseChangeMap_mk]
    simp only [gradedBaseChangeMap_apply]
    exact Algebra.smul_def r
      (Localization.mk (1 ⊗ₜ[R] x)
        ⟨((1 : R') ⊗ₜ[R] f) ^ k, Submonoid.pow_mem _
          (Submonoid.mem_powers ((1 : R') ⊗ₜ[R] f)) k⟩ :
        Localization (Submonoid.powers ((1 : R') ⊗ₜ[R] f)))
  · intro n r a x
    apply Subtype.ext
    change twistFullBaseChangeMap (R' := R') 𝒜 f d n
        (r ⊗ₜ[R] (a • x)) =
      (((awayBaseChangeAlgEquiv (R' := R') 𝒜 f d hf (r ⊗ₜ[R] a)) •
        (twistBaseChangeLinearMap (R' := R') 𝒜 f d hf n (1 ⊗ₜ[R] x)) :
        twistAway (fun i ↦ (𝒜 i).baseChange R')
          (gradedBaseChangeMap (R' := R') 𝒜 f) d n) :
        Localization (Submonoid.powers (gradedBaseChangeMap (R' := R') 𝒜 f)))
    rw [twistFullBaseChangeMap_smul 𝒜 f d hf n r a x, Submodule.coe_smul]
    change _ = (awayBaseChangeAlgEquiv (R' := R') 𝒜 f d hf (r ⊗ₜ[R] a)).val *
      twistFullBaseChangeMap (R' := R') 𝒜 f d n (1 ⊗ₜ[R] x)
    rw [twistFullBaseChangeMap_one_tmul]
    change _ = (awayBaseChangeAlgHom (R' := R') 𝒜 f d hf (r ⊗ₜ[R] a)).val *
      localizationBaseChangeMap (R' := R') 𝒜 f x
    rw [awayBaseChangeAlgHom_tmul, HomogeneousLocalization.val_mul,
      awayAlgebraMap_val]

end Stacks.ProjStandardOpenBaseChange
