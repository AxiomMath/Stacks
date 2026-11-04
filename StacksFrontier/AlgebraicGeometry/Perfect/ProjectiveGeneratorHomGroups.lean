module

public import Mathlib.Algebra.MvPolynomial.Division
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveGeneratorEndomorphisms
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms between twists of the structure sheaf on projective space

Let `A` be a commutative ring, `S = A[X₀, …, Xₙ]` and `X = ℙⁿ_A = Proj(S)`. For integers `c`,
`d`, `e` with `c + d = e`, multiplication by a homogeneous polynomial of degree `c` is a morphism
`𝒪_X(d) ⟶ 𝒪_X(e)`. This file proves that every morphism `𝒪_X(d) ⟶ 𝒪_X(e)` arises this way from
exactly one element of `S_c`, as soon as `c ≥ 0` or `n ≥ 1`. Applied to the entries of the
matrix algebra `R` of [Stacks, Tag 0CS9], this is the identification

`R = Hom_{𝒪_X}(P, P)`, `P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveGenerator.twistMul_injective`: multiplication by a
  homogeneous polynomial determines the polynomial.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.exists_twistMul_eq`: every morphism
  `𝒪_X(d) ⟶ 𝒪_X(e)` is multiplication by a homogeneous polynomial of degree `e - d`, provided
  `0 ≤ e - d` or `0 < n`.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.bijective_twistMul`: the two together,
  `Hom(𝒪(d), 𝒪(e)) = S_{e-d}`.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.bijective_matrixToEnd` and
  `Stacks.AlgebraicGeometry.ProjectiveGenerator.matrixRingEquivEnd`: **the upper triangular
  matrix algebra is the endomorphism ring of `P`.**

## The argument

On the standard open `D₊(Xₖ)` the twist `𝒪(d)` has the nowhere vanishing section `Xₖ^d`. A
morphism `φ : 𝒪(d) ⟶ 𝒪(e)` sends it to a section of `𝒪(e)` over `D₊(Xₖ)`, which is a single
fraction `gₖ / Xₖ^{Nₖ}` by [Stacks, Tag 01M6]; linearity of `φ` over the structure sheaf then
shows that, at every point of `D₊(Xₖ)`, `φ` is multiplication by `hₖ / Xₖ^{Mₖ}` for one
homogeneous `hₖ`. Comparing two charts on their overlap gives `X_l^{M_l} hₖ = Xₖ^{Mₖ} h_l` in
`S`, because a homogeneous element vanishing at every point of `D₊(Xₖ X_l)` is killed by a power
of `Xₖ X_l`, and the variables are nonzerodivisors. In the polynomial ring these relations force
`hₖ = Xₖ^{Mₖ} p` for a single `p ∈ S_c`, and then `φ` is multiplication by `p` at every point.

## References

* [Stacks Project, Tag 0CS9](https://stacks.math.columbia.edu/tag/0CS9)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace Stacks.AlgebraicGeometry.ProjectiveGenerator

universe u w

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Fractions in a graded ring -/

section Graded

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The ideal of a point of `Proj` is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

omit [GradedRing 𝒮] in
/-- An element of `S_c` is in the degree-`c` piece of the integer-extended grading. -/
public theorem mem_integerGrading_of_mem {c : ℕ} {x : S} (hx : x ∈ 𝒮 c) :
    x ∈ integerGrading 𝒮 (c : ℤ) := by
  rw [integerGrading_natCast, mem_homogeneousSubmodule]
  exact hx

omit [GradedRing 𝒮] in
/-- Membership in the integer-extended grading only depends on the degree. -/
public theorem mem_integerGrading_congr {i j : ℤ} (h : i = j) {x : S}
    (hx : x ∈ integerGrading 𝒮 i) : x ∈ integerGrading 𝒮 j :=
  h ▸ hx

/-- A power of an element of degree `k` lies in degree `r * k` of the integer-extended
grading. -/
public theorem pow_mem_integerGrading {f : S} {k : ℕ} (hf : f ∈ 𝒮 k) (r : ℕ) :
    f ^ r ∈ integerGrading 𝒮 ((r : ℤ) * k) := by
  have h := mem_integerGrading_of_mem 𝒮 (SetLike.pow_mem_graded r hf)
  rwa [smul_eq_mul, Nat.cast_mul] at h

/-- **Elements of `S(t)₍f₎` are single fractions.** Every element of the degree-zero
localization of the twist `S(t)` away from `f ∈ S_k` is `g / f ^ N` with `g` homogeneous of
degree `N k + t`. -/
public theorem exists_eq_mk_of_mem_degreeZero {f : S} {k : ℕ} (hf : f ∈ 𝒮 k) (t : ℤ)
    {z : LocalizedModule.Away (R := S) f S}
    (hz : z ∈ GradedModuleDegreeZeroLocalization 𝒮 (twistGrading (S := S) 𝒮 t) f) :
    ∃ (N : ℕ) (g : S), g ∈ integerGrading 𝒮 ((N : ℤ) * k + t) ∧
      z = LocalizedModule.mk g (⟨f ^ N, N, rfl⟩ : Submonoid.powers f) := by
  classical
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k', N, hf', g, hg, rfl⟩ := hy
    by_cases hfN : f ^ N = 0
    · have : Subsingleton (LocalizedModule.Away (R := S) f S) :=
        LocalizedModule.subsingleton (S := Submonoid.powers f) (M := S) (by
          rw [← hfN]; exact ⟨N, rfl⟩)
      exact ⟨0, 0, zero_mem _, Subsingleton.elim _ _⟩
    · have hdeg : N • k' = N • k :=
        DirectSum.degree_eq_of_mem_mem 𝒮
          (SetLike.pow_mem_graded N hf') (SetLike.pow_mem_graded N hf) hfN
      refine ⟨N, g, mem_integerGrading_congr 𝒮 ?_ hg, rfl⟩
      have hdeg' : ((N : ℤ) * k' : ℤ) = (N : ℤ) * k := by
        simpa [smul_eq_mul] using congrArg (fun m : ℕ => (m : ℤ)) hdeg
      rw [nsmul_eq_mul, hdeg']
  | zero => exact ⟨0, 0, zero_mem _, (LocalizedModule.zero_mk _).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨N, g, hg, rfl⟩ := hy
    obtain ⟨M, g', hg', rfl⟩ := hz
    refine ⟨N + M, f ^ M * g + f ^ N * g', add_mem ?_ ?_, ?_⟩
    · exact mem_integerGrading_congr 𝒮 (by push_cast; ring)
        (mul_mem_integerGrading' 𝒮 (pow_mem_integerGrading 𝒮 hf M) hg)
    · exact mem_integerGrading_congr 𝒮 (by push_cast; ring)
        (mul_mem_integerGrading' 𝒮 (pow_mem_integerGrading 𝒮 hf N) hg')
    · rw [LocalizedModule.mk_add_mk]
      congr 1
      exact Subtype.ext (by simp [pow_add])
  | smul r y _ hy =>
    obtain ⟨N, g, hg, rfl⟩ := hy
    obtain ⟨M, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒮 hf r
    refine ⟨M + N, b * g, ?_, ?_⟩
    · exact mem_integerGrading_congr 𝒮
        (by simp only [smul_eq_mul, Nat.cast_mul]; push_cast; ring)
        (mul_mem_integerGrading' 𝒮 (mem_integerGrading_of_mem 𝒮 hb) hg)
    · have key : (HomogeneousLocalization.Away.mk 𝒮 hf M b hb).val •
          LocalizedModule.mk g (⟨f ^ N, N, rfl⟩ : Submonoid.powers f) =
            LocalizedModule.mk (b * g) (⟨f ^ (M + N), M + N, rfl⟩ : Submonoid.powers f) := by
        rw [HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
        congr 1
        exact Subtype.ext (by simp [pow_add])
      exact key

/-- A fraction over the powers of `f` vanishes exactly when a power of `f` kills its
numerator. -/
public theorem mk_away_eq_zero_iff (f m : S) (s : Submonoid.powers f) :
    LocalizedModule.mk m s = 0 ↔ ∃ r : ℕ, f ^ r * m = 0 := by
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
  simp only [Submonoid.smul_def, one_smul, smul_eq_mul, mul_zero]
  constructor
  · rintro ⟨⟨_, r, rfl⟩, hu⟩
    exact ⟨r, hu⟩
  · rintro ⟨r, hr⟩
    exact ⟨⟨f ^ r, r, rfl⟩, hr⟩

/-- **A homogeneous element vanishing at every point of `D₊(f)` is killed by a power of `f`**,
for `f` homogeneous of positive degree. This is the injectivity of the comparison
`M₍f₎ → Γ(D₊(f), M̃)` of [Stacks, Tag 01M6], applied to the fraction `D / 1`. -/
public theorem exists_pow_mul_eq_zero {f : S} {k : ℕ} (hf : f ∈ 𝒮 k) (hk : 0 < k) {D : S}
    {δ : ℤ} (hD : D ∈ integerGrading 𝒮 δ)
    (h : ∀ x : ProjectiveSpectrum.basicOpen 𝒮 f,
      (LocalizedModule.mk D 1 : LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl S) =
        0) :
    ∃ r : ℕ, f ^ r * D = 0 := by
  have hD0 : D ∈ twistGrading (S := S) 𝒮 δ ((0 : ℕ) • (k : ℤ)) := by
    rw [twistGrading_apply, zero_smul, zero_add]
    exact hD
  have hsec : degreeZeroToSection 𝒮 (twistGrading (S := S) 𝒮 δ) f
      (degreeZeroFraction 𝒮 (twistGrading (S := S) 𝒮 δ) hf 0 D hD0) =
        degreeZeroToSection 𝒮 (twistGrading (S := S) 𝒮 δ) f 0 := by
    rw [map_zero]
    refine Subtype.ext (funext fun x => ?_)
    rw [degreeZeroToSection_fraction]
    refine Eq.trans ?_ (h x)
    congr 1
    exact Subtype.ext (pow_zero f)
  have h0 := congrArg Subtype.val (degreeZeroToSection_injective 𝒮 _ hf hk hsec)
  exact (mk_away_eq_zero_iff f D _).mp h0

end Graded

/-! ### Localizations -/

section Localization

variable {R : Type*} [CommRing R] {P : Submonoid R}

/-- An element of the submonoid can be cancelled from a scalar multiple in a localized
module. -/
public theorem smul_cancel_of_mem {M : Type*} [AddCommGroup M] [Module R M] {t : R}
    (ht : t ∈ P) {a b : LocalizedModule P M} (h : t • a = t • b) : a = b := by
  have hu := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap P M) ⟨t, ht⟩
  refine ((Module.End.isUnit_iff _).mp hu).1 ?_
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
  exact h

/-- If `D` kills a fraction with numerator in the submonoid, then `D` vanishes in the
localization. -/
public theorem mk_one_eq_zero_of_smul_mk {D a : R} (ha : a ∈ P) {s : P}
    (h : D • LocalizedModule.mk a s = (0 : LocalizedModule P R)) :
    LocalizedModule.mk D (1 : P) = 0 := by
  rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk (1 : P), LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  rw [← LocalizedModule.zero_mk (1 : P), LocalizedModule.mk_eq]
  refine ⟨u * ⟨a, ha⟩, ?_⟩
  simp only [Submonoid.smul_def, one_smul, smul_eq_mul, mul_zero, Submonoid.coe_mul] at hu ⊢
  rw [← hu]
  ring

end Localization

/-! ### Morphisms of twists act pointwise by multiplication -/

section Twists

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] {f : S} (hf : f ∈ 𝒮 1)

/-- The ideal of a point of `Proj` is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- For `f` of degree one, the section `f^m` of `𝒪(m)` over an open contained in `D₊(f)`: the
fraction `f^{max m 0} / f^{max (-m) 0}`. -/
public def powSection (m : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    (twistingSheaf 𝒮 m).val.obj (op W) :=
  ⟨fun x => LocalizedModule.mk (f ^ m.toNat)
      ⟨f ^ (-m).toNat,
        x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW x.2) _⟩, fun x =>
    ⟨W, x.2, 𝟙 _, (-m).toNat, f ^ m.toNat, f ^ (-m).toNat,
      mem_integerGrading_congr _ (by push_cast; omega)
        (pow_mem_integerGrading _ hf m.toNat),
      by simpa using SetLike.pow_mem_graded (-m).toNat hf,
      fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW y.2) _, fun _ => rfl⟩⟩

/-- The value of `powSection` at a point is the fraction `f^{max m 0} / f^{max (-m) 0}`. -/
@[simp] public theorem powSection_apply (m : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (x : W) :
    (powSection 𝒮 hf m hW).1 x = LocalizedModule.mk (f ^ m.toNat)
      ⟨f ^ (-m).toNat,
        x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW x.2) _⟩ :=
  rfl

/-- Restriction of sections of a twist is restriction of functions. -/
public theorem twistingSheaf_map_apply {m : ℤ} {U V : Opens (ProjectiveSpectrum.top 𝒮)}
    (i : V ⟶ U) (a : (twistingSheaf 𝒮 m).val.obj (op U)) (y : V) :
    ((twistingSheaf 𝒮 m).val.map i.op a).1 y = a.1 (i y) :=
  rfl

/-- Functions act on sections of a twist pointwise. -/
public theorem twistingSheaf_smul_apply {m : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒮)}
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U))
    (a : (twistingSheaf 𝒮 m).val.obj (op U)) (y : U) :
    ((show (ProjTrivialization.projRingSheaf 𝒮).obj.obj (op U) from r) • a).1 y =
      HomogeneousLocalization.val (r.1 y) • a.1 y :=
  rfl

/-- **A morphism of twists is determined on `D₊(f)` by its value on `f^d`.** If `φ` sends `f^d`
to `g / f^N` on `D₊(f)`, then at every point of `D₊(f)` it multiplies every section by
`f^{-d} g / f^N`: a section `t` of `𝒪(d)` is `ρ · f^d` for a function `ρ` near the point, and `φ`
is linear over the functions. -/
public theorem pow_smul_app_apply {d e : ℤ}
    (φ : twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 e)
    {N : ℕ} {g : S}
    (hv : ∀ y : ProjectiveSpectrum.basicOpen 𝒮 f,
      (φ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f))
        (powSection 𝒮 hf d le_rfl)).1 y = LocalizedModule.mk g
          ⟨f ^ N, y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem y.2 N⟩)
    (V : Opens (ProjectiveSpectrum.top 𝒮))
    (t : (twistingSheaf 𝒮 d).val.obj (op V)) (x : V)
    (hx : x.1 ∈ ProjectiveSpectrum.basicOpen 𝒮 f) :
    (f ^ (d.toNat + N) : S) • (φ.val.app (op V) t).1 x =
      (f ^ (-d).toNat * g) • t.1 x := by
  obtain ⟨V', hxV', i', K, m, s, hm, hs, hsn, hval⟩ := t.2 x
  let D := ProjectiveSpectrum.basicOpen 𝒮 f
  let W : Opens (ProjectiveSpectrum.top 𝒮) := V' ⊓ D
  let i : W ⟶ V := homOfLE inf_le_left ≫ i'
  let j : W ⟶ D := homOfLE inf_le_right
  let y : W := ⟨x.1, hxV', hx⟩
  have hnum : m * f ^ (-d).toNat ∈ 𝒮 (K + d.toNat) := by
    have h := mem_integerGrading_congr 𝒮 (j := ((K + d.toNat : ℕ) : ℤ)) (by push_cast; omega)
      (mul_mem_integerGrading' _ hm (pow_mem_integerGrading _ hf (-d).toNat))
    rwa [integerGrading_natCast, mem_homogeneousSubmodule] at h
  have hden : s * f ^ d.toNat ∈ 𝒮 (K + d.toNat) := by
    simpa using SetLike.mul_mem_graded hs (SetLike.pow_mem_graded d.toNat hf)
  have hz (z : W) : s * f ^ d.toNat ∈
      z.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.mul_mem _ (hsn ⟨z.1, z.2.1⟩) (Submonoid.pow_mem _ z.2.2 _)
  let ρ : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W) :=
    ⟨fun z => HomogeneousLocalization.mk ⟨K + d.toNat, ⟨_, hnum⟩, ⟨_, hden⟩, hz z⟩,
      fun z => ⟨W, z.2, 𝟙 _, K + d.toNat, ⟨_, hnum⟩, ⟨_, hden⟩, hz, fun _ => rfl⟩⟩
  have ht : (twistingSheaf 𝒮 d).val.map i.op t =
      (show (ProjTrivialization.projRingSheaf 𝒮).obj.obj (op W) from ρ) •
        (twistingSheaf 𝒮 d).val.map j.op (powSection 𝒮 hf d le_rfl) := by
    refine Subtype.ext (funext fun z => ?_)
    refine (hval ⟨z.1, z.2.1⟩).trans (Eq.trans ?_ (twistingSheaf_smul_apply 𝒮 ρ _ z).symm)
    rw [twistingSheaf_map_apply, powSection_apply, HomogeneousLocalization.val_mk,
      LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp only [Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul]; ring⟩
  have h1 : (φ.val.app (op V) t).1 x = (φ.val.app (op W)
      ((twistingSheaf 𝒮 d).val.map i.op t)).1 y := by
    rw [PresheafOfModules.naturality_apply]
    rfl
  have h2 : (φ.val.app (op W) ((twistingSheaf 𝒮 d).val.map i.op t)).1 y =
      HomogeneousLocalization.val (ρ.1 y) • LocalizedModule.mk g
        ⟨f ^ N, Submonoid.pow_mem _ hx N⟩ := by
    have hsm := (φ.val.app (op W)).hom.map_smul
      (show (ProjTrivialization.projRingSheaf 𝒮).obj.obj (op W) from ρ)
      ((twistingSheaf 𝒮 d).val.map j.op (powSection 𝒮 hf d le_rfl))
    have h3 : (φ.val.app (op W) ((twistingSheaf 𝒮 d).val.map j.op
        (powSection 𝒮 hf d le_rfl))).1 y = LocalizedModule.mk g
          ⟨f ^ N, Submonoid.pow_mem _ hx N⟩ := by
      rw [PresheafOfModules.naturality_apply]
      exact hv ⟨x.1, hx⟩
    rw [ht]
    exact (congrArg (fun a => a.1 y) hsm).trans
      ((twistingSheaf_smul_apply 𝒮 ρ _ y).trans (congrArg _ h3))
  have hx' : t.1 x = LocalizedModule.mk m ⟨s, hsn ⟨x.1, hxV'⟩⟩ := hval ⟨x.1, hxV'⟩
  rw [h1, h2, hx', HomogeneousLocalization.val_mk, LocalizedModule.mk_smul_mk,
    LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  exact ⟨1, by simp only [Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul]; ring⟩

/-- Multiplication by `p` multiplies the value of every section by `p`. -/
public theorem twistMul_app_apply (p : S) (c d e : ℤ) (hp : p ∈ integerGrading 𝒮 c)
    (he : c + d = e) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (t : (twistingSheaf 𝒮 d).val.obj (op U)) (x : U) :
    ((twistMul 𝒮 p c d e hp he).val.app (op U) t).1 x = p • t.1 x := by
  rw [twistMul_apply]
  induction t.1 x using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.map_mk, LocalizedModule.smul'_mk, LinearMap.mulLeft_apply,
      smul_eq_mul]

include hf in
/-- Two multiplication morphisms that agree have numerators agreeing at every point of
`D₊(f)`. -/
public theorem mk_sub_eq_zero_of_twistMul_eq {p q : S} {c d e : ℤ} (hp : p ∈ integerGrading 𝒮 c)
    (hq : q ∈ integerGrading 𝒮 c) (he : c + d = e)
    (h : twistMul 𝒮 p c d e hp he = twistMul 𝒮 q c d e hq he)
    (x : ProjectiveSpectrum.basicOpen 𝒮 f) :
    (LocalizedModule.mk (p - q) 1 :
      LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl S) = 0 := by
  let t := powSection 𝒮 hf d (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f))
  have h1 := twistMul_app_apply 𝒮 p c d e hp he _ t x
  have h2 := twistMul_app_apply 𝒮 q c d e hq he _ t x
  rw [h] at h1
  exact mk_one_eq_zero_of_smul_mk (Submonoid.pow_mem _ x.2 _)
    (show (p - q) • t.1 x = 0 by rw [sub_smul, ← h1, ← h2, sub_self])

/-- **Two charts agree on their overlap.** If `φ` sends `f^d` to `g / f^N` on `D₊(f)` and
`f'^d` to `g' / f'^{N'}` on `D₊(f')`, then `f'^{d⁺ + N'} f^{d⁻} g` and `f^{d⁺ + N} f'^{d⁻} g'`
agree at every point of `D₊(f f')`. -/
public theorem mk_chart_sub_eq_zero {f' : S} (hf' : f' ∈ 𝒮 1) {d e : ℤ}
    (φ : twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 e) {N N' : ℕ} {g g' : S}
    (hv : ∀ y : ProjectiveSpectrum.basicOpen 𝒮 f,
      (φ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f))
        (powSection 𝒮 hf d le_rfl)).1 y = LocalizedModule.mk g
          ⟨f ^ N, y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem y.2 N⟩)
    (hv' : ∀ y : ProjectiveSpectrum.basicOpen 𝒮 f',
      (φ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f'))
        (powSection 𝒮 hf' d le_rfl)).1 y = LocalizedModule.mk g'
          ⟨f' ^ N', y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem y.2 N'⟩)
    (x : ProjectiveSpectrum.basicOpen 𝒮 (f * f')) :
    (LocalizedModule.mk (f' ^ (d.toNat + N') * (f ^ (-d).toNat * g) -
        f ^ (d.toNat + N) * (f' ^ (-d).toNat * g')) 1 :
      LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl S) = 0 := by
  have hx : x.1 ∈ ProjectiveSpectrum.basicOpen 𝒮 f ⊓ ProjectiveSpectrum.basicOpen 𝒮 f' := by
    rw [← ProjectiveSpectrum.basicOpen_mul]
    exact x.2
  let U := ProjectiveSpectrum.basicOpen 𝒮 f
  let t := powSection 𝒮 hf d (le_refl U)
  let x' : U := ⟨x.1, hx.1⟩
  have e1 := pow_smul_app_apply 𝒮 hf φ hv U t x' hx.1
  have e2 := pow_smul_app_apply 𝒮 hf' φ hv' U t x' hx.2
  have h0 : (f' ^ (d.toNat + N') * (f ^ (-d).toNat * g) -
      f ^ (d.toNat + N) * (f' ^ (-d).toNat * g')) • t.1 x' = 0 := by
    rw [sub_smul, mul_smul (f' ^ (d.toNat + N')) (f ^ (-d).toNat * g),
      mul_smul (f ^ (d.toNat + N)) (f' ^ (-d).toNat * g'), ← e1, ← e2,
      smul_comm (f' ^ (d.toNat + N')), sub_self]
  exact mk_one_eq_zero_of_smul_mk (Submonoid.pow_mem _ hx.1 _) h0

/-- **On `D₊(f)`, `φ` is multiplication by `p`** as soon as `f^{d⁻} g = f^{d⁺ + N} p`, where `φ`
sends `f^d` to `g / f^N`. -/
public theorem twistMul_app_apply_eq_of_chart {d e c : ℤ}
    (φ : twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 e) {N : ℕ} {g p : S}
    (hv : ∀ y : ProjectiveSpectrum.basicOpen 𝒮 f,
      (φ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f))
        (powSection 𝒮 hf d le_rfl)).1 y = LocalizedModule.mk g
          ⟨f ^ N, y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem y.2 N⟩)
    (hp : p ∈ integerGrading 𝒮 c) (he : c + d = e)
    (hgp : f ^ (-d).toNat * g = f ^ (d.toNat + N) * p)
    (V : Opens (ProjectiveSpectrum.top 𝒮)) (t : (twistingSheaf 𝒮 d).val.obj (op V)) (x : V)
    (hx : x.1 ∈ ProjectiveSpectrum.basicOpen 𝒮 f) :
    ((twistMul 𝒮 p c d e hp he).val.app (op V) t).1 x = (φ.val.app (op V) t).1 x := by
  refine smul_cancel_of_mem (Submonoid.pow_mem _ hx (d.toNat + N)) ?_
  rw [pow_smul_app_apply 𝒮 hf φ hv V t x hx, twistMul_app_apply, hgp, mul_smul]

/-- The section of `𝒪(e)` over `D₊(f)` that `φ` attaches to `f^d` is a single fraction
`g / f^N`, by [Stacks, Tag 01M6]. -/
public theorem exists_chart {d e : ℤ} (φ : twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 e) :
    ∃ (N : ℕ) (g : S), g ∈ integerGrading 𝒮 ((N : ℤ) + e) ∧
      ∀ y : ProjectiveSpectrum.basicOpen 𝒮 f,
        (φ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f)) (powSection 𝒮 hf d le_rfl)).1 y =
          LocalizedModule.mk g
            ⟨f ^ N, y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem y.2 N⟩ := by
  obtain ⟨b, hb⟩ := degreeZeroToSection_surjective 𝒮 (twistGrading 𝒮 e) hf one_pos
    (φ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f)) (powSection 𝒮 hf d le_rfl))
  obtain ⟨N, g, hg, hbg⟩ := exists_eq_mk_of_mem_degreeZero 𝒮 hf e b.2
  refine ⟨N, g, mem_integerGrading_congr _ (by push_cast; ring) hg, fun y => ?_⟩
  have hy : ((degreeZeroToSection 𝒮 (twistGrading 𝒮 e) f) b).1 y =
      ((φ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f))) (powSection 𝒮 hf d le_rfl)).1 y := by
    rw [hb]
  refine hy.symm.trans ?_
  refine (congrArg (moduleToFiber 𝒮 f y) hbg).trans ?_
  exact moduleToFiber_mk 𝒮 f y g _

/-- Two morphisms of twists agree as soon as they agree on the value of every section at every
point. -/
public theorem twistingSheaf_hom_ext {d e : ℤ} (φ ψ : twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 e)
    (h : ∀ (U : Opens (ProjectiveSpectrum.top 𝒮)) (t : (twistingSheaf 𝒮 d).val.obj (op U))
      (x : U), (φ.val.app (op U) t).1 x = (ψ.val.app (op U) t).1 x) : φ = ψ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun t => Subtype.ext (funext fun x => h U.unop t x)))

/-- **A morphism of twists that is multiplication by `p` on each chart of a cover is
multiplication by `p`.** The charts are standard opens `D₊(Fᵢ)` of degree-one elements covering
`Proj S`, and on each of them `φ` sends `Fᵢ^d` to `gᵢ / Fᵢ^{Nᵢ}` with
`Fᵢ^{d⁻} gᵢ = Fᵢ^{d⁺ + Nᵢ} p`. -/
public theorem twistMul_eq_of_charts {ι : Type*} {F : ι → S} (hF : ∀ i, F i ∈ 𝒮 1)
    (hcov : ∀ x : ProjectiveSpectrum.top 𝒮, ∃ i, x ∈ ProjectiveSpectrum.basicOpen 𝒮 (F i))
    {c d e : ℤ} (φ : twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 e) {N : ι → ℕ} {g : ι → S}
    (hv : ∀ i, ∀ y : ProjectiveSpectrum.basicOpen 𝒮 (F i),
      (φ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 (F i)))
        (powSection 𝒮 (hF i) d le_rfl)).1 y = LocalizedModule.mk (g i)
          ⟨F i ^ N i, y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem y.2 (N i)⟩)
    {p : S} (hp : p ∈ integerGrading 𝒮 c) (he : c + d = e)
    (hgp : ∀ i, F i ^ (-d).toNat * g i = F i ^ (d.toNat + N i) * p) :
    twistMul 𝒮 p c d e hp he = φ :=
  twistingSheaf_hom_ext 𝒮 _ _ fun U t x =>
    let ⟨i, hi⟩ := hcov x.1
    twistMul_app_apply_eq_of_chart 𝒮 (hF i) φ (hv i) hp he (hgp i) U t x hi

end Twists


/-! ### Homogeneous polynomials divisible by powers of the variables -/

section Polynomial

open MvPolynomial

variable {A : Type u} [CommRing A] {n : ℕ}

/-- A polynomial all of whose monomials have exponent at least `M` in `Xₖ` is divisible by
`Xₖ^M`. -/
public theorem X_pow_dvd_of_forall_coeff {k : Fin (n + 1)} {M : ℕ}
    {q : MvPolynomial (Fin (n + 1)) A} (h : ∀ m, coeff m q ≠ 0 → M ≤ m k) :
    X k ^ M ∣ q := by
  classical
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero]
  ext m
  rw [coeff_zero]
  by_cases hle : Finsupp.single k M ≤ m
  · exact coeff_modMonomial_of_le _ hle
  · rw [coeff_modMonomial_of_not_le _ hle]
    by_contra hne
    exact hle (Finsupp.single_le_iff.mpr (h m hne))

/-- Multiplication by `Xₖ^M` shifts the coefficients by `M` in the `k`-th exponent. -/
public theorem coeff_single_add_X_pow_mul (k : Fin (n + 1)) (M : ℕ) (m : Fin (n + 1) →₀ ℕ)
    (q : MvPolynomial (Fin (n + 1)) A) :
    coeff (Finsupp.single k M + m) (X k ^ M * q) = coeff m q := by
  rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul]

/-- If `X_l^{M'} q = Xₖ^M q'` for two distinct variables, then `Xₖ^M` divides `q`. -/
public theorem X_pow_dvd_of_mul_eq {k l : Fin (n + 1)} (hkl : k ≠ l) {M M' : ℕ}
    {q q' : MvPolynomial (Fin (n + 1)) A} (h : X l ^ M' * q = X k ^ M * q') : X k ^ M ∣ q := by
  classical
  refine X_pow_dvd_of_forall_coeff fun m hm => ?_
  have hc := congrArg (coeff (Finsupp.single l M' + m)) h
  rw [coeff_single_add_X_pow_mul, X_pow_eq_monomial, coeff_monomial_mul'] at hc
  split_ifs at hc with hle
  · have h' := Finsupp.single_le_iff.mp hle
    simpa [Finsupp.single_apply, hkl, Ne.symm hkl] using h'
  · exact absurd hc hm

/-- Membership in a natural-number degree of the integer-extended polynomial grading, in terms
of the weights of the monomials. -/
private theorem mem_integerGrading_natCast_iff {c : ℕ} {p : MvPolynomial (Fin (n + 1)) A} :
    p ∈ integerGrading (polyGrading A n) (c : ℤ) ↔
      ∀ m, coeff m p ≠ 0 → Finsupp.weight (1 : Fin (n + 1) → ℕ) m = c := by
  rw [integerGrading_natCast, AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_homogeneousSubmodule]
  exact Iff.rfl

/-- The monomials of `p` have degree `c` when `Xₖ^M p` is homogeneous of degree `M + c`. -/
public theorem weight_eq_of_X_pow_mul_mem {k : Fin (n + 1)} {M : ℕ} {c : ℤ}
    {p : MvPolynomial (Fin (n + 1)) A}
    (hp : X k ^ M * p ∈ integerGrading (polyGrading A n) ((M : ℤ) + c)) {m : Fin (n + 1) →₀ ℕ}
    (hm : coeff m p ≠ 0) : (Finsupp.weight (1 : Fin (n + 1) → ℕ) m : ℤ) = c := by
  classical
  have hc0 : coeff (Finsupp.single k M + m) (X k ^ M * p) ≠ 0 := by
    rwa [coeff_single_add_X_pow_mul]
  have hnn : 0 ≤ (M : ℤ) + c := by
    by_contra hneg
    rw [integerGrading_neg _ _ (not_le.mp hneg), Submodule.mem_bot] at hp
    exact hc0 (by rw [hp, coeff_zero])
  rw [show (M : ℤ) + c = (((M : ℤ) + c).toNat : ℕ) by omega, mem_integerGrading_natCast_iff] at hp
  have hw := hp _ hc0
  rw [map_add, Finsupp.weight_single, Pi.one_apply, smul_eq_mul, mul_one] at hw
  omega

/-- **Compatible chart data on `ℙⁿ_A` come from one homogeneous polynomial.** If homogeneous
polynomials `hₖ` of degree `Mₖ + c` satisfy `X_l^{M_l} hₖ = Xₖ^{Mₖ} h_l` for all `k, l`, then
`hₖ = Xₖ^{Mₖ} p` for a single `p ∈ S_c`, provided `0 ≤ c` or `0 < n`. -/
public theorem exists_eq_X_pow_mul (c : ℤ) (h : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A)
    (M : Fin (n + 1) → ℕ) (hh : ∀ k, h k ∈ integerGrading (polyGrading A n) ((M k : ℤ) + c))
    (hrel : ∀ k l, X l ^ M l * h k = X k ^ M k * h l) (hnc : 0 ≤ c ∨ 0 < n) :
    ∃ p ∈ integerGrading (polyGrading A n) c, ∀ k, h k = X k ^ M k * p := by
  have hdvd : ∀ k, X k ^ M k ∣ h k := by
    intro k
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hc : 0 ≤ c := hnc.resolve_right (lt_irrefl 0)
      refine X_pow_dvd_of_forall_coeff fun m hm => ?_
      have hk := hh k
      rw [show (M k : ℤ) + c = ((M k + c.toNat : ℕ) : ℤ) by omega,
        mem_integerGrading_natCast_iff] at hk
      have hw := hk _ hm
      rw [Finsupp.weight_eq_sum, Fin.sum_univ_one] at hw
      obtain rfl : k = 0 := Fin.fin_one_eq_zero k
      simp only [Pi.one_apply, smul_eq_mul, mul_one] at hw
      omega
    · obtain ⟨l, hl⟩ : ∃ l : Fin (n + 1), k ≠ l := by
        by_cases hk : k = 0
        · exact ⟨⟨1, by omega⟩, by simp [hk, Fin.ext_iff]⟩
        · exact ⟨0, hk⟩
      exact X_pow_dvd_of_mul_eq hl (hrel k l)
  choose q hq using hdvd
  have hqe : ∀ k, q k = q 0 := by
    intro k
    have h1 := hrel k 0
    rw [hq k, hq 0, ← mul_assoc, ← mul_assoc, mul_comm (X 0 ^ M 0)] at h1
    exact ((isRegular_X_pow (M k)).mul (isRegular_X_pow (M 0))).left h1
  refine ⟨q 0, ?_, fun k => by rw [hq k, hqe k]⟩
  have hwt : ∀ m, coeff m (q 0) ≠ 0 →
      (Finsupp.weight (1 : Fin (n + 1) → ℕ) m : ℤ) = c := fun m hm =>
    weight_eq_of_X_pow_mul_mem (k := 0) (by rw [← hq 0]; exact hh 0) hm
  by_cases hp : q 0 = 0
  · rw [hp]
    exact zero_mem _
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hp
  have hc : 0 ≤ c := (hwt m hm) ▸ Int.natCast_nonneg _
  rw [show c = (c.toNat : ℤ) by omega, mem_integerGrading_natCast_iff]
  intro m' hm'
  have := hwt m' hm'
  omega

end Polynomial

/-! ### Morphisms between twists on `ℙⁿ_A` -/

section Main

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The ideal of a point of `ℙⁿ_A` is prime. -/
local instance (x : ProjectiveSpectrum.top (polyGrading A n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- Every point of `ℙⁿ_A` lies on a standard open `D₊(Xₖ)`. -/
public theorem exists_mem_basicOpen_X (x : ProjectiveSpectrum.top (polyGrading A n)) :
    ∃ k : Fin (n + 1), x ∈ ProjectiveSpectrum.basicOpen (polyGrading A n) (X k) := by
  by_contra! h
  refine x.not_irrelevant_le ((irrelevant_le_span_X A n).trans (Ideal.span_le.mpr ?_))
  rintro _ ⟨k, rfl⟩
  have hk := h k
  rwa [ProjectiveSpectrum.mem_basicOpen, not_not] at hk


/-- **Multiplication by a homogeneous polynomial determines the polynomial.** -/
public theorem twistMul_injective {c d e : ℤ} (he : c + d = e)
    {p q : MvPolynomial (Fin (n + 1)) A}
    (hp : p ∈ integerGrading (polyGrading A n) c) (hq : q ∈ integerGrading (polyGrading A n) c)
    (h : twistMul (polyGrading A n) p c d e hp he = twistMul (polyGrading A n) q c d e hq he) :
    p = q := by
  obtain ⟨r, hr⟩ := exists_pow_mul_eq_zero (polyGrading A n) (X_mem_one A n 0) one_pos
    (sub_mem hp hq) (mk_sub_eq_zero_of_twistMul_eq (polyGrading A n) (X_mem_one A n 0) hp hq he h)
  rw [← sub_eq_zero]
  exact (isRegular_X_pow r).left.mul_left_eq_zero_iff.mp hr

/-- **Every morphism `𝒪(d) ⟶ 𝒪(e)` on `ℙⁿ_A` is multiplication by a homogeneous polynomial of
degree `e - d`**, provided `0 ≤ e - d` or `0 < n`. -/
public theorem exists_twistMul_eq {c d e : ℤ} (he : c + d = e) (hnc : 0 ≤ c ∨ 0 < n)
    (φ : twistingSheaf (polyGrading A n) d ⟶ twistingSheaf (polyGrading A n) e) :
    ∃ (p : MvPolynomial (Fin (n + 1)) A) (hp : p ∈ integerGrading (polyGrading A n) c),
      twistMul (polyGrading A n) p c d e hp he = φ := by
  choose N g hg hv using fun k => exists_chart (polyGrading A n) (X_mem_one A n k) φ
  have hh : ∀ k, X k ^ (-d).toNat * g k ∈
      integerGrading (polyGrading A n) (((d.toNat + N k : ℕ) : ℤ) + c) := fun k =>
    mem_integerGrading_congr _ (by push_cast; omega)
      (mul_mem_integerGrading' _ (pow_mem_integerGrading _ (X_mem_one A n k) _) (hg k))
  have hrel : ∀ k l, X l ^ (d.toNat + N l) * (X k ^ (-d).toNat * g k) =
      X k ^ (d.toNat + N k) * (X l ^ (-d).toNat * g l) := by
    intro k l
    have hD := sub_mem
      (mul_mem_integerGrading' _ (pow_mem_integerGrading _ (X_mem_one A n l) (d.toNat + N l))
        (hh k))
      (mem_integerGrading_congr _ (by push_cast; ring)
        (mul_mem_integerGrading' _ (pow_mem_integerGrading _ (X_mem_one A n k)
          (d.toNat + N k)) (hh l)))
    obtain ⟨r, hr⟩ := exists_pow_mul_eq_zero (polyGrading A n)
      (SetLike.mul_mem_graded (X_mem_one A n k) (X_mem_one A n l)) two_pos hD
      (mk_chart_sub_eq_zero (polyGrading A n) (X_mem_one A n k) (X_mem_one A n l) φ
        (hv k) (hv l))
    rw [← sub_eq_zero]
    exact ((isRegular_X.mul isRegular_X).pow r).left.mul_left_eq_zero_iff.mp hr
  obtain ⟨p, hp, hph⟩ := exists_eq_X_pow_mul c _ _ hh hrel hnc
  exact ⟨p, hp, twistMul_eq_of_charts (polyGrading A n) (fun k => X_mem_one A n k)
    (exists_mem_basicOpen_X A n) φ hv hp he hph⟩

/-- **`Hom(𝒪(d), 𝒪(e)) = S_{e-d}` on `ℙⁿ_A`**, provided `0 ≤ e - d` or `0 < n`:
multiplication is a bijection from the homogeneous polynomials of degree `e - d` onto the
morphisms of twists. -/
public theorem bijective_twistMul {c d e : ℤ} (he : c + d = e) (hnc : 0 ≤ c ∨ 0 < n) :
    Function.Bijective fun p : integerGrading (polyGrading A n) c =>
      twistMul (polyGrading A n) p.1 c d e p.2 he := by
  refine ⟨fun p q h => Subtype.ext (twistMul_injective A n he p.2 q.2 h), fun φ => ?_⟩
  obtain ⟨p, hp, h⟩ := exists_twistMul_eq A n he hnc φ
  exact ⟨⟨p, hp⟩, h⟩

end Main

/-! ### The endomorphism ring of `𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)` -/

section Matrices

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The degree `j - i` of the `(i, j)` entry is nonnegative or there is more than one
variable. -/
public theorem entry_degree_nonneg_or (i j : Fin (n + 1)) : 0 ≤ (j : ℤ) - (i : ℤ) ∨ 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j, sub_self]
  · exact Or.inr hn

/-- **The comparison map `R ⟶ End(P)` is bijective**: an endomorphism of
`P = 𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)` is the matrix of its components, and the `(i, j)` component
`𝒪(-j) ⟶ 𝒪(-i)` is multiplication by exactly one element of `S_{j-i}`. -/
public theorem bijective_matrixToEnd : Function.Bijective (matrixToEnd A n) := by
  have h (i j : Fin (n + 1)) := bijective_twistMul A n
    (show ((j : ℤ) - (i : ℤ)) + -(j : ℤ) = -(i : ℤ) by ring) (entry_degree_nonneg_or n i j)
  refine ⟨fun M N hMN ↦ Subtype.ext (Matrix.ext fun i j ↦ ?_), fun φ ↦ ?_⟩
  · have hcomp : matrixEntryHom A n M i j = matrixEntryHom A n N i j := by
      rw [← components_matrixToEnd A n M j i, ← components_matrixToEnd A n N j i, hMN]
    rw [matrixEntryHom, matrixEntryHom, twistMulHom_apply, twistMulHom_apply] at hcomp
    exact congrArg Subtype.val ((h i j).1 hcomp)
  · choose q hq using fun i j : Fin (n + 1) =>
      (h i j).2 (biproduct.ι (twistFamily A n) j ≫ φ ≫ biproduct.π (twistFamily A n) i)
    refine ⟨⟨fun i j => (q i j).1, fun i j =>
      mem_homogeneousPiece_of_mem_integerGrading A n (q i j).2⟩, ?_⟩
    refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun i => ?_
    rw [Category.assoc, Category.assoc, components_matrixToEnd, matrixEntryHom,
      twistMulHom_apply]
    exact hq i j

/-- **[Stacks, Tag 0CS9]: `R = Hom_{𝒪_X}(P, P)`.** On `X = ℙⁿ_A = Proj A[X₀, …, Xₙ]`, the ring
of upper triangular `(n + 1) × (n + 1)` matrices whose `(i, j)` entry is homogeneous of degree
`j - i` — `S₀` on the diagonal, `S₁` above it, and so on — is the endomorphism ring of
`P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`, the `(i, j)` entry acting as the component
`𝒪_X(-j) ⟶ 𝒪_X(-i)` by multiplication. -/
@[stacks 0CS9]
public def matrixRingEquivEnd : endomorphismMatrices A n ≃+* End (projTwistSum A n) :=
  RingEquiv.ofBijective (matrixToEnd A n) (bijective_matrixToEnd A n)

/-- The `(i, j)` component of the endomorphism attached to a matrix is multiplication by its
`(i, j)` entry. -/
public theorem components_matrixRingEquivEnd (M : endomorphismMatrices A n)
    (j i : Fin (n + 1)) :
    biproduct.ι (twistFamily A n) j ≫ matrixRingEquivEnd A n M ≫
        biproduct.π (twistFamily A n) i = matrixEntryHom A n M i j :=
  components_matrixToEnd A n M j i

end Matrices

end Stacks.AlgebraicGeometry.ProjectiveGenerator

end
