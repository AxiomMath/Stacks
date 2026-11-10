module

import Mathlib.Tactic.Push
import Mathlib.Tactic.LinearCombination

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree-zero localization of a graded module at a point of `D₊(f)`

For `f` homogeneous of positive degree outside a homogeneous prime `𝔭`, the degree-zero
localization `M_(𝔭)` of a graded module `M` is the localization of `M_(f)` at the prime `𝔭'`
of fractions with numerator in `𝔭` (Stacks Tag 00JR, the module half).
-/

@[expose] public section

open DirectSum

/-!
# The degree-zero localization of a graded module at a point of `D₊(f)`

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, let `M = ⨁_{n ∈ ℤ} ℳ n` be a graded `A`-module, let `𝔭`
be a homogeneous prime of `A` and let `f ∈ 𝒜 m` with `m > 0` and `f ∉ 𝔭`. Write `A⁰_f` for the
degree-zero part of `A[1/f]` and `𝔭' ⊂ A⁰_f` for the prime of fractions `a/fⁿ` with `a ∈ 𝔭`. This
file proves that the `A⁰_f`-module `M_(𝔭)` of degree-zero fractions `y/g` with `g ∉ 𝔭` homogeneous
is the localization of the `A⁰_f`-module `M_(f)` of degree-zero fractions `y/fⁿ` at `𝔭'`.

## Main results

* `Stacks.GradedModule.DegreeZeroAtPrime.solution`: the statement of Stacks Tag 00JR, the module
  half.

## Implementation notes

The three obligations of `IsLocalizedModule` are checked on fractions, which is possible because
each of the two spans of degree-zero fractions is already equal to the set of degree-zero fractions
it spans: that set is closed under addition, `y/g + y'/g' = (g'y + gy')/(gg')` adding the degrees on
both sides, and under multiplication by a degree-zero fraction, for the same reason. This is
`mem_deg0_of_mem_span`, stated once for an arbitrary ring `R` acting on `M_x` through a ring map
`R → A_x` whose values are fractions with homogeneous numerator and denominator of equal degree;
both spans of the statement are instances of it.

Invertibility of a scalar `a/fⁿ ∉ 𝔭'` on `M_(𝔭)` is not proved by exhibiting the inverse scalar
`fⁿ/a`, which lies in `A_(𝔭)` rather than in `A⁰_f`: the image of `a/fⁿ` in `A_𝔭` is already a unit
there, since both `a` and `fⁿ` are outside `𝔭`, so it acts injectively on all of `M_𝔭`, and
surjectivity onto `M_(𝔭)` is the computation `(a/fⁿ) · (fⁿ y)/(a g) = y/g`.

Surjectivity of `M_(f) → M_(𝔭)` after inverting `𝔭'` is the source's map `ψ`: the scalar
`g^m/f^{deg g} ∉ 𝔭'` carries `y/g` to `(g^{m-1} y)/f^{deg g}`, which is a degree-zero fraction
with denominator a power of `f` precisely because `m > 0`. Injectivity up to `𝔭'`-torsion is where
homogeneity of `𝔭` enters: a witness `c ∉ 𝔭` for the equality of two fractions with homogeneous
numerators and denominators can be replaced by any of its homogeneous components, because the
components of `c` act on a homogeneous element in distinct degrees (`smul_congr_of_proj`), and one
component lies outside `𝔭`; a homogeneous component `c_j ∉ 𝔭` then gives the scalar
`c_j^m/f^j ∉ 𝔭'`.

## References

* [StackProject 00JR](https://stacks.math.columbia.edu/tag/00JR)
-/

namespace Stacks.GradedModule.DegreeZeroAtPrime

open HomogeneousLocalization

section LiftOfLE

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {S T : Submonoid R} (h : S ≤ T)

/-- `LocalizedModule.liftOfLE` sends the fraction `y/s` to the fraction `y/s`. -/
private lemma liftOfLE_mk (y : M) (s : S) :
    LocalizedModule.liftOfLE S T h (LocalizedModule.mk y s) =
      LocalizedModule.mk y ⟨(s : R), h s.2⟩ := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']

/-- `LocalizedModule.liftOfLE` is semilinear for multiplication by a fraction with denominator in
the smaller submonoid. -/
private lemma liftOfLE_smul_mk (a : R) (s : S) (z : LocalizedModule S M) :
    LocalizedModule.liftOfLE S T h (Localization.mk a s • z) =
      Localization.mk a ⟨(s : R), h s.2⟩ • LocalizedModule.liftOfLE S T h z := by
  induction z using LocalizedModule.induction_on with
  | _ y
    t =>
    rw [LocalizedModule.mk_smul_mk, liftOfLE_mk, liftOfLE_mk, LocalizedModule.mk_smul_mk]
    rfl

end LiftOfLE

/-- Two fractions with numerator and denominator exchanged, both in the submonoid, are inverse to
each other. -/
@[ega "0 1.2.2" "more general"]
private lemma mk_mul_mk_eq_one {R : Type*} [CommRing R] {x : Submonoid R} (a b : R) (ha : a ∈ x)
    (hb : b ∈ x) : Localization.mk b ⟨a, ha⟩ * Localization.mk a ⟨b, hb⟩ = 1 := by
  rw [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp [mul_comm]⟩

section Graded

variable {σ τ A M : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] [AddCommGroup M]
  [Module A M] [SetLike τ M] [AddSubmonoidClass τ M] (𝒜 : ℕ → σ) [GradedRing 𝒜] (ℳ : ℤ → τ)
  [DirectSum.Decomposition ℳ]
  (hℳ : ∀ (i : ℕ) (j : ℤ) (a : A) (y : M), a ∈ 𝒜 i → y ∈ ℳ j → a • y ∈ ℳ (i + j))

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
include hℳ in
/-- For `a ∈ 𝒜 i` homogeneous, the degree-`n` component of `a • y` is `a` times the degree-`n - i`
component of `y`. -/
private lemma decompose_smul_of_mem {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) (y : M) (n : ℤ) :
    (DirectSum.decompose ℳ (a • y) n : M) = a • (DirectSum.decompose ℳ y (n - i) : M) := by
  classical
  induction y using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous y =>
    rename_i j
    have hay : a • (y : M) ∈ ℳ ((i : ℤ) + j) := hℳ i j a y ha y.2
    by_cases hn : n = (i : ℤ) + j
    · subst hn
      rw [DirectSum.decompose_of_mem_same ℳ hay, show (i : ℤ) + j - i = j by ring,
        DirectSum.decompose_of_mem_same ℳ y.2]
    · rw [DirectSum.decompose_of_mem_ne ℳ hay (Ne.symm hn),
        DirectSum.decompose_of_mem_ne ℳ y.2 (by omega), smul_zero]
  | add y y' hy hy' =>
    rw [smul_add, DirectSum.decompose_add, DirectSum.add_apply, DirectSum.decompose_add,
      DirectSum.add_apply, AddMemClass.coe_add, AddMemClass.coe_add, hy, hy', smul_add]

include hℳ in
/-- For `y ∈ ℳ e` homogeneous and `c : A` arbitrary, the degree-`i + e` component of `c • y` is the
degree-`i` component of `c` acting on `y`. -/
private lemma proj_smul {e : ℤ} {y : M} (hy : y ∈ ℳ e) (c : A) (i : ℕ) :
    (DirectSum.decompose ℳ (c • y) ((i : ℤ) + e) : M) = (DirectSum.decompose 𝒜 c i : A) • y := by
  classical
  induction c using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous c =>
    rename_i j
    rw [decompose_smul_of_mem 𝒜 ℳ hℳ c.2 y ((i : ℤ) + e)]
    by_cases hij : j = i
    · subst hij
      rw [DirectSum.decompose_of_mem_same 𝒜 c.2, show (j : ℤ) + e - j = e by ring,
        DirectSum.decompose_of_mem_same ℳ hy]
    · rw [DirectSum.decompose_of_mem_ne 𝒜 c.2 hij, DirectSum.decompose_of_mem_ne ℳ hy (by omega)]
      simp
  | add c c' hc hc' =>
    rw [add_smul, DirectSum.decompose_add, DirectSum.add_apply, DirectSum.decompose_add,
      DirectSum.add_apply, AddMemClass.coe_add, AddMemClass.coe_add, hc, hc', add_smul]

include hℳ in
/-- If `c` acts in the same way on two homogeneous elements of the same degree, then so does every
homogeneous component of `c`. -/
private lemma smul_congr_of_proj {d : ℤ} {u v : M} (hu : u ∈ ℳ d) (hv : v ∈ ℳ d) {c : A}
    (h : c • u = c • v) (i : ℕ) :
    (DirectSum.decompose 𝒜 c i : A) • u = (DirectSum.decompose 𝒜 c i : A) • v := by
  rw [← proj_smul 𝒜 ℳ hℳ hu c i, ← proj_smul 𝒜 ℳ hℳ hv c i, h]

omit [DirectSum.Decomposition ℳ] in
include hℳ in
/-- The set of degree-zero fractions `y/g` in `M_x`, `g ∈ x` homogeneous and `y` homogeneous of the
same degree, is already a submodule over any ring acting through fractions with homogeneous
numerator and denominator of the same degree: it spans itself. -/
private lemma mem_deg0_of_mem_span {R : Type*} [CommRing R] {x : Submonoid A}
    (ψ : R →+* Localization x)
    (hψ :
      ∀ r : R, ∃ (i : ℕ) (a : A) (s : x), a ∈ 𝒜 i ∧ (s : A) ∈ 𝒜 i ∧ ψ r = Localization.mk a s) :
    letI : Module R (LocalizedModule x M) := Module.compHom _ ψ
    ∀
      z ∈
        Submodule.span R
          {z : LocalizedModule x M |
            ∃ (i : ℕ) (y : M) (g : x), y ∈ ℳ (i : ℤ) ∧ (g : A) ∈ 𝒜 i ∧ z = .mk y g},
      ∃ (i : ℕ) (y : M) (g : x), y ∈ ℳ (i : ℤ) ∧ (g : A) ∈ 𝒜 i ∧ z = .mk y g := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero => exact ⟨0, 0, 1, zero_mem _, SetLike.one_mem_graded 𝒜, (LocalizedModule.zero_mk 1).symm⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨i, y, g, hy, hg, rfl⟩ := hz
    obtain ⟨i', y', g', hy', hg', rfl⟩ := hz'
    refine ⟨i + i', (g' : A) • y + (g : A) • y', g * g', ?_, SetLike.mul_mem_graded hg hg', ?_⟩
    · have h1 : (g' : A) • y ∈ ℳ ((i : ℤ) + i') := by
        have := hℳ i' i (g' : A) y hg' hy
        rwa [show ((i' : ℤ) + i) = (i : ℤ) + i' by ring] at this
      have h2 : (g : A) • y' ∈ ℳ ((i : ℤ) + i') := hℳ i i' (g : A) y' hg hy'
      rw [show ((i + i' : ℕ) : ℤ) = (i : ℤ) + i' by
          push_cast; ring]
      exact add_mem h1 h2
    · rw [LocalizedModule.mk_add_mk]
      rfl
  | smul r z _ hz =>
    obtain ⟨i, y, g, hy, hg, rfl⟩ := hz
    obtain ⟨j, a, s, ha, hs, hr⟩ := hψ r
    refine ⟨j + i, a • y, s * g, ?_, SetLike.mul_mem_graded hs hg, ?_⟩
    · have := hℳ j i a y ha hy
      rwa [show ((j : ℤ) + i) = ((j + i : ℕ) : ℤ) by
          push_cast; ring] at this
    · change ψ r • LocalizedModule.mk y g = _
      rw [hr, LocalizedModule.mk_smul_mk]

end Graded

public theorem solution {σ τ A M : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [AddCommGroup M] [Module A M] [SetLike τ M] [AddSubmonoidClass τ M] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    (hℳ : ∀ (i : ℕ) (j : ℤ) (a : A) (y : M), a ∈ 𝒜 i → y ∈ ℳ j → a • y ∈ ℳ (i + j)) (𝔭 : Ideal A)
    [𝔭.IsPrime] (h𝔭 : 𝔭.IsHomogeneous 𝒜) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m) (hf𝔭 : f ∉ 𝔭)
    (𝔭' : Ideal (Away 𝒜 f)) [𝔭'.IsPrime]
    (h𝔭' : ∀ z : NumDenSameDeg 𝒜 (Submonoid.powers f), mk z ∈ 𝔭' ↔ (z.num : A) ∈ 𝔭) :
    letI : Module (Away 𝒜 f) (LocalizedModule (Submonoid.powers f) M) :=
      Module.compHom _ (algebraMap (Away 𝒜 f) (Localization (Submonoid.powers f)))
    letI : Module (Away 𝒜 f) (LocalizedModule 𝔭.primeCompl M) :=
      Module.compHom _
        ((algebraMap (AtPrime 𝒜 𝔭) (Localization 𝔭.primeCompl)).comp
          (mapId 𝒜 (Submonoid.powers_le.mpr hf𝔭)))
    ∃ φ :
      ↥(Submodule.span (Away 𝒜 f)
            {z : LocalizedModule (Submonoid.powers f) M |
              ∃ (i : ℕ) (y : M) (g : Submonoid.powers f),
                y ∈ ℳ (i : ℤ) ∧ (g : A) ∈ 𝒜 i ∧ z = .mk y g}) →ₗ[Away 𝒜 f]
        ↥(Submodule.span (Away 𝒜 f)
            {z : LocalizedModule 𝔭.primeCompl M |
              ∃ (i : ℕ) (y : M) (g : 𝔭.primeCompl), y ∈ ℳ (i : ℤ) ∧ (g : A) ∈ 𝒜 i ∧ z = .mk y g}),
      (∀ z,
          (φ z : LocalizedModule 𝔭.primeCompl M) =
            LocalizedModule.liftOfLE _ _ (Submonoid.powers_le.mpr hf𝔭) (z : _)) ∧
        IsLocalizedModule 𝔭'.primeCompl φ := by
  classical
  have hle : Submonoid.powers f ≤ 𝔭.primeCompl := Submonoid.powers_le.mpr hf𝔭
  let inst₁ : Module (Away 𝒜 f) (LocalizedModule (Submonoid.powers f) M) :=
    Module.compHom _ (algebraMap (Away 𝒜 f) (Localization (Submonoid.powers f)))
  let inst₂ : Module (Away 𝒜 f) (LocalizedModule 𝔭.primeCompl M) :=
    Module.compHom _ ((algebraMap (AtPrime 𝒜 𝔭) (Localization 𝔭.primeCompl)).comp (mapId 𝒜 hle))
  -- the two scalar actions, on fractions
  have hval₁ :
    ∀ z : NumDenSameDeg 𝒜 (Submonoid.powers f),
      algebraMap (Away 𝒜 f) (Localization (Submonoid.powers f)) (mk z) =
        Localization.mk (z.num : A) ⟨(z.den : A), z.den_mem⟩ := by
    intro z; simp
  have hval₂ :
    ∀ z : NumDenSameDeg 𝒜 (Submonoid.powers f),
      ((algebraMap (AtPrime 𝒜 𝔭) (Localization 𝔭.primeCompl)).comp (mapId 𝒜 hle)) (mk z) =
        Localization.mk (z.num : A) ⟨(z.den : A), hle z.den_mem⟩ := by
    intro z; rfl
  have hψ₁ :
    ∀ r : Away 𝒜 f,
      ∃ (i : ℕ) (a : A) (s : Submonoid.powers f),
        a ∈ 𝒜 i ∧
          (s : A) ∈ 𝒜 i ∧
          algebraMap (Away 𝒜 f) (Localization (Submonoid.powers f)) r = Localization.mk a s := by
    intro r
    obtain ⟨z, rfl⟩ := mk_surjective r
    exact ⟨z.deg, z.num, ⟨(z.den : A), z.den_mem⟩, z.num.2, z.den.2, hval₁ z⟩
  have hψ₂ :
    ∀ r : Away 𝒜 f,
      ∃ (i : ℕ) (a : A) (s : 𝔭.primeCompl),
        a ∈ 𝒜 i ∧
          (s : A) ∈ 𝒜 i ∧
          ((algebraMap (AtPrime 𝒜 𝔭) (Localization 𝔭.primeCompl)).comp (mapId 𝒜 hle)) r =
            Localization.mk a s := by
    intro r
    obtain ⟨z, rfl⟩ := mk_surjective r
    exact ⟨z.deg, z.num, ⟨(z.den : A), hle z.den_mem⟩, z.num.2, z.den.2, hval₂ z⟩
  have hmem₁ := mem_deg0_of_mem_span 𝒜 ℳ hℳ _ hψ₁
  have hmem₂ := mem_deg0_of_mem_span 𝒜 ℳ hℳ _ hψ₂
  -- the comparison map
  have hmaps :
    ∀
      z ∈
        Submodule.span (Away 𝒜 f)
          {z : LocalizedModule (Submonoid.powers f) M |
            ∃ (i : ℕ) (y : M) (g : Submonoid.powers f),
              y ∈ ℳ (i : ℤ) ∧ (g : A) ∈ 𝒜 i ∧ z = .mk y g},
      LocalizedModule.liftOfLE _ _ hle z ∈
        Submodule.span (Away 𝒜 f)
          {z : LocalizedModule 𝔭.primeCompl M |
            ∃ (i : ℕ) (y : M) (g : 𝔭.primeCompl),
              y ∈ ℳ (i : ℤ) ∧ (g : A) ∈ 𝒜 i ∧ z = .mk y g} := by
    intro z hz
    obtain ⟨i, y, g, hy, hg, rfl⟩ := hmem₁ z hz
    exact Submodule.subset_span ⟨i, y, ⟨(g : A), hle g.2⟩, hy, hg, liftOfLE_mk hle y g⟩
  have hsmul₁ :
    ∀ (r : Away 𝒜 f) (u : LocalizedModule (Submonoid.powers f) M),
      r • u = algebraMap (Away 𝒜 f) (Localization (Submonoid.powers f)) r • u :=
    fun _ _ => rfl
  have hsmul₂ :
    ∀ (r : Away 𝒜 f) (u : LocalizedModule 𝔭.primeCompl M),
      r • u = ((algebraMap (AtPrime 𝒜 𝔭) (Localization 𝔭.primeCompl)).comp (mapId 𝒜 hle)) r • u :=
    fun _ _ => rfl
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- the scalar `c^(m+1)/f^j ∉ 𝔭'` attached to a homogeneous `c ∉ 𝔭` of degree `j`
  have hscalar : ∀ (j : ℕ) (c : A), c ∈ 𝒜 j → c ∉ 𝔭 →
      ∃ (hc : c ^ (m + 1) ∈ 𝒜 (j * (m + 1))) (hfj : f ^ j ∈ 𝒜 (j * (m + 1))),
        (mk ⟨j * (m + 1), ⟨c ^ (m + 1), hc⟩, ⟨f ^ j, hfj⟩, j, rfl⟩ : Away 𝒜 f) ∉ 𝔭' := by
    intro j c hcj hc𝔭
    refine ⟨by simpa [mul_comm] using SetLike.pow_mem_graded (m + 1) hcj,
      by simpa using SetLike.pow_mem_graded j hf, ?_⟩
    rw [h𝔭' _]
    exact fun hmem => hc𝔭 (Ideal.IsPrime.mem_of_pow_mem ‹𝔭.IsPrime› _ hmem)
  refine
    ⟨{  toFun := fun z => ⟨LocalizedModule.liftOfLE _ _ hle (z : _), hmaps _ z.2⟩
        map_add' := fun z z' => Subtype.ext (map_add _ _ _)
        map_smul' := ?_ }, fun z => rfl, ?_, ?_, ?_⟩
  · -- the comparison map is `A⁰_f`-linear
    intro r z
    refine Subtype.ext ?_
    obtain ⟨w, rfl⟩ := mk_surjective r
    change
      LocalizedModule.liftOfLE _ _ hle
          ((mk w : Away 𝒜 f) • (z : LocalizedModule (Submonoid.powers f) M)) =
        (mk w : Away 𝒜 f) •
          LocalizedModule.liftOfLE _ _ hle (z : LocalizedModule (Submonoid.powers f) M)
    rw [hsmul₁, hsmul₂, hval₁, hval₂, liftOfLE_smul_mk]
  · -- every scalar outside `𝔭'` acts invertibly on `M_(𝔭)`
    intro s
    obtain ⟨w, hw⟩ := mk_surjective (s : Away 𝒜 f)
    have hnum : (w.num : A) ∉ 𝔭 := fun hmem => s.2 (hw ▸ (h𝔭' w).mpr hmem)
    have hunit :
      Localization.mk (w.den : A) (⟨(w.num : A), hnum⟩ : 𝔭.primeCompl) *
          Localization.mk (w.num : A) (⟨(w.den : A), hle w.den_mem⟩ : 𝔭.primeCompl) =
        1 :=
      mk_mul_mk_eq_one _ _ _ _
    refine (Module.End.isUnit_iff _).mpr ⟨fun z z' h => ?_, fun y => ?_⟩
    · -- injectivity: the scalar is already a unit in `M_𝔭`
      have h2 :
        (s : Away 𝒜 f) • (z : LocalizedModule 𝔭.primeCompl M) =
          (s : Away 𝒜 f) • (z' : LocalizedModule 𝔭.primeCompl M) :=
        congrArg Subtype.val h
      rw [hsmul₂, hsmul₂, ← hw, hval₂] at h2
      refine Subtype.ext ?_
      have h3 :=
        congrArg (fun t => Localization.mk (w.den : A) (⟨(w.num : A), hnum⟩ : 𝔭.primeCompl) • t) h2
      simpa only [← mul_smul, hunit, one_smul] using h3
    · -- surjectivity: `(a/fⁿ) · (fⁿ y)/(a g) = y/g`
      obtain ⟨i, y₀, g, hy₀, hg, hy⟩ := hmem₂ (y : LocalizedModule 𝔭.primeCompl M) y.2
      have hnumden : (w.den : A) • y₀ ∈ ℳ ((w.deg + i : ℕ) : ℤ) := by
        rw [show ((w.deg + i : ℕ) : ℤ) = (w.deg : ℤ) + i by
            push_cast; ring]
        exact hℳ w.deg i _ y₀ w.den.2 hy₀
      refine
        ⟨⟨LocalizedModule.mk ((w.den : A) • y₀)
              (⟨(w.num : A) * (g : A), mul_mem hnum g.2⟩ : 𝔭.primeCompl),
            Submodule.subset_span
              ⟨w.deg + i, _, _, hnumden, SetLike.mul_mem_graded w.num.2 hg, rfl⟩⟩,
          Subtype.ext ?_⟩
      change
        (s : Away 𝒜 f) •
            LocalizedModule.mk ((w.den : A) • y₀)
              (⟨(w.num : A) * (g : A), mul_mem hnum g.2⟩ : 𝔭.primeCompl) =
          (y : LocalizedModule 𝔭.primeCompl M)
      rw [hsmul₂, ← hw, hval₂, LocalizedModule.mk_smul_mk, hy]
      refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, smul_smul]
      congr 1
      ring
  · -- surjectivity of `M_(f) → M_(𝔭)` after inverting `𝔭'`: the source's map `ψ`
    intro y
    obtain ⟨i, y₀, g, hy₀, hg, hy⟩ := hmem₂ (y : LocalizedModule 𝔭.primeCompl M) y.2
    obtain ⟨hgm, hfi, hg𝔭'⟩ := hscalar i g hg g.2
    have hgnum : (g : A) ^ m • y₀ ∈ ℳ ((i * (m + 1) : ℕ) : ℤ) := by
      have := hℳ (m * i) i _ y₀ (by simpa using SetLike.pow_mem_graded m hg) hy₀
      rwa [show ((m * i : ℕ) : ℤ) + i = ((i * (m + 1) : ℕ) : ℤ) by
          push_cast; ring] at this
    refine
      ⟨⟨⟨LocalizedModule.mk ((g : A) ^ m • y₀) (⟨f ^ i, i, rfl⟩ : Submonoid.powers f),
            Submodule.subset_span ⟨i * (m + 1), _, _, hgnum, hfi, rfl⟩⟩,
          ⟨mk ⟨i * (m + 1), ⟨(g : A) ^ (m + 1), hgm⟩, ⟨f ^ i, hfi⟩, i, rfl⟩, hg𝔭'⟩⟩,
        Subtype.ext ?_⟩
    change
      (mk ⟨i * (m + 1), ⟨(g : A) ^ (m + 1), hgm⟩, ⟨f ^ i, hfi⟩, i, rfl⟩ : Away 𝒜 f) •
          (y : LocalizedModule 𝔭.primeCompl M) =
        LocalizedModule.liftOfLE _ _ hle
          (LocalizedModule.mk ((g : A) ^ m • y₀) (⟨f ^ i, i, rfl⟩ : Submonoid.powers f))
    rw [hsmul₂, hval₂, hy, LocalizedModule.mk_smul_mk, liftOfLE_mk]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, smul_smul]
    congr 1
    ring
  · -- two fractions with the same image agree after inverting `𝔭'`
    intro z z' hzz'
    obtain ⟨i₁, y₁, g₁, hy₁, hg₁, hz₁⟩ := hmem₁ (z : LocalizedModule (Submonoid.powers f) M) z.2
    obtain ⟨i₂, y₂, g₂, hy₂, hg₂, hz₂⟩ := hmem₁ (z' : LocalizedModule (Submonoid.powers f) M) z'.2
    have h2 :
      LocalizedModule.mk y₁ (⟨(g₁ : A), hle g₁.2⟩ : 𝔭.primeCompl) =
        LocalizedModule.mk y₂ (⟨(g₂ : A), hle g₂.2⟩ : 𝔭.primeCompl) := by
      have h5 :
        LocalizedModule.liftOfLE _ _ hle (z : LocalizedModule (Submonoid.powers f) M) =
          LocalizedModule.liftOfLE _ _ hle (z' : LocalizedModule (Submonoid.powers f) M) :=
        congrArg Subtype.val hzz'
      rwa [hz₁, hz₂, liftOfLE_mk, liftOfLE_mk] at h5
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h2
    have hu₁ : (g₂ : A) • y₁ ∈ ℳ ((i₂ : ℤ) + i₁) := hℳ i₂ i₁ _ y₁ hg₂ hy₁
    have hu₂ : (g₁ : A) • y₂ ∈ ℳ ((i₂ : ℤ) + i₁) := by
      have := hℳ i₁ i₂ _ y₂ hg₁ hy₂
      rwa [show ((i₁ : ℤ) + i₂) = (i₂ : ℤ) + i₁ by ring] at this
    have hc : (u : A) • ((g₂ : A) • y₁) = (u : A) • ((g₁ : A) • y₂) := hu
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (DirectSum.decompose 𝒜 (u : A) j : A) ∉ 𝔭 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact u.2 ((Ideal.IsHomogeneous.mem_iff 𝒜 h𝔭).mpr hcon)
    have hkey := smul_congr_of_proj 𝒜 ℳ hℳ hu₁ hu₂ hc j
    set c := (DirectSum.decompose 𝒜 (u : A) j : A) with hcdef
    have hcj : c ∈ 𝒜 j := (DirectSum.decompose 𝒜 (u : A) j).2
    obtain ⟨hcm, hfj, hc𝔭'⟩ := hscalar j c hcj hj
    refine ⟨⟨mk ⟨j * (m + 1), ⟨c ^ (m + 1), hcm⟩, ⟨f ^ j, hfj⟩, j, rfl⟩, hc𝔭'⟩, Subtype.ext ?_⟩
    change
      (mk ⟨j * (m + 1), ⟨c ^ (m + 1), hcm⟩, ⟨f ^ j, hfj⟩, j, rfl⟩ : Away 𝒜 f) •
          (z : LocalizedModule (Submonoid.powers f) M) =
        (mk ⟨j * (m + 1), ⟨c ^ (m + 1), hcm⟩, ⟨f ^ j, hfj⟩, j, rfl⟩ : Away 𝒜 f) •
          (z' : LocalizedModule (Submonoid.powers f) M)
    rw [hsmul₁, hsmul₁, hval₁, hz₁, hz₂, LocalizedModule.mk_smul_mk, LocalizedModule.mk_smul_mk]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    have hkey' : (c * (g₂ : A)) • y₁ = (c * (g₁ : A)) • y₂ := by
      rw [← smul_smul, ← smul_smul]; exact hkey
    have h4 := congrArg (fun t => (f ^ j * c ^ m) • t) hkey'
    simp only [smul_smul] at h4
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, smul_smul]
    convert h4 using 2 <;> ring

end Stacks.GradedModule.DegreeZeroAtPrime

/-!
# The homogeneous localization of a graded module at a point of `D₊(f)`

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, let `M = ⨁_{n ∈ ℤ} ℳ n` be a graded `A`-module, let `𝔭`
be a homogeneous prime ideal of `A` and let `f ∈ A` be homogeneous of degree `m > 0` with `f ∉ 𝔭`,
that is, `𝔭 ∈ D₊(f)`. Write `A⁰_f = A_(f)` for the degree-zero part of `A[1/f]`, whose elements are
the fractions `a/fⁿ` with `a` homogeneous of degree `deg fⁿ`; it is
`HomogeneousLocalization.Away 𝒜 f`, and its spectrum is `D₊(f)`. Two degree-zero localizations of
`M` are in play. First `M_(f)`, the degree-zero part of `M[1/f]`, whose elements are the fractions
`y/fⁿ` with `y` homogeneous of degree `deg fⁿ`. Second `M_(𝔭)`, the degree-zero part of the
localization of `M` at the homogeneous elements outside `𝔭`, whose elements are the fractions `y/g`
with `y ∈ M` and `g ∈ A` homogeneous of the same degree and `g ∉ 𝔭`. Both are modules over `A⁰_f`,
the second through the ring map `A⁰_f → A_(𝔭)` obtained by inverting more, and the content of this
file is that `M_(𝔭) = (M_(f))_{𝔭'}`, where `𝔭' ⊂ A⁰_f` is the prime corresponding to `𝔭` under the
identification `D₊(f) ≅ Spec A⁰_f`, namely the set of fractions `a/fⁿ` whose numerator lies in `𝔭`.
Geometrically: the stalk at `𝔭` of the sheaf on `Proj A` associated to `M` is computed on the affine
chart `D₊(f)`.

The hypothesis `m > 0` cannot be dropped. For `A = M = k[X, Y]` graded by degree, `f = 1 ∈ 𝒜 0` and
`𝔭 = (X)` one has `A⁰_f = 𝒜 0 = k` and `M_(f) = ℳ 0 = k`, while `M_(𝔭)` contains `X/Y`, so `M_(𝔭)`
is not a localization of `M_(f)`.

## Main results

* `HomogeneousLocalization.isLocalizedModule_atPrime`: for `f` homogeneous of positive degree
  outside a homogeneous prime `𝔭`, the `A⁰_f`-module `M_(𝔭)` is the localization of `M_(f)` at the
  prime `𝔭'` of fractions with numerator in `𝔭`.

## Implementation notes

The source states two conclusions, `S_(𝔭) = (S_(f))_{𝔭'}` for the graded ring `S` and, compatibly,
`M_(𝔭) = (M_(f))_{𝔭'}` for a graded `S`-module `M`. Only the second is stated here: the first is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime`, the case `M = A` of what
follows, phrased there for a point of `D₊(f)` bundled as such and for `𝔭'` the image of that point
under `AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec 𝒜 f`.

`HomogeneousLocalization` is a construction on graded rings, so the two degree-zero localizations
of `M` have no name to refer to and are spelled out. For a submonoid `x ⊆ A` the degree-zero part
of `M_x` is the set of fractions `y/g` with `g ∈ x` homogeneous and `y` homogeneous of the same
degree; that set is already an `A⁰_f`-submodule of `LocalizedModule x M` — it is closed under
addition because `y/g + y'/g' = (g'y + gy')/(gg')` and the degrees add on both sides, and under
multiplication by a degree-zero fraction because degrees add there too — so it is written as the
span of the displayed fractions, which needs no closure proof. Taking `x = Submonoid.powers f`
gives `M_(f)` and `x = 𝔭.primeCompl` gives `M_(𝔭)`.

Passing to `LocalizedModule 𝔭.primeCompl M` allows a non-homogeneous denominator and a
non-homogeneous witness in the equality of fractions, where the source allows only homogeneous
ones. Neither widens `M_(𝔭)`: the displayed fractions have homogeneous denominators by fiat, and if
`h·u = 0` with `h ∉ 𝔭` and `u` homogeneous, then every homogeneous component of `h` kills `u`, and
one of them lies outside `𝔭` because `𝔭` is a homogeneous prime.

The grading of `M` is a family `ℳ : ℤ → τ` of additive submonoids with `DirectSum.Decomposition ℳ`,
together with the compatibility `𝒜 i · ℳ j ⊆ ℳ (i + j)` as an explicit hypothesis rather than as
`SetLike.GradedSMul 𝒜 ℳ`: the latter is stated in terms of `i +ᵥ j` for `i : ℕ` and `j : ℤ`, and
Mathlib provides no `VAdd ℕ ℤ`. Degrees of `M` range over `ℤ`, as in the source, while degrees of
`A` range over `ℕ`; a degree-zero fraction therefore has a numerator of non-negative degree.

The comparison map is asserted to exist rather than named, because naming it means restricting
`LocalizedModule.liftOfLE` — which is `A`-linear — to the two spans, and that restriction is
exactly the statement that the map sends degree-zero fractions to degree-zero fractions. The
assertion pins it: `LocalizedModule.liftOfLE` sends `y/g` to `y/g`, the spans are carried by
injections into the ambient localizations, so at most one `A⁰_f`-linear map satisfies the displayed
compatibility.

The prime `𝔭'` is taken abstractly, as any prime of `A⁰_f` satisfying the description that the
source's Lemma 00JP gives for it — `a/fⁿ ∈ 𝔭'` if and only if `a ∈ 𝔭` — rather than as a particular
construction of it; that description is representative-independent because `𝔭` is a homogeneous
prime. Such a prime exists and is unique: it is the contraction of the maximal ideal of the local
ring `A_(𝔭)` along `HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hf𝔭)`.

Faithfulness. (1) Every hypothesis is used: homogeneity of `𝔭` is what makes the description of `𝔭'`
correct and what identifies `M_(𝔭)` with the source's module of homogeneous fractions, `0 < m` is
used as displayed above, `f ∉ 𝔭` is what produces the map `M_(f) → M_(𝔭)` being asserted to be a
localization map, and the two grading hypotheses are the source's definition of a graded module.
(2) The scalars are the source's: both modules are modules over `A⁰_f`, the degree-zero part of
`A[1/f]` for the given grading, and the localization is taken at the multiplicative set
`A⁰_f ∖ 𝔭'`. (3) The instantiation is not degenerate: for `A = M = k[X, Y]` graded by degree,
`f = X` and `𝔭 = (Y)`, one has `A⁰_f = M_(f) = k[Y/X]`, `𝔭' = (Y/X)` and
`M_(𝔭) = k[Y/X]_{(Y/X)}`, a discrete valuation ring, so neither side is zero and neither
localization is trivial.

## References

* [StackProject 00JR](https://stacks.math.columbia.edu/tag/00JR)
-/

namespace HomogeneousLocalization

/-- Let `A` be a graded ring, let `M` be a graded `A`-module, let `𝔭` be a homogeneous prime ideal
of `A`, and let `f ∈ A` be homogeneous of positive degree with `f ∉ 𝔭`. Let `𝔭'` be the prime of the
degree-zero localization `A⁰_f` consisting of the fractions `a/fⁿ` with `a ∈ 𝔭`. Then the
`A⁰_f`-module `M_(𝔭)` of degree-zero fractions `y/g` with `g ∉ 𝔭` homogeneous is the localization of
the `A⁰_f`-module `M_(f)` of degree-zero fractions `y/fⁿ` at `𝔭'`. -/
@[stacks 00JR "The module equality `M_(𝔭) = (M_(f))_{𝔭'}`; the ring equality
`S_(𝔭) = (S_(f))_{𝔭'}` is `AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime`."]
public theorem isLocalizedModule_atPrime {σ τ A M : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [AddCommGroup M] [Module A M] [SetLike τ M] [AddSubmonoidClass τ M]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    (hℳ : ∀ (i : ℕ) (j : ℤ) (a : A) (y : M), a ∈ 𝒜 i → y ∈ ℳ j → a • y ∈ ℳ (i + j)) (𝔭 : Ideal A)
    [𝔭.IsPrime] (h𝔭 : 𝔭.IsHomogeneous 𝒜) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m) (hf𝔭 : f ∉ 𝔭)
    (𝔭' : Ideal (Away 𝒜 f)) [𝔭'.IsPrime]
    (h𝔭' : ∀ z : NumDenSameDeg 𝒜 (Submonoid.powers f), mk z ∈ 𝔭' ↔ (z.num : A) ∈ 𝔭) :
    letI : Module (Away 𝒜 f) (LocalizedModule (Submonoid.powers f) M) :=
      Module.compHom _ (algebraMap (Away 𝒜 f) (Localization (Submonoid.powers f)))
    letI : Module (Away 𝒜 f) (LocalizedModule 𝔭.primeCompl M) :=
      Module.compHom _
        ((algebraMap (AtPrime 𝒜 𝔭) (Localization 𝔭.primeCompl)).comp
          (mapId 𝒜 (Submonoid.powers_le.mpr hf𝔭)))
    ∃ φ :
      ↥(Submodule.span (Away 𝒜 f)
            {z : LocalizedModule (Submonoid.powers f) M |
              ∃ (i : ℕ) (y : M) (g : Submonoid.powers f),
                y ∈ ℳ (i : ℤ) ∧ (g : A) ∈ 𝒜 i ∧ z = .mk y g}) →ₗ[Away 𝒜 f]
        ↥(Submodule.span (Away 𝒜 f)
            {z : LocalizedModule 𝔭.primeCompl M |
              ∃ (i : ℕ) (y : M) (g : 𝔭.primeCompl), y ∈ ℳ (i : ℤ) ∧ (g : A) ∈ 𝒜 i ∧ z = .mk y g}),
      (∀ z,
          (φ z : LocalizedModule 𝔭.primeCompl M) =
            LocalizedModule.liftOfLE _ _ (Submonoid.powers_le.mpr hf𝔭) (z : _)) ∧
        IsLocalizedModule 𝔭'.primeCompl φ :=
  Stacks.GradedModule.DegreeZeroAtPrime.solution (m := m) (τ := τ) (σ := σ) 𝒜 ℳ hℳ 𝔭 h𝔭 hf hm
    hf𝔭 𝔭' h𝔭'

end HomogeneousLocalization
