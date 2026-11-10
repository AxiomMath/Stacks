module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# Degree-zero fractions of graded modules

A degree-zero homogeneous fraction `x / fⁿ` of a graded module, with `f` of degree one, is
evaluated against a degreewise family of additive maps. This is the algebraic input to the map
from degree-zero localized twisted sections to sections over the nonvanishing open of a section
of an invertible sheaf.

## Main definitions

* `Stacks.SheafOfModules.fractionValue` and
  `Stacks.SheafOfModules.degreeZeroLocalizationLift` evaluate a degree-zero homogeneous
  fraction against a degreewise family of additive maps, for an arbitrary graded ring and
  graded module.
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] _root_.SheafOfModules.forget PresheafOfModules.restrictScalars
  TopCat.Presheaf.IsSheaf TopCat.Sheaf AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance_reducible] TensorSheafification.structureSheaf

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace DirectSum
open scoped _root_.Stacks.SheafOfModules.TensorProduct

universe u

section FractionConstruction

universe v w t

/-- `ℕ` acts on `ℤ` by translation: a degree-`m` element of `A` carries `B n` into
`B (m + n)`. -/
local instance : VAdd ℕ ℤ where vadd n z := (n : ℤ) + z
variable {R : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing R] [AddCommGroup M] [Module R M]
  [SetLike σ R] [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A]
  [SetLike τ M] [AddSubgroupClass τ M] (B : ℤ → τ) [Decomposition B]
  [SetLike.GradedSMul A B] {f : R}

/-- Addition of fractions with denominators `fⁿ` and `fᵐ`. -/
private theorem mk_add_mk_pow (x y : M) (n m : ℕ) :
    LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩ +
      LocalizedModule.mk (S := Submonoid.powers f) y ⟨f ^ m, by exact ⟨m, rfl⟩⟩ =
    LocalizedModule.mk (S := Submonoid.powers f) (f ^ m • x + f ^ n • y)
      ⟨f ^ (n + m), by exact ⟨n + m, rfl⟩⟩ := by
  rw [LocalizedModule.mk_add_mk]
  congr 1
  exact Subtype.ext (pow_add f n m).symm

/-- Scalar multiplication of a fraction with denominator `fⁿ` by `r / fᵐ`. -/
private theorem val_mk_smul_mk_pow (hf : f ∈ A 1) {m : ℕ} {r : R} (hr : r ∈ A (m • 1)) (n : ℕ)
    (x : M) :
    HomogeneousLocalization.val (HomogeneousLocalization.Away.mk A hf m r hr) •
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩ =
    LocalizedModule.mk (S := Submonoid.powers f) (r • x)
      ⟨f ^ (m + n), by exact ⟨m + n, rfl⟩⟩ := by
  rw [HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
  congr 1
  exact Subtype.ext (pow_add f m n).symm

/-- For `f ∈ A 1`, every element of the degree-zero localization of `B` at `f` is a fraction
`x / fⁿ` with `x ∈ B n`. -/
public theorem degreeZeroLocalization_exists_fraction
    (hf : f ∈ A 1)
    (z : GradedModuleDegreeZeroLocalization A B f) :
    ∃ (n : ℕ) (x : M), x ∈ B (n : ℤ) ∧
      (z : LocalizedModule.Away f M) =
        LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩ := by
  let := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := R) f M)
    (algebraMap (HomogeneousLocalization.Away A f) (Localization.Away f))
  by_cases hf0 : f = 0
  · have : Subsingleton (LocalizedModule.Away (R := R) f M) :=
      LocalizedModule.subsingleton_iff.mpr (fun m => ⟨f, ⟨1, pow_one f⟩, by simp [hf0]⟩)
    exact ⟨0, 0, zero_mem _, Subsingleton.elim _ _⟩
  have hsmul : ∀ {r : R} {m n k : ℕ} {x : M}, r ∈ A m → x ∈ B (n : ℤ) → m + n = k →
      r • x ∈ B (k : ℤ) := fun {r m n k x} hr hx hk => by
    have h : r • x ∈ B ((m : ℤ) + n) := SetLike.GradedSMul.smul_mem hr hx
    simpa [← hk] using h
  rcases z with ⟨z, hz⟩
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨d, n, hfd, x, hx, rfl⟩ := hz
      have hd : d = 1 := degree_eq_of_mem_mem A hfd hf hf0
      subst d
      exact ⟨n, x, by simpa using hx, rfl⟩
  | zero => exact ⟨0, 0, zero_mem _, (LocalizedModule.zero_mk _).symm⟩
  | add z w hz hw ihz ihw =>
      obtain ⟨n, x, hx, rfl⟩ := ihz
      obtain ⟨m, y, hy, rfl⟩ := ihw
      refine ⟨n + m, f ^ m • x + f ^ n • y, ?_, ?_⟩
      · have hpow (k : ℕ) : f ^ k ∈ A k := by simpa using SetLike.pow_mem_graded k hf
        exact add_mem (hsmul (hpow m) hx (Nat.add_comm m n)) (hsmul (hpow n) hy rfl)
      · exact mk_add_mk_pow x y n m
  | smul a z hz ih =>
      obtain ⟨n, x, hx, rfl⟩ := ih
      obtain ⟨m, r, hr, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf a
      refine ⟨m + n, r • x, ?_, ?_⟩
      · exact hsmul (by simpa using hr) hx rfl
      · exact val_mk_smul_mk_pow A hf hr n x


variable {N : Type*} [AddCommGroup N]

omit [AddSubgroupClass τ M] [Decomposition B] in
private theorem fraction_values_eq
    (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B (n : ℤ) → e (n + k) (f ^ k • x) = e n x)
    (n m : ℕ) (x y : M) (hx : x ∈ B (n : ℤ)) (hy : y ∈ B (m : ℤ))
    (h : LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩ =
      LocalizedModule.mk (S := Submonoid.powers f) y ⟨f ^ m, by exact ⟨m, rfl⟩⟩) :
    e n x = e m y := by
  obtain ⟨⟨u, k, rfl⟩, hu⟩ := LocalizedModule.mk_eq.mp h
  change f ^ k • f ^ m • x = f ^ k • f ^ n • y at hu
  rw [smul_smul, smul_smul, ← pow_add, ← pow_add] at hu
  rw [← he n (k + m) x hx, ← he m (k + n) y hy]
  rw [show n + (k + m) = m + (k + n) by omega, hu]

/-- The value `e n x` of a degreewise family `e` of additive maps on a degree-zero fraction,
computed from a chosen representation `x / fⁿ`. -/
public noncomputable def fractionValue
    (hf : f ∈ A 1) (e : ℕ → M →+ N)
    (z : GradedModuleDegreeZeroLocalization A B f) : N :=
  let h := degreeZeroLocalization_exists_fraction A B hf z
  e h.choose h.choose_spec.choose

theorem fractionValue_eq
    (hf : f ∈ A 1) (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B (n : ℤ) → e (n + k) (f ^ k • x) = e n x)
    (z : GradedModuleDegreeZeroLocalization A B f)
    (n : ℕ) (x : M) (hx : x ∈ B (n : ℤ))
    (hz : (z : LocalizedModule.Away f M) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    fractionValue A B hf e z = e n x := by
  let h := degreeZeroLocalization_exists_fraction A B hf z
  exact fraction_values_eq B e he _ _ _ _ h.choose_spec.choose_spec.1 hx
    (h.choose_spec.choose_spec.2.symm.trans hz)

/-- If the family `e` is unchanged by multiplying numerator and denominator by a power of `f`,
then `x / fⁿ ↦ e n x` is a well-defined additive map on the degree-zero localization. -/
public noncomputable def degreeZeroLocalizationLift
    (hf : f ∈ A 1) (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B (n : ℤ) → e (n + k) (f ^ k • x) = e n x) :
    GradedModuleDegreeZeroLocalization A B f →+ N where
  toFun := fractionValue A B hf e
  map_zero' := by
    rw [fractionValue_eq A B hf e he 0 0 0 (zero_mem _) (by simp)]
    exact map_zero _
  map_add' z w := by
    obtain ⟨n, x, hx, hz⟩ := degreeZeroLocalization_exists_fraction A B hf z
    obtain ⟨m, y, hy, hw⟩ := degreeZeroLocalization_exists_fraction A B hf w
    have hmx : f ^ m • x ∈ B ((n + m : ℕ) : ℤ) := by
      have hp : f ^ m ∈ A m := by simpa using SetLike.pow_mem_graded m hf
      have h : f ^ m • x ∈ B ((m : ℤ) + n) := SetLike.GradedSMul.smul_mem hp hx
      simpa [Nat.cast_add, add_comm] using h
    have hny : f ^ n • y ∈ B ((n + m : ℕ) : ℤ) := by
      have hp : f ^ n ∈ A n := by simpa using SetLike.pow_mem_graded n hf
      have h : f ^ n • y ∈ B ((n : ℤ) + m) := SetLike.GradedSMul.smul_mem hp hy
      simpa [Nat.cast_add] using h
    have hzw : ((z + w : GradedModuleDegreeZeroLocalization A B f) :
        LocalizedModule.Away f M) =
        LocalizedModule.mk (S := Submonoid.powers f) (f ^ m • x + f ^ n • y)
          ⟨f ^ (n + m), by exact ⟨n + m, rfl⟩⟩ := by
      change (z : LocalizedModule.Away f M) + (w : LocalizedModule.Away f M) = _
      rw [hz, hw, LocalizedModule.mk_add_mk]
      congr 1
      exact Subtype.ext (pow_add f n m).symm
    rw [fractionValue_eq A B hf e he (z + w) (n + m) _ (add_mem hmx hny) hzw,
      fractionValue_eq A B hf e he z n x hx hz,
      fractionValue_eq A B hf e he w m y hy hw, map_add, he n m x hx]
    congr 1
    simpa [Nat.add_comm] using he m n y hy


theorem degreeZeroLocalizationLift_smul
    (hf : f ∈ A 1) (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B (n : ℤ) → e (n + k) (f ^ k • x) = e n x)
    {K : Type*} [CommRing K] [Module K N]
    (φ : HomogeneousLocalization.Away A f →+* K)
    (hφ : ∀ (m n : ℕ) (r : R) (x : M) (hr : r ∈ A (m • 1))
      (_hx : x ∈ B (n : ℤ)), e (m + n) (r • x) =
        φ (HomogeneousLocalization.Away.mk A hf m r hr) • e n x)
    (a : HomogeneousLocalization.Away A f) (z : GradedModuleDegreeZeroLocalization A B f) :
    degreeZeroLocalizationLift A B hf e he (a • z) =
      φ a • degreeZeroLocalizationLift A B hf e he z := by
  obtain ⟨n, x, hx, hz⟩ := degreeZeroLocalization_exists_fraction A B hf z
  obtain ⟨m, r, hr, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf a
  have hrx : r • x ∈ B ((m + n : ℕ) : ℤ) := by
    have h : r • x ∈ B ((m : ℤ) + n) := SetLike.GradedSMul.smul_mem (by simpa using hr) hx
    simpa [Nat.cast_add] using h
  have haz : ((HomogeneousLocalization.Away.mk A hf m r hr • z :
      GradedModuleDegreeZeroLocalization A B f) : LocalizedModule.Away f M) =
      LocalizedModule.mk (S := Submonoid.powers f) (r • x)
        ⟨f ^ (m + n), by exact ⟨m + n, rfl⟩⟩ := by
    change HomogeneousLocalization.val (HomogeneousLocalization.Away.mk A hf m r hr) •
      (z : LocalizedModule.Away f M) = _
    rw [hz, val_mk_smul_mk_pow A hf hr]
  change fractionValue A B hf e _ = _ • fractionValue A B hf e z
  rw [fractionValue_eq A B hf e he _ (m + n) (r • x) hrx haz,
    fractionValue_eq A B hf e he z n x hx hz]
  exact hφ m n r x hr hx


end FractionConstruction

end Stacks.SheafOfModules

end
