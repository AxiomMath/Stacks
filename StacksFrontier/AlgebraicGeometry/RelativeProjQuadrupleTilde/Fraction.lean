module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheaf

/-!
# The fractions `x / c^m` on a chart of a relative projective spectrum

Let `s` be a relative `Proj` situation, `ℳ` a graded module over its graded algebra, `U` an open
of the base and `c` a section of the degree-`d` piece of the algebra over `U`, `d ≥ 1`. For every
integer `m` and every section `x` of the degree-`md` piece of `ℳ` over `U`, the fraction `x / c^m`
is a section of the sheaf `ℳ̃(U)` attached to the graded module of sections of `ℳ` over `U` on the
standard open `D₊(c)` of `Proj 𝒜(U)`. For `m < 0` it is `c^{-m} x / 1`.

The fraction `x / c^m`, defined uniformly in `m`, is additive and `𝒪_S(U)`-linear in `x`, and it
carries the action of a section `a` of the degree-`id` piece of the algebra to the action of the
degree-zero fraction `a / c^i`.

## Main definitions

* `Stacks.RelativeProj.Situation.QuadrupleChart.fracElt`: the fraction `x / c^m` in the
  degree-zero localization of the graded module of sections.

## Main results

* `Stacks.RelativeProj.Situation.QuadrupleChart.fracElt_smul`: the action of a section `a` of
  degree `id` on `x / c^m` is the action of `a / c^i`.
* `Stacks.RelativeProj.Situation.QuadrupleChart.fracElt_smul_base`: `x / c^m` is linear over the
  functions on `U`.
* `Stacks.RelativeProj.Situation.QuadrupleChart.fracElt_add`: `x / c^m` is additive in `x`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.RelativeProj.Situation.QuadrupleChart

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  (U : s.base.Opens) {d : ℕ} (c : s.sectionPieces U d)

/-- The section `c`, as a homogeneous element of degree `d` of the graded ring of sections. -/
abbrev cHom : s.sectionRing U := DirectSum.of (s.sectionPieces U) d c

/-- The section `c` is homogeneous of degree `d`. -/
theorem cHom_mem : cHom U c ∈ s.sectionRingGrading U d := ⟨c, rfl⟩

/-- The exponent `m⁺ - m` of `c` by which `x / c^m` is written over the denominator `c^{m⁺}`,
`m⁺ = max m 0`. -/
def ex (m : ℤ) : ℕ := ((m.toNat : ℤ) - m).toNat

/-- `ex m + m = m⁺`. -/
theorem ex_spec (m : ℤ) : ((ex m : ℕ) : ℤ) + m = (m.toNat : ℤ) := by
  unfold ex
  omega

/-- The numerator `c^{m⁺ - m} x` of `x / c^m` lies in degree `m⁺ d`. -/
theorem mem_fracNum (m : ℤ) (x : sectionModulePieces ℳ U (m * d)) :
    (cHom U c) ^ ex m • DirectSum.of (sectionModulePieces ℳ U) (m * d) x ∈
      sectionModuleGrading ℳ U (m.toNat • (d : ℤ)) := by
  have h1 := SetLike.pow_mem_graded (ex m) (cHom_mem U c)
  have h2 := (sectionModuleGradedSMul ℳ U).smul_mem h1 (mem_sectionModuleGrading_of ℳ U x)
  have hdeg : ((ex m • d : ℕ) : ℤ) + m * d = (m.toNat • (d : ℤ)) := by
    have := ex_spec m
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
    linear_combination (d : ℤ) * this
  exact hdeg ▸ h2

/-- The degree-zero localization of the graded module of sections of `ℳ` over `U` away from
`c`. -/
abbrev Loc : Type u :=
  GradedModuleDegreeZeroLocalization (s.sectionRingGrading U) (sectionModuleGrading ℳ U) (cHom U c)

/-- **The fraction `x / c^m`** in the degree-zero localization, written `c^{m⁺ - m} x / c^{m⁺}`. -/
def fracElt (m : ℤ) (x : sectionModulePieces ℳ U (m * d)) : Loc ℳ U c :=
  degreeZeroFraction (s.sectionRingGrading U) (sectionModuleGrading ℳ U) (cHom_mem U c) m.toNat
    ((cHom U c) ^ ex m • DirectSum.of (sectionModulePieces ℳ U) (m * d) x)
    (mem_fracNum ℳ U c m x)

/-- The underlying element of `x / c^m` is `c^{m⁺ - m} x / c^{m⁺}`. -/
theorem fracElt_val (m : ℤ) (x : sectionModulePieces ℳ U (m * d)) :
    (fracElt ℳ U c m x).1 = LocalizedModule.mk
      ((cHom U c) ^ ex m • DirectSum.of (sectionModulePieces ℳ U) (m * d) x)
      (⟨(cHom U c) ^ m.toNat, m.toNat, rfl⟩ : Submonoid.powers (cHom U c)) := rfl

/-- **`x / c^m` may be written over any power `c^n`, `n ≥ m`.** -/
theorem fracElt_val_eq (m : ℤ) (x : sectionModulePieces ℳ U (m * d)) (n : ℕ) (k : ℕ)
    (hk : (k : ℤ) + m = n) :
    (fracElt ℳ U c m x).1 = LocalizedModule.mk
      ((cHom U c) ^ k • DirectSum.of (sectionModulePieces ℳ U) (m * d) x)
      (⟨(cHom U c) ^ n, n, rfl⟩ : Submonoid.powers (cHom U c)) := by
  rw [fracElt_val, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul, ← pow_add]
  congr 2
  have := ex_spec m
  omega

end Stacks.RelativeProj.Situation.QuadrupleChart

namespace Stacks.RelativeProj.Situation.QuadrupleChart

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  (U : s.base.Opens) {d : ℕ} (c : s.sectionPieces U d)

/-- **The action of a section `a` of degree `id` on `x / c^m` is the action of `a / c^i`.** The
product is any homogeneous section `y` of degree `(m + i)d` whose summand inclusion is the product
of those of `a` and `x`. -/
theorem fracElt_smul (m : ℤ) (i : ℕ) (a : s.sectionPieces U (i * d))
    (x : sectionModulePieces ℳ U (m * d)) (y : sectionModulePieces ℳ U ((m + i) * d))
    (hy : DirectSum.of (sectionModulePieces ℳ U) ((m + i) * d) y =
      DirectSum.of (s.sectionPieces U) (i * d) a •
        DirectSum.of (sectionModulePieces ℳ U) (m * d) x) :
    fracElt ℳ U c (m + i) y =
      HomogeneousLocalization.Away.mk (s.sectionRingGrading U) (cHom_mem U c) i
          (DirectSum.of (s.sectionPieces U) (i * d) a) ⟨a, rfl⟩ • fracElt ℳ U c m x := by
  apply Subtype.ext
  change (fracElt ℳ U c (m + i) y).1 =
    HomogeneousLocalization.val (HomogeneousLocalization.Away.mk (s.sectionRingGrading U)
      (cHom_mem U c) i (DirectSum.of (s.sectionPieces U) (i * d) a) ⟨a, rfl⟩) •
        (fracElt ℳ U c m x).1
  rw [fracElt_val_eq ℳ U c (m + i) y (i + m.toNat) (ex m) (by have := ex_spec m; push_cast; omega),
    fracElt_val]
  change _ = (Localization.mk (DirectSum.of (s.sectionPieces U) (i * d) a)
    (⟨(cHom U c) ^ i, i, rfl⟩ : Submonoid.powers (cHom U c)) : Localization.Away (cHom U c)) • _
  rw [LocalizedModule.mk_smul_mk, hy, smul_comm ((cHom U c) ^ ex m)]
  congr 1
  exact Subtype.ext (pow_add _ _ _)

/-- **`x / c^m` is linear over the functions on `U`**, which act through the degree-zero
fractions `r / 1`. -/
theorem fracElt_smul_base (m : ℤ) (r : s.base.ringCatSheaf.obj.obj (op U))
    (x : sectionModulePieces ℳ U (m * d)) :
    fracElt ℳ U c m (r • x) =
      HomogeneousLocalization.Away.mk (s.sectionRingGrading U) (cHom_mem U c) 0
          (s.sectionRingBaseMap U r) (by simpa using sectionRingBaseMap_mem_zero s U r) •
        fracElt ℳ U c m x := by
  apply Subtype.ext
  change (fracElt ℳ U c m (r • x)).1 = (Localization.mk (s.sectionRingBaseMap U r)
    (⟨(cHom U c) ^ 0, 0, rfl⟩ : Submonoid.powers (cHom U c)) : Localization.Away (cHom U c)) •
      (fracElt ℳ U c m x).1
  rw [fracElt_val, fracElt_val, LocalizedModule.mk_smul_mk, ← sectionRingBaseMap_smul_of,
    smul_comm ((cHom U c) ^ ex m)]
  congr 1
  exact Subtype.ext (by simp)

/-- The fraction `x / c^m` is additive in `x`. -/
theorem fracElt_add (m : ℤ) (x y : sectionModulePieces ℳ U (m * d)) :
    fracElt ℳ U c m (x + y) = fracElt ℳ U c m x + fracElt ℳ U c m y := by
  apply Subtype.ext
  change (fracElt ℳ U c m (x + y)).1 = (fracElt ℳ U c m x).1 + (fracElt ℳ U c m y).1
  rw [fracElt_val, fracElt_val, fracElt_val, LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [map_add, smul_add, one_smul, Submonoid.smul_def, mul_smul]

/-- The fraction `0 / c^m` is zero. -/
theorem fracElt_zero (m : ℤ) : fracElt ℳ U c m 0 = 0 := by
  apply Subtype.ext
  change (fracElt ℳ U c m 0).1 = 0
  rw [fracElt_val, map_zero, smul_zero, LocalizedModule.zero_mk]

end Stacks.RelativeProj.Situation.QuadrupleChart

end
