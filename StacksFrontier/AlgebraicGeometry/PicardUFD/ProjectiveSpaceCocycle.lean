module

public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace

/-!
# The Picard group of projective space over a unique factorization domain

Grade `R[T₀, …, Tₙ]` by total degree, with `R` a unique factorization domain. Every invertible
module on `ℙⁿ_R = Proj R[T₀, …, Tₙ]` is a twist `𝒪(m)`: it is trivial on each standard chart
`D₊(Tᵢ)`, so it is described by the transition units of its chart generators; each of those is a
unit of `R` times an integer power of `Tᵢ / Tⱼ`; and the cocycle identity on the triple overlaps,
read at the generic point, forces a single exponent `m` and exhibits the units as a coboundary.
Rescaling the chart generators by that coboundary leaves exactly the transition units of `𝒪(m)`.

## Main results

* `Stacks.PicardUFD.exists_iso_twistingSheaf_general`: every invertible module on `ℙⁿ_R` is
  isomorphic to a twisting sheaf `𝒪(m)`, for every `n`.
* `Stacks.PicardUFD.twistPicardHom_surjective_general`: **the homomorphism `ℤ ⟶ Pic(ℙⁿ_R)`,
  `m ↦ 𝒪(m)`, is surjective for every `n`.**
* `Stacks.PicardUFD.twistPicardAddEquiv`: **the isomorphism `ℤ ≃+ Pic(ℙⁿ_R)` of Tag 0BXJ**, for
  `0 < n`, together with `Stacks.PicardUFD.twistPicardHom_bijective_general`.
* `Stacks.PicardUFD.subsingleton_picardGroup_dim_zero` and
  `Stacks.PicardUFD.not_injective_twistPicardHom_dim_zero`: at `n = 0` the Picard group of
  `ℙ⁰_R` is trivial, so `m ↦ 𝒪(m)` is the zero map and is not injective.

## Implementation notes

The exponent and the unit of each transition are read off at the generic point
`Stacks.PicardUFD.zeroPoint`, the zero ideal, which lies on every standard chart: there an
identity between products of constants and ratios `Tᵢ ^ e / Tⱼ ^ e` becomes an identity between
monomials of `R[T₀, …, Tₙ]`, and comparing the exponents of three distinct coordinates gives both
the equality of the exponents and the cocycle relation among the constants. This is the device of
the injectivity half of the tag, and it replaces any statement about injectivity of the
restriction maps between the rings of functions on the overlaps.

The constants are carried by `Stacks.PicardUFD.constSection`, the section `C r / 1` of the
structure sheaf on an arbitrary open; it restricts to itself on the nose, which is what makes the
coboundary rescaling a computation inside one commutative ring.

## References

* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.SheafOfModules

/-! ### Restricting a rescaled generator -/

section Rescale

open Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : RingedSpace.{u, u}} (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))

/-- The section of the restriction of a rescaled generator is the restricted unit times the
section of the restricted generator. -/
theorem generatorRestrict_smulUnit {U V : Opens X.carrier} (h : V ≤ U)
    (f : ((structureSheaf X.sheaf).obj.obj (op U))ˣ) (s : GeneratorSections X L U) :
    (generatorRestrict L h (generatorSmulUnit L f s)).val =
      (structureSheaf X.sheaf).obj.map (homOfLE h).op f.val •
        (generatorRestrict L h s).val :=
  PresheafOfModules.map_smul L.val (homOfLE h).op f.val s.val

end Rescale

end Stacks.SheafOfModules

namespace Stacks.PicardUFD

/-! ### The constant sections of the structure sheaf -/

section Constants

open Stacks.ProjectiveChart TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The fraction `C r / 1` in the local ring at a point of projective `n`-space. -/
def constFun (r : R)
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (x : W) :
    HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      x.1.asHomogeneousIdeal.toIdeal :=
  HomogeneousLocalization.mk ⟨0, ⟨MvPolynomial.C r, C_mem_degree_zero R n r⟩, 1, one_mem _⟩

/-- The constant fractions are multiplicative in the constant. -/
theorem constFun_mul (r s : R)
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (x : W) :
    constFun R n (r * s) x = constFun R n r x * constFun R n s x := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_mul, constFun, constFun, constFun,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk, Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

/-- The constant fraction at `1` is the unit of the local ring. -/
theorem constFun_one
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (x : W) : constFun R n (1 : R) x = 1 := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_one, constFun, HomogeneousLocalization.val_mk,
    ← Localization.mk_one]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

/-- The constant fraction is a section of the structure sheaf: it is a single homogeneous
fraction with numerator and denominator of degree zero. -/
theorem constFun_mem (r : R)
    (W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).pred (constFun R n r (W := W)) :=
  fun x => ⟨W, x.2, 𝟙 _, 0, ⟨MvPolynomial.C r, C_mem_degree_zero R n r⟩, 1,
    fun y => Submonoid.one_mem y.1.asHomogeneousIdeal.toIdeal.primeCompl, fun _ => rfl⟩

/-- The constant section `C r / 1` of the structure sheaf of projective `n`-space on an open. -/
def constSection (r : R)
    (W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) :
    (ProjectiveSpectrum.Proj.structureSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).obj.obj (op W) :=
  ⟨constFun R n r, constFun_mem R n r W⟩

/-- The constant sections are multiplicative in the constant. -/
theorem constSection_mul (r s : R)
    (W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) :
    constSection R n (r * s) W = constSection R n r W * constSection R n s W :=
  Subtype.ext (funext fun x => constFun_mul R n r s x)

/-- The constant section at `1` is the unit of the ring of sections. -/
theorem constSection_one
    (W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) :
    constSection R n (1 : R) W = 1 :=
  Subtype.ext (funext fun x => constFun_one R n x)

/-- The constant unit `C r / 1` of the ring of functions on an open, for `r` a unit of `R`. -/
def constUnitOn (r : Rˣ)
    (W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) :
    ((ProjectiveSpectrum.Proj.structureSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).obj.obj (op W))ˣ where
  val := constSection R n (r : R) W
  inv := constSection R n ((r⁻¹ : Rˣ) : R) W
  val_inv := by rw [← constSection_mul, r.mul_inv, constSection_one]
  inv_val := by rw [← constSection_mul, r.inv_mul, constSection_one]

/-- The constant unit on a standard chart of projective `n`-space. -/
def chartConstUnit (r : Rˣ) (i : Fin (n + 1)) :
    (Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)))ˣ :=
  constUnitOn R n r _

/-- The constant unit on the overlap of two standard charts of projective `n`-space. -/
def overlapConstUnit (r : Rˣ) (i j : Fin (n + 1)) :
    (Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.X j)))ˣ :=
  constUnitOn R n r _

theorem overlapConstUnit_val (r : Rˣ) (i j : Fin (n + 1)) :
    (overlapConstUnit R n r i j).val =
      constSection R n (r : R) (Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)) :=
  rfl

/-- The constant unit at `1` is the identity. -/
theorem overlapConstUnit_one (i j : Fin (n + 1)) : overlapConstUnit R n 1 i j = 1 :=
  Units.ext (constSection_one R n _)

/-- The constant units are multiplicative in the constant. -/
theorem overlapConstUnit_mul (r s : Rˣ) (i j : Fin (n + 1)) :
    overlapConstUnit R n (r * s) i j =
      overlapConstUnit R n r i j * overlapConstUnit R n s i j :=
  Units.ext (constSection_mul R n (r : R) (s : R) _)

/-- The fraction `Tᵢ ^ m / Tᵢ ^ m` is the unit of the local ring. -/
theorem ratioFun_self (m : ℤ) (i : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hWi hWj : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) (x : W) :
    ratioFun R m i i hWi hWj x = 1 := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_one, ratioFun, HomogeneousLocalization.val_mk,
    ← Localization.mk_one]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [mul_comm]))

/-- The transition unit of `𝒪(m)` from a standard chart to itself is `1`. -/
theorem overlapRatioUnit_self (m : ℤ) (i : Fin (n + 1)) : overlapRatioUnit R m i i = 1 :=
  Units.ext (Subtype.ext (funext fun x => ratioFun_self R n m i inf_le_left inf_le_right x))

/-- Restriction from the `i`-th chart to its overlap with the `j`-th carries the constant to the
constant. -/
theorem chartConstUnit_restrict_left (r : Rˣ) (i j : Fin (n + 1)) :
    (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
        (homOfLE (inf_le_left : Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (MvPolynomial.X j) ≤ _)).op (chartConstUnit R n r i).val =
      (overlapConstUnit R n r i j).val :=
  rfl

/-- Restriction from the `j`-th chart to its overlap with the `i`-th carries the constant to the
constant. -/
theorem chartConstUnit_restrict_right (r : Rˣ) (i j : Fin (n + 1)) :
    (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
        (homOfLE (inf_le_right : Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (MvPolynomial.X j) ≤ _)).op (chartConstUnit R n r j).val =
      (overlapConstUnit R n r i j).val :=
  rfl

end Constants

/-! ### The transition units of the chart generators of an invertible module -/

section Transition

open Stacks.ProjectiveChart Stacks.SheafOfModules TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ) [IsDomain R] [UniqueFactorizationMonoid R]
  (L : (AlgebraicGeometry.Proj
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
  [IsInvertible
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf
    (structureSheafRing (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace).property L]

/-- The transition unit of the chart generators of an invertible module on the overlap
`D₊(Tᵢ) ⊓ D₊(Tⱼ)` of two standard charts: the Čech `1`-cocycle of Tag 0BXJ. -/
def chartTransition (i j : Fin (n + 1)) :
    (Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.X j)))ˣ :=
  generatorRatioUnit L _
    (generatorRestrict L inf_le_right (chartGenerator R L j))
    (generatorRestrict L inf_le_left (chartGenerator R L i))

/-- The transition unit is the comparison scalar of the two restricted chart generators. -/
theorem chartTransition_val (i j : Fin (n + 1)) :
    (chartTransition R n L i j).val =
      generatorRatio L _ (generatorRestrict L inf_le_right (chartGenerator R L j))
        (generatorRestrict L inf_le_left (chartGenerator R L i)) :=
  generatorRatioUnit_val _ _ _ _

/-- The transition unit of a chart with itself is `1`. -/
theorem chartTransition_self (i : Fin (n + 1)) : chartTransition R n L i i = 1 :=
  generatorRatioUnit_self L _ _

/-- **The transition units compose at the generic point.** This is the cocycle identity of
Tag 0BXJ on the triple overlap `D₊(TᵢTⱼT_k)`, evaluated at the zero ideal. -/
theorem chartTransition_comp_apply (i j k : Fin (n + 1)) :
    (chartTransition R n L i j).val.1
        ⟨zeroPoint R n, ⟨zeroPoint_mem_basicOpen R n i, zeroPoint_mem_basicOpen R n j⟩⟩ *
      (chartTransition R n L j k).val.1
        ⟨zeroPoint R n, ⟨zeroPoint_mem_basicOpen R n j, zeroPoint_mem_basicOpen R n k⟩⟩ =
      (chartTransition R n L i k).val.1
        ⟨zeroPoint R n, ⟨zeroPoint_mem_basicOpen R n i, zeroPoint_mem_basicOpen R n k⟩⟩ := by
  have hVi : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X k) ≤
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) :=
    inf_le_left.trans inf_le_left
  have hVj : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X k) ≤
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j) :=
    inf_le_left.trans inf_le_right
  have hVk : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X k) ≤
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X k) :=
    inf_le_right
  have hcomp := generatorRatioUnit_comp L _
    (generatorRestrict L hVk (chartGenerator R L k))
    (generatorRestrict L hVj (chartGenerator R L j))
    (generatorRestrict L hVi (chartGenerator R L i))
  rw [generatorRatioUnit_restrict_inf L hVi hVj (chartGenerator R L i) (chartGenerator R L j),
    generatorRatioUnit_restrict_inf L hVj hVk (chartGenerator R L j) (chartGenerator R L k),
    generatorRatioUnit_restrict_inf L hVi hVk (chartGenerator R L i) (chartGenerator R L k)]
    at hcomp
  exact congrArg
    (fun z => z.val.1 ⟨zeroPoint R n, ⟨⟨zeroPoint_mem_basicOpen R n i,
      zeroPoint_mem_basicOpen R n j⟩, zeroPoint_mem_basicOpen R n k⟩⟩) hcomp

/-- **Every transition unit is a constant times an integer power of the ratio `Tᵢ / Tⱼ`.** The
module is trivial on the chart `D₊(Tᵢ)`, so the transition unit is an invertible function on the
overlap, and those are the units of the chart ring times a power of the ratio. -/
theorem exists_chartTransition_eq {i j : Fin (n + 1)} (hij : i ≠ j) :
    ∃ (e : ℤ) (r : Rˣ),
      chartTransition R n L i j = overlapConstUnit R n r i j * overlapRatioUnit R e i j := by
  obtain ⟨e, a, hea⟩ := exists_eq_restrict_mul_overlapRatioUnit R (Ne.symm hij)
    (chartTransition R n L i j)
  obtain ⟨r, hr, hra⟩ := exists_eq_sectionsChartEquiv_C_of_isUnit R n i a.isUnit
  refine ⟨e, hr.unit, hea.trans (congrArg (fun z => z * overlapRatioUnit R e i j) ?_)⟩
  refine Units.ext (Subtype.ext (funext fun x => ?_))
  show a.val.1 ⟨x.1, x.2.1⟩ = constFun R n ((hr.unit : Rˣ) : R) x
  rw [hra, hr.unit_spec]
  exact sectionsChartEquiv_C_apply R n i r _

/-- The transition unit of a chart with itself, in the normal form of the other transitions. -/
theorem chartTransition_self_eq (i : Fin (n + 1)) :
    chartTransition R n L i i = overlapConstUnit R n 1 i i * overlapRatioUnit R 0 i i := by
  rw [chartTransition_self, overlapRatioUnit_zero, mul_one, overlapConstUnit_one]

end Transition

/-! ### Monomial identities in two and three coordinates -/

section Monomials

open MvPolynomial

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Two monomials in two distinct coordinates with nonzero constant coefficients agree only
when their exponents and their coefficients do. -/
theorem eq_of_C_mul_X_pow_two {i j : Fin (n + 1)} (hij : i ≠ j) {p₁ q₁ p₂ q₂ : ℕ} {r t : R}
    (hr : r ≠ 0)
    (h : (C r * (X i ^ p₁ * X j ^ q₁) : MvPolynomial (Fin (n + 1)) R) =
      C t * (X i ^ p₂ * X j ^ q₂)) :
    p₁ = p₂ ∧ q₁ = q₂ ∧ r = t := by
  simp only [X_pow_eq_monomial, ← monomial_zero', monomial_mul_monomial, one_mul, mul_one,
    zero_add, monomial_eq_monomial_iff] at h
  rcases h with ⟨he, hrt⟩ | ⟨h0, -⟩
  · refine ⟨?_, ?_, hrt⟩
    · simpa [Finsupp.single_apply, hij, Ne.symm hij]
        using congrArg (fun f : Fin (n + 1) →₀ ℕ => f i) he
    · simpa [Finsupp.single_apply, hij, Ne.symm hij]
        using congrArg (fun f : Fin (n + 1) →₀ ℕ => f j) he
  · exact absurd h0 hr

/-- Two monomials in three distinct coordinates with nonzero constant coefficients agree only
when their exponents and their coefficients do. -/
theorem eq_of_C_mul_X_pow_three {i j k : Fin (n + 1)} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {p₁ q₁ s₁ p₂ q₂ s₂ : ℕ} {r t : R} (hr : r ≠ 0)
    (h : (C r * (X i ^ p₁ * X j ^ q₁ * X k ^ s₁) : MvPolynomial (Fin (n + 1)) R) =
      C t * (X i ^ p₂ * X j ^ q₂ * X k ^ s₂)) :
    p₁ = p₂ ∧ q₁ = q₂ ∧ s₁ = s₂ ∧ r = t := by
  simp only [X_pow_eq_monomial, ← monomial_zero', monomial_mul_monomial, one_mul, mul_one,
    zero_add, monomial_eq_monomial_iff] at h
  rcases h with ⟨he, hrt⟩ | ⟨h0, -⟩
  · refine ⟨?_, ?_, ?_, hrt⟩
    · simpa [Finsupp.single_apply, hij, hik, Ne.symm hij, Ne.symm hik]
        using congrArg (fun f : Fin (n + 1) →₀ ℕ => f i) he
    · simpa [Finsupp.single_apply, hij, hjk, Ne.symm hij, Ne.symm hjk]
        using congrArg (fun f : Fin (n + 1) →₀ ℕ => f j) he
    · simpa [Finsupp.single_apply, hik, hjk, Ne.symm hik, Ne.symm hjk]
        using congrArg (fun f : Fin (n + 1) →₀ ℕ => f k) he
  · exact absurd h0 hr

end Monomials

/-! ### The cocycle identity forces one exponent and a coboundary -/

section Cocycle

open Stacks.ProjectiveChart Stacks.SheafOfModules TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ) [IsDomain R] [UniqueFactorizationMonoid R]
  (L : (AlgebraicGeometry.Proj
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
  [IsInvertible
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf
    (structureSheafRing (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace).property L]

/-- The value at a point of a constant times the transition unit of a twist. -/
theorem overlapConstUnit_mul_overlapRatioUnit_apply (r : Rˣ) (e : ℤ) (i j : Fin (n + 1))
    (x : ↥(Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j))) :
    (overlapConstUnit R n r i j * overlapRatioUnit R e i j).val.1 x =
      constFun R n (r : R) x * ratioFun R e i j inf_le_left inf_le_right x :=
  rfl

/-- Clearing denominators in the cocycle identity at the generic point gives an identity between
monomials of `R[T₀, …, Tₙ]`. -/
private theorem monomial_eq_of_chartTransition {i j k : Fin (n + 1)} {a b c : ℤ} {s t w : Rˣ}
    (h₁ : chartTransition R n L i j = overlapConstUnit R n s i j * overlapRatioUnit R a i j)
    (h₂ : chartTransition R n L j k = overlapConstUnit R n t j k * overlapRatioUnit R b j k)
    (h₃ : chartTransition R n L i k = overlapConstUnit R n w i k * overlapRatioUnit R c i k) :
    (MvPolynomial.C ((s : R) * (t : R)) *
        (MvPolynomial.X i ^ (a.toNat + (-c).toNat) *
          MvPolynomial.X j ^ ((-a).toNat + b.toNat) *
          MvPolynomial.X k ^ ((-b).toNat + c.toNat)) : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.C ((w : R)) *
        (MvPolynomial.X i ^ ((-a).toNat + c.toNat) *
          MvPolynomial.X j ^ (a.toNat + (-b).toNat) *
          MvPolynomial.X k ^ (b.toNat + (-c).toNat)) := by
  have hcomp := chartTransition_comp_apply R n L i j k
  rw [h₁, h₂, h₃] at hcomp
  have hcomp2 := ((congrArg₂ (· * ·)
      (overlapConstUnit_mul_overlapRatioUnit_apply R n s a i j _).symm
      (overlapConstUnit_mul_overlapRatioUnit_apply R n t b j k _).symm).trans hcomp).trans
    (overlapConstUnit_mul_overlapRatioUnit_apply R n w c i k _)
  have hval := congrArg HomogeneousLocalization.val hcomp2
  simp only [HomogeneousLocalization.val_mul, constFun, ratioFun,
    HomogeneousLocalization.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists] at hval
  obtain ⟨d, hd⟩ := hval
  have hd0 : (d : MvPolynomial (Fin (n + 1)) R) ≠ 0 := fun h0 =>
    d.2 (by rw [h0]; exact Ideal.zero_mem _)
  simp only [Submonoid.coe_mul, SetLike.GradeZero.coe_one, one_mul, mul_one] at hd
  exact mul_left_cancel₀ hd0 (by simp only [map_mul, pow_add]; linear_combination hd)

/-- **The exponents of two opposite transitions agree and their constants are inverse.** -/
theorem exponent_eq_of_pair {i j : Fin (n + 1)} (hij : i ≠ j) {a b : ℤ} {s t : Rˣ}
    (h₁ : chartTransition R n L i j = overlapConstUnit R n s i j * overlapRatioUnit R a i j)
    (h₂ : chartTransition R n L j i = overlapConstUnit R n t j i * overlapRatioUnit R b j i) :
    a = b ∧ s * t = 1 := by
  have h := monomial_eq_of_chartTransition R n L h₁ h₂ (chartTransition_self_eq R n L i)
  simp only [Units.val_one, map_one, neg_zero, Int.toNat_zero, add_zero] at h
  obtain ⟨h1, -, h3⟩ := eq_of_C_mul_X_pow_two R n hij (mul_ne_zero s.ne_zero t.ne_zero)
    (p₁ := a.toNat + (-b).toNat) (q₁ := (-a).toNat + b.toNat) (p₂ := (-a).toNat + b.toNat)
    (q₂ := a.toNat + (-b).toNat) (t := 1) (by rw [map_one]; linear_combination h)
  exact ⟨by omega, Units.ext h3⟩

/-- **The cocycle identity on a triple overlap forces the three exponents to agree and the three
constants to compose.** -/
theorem exponent_eq_of_triple {i j k : Fin (n + 1)} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {a b c : ℤ} {s t w : Rˣ}
    (h₁ : chartTransition R n L i j = overlapConstUnit R n s i j * overlapRatioUnit R a i j)
    (h₂ : chartTransition R n L j k = overlapConstUnit R n t j k * overlapRatioUnit R b j k)
    (h₃ : chartTransition R n L i k = overlapConstUnit R n w i k * overlapRatioUnit R c i k) :
    a = b ∧ a = c ∧ s * t = w := by
  obtain ⟨h1, h2, -, h4⟩ := eq_of_C_mul_X_pow_three R n hij hjk hik
    (mul_ne_zero s.ne_zero t.ne_zero) (monomial_eq_of_chartTransition R n L h₁ h₂ h₃)
  exact ⟨by omega, by omega, Units.ext h4⟩

/-- **The normalizing data of Tag 0BXJ**: one twist degree `m` and one unit of `R` for each
standard chart, such that every transition unit of the chart generators is the coboundary of
those units times the transition unit of `𝒪(m)`. -/
theorem exists_normalizing_data (hn : 0 < n) :
    ∃ (m : ℤ) (v : Fin (n + 1) → Rˣ), ∀ i j : Fin (n + 1), i ≠ j →
      chartTransition R n L i j =
        overlapConstUnit R n (v i * (v j)⁻¹) i j * overlapRatioUnit R m i j := by
  classical
  have hdec : ∀ i j : Fin (n + 1), i ≠ j → ∃ (e : ℤ) (r : Rˣ),
      chartTransition R n L i j = overlapConstUnit R n r i j * overlapRatioUnit R e i j :=
    fun i j h => exists_chartTransition_eq R n L h
  choose! E S hES using hdec
  have hpair : ∀ i j : Fin (n + 1), i ≠ j → E i j = E j i ∧ S i j * S j i = 1 :=
    fun i j h => exponent_eq_of_pair R n L h (hES i j h) (hES j i (Ne.symm h))
  have htrip : ∀ i j k : Fin (n + 1), i ≠ j → j ≠ k → i ≠ k →
      E i j = E j k ∧ E i j = E i k ∧ S i j * S j k = S i k :=
    fun i j k h₁ h₂ h₃ =>
      exponent_eq_of_triple R n L h₁ h₂ h₃ (hES i j h₁) (hES j k h₂) (hES i k h₃)
  set p : Fin (n + 1) := ⟨1, by omega⟩ with hp
  have hpo : p ≠ (0 : Fin (n + 1)) := by
    intro h
    simpa [hp] using congrArg Fin.val h
  have hE0 : ∀ i : Fin (n + 1), i ≠ 0 → E i 0 = E p 0 := by
    intro i hi
    rcases eq_or_ne i p with rfl | hip
    · rfl
    · exact ((htrip i p 0 hip hpo hi).2.1).symm.trans (htrip i p 0 hip hpo hi).1
  refine ⟨E p 0, fun i => if i = 0 then 1 else S i 0, fun i j hij => ?_⟩
  have hE : E i j = E p 0 := by
    rcases eq_or_ne j 0 with rfl | hj0
    · exact hE0 i hij
    · rcases eq_or_ne i 0 with rfl | hi0
      · exact ((hpair 0 j hij).1).trans (hE0 j hj0)
      · exact ((htrip i j 0 hij hj0 hi0).1).trans (hE0 j hj0)
  have hS : S i j = (if i = 0 then 1 else S i 0) * (if j = 0 then 1 else S j 0)⁻¹ := by
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [if_pos rfl, if_neg hij, inv_one, mul_one]
    · rw [if_neg hj0]
      rcases eq_or_ne i 0 with rfl | hi0
      · rw [if_pos rfl, one_mul, eq_inv_iff_mul_eq_one]
        exact (hpair 0 j hij).2
      · rw [if_neg hi0, eq_mul_inv_iff_mul_eq]
        exact (htrip i j 0 hij hj0 hi0).2.2
  rw [hES i j hij, hE, hS]

end Cocycle

/-! ### Every invertible module on projective space is a twist -/

section Surjectivity

open Stacks.ProjectiveChart Stacks.SheafOfModules TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

variable [IsDomain R] [UniqueFactorizationMonoid R]
  (L : (AlgebraicGeometry.Proj
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
  [IsInvertible
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf
    (structureSheafRing (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace).property L]

/-- **The rescaled chart generators have exactly the transition units of `𝒪(m)`.** Rescaling the
generator on `D₊(Tᵢ)` by the constant `(vᵢ)⁻¹` cancels the constant of the transition unit, and
the ratio `(Tᵢ / Tⱼ) ^ m` is what is left. -/
theorem generatorRatioUnit_normalized (m : ℤ) (v : Fin (n + 1) → Rˣ)
    (hmv : ∀ i j : Fin (n + 1), i ≠ j →
      chartTransition R n L i j =
        overlapConstUnit R n (v i * (v j)⁻¹) i j * overlapRatioUnit R m i j)
    (i j : Fin (n + 1)) :
    generatorRatioUnit L _
        (generatorRestrict L inf_le_right (generatorSmulUnit L
          (chartConstUnit R n (v j)⁻¹ j) (chartGenerator R L j)))
        (generatorRestrict L inf_le_left (generatorSmulUnit L
          (chartConstUnit R n (v i)⁻¹ i) (chartGenerator R L i))) =
      overlapRatioUnit R m i j := by
  have hunit : overlapConstUnit R n (v i)⁻¹ i j * chartTransition R n L i j =
      overlapRatioUnit R m i j * overlapConstUnit R n (v j)⁻¹ i j := by
    rcases eq_or_ne i j with rfl | hij
    · rw [chartTransition_self, overlapRatioUnit_self, mul_one, one_mul]
    · rw [hmv i j hij, ← mul_assoc, ← overlapConstUnit_mul, inv_mul_cancel_left]
      exact mul_comm _ _
  have hring := congrArg Units.val hunit
  rw [Units.val_mul, Units.val_mul, chartTransition_val] at hring
  have h1 := Stacks.SheafOfModules.generatorRestrict_smulUnit L
    (inf_le_left : Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X j) ≤ _)
    (chartConstUnit R n (v i)⁻¹ i) (chartGenerator R L i)
  have h2 := Stacks.SheafOfModules.generatorRestrict_smulUnit L
    (inf_le_right : Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X j) ≤ _)
    (chartConstUnit R n (v j)⁻¹ j) (chartGenerator R L j)
  have hB' := generatorRatio_smul L _
    (generatorRestrict L inf_le_right (chartGenerator R L j))
    (generatorRestrict L inf_le_left (chartGenerator R L i))
    (generatorRestrict L inf_le_left (generatorSmulUnit L
      (chartConstUnit R n (v i)⁻¹ i) (chartGenerator R L i))) _ h1
  rw [← chartTransition_val] at hB'
  have hA : generatorRatioUnit L _
      (generatorRestrict L inf_le_right (chartGenerator R L j))
      (generatorRestrict L inf_le_right (generatorSmulUnit L
        (chartConstUnit R n (v j)⁻¹ j) (chartGenerator R L j))) =
      overlapConstUnit R n (v j)⁻¹ i j :=
    generatorRatioUnit_eq L _ _ _ _ h2
  have hB : generatorRatioUnit L _
      (generatorRestrict L inf_le_right (chartGenerator R L j))
      (generatorRestrict L inf_le_left (generatorSmulUnit L
        (chartConstUnit R n (v i)⁻¹ i) (chartGenerator R L i))) =
      overlapRatioUnit R m i j * overlapConstUnit R n (v j)⁻¹ i j :=
    Units.ext ((generatorRatioUnit_val L _ _ _).trans (hB'.trans hring))
  have hc := generatorRatioUnit_comp L _
    (generatorRestrict L inf_le_right (chartGenerator R L j))
    (generatorRestrict L inf_le_right (generatorSmulUnit L
      (chartConstUnit R n (v j)⁻¹ j) (chartGenerator R L j)))
    (generatorRestrict L inf_le_left (generatorSmulUnit L
      (chartConstUnit R n (v i)⁻¹ i) (chartGenerator R L i)))
  rw [hA, hB] at hc
  exact mul_right_cancel hc

end Surjectivity

/-! ### Surjectivity of `m ↦ 𝒪(m)` -/

section Conclusion

open Stacks.ProjectiveChart Stacks.SheafOfModules TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-- **Every invertible module on `ℙ⁰_R` is the trivial twist.** Projective `0`-space is covered
by its single standard chart, on which the module is trivial, so there is nothing to glue. -/
theorem exists_iso_twistingSheaf_dim_zero
    (M : (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R)).Modules)
    (hM : Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R)).presheaf
        (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R)).ringCatIsSheaf M) :
    Nonempty (M ≅ twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R) 0) := by
  have hMi := hM
  refine ⟨isoOfTransitionEq M
    (U := fun b : ULift.{u} (Fin (0 + 1)) =>
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R)
        (MvPolynomial.X b.down))
    (fun b => chartGenerator R M b.down) (fun b => twistChartGenerator R 0 b.down)
    (le_trans (le_of_eq (iSup_basicOpen_X_eq_top R 0).symm)
      (iSup_le fun i => le_iSup_of_le ⟨i⟩ le_rfl)) ?_⟩
  rintro ⟨i⟩ ⟨j⟩ V hi hj
  obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
  exact (generatorRatioUnit_self M V _).trans (generatorRatioUnit_self _ V _).symm

variable (n : ℕ)

/-- **Every invertible module on projective `n`-space over a unique factorization domain is a
twist `𝒪(m)`.** This is the content of Tag 0BXJ: the chart generators exist because each chart
has trivial Picard group, the cocycle identity on the triple overlaps gives one twist degree and
a coboundary, and rescaling by the coboundary matches the transition units of `𝒪(m)`. -/
theorem exists_iso_twistingSheaf_general
    (L : (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf
        (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).ringCatIsSheaf L) :
    ∃ m : ℤ, Nonempty
      (L ≅ twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m) := by
  have hLi := hL
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, exists_iso_twistingSheaf_dim_zero R L hL⟩
  obtain ⟨m, v, hmv⟩ := exists_normalizing_data R n L hn
  refine ⟨m, ⟨isoOfTransitionEq L
    (U := fun b : ULift.{u} (Fin (n + 1)) =>
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X b.down))
    (fun b => generatorSmulUnit L (chartConstUnit R n (v b.down)⁻¹ b.down)
      (chartGenerator R L b.down))
    (fun b => twistChartGenerator R m b.down)
    (le_trans (le_of_eq (iSup_basicOpen_X_eq_top R n).symm)
      (iSup_le fun i => le_iSup_of_le ⟨i⟩ le_rfl)) ?_⟩⟩
  rintro ⟨i⟩ ⟨j⟩ V hi hj
  exact ((generatorRatioUnit_restrict_inf L hi hj _ _).trans
    (congrArg _ ((generatorRatioUnit_normalized R n L m v hmv i j).trans
      (generatorRatioUnit_twistChartGenerator R m i j).symm))).trans
    (generatorRatioUnit_restrict_inf _ hi hj _ _).symm

/-- **Stacks Project, Tag 0BXJ.** The homomorphism `ℤ ⟶ Pic(ℙⁿ_R)`, `m ↦ 𝒪(m)`, is surjective
for `R` a unique factorization domain and every `n`. -/
@[stacks 0BXJ "surjectivity of m ↦ 𝒪(m), for every n"]
theorem twistPicardHom_surjective_general :
    Function.Surjective (twistPicardHom R n) := by
  intro x
  obtain ⟨M, hM, hMx⟩ := Stacks.SheafOfModules.exists_picardClass_eq
    (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf
    (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).ringCatIsSheaf x
  obtain ⟨m, ⟨e⟩⟩ := exists_iso_twistingSheaf_general R n M hM
  refine ⟨m, ?_⟩
  rw [twistPicardHom_apply, ← hMx]
  exact (AlgebraicGeometry.Scheme.picardClass_eq_iff _ _ _
    (isInvertible_twistingSheaf R n m) hM).mpr ⟨e.symm⟩

/-- **The homomorphism `ℤ ⟶ Pic(ℙⁿ_R)`, `m ↦ 𝒪(m)`, is bijective** for `0 < n`. -/
theorem twistPicardHom_bijective_general (hn : 0 < n) :
    Function.Bijective (twistPicardHom R n) :=
  ⟨twistPicardHom_injective R n hn, twistPicardHom_surjective_general R n⟩

/-- **Stacks Project, Tag 0BXJ.** The Picard group of `ℙⁿ_R` is `ℤ` for `R` a unique
factorization domain and `0 < n`, the isomorphism sending `m` to the class of `𝒪(m)`. -/
@[stacks 0BXJ "the isomorphism ℤ ≃+ Pic(ℙⁿ_R) carrying m to the class of 𝒪(m), for 0 < n"]
def twistPicardAddEquiv (hn : 0 < n) :
    ℤ ≃+ (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).picardGroup :=
  AddEquiv.ofBijective (twistPicardHom R n) (twistPicardHom_bijective_general R n hn)

@[simp] theorem twistPicardAddEquiv_apply (hn : 0 < n) (m : ℤ) :
    twistPicardAddEquiv R n hn m = twistPicardHom R n m :=
  rfl

/-- At `n = 0` every twist is trivial: the class of `𝒪(m)` in `Pic(ℙ⁰_R)` vanishes. -/
theorem twistPicardHom_dim_zero_apply (m : ℤ) : twistPicardHom R 0 m = 0 := by
  obtain ⟨e⟩ := exists_iso_twistingSheaf_dim_zero R
    (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R) m)
    (isInvertible_twistingSheaf R 0 m)
  rw [← map_zero (twistPicardHom R 0), twistPicardHom_apply, twistPicardHom_apply]
  exact (AlgebraicGeometry.Scheme.picardClass_eq_iff _ _ _
    (isInvertible_twistingSheaf R 0 m) (isInvertible_twistingSheaf R 0 0)).mpr ⟨e⟩

/-- **The Picard group of `ℙ⁰_R` is trivial.** -/
theorem subsingleton_picardGroup_dim_zero :
    Subsingleton (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (0 + 1)) R)).picardGroup := by
  refine AlgebraicGeometry.Scheme.subsingleton_picardGroup _ fun M hM => ?_
  obtain ⟨e⟩ := exists_iso_twistingSheaf_dim_zero R M hM
  refine (AlgebraicGeometry.Scheme.picardClass_eq_zero_iff _ M hM).mp ?_
  rw [(AlgebraicGeometry.Scheme.picardClass_eq_iff _ M _ hM
    (isInvertible_twistingSheaf R 0 0)).mpr ⟨e⟩]
  exact twistPicardHom_dim_zero_apply R 0

/-- **The boundary case of Tag 0BXJ.** The source states no restriction on `n`, but at `n = 0`
the Picard group of `ℙ⁰_R` is trivial, so `m ↦ 𝒪(m)` is the zero map and is not injective. -/
@[stacks 0BXJ "the n = 0 boundary case: m ↦ 𝒪(m) is the zero map into the trivial group \
  Pic(ℙ⁰_R) and is not injective, so the unrestricted source statement fails there"]
theorem not_injective_twistPicardHom_dim_zero :
    ¬ Function.Injective (twistPicardHom R 0) := fun h =>
  one_ne_zero (h ((twistPicardHom_dim_zero_apply R 1).trans
    (map_zero (twistPicardHom R 0)).symm))

end Conclusion

end Stacks.PicardUFD

end
