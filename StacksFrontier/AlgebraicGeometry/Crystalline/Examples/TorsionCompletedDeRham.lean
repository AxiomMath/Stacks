module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionNonvanishing
public import StacksFrontier.RingTheory.DividedPowers.CompletionUniversalProperty

/-!
# The complex `D → Ω¹_D → Ω²_D → ⋯` of the example of [Stacks, Tag 07LJ]

Fix a prime `p` and keep the situation of
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero`: the base
`(A, I, γ) = (ℤ_[p], (p), γ)`, the presentation `C = P/J = ℤ_[p][x, y]/(p, x², xy, y²)` of
`C = 𝐅_p[x, y]/(x², xy, y²)`, the `p`-adically completed divided power envelope
`D = D_{P, γ}(J)^∧` with its divided powers `γ̄`, and the element
`τ = γ̄_p(x²) γ̄_p(y²) − γ̄_p(xy)² ∈ D`.

This module builds the complex that [Stacks, Proposition 60.21.3, Tag 07LG] attaches to this
situation,

`D → Ω¹_D → Ω²_D → ⋯`,

as the `p`-adic completion of the divided power de Rham complex of `D` over `A`, and reads the
example's first numbered conclusion off it: the kernel of its degree zero differential has a
nonzero element killed by `p`, namely `τ`. The source states its conclusions for
`H⁰(Cris(X/S), 𝒪_{X/S})`, which [Stacks, Proposition 60.21.3, Tag 07LG] computes by this complex.

## Main definitions

* `Crystalline.TorsionExample.forms` is `Ω^i_{D/A,γ̄}`, the `i`-th module of divided power
  differential forms of [Stacks, Tag 07HZ], and `completedForms` is its `p`-adic completion
  `Ω^i_D`, the `i`-th term of the complex above.
* `Crystalline.TorsionExample.completedDifferential` is the completion of the divided power
  de Rham differential, and `Crystalline.TorsionExample.deRhamComplexNat` the resulting cochain
  complex of abelian groups indexed by `ℕ`.
* `Crystalline.TorsionExample.completedFormsZeroEquiv` is the identification `Ω^0_D = D` of the
  degree zero term with `D` itself.
* `Crystalline.TorsionExample.tauForm` is `τ` read as an element of `Ω^0_D`.

## Main results

* `Crystalline.TorsionExample.completedDifferential_tauForm` — `τ` lies in the kernel of the
  degree zero differential of the complex, which is `dτ = 0` transported along `Ω^0_D = D`.
* `Crystalline.TorsionExample.tauForm_ne_zero` and
  `Crystalline.TorsionExample.prime_smul_tauForm` — `τ ≠ 0` and `p τ = 0` in `Ω^0_D`.
* `Crystalline.TorsionExample.exists_ne_zero_prime_smul_eq_zero_ker_completedDifferential` —
  **conclusion (1) of [Stacks, Tag 07LJ] for the complex of [Stacks, Tag 07LG]**: the kernel of
  the degree zero differential of `D → Ω¹_D → ⋯` has a nonzero element killed by `p`.

## Implementation notes

The divided power de Rham differential of [Stacks, Tag 07HZ] is `A`-linear and `(p) ⊆ A`
generates the ideal for which `D` is a completion, so `Ω^i_D` is the adic completion of
`Ω^i_{D/A,γ̄}` for the ideal `(p) ⊆ A`; this makes the completed differential Mathlib's
`AdicCompletion.map` of an `A`-linear map.  Degree zero of the de Rham complex is the degree
zero exterior power, following the convention of Tag 07HZ, and `completedFormsZeroEquiv`
identifies it with `D`, which is legitimate because `D` is `p`-adically complete.

## References

* [Stacks Project, Tag 07LJ](https://stacks.math.columbia.edu/tag/07LJ)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

namespace Crystalline

namespace TorsionExample

variable (p : ℕ) [Fact p.Prime]

/-! ### The divided power differential forms of `D` and their completions -/

/-- The crystalline base ideal `(p) ⊆ ℤ_[p]`, the ideal for which the complex of
[Stacks, Tag 07LG] is completed. -/
abbrev baseIdeal : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p])}

/-- `Ω¹_{D/A,γ̄}`, the module of divided power differentials of `D` over the base `A = ℤ_[p]`. -/
abbrev differentials := dividedPowerDifferentials (A := ℤ_[p]) (completedGamma p)

/-- The universal divided power differential `D → Ω¹_{D/A,γ̄}`. -/
abbrev differential (b : completedEnvelope p) : differentials p :=
  dividedPowerDifferential (A := ℤ_[p]) (completedGamma p) b

/-- `Ω^i_{D/A,γ̄}`, the `i`-th module of divided power differential forms of `D` over the
crystalline base `A = ℤ_[p]` ([Stacks, Tag 07HZ]). -/
def forms (i : ℕ) : Type :=
  dividedPowerDifferentialForms (A := ℤ_[p]) (completedGamma p) i

/-- The additive group of `Ω^i_{D/A,γ̄}`. -/
instance instAddCommGroupForms (i : ℕ) : AddCommGroup (forms p i) :=
  inferInstanceAs (AddCommGroup
    (dividedPowerDifferentialForms (A := ℤ_[p]) (completedGamma p) i))

/-- The `D`-module structure on `Ω^i_{D/A,γ̄}`. -/
instance instModuleFormsD (i : ℕ) : Module (completedEnvelope p) (forms p i) :=
  inferInstanceAs (Module (completedEnvelope p)
    (dividedPowerDifferentialForms (A := ℤ_[p]) (completedGamma p) i))

/-- The `A`-module structure on `Ω^i_{D/A,γ̄}`, by restriction of scalars along `A → D`. -/
instance instModuleFormsA (i : ℕ) : Module ℤ_[p] (forms p i) :=
  Module.restrictScalars ℤ_[p] (completedEnvelope p) (forms p i)

/-- The `A`-action on `Ω^i_{D/A,γ̄}` is the `D`-action restricted along `A → D`. -/
instance instIsScalarTowerForms (i : ℕ) :
    IsScalarTower ℤ_[p] (completedEnvelope p) (forms p i) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The divided power de Rham differential `Ω^i_{D/A,γ̄} → Ω^{i+1}_{D/A,γ̄}` of
[Stacks, Tag 07HZ], which is `A`-linear. -/
def deRhamDifferential (i : ℕ) : forms p i →ₗ[ℤ_[p]] forms p (i + 1) :=
  (dividedPowerDeRhamComplex (A := ℤ_[p]) (completedGamma p)).differential i

/-- `Ω^i_D`, the `i`-th term of the complex of [Stacks, Tag 07LG] for this example: the `p`-adic
completion of `Ω^i_{D/A,γ̄}`. -/
def completedForms (i : ℕ) : Type := AdicCompletion (baseIdeal p) (forms p i)

/-- The additive group of `Ω^i_D`. -/
instance instAddCommGroupCompletedForms (i : ℕ) : AddCommGroup (completedForms p i) :=
  inferInstanceAs (AddCommGroup (AdicCompletion (baseIdeal p) (forms p i)))

/-- The `A`-module structure on `Ω^i_D`. -/
instance instModuleCompletedForms (i : ℕ) : Module ℤ_[p] (completedForms p i) :=
  inferInstanceAs (Module ℤ_[p] (AdicCompletion (baseIdeal p) (forms p i)))

/-- The canonical map `Ω^i_{D/A,γ̄} → Ω^i_D` onto the dense image in the completion. -/
def ofForms (i : ℕ) : forms p i →ₗ[ℤ_[p]] completedForms p i :=
  AdicCompletion.of (baseIdeal p) (forms p i)

/-- The `p`-adically completed divided power de Rham differential `Ω^i_D → Ω^{i+1}_D`. -/
def completedDifferential (i : ℕ) : completedForms p i →ₗ[ℤ_[p]] completedForms p (i + 1) :=
  (AdicCompletion.map (baseIdeal p) (deRhamDifferential p i)).restrictScalars ℤ_[p]

/-- The completed differential agrees with the divided power de Rham differential on the dense
image of `Ω^i_{D/A,γ̄}` in `Ω^i_D`.  This property characterises it, the image being dense. -/
theorem completedDifferential_ofForms (i : ℕ) (ω : forms p i) :
    completedDifferential p i (ofForms p i ω) = ofForms p (i + 1) (deRhamDifferential p i ω) :=
  AdicCompletion.map_of (baseIdeal p) (deRhamDifferential p i) ω

/-- Consecutive completed differentials compose to zero. -/
theorem completedDifferential_comp (i : ℕ) :
    (completedDifferential p (i + 1)).comp (completedDifferential p i) = 0 := by
  have h : (deRhamDifferential p (i + 1)).comp (deRhamDifferential p i) = 0 :=
    (dividedPowerDeRhamComplex (A := ℤ_[p]) (completedGamma p)).differential_squared i
  have h2 : (AdicCompletion.map (baseIdeal p) (deRhamDifferential p (i + 1))).comp
      (AdicCompletion.map (baseIdeal p) (deRhamDifferential p i)) = 0 := by
    rw [AdicCompletion.map_comp, h, AdicCompletion.map_zero]
  ext x
  exact LinearMap.congr_fun h2 x

/-- **The complex `D → Ω¹_D → Ω²_D → ⋯` of [Stacks, Proposition 60.21.3, Tag 07LG] for the
example of [Stacks, Tag 07LJ]**: the `p`-adically completed divided power de Rham complex of `D`
over `A = ℤ_[p]`, as a cochain complex of abelian groups indexed by `ℕ`. -/
def deRhamComplexNat : CochainComplex AddCommGrpCat.{0} ℕ :=
  CochainComplex.of (fun i ↦ AddCommGrpCat.of (completedForms p i))
    (fun i ↦ AddCommGrpCat.ofHom (completedDifferential p i).toAddMonoidHom)
    (fun i ↦ by
      ext x
      exact LinearMap.congr_fun (completedDifferential_comp p i) x)

/-- The degree-`i` term of the complex is `Ω^i_D`. -/
theorem deRhamComplexNat_X (i : ℕ) :
    (deRhamComplexNat p).X i = AddCommGrpCat.of (completedForms p i) := rfl

/-- The differential of the complex is the completed de Rham differential. -/
theorem deRhamComplexNat_d (i : ℕ) (x : completedForms p i) :
    (deRhamComplexNat p).d i (i + 1) x = completedDifferential p i x := by
  simp only [deRhamComplexNat, CochainComplex.of, CochainComplex.of_d]
  rfl

/-! ### The degree zero term is `D` -/

/-- `D` is `p`-adically complete as a module over the crystalline base `A = ℤ_[p]`: the ideal
`(p) ⊆ ℤ_[p]` generates the ideal `(p) ⊆ D` for which `D` is a `p`-adic completion. -/
instance instIsAdicCompleteBaseIdealCompletedEnvelope :
    IsAdicComplete (baseIdeal p) (completedEnvelope p) := by
  have hmap : (baseIdeal p).map (algebraMap ℤ_[p] (completedEnvelope p)) =
      DividedPowers.pAdicIdeal (A := completedEnvelope p) p := by
    rw [baseIdeal, Ideal.map_span]
    simp [DividedPowers.pAdicIdeal]
  have h1 : IsHausdorff (baseIdeal p) (completedEnvelope p) := by
    rw [← IsHausdorff.map_algebraMap_iff (S := completedEnvelope p) (I := baseIdeal p)
      (M := completedEnvelope p), hmap]
    infer_instance
  have h2 : IsPrecomplete (baseIdeal p) (completedEnvelope p) := by
    rw [← IsPrecomplete.map_algebraMap_iff (S := completedEnvelope p) (I := baseIdeal p)
      (M := completedEnvelope p), hmap]
    infer_instance
  exact { toIsHausdorff := h1, toIsPrecomplete := h2 }

/-- `Ω^0_{D/A,γ̄} = D`, the degree zero divided power forms being the degree zero exterior
power. -/
def formsZeroEquiv : forms p 0 ≃ₗ[completedEnvelope p] completedEnvelope p :=
  exteriorPower.zeroEquiv (completedEnvelope p) (differentials p)

/-- `Ω^1_{D/A,γ̄} = Ω¹_{D/A,γ̄}`, the degree one divided power forms being the degree one
exterior power. -/
def formsOneEquiv : forms p 1 ≃ₗ[completedEnvelope p] differentials p :=
  exteriorPower.oneEquiv (completedEnvelope p) (differentials p)

/-- The de Rham differential in degree zero, read through `Ω^0 = D` and `Ω^1 = Ω¹`, is the
universal divided power differential of `D`. -/
theorem formsOneEquiv_deRhamDifferential_zero (omega : forms p 0) :
    formsOneEquiv p (deRhamDifferential p 0 omega) =
      differential p (formsZeroEquiv p omega) := by
  set b := formsZeroEquiv p omega with hb
  have hzero : b • exteriorPower.ιMulti (completedEnvelope p) 0
      (fun _ : Fin 0 ↦ dividedPowerDifferential (A := ℤ_[p]) (completedGamma p) b) = omega := by
    refine (formsZeroEquiv p).injective ?_
    change exteriorPower.zeroEquiv (completedEnvelope p) (differentials p)
      (b • exteriorPower.ιMulti (completedEnvelope p) 0
        (fun _ : Fin 0 ↦ dividedPowerDifferential (A := ℤ_[p]) (completedGamma p) b)) = b
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  have hgen := (dividedPowerDeRhamComplex (A := ℤ_[p])
    (completedGamma p)).differential_generator 0 (fun _ : Fin 1 ↦ b)
  rw [hzero] at hgen
  change formsOneEquiv p ((dividedPowerDeRhamComplex (A := ℤ_[p])
    (completedGamma p)).differential 0 omega) = differential p b
  rw [hgen]
  change exteriorPower.oneEquiv (completedEnvelope p) (differentials p)
    (exteriorPower.ιMulti (completedEnvelope p) 1
      (fun _ : Fin 1 ↦ dividedPowerDifferential (A := ℤ_[p]) (completedGamma p) b)) =
    differential p b
  rw [← exteriorPower.oneEquiv_symm_apply, LinearEquiv.apply_symm_apply]

/-- The `A`-linear map `Ω^0_{D/A,γ̄} → D` underlying the identification `Ω^0_D = D`. -/
def formsZeroMap : forms p 0 →ₗ[ℤ_[p]] completedEnvelope p :=
  ((formsZeroEquiv p).restrictScalars ℤ_[p]).toLinearMap

/-- **The identification `Ω^0_D = D`** of the degree zero term of the complex of
[Stacks, Tag 07LG] with `D` itself: in degree zero the forms are the ring, and `D` is
`p`-adically complete. -/
def completedFormsZeroEquiv : completedForms p 0 ≃ₗ[ℤ_[p]] completedEnvelope p :=
  ((AdicCompletion.congr (baseIdeal p)
      ((formsZeroEquiv p).restrictScalars ℤ_[p])).restrictScalars ℤ_[p]).trans
    (AdicCompletion.ofLinearEquiv (baseIdeal p) (completedEnvelope p)).symm

/-- The identification `Ω^0_D = D` read against the canonical map into the completion. -/
theorem of_completedFormsZeroEquiv (xi : completedForms p 0) :
    AdicCompletion.of (baseIdeal p) (completedEnvelope p) (completedFormsZeroEquiv p xi) =
      AdicCompletion.map (baseIdeal p) (formsZeroMap p) xi := by
  change AdicCompletion.of (baseIdeal p) (completedEnvelope p)
    ((AdicCompletion.ofLinearEquiv (baseIdeal p) (completedEnvelope p)).symm
      (AdicCompletion.congr (baseIdeal p)
        ((formsZeroEquiv p).restrictScalars ℤ_[p]) xi)) = _
  rw [AdicCompletion.of_ofLinearEquiv_symm]
  rfl

/-- The identification `Ω^0_D = D` agrees with `Ω^0_{D/A,γ̄} = D` on the dense image. -/
@[simp]
theorem completedFormsZeroEquiv_ofForms (omega : forms p 0) :
    completedFormsZeroEquiv p (ofForms p 0 omega) = formsZeroEquiv p omega := by
  refine (AdicCompletion.ofLinearEquiv (baseIdeal p) (completedEnvelope p)).injective ?_
  change AdicCompletion.of (baseIdeal p) (completedEnvelope p)
      (completedFormsZeroEquiv p (ofForms p 0 omega)) =
    AdicCompletion.of (baseIdeal p) (completedEnvelope p) (formsZeroEquiv p omega)
  rw [of_completedFormsZeroEquiv]
  change AdicCompletion.map (baseIdeal p) (formsZeroMap p)
      (AdicCompletion.of (baseIdeal p) (forms p 0) omega) = _
  rw [AdicCompletion.map_of]
  rfl

/-! ### `τ` as an element of the degree zero term -/

/-- The element `τ = γ̄_p(x²) γ̄_p(y²) − γ̄_p(xy)²` read in the degree zero term `Ω^0_D` of the
complex of [Stacks, Tag 07LG], through the identification `Ω^0_D = D`. -/
def tauForm : completedForms p 0 := ofForms p 0 ((formsZeroEquiv p).symm (tau p))

/-- `tauForm` is `τ` under the identification `Ω^0_D = D`. -/
@[simp]
theorem completedFormsZeroEquiv_tauForm : completedFormsZeroEquiv p (tauForm p) = tau p := by
  rw [tauForm, completedFormsZeroEquiv_ofForms, LinearEquiv.apply_symm_apply]

/-- **`τ` lies in the kernel of the degree zero differential of the complex of
[Stacks, Tag 07LG]**, which is the example's identity `dτ = 0` read through `Ω^0_D = D`. -/
@[stacks 07LJ "dτ = 0 in Ω_D, the p-adic completion of the divided power differentials of \
D = D_{P,γ}(J)^∧ over ZZ_p: τ lies in the kernel of the degree zero differential of \
D → Ω¹_D → Ω²_D → ⋯"]
theorem completedDifferential_tauForm : completedDifferential p 0 (tauForm p) = 0 := by
  have hd : deRhamDifferential p 0 ((formsZeroEquiv p).symm (tau p)) = 0 := by
    refine (formsOneEquiv p).injective ?_
    rw [formsOneEquiv_deRhamDifferential_zero, LinearEquiv.apply_symm_apply, map_zero]
    exact dividedPowerDifferential_tau p
  rw [tauForm, completedDifferential_ofForms, hd, map_zero]

/-- **`τ ≠ 0` in `Ω^0_D`**: the identification `Ω^0_D = D` carries it to `τ`, which is nonzero
in `D`. -/
theorem tauForm_ne_zero : tauForm p ≠ 0 := by
  intro h
  have h0 : completedFormsZeroEquiv p (tauForm p) = 0 := by rw [h, map_zero]
  rw [completedFormsZeroEquiv_tauForm] at h0
  exact tau_ne_zero p h0

/-- **`p τ = 0` in `Ω^0_D`**, the example's torsion identity read through `Ω^0_D = D`. -/
theorem prime_smul_tauForm : (p : ℤ_[p]) • tauForm p = 0 := by
  refine (completedFormsZeroEquiv p).injective ?_
  rw [map_smul, completedFormsZeroEquiv_tauForm, map_zero, Algebra.smul_def, map_natCast]
  exact prime_mul_tau_eq_zero p

/-! ### Conclusion (1) of [Stacks, Tag 07LJ] for the complex of [Stacks, Tag 07LG] -/

/-- **Conclusion (1) of [Stacks, Tag 07LJ] for the complex of
[Stacks, Proposition 60.21.3, Tag 07LG]**: the kernel of the degree zero differential of

`D → Ω¹_D → Ω²_D → ⋯`

has a nonzero element killed by `p`.  The element is `τ = γ̄_p(x²) γ̄_p(y²) − γ̄_p(xy)²`: it is
killed by `d` by the example's displayed differential computation, it is killed by `p` by the
example's displayed divided power computation, and it is nonzero because it maps to `uv ≠ 0` in
the example's own witness thickening `B = 𝐅_p[x, y, u, v]/(x³, x²y, xy², y³, xu, yu, xv, yv,
u², v²)`. -/
theorem exists_ne_zero_prime_smul_eq_zero_ker_completedDifferential :
    ∃ a : LinearMap.ker (completedDifferential p 0), a ≠ 0 ∧ (p : ℤ_[p]) • a = 0 :=
  ⟨⟨tauForm p, LinearMap.mem_ker.mpr (completedDifferential_tauForm p)⟩,
    fun h ↦ tauForm_ne_zero p (congrArg Subtype.val h),
    Subtype.ext (prime_smul_tauForm p)⟩

end TorsionExample

end Crystalline

end
