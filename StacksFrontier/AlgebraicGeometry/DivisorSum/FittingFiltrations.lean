module

public import StacksFrontier.AlgebraicGeometry.AnnihilatorQcoh.Qcoh
public import StacksFrontier.AlgebraicGeometry.DivisorSum.FittingDivisors
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierIdealFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.IdealSmul

/-!
# The two filtrations of Stacks tag 0ESU, as subsheaves

`StacksFrontier.AlgebraicGeometry.DivisorSum.FittingDivisors` produces the effective Cartier
divisors `D_j` of tag 0ESU on an admissible blowup, with `Fit_k(ℱ) = ∑_{j > k} (j - k) D_j` a
locally finite sum. The source then asserts that `ℱ` carries two canonical locally finite
filtrations

```
0 = F⁰ ⊆ F¹ ⊆ ⋯ ⊆ ℱ        and        ℱ = F₁ ⊇ F₂ ⊇ ⋯ ⊇ 0,
```

whose local descriptions on an affine open carrying equations `e_1, …, e_N` for the `D_j` are
`Fⁱ = (e_{i+1} ⋯ e_N) · ℱ` and `F_i = Ker(e_i ⋯ e_N : ℱ → ℱ)`. This file defines them as
*subsheaves* of `ℱ`, globally and with no choices, and identifies their sections on such an affine
open with the local descriptions.

## Main definitions

* `AlgebraicGeometry.idealSubsheaf`: the sheaf of ideals of a quasi-coherent ideal sheaf datum,
  at the type `Stacks.AlgebraicGeometry.AnnihilatorQcoh.IsAnnihilatorSubsheaf` consumes, namely a
  submodule of the unit sheaf `𝒪_X`.
* `AlgebraicGeometry.divisorTail`: the tail `D_i + D_{i+1} + ⋯` of a locally finite family of
  divisors, as a quasi-coherent ideal sheaf.
* `AlgebraicGeometry.fittingIncr`: the increasing filtration `Fⁱ = ℐ_{i+1} · ℱ`, where `ℐ_{i+1}`
  is the ideal of the tail `D_{i+1} + D_{i+2} + ⋯`.
* `AlgebraicGeometry.fittingDecr`: the decreasing filtration `F_i = Ann_ℱ(ℐ_i)`, the subsheaf of
  sections annihilated by the ideal of the tail `D_i + D_{i+1} + ⋯`.

## Main results

* `AlgebraicGeometry.divisorTail_ideal_eq_equationTail`: on an affine open carrying local
  equations the tail is cut out by the product `e_{i+1} ⋯ e_N`.
* `AlgebraicGeometry.mem_fittingIncr_iff`: `Fⁱ(V) = (e_{i+1} ⋯ e_N) · Γ(ℱ, V)`.
* `AlgebraicGeometry.mem_fittingDecr_iff`: `F_{i+1}(V) = Ker(e_{i+1} ⋯ e_N : Γ(ℱ, V) → Γ(ℱ, V))`.
* `AlgebraicGeometry.isQuasicoherent_fittingIncr` and
  `AlgebraicGeometry.isQuasicoherent_fittingDecr`: both filtrations are quasi-coherent.
* `AlgebraicGeometry.fittingIncr_mono` and `AlgebraicGeometry.fittingDecr_antitone`: **the two
  filtrations are monotone**, increasing and decreasing respectively. This is what lets the
  graded pieces `Fⁱ⁺¹/Fⁱ` and `F_i/F_{i+1}` be formed at all.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_divisors_filtrations`: **the blowup, the divisors
  and both filtrations together**, with the local descriptions on a cover by affine opens.

## Implementation notes

**Both filtrations are defined by ideal sheaves, not by local equations.** The increasing one is
the ideal-times-module subsheaf `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul` at
exponent one, whose affine sections are `ℐ(V) · Γ(ℱ, V)` by
`Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul`. The decreasing one is the annihilator
subsheaf `Stacks.SheafOfModules.annihilatorSubmodule`, whose membership condition quantifies over
all smaller opens; the collapse to the affine open itself is
`Stacks.AlgebraicGeometry.AnnihilatorQcoh.IsAnnihilatorSubsheaf.mem_iff_of_isAffineOpen`, tag
01PO. So neither definition refers to a chart, and the local descriptions below are theorems
rather than definitions — which is what makes the filtrations canonical.

**The ideal sheaf as a submodule of `𝒪_X`.** `AlgebraicGeometry.idealSubsheaf` is an `abbrev` for
the kernel of `𝒪_X ⟶ (ι_I)_* 𝒪_{V(I)}`, so the quasi-coherence
`Stacks.Algebraization.idealKernel_isQuasicoherent` and the affine sections
`Stacks.Algebraization.kernelSubmodule_obj_affine` of that kernel apply to it unchanged. No new
ideal-sheaf object is introduced.

**Indexing.** As in `FittingDivisors`, `D j` is the source's `D_{j+1}`. The tail `divisorTail D i`
is the sum of the source's `D_i, D_{i+1}, …`, so it is `locallyFiniteSum` with multiplicity one
exactly on the indices `j` with `i ≤ j + 1`. The increasing filtration uses the tail from `i + 1`
and the decreasing one the tail from `i`, matching
`Stacks.FittingFiltration.incr` and `Stacks.FittingFiltration.decr`.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
* [Stacks Project, Tag 01PO](https://stacks.math.columbia.edu/tag/01PO)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.Divisors Stacks.FittingFiltration
open Stacks.AlgebraicGeometry.AnnihilatorQcoh Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The sheaf of ideals as a submodule of the structure sheaf -/

/-- **The sheaf of ideals of a quasi-coherent ideal sheaf datum, as a submodule of `𝒪_X`.** This
is the kernel of `𝒪_X ⟶ (ι_I)_* 𝒪_{V(I)}`, which is the type that the annihilator-subsheaf API
of [Stacks, Tag 01PO] consumes. Its sections on an affine open are `I.ideal U`, by
`AlgebraicGeometry.idealSubsheaf_obj_affine`. -/
abbrev idealSubsheaf (I : X.IdealSheafData) :
    (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule :=
  Stacks.Algebraization.kernelSubmodule
    (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)

/-- On an affine open the sections of the sheaf of ideals of `I` are `I`'s own ideal there. -/
theorem idealSubsheaf_obj_affine (I : X.IdealSheafData) (U : X.affineOpens) :
    (idealSubsheaf I).toSubmodule.obj (op U.1) = I.ideal U :=
  Stacks.Algebraization.kernelSubmodule_obj_affine I U

/-! ### The tail of a locally finite family of divisors -/

/-- **The tail `D_i + D_{i+1} + ⋯` of a locally finite family of divisors.** In the indexing of
`AlgebraicGeometry.exists_divisors_locallyFiniteSum_eq_fittingIdeal`, where `D j` is the source's
`D_{j+1}`, this is the locally finite sum with multiplicity one on the indices `j` with
`i ≤ j + 1`. -/
def divisorTail (D : ℕ → X.IdealSheafData) (i : ℕ) : X.IdealSheafData :=
  locallyFiniteSum D fun j => if i ≤ j + 1 then 1 else 0

/-- **On an affine open carrying local equations the tail is cut out by the tail product.** If
`D_j` is cut out by `e_{j+1}` for `j + 1 ≤ N` and is empty from `N` on, then the tail from
`i + 1` is the ideal `(e_{i+1}) ⋯ (e_N)`. -/
theorem divisorTail_ideal_eq_equationTail {D : ℕ → X.IdealSheafData}
    (hD : IsLocallyFiniteFamily D) (V : X.affineOpens) {N : ℕ} {e : ℕ → Γ(X, V.1)}
    (hlow : ∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)})
    (htop : ∀ j, N ≤ j → (D j).ideal V = ⊤) (i : ℕ) :
    (divisorTail D (i + 1)).ideal V = equationTail e N i := by
  classical
  have hrange : ∀ j ∉ Finset.range N, (D j).ideal V = ⊤ := fun j hj =>
    htop j (by by_contra h; exact hj (Finset.mem_range.mpr (by omega)))
  rw [divisorTail, locallyFiniteSum_ideal_eq_finsetProd hD _ V hrange,
    Scheme.IdealSheafData.ideal_finsetProd_eq_prod]
  -- On the chart each factor is a power of a principal ideal, with exponent `0` or `1`.
  have hfac : (∏ j ∈ Finset.range N, ((D j) ^ (if i + 1 ≤ j + 1 then 1 else 0)).ideal V)
      = ∏ j ∈ Finset.range N, if i ≤ j then Ideal.span {e (j + 1)} else 1 := by
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    rw [ideal_pow_apply, hlow j (by omega)]
    rcases le_or_gt i j with hij | hij
    · rw [if_pos (by omega), if_pos hij, pow_one]
    · rw [if_neg (by omega), if_neg (by omega), pow_zero]
  rw [hfac, ← Finset.prod_filter]
  -- The surviving factors are indexed by `Ico i N`, which is `Icc (i+1) N` shifted by one.
  have hfilter : (Finset.range N).filter (fun j => i ≤ j) = Finset.Ico i N := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfilter, equationTail, show Finset.Icc (i + 1) N = (Finset.Ico i N).image (· + 1) by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_Ico]
    constructor
    · intro hz
      exact ⟨z - 1, by omega, by omega⟩
    · rintro ⟨w, hw, rfl⟩
      omega]
  rw [Finset.prod_image fun a _ b _ h => by simpa using h]

/-! ### The two filtrations -/

variable (D : ℕ → X.IdealSheafData) (F : X.Modules)

/-- **The increasing filtration of Stacks tag 0ESU, as a subsheaf.** `Fⁱ = ℐ_{i+1} · ℱ`, where
`ℐ_{i+1}` is the ideal of the tail `D_{i+1} + D_{i+2} + ⋯`. On an affine open carrying local
equations this is `(e_{i+1} ⋯ e_N) · Γ(ℱ, V)`, by `AlgebraicGeometry.mem_fittingIncr_iff` — the
local filtration `Stacks.FittingFiltration.incr`. -/
def fittingIncr [F.IsQuasicoherent] (i : ℕ) : F.Submodule :=
  idealPowSmul (divisorTail D (i + 1)) 1 F

/-- **The decreasing filtration of Stacks tag 0ESU, as a subsheaf.** `F_i = Ann_ℱ(ℐ_i)`, the
sections annihilated by the ideal of the tail `D_i + D_{i+1} + ⋯`. On an affine open carrying
local equations this is `Ker(e_i ⋯ e_N : Γ(ℱ, V) → Γ(ℱ, V))`, by
`AlgebraicGeometry.mem_fittingDecr_iff` — the local filtration
`Stacks.FittingFiltration.decr`. -/
def fittingDecr (i : ℕ) : F.Submodule :=
  Stacks.SheafOfModules.annihilatorSubmodule F (mul_comm_ringCatSheaf X)
    (idealSubsheaf (divisorTail D i))

/-- Both filtrations are quasi-coherent: the increasing one because an ideal multiple of a
quasi-coherent module is. -/
theorem isQuasicoherent_fittingIncr [F.IsQuasicoherent] (i : ℕ) :
    (fittingIncr D F i).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_idealPowSmul _ 1 F

/-- The decreasing filtration is quasi-coherent, by [Stacks, Tag 01PO] part (1): the ideal sheaf
of a divisor is quasi-coherent and of finite type, being locally principal. -/
theorem isQuasicoherent_fittingDecr [F.IsQuasicoherent] (i : ℕ)
    [(idealSubsheaf (divisorTail D i)).toSheafOfModules.IsFiniteType] :
    (fittingDecr D F i).toSheafOfModules.IsQuasicoherent := by
  have := Stacks.Algebraization.idealKernel_isQuasicoherent (divisorTail D i)
  exact (isAnnihilatorSubsheaf_annihilatorSubmodule _ F).isQuasicoherent

/-- **The ideal sheaf of the tail of a locally finite family of effective Cartier divisors is of
finite type.** The tail is itself an effective Cartier divisor, by
`AlgebraicGeometry.isEffectiveCartierDivisor_locallyFiniteSum`, so its ideal sheaf is invertible,
hence generated by one section near every point.

This is what supplies the finite-type hypothesis of
`AlgebraicGeometry.isQuasicoherent_fittingDecr`, which nothing in the tree discharged before. -/
theorem isFiniteType_idealSubsheaf_divisorTail (hD : IsLocallyFiniteFamily D)
    (hcart : ∀ j, IsEffectiveCartierDivisor (D j)) (i : ℕ) :
    (idealSubsheaf (divisorTail D i)).toSheafOfModules.IsFiniteType :=
  Stacks.Algebraization.idealKernel_isFiniteType_of_isEffectiveCartierDivisor _
    (isEffectiveCartierDivisor_locallyFiniteSum hD hcart _)

/-- **The decreasing filtration of a locally finite family of effective Cartier divisors is
quasi-coherent**, with no hypothesis beyond the ones 0ESU's divisors satisfy. This is
`AlgebraicGeometry.isQuasicoherent_fittingDecr` with its finite-type instance discharged by
`AlgebraicGeometry.isFiniteType_idealSubsheaf_divisorTail`. -/
theorem isQuasicoherent_fittingDecr_of_isEffectiveCartierDivisor [F.IsQuasicoherent]
    (hD : IsLocallyFiniteFamily D) (hcart : ∀ j, IsEffectiveCartierDivisor (D j)) (i : ℕ) :
    (fittingDecr D F i).toSheafOfModules.IsQuasicoherent :=
  have := isFiniteType_idealSubsheaf_divisorTail D hD hcart i
  isQuasicoherent_fittingDecr D F i

/-! ### Monotonicity of the two filtrations -/

/-- **The sheaf of ideals of an ideal sheaf datum is monotone in the datum.** Membership in a
subsheaf is affine-local, and on an affine open the sections are `I.ideal U` by
`AlgebraicGeometry.idealSubsheaf_obj_affine`, where the order on `X.IdealSheafData` is exactly
affine-local inclusion of ideals. -/
theorem idealSubsheaf_mono {I J : X.IdealSheafData} (h : I ≤ J) :
    idealSubsheaf I ≤ idealSubsheaf J := by
  intro U s hs
  refine Stacks.Algebraization.mem_submodule_of_affine
    (F := (SheafOfModules.unit.{u} X.ringCatSheaf : X.Modules)) (idealSubsheaf J) U.unop s
    fun V i => ?_
  have hsV := (idealSubsheaf I).toSubmodule.map_mem i.op hs
  rw [idealSubsheaf_obj_affine] at hsV
  rw [idealSubsheaf_obj_affine]
  exact Scheme.IdealSheafData.le_def.mp h V hsV

/-- **The tail `D_i + D_{i+1} + ⋯` shrinks as `i` grows**, so its sheaf of ideals grows. The
multiplicity function `j ↦ if i ≤ j + 1 then 1 else 0` is antitone in `i`, and
`Stacks.Divisors.locallyFiniteSum` is antitone in the multiplicities. -/
theorem divisorTail_mono (D : ℕ → X.IdealSheafData) : Monotone (divisorTail D) := by
  intro i i' h
  rw [divisorTail, divisorTail]
  refine locallyFiniteSum_antitone D fun j => ?_
  dsimp only
  split_ifs <;> omega

/-- **The increasing filtration is increasing.** `Fⁱ = ℐ_{i+1} · ℱ`, the ideal of the tail grows
with `i` by `AlgebraicGeometry.divisorTail_mono`, and an ideal multiple of `ℱ` is monotone in the
ideal by `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul_mono_left`. -/
theorem fittingIncr_mono [F.IsQuasicoherent] : Monotone (fittingIncr D F) := fun _ _ h =>
  idealPowSmul_mono_left (divisorTail_mono D (Nat.succ_le_succ h)) 1 F

/-- **The decreasing filtration is decreasing.** `F_i = Ann_ℱ(ℐ_i)` and the ideal of the tail
grows with `i`, so a section annihilated by every section of `ℐ_{i'}` is annihilated by every
section of the smaller `ℐ_i`. -/
theorem fittingDecr_antitone : Antitone (fittingDecr D F) := by
  intro i i' h U s hs Y g a ha
  exact hs Y g a (idealSubsheaf_mono (divisorTail_mono D h) Y ha)

/-! ### The local descriptions -/

/-- **The increasing filtration on an affine open carrying local equations.** A section of `ℱ`
over `V` lies in `Fⁱ` exactly when it is `(e_{i+1} ⋯ e_N)` times a section of `ℱ` over `V`. This
is `Stacks.FittingFiltration.incr`, which is the image of multiplication by that product. -/
theorem mem_fittingIncr_iff [F.IsQuasicoherent] {D : ℕ → X.IdealSheafData}
    (hD : IsLocallyFiniteFamily D) (V : X.affineOpens) {N : ℕ} {e : ℕ → Γ(X, V.1)}
    (hlow : ∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)})
    (htop : ∀ j, N ≤ j → (D j).ideal V = ⊤) (i : ℕ) (s : Γ(F, V.1)) :
    s ∈ (fittingIncr D F i).toSubmodule.obj (op V.1) ↔
      ∃ t : Γ(F, V.1), (∏ j ∈ Finset.Icc (i + 1) N, e j) • t = s := by
  rw [fittingIncr, obj_idealPowSmul, pow_one,
    divisorTail_ideal_eq_equationTail hD V hlow htop i, equationTail_eq_span]
  set g := ∏ j ∈ Finset.Icc (i + 1) N, e j with hg
  refine ⟨fun hs => ?_, ?_⟩
  · -- A product of a multiple of `g` with a section is `g` times a section.
    refine Submodule.smul_induction_on hs ?_ ?_
    · intro a ha x _
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      exact ⟨c • x, by rw [smul_smul, mul_comm]⟩
    · rintro x y ⟨tx, rfl⟩ ⟨ty, rfl⟩
      exact ⟨tx + ty, by rw [smul_add]⟩
  · rintro ⟨t, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self g) Submodule.mem_top

/-- **The decreasing filtration on an affine open carrying local equations.** A section of `ℱ`
over `V` lies in `F_{i+1}` exactly when `(e_{i+1} ⋯ e_N)` kills it. This is
`Stacks.FittingFiltration.decr`, the kernel of multiplication by that product.

The annihilator subsheaf asks for the vanishing of `a • s|_W` for every `W ≤ V` and every
section `a` of the ideal over `W`; [Stacks, Tag 01PO] part (2) collapses that to the single
condition over `V` itself, and the ideal of the tail is principal there. -/
theorem mem_fittingDecr_iff [F.IsQuasicoherent] {D : ℕ → X.IdealSheafData}
    (hD : IsLocallyFiniteFamily D) (V : X.affineOpens) {N : ℕ} {e : ℕ → Γ(X, V.1)}
    (hlow : ∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)})
    (htop : ∀ j, N ≤ j → (D j).ideal V = ⊤) (i : ℕ) (s : Γ(F, V.1)) :
    s ∈ (fittingDecr D F (i + 1)).toSubmodule.obj (op V.1) ↔
      (∏ j ∈ Finset.Icc (i + 1) N, e j) • s = 0 := by
  have := Stacks.Algebraization.idealKernel_isQuasicoherent (divisorTail D (i + 1))
  rw [fittingDecr,
    (isAnnihilatorSubsheaf_annihilatorSubmodule
      (idealSubsheaf (divisorTail D (i + 1))) F).mem_iff_of_isAffineOpen V.2 s,
    idealSubsheaf_obj_affine, divisorTail_ideal_eq_equationTail hD V hlow htop i,
    equationTail_eq_span]
  set g := ∏ j ∈ Finset.Icc (i + 1) N, e j with hg
  refine ⟨fun h => h g (Ideal.mem_span_singleton_self g), fun h a ha => ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [← smul_smul, h, smul_zero]

/-! ### The blowup, the divisors and both filtrations -/

/-- **Stacks Project, Tag 0ESU: an admissible blowup carrying the divisors `D_j` and both
filtrations of `b^*ℱ`.** For a finitely presented `𝒪_X`-module `ℱ` vanishing on an open `U`
there is a `U`-admissible blowup `b : X' → X` and effective Cartier divisors `D_j` on `X'`, only
finitely many meeting any affine open, with

* `Fit_k(b^*ℱ) = D_{k+1} + 2 D_{k+2} + ⋯` as a locally finite sum, and
* around every point an affine open `V` with equations `e_1, …, e_N` for the `D_j` on which the
  increasing filtration is `Fⁱ(V) = (e_{i+1} ⋯ e_N) · Γ(b^*ℱ, V)` and the decreasing one is
  `F_{i+1}(V) = Ker(e_{i+1} ⋯ e_N)`.

The filtrations themselves are the global subsheaves `AlgebraicGeometry.fittingIncr` and
`AlgebraicGeometry.fittingDecr` of the divisors, defined with no reference to a chart; the local
descriptions are the source's. -/
theorem exists_isAdmissibleBlowup_divisors_filtrations [F.IsFinitePresentation] (U : X.Opens)
    (hzero : CategoryTheory.Limits.IsZero ((Scheme.Modules.pullback U.ι).obj F)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X) (_ : Stacks.Blowup.IsAdmissibleBlowup U b)
      (_ : ((Scheme.Modules.pullback b).obj F).IsQuasicoherent)
      (D : ℕ → X'.IdealSheafData),
      (∀ j, IsEffectiveCartierDivisor (D j)) ∧
      IsLocallyFiniteFamily D ∧
      (∀ k : ℕ, fittingIdeal ((Scheme.Modules.pullback b).obj F) (k : ℤ) =
        locallyFiniteSum D fun j => (j + 1) - k) ∧
      ∀ x : X', ∃ V : X'.affineOpens, x ∈ (V.1 : Set X') ∧
        ∃ (N : ℕ) (e : ℕ → Γ(X', V.1)),
          (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
          (∀ j, N ≤ j → (D j).ideal V = ⊤) ∧
          (∀ j, e j ∈ nonZeroDivisors Γ(X', V.1)) ∧
          (∀ j, N < j → IsUnit (e j)) ∧
          (∀ k : ℕ, (fittingIdeal ((Scheme.Modules.pullback b).obj F) (k : ℤ)).ideal V =
            ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) ∧
          (∀ (i : ℕ) (s : Γ((Scheme.Modules.pullback b).obj F, V.1)),
            s ∈ (fittingIncr D ((Scheme.Modules.pullback b).obj F) i).toSubmodule.obj (op V.1) ↔
              ∃ t : Γ((Scheme.Modules.pullback b).obj F, V.1),
                (∏ j ∈ Finset.Icc (i + 1) N, e j) • t = s) ∧
          (∀ (i : ℕ) (s : Γ((Scheme.Modules.pullback b).obj F, V.1)),
            s ∈ (fittingDecr D ((Scheme.Modules.pullback b).obj F)
                (i + 1)).toSubmodule.obj (op V.1) ↔
              (∏ j ∈ Finset.Icc (i + 1) N, e j) • s = 0) := by
  obtain ⟨X', b, hb, D, hDcart, hlf, hsum, hchart⟩ :=
    exists_isAdmissibleBlowup_divisors F U hzero
  have hfp : ((Scheme.Modules.pullback b).obj F).IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ b.toLRSHom.toShHom F ‹_›
  have hqc : ((Scheme.Modules.pullback b).obj F).IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation _
  refine ⟨X', b, hb, hqc, D, hDcart, hlf, hsum, fun x => ?_⟩
  obtain ⟨V, hxV, N, e, hlow, htop, hemem, heunit, heprod⟩ := hchart x
  exact ⟨V, hxV, N, e, hlow, htop, hemem, heunit, heprod,
    fun i s => mem_fittingIncr_iff _ hlf V hlow htop i s,
    fun i s => mem_fittingDecr_iff _ hlf V hlow htop i s⟩

end AlgebraicGeometry

end
