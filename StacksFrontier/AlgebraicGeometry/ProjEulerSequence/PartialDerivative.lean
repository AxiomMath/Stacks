module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Comorphism
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away
public import StacksFrontier.RingTheory.Derivation.Localization
public import StacksFrontier.RingTheory.GradedAlgebra.GradedJacobian

/-!
# The coordinate derivatives of the structure sheaf of projective space

Let `R` be a commutative ring, grade `S = R[T₀, …, Tₙ]` by total degree and write
`X = Proj S = P^n_R`. For each variable `Tⱼ` the coordinate derivative `∂/∂Tⱼ` is a map of sheaves
of abelian groups `𝒪_X ⟶ 𝒪_X(-1)`: it raises the degree of a denominator by one, which is
exactly the twist by `-1`. This file constructs that map and establishes its Leibniz rule, its
vanishing on the sections coming from the coefficient ring, and the quotient rule that computes
it on a local fraction.

The construction is pointwise. The fibre of `𝒪_X` at a homogeneous prime `x` is the degree-zero
homogeneous localization `S_{(x)}`, which sits inside the full localization `S_x` by
`HomogeneousLocalization.val`; the derivation `∂/∂Tⱼ` of `S` extends uniquely to `S_x`, and the
extension applied to `val (a x)` is the value of `∂ⱼ a` at `x`. The quotient rule turns a local
representation `a = m / s` with `m, s` homogeneous of degree `d` into
`(s ∂ⱼm - m ∂ⱼs) / s²`, whose numerator is homogeneous of degree `2d - 1` and whose denominator
is homogeneous of degree `2d`: a local fraction for the twist by `-1`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.pderivFiber`: the unique extension of `∂/∂Tⱼ` to
  the localization of `R[T]` at a homogeneous prime.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.pderivApp`: the additive map
  `Γ(U, 𝒪_X) → Γ(U, 𝒪_X(-1))`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.projSpace` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOne`: `P^n_R` as a scheme and `𝒪(-1)`
  as a sheaf of modules on it.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.pderivDerivation`: the maps `pderivApp` packaged
  as a derivation of `𝒪_X` with values in `𝒪_X(-1)` relative to the constant presheaf `ℤ`.

## Main results

* `pderivApp_res` and `pderivApp_map`: the maps `pderivApp` commute with restriction, so they
  assemble into a morphism of sheaves of abelian groups.
* `pderivApp_mul`: the Leibniz rule `∂ⱼ(a b) = a • ∂ⱼ b + b • ∂ⱼ a`.
* `pderivApp_one`, `pderivFiber_algebraMap_C` and `pderivFiber_mk_C`: `∂ⱼ` kills the constants
  and, more generally, every fraction of two constants.
* `pderivFiber_val_eq_zero_of_isLocalization`: `∂ⱼ` kills the image of every ring map from a
  localization of `R` that sends constants to constants — in particular everything pulled back
  from the coefficient ring.
* `pderivApp_apply_of_val_eq_mk`: the quotient rule on a local fraction.
* `smul_sections_apply`: a section of `𝒪_X` acts on a section of a twist by multiplication in
  the localization at each point.

## Implementation notes

The fibres of all the twists `𝒪_X(d)` are the *same* object, namely the full localization `S_x`
of `R[T]` at the homogeneous prime `x`: twisting shifts the grading of the module `R[T]` but not
the module itself, and the localization forgets the grading. The twist is therefore recorded
entirely in the local-fraction condition cutting out the sections — a section of `𝒪_X(d)` is
locally `m / s` with `m` homogeneous of degree `k + d` and `s` homogeneous of degree `k` — and
not in the type of the fibres. This is what lets `∂ⱼ` be defined by one formula applied to the
fibres of `𝒪_X`, with all the degree bookkeeping concentrated in a single membership lemma.

The degree bookkeeping has one genuine edge case. The numerator `s ∂ⱼm - m ∂ⱼs` is homogeneous
of degree `2d - 1`, and for `d = 0` this would be degree `-1`, where the shifted grading is the
zero submodule. The numerator does vanish there: a polynomial homogeneous of degree zero is a
constant, so all its coordinate derivatives are zero. Mathlib's degree statement
`MvPolynomial.IsHomogeneous.pderiv` uses truncated subtraction and is therefore too weak to see
this, so the case `d = 0` is treated separately through
`MvPolynomial.IsWeightedHomogeneous.pderiv_eq_zero_of_lt'`.

## References

* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The ideal underlying a point of the projective spectrum of `R[T₀, …, Tₙ]` is prime. -/
local instance (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- The unique extension of `∂/∂Tⱼ` to the localization of `R[T₀, …, Tₙ]` at a homogeneous
prime of the total-degree grading. This localization is the fibre at that point of every twist
of the structure sheaf of `Proj R[T]`. -/
def pderivFiber (j : Fin (n + 1))
    (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)) :
    Derivation R (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) :=
  (MvPolynomial.pderiv j).localization x.asHomogeneousIdeal.toIdeal.primeCompl _

/-- **The quotient rule** for `pderivFiber`: the extension of `∂/∂Tⱼ` sends the fraction `a / s`
to `(s ∂ⱼa - a ∂ⱼs) / s²`. -/
theorem pderivFiber_mk (j : Fin (n + 1))
    (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n))
    (a : MvPolynomial (Fin (n + 1)) R) (s : x.asHomogeneousIdeal.toIdeal.primeCompl) :
    pderivFiber R n j x (Localization.mk a s) =
      Localization.mk ((s : MvPolynomial (Fin (n + 1)) R) * MvPolynomial.pderiv j a -
        a * MvPolynomial.pderiv j (s : MvPolynomial (Fin (n + 1)) R)) (s * s) :=
  Derivation.localization_mk _ _ a s

/-- `pderivFiber` extends `∂/∂Tⱼ` along the localization map. -/
@[simp] theorem pderivFiber_algebraMap (j : Fin (n + 1))
    (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n))
    (f : MvPolynomial (Fin (n + 1)) R) :
    pderivFiber R n j x (algebraMap (MvPolynomial (Fin (n + 1)) R) _ f) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) _ (MvPolynomial.pderiv j f) :=
  Derivation.localization_algebraMap _ _ _ f

/-- A polynomial homogeneous of degree zero is constant, so its coordinate derivatives vanish. -/
private theorem pderiv_eq_zero_of_mem_polyGrading_zero (j : Fin (n + 1))
    {f : MvPolynomial (Fin (n + 1)) R} (hf : f ∈ ProjPolyChart.polyGrading R n 0) :
    MvPolynomial.pderiv j f = 0 :=
  MvPolynomial.IsWeightedHomogeneous.pderiv_eq_zero_of_lt'
    ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hf) (by simp)

/-- A coordinate derivative of a polynomial homogeneous of degree `k` lies in the degree `k - 1`
piece of the total-degree grading extended to `ℤ` by zero. At `k = 0` the piece in question is
the zero submodule, and the derivative indeed vanishes: a degree-zero polynomial is a constant.
-/
theorem pderiv_mem_integerGrading (j : Fin (n + 1)) {k : ℕ}
    {f : MvPolynomial (Fin (n + 1)) R} (hf : f ∈ ProjPolyChart.polyGrading R n k) :
    MvPolynomial.pderiv j f ∈ integerGrading (ProjPolyChart.polyGrading R n) ((k : ℤ) - 1) := by
  have hf' : f.IsHomogeneous k := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
  match k with
  | 0 =>
    rw [pderiv_eq_zero_of_mem_polyGrading_zero R n j hf]
    exact zero_mem _
  | m + 1 =>
    have hcast : ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, integerGrading_natCast, mem_homogeneousSubmodule]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 hf'.pderiv

/-- The numerator produced by the quotient rule from a fraction of two polynomials homogeneous
of degree `k` lies in the degree `2k` piece of the grading of `R[T]` shifted by `-1`, that is in
degree `2k - 1` for the total-degree grading. -/
theorem quotient_num_mem (j : Fin (n + 1)) {k : ℕ} {m s : MvPolynomial (Fin (n + 1)) R}
    (hm : m ∈ ProjPolyChart.polyGrading R n k) (hs : s ∈ ProjPolyChart.polyGrading R n k) :
    s * MvPolynomial.pderiv j m - m * MvPolynomial.pderiv j s ∈
      twistGrading (ProjPolyChart.polyGrading R n) (-1) ((2 * k : ℕ) : ℤ) := by
  have hm' : m.IsHomogeneous k := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hm
  have hs' : s.IsHomogeneous k := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hs
  match k with
  | 0 =>
    rw [pderiv_eq_zero_of_mem_polyGrading_zero R n j hm,
      pderiv_eq_zero_of_mem_polyGrading_zero R n j hs]
    simp
  | k + 1 =>
    have hcast : ((2 * (k + 1) : ℕ) : ℤ) + (-1) = ((2 * k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [twistGrading_apply, hcast, integerGrading_natCast, mem_homogeneousSubmodule]
    have hdeg : k + 1 + k = 2 * k + 1 := by omega
    refine Submodule.sub_mem _ ?_ ?_
    · exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 (hdeg ▸ hs'.mul hm'.pderiv)
    · exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 (hdeg ▸ hm'.mul hs'.pderiv)

/-- The pointwise coordinate derivative of a section of `𝒪_X` satisfies the local-fraction
condition for the twist by `-1`: a local representation `m / s` with `m` and `s` homogeneous of
degree `k` is sent to `(s ∂ⱼm - m ∂ⱼs) / s²`, whose numerator is homogeneous of degree `2k - 1`
and whose denominator is homogeneous of degree `2k`. -/
theorem pderivSection_mem (j : Fin (n + 1))
    (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))
    (a : (ProjectiveSpectrum.Proj.structureSheaf
      (ProjPolyChart.polyGrading R n)).obj.obj (op U)) :
    (fun x : U => pderivFiber R n j x.1 (HomogeneousLocalization.val (a.1 x))) ∈
      moduleSections (ProjPolyChart.polyGrading R n)
        (twistGrading (ProjPolyChart.polyGrading R n) (-1)) U := by
  intro x
  obtain ⟨V, hxV, i, k, m, s, hnin, hval⟩ := a.2 x
  refine ⟨V, hxV, i, 2 * k,
    (s : MvPolynomial (Fin (n + 1)) R) *
        MvPolynomial.pderiv j (m : MvPolynomial (Fin (n + 1)) R) -
      (m : MvPolynomial (Fin (n + 1)) R) *
        MvPolynomial.pderiv j (s : MvPolynomial (Fin (n + 1)) R),
    (s : MvPolynomial (Fin (n + 1)) R) * (s : MvPolynomial (Fin (n + 1)) R),
    quotient_num_mem R n j m.2 s.2, ?_,
    fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hnin y) (hnin y), ?_⟩
  · have h2 : k + k = 2 * k := by omega
    exact h2 ▸ SetLike.mul_mem_graded s.2 s.2
  · intro y
    simp only [hval y, HomogeneousLocalization.val_mk, pderivFiber_mk]
    rfl

/-- **The `j`-th coordinate derivative on sections.** Over every open `U` of `Proj R[T]` it is the
additive map `Γ(U, 𝒪) → Γ(U, 𝒪(-1))` that applies the extension of `∂/∂Tⱼ` in each fibre. -/
def pderivApp (j : Fin (n + 1))
    (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n))) :
    (ProjectiveSpectrum.Proj.structureSheaf
        (ProjPolyChart.polyGrading R n)).obj.obj (op U) →+
      moduleSections (ProjPolyChart.polyGrading R n)
        (twistGrading (ProjPolyChart.polyGrading R n) (-1)) U where
  toFun a := ⟨fun x => pderivFiber R n j x.1 (HomogeneousLocalization.val (a.1 x)),
    pderivSection_mem R n j U a⟩
  map_zero' := by
    refine Subtype.ext (funext fun x => ?_)
    simp
  map_add' a b := by
    refine Subtype.ext (funext fun x => ?_)
    simp [HomogeneousLocalization.val_add]

/-- The value of `pderivApp R n j U a` at a point `x` is the extension of `∂/∂Tⱼ` to the fibre at
`x`, applied to the value of `a` at `x`. -/
@[simp] theorem pderivApp_apply (j : Fin (n + 1))
    (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))
    (a : (ProjectiveSpectrum.Proj.structureSheaf
      (ProjPolyChart.polyGrading R n)).obj.obj (op U)) (x : U) :
    (pderivApp R n j U a).1 x =
      pderivFiber R n j x.1 (HomogeneousLocalization.val (a.1 x)) := rfl

/-- **`pderivApp` is natural in `U`.** Restricting the coordinate derivative of a section is the
coordinate derivative of its restriction, so the maps `pderivApp` constitute a morphism of sheaves
of abelian groups `𝒪_X ⟶ 𝒪_X(-1)`. -/
theorem pderivApp_res (j : Fin (n + 1))
    {U V : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n))} (i : V ⟶ U)
    (a : (ProjectiveSpectrum.Proj.structureSheaf
      (ProjPolyChart.polyGrading R n)).obj.obj (op U)) :
    (modulePresheaf (ProjPolyChart.polyGrading R n)
        (twistGrading (ProjPolyChart.polyGrading R n) (-1))).map i.op (pderivApp R n j U a) =
      pderivApp R n j V ((ProjectiveSpectrum.Proj.structureSheaf
        (ProjPolyChart.polyGrading R n)).obj.map i.op a) := rfl

/-- `pderivApp_res` in the form of a naturality square over the opposite category of opens. -/
theorem pderivApp_map (j : Fin (n + 1))
    {W W' : (Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))ᵒᵖ} (f : W ⟶ W')
    (a : (ProjectiveSpectrum.Proj.structureSheaf
      (ProjPolyChart.polyGrading R n)).obj.obj W) :
    pderivApp R n j W'.unop
        ((ProjectiveSpectrum.Proj.structureSheaf (ProjPolyChart.polyGrading R n)).obj.map f a) =
      (modulePresheaf (ProjPolyChart.polyGrading R n)
        (twistGrading (ProjPolyChart.polyGrading R n) (-1))).map f
          (pderivApp R n j W.unop a) := rfl

/-- Addition of sections of a twist is pointwise addition in the fibres. -/
theorem add_sections_apply (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))
    (σ τ : moduleSections (ProjPolyChart.polyGrading R n)
      (twistGrading (ProjPolyChart.polyGrading R n) d) U) (x : U) :
    (σ + τ).1 x = σ.1 x + τ.1 x := rfl

/-- The fibre of a twist at `x` is the localization of `R[T]` at `x`, and the action of that
localization on the fibre is its own multiplication. -/
theorem fiber_smul_eq_mul (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n))
    (u : Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
    (v : ModuleFiber (M := MvPolynomial (Fin (n + 1)) R)
      (ProjPolyChart.polyGrading R n) x) :
    u • v = u * v := rfl

/-- **The action of `𝒪_X` on a twist, read in a fibre.** A section of the structure sheaf acts on
a section of `𝒪_X(d)` through its own value in the full localization at each point. -/
theorem smul_sections_apply' (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))
    (r : (ProjectiveSpectrum.Proj.structureSheaf
      (ProjPolyChart.polyGrading R n)).obj.obj (op U))
    (σ : moduleSections (ProjPolyChart.polyGrading R n)
      (twistGrading (ProjPolyChart.polyGrading R n) d) U) (x : U) :
    (r • σ).1 x = HomogeneousLocalization.val (r.1 x) • σ.1 x := rfl

/-- `smul_sections_apply'` with the action rewritten as multiplication in the localization at
the point. This is the form the Leibniz rule is stated in. -/
theorem smul_sections_apply (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))
    (r : (ProjectiveSpectrum.Proj.structureSheaf
      (ProjPolyChart.polyGrading R n)).obj.obj (op U))
    (σ : moduleSections (ProjPolyChart.polyGrading R n)
      (twistGrading (ProjPolyChart.polyGrading R n) d) U) (x : U) :
    (r • σ).1 x = HomogeneousLocalization.val (r.1 x) * σ.1 x :=
  (smul_sections_apply' R n d U r σ x).trans (fiber_smul_eq_mul R n x.1 _ _)

/-- **The Leibniz rule.** `∂ⱼ(a b) = a ∂ⱼb + b ∂ⱼa`, where a section of `𝒪_X` acts on sections
of `𝒪_X(-1)` through its value in each fibre. -/
theorem pderivApp_mul (j : Fin (n + 1))
    (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))
    (a b : (ProjectiveSpectrum.Proj.structureSheaf
      (ProjPolyChart.polyGrading R n)).obj.obj (op U)) :
    pderivApp R n j U (a * b) = a • pderivApp R n j U b + b • pderivApp R n j U a := by
  refine Subtype.ext (funext fun x => ?_)
  have hval : HomogeneousLocalization.val ((a * b).1 x) =
      HomogeneousLocalization.val (a.1 x) * HomogeneousLocalization.val (b.1 x) :=
    HomogeneousLocalization.val_mul _ _
  have hleib : pderivFiber R n j x.1 (HomogeneousLocalization.val ((a * b).1 x)) =
      HomogeneousLocalization.val (a.1 x) *
          pderivFiber R n j x.1 (HomogeneousLocalization.val (b.1 x)) +
        HomogeneousLocalization.val (b.1 x) *
          pderivFiber R n j x.1 (HomogeneousLocalization.val (a.1 x)) := by
    rw [hval, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hadd := add_sections_apply R n (-1) U
    (a • pderivApp R n j U b) (b • pderivApp R n j U a) x
  have hsmul₁ : (a • pderivApp R n j U b).1 x = HomogeneousLocalization.val (a.1 x) *
      pderivFiber R n j x.1 (HomogeneousLocalization.val (b.1 x)) :=
    smul_sections_apply R n (-1) U a (pderivApp R n j U b) x
  have hsmul₂ : (b • pderivApp R n j U a).1 x = HomogeneousLocalization.val (b.1 x) *
      pderivFiber R n j x.1 (HomogeneousLocalization.val (a.1 x)) :=
    smul_sections_apply R n (-1) U b (pderivApp R n j U a) x
  exact hleib.trans ((congrArg₂ (· + ·) hsmul₁.symm hsmul₂.symm).trans hadd.symm)

/-- **The computation rule.** If the value of `a` at `x` is the fraction `m / s`, then the value
of `∂ⱼ a` at `x` is `(s ∂ⱼm - m ∂ⱼs) / s²`. No homogeneity is needed for this identity; it is
needed only to know that `∂ⱼ a` is a section of the twist by `-1`. -/
theorem pderivApp_apply_of_val_eq_mk (j : Fin (n + 1))
    (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))
    (a : (ProjectiveSpectrum.Proj.structureSheaf
      (ProjPolyChart.polyGrading R n)).obj.obj (op U)) (x : U)
    {m s : MvPolynomial (Fin (n + 1)) R}
    (hs : s ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl)
    (ha : HomogeneousLocalization.val (a.1 x) = Localization.mk m ⟨s, hs⟩) :
    (pderivApp R n j U a).1 x =
      Localization.mk (s * MvPolynomial.pderiv j m - m * MvPolynomial.pderiv j s)
        ⟨s * s, x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hs hs⟩ := by
  rw [pderivApp_apply, ha, pderivFiber_mk]
  rfl

/-- `∂ⱼ` annihilates the image of a constant polynomial in a fibre. -/
@[simp] theorem pderivFiber_algebraMap_C (j : Fin (n + 1))
    (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)) (r : R) :
    pderivFiber R n j x
      (algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.C r)) = 0 := by
  rw [pderivFiber_algebraMap, MvPolynomial.pderiv_C, map_zero]

/-- `∂ⱼ` annihilates a fibre value that is a fraction of two constant polynomials. This is the
local shape of a function pulled back from the coefficient ring. -/
theorem pderivFiber_mk_C (j : Fin (n + 1))
    (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)) (c t : R)
    (ht : MvPolynomial.C t ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    pderivFiber R n j x (Localization.mk (MvPolynomial.C c) ⟨MvPolynomial.C t, ht⟩) = 0 := by
  rw [pderivFiber_mk]
  simp [Localization.mk_zero]

/-- `∂ⱼ` annihilates the unit section, hence every section of the constant presheaf `ℤ`. -/
@[simp] theorem pderivApp_one (j : Fin (n + 1))
    (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n))) :
    pderivApp R n j U 1 = 0 := by
  refine Subtype.ext (funext fun x => ?_)
  simp [HomogeneousLocalization.val_one]

/-- A section is annihilated by `∂ⱼ` exactly when it is annihilated in every fibre; sections of
`𝒪_X(-1)` are dependent functions, so vanishing is a pointwise condition. -/
theorem pderivApp_eq_zero_iff (j : Fin (n + 1))
    (U : Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))
    (a : (ProjectiveSpectrum.Proj.structureSheaf
      (ProjPolyChart.polyGrading R n)).obj.obj (op U)) :
    pderivApp R n j U a = 0 ↔
      ∀ x : U, pderivFiber R n j x.1 (HomogeneousLocalization.val (a.1 x)) = 0 := by
  refine ⟨fun h x => ?_, fun h => Subtype.ext (funext fun x => ?_)⟩
  · simpa using congrFun (Subtype.ext_iff.mp h) x
  · simpa using h x

/-- **`∂ⱼ` annihilates everything that comes from the coefficient ring.** Let `A` be a
localization of `R` and let `ψ : A → S_{(x)}` be a ring homomorphism into the degree-zero
homogeneous localization at `x` which carries the image of `r : R` to the image of the constant
polynomial `r`. Then `∂ⱼ` kills the whole image of `ψ`: the composite is a derivation of `A`
vanishing on the image of `R`, and the denominators of `A` are units. -/
theorem pderivFiber_val_eq_zero_of_isLocalization (j : Fin (n + 1))
    (x : ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n))
    {A : Type*} [CommRing A] [Algebra R A] (p : Submonoid R) [IsLocalization p A]
    (ψ : A →+* HomogeneousLocalization.AtPrime (ProjPolyChart.polyGrading R n)
      x.asHomogeneousIdeal.toIdeal)
    (hψ : ∀ r : R, HomogeneousLocalization.val (ψ (algebraMap R A r)) =
      algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.C r))
    (u : A) :
    pderivFiber R n j x (HomogeneousLocalization.val (ψ u)) = 0 := by
  obtain ⟨⟨c, t⟩, hu⟩ := IsLocalization.surj p u
  have hbase : ∀ r : R,
      pderivFiber R n j x (HomogeneousLocalization.val (ψ (algebraMap R A r))) = 0 := by
    intro r
    rw [hψ r, pderivFiber_algebraMap_C]
  obtain ⟨v, hv⟩ := (IsLocalization.map_units A t).exists_right_inv
  have hunit : IsUnit (HomogeneousLocalization.val (ψ (algebraMap R A (t : R)))) :=
    IsUnit.of_mul_eq_one (HomogeneousLocalization.val (ψ v)) (by
      rw [← HomogeneousLocalization.val_mul, ← map_mul, hv, map_one,
        HomogeneousLocalization.val_one])
  have key : HomogeneousLocalization.val (ψ u) *
      HomogeneousLocalization.val (ψ (algebraMap R A (t : R))) =
      HomogeneousLocalization.val (ψ (algebraMap R A c)) := by
    rw [← HomogeneousLocalization.val_mul, ← map_mul, hu]
  have h := congrArg (pderivFiber R n j x) key
  rw [Derivation.leibniz, hbase (t : R), hbase c, smul_zero, zero_add, smul_eq_mul] at h
  exact hunit.mul_left_cancel (by rw [h, mul_zero])

/-- Projective `n`-space over `R`, as the scheme `Proj` of the total-degree grading. -/
abbrev projSpace : Scheme.{u} := AlgebraicGeometry.Proj (ProjPolyChart.polyGrading R n)

/-- The twist `𝒪(-1)` on `P^n_R`, regarded as a sheaf of modules over the scheme. -/
def twistMinusOne : (projSpace R n).Modules :=
  twistingSheaf (ProjPolyChart.polyGrading R n) (-1)

/-- **`∂/∂Tⱼ` as a derivation of `𝒪_X` with values in `𝒪_X(-1)`**, relative to the constant
presheaf of rings `ℤ`. Its three constituents are the additive maps on sections, the Leibniz
rule, and naturality in the open set; the relative condition is vacuous beyond `∂ⱼ 1 = 0`. -/
def pderivDerivation (j : Fin (n + 1)) :
    PresheafOfModulesOfCommRing.Derivation' (twistMinusOne R n).val
      (AlgebraicGeometry.SheafOfModules.constIntMap (projSpace R n).presheaf) where
  d {W} := pderivApp R n j W.unop
  d_mul {_} a b := pderivApp_mul R n j _ a b
  d_map {_ _} f a := pderivApp_map R n j f a
  d_app {W} a :=
    AlgebraicGeometry.SheafOfModules.constIntMap_app_eq_zero
      (pderivApp R n j W.unop) (pderivApp_one R n j W.unop) a

/-- On sections over `W`, the derivation `pderivDerivation R n j` acts as
`pderivApp R n j W.unop`. -/
@[simp] theorem pderivDerivation_d (j : Fin (n + 1))
    {W : (Opens (ProjectiveSpectrum.top (ProjPolyChart.polyGrading R n)))ᵒᵖ}
    (a : (ProjectiveSpectrum.Proj.structureSheaf
      (ProjPolyChart.polyGrading R n)).obj.obj W) :
    (pderivDerivation R n j).d a = pderivApp R n j W.unop a := rfl

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
