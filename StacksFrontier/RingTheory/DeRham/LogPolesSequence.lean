module

public import StacksFrontier.RingTheory.DeRham.LogPolesRestriction
public import StacksFrontier.RingTheory.DeRham.LaurentResidue
public import StacksFrontier.LinearAlgebra.ExteriorPower.KoszulSplitting

/-!
# The residue sequence of the de Rham complex of log poles

Let `A → R` be a ring map and let `t ∈ R` cut out the effective Cartier divisor
`Y = Spec (R ⧸ (t))` in `X = Spec R`. Assume the de Rham complex of log poles is defined for
`Y ⊆ X` over `S = Spec A`, which by Stacks Tag 0FMV means that `g ↦ g · dt` is a split injection
`R → Ω[R⁄A]` and that `Ω^p_{R/A}` is `t`-torsion free for every `p`. This file constructs the
complex `Ω^•_{X/S}(log Y)` of forms with a logarithmic pole along `Y`, the inclusion of the forms
with no pole and the residue, and proves that

`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → 0`

is a short exact sequence of complexes. This is Stacks Tag 0FMW in the affine local case.

## Main definitions

* `Stacks.LogPoles.logRel`: the relations of the pair model, the pairs `(ω, η)` with
  `t ω + dt ∧ η = 0`.
* `Stacks.LogPoles.logComplex`: **the de Rham complex of log poles** `Ω^•_{X/S}(log Y)`.
* `Stacks.LogPoles.logIncl`: the inclusion `Ω^•_{X/S} ⊆ Ω^•_{X/S}(log Y)`.
* `Stacks.LogPoles.logResidue`: the residue `Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1]`.
* `Stacks.LogPoles.logShortComplex`: the three of them assembled as a short complex.

## Main results

* `Stacks.LogPoles.logPairD_mem_logRel`: the relations are stable under `(ω, η) ↦ (dω, -dη)`, so
  the complex has a differential.
* `Stacks.LogPoles.injective_logIncl_f`: the inclusion is injective in every degree.
* `Stacks.LogPoles.surjective_logResidue_f_succ`: the residue is surjective in every positive
  degree.
* `Stacks.LogPoles.shortExact_logShortComplex`: **Stacks Tag 0FMW** in the affine local case, the
  short exactness of the residue sequence of complexes.

## Implementation notes

A form with a logarithmic pole is presented as a pair: `(ω, η)` stands for
`ω + dlog t ∧ η = ω + t⁻¹ dt ∧ η`. Two pairs present the same form exactly when their difference
satisfies `t ω + dt ∧ η = 0`, so the degree-`p + 1` term is
`(Ω^{p+1} × Ω^p) / Stacks.LogPoles.logRel`. No localization of `R` and no module of forms with a
pole is needed to say this, and the differential is then literally `(ω, η) ↦ (dω, -dη)`, whose
square is zero for free; the alternative, realising the complex inside `t⁻¹ Ω^•`, makes the
differential carry a denominator. The sign on the second component is the one the Leibniz rule
forces, `d(dlog t ∧ η) = -dlog t ∧ dη`, and it is the sign that the shift carries by the
convention of Stacks Tag 011G.

The two conditions of Tag 0FMV enter at exactly the two places the source uses them. Torsion
freeness makes the relations `d`-stable and makes the inclusion injective: a pair `(ω, 0)` is a
relation only when `t ω = 0`. The splitting enters through the Koszul contraction against a
retraction of `g ↦ g · dt`, which writes the second component of a relation as a multiple of `t`
plus a form with a factor `dt`, hence inside the kernel of restriction to the divisor computed
in `StacksFrontier.RingTheory.DeRham.LogPolesRestriction`; that is what makes the residue well
defined. The retraction is bound by an existential hypothesis and never chosen in a definition:
the complex, the inclusion and the residue depend only on `t`.

The target of the residue is the shift `Ω^•_{Y/S}[-1]` of `LaurentDeRham.deRhamComplexShift`,
which is zero in degree zero, `Ω^{p}_{Y/S}` in degree `p + 1` and carries the differential `-d`.
The indexing is by `ℕ`, which has no `HasShift`, so the hand-built shift of the residue sequence
of Tag 0FUF is reused.

This is the affine local case, as the attribute says: `X` and `Y` are affine and the divisor is
cut out by a global equation `t`. The sheaf-theoretic statement of Tag 0FMW for an arbitrary
morphism of schemes is not proved here.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), the hypothesis
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF), the residue sequence of
  a Laurent polynomial algebra, whose affine form this one is modelled on
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace Stacks.LogPoles

variable (A : Type u) {R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-! ### The pair model of the forms with a logarithmic pole -/

/-- The `R`-linear map `(ω, η) ↦ t · ω + dt ∧ η` from `Ω^{p+1} × Ω^p` to `Ω^{p+1}`.  A pair
`(ω, η)` stands for the form `ω + dlog t ∧ η` with a logarithmic pole along the divisor `t = 0`,
and this map multiplies that form by `t`, landing it back among the forms with no pole. -/
def logPairMap (t : R) (p : ℕ) :
    (⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) →ₗ[R] ⋀[R]^(p + 1) (Ω[R⁄A]) :=
  t • LinearMap.fst R _ _ +
    (exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p).comp (LinearMap.snd R _ _)

/-- **The relations of the pair model.**  Two pairs present the same form with a logarithmic pole
exactly when their difference satisfies `t ω + dt ∧ η = 0`. -/
def logRel (t : R) (p : ℕ) :
    Submodule R (⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :=
  LinearMap.ker (logPairMap A t p)

/-- A pair `(ω, η)` is a relation exactly when `t ω + dt ∧ η = 0`. -/
theorem mem_logRel_iff (t : R) (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} :
    x ∈ logRel A t p ↔
      t • x.1 + exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p x.2 = 0 :=
  Iff.rfl

variable {A}

/-- For a relation `(ω, η)`, `t ω = -(dt ∧ η)`. -/
private theorem smul_fst_eq_neg_wedgeLeft_snd {t : R} (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} (hx : x ∈ logRel A t p) :
    t • x.1 = -exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p x.2 :=
  eq_neg_iff_add_eq_zero.mpr ((mem_logRel_iff A t p).mp hx)

/-- A relation has a `dt`-free first component: if `t ω + dt ∧ η = 0` then `dt ∧ ω = 0`.  This is
where the `t`-torsion freeness of the forms, the second condition of Stacks Tag 0FMV, enters. -/
theorem wedgeLeft_D_fst_eq_zero_of_mem_logRel {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} (hx : x ∈ logRel A t p) :
    exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) (p + 1) x.1 = 0 := by
  have key : t • exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) (p + 1) x.1 =
      t • (0 : ⋀[R]^(p + 1 + 1) (Ω[R⁄A])) := by
    rw [smul_zero, ← map_smul, smul_fst_eq_neg_wedgeLeft_snd p hx, map_neg,
      exteriorPower.wedgeLeft_wedgeLeft, neg_zero]
  exact ht (p + 1 + 1) key

/-- The differential of the pair model, `(ω, η) ↦ (dω, -dη)`.  The sign is the one forced by the
Leibniz rule, `d(dlog t ∧ η) = -dlog t ∧ dη`, and it is the sign of the shift. -/
def logPairD (A : Type u) {R : Type u} [CommRing A] [CommRing R] [Algebra A R] (p : ℕ) :
    (⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) →ₗ[A]
      (⋀[R]^(p + 1 + 1) (Ω[R⁄A]) × ⋀[R]^(p + 1) (Ω[R⁄A])) :=
  (deRhamDifferential (A := A) (p + 1)).prodMap (-deRhamDifferential (A := A) p)

/-- The differential of the pair model sends `(ω, η)` to `(dω, -dη)`. -/
@[simp]
theorem logPairD_apply (p : ℕ) (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairD A p x =
      (deRhamDifferential (A := A) (p + 1) x.1, -deRhamDifferential (A := A) p x.2) := rfl

/-- **The relations are stable under the differential**, so the differential of the pair model is
well defined.  This is the computation `d(ω + dlog t ∧ η) = dω - dlog t ∧ dη`. -/
theorem logPairD_mem_logRel {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} (hx : x ∈ logRel A t p) :
    logPairD A p x ∈ logRel A t (p + 1) := by
  have hd : deRhamDifferential (A := A) (p + 1)
      (t • x.1 + exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p x.2) = 0 := by
    rw [(mem_logRel_iff A t p).mp hx, map_zero]
  rw [map_add, deRhamDifferential_smul, deRhamDifferential_wedgeLeft_D,
    wedgeLeft_D_fst_eq_zero_of_mem_logRel ht p hx, zero_add] at hd
  rw [mem_logRel_iff, logPairD_apply, map_neg]
  exact hd

/-! ### The de Rham complex of log poles -/

variable (A)

/-- The degree-`p` term of the complex of forms with a logarithmic pole along `t = 0`: the
functions in degree zero, and in degree `p + 1` the pair model `(Ω^{p+1} × Ω^p) / logRel`, whose
elements are the forms `ω + dlog t ∧ η`. -/
def logFormsX (t : R) : ℕ → ModuleCat.{u} A
  | 0 => ModuleCat.of A ↥(⋀[R]^0 (Ω[R⁄A]))
  | p + 1 => ModuleCat.of A ((⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) ⧸
      Submodule.restrictScalars A (logRel A t p))

variable {A}

/-- The differential of the complex of forms with a logarithmic pole. -/
def logFormsD {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    (p : ℕ) → (logFormsX A t p ⟶ logFormsX A t (p + 1))
  | 0 => ModuleCat.ofHom
      ((Submodule.restrictScalars A (logRel A t 0)).mkQ.comp
        ((deRhamDifferential (A := A) 0).prod 0))
  | p + 1 => ModuleCat.ofHom
      (Submodule.mapQ _ _ (logPairD A p) fun _ hx ↦ logPairD_mem_logRel ht p hx)

/-- In degree zero the differential sends a function `ω` to the class of the pair `(dω, 0)`. -/
@[simp]
theorem logFormsD_zero_apply {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (ω : ⋀[R]^0 (Ω[R⁄A])) :
    (logFormsD ht 0).hom ω =
      Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t 0))
        (deRhamDifferential (A := A) 0 ω, 0) := rfl

/-- In degree `p + 1` the differential sends the class of `(ω, η)` to the class of
`(dω, -dη)`. -/
@[simp]
theorem logFormsD_succ_apply {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    (logFormsD ht (p + 1)).hom
        (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t p)) x) =
      Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t (p + 1)))
        (logPairD A p x) := rfl

/-- **The de Rham complex of log poles** `Ω^•_{X/S}(log Y)` of Stacks Tag 0FMW, in its affine
local form: in degree `p + 1` a form is a pair `(ω, η)` standing for `ω + dlog t ∧ η`, taken
modulo the relations `t ω + dt ∧ η = 0`, and the differential is `(ω, η) ↦ (dω, -dη)`. -/
def logComplex {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (logFormsX A t) (logFormsD ht) fun p ↦ by
    cases p with
    | zero =>
        ext ω
        obtain ⟨ω, rfl⟩ : ∃ y : ⋀[R]^0 (Ω[R⁄A]), y = ω := ⟨ω, rfl⟩
        change (logFormsD ht 1).hom ((logFormsD ht 0).hom ω) = 0
        rw [logFormsD_zero_apply, logFormsD_succ_apply]
        refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
        rw [Submodule.restrictScalars_mem, mem_logRel_iff, logPairD_apply]
        simp [deRhamDifferential_comp_self]
    | succ q =>
        ext z
        obtain ⟨z, rfl⟩ : ∃ y : (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) ⧸
            Submodule.restrictScalars A (logRel A t q), y = z := ⟨z, rfl⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        change (logFormsD ht (q + 1 + 1)).hom ((logFormsD ht (q + 1)).hom
          (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x)) = 0
        rw [logFormsD_succ_apply, logFormsD_succ_apply]
        refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
        rw [Submodule.restrictScalars_mem, mem_logRel_iff, logPairD_apply, logPairD_apply]
        simp [deRhamDifferential_comp_self]

/-- The degree-`p` term of `logComplex` is `logFormsX A t p`. -/
@[simp]
theorem logComplex_X {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ) :
    (logComplex ht).X p = logFormsX A t p := rfl

/-- The differential of `logComplex` from degree `p` to degree `p + 1` is `logFormsD`. -/
@[simp]
theorem logComplex_d {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ) :
    (logComplex ht).d p (p + 1) = logFormsD ht p := by
  apply CochainComplex.of_d

/-! ### The inclusion of the forms with no pole -/

/-- The degreewise inclusion of the forms with no pole: `ω ↦ (ω, 0)`. -/
def logInclF {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    (p : ℕ) → ((deRhamComplex A R).X p ⟶ (logComplex ht).X p)
  | 0 => ModuleCat.ofHom LinearMap.id
  | p + 1 => ModuleCat.ofHom
      ((Submodule.restrictScalars A (logRel A t p)).mkQ.comp (LinearMap.inl A _ _))

/-- In degree `p + 1` the inclusion sends a form `ω` to the class of the pair `(ω, 0)`. -/
@[simp]
theorem logInclF_succ_apply {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ)
    (ω : ⋀[R]^(p + 1) (Ω[R⁄A])) :
    (logInclF ht (p + 1)).hom ω =
      Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t p)) (ω, 0) := rfl

/-- **The inclusion `Ω^•_{X/S} ⊆ Ω^•_{X/S}(log Y)`**: a form with no pole is the pair
`(ω, 0)`. -/
def logIncl {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    deRhamComplex A R ⟶ logComplex ht :=
  CochainComplex.ofHom (logInclF ht) fun p ↦ by
    cases p with
    | zero =>
        ext ω
        obtain ⟨ω, rfl⟩ : ∃ y : ⋀[R]^0 (Ω[R⁄A]), y = ω := ⟨ω, rfl⟩
        change ((logComplex ht).d 0 1).hom ((logInclF ht 0).hom ω) =
          (logInclF ht 1).hom (((deRhamComplex A R).d 0 1).hom ω)
        simp only [logComplex_d, deRhamComplex_d]
        rfl
    | succ q =>
        ext ω
        obtain ⟨ω, rfl⟩ : ∃ y : ⋀[R]^(q + 1) (Ω[R⁄A]), y = ω := ⟨ω, rfl⟩
        change ((logComplex ht).d (q + 1) (q + 1 + 1)).hom ((logInclF ht (q + 1)).hom ω) =
          (logInclF ht (q + 1 + 1)).hom (((deRhamComplex A R).d (q + 1) (q + 1 + 1)).hom ω)
        simp only [logComplex_d, deRhamComplex_d]
        have hpair : ((deRhamDifferential (A := A) (q + 1) ω,
              -deRhamDifferential (A := A) q (0 : ⋀[R]^q (Ω[R⁄A]))) :
            ⋀[R]^(q + 1 + 1) (Ω[R⁄A]) × ⋀[R]^(q + 1) (Ω[R⁄A])) =
            (deRhamDifferential (A := A) (q + 1) ω, 0) := by
          rw [map_zero, neg_zero]
        exact congrArg (Submodule.Quotient.mk
          (p := Submodule.restrictScalars A (logRel A t (q + 1)))) hpair

/-- The degree-`p` component of `logIncl` is `logInclF ht p`. -/
@[simp]
theorem logIncl_f {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ) :
    (logIncl ht).f p = logInclF ht p := rfl

/-- The inclusion is injective in every degree: a pair `(ω, 0)` is a relation only when
`t ω = 0`, hence only when `ω = 0` by the `t`-torsion freeness of the forms. -/
theorem injective_logIncl_f {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ) :
    Function.Injective ((logIncl ht).f p).hom := by
  cases p with
  | zero => exact fun a b h ↦ h
  | succ q =>
      intro ω₁ ω₂ h
      obtain ⟨ω₁, rfl⟩ : ∃ y : ⋀[R]^(q + 1) (Ω[R⁄A]), y = ω₁ := ⟨ω₁, rfl⟩
      obtain ⟨ω₂, rfl⟩ : ∃ y : ⋀[R]^(q + 1) (Ω[R⁄A]), y = ω₂ := ⟨ω₂, rfl⟩
      have h' : Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) (ω₁, 0) =
          Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) (ω₂, 0) := h
      rw [Submodule.Quotient.eq, Submodule.restrictScalars_mem, mem_logRel_iff] at h'
      simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, map_zero, add_zero] at h'
      exact sub_eq_zero.mp (ht (q + 1) (show t • (ω₁ - ω₂) = t • 0 by rw [h', smul_zero]))

/-! ### The residue -/

variable (A)

/-- A retraction `r` of `g ↦ g · dt` satisfies `r (dt) = 1`. -/
theorem apply_D_eq_one_of_retraction {t : R} {r : Ω[R⁄A] →ₗ[R] R}
    (hr : r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) =
      LinearMap.id) :
    r (KaehlerDifferential.D A R t) = 1 := by
  have h := DFunLike.congr_fun hr (1 : R)
  simpa [LinearMap.toSpanSingleton_apply] using h

variable {A}

/-- **A relation restricts to zero on the divisor.**  If `t ω + dt ∧ η = 0` then `η` restricts to
zero on `Spec (R ⧸ (t))`: contracting the relation against a retraction of `g ↦ g · dt` writes
`η` as a multiple of `t` plus a form with a factor `dt`.  Both conditions of Stacks Tag 0FMV are
used — the splitting supplies the contraction, the torsion freeness the description of the
kernel of restriction. -/
theorem mapExteriorPower_snd_eq_zero_of_mem_logRel {t : R}
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (p : ℕ) {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} (hx : x ∈ logRel A t p) :
    KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) p x.2 = 0 := by
  obtain ⟨r, hr⟩ := hsplit
  have hr1 : r (KaehlerDifferential.D A R t) = 1 := apply_D_eq_one_of_retraction A hr
  have h := neg_eq_iff_eq_neg.mp (smul_fst_eq_neg_wedgeLeft_snd p hx).symm
  rw [← LinearMap.mem_ker]
  cases p with
  | zero =>
      rw [ker_mapExteriorPower_quotient_zero]
      have hid := DFunLike.congr_fun
        (exteriorPower.contraction_comp_wedgeLeft_zero r (KaehlerDifferential.D A R t)) x.2
      rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        hr1, one_smul, h, map_neg, map_smul] at hid
      rw [← hid]
      exact Submodule.neg_mem _
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top)
  | succ q =>
      rw [ker_mapExteriorPower_quotient_succ, logSubmodule_span_singleton]
      have hid := exteriorPower.contraction_wedgeLeft_add_wedgeLeft_contraction_eq_self r
        (KaehlerDifferential.D A R t) hr1 q x.2
      rw [← hid, h, map_neg, map_smul]
      exact Submodule.add_mem _
        (Submodule.mem_sup_right (Submodule.neg_mem _
          (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top)))
        (Submodule.mem_sup_left ⟨_, rfl⟩)

/-- **The residue**, degreewise: zero in degree zero and `(ω, η) ↦ η|_Y` in degree `p + 1`. -/
def logResidueF {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    (p : ℕ) → ((logComplex ht).X p ⟶
      (LaurentDeRham.deRhamComplexShift A (R ⧸ Ideal.span {t})).X p)
  | 0 => 0
  | p + 1 => ModuleCat.ofHom
      (Submodule.liftQ _
        (((KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t})
            p).restrictScalars A).comp (LinearMap.snd A _ _))
        fun _ hx ↦ mapExteriorPower_snd_eq_zero_of_mem_logRel hsplit p hx)

/-- In degree `p + 1` the residue sends the class of `(ω, η)` to the restriction `η|_Y`. -/
@[simp]
theorem logResidueF_succ_apply {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (p : ℕ) (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    (logResidueF ht hsplit (p + 1)).hom
        (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t p)) x) =
      KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) p x.2 := rfl

/-- **The residue as a map of complexes** `Res : Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1]`.  It
intertwines `(ω, η) ↦ (dω, -dη)` with the differential `-d` of the shift, the sign convention of
Stacks Tag 011G. -/
def logResidue {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    logComplex ht ⟶ LaurentDeRham.deRhamComplexShift A (R ⧸ Ideal.span {t}) where
  f := logResidueF ht hsplit
  comm' := by
    rintro i j (rfl : i + 1 = j)
    cases i with
    | zero =>
        have hl : logResidueF ht hsplit 0 ≫
            (LaurentDeRham.deRhamComplexShift A (R ⧸ Ideal.span {t})).d 0 1 = 0 := by
          rw [LaurentDeRham.deRhamComplexShift_d_zero, Limits.comp_zero]
        have hr : (logComplex ht).d 0 1 ≫ logResidueF ht hsplit 1 = 0 := by
          ext ω
          obtain ⟨ω, rfl⟩ : ∃ y : ⋀[R]^0 (Ω[R⁄A]), y = ω := ⟨ω, rfl⟩
          change (logResidueF ht hsplit 1).hom (((logComplex ht).d 0 1).hom ω) = 0
          rw [logComplex_d]
          have key : KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) 0
              (0 : ⋀[R]^0 (Ω[R⁄A])) = 0 := map_zero _
          exact key
        rw [hl, hr]
    | succ q =>
        ext z
        obtain ⟨z, rfl⟩ : ∃ y : (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) ⧸
            Submodule.restrictScalars A (logRel A t q), y = z := ⟨z, rfl⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        change ((LaurentDeRham.deRhamComplexShift A (R ⧸ Ideal.span {t})).d (q + 1)
                (q + 1 + 1)).hom ((logResidueF ht hsplit (q + 1)).hom
              (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x)) =
          (logResidueF ht hsplit (q + 1 + 1)).hom (((logComplex ht).d (q + 1)
            (q + 1 + 1)).hom
              (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x))
        rw [LaurentDeRham.deRhamComplexShift_d_succ, logComplex_d]
        have key : KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) (q + 1)
              (-deRhamDifferential (A := A) q x.2) =
            -deRhamDifferential (A := A) q
              (KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) q x.2) := by
          rw [map_neg, KaehlerDifferential.mapExteriorPower_deRhamDifferential]
        exact key.symm

/-- The degree-`p` component of `logResidue` is `logResidueF ht hsplit p`. -/
@[simp]
theorem logResidue_f {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (p : ℕ) : (logResidue ht hsplit).f p = logResidueF ht hsplit p := rfl

/-- The residue is surjective in every positive degree: the pair `(0, η)` has residue `η|_Y`, and
every form on the divisor is a restriction. -/
theorem surjective_logResidue_f_succ {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (p : ℕ) : Function.Surjective ((logResidue ht hsplit).f (p + 1)).hom := by
  intro ζ
  obtain ⟨η, hη⟩ := surjective_mapExteriorPower_quotient (A := A) (Ideal.span {t}) p ζ
  refine ⟨Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t p)) (0, η), ?_⟩
  show (logResidueF ht hsplit (p + 1)).hom
      (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t p)) (0, η)) = ζ
  rw [logResidueF_succ_apply]
  exact hη

/-- The residue kills the forms with no pole. -/
theorem logIncl_comp_logResidue {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    logIncl ht ≫ logResidue ht hsplit = 0 := by
  ext p : 1
  cases p with
  | zero => exact (Limits.isZero_zero (ModuleCat.{u} A)).eq_of_tgt _ _
  | succ q =>
      ext
      exact map_zero (KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) q)

/-! ### The short exact sequence -/

/-- **The residue sequence of log poles**, as a short complex of cochain complexes:
`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → 0`. -/
def logShortComplex {t : R} (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℕ) :=
  ShortComplex.mk (logIncl ht) (logResidue ht hsplit) (logIncl_comp_logResidue ht hsplit)

/-- The residue sequence of log poles is short exact in every degree. -/
theorem shortExact_map_eval_logShortComplex {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (p : ℕ) :
    ((logShortComplex ht hsplit).map
      (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℕ) p)).ShortExact := by
  cases p with
  | zero =>
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · rw [ShortComplex.moduleCat_exact_iff]
        intro x _
        exact ⟨x, rfl⟩
      · exact (ModuleCat.mono_iff_injective _).mpr (injective_logIncl_f ht 0)
      · exact ⟨fun g h _ ↦ (Limits.isZero_zero (ModuleCat.{u} A)).eq_of_src g h⟩
  | succ q =>
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · rw [ShortComplex.moduleCat_exact_iff]
        intro z hz
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        have hres : KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) q x.2 = 0 := by
          rw [← logResidueF_succ_apply ht hsplit q x]
          exact hz
        obtain ⟨y, hy⟩ :=
          exists_smul_wedgeLeft_D_of_mapExteriorPower_eq_zero (A := A) t q hres
        refine ⟨x.1 + y, ?_⟩
        show Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q))
            (x.1 + y, 0) = Submodule.Quotient.mk x
        rw [Submodule.Quotient.eq, Submodule.restrictScalars_mem, mem_logRel_iff]
        simp only [Prod.fst_sub, Prod.snd_sub, add_sub_cancel_left, zero_sub, map_neg, hy]
        rw [add_neg_cancel]
      · exact (ModuleCat.mono_iff_injective _).mpr (injective_logIncl_f ht (q + 1))
      · exact (ModuleCat.epi_iff_surjective _).mpr (surjective_logResidue_f_succ ht hsplit q)

/-- **Stacks Project, Tag 0FMW**, in its affine local form.  Let `A → R` be a ring map and let
`t ∈ R` cut out the effective Cartier divisor `Y = Spec (R ⧸ (t))` in `X = Spec R`.  Assume the
de Rham complex of log poles is defined for `Y ⊆ X` over `S = Spec A`, that is: `g ↦ g · dt` is a
split injection `R → Ω[R⁄A]` and `Ω^p_{R/A}` is `t`-torsion free for every `p`.  Then there is a
canonical short exact sequence of complexes
`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → 0`,
given by the inclusion of the forms with no pole and by the residue. -/
@[stacks 0FMW "the affine local case: the residue short exact sequence of complexes \
for a principal effective Cartier divisor"]
theorem shortExact_logShortComplex {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    (logShortComplex ht hsplit).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (shortExact_map_eval_logShortComplex ht hsplit)

end Stacks.LogPoles

end
