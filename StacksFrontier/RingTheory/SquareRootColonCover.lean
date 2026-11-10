module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.ModuleQuadraticExtension

@[expose] public section

/-!
# The integral cover of an affine scheme on which a germ becomes a square

Let `R` be a commutative ring, `a b : R`. This file builds a commutative `R`-algebra

```
Cover a b = (R ⧸ Γ(b) ⊕ ((b) : a)) × R ⧸ (b)
```

— the quadratic extension `Stacks.ModuleQuadraticExtension.Ext` of `R ⧸ Γ(b)` by the colon ideal
`((b) : a)`, times the quotient `R ⧸ (b)` — which is **integral** over `R`, whose spectrum
**surjects** onto `Spec R`, and in which `a * b` is a **square**. Here `Γ(b)` is the kernel of
`R ⟶ R_b`, the ideal cutting out the closure of `D(b)`; `b` is a nonzerodivisor in `R ⧸ Γ(b)`, so
"multiplication by `a / b`" is a well-defined `R ⧸ Γ(b)`-linear map on the colon ideal.

Consequently, if `𝔭` is a prime of `R` and `u = a / b` is an element of the local ring `R_𝔭`
(every element of `R_𝔭` is of that form, with `b ∉ 𝔭`), then at **every** prime `Q` of
`Cover a b` lying over `𝔭` the image of `u` in the local ring of `Cover a b` at `Q` is a square.

That is the statement

> **(SQ)** for every scheme `S`, every point `x` of `S`, every affine open `Ω ∋ x` and every
> `u ∈ Γ(S, Ω)` there is a surjective integral morphism `A ⟶ S` such that the image of `u` is a
> square in `𝒪_{A, p}` at every point `p` of `A` over `x`

for an **affine** scheme `S`: the pair `(Ω, u)` enters only through the germ of `u` at `x`, which
is an arbitrary element of `𝒪_{S, x} = R_𝔭`.

## Main definitions

* `Stacks.SquareRootCover.colonIdeal`: the colon ideal `((b) : a) = {f | f * a ∈ (b)}`.
* `Stacks.SquareRootCover.mu`: multiplication by `a / b`, as an `R`-linear map from the colon
  ideal to `R`, available once `b` is a nonzerodivisor.
* `Stacks.SquareRootCover.colonDatum`: the resulting
  `Stacks.ModuleQuadraticExtension.QuadraticDatum`.
* `Stacks.SquareRootCover.awayKer`: the kernel `Γ(b)` of `R ⟶ R_b`.
* `Stacks.SquareRootCover.Cover`: the algebra displayed above, with its structure morphism
  `Stacks.SquareRootCover.coverHom`.

## Main results

* `Stacks.SquareRootCover.isSquare_algebraMap_mul_ext` and
  `Stacks.SquareRootCover.isSquare_algebraMap_mul`: `a * b` is a square in the quadratic
  extension, and in the cover.
* `Stacks.SquareRootCover.mk_mem_nonZeroDivisors`: `b` is a nonzerodivisor modulo its own
  `b`-power torsion.
* `Stacks.SquareRootCover.exists_isPrime_comap_eq`: every prime of `R` is the contraction of a
  prime of `Cover a b`; equivalently `Spec (Cover a b) ⟶ Spec R` is surjective.
* `Stacks.SquareRootCover.instIsIntegralCover`: `Cover a b` is integral over `R`.
* `Stacks.SquareRootCover.isSquare_localRingHom`: the local statement — the image of `a / b` in
  the local ring of `Cover a b` at a prime over `𝔭` is a square.
* `Stacks.SquareRootCover.exists_isIntegral_surjective_isSquare`: **(SQ) for an affine base**,
  in ring-theoretic form: for every element `u` of `R_𝔭` there is an integral `R`-algebra with
  surjective spectrum in whose local ring at every prime over `𝔭` the image of `u` is a square.

## References

* [Stacks Project, Tag 0CNZ](https://stacks.math.columbia.edu/tag/0CNZ)
* [Stacks Project, Tag 0CNX](https://stacks.math.columbia.edu/tag/0CNX)
-/

open Stacks.ModuleQuadraticExtension
open scoped nonZeroDivisors

universe u

namespace Stacks.SquareRootCover

variable {R : Type u} [CommRing R]

/-! ### The colon ideal and division by a nonzerodivisor -/

/-- The colon ideal `((b) : a) = {f | f * a ∈ (b)}`. -/
def colonIdeal (a b : R) : Ideal R := (Ideal.span {b}).colon {a}

/-- Membership in the colon ideal: `f` is a denominator of `a / b` exactly when `f * a` is a
multiple of `b`. -/
theorem mem_colonIdeal_iff {a b f : R} : f ∈ colonIdeal a b ↔ ∃ c : R, b * c = f * a := by
  rw [colonIdeal, Submodule.mem_colon_singleton, Ideal.mem_span_singleton', smul_eq_mul]
  exact ⟨fun ⟨c, hc⟩ ↦ ⟨c, by linear_combination hc⟩, fun ⟨c, hc⟩ ↦ ⟨c, by linear_combination hc⟩⟩

/-- The denominator `b` itself lies in `((b) : a)`. -/
theorem self_mem_colonIdeal (a b : R) : b ∈ colonIdeal a b :=
  mem_colonIdeal_iff.mpr ⟨a, rfl⟩

/-- Cancelling a nonzerodivisor on the left. -/
theorem mul_left_cancel_of_mem_nonZeroDivisors {b : R} (hb : b ∈ R⁰) {x y : R}
    (h : b * x = b * y) : x = y := by
  refine sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hb).1 (x - y) ?_)
  rw [mul_sub, h, sub_self]

/-- The quotient `f * a / b` of an element `f` of the colon ideal `((b) : a)`, chosen by the
defining property; it is unique as soon as `b` is a nonzerodivisor. -/
noncomputable def quot {a b : R} (f : colonIdeal a b) : R :=
  (mem_colonIdeal_iff.mp f.2).choose

/-- The defining property of `quot`: `b * quot f = f * a`. -/
theorem mul_quot {a b : R} (f : colonIdeal a b) : b * quot f = (f : R) * a :=
  (mem_colonIdeal_iff.mp f.2).choose_spec

/-- **Multiplication by `a / b`.** For `b` a nonzerodivisor, the `R`-linear map on the colon
ideal `((b) : a)` sending `f` to the unique `c` with `b * c = f * a`. -/
noncomputable def mu {a b : R} (hb : b ∈ R⁰) : colonIdeal a b →ₗ[R] R where
  toFun := quot
  map_add' f g := by
    refine mul_left_cancel_of_mem_nonZeroDivisors hb ?_
    have hc : ((f + g : colonIdeal a b) : R) = (f : R) + (g : R) := Submodule.coe_add f g
    linear_combination mul_quot (f + g) - mul_quot f - mul_quot g + a * hc
  map_smul' r f := by
    refine mul_left_cancel_of_mem_nonZeroDivisors hb ?_
    have hc : ((r • f : colonIdeal a b) : R) = r * (f : R) := by
      rw [SetLike.val_smul, smul_eq_mul]
    have hr : ((RingHom.id R) r • quot f) = r * quot f := by
      rw [RingHom.id_apply, smul_eq_mul]
    linear_combination mul_quot (r • f) - r * mul_quot f + a * hc - b * hr

/-- The map `mu hb` sends `f` to `quot f`. -/
theorem mu_apply {a b : R} (hb : b ∈ R⁰) (f : colonIdeal a b) : mu hb f = quot f := rfl

/-- The exchange law for multiplication by `a / b`: both `mu f * g` and `mu g * f` are
`f * g * a / b`. -/
theorem mu_mul_comm {a b : R} (hb : b ∈ R⁰) (f g : colonIdeal a b) :
    mu hb f * (g : R) = mu hb g * (f : R) := by
  refine mul_left_cancel_of_mem_nonZeroDivisors hb ?_
  simp only [mu_apply]
  linear_combination (g : R) * mul_quot f - (f : R) * mul_quot g

/-- The value of `mu` at the denominator `b` is the numerator `a`. -/
theorem mu_self {a b : R} (hb : b ∈ R⁰) :
    mu hb (⟨b, self_mem_colonIdeal a b⟩ : colonIdeal a b) = a := by
  refine mul_left_cancel_of_mem_nonZeroDivisors hb ?_
  rw [mu_apply, mul_quot]

/-- The quadratic datum of the colon ideal: the form `(f, g) ↦ f * g * a / b`. -/
noncomputable def colonDatum (a : R) {b : R} (hb : b ∈ R⁰) :
    QuadraticDatum R (colonIdeal a b) :=
  idealDatum (colonIdeal a b) (mu hb) (mu_mul_comm hb)

/-- **`a * b` is a square in the quadratic extension of `R` by `((b) : a)`.** -/
theorem isSquare_algebraMap_mul_ext (a : R) {b : R} (hb : b ∈ R⁰) :
    IsSquare (algebraMap R (Ext (colonDatum a hb)) (a * b)) :=
  Ext.isSquare_algebraMap_of_form_eq (x := ⟨b, self_mem_colonIdeal a b⟩) <| by
    rw [colonDatum, idealDatum_form, idealForm_apply, mu_self]

/-! ### The `b`-power torsion -/

/-- The `b`-power torsion of `R`: the kernel of the localization map `R ⟶ R_b`, equivalently the
ideal `{x | b ^ n * x = 0 for some n}`, which cuts out the closure of `D(b)` in `Spec R`. -/
def awayKer (b : R) : Ideal R := RingHom.ker (algebraMap R (Localization.Away b))

/-- `x` lies in the `b`-power torsion exactly when `b ^ n * x = 0` for some `n`. -/
theorem mem_awayKer_iff {b x : R} : x ∈ awayKer b ↔ ∃ n : ℕ, b ^ n * x = 0 := by
  rw [awayKer, RingHom.mem_ker,
    IsLocalization.map_eq_zero_iff (Submonoid.powers b) (Localization.Away b)]
  exact ⟨fun ⟨⟨_, n, rfl⟩, hm⟩ ↦ ⟨n, hm⟩, fun ⟨n, hn⟩ ↦ ⟨⟨b ^ n, n, rfl⟩, hn⟩⟩

/-- Every prime not containing `b` contains the `b`-power torsion. -/
theorem awayKer_le_of_notMem {b : R} {𝔮 : Ideal R} (h𝔮 : 𝔮.IsPrime) (hb : b ∉ 𝔮) :
    awayKer b ≤ 𝔮 := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_awayKer_iff.mp hx
  exact (h𝔮.mem_or_mem (hn ▸ 𝔮.zero_mem)).resolve_left fun h ↦ hb (h𝔮.mem_of_pow_mem n h)

/-- **`b` is a nonzerodivisor modulo its own `b`-power torsion.** -/
theorem mk_mem_nonZeroDivisors (b : R) :
    (Ideal.Quotient.mk (awayKer b) b) ∈ (R ⧸ awayKer b)⁰ := by
  have key : ∀ z : R ⧸ awayKer b, (Ideal.Quotient.mk (awayKer b) b) * z = 0 → z = 0 := by
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hz
    obtain ⟨n, hn⟩ := mem_awayKer_iff.mp hz
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (mem_awayKer_iff.mpr ⟨n + 1, ?_⟩)
    rw [pow_succ]
    linear_combination hn
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun z hz ↦ key z (by rw [mul_comm]; exact hz)⟩

/-! ### The cover -/

variable (a b : R)

/-- The quadratic extension of `R ⧸ Γ(b)` by the colon ideal of the image of `a / b` there: the
first factor of `Stacks.SquareRootCover.Cover`. -/
noncomputable abbrev quadraticPart : Type u :=
  Ext (colonDatum (Ideal.Quotient.mk (awayKer b) a) (mk_mem_nonZeroDivisors b))

/-- **The integral cover of `Spec R` on which `a / b` becomes a square.** The product of the
quadratic extension of `R ⧸ Γ(b)` by the colon ideal of `a / b` with `R ⧸ (b)`. -/
noncomputable abbrev Cover : Type u := quadraticPart a b × (R ⧸ Ideal.span {b})

/-- The structure morphism of the cover: `r ↦ (r mod Γ(b), r mod (b))`. -/
noncomputable def coverHom : R →+* Cover a b :=
  RingHom.prod
    ((Ext.inlHom (colonDatum (Ideal.Quotient.mk (awayKer b) a)
      (mk_mem_nonZeroDivisors b))).comp (Ideal.Quotient.mk (awayKer b)))
    (Ideal.Quotient.mk (Ideal.span {b}))

/-- The `R`-algebra structure on the cover given by `coverHom`. -/
noncomputable instance instAlgebraCover : Algebra R (Cover a b) := (coverHom a b).toAlgebra

/-- The algebra map `R → Cover a b` is `coverHom a b`. -/
theorem algebraMap_cover_eq : algebraMap R (Cover a b) = coverHom a b :=
  RingHom.algebraMap_toAlgebra _

/-- The first component of `coverHom a b r` is `(r mod Γ(b), 0)` in the quadratic
extension `quadraticPart a b`. -/
theorem coverHom_fst (r : R) : ((coverHom a b) r).1 =
    Ext.mk (colonDatum (Ideal.Quotient.mk (awayKer b) a) (mk_mem_nonZeroDivisors b))
      (Ideal.Quotient.mk (awayKer b) r) 0 := rfl

/-- The second component of `coverHom a b r` is `r mod (b)`. -/
theorem coverHom_snd (r : R) :
    ((coverHom a b) r).2 = Ideal.Quotient.mk (Ideal.span {b}) r := rfl

/-! ### Integrality -/

/-- A product of two integral ring homomorphisms out of the same ring is integral. -/
theorem _root_.RingHom.IsIntegral.prod {A B : Type*} [CommRing A] [CommRing B]
    {f : R →+* A} {g : R →+* B} (hf : f.IsIntegral) (hg : g.IsIntegral) :
    (f.prod g).IsIntegral := by
  have key : ∀ (y : A × B) (r : Polynomial R), Polynomial.eval₂ (f.prod g) y r
      = (Polynomial.eval₂ f y.1 r, Polynomial.eval₂ g y.2 r) := fun y r ↦ Prod.ext
    (by simpa using Polynomial.hom_eval₂ r (f.prod g) (RingHom.fst A B) y)
    (by simpa using Polynomial.hom_eval₂ r (f.prod g) (RingHom.snd A B) y)
  intro y
  obtain ⟨p, hp, hpy⟩ := hf y.1
  obtain ⟨q, hq, hqy⟩ := hg y.2
  refine ⟨p * q, hp.mul hq, ?_⟩
  rw [key y (p * q), Polynomial.eval₂_mul, Polynomial.eval₂_mul, hpy, hqy, zero_mul, mul_zero]
  rfl

/-- The structure morphism of the cover is integral. -/
theorem isIntegral_coverHom : (coverHom a b).IsIntegral := by
  have h1 : (Ideal.Quotient.mk (awayKer b)).IsIntegral :=
    (Ideal.Quotient.mk (awayKer b)).isIntegral_of_surjective Ideal.Quotient.mk_surjective
  have h2 : (Ext.inlHom (colonDatum (Ideal.Quotient.mk (awayKer b) a)
      (mk_mem_nonZeroDivisors b))).IsIntegral := fun x ↦ Ext.isIntegral_elem x
  have h3 : (Ideal.Quotient.mk (Ideal.span {b})).IsIntegral :=
    (Ideal.Quotient.mk (Ideal.span {b})).isIntegral_of_surjective Ideal.Quotient.mk_surjective
  exact RingHom.IsIntegral.prod (RingHom.IsIntegral.trans _ _ h1 h2) h3

/-- **The cover is integral over `R`.** -/
instance instIsIntegralCover : Algebra.IsIntegral R (Cover a b) :=
  ⟨fun x ↦ by
    have h := isIntegral_coverHom a b x
    rwa [← algebraMap_cover_eq] at h⟩

/-! ### Surjectivity of the spectrum -/

/-- **Every prime of `R` is the contraction of a prime of the cover**; equivalently
`Spec (Cover a b) ⟶ Spec R` is surjective. -/
theorem exists_isPrime_comap_eq (𝔮 : Ideal R) (h𝔮 : 𝔮.IsPrime) :
    ∃ Q : Ideal (Cover a b), Q.IsPrime ∧ Q.comap (algebraMap R (Cover a b)) = 𝔮 := by
  have := h𝔮
  by_cases hb : b ∈ 𝔮
  · have hle : Ideal.span {b} ≤ 𝔮 := (Ideal.span_singleton_le_iff_mem _).mpr hb
    have := Ideal.isPrime_map_quotientMk_of_isPrime hle
    have hPcomap := Ideal.comap_map_mk hle
    refine ⟨Ideal.prod ⊤ (𝔮.map (Ideal.Quotient.mk (Ideal.span {b}))),
      Ideal.isPrime_ideal_prod_top' (h := inferInstance), ?_⟩
    ext r
    rw [Ideal.mem_comap, algebraMap_cover_eq, Ideal.mem_prod, coverHom_snd, ← Ideal.mem_comap,
      hPcomap]
    exact and_iff_right trivial
  · have hle : awayKer b ≤ 𝔮 := awayKer_le_of_notMem h𝔮 hb
    have := Ideal.isPrime_map_quotientMk_of_isPrime hle
    have hPcomap := Ideal.comap_map_mk hle
    obtain ⟨Q₀, hQ₀, hQ₀comap⟩ :=
      Ext.exists_isPrime_comap_eq (d := colonDatum (Ideal.Quotient.mk (awayKer b) a)
        (mk_mem_nonZeroDivisors b)) (𝔮.map (Ideal.Quotient.mk (awayKer b)))
    refine ⟨Ideal.prod Q₀ ⊤, Ideal.isPrime_ideal_prod_top (h := hQ₀), ?_⟩
    ext r
    rw [Ideal.mem_comap, algebraMap_cover_eq, Ideal.mem_prod, coverHom_fst, ← Ext.algebraMap_eq,
      ← Ideal.mem_comap, hQ₀comap, ← Ideal.mem_comap, hPcomap]
    exact and_iff_left trivial

/-! ### The square -/

/-- **`a * b` is a square in the cover.** -/
theorem isSquare_algebraMap_mul : IsSquare (algebraMap R (Cover a b) (a * b)) := by
  obtain ⟨y, hy⟩ := isSquare_algebraMap_mul_ext (Ideal.Quotient.mk (awayKer b) a)
    (mk_mem_nonZeroDivisors b)
  refine ⟨(y, 0), ?_⟩
  rw [algebraMap_cover_eq]
  refine Prod.ext ?_ ?_
  · change ((coverHom a b) (a * b)).1 = y * y
    refine Eq.trans ?_ hy
    rw [Ext.algebraMap_eq, ← map_mul, coverHom_fst]
  · change ((coverHom a b) (a * b)).2 = 0 * 0
    rw [coverHom_snd, mul_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self b)

/-- Dividing a square by a unit twice: if `v * w` is a square and `z` is an inverse of `w`, then
`v * z` is a square. -/
theorem isSquare_mul_of_isSquare_mul_of_mul_eq_one {A : Type*} [CommRing A] {v w z : A}
    (hz : w * z = 1) (h : IsSquare (v * w)) : IsSquare (v * z) := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y * z, by linear_combination z * z * hy - v * z * hz⟩

/-- **The local statement.** Let `𝔭` be a prime of `R` not containing `b`, let `u` be the element
`a / b` of the local ring `R_𝔭` — written here as the relation `a = u * b` there, which is what
`a / b` means — and let `Q` be a prime of the cover lying over `𝔭`. Then the image of `u` in the
local ring of the cover at `Q` is a square. -/
theorem isSquare_localRingHom (𝔭 : Ideal R) [𝔭.IsPrime] (hb : b ∉ 𝔭)
    {u : Localization.AtPrime 𝔭}
    (hu : algebraMap R (Localization.AtPrime 𝔭) a
      = u * algebraMap R (Localization.AtPrime 𝔭) b)
    (Q : Ideal (Cover a b)) [Q.IsPrime] (h : 𝔭 = Q.comap (algebraMap R (Cover a b))) :
    IsSquare (Localization.localRingHom 𝔭 Q (algebraMap R (Cover a b)) h u) := by
  have hbQ : algebraMap R (Cover a b) b ∈ Q.primeCompl := fun hc ↦ hb (by rw [h]; exact hc)
  set g := Localization.localRingHom 𝔭 Q (algebraMap R (Cover a b)) h with hg
  set A := algebraMap (Cover a b) (Localization.AtPrime Q) (algebraMap R (Cover a b) a) with hA
  set B := algebraMap (Cover a b) (Localization.AtPrime Q) (algebraMap R (Cover a b) b) with hB
  have hu' : A = g u * B := by
    simpa only [map_mul, hg, Localization.localRingHom_to_map] using congrArg g hu
  obtain ⟨w, hw⟩ :=
    (IsLocalization.map_units (Localization.AtPrime Q)
      (⟨algebraMap R (Cover a b) b, hbQ⟩ : Q.primeCompl)).exists_right_inv
  have hwB : B * w = 1 := hw
  have hgu : g u = A * w := by rw [hu', mul_assoc, hwB, mul_one]
  have hsq : IsSquare (A * B) := by
    obtain ⟨y, hy⟩ := isSquare_algebraMap_mul a b
    refine ⟨algebraMap (Cover a b) (Localization.AtPrime Q) y, ?_⟩
    rw [hA, hB, ← map_mul, ← map_mul, hy, map_mul]
  rw [hgu]
  exact isSquare_mul_of_isSquare_mul_of_mul_eq_one hwB hsq

/-! ### (SQ) for an affine base -/

/-- **(SQ) for an affine scheme, in ring-theoretic form.** For every commutative ring `R`, every
prime `𝔭` of `R` and every element `u` of the local ring `R_𝔭` there is a commutative
`R`-algebra `T` which is integral over `R`, whose spectrum surjects onto `Spec R`, and such that
at every prime `Q` of `T` lying over `𝔭` the image of `u` in the local ring `T_Q` is a square. -/
theorem exists_isIntegral_surjective_isSquare (R : Type u) [CommRing R] (𝔭 : Ideal R)
    [𝔭.IsPrime] (u : Localization.AtPrime 𝔭) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      (algebraMap R T).IsIntegral ∧
      (∀ 𝔮 : Ideal R, 𝔮.IsPrime →
        ∃ Q : Ideal T, Q.IsPrime ∧ Q.comap (algebraMap R T) = 𝔮) ∧
      ∀ (Q : Ideal T) (_ : Q.IsPrime) (h : 𝔭 = Q.comap (algebraMap R T)),
        IsSquare (Localization.localRingHom 𝔭 Q (algebraMap R T) h u) := by
  obtain ⟨⟨a, s⟩, hu⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl u
  have hu' : algebraMap R (Localization.AtPrime 𝔭) a
      = u * algebraMap R (Localization.AtPrime 𝔭) (s : R) :=
    IsLocalization.mk'_eq_iff_eq_mul.mp hu
  refine ⟨Cover a (s : R), inferInstance, inferInstance, ?_,
    exists_isPrime_comap_eq a (s : R), fun Q hQ h ↦ ?_⟩
  · rw [algebraMap_cover_eq]
    exact isIntegral_coverHom a (s : R)
  · have := hQ
    exact isSquare_localRingHom a (s : R) 𝔭 s.2 hu' Q h

end Stacks.SquareRootCover

end
