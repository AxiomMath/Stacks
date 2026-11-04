module

public import StacksFrontier.RingTheory.DeRham.LogPolesSequence
public import StacksFrontier.RingTheory.DeRham.PolynomialQuasiIso
public import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham complex of log poles for a divisor

Let `A → R` be a ring map and let `t ∈ R` cut out the effective Cartier divisor
`Y = Spec (R ⧸ (t))` in `X = Spec R`.  Assume the de Rham complex of log poles is defined for
`Y ⊆ X` over `S = Spec A`, which by Stacks Tag 0FMV means that `g ↦ g · dt` is a split injection
`R → Ω[R⁄A]` and that `Ω^p_{R/A}` is `t`-torsion free for every `p`.  Stacks Tag 0FMW constructs
the complex `Ω^•_{X/S}(log Y)` together with the short exact sequence

`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → 0`

and Stacks Tag 0FUA *names* that complex the de Rham complex of log poles for `Y ⊆ X` over `S`.
This file introduces that name, and then proves the fact that entitles the name to its definite
article: the complex depends only on the divisor, not on the local equation chosen to present it.
Two equations of the same divisor differ by a unit, and the two complexes they build are
canonically isomorphic, compatibly with the inclusion of the forms with no pole.

## Main definitions

* `Stacks.LogPoles.deRhamComplexLogPoles`: **the de Rham complex of log poles**
  `Ω^•_{X/S}(log Y)` of Stacks Tag 0FUA, namely the complex constructed in Stacks Tag 0FMW.
* `Stacks.LogPoles.dlogUnit`: the one-form `dlog u = u⁻¹ du` of a unit `u`.
* `Stacks.LogPoles.logComplexUnitIso`: **the canonical isomorphism**
  `Ω^•_{X/S}(log Y)` built from `u · t` to the one built from `t`, for a unit `u`.

## Main results

* `Stacks.LogPoles.shortExact_logPolesSequence`: the named complex is the middle term of the
  short exact sequence of Stacks Tag 0FMW.
* `Stacks.LogPoles.logComplexUnitIso`: the two complexes built from two equations of the same
  principal divisor are canonically isomorphic, and
  `Stacks.LogPoles.logIncl_comp_logComplexUnitHom`: that isomorphism is compatible with the
  inclusion of the forms with no pole, so it identifies the two residue sequences on their
  left-hand terms.
* `Stacks.LogPoles.not_surjective_logIncl_f_succ`: the complex is strictly larger than
  `Ω^•_{X/S}` whenever the divisor carries a nonzero form, so the name "log poles" is not
  vacuous.

## Implementation notes

The complex of Stacks Tag 0FMW is genuine data in the library,
`Stacks.LogPoles.logComplex`, built from the pair model: a form of degree `p + 1` is a pair
`(ω, η)` standing for `ω + dlog t ∧ η`, taken modulo the relations `t ω + dt ∧ η = 0`.  Tag 0FUA
is therefore introduced as a `def` whose body is that complex, not as a predicate and not as an
existence statement; nothing is chosen.

`Stacks.LogPoles.logComplex` needs only the `t`-torsion freeness of the forms, the second
condition of Tag 0FMV, so that is the only hypothesis of
`Stacks.LogPoles.deRhamComplexLogPoles`.  The splitting, the first condition, enters only with
the residue, and so appears only on the statements that mention it.

**Canonicity.**  The source proves the complex independent of the local equation inside the proof
of Tag 0FMW, by observing that `dlog (u t) - dlog t = dlog u` is a section of `Ω_{X/S}`.  In the
pair model that observation becomes an explicit isomorphism: the degree-`p + 1` comparison is
`(ω, η) ↦ (ω + dlog u ∧ η, η)`, which carries the relations for `u t` to the relations for `t`
because `d(u t) = u · dt + t · du`.  It commutes with the differential `(ω, η) ↦ (dω, -dη)`
because `dlog u` is closed, and is the identity on the forms with no pole because those are the
pairs `(ω, 0)`.  Its inverse is the comparison for `u⁻¹`.

The hypotheses are satisfiable: the library establishes both conditions of Tag 0FMV, for a
formally smooth ring map in a tower, in
`Stacks.LogPoles.exists_linearMap_apply_D_eq_one` and
`Stacks.LogPoles.isSMulRegular_exteriorPower_kaehlerDifferential`, and at the scheme level for a
smooth morphism in `AlgebraicGeometry.Scheme.Hom.hasLogPolesDeRhamComplex_of_smooth`.  Those live
in the `StacksDraft.AlgebraicGeometry.DeRham.LogPoles` tree, which is downstream of this file, so
they are cited rather than imported.

The two complexes have the *same* residue target only up to the equality of ideals
`(u t) = (t)`; the quotients `R ⧸ (u t)` and `R ⧸ (t)` are equal ideals but not the same term, so
compatibility with the residue is not stated here, where it would be an equality between maps
into two different types.  The inclusion, whose source is `Ω^•_{X/S}` for both equations, carries
no such transport, and it is the half that pins the isomorphism down.

## References

* [Stacks Project, Tag 0FUA](https://stacks.math.columbia.edu/tag/0FUA), the definition
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), the construction
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), the hypothesis
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace Stacks.LogPoles

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-! ### The de Rham complex of log poles -/

/-- **Stacks Project, Tag 0FUA.**  **The de Rham complex of log poles**
`Ω^•_{X/S}(log Y)` for an effective Cartier divisor `Y = Spec (R ⧸ (t))` in `X = Spec R` over
`S = Spec A`: the complex constructed in Stacks Tag 0FMW, namely `Stacks.LogPoles.logComplex`.
A form of degree `p + 1` is a pair `(ω, η)` standing for `ω + dlog t ∧ η`, taken modulo the
relations `t ω + dt ∧ η = 0`, and the differential is `(ω, η) ↦ (dω, -dη)`. -/
@[stacks 0FUA "the de Rham complex of log poles is the complex constructed in 0FMW; as 0FMW is \
formalized in its affine local form, this names that complex, for a principal divisor (t)"]
def deRhamComplexLogPoles {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  logComplex ht

/-- The de Rham complex of log poles is the complex constructed in Stacks Tag 0FMW. -/
theorem deRhamComplexLogPoles_eq {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    deRhamComplexLogPoles ht = logComplex ht := rfl

/-- The degree-`p` term of the de Rham complex of log poles: the functions in degree zero, and
in degree `p + 1` the pair model of the forms `ω + dlog t ∧ η`. -/
@[simp]
theorem deRhamComplexLogPoles_X {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ) :
    (deRhamComplexLogPoles ht).X p = logFormsX A t p := rfl

/-- The differential of the de Rham complex of log poles is `(ω, η) ↦ (dω, -dη)`. -/
@[simp]
theorem deRhamComplexLogPoles_d {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ) :
    (deRhamComplexLogPoles ht).d p (p + 1) = logFormsD ht p :=
  logComplex_d ht p

/-- **The de Rham complex of log poles sits in the short exact sequence of Stacks Tag 0FMW**
`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → 0`, between the forms with no pole and the
forms on the divisor.  This is what entitles the complex to its name. -/
theorem shortExact_logPolesSequence {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id) :
    (ShortComplex.mk (X₁ := deRhamComplex A R) (X₂ := deRhamComplexLogPoles ht)
      (logIncl ht) (logResidue ht hsplit) (logIncl_comp_logResidue ht hsplit)).ShortExact :=
  shortExact_logShortComplex ht hsplit

/-! ### Non-vacuity: the complex is strictly larger than the forms with no pole -/

/-- **The de Rham complex of log poles genuinely has poles.**  If the divisor carries a nonzero
`p`-form then the inclusion `Ω^{p+1}_{X/S} → Ω^{p+1}_{X/S}(log Y)` is not surjective: the residue
is onto `Ω^p_{Y/S}` and kills the forms with no pole. -/
theorem not_surjective_logIncl_f_succ {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hsplit : ∃ r : Ω[R⁄A] →ₗ[R] R,
      r ∘ₗ LinearMap.toSpanSingleton R Ω[R⁄A] (KaehlerDifferential.D A R t) = LinearMap.id)
    (p : ℕ) (hne : ∃ ζ : ⋀[R ⧸ Ideal.span {t}]^p (Ω[(R ⧸ Ideal.span {t})⁄A]), ζ ≠ 0) :
    ¬ Function.Surjective ((logIncl ht).f (p + 1)).hom := by
  obtain ⟨ζ, hζ⟩ := hne
  intro hsurj
  obtain ⟨x, hx⟩ := surjective_logResidue_f_succ ht hsplit p ζ
  obtain ⟨ω, hω⟩ := hsurj x
  obtain ⟨ω, rfl⟩ : ∃ y : ⋀[R]^(p + 1) (Ω[R⁄A]), y = ω := ⟨ω, rfl⟩
  have h := congrArg (fun z => ((logResidue ht hsplit).f (p + 1)).hom z) hω
  rw [hx] at h
  have hzero : ((logResidue ht hsplit).f (p + 1)).hom
      (((logIncl ht).f (p + 1)).hom ω) = 0 := by
    rw [logIncl_f, logResidue_f, logInclF_succ_apply, logResidueF_succ_apply]
    exact map_zero _
  exact hζ (h.symm.trans hzero)

/-! ### `dlog` of a unit -/

/-- The one-form `dlog u = u⁻¹ du` of a unit `u` of `R`.  It is the difference
`dlog (u t) - dlog t` of the logarithmic differentials of two equations of the same divisor, and
unlike those it is a form with no pole. -/
def dlogUnit (A : Type u) [CommRing A] [Algebra A R] (u : Rˣ) : Ω[R⁄A] :=
  (↑u⁻¹ : R) • KaehlerDifferential.D A R (u : R)

/-- Leibniz rule for `u⁻¹ * u = 1`: `u⁻¹ du + u d(u⁻¹) = 0`. -/
private theorem inv_smul_D_add_smul_D_inv (u : Rˣ) :
    (↑u⁻¹ : R) • KaehlerDifferential.D A R (u : R) +
      (u : R) • KaehlerDifferential.D A R (↑u⁻¹ : R) = 0 := by
  have h := (KaehlerDifferential.D A R).leibniz (↑u⁻¹ : R) (u : R)
  rw [u.inv_mul, (KaehlerDifferential.D A R).map_one_eq_zero] at h
  exact h.symm

/-- `dlog u` is closed in the strong sense that wedging with it twice is zero, which is what the
compatibility of the comparison with the differential needs. -/
theorem wedgeLeft_dlogUnit_wedgeLeft_D (u : Rˣ) (p : ℕ) (ξ : ⋀[R]^p (Ω[R⁄A])) :
    exteriorPower.wedgeLeft (KaehlerDifferential.D A R (↑u⁻¹ : R)) (p + 1)
        (exteriorPower.wedgeLeft (KaehlerDifferential.D A R (u : R)) p ξ) = 0 := by
  have h0 := inv_smul_D_add_smul_D_inv (A := A) u
  have h1 : (u : R) • KaehlerDifferential.D A R (↑u⁻¹ : R) =
      -((↑u⁻¹ : R) • KaehlerDifferential.D A R (u : R)) := by
    rwa [eq_neg_iff_add_eq_zero, add_comm]
  have h2 := congrArg (fun z : Ω[R⁄A] => (↑u⁻¹ : R) • z) h1
  simp only [smul_smul, smul_neg] at h2
  rw [u.inv_mul, one_smul] at h2
  have hinv : KaehlerDifferential.D A R (↑u⁻¹ : R) =
      (-((↑u⁻¹ : R) * (↑u⁻¹ : R))) • KaehlerDifferential.D A R (u : R) := by
    rwa [neg_smul]
  rw [hinv, exteriorPower.wedgeLeft_smul, LinearMap.smul_apply,
    exteriorPower.wedgeLeft_wedgeLeft_apply, smul_zero]

/-- **The de Rham differential anticommutes with `dlog u ∧ ·`** for a unit `u`.  This is the
Leibniz rule for the closed one-form `dlog u`, deduced from the rule for the exact one-form `du`
together with `dlog u ∧ dlog u = 0`. -/
theorem deRhamDifferential_wedgeLeft_dlogUnit (u : Rˣ) (p : ℕ) (ξ : ⋀[R]^p (Ω[R⁄A])) :
    deRhamDifferential (A := A) (p + 1)
        (exteriorPower.wedgeLeft (dlogUnit A u) p ξ) =
      -exteriorPower.wedgeLeft (dlogUnit A u) (p + 1) (deRhamDifferential (A := A) p ξ) := by
  rw [dlogUnit, exteriorPower.wedgeLeft_smul, LinearMap.smul_apply,
    deRhamDifferential_smul, wedgeLeft_dlogUnit_wedgeLeft_D, zero_add,
    deRhamDifferential_wedgeLeft_D, exteriorPower.wedgeLeft_smul, LinearMap.smul_apply,
    smul_neg]

/-! ### The comparison of the pair models of two equations of one divisor -/

/-- The pair-model comparison for a change of local equation by a unit:
`(ω, η) ↦ (ω + dlog u ∧ η, η)`.  It carries the model built from `u · t` to the one built from
`t`, because `ω + dlog (u t) ∧ η = (ω + dlog u ∧ η) + dlog t ∧ η`. -/
def logPairUnit (A : Type u) [CommRing A] [Algebra A R] (u : Rˣ) (p : ℕ) :
    (⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) →ₗ[R]
      (⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :=
  (LinearMap.fst R _ _ +
      (exteriorPower.wedgeLeft (dlogUnit A u) p).comp (LinearMap.snd R _ _)).prod
    (LinearMap.snd R _ _)

/-- The comparison `logPairUnit A u p` sends `(ω, η)` to `(ω + dlog u ∧ η, η)`. -/
@[simp]
theorem logPairUnit_apply (u : Rˣ) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairUnit A u p x =
      (x.1 + exteriorPower.wedgeLeft (dlogUnit A u) p x.2, x.2) := rfl

/-- The comparisons for `u` and for `u⁻¹` are mutually inverse, because
`dlog u + dlog u⁻¹ = dlog 1 = 0`. -/
theorem logPairUnit_logPairUnit (u : Rˣ) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairUnit A u⁻¹ p (logPairUnit A u p x) = x := by
  rw [logPairUnit_apply, logPairUnit_apply]
  refine Prod.ext ?_ rfl
  have hsum : dlogUnit A u + dlogUnit A u⁻¹ = (0 : Ω[R⁄A]) := by
    simp only [dlogUnit, inv_inv]
    exact inv_smul_D_add_smul_D_inv u
  have hz : exteriorPower.wedgeLeft (R := R) (0 : Ω[R⁄A]) p = 0 := by
    have hzz := exteriorPower.wedgeLeft_smul (R := R) (0 : R) (0 : Ω[R⁄A]) p
    rwa [zero_smul, zero_smul] at hzz
  rw [add_assoc, ← LinearMap.add_apply, ← exteriorPower.wedgeLeft_add, hsum, hz,
    LinearMap.zero_apply, add_zero]

/-- **The comparison carries the relations of `u · t` to the relations of `t`.**  If
`(u t) ω + d(u t) ∧ η = 0` then, after dividing by `u` and using `d(u t) = u dt + t du`,
`t (ω + dlog u ∧ η) + dt ∧ η = 0`. -/
theorem logPairUnit_mem_logRel {t s : R} (u : Rˣ) (hs : s = (u : R) * t) (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])}
    (hx : x ∈ logRel A s p) :
    logPairUnit A u p x ∈ logRel A t p := by
  subst hs
  rw [mem_logRel_iff] at hx
  rw [mem_logRel_iff]
  rw [(KaehlerDifferential.D A R).leibniz (u : R) t, exteriorPower.wedgeLeft_add,
    exteriorPower.wedgeLeft_smul, exteriorPower.wedgeLeft_smul] at hx
  have hscaled := congrArg (fun z : ⋀[R]^(p + 1) (Ω[R⁄A]) => (↑u⁻¹ : R) • z) hx
  simp only [smul_add, smul_zero, LinearMap.add_apply, LinearMap.smul_apply, smul_smul] at hscaled
  rw [show (↑u⁻¹ : R) * ((u : R) * t) = t by rw [← mul_assoc, u.inv_mul, one_mul],
    show (↑u⁻¹ : R) * (u : R) = 1 by rw [u.inv_mul], one_smul] at hscaled
  change t • (x.1 + exteriorPower.wedgeLeft (dlogUnit A u) p x.2) +
    exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p x.2 = 0
  have key : t • (x.1 + exteriorPower.wedgeLeft (dlogUnit A u) p x.2) +
        exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p x.2 =
      t • x.1 + (exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p x.2 +
        ((↑u⁻¹ : R) * t) • exteriorPower.wedgeLeft
          (KaehlerDifferential.D A R (u : R)) p x.2) := by
    rw [dlogUnit, exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, smul_add, smul_smul,
      mul_comm t (↑u⁻¹ : R)]
    abel
  exact key.trans hscaled

/-- The comparison in each degree, on the pair model modulo the relations. -/
def logFormsUnitMap {t s : R} (u : Rˣ) (hs : s = (u : R) * t) :
    (p : ℕ) → (logFormsX A s p ⟶ logFormsX A t p)
  | 0 => ModuleCat.ofHom LinearMap.id
  | p + 1 => ModuleCat.ofHom
      (Submodule.mapQ _ _ ((logPairUnit A u p).restrictScalars A)
        fun _ hx ↦ logPairUnit_mem_logRel u hs p hx)

/-- The comparison commutes with the pair-model differential `(ω, η) ↦ (dω, -dη)`, because
`d(dlog u ∧ η) = -dlog u ∧ dη`. -/
theorem logPairD_logPairUnit (u : Rˣ) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairD A p (logPairUnit A u p x) = logPairUnit A u (p + 1) (logPairD A p x) := by
  rw [logPairD_apply, logPairD_apply, logPairUnit_apply, logPairUnit_apply]
  refine Prod.ext ?_ rfl
  simp only [map_add, map_neg]
  rw [deRhamDifferential_wedgeLeft_dlogUnit]

/-- **The comparison is a morphism of complexes** `Ω^•_{X/S}(log Y)` built from `s = u · t` to
the one built from `t`.  It commutes with `(ω, η) ↦ (dω, -dη)` because `dlog u` is closed. -/
def logComplexUnitHom {t s : R} (u : Rˣ) (hs : s = (u : R) * t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) s)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    logComplex hs' ⟶ logComplex ht :=
  CochainComplex.ofHom (logFormsUnitMap u hs) fun p ↦ by
    cases p with
    | zero =>
        ext ω
        obtain ⟨ω, rfl⟩ : ∃ y : ⋀[R]^0 (Ω[R⁄A]), y = ω := ⟨ω, rfl⟩
        have hpair : logPairUnit A u 0
              (deRhamDifferential (A := A) 0 ω, (0 : ⋀[R]^0 (Ω[R⁄A]))) =
            (deRhamDifferential (A := A) 0 ω, (0 : ⋀[R]^0 (Ω[R⁄A]))) := by
          rw [logPairUnit_apply]
          simp
        change ((logComplex ht).d 0 1).hom ((logFormsUnitMap (A := A) u hs 0).hom ω) =
          (logFormsUnitMap (A := A) u hs 1).hom (((logComplex hs').d 0 1).hom ω)
        simp only [logComplex_d]
        exact (congrArg (Submodule.Quotient.mk
          (p := Submodule.restrictScalars A (logRel A t 0))) hpair).symm
    | succ q =>
        ext z
        obtain ⟨z, rfl⟩ : ∃ y : (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) ⧸
            Submodule.restrictScalars A (logRel A s q), y = z := ⟨z, rfl⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        change ((logComplex ht).d (q + 1) (q + 1 + 1)).hom
            ((logFormsUnitMap (A := A) u hs (q + 1)).hom (Submodule.Quotient.mk x)) =
          (logFormsUnitMap (A := A) u hs (q + 1 + 1)).hom
            (((logComplex hs').d (q + 1) (q + 1 + 1)).hom (Submodule.Quotient.mk x))
        simp only [logComplex_d]
        exact congrArg (Submodule.Quotient.mk
          (p := Submodule.restrictScalars A (logRel A t (q + 1)))) (logPairD_logPairUnit u q x)

/-- In degree `p`, the morphism of complexes `logComplexUnitHom u hs hs' ht` is the comparison
`logFormsUnitMap u hs p`. -/
@[simp]
theorem logComplexUnitHom_f {t s : R} (u : Rˣ) (hs : s = (u : R) * t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) s)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ) :
    (logComplexUnitHom u hs hs' ht).f p = logFormsUnitMap u hs p := rfl

/-- **The comparison is compatible with the inclusion of the forms with no pole**: both models
present a form with no pole by the pair `(ω, 0)`, and the comparison fixes those.  This is the
half of the identification of the two residue sequences that needs no transport. -/
theorem logIncl_comp_logComplexUnitHom {t s : R} (u : Rˣ) (hs : s = (u : R) * t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) s)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    logIncl hs' ≫ logComplexUnitHom u hs hs' ht = logIncl ht := by
  ext p : 1
  cases p with
  | zero => rfl
  | succ q =>
      ext ω
      obtain ⟨ω, rfl⟩ : ∃ y : ⋀[R]^(q + 1) (Ω[R⁄A]), y = ω := ⟨ω, rfl⟩
      change (logFormsUnitMap (A := A) u hs (q + 1)).hom ((logInclF hs' (q + 1)).hom ω) =
        (logInclF ht (q + 1)).hom ω
      rw [logInclF_succ_apply, logInclF_succ_apply]
      refine congrArg (Submodule.Quotient.mk
        (p := Submodule.restrictScalars A (logRel A t q))) ?_
      change logPairUnit A u q (ω, (0 : ⋀[R]^q (Ω[R⁄A]))) = (ω, 0)
      rw [logPairUnit_apply]
      simp

/-- `t` is regular on the forms if and only if `u · t` is, for a unit `u`. -/
theorem isSMulRegular_unit_mul_iff (t : R) (u : Rˣ) (p : ℕ) :
    IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) ((u : R) * t) ↔
      IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t := by
  refine ⟨fun h => ?_, ((u.isUnit).isSMulRegular _).mul⟩
  have hmul := ((u⁻¹.isUnit).isSMulRegular (↥(⋀[R]^p (Ω[R⁄A])))).mul h
  rwa [← mul_assoc, u.inv_mul, one_mul] at hmul

/-- **The de Rham complex of log poles depends only on the divisor, not on the equation chosen
to present it.**  Two equations of the same principal divisor differ by a unit, `s = u · t`, and
the complexes they build are canonically isomorphic by `(ω, η) ↦ (ω + dlog u ∧ η, η)`, with
inverse the comparison for `u⁻¹`.  This is the independence of the choice of local equation that
the proof of Stacks Tag 0FMW checks, and it is what entitles Stacks Tag 0FUA to speak of *the*
de Rham complex of log poles. -/
def logComplexUnitIso {t s : R} (u : Rˣ) (hs : s = (u : R) * t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) s)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    logComplex hs' ≅ logComplex ht where
  hom := logComplexUnitHom u hs hs' ht
  inv := logComplexUnitHom u⁻¹
    (by rw [hs, ← mul_assoc, u.inv_mul, one_mul]) ht hs'
  hom_inv_id := by
    ext p : 1
    cases p with
    | zero => rfl
    | succ q =>
        ext z
        obtain ⟨z, rfl⟩ : ∃ y : (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) ⧸
            Submodule.restrictScalars A (logRel A s q), y = z := ⟨z, rfl⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        change Submodule.Quotient.mk
            (p := Submodule.restrictScalars A (logRel A s q))
            (logPairUnit A u⁻¹ q (logPairUnit A u q x)) = Submodule.Quotient.mk x
        exact congrArg (Submodule.Quotient.mk
          (p := Submodule.restrictScalars A (logRel A s q))) (logPairUnit_logPairUnit u q x)
  inv_hom_id := by
    ext p : 1
    cases p with
    | zero => rfl
    | succ q =>
        ext z
        obtain ⟨z, rfl⟩ : ∃ y : (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) ⧸
            Submodule.restrictScalars A (logRel A t q), y = z := ⟨z, rfl⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        change Submodule.Quotient.mk
            (p := Submodule.restrictScalars A (logRel A t q))
            (logPairUnit A u q (logPairUnit A u⁻¹ q x)) = Submodule.Quotient.mk x
        refine congrArg (Submodule.Quotient.mk
          (p := Submodule.restrictScalars A (logRel A t q))) ?_
        have h := logPairUnit_logPairUnit (A := A) u⁻¹ q x
        rwa [inv_inv] at h

end Stacks.LogPoles

end
