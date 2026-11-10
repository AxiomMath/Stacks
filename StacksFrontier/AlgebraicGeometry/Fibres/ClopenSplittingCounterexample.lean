module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.AlgebraicGeometry.Fibres.IdempotentsFromClopenSplitting
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Sections

/-!
# A proper morphism whose fibre splits but whose neighbourhoods do not

[Stacks, Tag 0G7X] says that for a proper morphism `f : X ⟶ S`, a point `s : S` and an
idempotent `e ∈ Γ(X_s, 𝒪_{X_s})`, the element `e` lies in the image of `(f_*𝒪_X)_s`, which is
to say that `e` is the restriction of *some* section of `𝒪_X` over `f ⁻¹ᵁ U` for some open
neighbourhood `U` of `s`. The section produced is not claimed to be idempotent, and the
decomposition of the fibre attached to `e` is not claimed to spread out to a neighbourhood: in
the source's proof the decomposition is spread over the *infinitesimal* neighbourhoods of the
fibre, which have the same underlying space as the fibre itself, and the passage from those to
`(f_*𝒪_X)_s` is the theorem on formal functions.

This file shows that the Zariski-local statement one might hope for instead — that `f ⁻¹ᵁ U`
itself decomposes into two disjoint opens cutting the fibre in `D(e)` and `D(1-e)` — is **false**
for proper morphisms, so it is not a route to Tag 0G7X. The counterexample is the simplest
failure of idempotent lifting over a local ring that is not Henselian:

* `k` is a field with `2 ≠ 0`, `R = k[X]_{(X)}` is the local ring of the affine line at the
  origin, and `S = R[Y]/(Y² - (1+X))`;
* `S` is a free `R`-module of rank `2`, so `g : Spec S ⟶ Spec R` is finite, hence proper;
* `1 + X` is not a square in `R` — a square root would force a degree parity `2d = 2e + 1` — so
  `S` has no idempotents other than `0` and `1` and `Spec S` admits no nontrivial decomposition
  into two disjoint opens;
* `1 + X` becomes `1` in the residue field, which has the two distinct square roots `±1`, so the
  closed fibre has two points, and being the fibre of a finite morphism it is discrete. A
  one-point open of it carries an idempotent `c` with `D(c)` neither empty nor everything;
* the only open neighbourhood of the closed point of `Spec R` is `Spec R` itself, so a splitting
  of `g ⁻¹ᵁ U` would be a splitting of `Spec S`, and there is none.

## Main results

* `Stacks.AlgebraicGeometry.Fibres.exists_isIdempotentElem_not_clopenSplitting`: the geometric
  criterion. Over a base point whose only open neighbourhood is everything, a scheme with no
  idempotent sections but `0` and `1` and with a discrete fibre of at least two points carries an
  idempotent on that fibre admitting no splitting of the preimage of a neighbourhood.
* `Stacks.AlgebraicGeometry.Fibres.isIdempotentElem_adjoinRoot_quadratic`: over a domain, the only
  idempotents of `R[Y]/(Y² - u)` are `0` and `1` as soon as `u` is not a square in `R`.
* `Stacks.AlgebraicGeometry.Fibres.not_clopenSplitting` and
  `Stacks.AlgebraicGeometry.Fibres.not_forall_exists_clopenSplitting_of_isProper`: **the
  refutation.** There is no such splitting for every proper morphism, every point of the base and
  every idempotent on the fibre.

## References

* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X): the theorem about the
  image of `(f_*𝒪_X)_s`, which the refuted statement is not a route to.
* [Stacks Project, Tag 04GE](https://stacks.math.columbia.edu/tag/04GE): lifting idempotents along
  a finite algebra over a local ring is exactly the Henselian property, which `k[X]_{(X)}` does
  not have.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Fibres

/-! ### The geometric criterion -/

/-- **A decomposition of a scheme into two disjoint opens is cut out by an idempotent global
section.** If `V₁` and `V₂` are disjoint opens covering `X`, some idempotent `a ∈ Γ(X, 𝒪_X)` has
nonvanishing locus `V₁`: by
`Stacks.AlgebraicGeometry.ProperGeomConnected.bijective_piRestrict` there is a global section
restricting to `1` on `V₁` and to `0` on `V₂`, it is idempotent because `a * a` has the same
restrictions, and its nonvanishing locus contains `V₁`, misses `V₂` and lies in `V₁ ⊔ V₂`. -/
private theorem exists_isIdempotentElem_basicOpen_eq_of_top_le_sup {X : Scheme.{u}}
    {V₁ V₂ : X.Opens} (hcover : ⊤ ≤ V₁ ⊔ V₂) (hdisj : V₁ ⊓ V₂ = ⊥) :
    ∃ a : Γ(X, ⊤), IsIdempotentElem a ∧ X.basicOpen a = V₁ := by
  let V : ULift.{u} Bool → X.Opens := fun b ↦ bif b.down then V₁ else V₂
  have hcover' : ⊤ ≤ ⨆ b, V b :=
    hcover.trans (sup_le (le_iSup V ⟨true⟩) (le_iSup V ⟨false⟩))
  have hdisj' : ∀ i j, i ≠ j → V i ⊓ V j = ⊥ := by
    rintro ⟨i⟩ ⟨j⟩ hij
    cases i <;> cases j
    · exact absurd rfl hij
    · change V₂ ⊓ V₁ = ⊥
      rw [inf_comm]
      exact hdisj
    · exact hdisj
    · exact absurd rfl hij
  have hbij := ProperGeomConnected.bijective_piRestrict V hcover' hdisj'
  obtain ⟨a, ha⟩ := hbij.2 fun b ↦ bif b.down then (1 : Γ(X, V b)) else 0
  have hres : ∀ b, X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op a =
      bif b.down then (1 : Γ(X, V b)) else 0 := fun b ↦ congrFun ha b
  refine ⟨a, hbij.1 ?_, ?_⟩
  · rw [map_mul, ha]
    funext b
    rcases b with ⟨_ | _⟩
    · exact mul_zero _
    · exact mul_one _
  · have hb : ∀ b, X.basicOpen (bif b.down then (1 : Γ(X, V b)) else 0) =
        V b ⊓ X.basicOpen a := fun b ↦ by
      rw [← hres b]
      exact Scheme.basicOpen_res X a _
    have e₁ := hb ⟨true⟩
    have e₂ := hb ⟨false⟩
    change X.basicOpen (1 : Γ(X, V₁)) = _ at e₁
    change X.basicOpen (0 : Γ(X, V₂)) = _ at e₂
    rw [Scheme.basicOpen_one] at e₁
    rw [Scheme.basicOpen_zero, inf_comm] at e₂
    exact le_antisymm
      (Disjoint.left_le_of_le_sup_right (le_top.trans hcover) (disjoint_iff.mpr e₂.symm))
      (inf_eq_left.mp e₁.symm)

/-- **A fibre idempotent with no splitting of a neighbourhood.** Let `g : Y ⟶ T` be a morphism
and `t : T` a point whose only open neighbourhood is `⊤` — the closed point of the spectrum of a
local ring, say. Assume that the only idempotents of `Γ(Y, 𝒪_Y)` are `0` and `1`, that the fibre
`Y_t` is discrete, and that it has two distinct points. Then some idempotent `c` of
`Γ(Y_t, 𝒪_{Y_t})` admits no decomposition of `g ⁻¹ᵁ U`, for any neighbourhood `U` of `t`, into
two disjoint opens the first of which meets the fibre exactly in `D(c)`.

Indeed the two opens `{x₁}` and its complement decompose the discrete fibre disjointly, so by
`Stacks.AlgebraicGeometry.Fibres.exists_isIdempotentElem_basicOpen_eq_of_top_le_sup` they come
from an idempotent `c` with `D(c) = {x₁}`, which contains `x₁` and misses `x₂`. A splitting of
`g ⁻¹ᵁ U = Y` would likewise come from an idempotent of `Γ(Y, 𝒪_Y)`, hence from `0` or `1`, so
its first member would be `⊥` or `⊤` and would meet the fibre in `⊥` or `⊤`. -/
theorem exists_isIdempotentElem_not_clopenSplitting {Y T : Scheme.{u}} (g : Y ⟶ T) (t : T)
    (hconn : ∀ a : Γ(Y, ⊤), IsIdempotentElem a → a = 0 ∨ a = 1)
    (htop : ∀ U : T.Opens, t ∈ U → U = ⊤)
    [DiscreteTopology (g.fiber t)] {x₁ x₂ : g.fiber t} (hx : x₁ ≠ x₂) :
    ∃ c : Γ(g.fiber t, ⊤), IsIdempotentElem c ∧
      ¬ ∃ (U : T.Opens) (_ : t ∈ U) (V₁ V₂ : Y.Opens), V₁ ≤ g ⁻¹ᵁ U ∧ V₂ ≤ g ⁻¹ᵁ U ∧
          g ⁻¹ᵁ U ≤ V₁ ⊔ V₂ ∧ V₁ ⊓ V₂ = ⊥ ∧
            g.fiberι t ⁻¹ᵁ V₁ = (g.fiber t).basicOpen c := by
  set W₁ : (g.fiber t).Opens := ⟨{x₁}, isOpen_discrete _⟩ with hW₁
  set W₂ : (g.fiber t).Opens := ⟨{x₁}ᶜ, isOpen_discrete _⟩ with hW₂
  have hcov : (⊤ : (g.fiber t).Opens) ≤ W₁ ⊔ W₂ := by
    intro x _
    by_cases h : x ∈ ({x₁} : Set (g.fiber t))
    · exact Or.inl h
    · exact Or.inr h
  have hdisj : W₁ ⊓ W₂ = ⊥ := by
    ext x
    simp [hW₁, hW₂]
  obtain ⟨c, hcidem, hbc⟩ := exists_isIdempotentElem_basicOpen_eq_of_top_le_sup hcov hdisj
  refine ⟨c, hcidem, ?_⟩
  rintro ⟨U, hU, V₁, V₂, -, -, hcover, hdisj', htrace⟩
  obtain rfl := htop U hU
  rw [show g ⁻¹ᵁ (⊤ : T.Opens) = ⊤ from rfl] at hcover
  obtain ⟨a, haidem, hba⟩ := exists_isIdempotentElem_basicOpen_eq_of_top_le_sup hcover hdisj'
  rcases hconn a haidem with h | h
  · rw [h, Scheme.basicOpen_zero] at hba
    rw [← hba] at htrace
    have hx₁ : x₁ ∈ (g.fiber t).basicOpen c := by
      rw [hbc]
      exact rfl
    rw [← htrace] at hx₁
    simp at hx₁
  · rw [h, Scheme.basicOpen_one] at hba
    rw [← hba] at htrace
    have hx₂ : x₂ ∈ (g.fiber t).basicOpen c := by
      rw [← htrace]
      trivial
    rw [hbc] at hx₂
    exact hx (hx₂.symm ▸ rfl)

/-! ### Idempotents of a quadratic extension -/

section Quadratic

open Polynomial

variable {R : Type*} [CommRing R]

/-- Over a domain `1` and the image of `Y` are linearly independent in `R[Y]/(Y² - u)`: an
element of the ideal `(Y² - u)` of degree at most one vanishes, because `Y² - u` has degree
two. -/
theorem adjoinRoot_quadratic_eq_zero [IsDomain R] (u : R) {a b : R}
    (h : AdjoinRoot.of (X ^ 2 - C u) a + AdjoinRoot.of (X ^ 2 - C u) b *
      AdjoinRoot.root (X ^ 2 - C u) = 0) : a = 0 ∧ b = 0 := by
  have hdeg : (X ^ 2 - C u : R[X]).degree = 2 := by
    exact_mod_cast degree_X_pow_sub_C (by norm_num) u
  have hq : AdjoinRoot.mk (X ^ 2 - C u) (C a + C b * X) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    exact h
  have hlt : (C a + C b * X : R[X]).degree < (X ^ 2 - C u : R[X]).degree := by
    rw [hdeg]
    refine lt_of_le_of_lt (degree_add_le _ _) ?_
    refine max_lt (lt_of_le_of_lt degree_C_le (by norm_num)) ?_
    exact lt_of_le_of_lt (degree_C_mul_X_le b) (by norm_num)
  have hzero := eq_zero_of_dvd_of_degree_lt (AdjoinRoot.mk_eq_zero.mp hq) hlt
  constructor
  · simpa using congrArg (fun p : R[X] => p.coeff 0) hzero
  · simpa using congrArg (fun p : R[X] => p.coeff 1) hzero

/-- Every element of `R[Y]/(Y² - u)` is `a + b·y` for the class `y` of `Y`: reduce a
representative modulo the monic polynomial `Y² - u` and read off its two coefficients. -/
theorem adjoinRoot_quadratic_repr [Nontrivial R] (u : R) (e : AdjoinRoot (X ^ 2 - C u)) :
    ∃ a b : R, e = AdjoinRoot.of (X ^ 2 - C u) a +
      AdjoinRoot.of (X ^ 2 - C u) b * AdjoinRoot.root (X ^ 2 - C u) := by
  have hdeg : (X ^ 2 - C u : R[X]).degree = 2 := by
    exact_mod_cast degree_X_pow_sub_C (by norm_num) u
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (g := X ^ 2 - C u) e
  refine ⟨(p %ₘ (X ^ 2 - C u)).coeff 0, (p %ₘ (X ^ 2 - C u)).coeff 1, ?_⟩
  have hmk : AdjoinRoot.mk (X ^ 2 - C u) p
      = AdjoinRoot.mk (X ^ 2 - C u) (p %ₘ (X ^ 2 - C u)) := by
    refine AdjoinRoot.mk_eq_mk.mpr ⟨p /ₘ (X ^ 2 - C u), ?_⟩
    rw [modByMonic_eq_sub_mul_div p (X ^ 2 - C u)]
    ring
  have hdlt : (p %ₘ (X ^ 2 - C u)).degree < (X ^ 2 - C u : R[X]).degree :=
    degree_modByMonic_lt p (monic_X_pow_sub_C u two_ne_zero)
  rw [hdeg] at hdlt
  have hdlt' : (p %ₘ (X ^ 2 - C u)).degree < ((2 : ℕ) : WithBot ℕ) := by exact_mod_cast hdlt
  have hle : (p %ₘ (X ^ 2 - C u)).degree ≤ 1 := by
    rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hdlt'
    refine hdlt' m ?_
    have hm' : (1 : ℕ) < m := by exact_mod_cast hm
    omega
  rw [← hp, hmk]
  nth_rewrite 1 [eq_X_add_C_of_degree_le_one hle]
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  ring

/-- **A quadratic extension of a domain by a non-square has no idempotents but `0` and `1`.**
Writing an idempotent as `a + b·y` with `y² = u`, idempotency says `a² + ub² = a` and `2ab = b`.
The second factors as `b(2a - 1) = 0`. If `b = 0` then `a² = a`, so `a` is `0` or `1`; and if
`2a = 1` then `u(2b)² = 4a - 4a² = 1`, which makes `u(2b)` a square root of `u`. -/
theorem isIdempotentElem_adjoinRoot_quadratic [IsDomain R] {u : R}
    (hu : ∀ v : R, v * v ≠ u) {e : AdjoinRoot (X ^ 2 - C u)} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  obtain ⟨a, b, rfl⟩ := adjoinRoot_quadratic_repr u e
  have hroot : AdjoinRoot.root (X ^ 2 - C u) ^ 2 = AdjoinRoot.of (X ^ 2 - C u) u := by
    have h := AdjoinRoot.mk_self (f := X ^ 2 - C u)
    rwa [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  have hidem : (AdjoinRoot.of (X ^ 2 - C u) a + AdjoinRoot.of (X ^ 2 - C u) b *
      AdjoinRoot.root (X ^ 2 - C u)) * (AdjoinRoot.of (X ^ 2 - C u) a +
        AdjoinRoot.of (X ^ 2 - C u) b * AdjoinRoot.root (X ^ 2 - C u)) =
      AdjoinRoot.of (X ^ 2 - C u) a + AdjoinRoot.of (X ^ 2 - C u) b *
        AdjoinRoot.root (X ^ 2 - C u) := he
  have key : AdjoinRoot.of (X ^ 2 - C u) (a * a + u * (b * b) - a)
      + AdjoinRoot.of (X ^ 2 - C u) (2 * (a * b) - b) * AdjoinRoot.root (X ^ 2 - C u) = 0 := by
    simp only [map_sub, map_add, map_mul, map_ofNat]
    linear_combination hidem - (AdjoinRoot.of (X ^ 2 - C u) b) ^ 2 * hroot
  obtain ⟨h1, h2⟩ := adjoinRoot_quadratic_eq_zero u key
  have h2' : b * (2 * a - 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h2' with hb | ha
  · subst hb
    have hfac : a * (a - 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp hfac with h | h
    · left
      simp [h]
    · obtain rfl : a = 1 := by linear_combination h
      simp
  · exact absurd (by linear_combination (4 * u) * h1 - (u * (2 * a - 1)) * ha :
      (u * (2 * b)) * (u * (2 * b)) = u) (hu _)

end Quadratic

/-! ### The local ring of the line at the origin and its quadratic extension -/

section Concrete

open Polynomial

variable (k : Type u) [Field k]

/-- The ideal `(X)` of `k[X]` is prime. -/
instance spanXIsPrime : (Ideal.span {(X : k[X])}).IsPrime :=
  (Ideal.span_singleton_prime X_ne_zero).mpr prime_X

/-- The local ring `k[X]_{(X)}` of the affine line at the origin. -/
abbrev baseLoc : Type u := Localization.AtPrime (Ideal.span {(X : k[X])})

/-- The local ring `k[X]_{(X)}` is an integral domain. -/
instance : IsDomain (baseLoc k) :=
  IsLocalization.isDomain_of_local_atPrime (P := Ideal.span {(X : k[X])}) inferInstance

/-- The element `1 + X` of `k[X]_{(X)}`: a unit congruent to `1` modulo the maximal ideal, and
not a square. -/
noncomputable def onePlusX : baseLoc k := algebraMap k[X] (baseLoc k) (1 + X)

/-- **`1 + X` is not a square in `k[X]_{(X)}`.** A square root is a fraction `a/b` with `b(0) ≠ 0`
and `a² = (1 + X)b²`, and comparing degrees gives `2 deg a = 1 + 2 deg b`. -/
theorem not_isSquare_onePlusX : ∀ v : baseLoc k, v * v ≠ onePlusX k := by
  intro v hv
  obtain ⟨a, y, hay⟩ :=
    IsLocalization.exists_mk'_eq (S := baseLoc k) (Ideal.span {(X : k[X])}).primeCompl v
  obtain ⟨b, hb⟩ := y
  have hinj : Function.Injective (algebraMap k[X] (baseLoc k)) :=
    IsLocalization.injective (M := (Ideal.span {(X : k[X])}).primeCompl) (baseLoc k)
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(X : k[X])}))
  have hspec : v * algebraMap k[X] (baseLoc k) b = algebraMap k[X] (baseLoc k) a := by
    rw [← hay]
    exact IsLocalization.mk'_spec _ _ _
  have heq : a * a = (1 + X) * (b * b) := by
    refine hinj ?_
    rw [map_mul, map_mul, map_mul, ← hspec]
    rw [show algebraMap k[X] (baseLoc k) (1 + X) = v * v from hv.symm]
    ring
  have hone : ((1 : k[X]) + X).natDegree = 1 := by simp
  have honene : (1 : k[X]) + X ≠ 0 := by
    intro hx
    rw [hx] at hone
    simp at hone
  have hbne : b ≠ 0 := fun h ↦ hb (h ▸ Ideal.zero_mem _)
  have hane : a ≠ 0 := by
    intro h
    rw [h, zero_mul] at heq
    rcases mul_eq_zero.mp heq.symm with h' | h'
    · exact honene h'
    · exact hbne (by simpa using mul_eq_zero.mp h')
  have hdeg := congrArg Polynomial.natDegree heq
  rw [natDegree_mul hane hane, natDegree_mul honene (mul_ne_zero hbne hbne),
    natDegree_mul hbne hbne, hone] at hdeg
  omega

/-- The quadratic extension `k[X]_{(X)}[Y]/(Y² - (1 + X))`. It is a free module of rank two, so
the induced morphism of spectra is finite and hence proper. -/
noncomputable abbrev quadExt : Type u := AdjoinRoot (X ^ 2 - C (onePlusX k))

/-- `1 + X` is congruent to `1` modulo the maximal ideal of `k[X]_{(X)}`. -/
theorem residue_onePlusX : IsLocalRing.residue (baseLoc k) (onePlusX k) = 1 := by
  have hmem : onePlusX k - 1 ∈ IsLocalRing.maximalIdeal (baseLoc k) := by
    have heq : onePlusX k - 1 = algebraMap k[X] (baseLoc k) X := by
      rw [onePlusX, ← map_one (algebraMap k[X] (baseLoc k)), ← map_sub]
      congr 1
      ring
    rw [heq, IsLocalization.AtPrime.to_map_mem_maximal_iff (baseLoc k)
      (Ideal.span {(X : k[X])}) X]
    exact Ideal.mem_span_singleton_self _
  rwa [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at hmem

/-- The residue field of `k[X]_{(X)}` has characteristic different from two when `k` does, so the
two square roots `±1` of the residue of `1 + X` are distinct. -/
theorem two_ne_zero_residueField (h2 : (2 : k) ≠ 0) :
    (2 : IsLocalRing.ResidueField (baseLoc k)) ≠ 0 := by
  intro h
  have h' : IsLocalRing.residue (baseLoc k) 2 = 0 := by rwa [map_ofNat]
  rw [IsLocalRing.residue_eq_zero_iff,
    show (2 : baseLoc k) = algebraMap k[X] (baseLoc k) 2 from
      (map_ofNat (algebraMap k[X] (baseLoc k)) 2).symm,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (baseLoc k) (Ideal.span {(X : k[X])}) 2,
    Ideal.mem_span_singleton, X_dvd_iff] at h'
  simp only [Polynomial.coeff_ofNat_zero] at h'
  exact h2 h'

/-- A square root `s` of `1` in the residue field sends `Y` to `s` and gives a `κ`-point of the
closed fibre of `Spec k[X]_{(X)}[Y]/(Y² - (1+X))`. -/
noncomputable def fibreHom (s : IsLocalRing.ResidueField (baseLoc k)) (hs : s * s = 1) :
    quadExt k →+* IsLocalRing.ResidueField (baseLoc k) :=
  AdjoinRoot.lift (IsLocalRing.residue (baseLoc k)) s (by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, residue_onePlusX]
    rw [pow_two, hs, sub_self])

/-- `fibreHom k s hs` sends the class of `Y` to `s`. -/
@[simp]
theorem fibreHom_root (s : IsLocalRing.ResidueField (baseLoc k)) (hs : s * s = 1) :
    fibreHom k s hs (AdjoinRoot.root _) = s :=
  AdjoinRoot.lift_root _

/-- `fibreHom k s hs` restricts to the residue map on `k[X]_{(X)}`. -/
@[simp]
theorem fibreHom_algebraMap (s : IsLocalRing.ResidueField (baseLoc k)) (hs : s * s = 1)
    (x : baseLoc k) :
    fibreHom k s hs (algebraMap (baseLoc k) (quadExt k) x) = IsLocalRing.residue _ x := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

/-- The point of the spectrum of `k[X]_{(X)}[Y]/(Y² - (1+X))` attached to a square root of `1` in
the residue field: the kernel of `Stacks.AlgebraicGeometry.Fibres.fibreHom`. -/
noncomputable def fibrePrime (s : IsLocalRing.ResidueField (baseLoc k)) (hs : s * s = 1) :
    PrimeSpectrum (quadExt k) :=
  ⟨RingHom.ker (fibreHom k s hs), RingHom.ker_isPrime _⟩

/-- The point `fibrePrime k s hs` lies over the closed point of `Spec k[X]_{(X)}`. -/
theorem comap_fibrePrime (s : IsLocalRing.ResidueField (baseLoc k)) (hs : s * s = 1) :
    PrimeSpectrum.comap (algebraMap (baseLoc k) (quadExt k)) (fibrePrime k s hs)
      = IsLocalRing.closedPoint (baseLoc k) := by
  refine PrimeSpectrum.ext ?_
  ext x
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, fibrePrime, RingHom.mem_ker,
    IsLocalRing.closedPoint]
  rw [fibreHom_algebraMap]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- If `2 ≠ 0` in `k`, the square roots `1` and `-1` give distinct points of the closed fibre. -/
theorem fibrePrime_ne (h2 : (2 : k) ≠ 0) :
    fibrePrime k 1 (by ring) ≠ fibrePrime k (-1) (by ring) := by
  intro h
  have hker : RingHom.ker (fibreHom k 1 (by ring)) = RingHom.ker (fibreHom k (-1) (by ring)) :=
    congrArg PrimeSpectrum.asIdeal h
  have hmem : (AdjoinRoot.root (X ^ 2 - C (onePlusX k)) - 1)
      ∈ RingHom.ker (fibreHom k 1 (by ring)) := by
    rw [RingHom.mem_ker, map_sub, fibreHom_root, map_one, sub_self]
  rw [hker, RingHom.mem_ker, map_sub, fibreHom_root, map_one] at hmem
  apply two_ne_zero_residueField k h2
  linear_combination -hmem

end Concrete

/-! ### The refutation -/

section Refutation

open Polynomial

variable (k : Type u) [Field k]

/-- The finite morphism `Spec k[X]_{(X)}[Y]/(Y² - (1+X)) ⟶ Spec k[X]_{(X)}`. -/
noncomputable def counterMap :
    Spec (CommRingCat.of (quadExt k)) ⟶ Spec (CommRingCat.of (baseLoc k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (baseLoc k) (quadExt k)))

/-- The morphism `counterMap k` is finite. -/
instance : IsFinite (counterMap k) := by
  rw [counterMap, AlgebraicGeometry.IsFinite.SpecMap_iff]
  change (algebraMap (baseLoc k) (quadExt k)).Finite
  rw [RingHom.finite_algebraMap]
  exact Polynomial.Monic.finite_adjoinRoot (monic_X_pow_sub_C _ two_ne_zero)

/-- The global sections of the spectrum of the quadratic extension have no idempotents but `0`
and `1`, so that spectrum has no nontrivial decomposition into two disjoint opens. -/
theorem isIdempotentElem_quadExt_sections (a : Γ(Spec (CommRingCat.of (quadExt k)), ⊤))
    (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  set e := (Scheme.ΓSpecIso (CommRingCat.of (quadExt k))).commRingCatIsoToRingEquiv
  rcases isIdempotentElem_adjoinRoot_quadratic (not_isSquare_onePlusX k) (ha.map e) with h | h
  · left
    exact e.injective (by rw [h, map_zero])
  · right
    exact e.injective (by rw [h, map_one])

/-- **No clopen splitting of a neighbourhood for the proper morphism
`Spec k[X]_{(X)}[Y]/(Y² - (1+X)) ⟶ Spec k[X]_{(X)}`.** For a field `k` with `2 ≠ 0` there is no
assignment, to every proper morphism `g : Y ⟶ T`, every `t : T` and every idempotent `c` on the
fibre `Y_t`, of an open neighbourhood `U` of `t` and a decomposition of `g ⁻¹ᵁ U` into two
disjoint opens the first of which meets the fibre exactly in `D(c)`.

The counterexample is the finite morphism above at the closed point: its source has no nontrivial
decomposition into two disjoint opens, while its closed fibre has two points. -/
theorem not_clopenSplitting (h2 : (2 : k) ≠ 0) :
    ¬ ∀ {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] (t : T) (c : Γ(g.fiber t, ⊤)),
      IsIdempotentElem c → ∃ (U : T.Opens) (_ : t ∈ U) (V₁ V₂ : Y.Opens), V₁ ≤ g ⁻¹ᵁ U ∧
        V₂ ≤ g ⁻¹ᵁ U ∧ g ⁻¹ᵁ U ≤ V₁ ⊔ V₂ ∧ V₁ ⊓ V₂ = ⊥ ∧
          g.fiberι t ⁻¹ᵁ V₁ = (g.fiber t).basicOpen c := by
  intro hsplit
  have hmem : ∀ (s : IsLocalRing.ResidueField (baseLoc k)) (hs : s * s = 1),
      fibrePrime k s hs ∈ counterMap k ⁻¹'
        {(IsLocalRing.closedPoint (baseLoc k) : Spec (CommRingCat.of (baseLoc k)))} :=
    comap_fibrePrime k
  set t : (Spec (CommRingCat.of (baseLoc k)) : Scheme.{u}) :=
    IsLocalRing.closedPoint (baseLoc k)
  set x₁ := ((counterMap k).fiberHomeo t).symm ⟨_, hmem 1 (by ring)⟩ with hx₁
  set x₂ := ((counterMap k).fiberHomeo t).symm ⟨_, hmem (-1) (by ring)⟩ with hx₂
  have hx : x₁ ≠ x₂ := by
    intro h
    have h₁ := (counterMap k).fiberι_fiberHomeo_symm t ⟨_, hmem 1 (by ring)⟩
    have h₂ := (counterMap k).fiberι_fiberHomeo_symm t ⟨_, hmem (-1) (by ring)⟩
    rw [← hx₁] at h₁
    rw [← hx₂] at h₂
    rw [h, h₂] at h₁
    exact fibrePrime_ne k h2 h₁.symm
  obtain ⟨c, hc, hno⟩ := exists_isIdempotentElem_not_clopenSplitting (counterMap k) t
    (isIdempotentElem_quadExt_sections k) (fun U ↦ (IsLocalRing.closedPoint_mem_iff U).mp)
    hx
  exact hno (hsplit (counterMap k) t c hc)

/-- **[Stacks, Tag 0G7X] itself holds for the counterexample, for every function on the fibre and
not merely for the idempotents.** The morphism is finite and the base point is closed, so this is
`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isFinite`. Together with
`Stacks.AlgebraicGeometry.Fibres.not_clopenSplitting` this is the gap between the tag and the
refuted statement, exhibited on one morphism: every function on the closed fibre is the
restriction of a section over the whole source, while the decomposition of the fibre attached to
an idempotent is cut out by no decomposition of the source. -/
theorem extendsOverNeighbourhood_counterMap
    (c : Γ((counterMap k).fiber (IsLocalRing.closedPoint (baseLoc k)), ⊤)) :
    ExtendsOverNeighbourhood (counterMap k) (IsLocalRing.closedPoint (baseLoc k)) c :=
  extendsOverNeighbourhood_of_isFinite (counterMap k)
    (IsLocalRing.isClosed_singleton_closedPoint (baseLoc k)) c

/-- `2 ≠ 0` in a universe-lifted copy of the rationals, which supplies a field in every
universe. -/
theorem two_ne_zero_uliftRat : (2 : ULift.{u} ℚ) ≠ 0 := by
  intro h
  have hdown := congrArg ULift.down h
  norm_num at hdown

/-- **The clopen-splitting statement is false in every universe.** There is no assignment, to
every proper morphism `g : Y ⟶ T`, every point `t` of the base and every idempotent `c` on the
fibre `Y_t`, of an open neighbourhood `U` of `t` and a decomposition of `g ⁻¹ᵁ U` into two
disjoint opens the first of which meets the fibre exactly in the nonvanishing locus of `c`.

This is `Stacks.AlgebraicGeometry.Fibres.not_clopenSplitting` over the universe-lifted
rationals. [Stacks, Tag 0G7X] is not this statement: it says only that an idempotent on the fibre
is the restriction of *some* section over `f ⁻¹ᵁ U`, and that section is not idempotent in
general. -/
theorem not_forall_exists_clopenSplitting_of_isProper :
    ¬ ∀ {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] (t : T) (c : Γ(g.fiber t, ⊤)),
      IsIdempotentElem c → ∃ (U : T.Opens) (_ : t ∈ U) (V₁ V₂ : Y.Opens), V₁ ≤ g ⁻¹ᵁ U ∧
        V₂ ≤ g ⁻¹ᵁ U ∧ g ⁻¹ᵁ U ≤ V₁ ⊔ V₂ ∧ V₁ ⊓ V₂ = ⊥ ∧
          g.fiberι t ⁻¹ᵁ V₁ = (g.fiber t).basicOpen c :=
  not_clopenSplitting (ULift.{u} ℚ) two_ne_zero_uliftRat

end Refutation

end Stacks.AlgebraicGeometry.Fibres

end
