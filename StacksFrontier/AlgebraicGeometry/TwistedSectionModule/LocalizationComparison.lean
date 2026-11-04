module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.Localization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.Basic

/-!
# The comparison map out of the localized twisted sections

Stacks Tag 0B5L sends a degree-zero fraction `t / sⁿ` of the graded module
`Γ_*(X, F, L) = ⨁_{m ≥ 0} Γ(X, F ⊗ L ^⊗ m)`, localized at a global section `s` of a tensor power
`L ^⊗ d`, to the section of `F` over the nonvanishing locus `X_s` obtained by restricting `t` and
dividing by `sⁿ`, which is invertible there. The degree `d` is arbitrary.

The map is constructed in the *site-level* spelling of the graded module,
`Stacks.SheafOfModules.sectionModule`, as `Stacks.SheafOfModules.sectionLocalizationMap`.

The graded module that the `Proj`-side morphism `Stacks.SectionRingProjMorphism.projHomOfIsAmple`
is stated over is a different object: the *whiskering* spelling
`Stacks.TwistedSections.twistModule`, graded by `Stacks.TwistedSections.moduleGrading`. This file
builds the comparison map there. Its one geometric input is isolated as a hypothesis: a family of
divisions by the powers of `s`, compatible with enlarging the exponent.

## Main definitions

* `Stacks.TwistedSections.sectionPowOfDegree`: `sⁿ` as a section of `L ^⊗ (d * n)`, namely the
  degree-`d * n` component of the `n`-th power of `s` in the section ring.
* `Stacks.TwistedSections.numeratorHom`: the degree-`d * n` numerator a fraction of exponent `n`
  has, as a morphism out of the whole graded module.
* `Stacks.TwistedSections.IsPowerInvariant`: the compatibility a family of divisions by the
  powers of `s` must satisfy to descend to the degree-zero localization — dividing `t ⊗ sᵏ` by
  `s ^ (n + k)` must agree with dividing `t` by `sⁿ`. The family is indexed by the *exponent* of
  the denominator, so its `n`-th member divides numerators of degree `d * n`.
* `Stacks.TwistedSections.localizationLift`: **the comparison map in the whiskering spelling**,
  `Γ_*(X, F, L)_{(s)} ⟶ N`, for any compatible family of divisions with values in `N`.

## Main results

* `Stacks.TwistedSections.pow_homogeneousSection_smul_of`: acting by `sᵏ` on a homogeneous
  element of degree `n` is the homogeneous element of degree `d * k + n` obtained by
  whiskering.
* `Stacks.TwistedSections.localizationLift_fraction` and
  `Stacks.TwistedSections.localizationLift_mk`: **the value of the comparison map on a fraction**
  `t / sⁿ` is the `n`-th division of `t`, for any representative and on the generator itself.
* `Stacks.TwistedSections.localizationLift_smul`: the comparison map is semilinear over a ring
  map out of `Γ_*(X, L)_{(s)}` as soon as the divisions are so on numerators.
* `Stacks.TwistedSections.sectionGrading_eq_ampleGrading`: the grading of the section ring used
  here is the one graded prime avoidance and the `Proj`-side morphism use, on the nose.

## Implementation notes

**The divisions are a hypothesis.** Families of them are `Stacks.TwistedSections.powerDivision`,
with `Stacks.TwistedSections.isPowerInvariant_powerDivision`, for a section invertible as a
morphism `𝟙_ C ⟶ 𝟙_ C ⊗ L`, and `Stacks.TwistedSections.monoidalDivision`, with
`Stacks.TwistedSections.isPowerInvariant_monoidalDivision`, for a section that becomes invertible
after a monoidal functor — on a scheme, after restriction to an open inside the nonvanishing
locus. These divisions are the inverse of multiplication by `sⁿ`, which is bijective once `s` is
an isomorphism; see `Stacks.TwistedSections.shiftBySection_comp_twistIso`.

**The two spellings of the graded module are not isomorphic, and the map is built directly.** The
site-level `Stacks.SheafOfModules.sectionModule` is indexed by `ℤ` with the sections of *every*
twist of `F`, while `Stacks.TwistedSections.moduleGrading` is trivial in negative degrees; so
there is no isomorphism of graded modules to transport that map along, even though the
degree-zero localizations only ever see the nonnegative part. The ring side is the opposite
situation: `Stacks.TwistedSections.sectionGrading` and `Stacks.AmpleFiniteAvoidance.grading` are
the same family of subgroups, which is `sectionGrading_eq_ampleGrading`.

**The family is indexed by the exponent of the denominator, and one reindexing is unavoidable.**
A fraction of the degree-zero localization at a section of `L ^⊗ d` has numerator of degree
`n * d` for `n` the exponent of its denominator, which is the spelling
`Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree` records. The divisions produced in the
sibling files are indexed as `twistSections F L (d * n)`, because `d * (n + 1)` and `d * n + d`
are definitionally equal while `(n + 1) * d` and `n * d + d` are not. The two orders
of the product are crossed exactly once, inside
`Stacks.TwistedSections.numeratorHom`, and `Stacks.TwistedSections.twistCongr_trans` collapses
the composites of reindexings that result.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4) — the degree-zero
  localization of a graded module.
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV) — the section ring.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections sectionRing HasTrivialSelfBraiding)
open scoped Stacks.GradedLocalization

universe w v u

namespace Stacks.TwistedSections

section Abstract

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] {L : C}
  [(tensorRight L).Additive]

/-- **`sⁿ` as a section of `L ^⊗ n`**: the degree-`n` component of the `n`-th power of `s` in the
section ring, which is homogeneous of degree `n`. -/
noncomputable def sectionPow (s : powSections L 1) (n : ℕ) : powSections L n :=
  (homogeneousSection s ^ n) n

/-- **`sⁿ` as a section of `L ^⊗ (d * n)`**: the degree-`d * n` component of the `n`-th power of
a section `s` of `L ^⊗ d` in the section ring, which is homogeneous of that degree. -/
noncomputable def sectionPowOfDegree {d : ℕ} (s : powSections L d) (n : ℕ) :
    powSections L (d * n) :=
  (homogeneousSectionOfDegree s ^ n) (d * n)

/-- The degree-`n` component of `sⁿ` is `sⁿ`. -/
theorem of_sectionPow (s : powSections L 1) (n : ℕ) :
    DirectSum.of (powSections L) n (sectionPow s n) = homogeneousSection s ^ n := by
  obtain ⟨q, hq⟩ : homogeneousSection s ^ n ∈ sectionGrading L n := by
    simpa using SetLike.pow_mem_graded n (homogeneousSection_mem s)
  unfold sectionPow
  rw [← hq, DirectSum.of_eq_same]

/-- The degree-`d * n` component of `sⁿ` is `sⁿ`. -/
theorem of_sectionPowOfDegree {d : ℕ} (s : powSections L d) (n : ℕ) :
    DirectSum.of (powSections L) (d * n) (sectionPowOfDegree s n) =
      homogeneousSectionOfDegree s ^ n := by
  obtain ⟨q, hq⟩ : homogeneousSectionOfDegree s ^ n ∈ sectionGrading L (d * n) := by
    have h : homogeneousSectionOfDegree s ^ n ∈ sectionGrading L (n • d) :=
      SetLike.pow_mem_graded n (homogeneousSectionOfDegree_mem s)
    rwa [smul_eq_mul, Nat.mul_comm n d] at h
  unfold sectionPowOfDegree
  rw [← hq, DirectSum.of_eq_same]

/-- The first power of `s` is `s`. -/
@[simp] theorem sectionPow_one (s : powSections L 1) : sectionPow s 1 = s := by
  unfold sectionPow
  rw [pow_one, homogeneousSection, DirectSum.of_eq_same]

/-- The first power of `s` is `s` itself, read in the section ring. -/
theorem of_sectionPow_one {d : ℕ} (s : powSections L d) :
    DirectSum.of (powSections L) (d * 1) (sectionPowOfDegree s 1) =
      homogeneousSectionOfDegree s := by
  rw [of_sectionPowOfDegree, pow_one]

/-- The zeroth power of `s` is the unit section `𝟙 (𝟙_ C)` of degree `0`. -/
@[simp] theorem sectionPow_zero (s : powSections L 1) :
    sectionPow s 0 = (𝟙 (𝟙_ C) : powSections L 0) := by
  unfold sectionPow
  rw [pow_zero]
  rfl

/-- The zeroth power of `s` is the unit section `𝟙 (𝟙_ C)` of degree `0`. -/
@[simp] theorem sectionPowOfDegree_zero {d : ℕ} (s : powSections L d) :
    sectionPowOfDegree s 0 = (𝟙 (𝟙_ C) : powSections L 0) := by
  unfold sectionPowOfDegree
  rw [pow_zero]
  rfl

/-- The degree of the numerator of `t ⊗ sᵏ` over `s ^ (n + k)`: multiplying a numerator of degree
`d * n` by `sᵏ` gives one of degree `d * (n + k)`. -/
theorem mul_add_degree (d n k : ℕ) : d * k + d * n = d * (n + k) := by ring

/-- The degree of the numerator of `a · t` for `a` homogeneous of degree `m • d`. -/
theorem nsmul_add_degree (d m n : ℕ) : m • d + d * n = d * (m + n) := by
  rw [smul_eq_mul]; ring

variable {F : C} [BraidedCategory C] [HasTrivialSelfBraiding L]

/-- **Acting by `sᵏ` on a homogeneous twisted section**: the result is the twisted section of
degree `k + n` obtained by whiskering by `k` copies of `L`. -/
theorem pow_homogeneousSection_smul_of (s : powSections L 1) (k n : ℕ)
    (t : twistSections F L n) :
    homogeneousSection s ^ k • DirectSum.of (twistSections F L) n t =
      DirectSum.of (twistSections F L) (k + n) (gsmul (sectionPow s k) t) := by
  rw [← of_sectionPow, of_smul_of]

/-- **Acting by `sᵏ` on a homogeneous twisted section**: the result is the twisted section of
degree `d * k + n` obtained by whiskering by `d * k` copies of `L`. -/
theorem pow_homogeneousSectionOfDegree_smul_of {d : ℕ} (s : powSections L d) (k n : ℕ)
    (t : twistSections F L n) :
    homogeneousSectionOfDegree s ^ k • DirectSum.of (twistSections F L) n t =
      DirectSum.of (twistSections F L) (d * k + n) (gsmul (sectionPowOfDegree s k) t) := by
  rw [← of_sectionPowOfDegree, of_smul_of]

variable {N : Type w} [AddCommGroup N]

/-- **A family of divisions by the powers of `s` is power-invariant** when dividing `t ⊗ sᵏ` by
`s ^ (k + n)` agrees with dividing `t` by `sⁿ`. -/
def IsPowerInvariant (s : powSections L 1) (D : (n : ℕ) → twistSections F L n →+ N) : Prop :=
  ∀ (n k : ℕ) (t : twistSections F L n), D (k + n) (gsmul (sectionPow s k) t) = D n t

/-- **A family of divisions by the powers of `s` is power-invariant** when dividing `t ⊗ sᵏ` by
`s ^ (n + k)` agrees with dividing `t` by `sⁿ`. The family is indexed by the *exponent* of the
denominator, so its `n`-th member divides numerators of degree `d * n`. -/
def IsPowerInvariantOfDegree {d : ℕ} (s : powSections L d)
    (D : (n : ℕ) → twistSections F L (d * n) →+ N) : Prop :=
  ∀ (n k : ℕ) (t : twistSections F L (d * n)),
    D (n + k) (twistCongr (mul_add_degree d n k) (gsmul (sectionPowOfDegree s k) t)) = D n t

/-- The total map of a power-invariant family is unchanged by multiplying a homogeneous element
by a power of `s`. -/
theorem toAddMonoid_pow_smul (s : powSections L 1)
    (D : (n : ℕ) → twistSections F L n →+ N) (hD : IsPowerInvariant s D)
    (n k : ℕ) (x : twistModule F L) (hx : x ∈ moduleGrading F L ((n * 1 : ℕ) : ℤ)) :
    DirectSum.toAddMonoid D (homogeneousSection s ^ k • x) = DirectSum.toAddMonoid D x := by
  rw [Nat.mul_one] at hx
  obtain ⟨t, rfl⟩ := mem_moduleGrading_natCast_iff.mp hx
  rw [pow_homogeneousSection_smul_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, hD]

/-- **The degree-`d * n` numerator a fraction of exponent `n` has**, as a morphism of additive
groups out of the whole graded module: the degree-`n * d` component, reindexed to degree
`d * n`. -/
noncomputable def numeratorHom (F L : C) [(tensorRight L).Additive] (d n : ℕ) :
    twistModule F L →+ twistSections F L (d * n) :=
  (twistCongrHom F L (Nat.mul_comm n d)).comp (componentHom F L (n * d))

/-- `numeratorHom F L d n` sends the homogeneous element of degree `d * n` given by `t` to `t`. -/
@[simp] theorem numeratorHom_of {d n : ℕ} (t : twistSections F L (d * n)) :
    numeratorHom F L d n (DirectSum.of (twistSections F L) (d * n) t) = t := by
  rw [numeratorHom, AddMonoidHom.comp_apply, ← of_twistCongr (Nat.mul_comm d n) t,
    componentHom_of, twistCongrHom_apply, twistCongr_trans]
  exact twistCongr_rfl t

/-- `numeratorHom F L d n` reindexes the degree-`n * d` component. -/
private theorem numeratorHom_of_nat_mul {d n : ℕ} (t : twistSections F L (n * d)) :
    numeratorHom F L d n (DirectSum.of (twistSections F L) (n * d) t) =
      twistCongr (Nat.mul_comm n d) t := by
  rw [numeratorHom, AddMonoidHom.comp_apply, componentHom_of, twistCongrHom_apply]

/-- `numeratorHom F L d M` of a section `a` acting on a homogeneous element of degree `n * d`. -/
private theorem numeratorHom_of_gsmul {d M m n : ℕ} (a : powSections L m)
    (t : twistSections F L (n * d)) (h : m + d * n = d * M) :
    numeratorHom F L d M (DirectSum.of (twistSections F L) (m + n * d) (gsmul a t)) =
      twistCongr h (gsmul a (twistCongr (Nat.mul_comm n d) t)) := by
  rw [← of_twistCongr (show m + n * d = d * M by rwa [Nat.mul_comm n d]), numeratorHom_of,
    gsmul_twistCongr, twistCongr_trans]

/-- The numerator of a power-invariant family's input is unchanged, up to the family, by
multiplying numerator and denominator by `sᵏ`. -/
theorem numeratorHom_pow_smul {d : ℕ} (s : powSections L d)
    (D : (n : ℕ) → twistSections F L (d * n) →+ N) (hD : IsPowerInvariantOfDegree s D)
    (n k : ℕ) (x : twistModule F L) (hx : x ∈ moduleGrading F L ((n * d : ℕ) : ℤ)) :
    D (n + k) (numeratorHom F L d (n + k) (homogeneousSectionOfDegree s ^ k • x)) =
      D n (numeratorHom F L d n x) := by
  obtain ⟨t, rfl⟩ := mem_moduleGrading_natCast_iff.mp hx
  rw [pow_homogeneousSectionOfDegree_smul_of, numeratorHom_of_nat_mul,
    numeratorHom_of_gsmul _ _ (mul_add_degree d n k)]
  exact hD n k _

/-- **The comparison map of Stacks Tag 0B5L in the whiskering spelling**: a power-invariant
family of divisions by the powers of `s` descends to the degree-zero localization
`Γ_*(X, F, L)_{(s)}` of the twisted sections away from `s`. -/
noncomputable def localizationLift (s : powSections L 1)
    (D : (n : ℕ) → twistSections F L n →+ N) (hD : IsPowerInvariant s D) :
    sectionAtNonvanishingOpen F L s →+ N :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree (sectionGrading L)
    (moduleGrading F L) (homogeneousSection_mem s) (fun _ => DirectSum.toAddMonoid D)
    (fun n k x hx => toAddMonoid_pow_smul s D hD n k x hx)

/-- **The comparison map of Stacks Tag 0B5L in the whiskering spelling**: a power-invariant
family of divisions by the powers of `s` descends to the degree-zero localization
`Γ_*(X, F, L)_{(s)}` of the twisted sections away from `s`. -/
noncomputable def localizationLiftOfDegree {d : ℕ} (s : powSections L d)
    (D : (n : ℕ) → twistSections F L (d * n) →+ N) (hD : IsPowerInvariantOfDegree s D) :
    sectionAtNonvanishingOpenOfDegree F L s →+ N :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree (sectionGrading L)
    (moduleGrading F L) (homogeneousSectionOfDegree_mem s)
    (fun n => (D n).comp (numeratorHom F L d n))
    (fun n k x hx => numeratorHom_pow_smul s D hD n k x hx)

/-- **The value of the comparison map on a fraction** `t / sⁿ` with twisted numerator `t` of
degree `n` is the `n`-th division of `t`. -/
theorem localizationLift_fraction (s : powSections L 1)
    (D : (n : ℕ) → twistSections F L n →+ N) (hD : IsPowerInvariant s D)
    (z : sectionAtNonvanishingOpen F L s) (n : ℕ) (t : twistSections F L n)
    (hz : (z : LocalizedModule.Away (homogeneousSection s) (twistModule F L)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSection s))
        (DirectSum.of (twistSections F L) n t) ⟨homogeneousSection s ^ n, ⟨n, rfl⟩⟩) :
    localizationLift s D hD z = D n t := by
  have hx : DirectSum.of (twistSections F L) n t ∈ moduleGrading F L ((n * 1 : ℕ) : ℤ) := by
    rw [Nat.mul_one]
    exact ⟨t, rfl⟩
  rw [localizationLift, Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_fraction
    (sectionGrading L) (moduleGrading F L) (homogeneousSection_mem s) _ _ z n _ hx hz,
    DirectSum.toAddMonoid_of]

/-- **The value of the comparison map on a fraction** `t / sⁿ` with twisted numerator `t` of
degree `d * n` is the `n`-th division of `t`. -/
theorem localizationLiftOfDegree_fraction {d : ℕ} (s : powSections L d)
    (D : (n : ℕ) → twistSections F L (d * n) →+ N) (hD : IsPowerInvariantOfDegree s D)
    (z : sectionAtNonvanishingOpenOfDegree F L s) (n : ℕ) (t : twistSections F L (d * n))
    (hz : (z : LocalizedModule.Away (homogeneousSectionOfDegree s) (twistModule F L)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSectionOfDegree s))
        (DirectSum.of (twistSections F L) (d * n) t) ⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩) :
    localizationLiftOfDegree s D hD z = D n t := by
  have hx : DirectSum.of (twistSections F L) (d * n) t ∈
      moduleGrading F L ((n * d : ℕ) : ℤ) :=
    ⟨twistCongr (Nat.mul_comm d n) t, of_twistCongr (Nat.mul_comm d n) t⟩
  rw [localizationLiftOfDegree, Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_fraction
    (sectionGrading L) (moduleGrading F L) (homogeneousSectionOfDegree_mem s) _ _ z n _ hx hz,
    AddMonoidHom.comp_apply, numeratorHom_of]

/-- **The comparison map on a generator**: the fraction `t / sⁿ` cut out by a twisted section `t`
of degree `n` is sent to the `n`-th division of `t`. -/
theorem localizationLift_mk (s : powSections L 1)
    (D : (n : ℕ) → twistSections F L n →+ N) (hD : IsPowerInvariant s D)
    (n : ℕ) (t : twistSections F L n) :
    localizationLift s D hD ⟨LocalizedModule.mk (DirectSum.of (twistSections F L) n t)
        (⟨homogeneousSection s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (homogeneousSection s)),
      mk_mem_sectionAtNonvanishingOpen s n t⟩ = D n t :=
  localizationLift_fraction s D hD _ n t rfl

/-- **The comparison map on a generator**: the fraction `t / sⁿ` cut out by a twisted section `t`
of degree `d * n` is sent to the `n`-th division of `t`. -/
theorem localizationLiftOfDegree_mk {d : ℕ} (s : powSections L d)
    (D : (n : ℕ) → twistSections F L (d * n) →+ N) (hD : IsPowerInvariantOfDegree s D)
    (n : ℕ) (t : twistSections F L (d * n)) :
    localizationLiftOfDegree s D hD ⟨LocalizedModule.mk (DirectSum.of (twistSections F L) (d * n) t)
        (⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩ :
          Submonoid.powers (homogeneousSectionOfDegree s)),
      mk_mem_sectionAtNonvanishingOpenOfDegree s n t⟩ = D n t :=
  localizationLiftOfDegree_fraction s D hD _ n t rfl

/-- **Post-composing the comparison map is post-composing the division family**: for an additive
map `ε : N →+ N'`, the comparison map of the family `ε ∘ D` is `ε` composed with that of `D`. -/
theorem localizationLift_comp {N' : Type*} [AddCommGroup N'] (ε : N →+ N')
    {d : ℕ} (s : powSections L d)
    (D : (n : ℕ) → twistSections F L (d * n) →+ N) (hD : IsPowerInvariantOfDegree s D) :
    localizationLiftOfDegree s (fun n => ε.comp (D n)) (fun n k t => congrArg ε (hD n k t)) =
      ε.comp (localizationLiftOfDegree s D hD) :=
  AddMonoidHom.ext fun _ => rfl

/-- **The comparison map depends only on the division family**: two power-invariant families that
agree degreewise have the same comparison map. -/
theorem localizationLift_congr {d : ℕ} (s : powSections L d)
    {D D' : (n : ℕ) → twistSections F L (d * n) →+ N} (hD : IsPowerInvariantOfDegree s D)
    (hD' : IsPowerInvariantOfDegree s D') (h : ∀ n, D n = D' n) :
    localizationLiftOfDegree s D hD = localizationLiftOfDegree s D' hD' := by
  obtain rfl : D = D' := funext h
  rfl

/-- **The comparison map is semilinear** over a ring map `φ` out of the degree-zero localized
section ring `Γ_*(X, L)_{(s)}`, as soon as acting by a homogeneous section of `L ^⊗ m` on a
numerator is multiplication by the value of `φ` on the corresponding fraction. -/
theorem localizationLift_smul (s : powSections L 1)
    (D : (n : ℕ) → twistSections F L n →+ N) (hD : IsPowerInvariant s D)
    {K : Type*} [CommRing K] [Module K N] (φ : ringAtNonvanishingOpen s →+* K)
    (hφ : ∀ (m n : ℕ) (a : powSections L (m • 1)) (t : twistSections F L n),
      D (m • 1 + n) (gsmul a t) =
        φ (HomogeneousLocalization.Away.mk (sectionGrading L) (homogeneousSection_mem s) m
          (DirectSum.of (powSections L) (m • 1) a) ⟨a, rfl⟩) • D n t)
    (a : ringAtNonvanishingOpen s) (z : sectionAtNonvanishingOpen F L s) :
    localizationLift s D hD (a • z) = φ a • localizationLift s D hD z := by
  refine Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_smul (sectionGrading L)
    (moduleGrading F L) (homogeneousSection_mem s) _ _ φ ?_ a z
  intro m n r x hr hx
  rw [Nat.mul_one] at hx
  obtain ⟨t, rfl⟩ := mem_moduleGrading_natCast_iff.mp hx
  obtain ⟨b, rfl⟩ := hr
  rw [of_smul_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
  exact hφ m n b t

/-- **The comparison map is semilinear** over a ring map `φ` out of the degree-zero localized
section ring `Γ_*(X, L)_{(s)}`, as soon as acting by a homogeneous section of `L ^⊗ (m * d)` on a
numerator is multiplication by the value of `φ` on the corresponding fraction. -/
theorem localizationLiftOfDegree_smul {d : ℕ} (s : powSections L d)
    (D : (n : ℕ) → twistSections F L (d * n) →+ N) (hD : IsPowerInvariantOfDegree s D)
    {K : Type*} [CommRing K] [Module K N] (φ : ringAtNonvanishingOpenOfDegree s →+* K)
    (hφ : ∀ (m n : ℕ) (a : powSections L (m • d)) (t : twistSections F L (d * n)),
      D (m + n) (twistCongr (nsmul_add_degree d m n) (gsmul a t)) =
        φ (HomogeneousLocalization.Away.mk (sectionGrading L) (homogeneousSectionOfDegree_mem s) m
          (DirectSum.of (powSections L) (m • d) a) ⟨a, rfl⟩) • D n t)
    (a : ringAtNonvanishingOpenOfDegree s) (z : sectionAtNonvanishingOpenOfDegree F L s) :
    localizationLiftOfDegree s D hD (a • z) = φ a • localizationLiftOfDegree s D hD z := by
  refine Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_smul (sectionGrading L)
    (moduleGrading F L) (homogeneousSectionOfDegree_mem s) _ _ φ ?_ a z
  intro m n r x hr hx
  obtain ⟨t, rfl⟩ := mem_moduleGrading_natCast_iff.mp hx
  obtain ⟨b, rfl⟩ := hr
  rw [of_smul_of, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, numeratorHom_of_nat_mul,
    numeratorHom_of_gsmul _ _ (nsmul_add_degree d m n)]
  exact hφ m n b _

end Abstract

section Scheme

open AlgebraicGeometry

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- **The grading of the section ring of an invertible module on a scheme has one spelling**: the
family the twisted-section module is graded over is the family graded prime avoidance and the
`Proj`-side morphism are stated over. -/
theorem sectionGrading_eq_ampleGrading {X : Scheme.{u}} (L : X.Modules) :
    sectionGrading L = Stacks.AmpleFiniteAvoidance.grading L := rfl

end Scheme

end Stacks.TwistedSections

end
