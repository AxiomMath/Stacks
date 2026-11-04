module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.WeightSplitting

/-!
# The restriction maps of a twist on `Proj` are the localization maps

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring and let `f ∈ 𝒜 k`, `g ∈ 𝒜 l` be homogeneous of
positive degrees with `D₊(g) ⊆ D₊(f)`. The sections of the twist `𝒪(d)` over `D₊(f)` are
identified with the degree-`d` part of the localization `A[1/f]`
(`Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading`). This file proves that this
identification is natural in the standard open: the restriction map of `𝒪(d)` is the localization
map. It does so first for a general graded ring and then for a polynomial ring and an intersection
of standard coordinate charts.

For a polynomial ring and two chart intersections with `Set.range s ⊆ Set.range t` — so that the
chart intersection at `t` is contained in the one at `s` — the square

```
Γ(D₊(T_{i₀} ⋯ T_{i_p}), 𝒪(d))  --restriction-->  Γ(D₊(T_{j₀} ⋯ T_{j_q}), 𝒪(d))
            |                                                |
            |  sectionsTwistProdXEquiv                       |  sectionsTwistProdXEquiv
            v                                                v
  (R[T, 1/(T_{i₀} ⋯ T_{i_p})])_d  --chartTransition-->  (R[T, 1/(T_{j₀} ⋯ T_{j_q})])_d
```

commutes (`Stacks.ProjectiveCohomology.coe_sectionsTwistProdXEquiv_map_homOfLE`). Since
`Stacks.ProjectiveCohomology.chartTransition` carries each Laurent weight piece into the piece
of the same weight, the restriction maps of `𝒪(d)` are weight-preserving
(`Stacks.ProjectiveCohomology.mem_chartWeight_sectionsTwistProdXEquiv_map_homOfLE`).

Everything here is on `AlgebraicGeometry.Proj (Stacks.ProjectiveCohomology.polyGrading R n)`,
equivalently on `AlgebraicGeometry.Proj` of `MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R`
(`Stacks.ProjectiveCohomology.polyGrading_eq`), not on `AlgebraicGeometry.projectiveSpaceOverRing`.

## Main results

* `Stacks.ProjectiveCohomology.standardOpenEquivTwist_map_homOfLE`: for an arbitrary graded ring,
  the standard-open identification of the sections of a twist is natural in the standard open:
  restriction along `D₊(g) ⊆ D₊(f)` becomes the canonical degree-zero restriction map of
  [Stacks, Tag 01M4].
* `Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_map_homOfLE`: the same square
  read on the degree-`d` part of the localization, where it becomes the map of ordinary
  localizations.
* `Stacks.ProjectiveCohomology.eq_chartTransition_of_algebraMap`: `chartTransition` is the only
  map between two Čech terms which is linear over the polynomial ring and is the identity on
  polynomials.
* `Stacks.ProjectiveCohomology.localizedMap_eq_chartTransition`: the localization map of
  [Stacks, Tag 01M4] between two chart intersections is `chartTransition`.
* `Stacks.ProjectiveCohomology.coe_sectionsTwistProdXEquiv_map_homOfLE`: the naturality square
  above — the restriction map of `𝒪(d)` between two intersections of standard coordinate charts
  of `Proj R[T₀, …, Tₙ]` is `chartTransition`.
* `Stacks.ProjectiveCohomology.coe_sectionsTwistProdXEquivWeightSpan_map_homOfLE`: the same square
  through the Laurent monomial basis of the Čech term.
* `Stacks.ProjectiveCohomology.mem_chartWeight_sectionsTwistProdXEquiv_map_homOfLE`: the
  restriction maps of `𝒪(d)` carry each Laurent weight piece into the piece of the same weight.

## Implementation notes

No attribute for [Stacks, Tag 01XT] is attached: that tag is a statement about the cohomology
groups `H^q(ℙⁿ_R, 𝒪(d))`, and nothing here mentions cohomology.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open TopologicalSpace Opposite
open Stacks.PartialLaurent

universe u

namespace Stacks.ProjectiveCohomology

/-! ### Clearing the denominator of a single fraction -/

section Fraction

variable {A : Type u} [CommRing A] (F : A)

/-- In `A[1/F]`, `F ^ m • (a / F ^ m) = a / 1`. -/
theorem pow_smul_mk_pow (a : A) (m : ℕ) :
    (F ^ m) • (LocalizedModule.mk a ⟨F ^ m, by exact ⟨m, rfl⟩⟩ : LocalizedModule.Away F A) =
      LocalizedModule.mk a 1 := by
  rw [LocalizedModule.smul'_mk,
    show (F ^ m) • a = (⟨F ^ m, by exact ⟨m, rfl⟩⟩ : Submonoid.powers F) • a from rfl,
    LocalizedModule.mk_cancel]

end Fraction

/-! ### Naturality of the standard-open identification, for a general graded ring -/

section Graded

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {k l : ℕ}

/-- **The standard-open identification of the sections of a twist is natural in the standard
open.** Restricting a section of `𝒪(d)` from `D₊(f)` to a smaller standard open `D₊(g)` and then
reading it as a degree-zero fraction is the same as reading it on `D₊(f)` and applying the
canonical degree-zero restriction map of [Stacks, Tag 01M4]. -/
theorem standardOpenEquivTwist_map_homOfLE
    (hf : f ∈ 𝒜 k) (hk : 0 < k) (hg : g ∈ 𝒜 l) (hl : 0 < l)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (d : ℤ)
    (x : (twistingSheaf 𝒜 d).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 d) hg hl
        (((twistingSheaf 𝒜 d).val.map (homOfLE hfg).op).hom x) =
      (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 (twistGrading (S := A) 𝒜 d) f g
          ⟨k, hk, hf⟩ ⟨l, hl, hg⟩ hfg).degreeZeroMap
        (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 d) hf hk x) := by
  obtain ⟨a, rfl⟩ :=
    (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 d) hf hk).symm.surjective x
  have key : ((twistingSheaf 𝒜 d).val.map (homOfLE hfg).op).hom
        ((associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 d) hf hk).symm a) =
      (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 d) hg hl).symm
        ((ProjectiveSpectrum.moduleRestrictionMaps 𝒜 (twistGrading (S := A) 𝒜 d) f g
          ⟨k, hk, hf⟩ ⟨l, hl, hg⟩ hfg).degreeZeroMap a) :=
    ProjectiveSpectrum.Proj.degreeZeroToSection_restriction 𝒜 (twistGrading (S := A) 𝒜 d) f g
      ⟨k, hk, hf⟩ ⟨l, hl, hg⟩ hfg a
  rw [key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- **The same square, read on the degree-`d` part of the localization.** There the restriction
map of `𝒪(d)` becomes the map of ordinary localizations `A[1/f] → A[1/g]`. -/
theorem coe_sectionsTwistEquivAwayGrading_map_homOfLE
    (hf : f ∈ 𝒜 k) (hk : 0 < k) (hg : g ∈ 𝒜 l) (hl : 0 < l)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (d : ℤ)
    (x : (twistingSheaf 𝒜 d).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((sectionsTwistEquivAwayGrading 𝒜 hg hl d
          (((twistingSheaf 𝒜 d).val.map (homOfLE hfg).op).hom x) : LocalizedModule.Away g A)) =
      (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 (twistGrading (S := A) 𝒜 d) f g
          ⟨k, hk, hf⟩ ⟨l, hl, hg⟩ hfg).localizedMap
        ((sectionsTwistEquivAwayGrading 𝒜 hf hk d x : LocalizedModule.Away f A)) :=
  ((coe_sectionsTwistEquivAwayGrading 𝒜 hg hl d
          (((twistingSheaf 𝒜 d).val.map (homOfLE hfg).op).hom x)).trans
      (congrArg Subtype.val
        (standardOpenEquivTwist_map_homOfLE 𝒜 hf hk hg hl hfg d x))).trans
    (((ProjectiveSpectrum.moduleRestrictionMaps 𝒜 (twistGrading (S := A) 𝒜 d) f g
          ⟨k, hk, hf⟩ ⟨l, hl, hg⟩ hfg).degreeZeroMap_val _).trans
      (congrArg _ (coe_sectionsTwistEquivAwayGrading 𝒜 hf hk d x).symm))

end Graded

/-! ### The restriction maps between the Čech terms of the standard cover -/

section Polynomial

variable {n q r : ℕ} (R : Type u) [CommRing R]
  (s : Fin (r + 1) → Fin (n + 1)) (t : Fin (q + 1) → Fin (n + 1))

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chart intersection at `t` is contained in the one at `s` whenever every coordinate
inverted at `s` is inverted at `t`. -/
theorem basicOpen_prod_X_le (hst : Set.range s ⊆ Set.range t) :
    ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (∏ j, MvPolynomial.X (t j)) ≤
      ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (∏ j, MvPolynomial.X (s j)) := by
  obtain ⟨c, hc⟩ := prod_X_dvd_prod_X_pow R s t hst
  rw [← ProjectiveSpectrum.basicOpen_pow (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (∏ j, MvPolynomial.X (t j)) (r + 1) (Nat.succ_pos r), hc]
  exact ProjectiveSpectrum.basicOpen_mul_le_left _ _ _

/-- **`chartTransition` is the only map between two Čech terms which is linear over the
polynomial ring and is the identity on polynomials.** The map is not assumed to be additive. -/
theorem eq_chartTransition_of_algebraMap (hst : Set.range s ⊆ Set.range t)
    (ψ : chartRing R s → chartRing R t)
    (hsmul : ∀ (c : MvPolynomial (Fin (n + 1)) R) (z : chartRing R s), ψ (c • z) = c • ψ z)
    (halg : ∀ a : MvPolynomial (Fin (n + 1)) R,
      ψ (algebraMap (MvPolynomial (Fin (n + 1)) R) (chartRing R s) a) =
        algebraMap (MvPolynomial (Fin (n + 1)) R) (chartRing R t) a)
    (z : chartRing R s) :
    ψ z = chartTransition R s t hst z := by
  induction z using LocalizedModule.induction_on with
  | h a w =>
    obtain ⟨_, m, rfl⟩ := w
    have hu : IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) R) (chartRing R t)
        ((∏ j, MvPolynomial.X (s j)) ^ m)) := by
      rw [map_pow]
      exact (isUnit_algebraMap_prod_X R s t hst).pow m
    refine hu.mul_left_cancel ?_
    have hL : algebraMap (MvPolynomial (Fin (n + 1)) R) (chartRing R t)
          ((∏ j, MvPolynomial.X (s j)) ^ m) *
            ψ (LocalizedModule.mk a
              ⟨(∏ j, MvPolynomial.X (s j)) ^ m, by exact ⟨m, rfl⟩⟩) =
        algebraMap (MvPolynomial (Fin (n + 1)) R) (chartRing R t) a := by
      rw [← Algebra.smul_def, ← hsmul, pow_smul_mk_pow]
      exact halg a
    have hR : algebraMap (MvPolynomial (Fin (n + 1)) R) (chartRing R t)
          ((∏ j, MvPolynomial.X (s j)) ^ m) *
            chartTransition R s t hst (LocalizedModule.mk a
              ⟨(∏ j, MvPolynomial.X (s j)) ^ m, by exact ⟨m, rfl⟩⟩) =
        algebraMap (MvPolynomial (Fin (n + 1)) R) (chartRing R t) a := by
      rw [← chartTransition_algebraMap R s t hst ((∏ j, MvPolynomial.X (s j)) ^ m), ← map_mul,
        ← Algebra.smul_def, pow_smul_mk_pow]
      exact chartTransition_algebraMap R s t hst a
    rw [hL, hR]

/-- **The localization map of [Stacks, Tag 01M4] between two chart intersections is
`chartTransition`.** -/
theorem localizedMap_eq_chartTransition (hst : Set.range s ⊆ Set.range t) (d : ℤ)
    (z : chartRing R s) :
    (ProjectiveSpectrum.moduleRestrictionMaps
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d)
        (∏ j, MvPolynomial.X (s j)) (∏ j, MvPolynomial.X (t j))
        ⟨r + 1, Nat.succ_pos r, prod_X_mem_degree R s⟩
        ⟨q + 1, Nat.succ_pos q, prod_X_mem_degree R t⟩
        (basicOpen_prod_X_le R s t hst)).localizedMap z =
      chartTransition R s t hst z :=
  eq_chartTransition_of_algebraMap R s t hst _
    (fun c y => LinearMap.CompatibleSMul.map_smul _ c y)
    (fun a => (ProjectiveSpectrum.moduleRestrictionMaps
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d)
      (∏ j, MvPolynomial.X (s j)) (∏ j, MvPolynomial.X (t j))
      ⟨r + 1, Nat.succ_pos r, prod_X_mem_degree R s⟩
      ⟨q + 1, Nat.succ_pos q, prod_X_mem_degree R t⟩
      (basicOpen_prod_X_le R s t hst)).map_mk a) z

/-- **The restriction map of `𝒪(d)` between two intersections of standard coordinate charts of
`Proj R[T₀, …, Tₙ]` is `chartTransition`**, under the identifications
`Stacks.ProjectiveCohomology.sectionsTwistProdXEquiv` of the sections with the degree-`d` parts of
the localizations. -/
theorem coe_sectionsTwistProdXEquiv_map_homOfLE (hst : Set.range s ⊆ Set.range t) (d : ℤ)
    (x : (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj
      (op (ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (∏ j, MvPolynomial.X (s j))))) :
    ((sectionsTwistProdXEquiv R t d
        (((twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.map
          (homOfLE (basicOpen_prod_X_le R s t hst)).op).hom x) : chartRing R t)) =
      chartTransition R s t hst ((sectionsTwistProdXEquiv R s d x : chartRing R s)) :=
  (coe_sectionsTwistEquivAwayGrading_map_homOfLE
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (prod_X_mem_degree R s) (Nat.succ_pos r)
      (prod_X_mem_degree R t) (Nat.succ_pos q) (basicOpen_prod_X_le R s t hst) d x).trans
    (localizedMap_eq_chartTransition R s t hst d _)

/-- The restriction map of `𝒪(d)` between two intersections of standard coordinate charts is
`chartTransition`, read through `Stacks.ProjectiveCohomology.sectionsTwistProdXEquivWeightSpan`. -/
theorem coe_sectionsTwistProdXEquivWeightSpan_map_homOfLE
    (hst : Set.range s ⊆ Set.range t) (d : ℤ)
    (x : (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj
      (op (ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (∏ j, MvPolynomial.X (s j))))) :
    ((sectionsTwistProdXEquivWeightSpan R t d
        (((twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.map
          (homOfLE (basicOpen_prod_X_le R s t hst)).op).hom x) : chartRing R t)) =
      chartTransition R s t hst
        ((sectionsTwistProdXEquivWeightSpan R s d x : chartRing R s)) :=
  coe_sectionsTwistProdXEquiv_map_homOfLE R s t hst d x

/-- **The restriction maps of `𝒪(d)` between intersections of standard coordinate charts carry
each Laurent weight piece into the weight piece of the same weight.** -/
theorem mem_chartWeight_sectionsTwistProdXEquiv_map_homOfLE
    (hst : Set.range s ⊆ Set.range t) (d : ℤ) (e : Fin (n + 1) →₀ ℤ)
    (x : (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj
      (op (ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (∏ j, MvPolynomial.X (s j)))))
    (hx : ((sectionsTwistProdXEquiv R s d x : chartRing R s)) ∈ chartWeight R s e) :
    ((sectionsTwistProdXEquiv R t d
        (((twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.map
          (homOfLE (basicOpen_prod_X_le R s t hst)).op).hom x) : chartRing R t)) ∈
      chartWeight R t e := by
  rw [coe_sectionsTwistProdXEquiv_map_homOfLE]
  exact chartTransition_mem_chartWeight R s t hst e hx

end Polynomial

end Stacks.ProjectiveCohomology

end
