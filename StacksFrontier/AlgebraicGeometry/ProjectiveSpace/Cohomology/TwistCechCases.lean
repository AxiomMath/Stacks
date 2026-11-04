module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.MiddleDegrees
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TopDuality

/-!
# The three cases of the Čech cohomology of a twist on projective space

Let `R` be a commutative ring and let `n = m + 1 ≥ 1`. Projective `n`-space over `R` is covered
by the `n + 1` standard opens `D₊(T₀), …, D₊(Tₙ)`, and the ordered Čech complex of that cover
for the twist `𝒪(d)` is written down in the monomial model as the submodules
`Stacks.ProjectiveSpace.Cohomology.laurentCechCochains R n d q` of
`Stacks.ProjectiveSpace.Cohomology.LaurentCochain R n` with the differential
`Stacks.ProjectiveSpace.Cohomology.laurentCechDiffRestrict`. This file collects the cohomology
of that one complex, in all degrees at once, into the three cases of the displayed equation of
[Stacks, Tag 01XU]:

* in degree `0` it is the degree-`d` part of `R[T₀, …, Tₙ]`;
* in every degree other than `0` and `n` it vanishes;
* in degree `n` it is `Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`.

Two of the three are assembled from known results — the contracting homotopy of
`Stacks.ProjectiveSpace.Cohomology.exists_laurentCechDiff_eq` for the middle degrees, the
absence of cochains above degree `n`, and the common-value argument of
`Stacks.ProjectiveSpace.Cohomology.laurentCechCohomologyZeroEquiv` for degree zero. The third
needs two new steps, both supplied here: the degree-`n` cochains are the sections on the total
intersection, because the only index set of size `n + 1` is the whole of `{0, …, n}`
(`topCochainEquiv`), and under that identification the image of the Čech differential out of
degree `n - 1` is the image of
`Stacks.ProjectiveSpace.Cohomology.topCechDiff` (`map_range_laurentCechDiffRestrict_top`), whose
cokernel is dualized by
`Stacks.ProjectiveSpace.Cohomology.topCechCohomologyDualEquiv`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.topCochainEquiv`: the degree-`n` Čech cochains are the
  degree-`d` Laurent sections on the total intersection `D₊(T₀ ⋯ Tₙ)`.
* `Stacks.ProjectiveSpace.Cohomology.TwistCechCohomology`: the three cases, bundled.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.map_range_laurentCechDiffRestrict_top`: the image of the
  Čech differential out of degree `n - 1` is the image of
  `Stacks.ProjectiveSpace.Cohomology.topCechDiff`.
* `Stacks.ProjectiveSpace.Cohomology.laurentCechCohomologyTopEquiv`: **the top-degree Čech
  cohomology of the standard cover is `Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`.**
* `Stacks.ProjectiveSpace.Cohomology.range_laurentCechDiffRestrict_of_ne`: **the Čech cohomology
  vanishes in every degree other than `0` and `n`**, in one statement covering both the middle
  degrees and the degrees above `n`.
* `Stacks.ProjectiveSpace.Cohomology.twistCechCohomology`: **the three cases of the displayed
  equation of [Stacks, Tag 01XU], for the Čech cohomology of the standard cover.**

## Implementation notes

**No tag attribute is attached *in this file*, and the omission is deliberate.** The displayed
equation of [Stacks, Tag 01XU] is a statement about the sheaf cohomology `H^q(ℙⁿ_R, 𝒪(d))`, and
what is assembled here is the cohomology of one explicit complex of `R`-modules. The passage
between the two is [Stacks, Tag 01XD], available for the Čech complex of [Stacks, Tag 01EP] of a
cover with affine finite intersections as
`Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived`, and the identification of the complex
used here with that one is **proved**, downstream:
`Stacks.ProjectiveSpace.Cohomology.twistOrderedComplexIsoLaurent` of
`ProjectiveSpace/Cohomology/SerreComputation.lean` identifies the ordered Čech complex of the
standard cover with `laurentCechComplex`, `sheafCohomologyIsoOrderedHomology` in the same file
crosses from sheaf cohomology to that ordered complex's homology through [Stacks, Tags 01XD,
01FJ and 01FM], and their composite `twistCohomologyIsoLaurentHomology` is
`H^q(ℙⁿ_R, 𝒪(d)) ≅ (laurentCechComplex R n d).homology q`. So every case assembled here *is* a
statement about `H^q(ℙⁿ_R, 𝒪(d))` once transported, and the tag attributes sit on the
transported forms, in `SerreComputation.lean` and `TwistCohomologyMonomial.lean`. This file is
the reduction of the whole equation to that identification, not a statement waiting on it.

**Why `n` is `m + 1`.** The displayed equation is ill-formed at `n = 0`: its first row applies
when `q = 0` and its third when `q = n`, so at `n = 0` both apply, and they disagree — for
`n = 0` and `d ≥ 0` the first gives `(R[T₀])_d = R` and the third gives
`Hom_R((R[T₀])_{-1-d}, R) = 0`. So `n ≥ 1` is a standing hypothesis of the equation and not an
artefact of the model; writing `n = m + 1` carries it, and also gives the top degree a
predecessor `m` to index the differential by.

**The degree-`d` part of `R[T₀, …, Tₙ]` is the chart with no variable inverted.** That is
`Stacks.ProjectiveSpace.Cohomology.twistChart R n d ∅`, which
`Stacks.ProjectiveSpace.Cohomology.twistChartEmptyLinearEquiv` identifies with
`MvPolynomial.homogeneousSubmodule` for `0 ≤ d` and
`Stacks.ProjectiveSpace.Cohomology.twistChart_eq_bot_of_neg` kills for `d < 0`. Using it rather
than a new integer-indexed submodule of `MvPolynomial` is what makes the first and third cases
uniform in `d`, as the source's rows are.

**The vanishing case is stated as an equality of coboundaries and cocycles** rather than as
`IsZero` of a quotient, matching
`Stacks.ProjectiveSpace.Cohomology.range_laurentCechDiffRestrict`; above degree `n` it holds
because the ambient module of cochains is itself zero, so the two submodules are both the whole
of a zero module.

## References

* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open Finsupp

universe u

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {n : ℕ} {d : ℤ} {q : ℕ}

/-! ### The degree-`n` cochains are the sections on the total intersection -/

/-- An index set of `n + 1` of the `n + 1` coordinates of `ℙⁿ_R` is all of them. -/
theorem eq_univ_of_card_eq (S : Finset (Fin (n + 1))) (hS : S.card = n + 1) :
    S = Finset.univ := by
  rw [← Finset.card_eq_iff_eq_univ]
  simpa using hS

/-- **The degree-`n` Čech cochains of the standard cover of `ℙⁿ_R` are the degree-`d` Laurent
sections on the total intersection `D₊(T₀ ⋯ Tₙ)`**: a cochain of that degree is concentrated on
the index sets of size `n + 1`, of which there is only one. -/
def topCochainMap (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    laurentCechCochains R (m + 1) d (m + 1) →ₗ[R]
      twistChart R (m + 1) d (Set.univ : Set (Fin (m + 1 + 1))) where
  toFun c := ⟨(c : LaurentCochain R (m + 1)) Finset.univ, by
    have h := (mem_laurentCechCochains.1 c.2).1 Finset.univ
    rwa [Finset.coe_univ] at h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `topCochainMap` is evaluation at the total index set. -/
@[simp]
theorem coe_topCochainMap_apply (m : ℕ) (c : laurentCechCochains R (m + 1) d (m + 1)) :
    (topCochainMap R m d c : (Fin (m + 1 + 1) → ℤ) →₀ R)
      = (c : LaurentCochain R (m + 1)) Finset.univ :=
  rfl

/-- **The degree-`n` Čech cochains are the sections on the total intersection**, as an
equivalence: a degree-`n` cochain is determined by, and may be prescribed arbitrarily at, its
value on the total index set. -/
def topCochainEquiv (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    laurentCechCochains R (m + 1) d (m + 1) ≃ₗ[R]
      twistChart R (m + 1) d (Set.univ : Set (Fin (m + 1 + 1))) := by
  classical
  refine LinearEquiv.ofBijective (topCochainMap R m d) ⟨fun c₁ c₂ h => ?_, fun x => ?_⟩
  · refine Subtype.ext (funext fun S => ?_)
    by_cases hS : S.card = m + 1 + 1
    · rw [eq_univ_of_card_eq S hS]
      exact congrArg (fun y : twistChart R (m + 1) d (Set.univ : Set (Fin (m + 1 + 1))) =>
        (y : (Fin (m + 1 + 1) → ℤ) →₀ R)) h
    · rw [(mem_laurentCechCochains.1 c₁.2).2 S hS, (mem_laurentCechCochains.1 c₂.2).2 S hS]
  · refine ⟨⟨fun S => if S = Finset.univ then (x : (Fin (m + 1 + 1) → ℤ) →₀ R) else 0,
      ⟨fun S => ?_, fun S hS => ?_⟩⟩, ?_⟩
    · change (if S = Finset.univ then (x : (Fin (m + 1 + 1) → ℤ) →₀ R) else 0)
        ∈ twistChart R (m + 1) d (S : Set (Fin (m + 1 + 1)))
      by_cases hS : S = Finset.univ
      · rw [ite_eq_left hS, hS, Finset.coe_univ]
        exact x.2
      · rw [ite_eq_right hS]
        exact zero_mem _
    · change (if S = Finset.univ then (x : (Fin (m + 1 + 1) → ℤ) →₀ R) else 0) = 0
      refine ite_eq_right fun hSu => hS ?_
      rw [hSu, Finset.card_univ, Fintype.card_fin]
    · exact Subtype.ext (by simp)

/-- The underlying cochain of the inverse of `topCochainEquiv` is the given section on the total
index set and zero elsewhere. -/
theorem topCochainEquiv_symm_apply_apply (m : ℕ)
    (x : twistChart R (m + 1) d (Set.univ : Set (Fin (m + 1 + 1))))
    (S : Finset (Fin (m + 1 + 1))) :
    (((topCochainEquiv R m d).symm x : laurentCechCochains R (m + 1) d (m + 1)) :
        LaurentCochain R (m + 1)) S
      = if S = Finset.univ then (x : (Fin (m + 1 + 1) → ℤ) →₀ R) else 0 := by
  classical
  by_cases hS : S.card = m + 1 + 1
  · rw [eq_univ_of_card_eq S hS, ite_eq_left rfl]
    exact congrArg (fun y : twistChart R (m + 1) d (Set.univ : Set (Fin (m + 1 + 1))) =>
        (y : (Fin (m + 1 + 1) → ℤ) →₀ R))
      ((topCochainEquiv R m d).apply_symm_apply x)
  · rw [(mem_laurentCechCochains.1 ((topCochainEquiv R m d).symm x).2).2 S hS,
      ite_eq_right fun hSu => hS (by rw [hSu, Finset.card_univ, Fintype.card_fin])]

/-! ### The top-degree Čech cohomology -/

/-- `topCochainEquiv` is `topCochainMap`, hence evaluation at the total index set. -/
@[simp]
theorem coe_topCochainEquiv_apply (m : ℕ) (c : laurentCechCochains R (m + 1) d (m + 1)) :
    (topCochainEquiv R m d c : (Fin (m + 1 + 1) → ℤ) →₀ R)
      = (c : LaurentCochain R (m + 1)) Finset.univ :=
  rfl

/-- Through `topCochainEquiv` the Čech differential out of degree `n - 1` is
`Stacks.ProjectiveSpace.Cohomology.laurentTopCechDiff`. -/
theorem coe_topCochainEquiv_laurentCechDiffRestrict (m : ℕ)
    (b : laurentCechCochains R (m + 1) d m) :
    (topCochainEquiv R m d (laurentCechDiffRestrict R (m + 1) d m b) :
        (Fin (m + 1 + 1) → ℤ) →₀ R)
      = laurentTopCechDiff R m d b :=
  rfl

/-- **The image of the Čech differential out of degree `n - 1`, read on the sections of the total
intersection, is the image of `Stacks.ProjectiveSpace.Cohomology.topCechDiff`.** This is what
makes the top-degree computation of `TopDegree.lean` and `TopCech.lean` a computation of
the degree-`n` cohomology of the Čech complex of the standard cover. -/
theorem map_range_laurentCechDiffRestrict_top (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    Submodule.map (topCochainEquiv R m d).toLinearMap
        (LinearMap.range (laurentCechDiffRestrict R (m + 1) d m))
      = (LinearMap.range (topCechDiff R (m + 1) d)).comap
          (twistChart R (m + 1) d (Set.univ : Set (Fin (m + 1 + 1)))).subtype := by
  rw [← range_laurentTopCechDiff R m d]
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, (coe_topCochainEquiv_laurentCechDiffRestrict m b).symm⟩
  · obtain ⟨b, hb⟩ := Submodule.mem_comap.1 hx
    exact ⟨laurentCechDiffRestrict R (m + 1) d m b, ⟨b, rfl⟩,
      Subtype.ext ((coe_topCochainEquiv_laurentCechDiffRestrict m b).trans hb)⟩

/-- **The top-degree case of the displayed equation of [Stacks, Tag 01XU], for the Čech
cohomology of the standard cover.** The degree-`n` cohomology of the Čech complex of the
standard cover of `ℙⁿ_R` for `𝒪(d)`, with `n = m + 1`, is the `R`-dual of the degree-`(-n-1-d)`
part of `R[T₀, …, Tₙ]`, via the residue pairing of
`Stacks.ProjectiveSpace.Cohomology.topDualEquiv`. -/
def laurentCechCohomologyTopEquiv (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    (laurentCechCochains R (m + 1) d (m + 1) ⧸
        LinearMap.range (laurentCechDiffRestrict R (m + 1) d m)) ≃ₗ[R]
      (twistChart R (m + 1) (-d - (((m + 1 : ℕ) : ℤ) + 1)) (∅ : Set (Fin (m + 1 + 1)))
        →ₗ[R] R) :=
  (Submodule.Quotient.equiv _ _ (topCochainEquiv R m d)
      (map_range_laurentCechDiffRestrict_top R m d)).trans
    (topCechCohomologyDualEquiv R (m + 1) d)

/-- **The top-degree case of the displayed equation of [Stacks, Tag 01XU], for the Čech
cohomology of the standard cover, with the polynomials written as polynomials.** For
`d ≤ -n - 1` the degree-`n` cohomology of the Čech complex of the standard cover is
`Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`; in the remaining degrees it vanishes, by
`Stacks.ProjectiveSpace.Cohomology.topCechDiff_range_eq_twistChart_univ`. -/
def laurentCechCohomologyTopPolynomialEquiv (R : Type u) [CommRing R] (m : ℕ) (d : ℤ)
    (hd : d ≤ -((m + 1 : ℕ) : ℤ) - 1) :
    (laurentCechCochains R (m + 1) d (m + 1) ⧸
        LinearMap.range (laurentCechDiffRestrict R (m + 1) d m)) ≃ₗ[R]
      (MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R
        (-d - (((m + 1 : ℕ) : ℤ) + 1)).toNat →ₗ[R] R) :=
  (Submodule.Quotient.equiv _ _ (topCochainEquiv R m d)
      (map_range_laurentCechDiffRestrict_top R m d)).trans
    (topCechCohomologyPolynomialDualEquiv R (m + 1) d hd)

/-! ### The vanishing degrees, uniformly -/

/-- **The Čech cohomology of `𝒪(d)` on `ℙⁿ_R` vanishes in every degree other than `0` and `n`**,
at the Čech level in the monomial model: the cocycles in degree `q + 1 ≠ n` are exactly the
coboundaries from degree `q`, for every `d`. Below `n` this is the contracting homotopy of
`Stacks.ProjectiveSpace.Cohomology.range_laurentCechDiffRestrict`; above `n` there are no
cochains at all, so both submodules are the whole of a zero module. -/
theorem range_laurentCechDiffRestrict_of_ne (hq : q + 1 ≠ n) :
    LinearMap.range (laurentCechDiffRestrict R n d q)
      = LinearMap.ker (laurentCechDiffRestrict R n d (q + 1)) := by
  rcases lt_or_gt_of_ne hq with h | h
  · exact range_laurentCechDiffRestrict (by omega)
  · have hbot : laurentCechCochains R n d (q + 1) = ⊥ := laurentCechCochains_eq_bot (by omega)
    have := Submodule.subsingleton_iff_eq_bot.2 hbot
    exact Subsingleton.elim _ _

/-! ### The three cases -/

/-- The three cases of the displayed equation of [Stacks, Tag 01XU], for the Čech cohomology of
the standard cover of `ℙ^{m+1}_R` with coefficients in `𝒪(d)`: the degree-zero cohomology is the
degree-`d` part of `R[T₀, …, T_{m+1}]`, the cohomology vanishes in every degree other than `0`
and `m + 1`, and the degree-`(m+1)` cohomology is the `R`-dual of the degree-`(-m-2-d)` part of
`R[T₀, …, T_{m+1}]`. -/
structure TwistCechCohomology (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) where
  /-- `H⁰` is the degree-`d` part of `R[T₀, …, T_{m+1}]`. -/
  degreeZero : LinearMap.ker (laurentCechDiffRestrict R (m + 1) d 0) ≃ₗ[R]
    twistChart R (m + 1) d (∅ : Set (Fin (m + 1 + 1)))
  /-- `H^q = 0` for `q ≠ 0, m + 1`. -/
  vanishing : ∀ q : ℕ, q + 1 ≠ m + 1 →
    LinearMap.range (laurentCechDiffRestrict R (m + 1) d q)
      = LinearMap.ker (laurentCechDiffRestrict R (m + 1) d (q + 1))
  /-- `H^{m+1}` is the `R`-dual of the degree-`(-m-2-d)` part of `R[T₀, …, T_{m+1}]`. -/
  degreeTop : (laurentCechCochains R (m + 1) d (m + 1) ⧸
      LinearMap.range (laurentCechDiffRestrict R (m + 1) d m)) ≃ₗ[R]
    (twistChart R (m + 1) (-d - (((m + 1 : ℕ) : ℤ) + 1)) (∅ : Set (Fin (m + 1 + 1))) →ₗ[R] R)

/-- **The three cases of the displayed equation of [Stacks, Tag 01XU], for the Čech cohomology of
the standard cover of `ℙⁿ_R`, `n = m + 1 ≥ 1`.** Every case holds for every commutative ring `R`
and every integer `d`; the degree-`d` part of `R[T₀, …, Tₙ]` is read as the chart with no
variable inverted, which vanishes in negative degrees, so the first and third cases are uniform
in `d` exactly as the source's rows are.

The sheaf-cohomology form of the equation is this statement transported along
`Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoLaurentHomology` of
`ProjectiveSpace/Cohomology/SerreComputation.lean`, which identifies the complex used here with
the ordered Čech complex of the standard cover (`twistOrderedComplexIsoLaurent`) and that with
sheaf cohomology ([Stacks, Tags 01XD, 01FJ and 01FM], through
`Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived`). The transport is performed in that
file, which is where the tag is attached. -/
def twistCechCohomology (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    TwistCechCohomology R m d where
  degreeZero := (laurentCechCohomologyZeroEquiv (R := R) (n := m + 1) (d := d) m.succ_pos).symm
  vanishing _ hq := range_laurentCechDiffRestrict_of_ne hq
  degreeTop := laurentCechCohomologyTopEquiv R m d

end Stacks.ProjectiveSpace.Cohomology

end
