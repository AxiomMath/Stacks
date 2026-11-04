module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCechCases

/-!
# The Čech complex of a twist on projective space, and its cohomology

Let `R` be a commutative ring. Projective `n`-space over `R` is covered by the `n + 1` standard
opens `D₊(T₀), …, D₊(Tₙ)`, and the ordered Čech complex of that cover for the twist `𝒪(d)` is
written down in the monomial model as the submodules
`Stacks.ProjectiveSpace.Cohomology.laurentCechCochains R n d q` of
`Stacks.ProjectiveSpace.Cohomology.LaurentCochain R n` together with the differential
`Stacks.ProjectiveSpace.Cohomology.laurentCechDiffRestrict`. This file assembles those modules
into a genuine cochain complex `Stacks.ProjectiveSpace.Cohomology.laurentCechComplex` of
`R`-modules, and restates the three cases of the displayed equation of [Stacks, Tag 01XU]
— computed over `TwistCechCases.lean` in terms of cocycles, coboundaries and quotients — as
statements about the homology of that one complex:

* in degree `0` the homology is the degree-`d` part of `R[T₀, …, Tₙ]`;
* in every degree other than `0` and `n` the complex is exact, so its homology is zero;
* in degree `n` the homology is `Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`.

As in `TwistCechCases.lean`, the first and third cases are stated for `n = m + 1 ≥ 1`: the
displayed equation is ill-formed at `n = 0`, where its first and third rows would both apply and
would disagree.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.laurentCechComplex`: the ordered Čech complex of the
  standard cover of `ℙⁿ_R` for `𝒪(d)`, in the monomial model, as a cochain complex of
  `R`-modules indexed by `ℕ`.
* `Stacks.ProjectiveSpace.Cohomology.homologyZeroIso`: its degree-zero homology is the degree-`d`
  part of `R[T₀, …, Tₙ]`.
* `Stacks.ProjectiveSpace.Cohomology.homologyTopIso`: its degree-`n` homology is the `R`-dual of
  the degree-`(-n-1-d)` part of `R[T₀, …, Tₙ]`.
* `Stacks.ProjectiveSpace.Cohomology.TwistCechComplexCohomology`: the three cases, bundled.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.laurentCechDiffRestrict_comp_self`: the Čech differential
  squares to zero, which is what makes the complex a complex.
* `Stacks.ProjectiveSpace.Cohomology.exactAt_laurentCechComplex` and
  `Stacks.ProjectiveSpace.Cohomology.isZero_homology_laurentCechComplex`: **the Čech complex is
  exact, equivalently has vanishing homology, in every degree other than `0` and `n`.**
* `Stacks.ProjectiveSpace.Cohomology.twistCechComplexCohomology`: **the three cases of the
  displayed equation of [Stacks, Tag 01XU], as a computation of the homology of the Čech complex
  of the standard cover.**

## Implementation notes

The complex is indexed by `ℕ` with `ComplexShape.up ℕ`, so degree `0` has no incoming
differential and, because there are no cochains above degree `n`, degree `n` has no outgoing one.
The two non-vanishing degrees are therefore reached through
`HomologicalComplex.isoHomologyπ` and `HomologicalComplex.isoHomologyι`, which identify the
homology with the cycles and with the opcycles respectively; that is what turns the cocycle
description of degree `0` and the cokernel description of degree `n` proved in
`TwistCechCases.lean` into statements about homology.

The differentials produced by `CochainComplex.of` are only propositionally — not definitionally —
equal to the maps handed to it, since the construction branches on an equality of indices.
`laurentCechComplex_d` is the lemma that performs that step, and
`laurentCechComplex` is made transparent locally so that the submodules of the ambient cochain
modules appearing on either side of it are recognised as living in the same type.

No statement in *this file* is a statement about the sheaf cohomology `H^q(ℙⁿ_R, 𝒪(d))`. The
passage from this explicit complex to sheaf cohomology is proved downstream, as
`Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoLaurentHomology` of
`ProjectiveSpace/Cohomology/SerreComputation.lean`: that file identifies `laurentCechComplex`
with the ordered Čech complex of the standard cover and that complex's homology with sheaf
cohomology.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {n : ℕ} {d : ℤ} {q : ℕ}

/-! ### The Čech complex -/

/-- **The Čech differential of the standard cover of `ℙⁿ_R` squares to zero** on the degree-`q`
cochains for `𝒪(d)`: the composite of the differentials out of degrees `q` and `q + 1` is the
zero map. -/
theorem laurentCechDiffRestrict_comp_self (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ) :
    (laurentCechDiffRestrict R n d (q + 1)).comp (laurentCechDiffRestrict R n d q) = 0 :=
  LinearMap.ext fun c =>
    LinearMap.mem_ker.1 (range_laurentCechDiffRestrict_le_ker (LinearMap.mem_range_self _ c))

/-- **The ordered Čech complex of the standard cover of `ℙⁿ_R` for `𝒪(d)`, in the monomial
model**: the cochain complex of `R`-modules whose degree-`q` term is
`Stacks.ProjectiveSpace.Cohomology.laurentCechCochains R n d q` and whose differential is
`Stacks.ProjectiveSpace.Cohomology.laurentCechDiffRestrict`. -/
def laurentCechComplex (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of R (laurentCechCochains R n d q))
    (fun q => ModuleCat.ofHom (laurentCechDiffRestrict R n d q))
    (fun q => ModuleCat.hom_ext (laurentCechDiffRestrict_comp_self R n d q))

attribute [local implicit_reducible] laurentCechComplex

/-- The degree-`q` term of the Čech complex is the module of degree-`q` Čech cochains of the
standard cover of `ℙⁿ_R` for `𝒪(d)`. -/
@[simp]
theorem laurentCechComplex_X (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ) :
    (laurentCechComplex R n d).X q = ModuleCat.of R (laurentCechCochains R n d q) :=
  rfl

/-- The differential of the Čech complex from degree `q` to degree `q + 1` is the Čech
differential. -/
@[simp]
theorem laurentCechComplex_d (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ) :
    (laurentCechComplex R n d).d q (q + 1)
      = ModuleCat.ofHom (laurentCechDiffRestrict R n d q) := by
  apply CochainComplex.of_d

/-- **Above degree `n` the Čech differential of the standard cover of `ℙⁿ_R` is the zero map**,
because the module of degree-`(q + 1)` cochains it lands in is itself zero. -/
theorem laurentCechDiffRestrict_eq_zero_of_lt (hq : n < q + 1) :
    laurentCechDiffRestrict R n d q = 0 := by
  have hsub : Subsingleton (laurentCechCochains R n d (q + 1)) := by
    rw [laurentCechCochains_eq_bot hq]
    infer_instance
  exact LinearMap.ext fun c => Subsingleton.elim _ _

/-- Above degree `n` the differentials of the Čech complex of the standard cover of `ℙⁿ_R`
vanish; in particular the complex has no differential out of its top degree `n`. -/
theorem laurentCechComplex_d_eq_zero_of_lt (hq : n < q + 1) :
    (laurentCechComplex R n d).d q (q + 1) = 0 := by
  rw [laurentCechComplex_d, laurentCechDiffRestrict_eq_zero_of_lt hq, ModuleCat.ofHom_zero]

/-! ### The vanishing degrees -/

/-- **The Čech complex of `𝒪(d)` on `ℙⁿ_R` is exact in every degree other than `0` and `n`**, for
every commutative ring `R` and every integer `d`: in degree `q + 1 ≠ n` the cocycles are exactly
the coboundaries from degree `q`. -/
theorem exactAt_laurentCechComplex (hq : q + 1 ≠ n) :
    (laurentCechComplex R n d).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' (laurentCechComplex R n d) q (q + 1) (q + 1 + 1)
    (by simp) (by simp), ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, laurentCechComplex_d]
  exact range_laurentCechDiffRestrict_of_ne hq

/-- **The homology of the Čech complex of `𝒪(d)` on `ℙⁿ_R` vanishes in every degree other than
`0` and `n`**, for every commutative ring `R` and every integer `d`. -/
theorem isZero_homology_laurentCechComplex (hq : q + 1 ≠ n) :
    IsZero ((laurentCechComplex R n d).homology (q + 1)) :=
  (exactAt_laurentCechComplex hq).isZero_homology

/-! ### The two non-vanishing degrees -/

/-- **The degree-zero homology of the Čech complex of the standard cover of `ℙⁿ_R`, `n = m + 1`,
is the degree-`d` part of `R[T₀, …, Tₙ]`**, read as the chart with no variable inverted. Nothing
maps into degree `0`, so the homology there is the module of degree-zero cocycles, which
`Stacks.ProjectiveSpace.Cohomology.laurentCechCohomologyZeroEquiv` computes. -/
def homologyZeroIso (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    (laurentCechComplex R (m + 1) d).homology 0 ≅
      ModuleCat.of R (twistChart R (m + 1) d (∅ : Set (Fin (m + 1 + 1)))) :=
  ((laurentCechComplex R (m + 1) d).isoHomologyπ 0 0 (by simp)
        ((laurentCechComplex R (m + 1) d).shape 0 0 (by simp))).symm ≪≫
    (laurentCechComplex R (m + 1) d).cyclesIsoSc' 0 0 (0 + 1) (by simp) (by simp) ≪≫
    ShortComplex.moduleCatCyclesIso _ ≪≫
    LinearEquiv.toModuleIso
      ((LinearEquiv.ofEq _ _ (by
          simp only [HomologicalComplex.shortComplexFunctor'_obj_g, laurentCechComplex_d]
          rfl)).trans
        (laurentCechCohomologyZeroEquiv (R := R) (n := m + 1) (d := d) m.succ_pos).symm)

/-- **The degree-`n` homology of the Čech complex of the standard cover of `ℙⁿ_R`, `n = m + 1`,
is the `R`-dual of the degree-`(-n-1-d)` part of `R[T₀, …, Tₙ]`**, via the residue pairing of
`Stacks.ProjectiveSpace.Cohomology.topDualEquiv`. Nothing maps out of degree `n`, so the homology
there is the cokernel of the differential from degree `n - 1`, which
`Stacks.ProjectiveSpace.Cohomology.laurentCechCohomologyTopEquiv` computes. -/
def homologyTopIso (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    (laurentCechComplex R (m + 1) d).homology (m + 1) ≅
      ModuleCat.of R (twistChart R (m + 1) (-d - (((m + 1 : ℕ) : ℤ) + 1))
        (∅ : Set (Fin (m + 1 + 1))) →ₗ[R] R) :=
  (laurentCechComplex R (m + 1) d).isoHomologyι (m + 1) (m + 1 + 1) (by simp)
      (laurentCechComplex_d_eq_zero_of_lt (by omega)) ≪≫
    (laurentCechComplex R (m + 1) d).opcyclesIsoSc' m (m + 1) (m + 1 + 1) (by simp) (by simp) ≪≫
    ShortComplex.moduleCatOpcyclesIso _ ≪≫
    LinearEquiv.toModuleIso
      ((Submodule.quotEquivOfEq _ _ (by
          simp only [HomologicalComplex.shortComplexFunctor'_obj_f, laurentCechComplex_d]
          rfl)).trans
        (laurentCechCohomologyTopEquiv R m d))

/-! ### The three cases -/

/-- The three cases of the displayed equation of [Stacks, Tag 01XU], for the homology of the Čech
complex of the standard cover of `ℙ^{m+1}_R` with coefficients in `𝒪(d)`: the degree-zero
homology is the degree-`d` part of `R[T₀, …, T_{m+1}]`, the homology vanishes in every degree
other than `0` and `m + 1`, and the degree-`(m+1)` homology is the `R`-dual of the
degree-`(-m-2-d)` part of `R[T₀, …, T_{m+1}]`. -/
structure TwistCechComplexCohomology (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) where
  /-- `H⁰` is the degree-`d` part of `R[T₀, …, T_{m+1}]`. -/
  degreeZero : (laurentCechComplex R (m + 1) d).homology 0 ≅
    ModuleCat.of R (twistChart R (m + 1) d (∅ : Set (Fin (m + 1 + 1))))
  /-- `H^q = 0` for `q ≠ 0, m + 1`. -/
  vanishing : ∀ q : ℕ, q + 1 ≠ m + 1 →
    IsZero ((laurentCechComplex R (m + 1) d).homology (q + 1))
  /-- `H^{m+1}` is the `R`-dual of the degree-`(-m-2-d)` part of `R[T₀, …, T_{m+1}]`. -/
  degreeTop : (laurentCechComplex R (m + 1) d).homology (m + 1) ≅
    ModuleCat.of R (twistChart R (m + 1) (-d - (((m + 1 : ℕ) : ℤ) + 1))
      (∅ : Set (Fin (m + 1 + 1))) →ₗ[R] R)

/-- **The three cases of the displayed equation of [Stacks, Tag 01XU], as a computation of the
homology of the Čech complex of the standard cover of `ℙⁿ_R`, `n = m + 1 ≥ 1`.** Every case holds
for every commutative ring `R` and every integer `d`; the degree-`d` part of `R[T₀, …, Tₙ]` is
read as the chart with no variable inverted, which vanishes in negative degrees, so the first and
third cases are uniform in `d` exactly as the source's rows are. -/
def twistCechComplexCohomology (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    TwistCechComplexCohomology R m d where
  degreeZero := homologyZeroIso R m d
  vanishing _ hq := isZero_homology_laurentCechComplex hq
  degreeTop := homologyTopIso R m d

end Stacks.ProjectiveSpace.Cohomology

end
