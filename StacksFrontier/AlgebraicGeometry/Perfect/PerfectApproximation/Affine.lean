module

public import Mathlib.RingTheory.Spectrum.Prime.Module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EssentialImage
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ImmersionIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.KoszulLiftSheaf
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas

/-!
# Approximation by perfect complexes on an affine scheme

Let `R` be a commutative ring, let `f₁, …, f_r ∈ R` and let `T = V(f₁, …, f_r)`, so that
`Spec R ∖ T` is the union of the `r` basic opens `D(f_i)`. Approximation holds for a triple
`(T, E, m)` as soon as `E` is `m`-pseudo-coherent and the cohomology of `E` is supported on `T` in
all degrees `≥ m - r + 1`, and approximation by perfect complexes holds on `Spec R`. This file
contains the induction and the one-step construction of the proof of [Stacks, Tag 08EQ]; the
statement of the tag for an arbitrary closed subset whose complement is a union of `r` affine
opens is `AlgebraicGeometry.PerfectApproximation.approximationHolds_of_affineCover`, in
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/AffineCover.lean`.

## Main definitions

* `AlgebraicGeometry.PerfectApproximation.ApproximationClass`: the objects `F` of `D(𝒪_X)` with
  quasi-coherent cohomology which are `m`-pseudo-coherent and whose cohomology is supported on
  `T` in all degrees `≥ b`. For `b = m - r + 1` these are exactly the objects to which Tag 08EQ
  applies, and the induction of its proof runs on this class.

## Main results

* `AlgebraicGeometry.PerfectApproximation.approximationHolds_of_zeroLocus`: approximation holds
  for `(V(f₁, …, f_r), E, m)` whenever `E` has quasi-coherent cohomology, is `m`-pseudo-coherent,
  and has its cohomology supported on `V(f₁, …, f_r)` in all degrees `≥ m - r + 1`.
* `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_spec` and
  `AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes_spec`: approximation
  by perfect complexes holds on `Spec R`, in the two encodings of Tag 08EN.
* `AlgebraicGeometry.PerfectApproximation.approximationClass_obj₃_of_distinguished`: the class
  above passes to the cone of a map from an admissible object. This is Tag 08CD for
  pseudo-coherence, the Serre property of quasi-coherence, and the cohomology sequence of stalks
  for the support condition.
* `AlgebraicGeometry.PerfectApproximation.approximationHolds_of_oneStep_approximationClass`:
  approximation holds for every object of that class with cohomology bounded above, granted the
  one-step construction.
* `AlgebraicGeometry.PerfectApproximation.isAdmissible_shift`: a shift of a perfect object
  supported on `T` is again one.
* `Stacks.AffineTilde.exists_pow_smul_eq_zero_of_isZero_stalk_tilde` and
  `Stacks.AffineTilde.isZero_stalk_tilde_of_exists_pow_smul_eq_zero`: a module whose associated
  sheaf has vanishing stalks on `D(g)` is exactly a `g`-power torsion module. This is the
  dictionary the sheaf-level Koszul lift was missing.
* `Stacks.AffineTilde.exists_isAdmissible_koszulPowerTilde_lift_of_isZero_stalk_homology`: the
  Koszul power lift of Tag 08E3 with the *geometric* hypothesis of the source — vanishing of the
  cohomology sheaves of `F` on `⋃ᵢ D(f_i)` in the degrees `-r + 1, …, 0` — in place of the
  algebraic torsion condition.
* `Stacks.AffineTilde.exists_isAdmissible_epi_homology_zero`,
  `Stacks.AffineTilde.exists_isAdmissible_epi_homology_of_lift` and
  `Stacks.AffineTilde.exists_isAdmissible_epi_homology_of_approximationClass`: the one-step
  construction of the source's proof, first in cohomological degree zero and then in an
  arbitrary degree, from any family of Koszul lifts.

## Implementation notes

**The zero-locus form.** The source's proof writes `T = V(f₁, …, f_r)` with `r` the number of
affine opens covering `X ∖ T`. That presentation is available when the affine opens are the
basic opens `D(f_i)`, and this file treats that case: the Koszul complex on `r` elements occupies
the cohomological degrees `-r, …, 0`, and the support hypothesis `i ≥ m - r + 1` is exactly what
its torsion condition consumes. For a general cover of `X ∖ T` by `r` affine opens the two counts
differ, and the support hypothesis is matched instead against the cohomological dimension of
`X ∖ T`, which is at most `r - 1` by [Stacks, Tag 01XI]; that argument is in
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/AffineCover.lean`.

The second assertion of the tag needs only the zero-locus form: the complement of a closed
subset of `Spec R` with retrocompact complement is a finite union of basic opens, and the integer
of Tag 08EN is existentially quantified, so the cardinality of any finite presentation of `T`
will do. The case of an arbitrary affine scheme is
`AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_of_isAffine` in
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/AffineScheme.lean`, which transports
these statements along `X ≅ Spec Γ(X, 𝒪_X)`.

**Boundedness of the cohomology is derived, not assumed.** The source's proof begins "let `t` be
the largest integer such that `H^t(E) ≠ 0`", so it presupposes that the cohomology of `E`
vanishes in all large degrees. That is implied by the hypotheses: on a quasi-compact space an
`m`-pseudo-coherent object has cohomology bounded above, by
`AlgebraicGeometry.RingedSpace.exists_isZero_homology_of_isPseudoCoherentFrom`, and `Spec R` is
quasi-compact. No boundedness hypothesis is therefore carried by the statements of Tag 08EQ
below.

**The one-step construction.** The source produces the approximating object in degree `t` from a
finite generating family of the sheaf `H^t(E)`, which is of finite type by Tag 08DN. The
construction is carried out here in degree zero —
`Stacks.AffineTilde.exists_isAdmissible_epi_homology_zero` — where `H⁰(F)` is the sheaf
associated to a finite `R`-module by Tag 01PB, a generating family of that module gives
morphisms out of `R[0]` through `DerivedCategory.homologyFromSingleAddEquiv` (the structure sheaf
is not a projective object of `D(𝒪_X)`, but `R` is a projective `R`-module, and derived
sheafification is fully faithful), and each of those morphisms factors through a sheafified
Koszul complex. The general degree is reduced to degree zero by replacing `F` with `F[t]`: the
shift carries `H^n` to `H^{n + t}`, so the support condition in the degrees `-r + 1, …, 0`
becomes the source's condition in the degrees `t - r + 1, …, t`, which `t ≥ m` makes available.

**The model.** The Tag 08EQ cluster lives at `CategoryTheory.HasDerivedCategory.standard`, and
the locally small instances of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` are
global and reach this file through `AlgebraicGeometry.derivedTilde`. The standard model is
therefore selected at raised priority, as in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineDerivedPresentation.lean`; the plain
`attribute [local instance]` of
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/Defs.lean` is not enough in a file
with `AlgebraicGeometry.derivedTilde` in its import closure. Statements about `(Spec R).Modules`
that must meet the ones of
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/KoszulLiftSheaf.lean` pin the model
with a `let` in the statement instead, the device of
`Stacks.AffineTilde.exists_isAdmissible_koszulPowerTilde_lift`.

Essential surjectivity of derived sheafification is available at the standard model:
`Stacks.AffineTilde.exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard` reads it off
`Stacks.DerivedQCoh.exists_iso_derivedTildeEquiv_obj_of_isDQCoh`, which is stated at that model,
so the presentation hypothesis of the Koszul lift costs nothing beyond quasi-coherence of the
cohomology and no comparison of the two models is needed. The object of `D(R)` produced there
lives at the standard model of `D(R)`, so it is carried across to the free model of the statement
by a complex representing it.

## References

* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 08EM](https://stacks.math.columbia.edu/tag/08EM)
* [Stacks Project, Tag 08EN](https://stacks.math.columbia.edu/tag/08EN)
* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
* [Stacks Project, Tag 08DD](https://stacks.math.columbia.edu/tag/08DD)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 08CD](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Cohomological support passes to the third vertex, degree by degree.** If the first vertex
of a distinguished triangle has all its cohomology supported on `T` and the second has its
cohomology supported on `T` in all degrees `≥ b`, then so does the third.

The stalk functor at a point outside `T` is exact, so it carries the exact sequence
`H^i(E₂) ⟶ H^i(E₃) ⟶ H^{i+1}(E₁)` of cohomology sheaves to an exact sequence of modules whose
outer terms vanish. -/
theorem isZero_stalk_homology_obj₃_of_distinguished {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (T : Set X) (b : ℤ)
    (S : Triangle (DerivedCategory (_root_.SheafOfModules.{u} O)))
    (hS : S ∈ distTriang (DerivedCategory (_root_.SheafOfModules.{u} O)))
    (h₁ : CohomologySupportedOn O T S.obj₁)
    (h₂ : ∀ i : ℤ, b ≤ i → ∀ x : X, x ∉ T →
      IsZero (TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).obj
          S.obj₂).val.presheaf) x))
    (i : ℤ) (hi : b ≤ i) (x : X) (hx : x ∉ T) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).obj
        S.obj₃).val.presheaf) x) := by
  rw [← SheafOfModules.isZero_stalkFunctor_obj_iff O x]
  exact ((DerivedCategory.HomologySequence.exact₃ S hS i (i + 1) rfl).map
    (SheafOfModules.stalkFunctor O x)).isZero_of_both_isZero
    ((SheafOfModules.isZero_stalkFunctor_obj_iff O x _).2 (h₂ i hi x hx))
    ((SheafOfModules.isZero_stalkFunctor_obj_iff O x _).2 (h₁ (i + 1) x hx))

end AlgebraicGeometry

namespace AlgebraicGeometry.PerfectApproximation

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- **A perfect object has quasi-coherent cohomology.** Perfectness implies pseudo-coherence,
and the cohomology sheaves of a pseudo-coherent object are quasi-coherent by Tag 08E5. -/
theorem isQuasicoherent_homology_of_isPerfect (P : DerivedCategory.{u + 1} X.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj P).IsQuasicoherent :=
  isQuasicoherentDerived_of_isPseudoCoherent.{u, u + 1} X P
    (((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace
      (X := X.toRingedSpace) P).1 hP).isPseudoCoherent) i

/-- The cohomology of a shift: `H^a(E⟦n⟧) ≅ H^{n+a}(E)`, naturally in `E`. This is the shift
sequence of `CategoryTheory.DerivedCategory.homologyFunctor`, read through
`CategoryTheory.DerivedCategory.shift_homologyFunctor`. -/
def homologyShiftIso (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (n a a' : ℤ) (h : n + a = a') :
    shiftFunctor (DerivedCategory C) n ⋙ DerivedCategory.homologyFunctor C a ≅
      DerivedCategory.homologyFunctor C a' :=
  (DerivedCategory.homologyFunctor C 0).shiftIso n a a' h

/-- The stalks of `H^i(P⟦n⟧)` vanish where those of `H^{n+i}(P)` do. -/
private theorem isZero_stalk_homology_shift {P : DerivedCategory.{u + 1} X.Modules} (n i : ℤ)
    {x : X} (h : IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor X.Modules (n + i)).obj P).val.presheaf) x)) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor X.Modules i).obj (P⟦n⟧)).val.presheaf) x) :=
  h.of_iso ((Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((homologyShiftIso X.Modules n i (n + i) rfl).app P))

/-- The cohomology sheaves of `P⟦n⟧` are quasi-coherent if those of `P` are. -/
private theorem isQuasicoherent_homology_shift {P : DerivedCategory.{u + 1} X.Modules}
    (h : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj P).IsQuasicoherent) (n i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj (P⟦n⟧)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((homologyShiftIso X.Modules n i (n + i) rfl).app P).symm (h (n + i))

/-- **A shift of an admissible approximating object is admissible.** Perfectness is stable under
shifting, and the cohomology of `P⟦n⟧` in degree `i` is that of `P` in degree `n + i`, so the
support condition is preserved. -/
theorem isAdmissible_shift (T : Set X) {P : DerivedCategory.{u + 1} X.Modules}
    (hP : IsAdmissible X T P) (n : ℤ) : IsAdmissible X T (P⟦n⟧) :=
  ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hP.1 n, fun i x hx =>
    isZero_stalk_homology_shift X n i (hP.2 (n + i) x hx)⟩

/-- **The objects to which Tag 08EQ applies.** An object of the derived category of
`𝒪_X`-modules with quasi-coherent cohomology which is `m`-pseudo-coherent and whose cohomology
is supported on `T` in all degrees `≥ b`. Tag 08EQ is the case `b = m - r + 1`, where the
complement of `T` is covered by `r` affine opens. -/
def ApproximationClass (T : Set X) (m b : ℤ) (F : DerivedCategory.{u + 1} X.Modules) : Prop :=
  (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj F).IsQuasicoherent) ∧
    RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) F m ∧
      ∀ i : ℤ, b ≤ i → ∀ x : X, x ∉ T →
        IsZero (TopCat.Presheaf.stalk (X := X)
          (((DerivedCategory.homologyFunctor X.Modules i).obj F).val.presheaf) x)

/-- **The class of Tag 08EQ passes to the cone of a map from an admissible object.** This is the
hypothesis `hcone` of
`AlgebraicGeometry.PerfectApproximation.approximationHolds_of_oneStep`, for the class on which
the induction of Tag 08EQ runs.

Quasi-coherence of the cohomology is a Serre condition, so it propagates along the cohomology
sequence; pseudo-coherence propagates by Tag 08CD, an admissible object being pseudo-coherent in
every degree; and the support condition propagates by exactness of the stalk functor. -/
theorem approximationClass_obj₃_of_distinguished (T : Set X) (m b : ℤ)
    (S : Triangle (DerivedCategory.{u + 1} X.Modules))
    (hS : S ∈ distTriang (DerivedCategory.{u + 1} X.Modules))
    (h₁ : IsAdmissible X T S.obj₁) (h₂ : ApproximationClass X T m b S.obj₂) :
    ApproximationClass X T m b S.obj₃ := by
  obtain ⟨hqc, hpc, hsupp⟩ := h₂
  refine ⟨?_, ?_, isZero_stalk_homology_obj₃_of_distinguished X.ringCatSheaf T b S hS h₁.2 hsupp⟩
  · exact DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
      S.rotate (rot_of_distTriang S hS) hqc
      (DerivedCategoryB.derivedCategoryB_shift_mem _
        (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X) 1
        (isQuasicoherent_homology_of_isPerfect X S.obj₁ h₁.1))
  · refine RingedSpace.isPseudoCoherentFrom_obj₃_of_distinguished.{u, u + 1} m S hS ?_ hpc
    exact (((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace
      (X := X.toRingedSpace) S.obj₁).1 h₁.1).isPseudoCoherent).isPseudoCoherentFrom (m + 1)

/-- **Tag 08EQ, reduced to its one-step construction, for the class on which its induction
runs.** Granted that every object `F` of
`AlgebraicGeometry.PerfectApproximation.ApproximationClass` whose cohomology vanishes above some
`t ≥ m` receives a degree-`t` surjection from an admissible object with the same vanishing,
approximation holds for `(T, F, m)` for every object of the class whose cohomology vanishes above
some degree.

This is `AlgebraicGeometry.PerfectApproximation.approximationHolds_of_oneStep` with its
hypothesis `hcone` discharged by
`AlgebraicGeometry.PerfectApproximation.approximationClass_obj₃_of_distinguished`. On `Spec R`
the remaining hypothesis `hstep` is
`Stacks.AffineTilde.exists_isAdmissible_epi_homology_of_approximationClass`. -/
theorem approximationHolds_of_oneStep_approximationClass (T : Set X) (m b : ℤ)
    (hstep : ∀ F : DerivedCategory.{u + 1} X.Modules, ApproximationClass X T m b F →
      ∀ t : ℤ, m ≤ t →
      (∀ i : ℤ, t < i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj F)) →
      ∃ P : DerivedCategory.{u + 1} X.Modules, IsAdmissible X T P ∧
        (∀ i : ℤ, t < i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj P)) ∧
        ∃ α : P ⟶ F, Epi ((DerivedCategory.homologyFunctor X.Modules t).map α))
    (E : DerivedCategory.{u + 1} X.Modules) (hE : ApproximationClass X T m b E) (t : ℤ)
    (hvan : ∀ i : ℤ, t < i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj E)) :
    ApproximationHolds X T E m :=
  approximationHolds_of_oneStep X T m (ApproximationClass X T m b)
    (fun S hS hA hQ => approximationClass_obj₃_of_distinguished X T m b S hS hA hQ)
    hstep E hE t hvan

end AlgebraicGeometry.PerfectApproximation

namespace Stacks.AffineTilde

open _root_.AlgebraicGeometry

universe w u

variable {R : CommRingCat.{u}} {r : ℕ}

/-! ### The torsion dictionary -/

/-- A prime at which the stalk of `M̃` vanishes lies outside the support of `M`. -/
theorem notMem_support_of_isZero_stalk_tilde (M : ModuleCat.{u} R) (x : PrimeSpectrum R)
    (h : IsZero ((tilde M).presheaf.stalk x)) : x ∉ Module.support R M := by
  have hs : Subsingleton ((tilde M).presheaf.stalk x) := AddCommGrpCat.subsingleton_of_isZero h
  exact Module.notMem_support_iff'.2
    ((IsLocalizedModule.subsingleton_iff x.asIdeal.primeCompl (tilde.toStalk M x).hom).1 hs)

/-- **`M̃` vanishes on `D(g)` exactly when `M` is `g`-power torsion.** This direction: if the
stalks of `M̃` vanish at every prime not containing `g`, then every element of `M` is
annihilated by a power of `g`. -/
theorem exists_pow_smul_eq_zero_of_isZero_stalk_tilde (M : ModuleCat.{u} R) (g : R)
    (h : ∀ x : PrimeSpectrum R, g ∉ x.asIdeal → IsZero ((tilde M).presheaf.stalk x))
    (m : M) : ∃ k : ℕ, g ^ k • m = 0 := by
  have hdisj : Disjoint (↑(PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum R))
      (Module.support R M) :=
    Set.disjoint_left.2 fun p hp =>
      notMem_support_of_isZero_stalk_tilde M p (h p ((PrimeSpectrum.mem_basicOpen g p).1 hp))
  obtain ⟨a, ha, hm⟩ := LocalizedModule.subsingleton_iff.1
    (LocalizedModule.subsingleton_iff_disjoint.2 hdisj) m
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff a g).1 ha
  exact ⟨k, hm⟩

/-- The converse: if every element of `M` is annihilated by a power of `g`, then the stalks of
`M̃` vanish at every prime not containing `g`. -/
theorem isZero_stalk_tilde_of_exists_pow_smul_eq_zero (M : ModuleCat.{u} R) (g : R)
    (h : ∀ m : M, ∃ k : ℕ, g ^ k • m = 0) (x : PrimeSpectrum R) (hx : g ∉ x.asIdeal) :
    IsZero ((tilde M).presheaf.stalk x) := by
  have hsub : Subsingleton ((tilde M).presheaf.stalk x) := by
    refine (IsLocalizedModule.subsingleton_iff x.asIdeal.primeCompl
      (tilde.toStalk M x).hom).2 fun m => ?_
    obtain ⟨k, hk⟩ := h m
    exact ⟨g ^ k, x.asIdeal.primeCompl.pow_mem hx k, hk⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-! ### Cohomology of a derived sheafification -/

/-- **An exact functor commutes with the cohomology of the derived category, naturally.** For
`F : C₁ ⥤ C₂` exact, the two functors `Hⁿ ∘ D(F)` and `F ∘ Hⁿ` on `D(C₁)` are isomorphic.

The complex-level statement is `CategoryTheory.ShortComplex.mapHomologyIso`; it descends along
the localisation `CategoryTheory.DerivedCategory.Q`. -/
private def mapDerivedCategoryCompHomologyFunctorIso {C₁ : Type*} {C₂ : Type*} [Category C₁]
    [Category C₂] [Abelian C₁] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (G : C₁ ⥤ C₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (n : ℤ) :
    G.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n ≅
      DerivedCategory.homologyFunctor C₁ n ⋙ G :=
  let e : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) n ⋙ G :=
    NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso G) (fun φ ↦
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor C₁ (ComplexShape.up ℤ) n).map φ) G)
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (G.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C₁ n ⋙ G)) _ _
    (Functor.isoWhiskerRight G.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor C₂ n) ≪≫
      Functor.isoWhiskerLeft (G.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors C₂ n) ≪≫ e ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C₁ n).symm G)

/-- **The cohomology of a derived sheafification is the sheafification of the cohomology.**
Sheafification is exact, so it commutes with the cohomology of a representing complex. -/
theorem nonempty_homology_mapDerivedCategory_tilde_iso
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    let _inst : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
    ∀ (E : DerivedCategory (ModuleCat.{u} R)) (n : ℤ),
      Nonempty ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
          ((tilde.functor R).mapDerivedCategory.obj E) ≅
        (tilde.functor R).obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E)) := by
  intro _inst E n
  obtain ⟨K, ⟨e⟩⟩ : (DerivedCategory.Q (C := ModuleCat.{u} R)).essImage E :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) E
  obtain ⟨iso⟩ := nonempty_homology_Q_obj_tildeComplex_iso K n
  exact ⟨(DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
      ((tilde.functor R).mapDerivedCategory.mapIso e.symm ≪≫
        (tilde.functor R).mapDerivedCategoryFactors.app K) ≪≫ iso ≪≫
    (tilde.functor R).mapIso
      (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app K).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso e)⟩

/-- **From geometric support to algebraic torsion.** If `F` is the derived sheafification of an
object `E` of `D(R)` and the cohomology sheaves of `F` vanish on `⋃ᵢ D(f_i)` in the degrees
`-r + 1, …, 0`, then the cohomology modules of `E` in those degrees are `f_i`-power torsion for
every `i`.

This is the hypothesis of
`Stacks.AffineTilde.exists_isAdmissible_koszulPowerTilde_lift` read off the support condition of
[Stacks, Tag 08E3], through
`Stacks.AffineTilde.exists_pow_smul_eq_zero_of_isZero_stalk_tilde`. -/
theorem forall_exists_pow_smul_eq_zero_of_isZero_stalk_homology
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    let _inst : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
    ∀ (f : Fin r → R) (E : DerivedCategory (ModuleCat.{u} R))
      {F : DerivedCategory (Spec R).Modules},
      ((tilde.functor R).mapDerivedCategory.obj E ≅ F) →
      (∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 → ∀ x : PrimeSpectrum R,
        x ∉ PrimeSpectrum.zeroLocus (Set.range f) →
        IsZero (TopCat.Presheaf.stalk
          (((DerivedCategory.homologyFunctor (Spec R).Modules n).obj F).val.presheaf) x)) →
      ∀ i : Fin r, ∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 →
        ∀ y : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj E,
          ∃ k : ℕ, f i ^ k • y = 0 := by
  intro _inst f E F hEF hvan i n hn hn' y
  obtain ⟨e⟩ := nonempty_homology_mapDerivedCategory_tilde_iso E n
  refine exists_pow_smul_eq_zero_of_isZero_stalk_tilde _ (f i) (fun x hx => ?_) y
  refine (hvan n hn hn' x fun hmem => hx (hmem ⟨i, rfl⟩)).of_iso ?_
  exact ((Scheme.Modules.toPresheaf (Spec R) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso hEF.symm ≪≫ e)).symm

/-- **An object of `D(𝒪_{Spec R})` with quasi-coherent cohomology is the complex of associated
sheaves of a complex of `R`-modules**, at the standard model of the derived category of
`𝒪_{Spec R}`-modules.

This is `Stacks.DerivedQCoh.exists_iso_derivedTildeEquiv_obj_of_isDQCoh`, which is [Stacks,
Tag 06Z0], with its object of `D(R)` replaced by a complex representing it; degreewise
sheafification is the `~` edge of Stacks 06Z0 followed by the inclusion of the quasi-coherent
modules, so the two readings of the sheafified complex agree. -/
private theorem exists_iso_Q_obj_mapHomologicalComplex_tilde_of_isQuasicoherent :
    let _inst : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
    ∀ F : DerivedCategory (Spec R).Modules,
      (∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj F).IsQuasicoherent) →
      ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
        Nonempty (DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅ F) := by
  intro _inst F hF
  let _instMod : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let _instSheaf : HasDerivedCategory.{u + 1} (_root_.SheafOfModules.{u} (Spec R).ringCatSheaf) :=
    Stacks.DerivedQCoh.hasDerivedCategoryRingCatSheaf (Spec R) _inst
  let _instQCoh : HasDerivedCategory.{u + 1}
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    HasDerivedCategory.standard _
  obtain ⟨M, ⟨e⟩⟩ := Stacks.DerivedQCoh.exists_iso_derivedTildeEquiv_obj_of_isDQCoh R F hF
  exact ⟨DerivedCategory.Q.objPreimage M,
    ⟨((tilde.functor R).mapDerivedCategoryFactors.app _).symm ≪≫
      (tilde.functor R).mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M) ≪≫
      ((Functor.mapDerivedCategoryCompIso (Iso.refl _ : (tildeEquiv (R := R)).functor ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) ≅
          tilde.functor R)).app M).symm ≪≫ e⟩⟩

/-- **Every object of `D(𝒪_{Spec R})` with quasi-coherent cohomology is a derived
sheafification**, at the standard model of the derived category of `𝒪_{Spec R}`-modules.

This is essential surjectivity of derived sheafification, [Stacks, Tag 06Z0]: the complex of
associated sheaves of a complex `P` of `R`-modules is the derived sheafification of the class of
`P`, by `CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
theorem exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    let _inst : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
    ∀ F : DerivedCategory (Spec R).Modules,
      (∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj F).IsQuasicoherent) →
      ∃ E : DerivedCategory (ModuleCat.{u} R),
        Nonempty ((tilde.functor R).mapDerivedCategory.obj E ≅ F) := by
  intro _inst F hF
  obtain ⟨P, ⟨e⟩⟩ := exists_iso_Q_obj_mapHomologicalComplex_tilde_of_isQuasicoherent F hF
  exact ⟨DerivedCategory.Q.obj P, ⟨(tilde.functor R).mapDerivedCategoryFactors.app P ≪≫ e⟩⟩

/-! ### Finitely many generators, sheafified -/

/-- **A finite generating family of a module sheafifies to a jointly epimorphic family.** If
`g₁, …, g_k` generate the `R`-module `M`, then two morphisms out of `M̃` which agree after
composition with the sheafification of `c ↦ c · g_j` for every `j` are equal.

The linear combination map `Rᵏ → M` is surjective, and it is the sum over `j` of the `j`-th
projection followed by `c ↦ c · g_j`; sheafification is additive and preserves
epimorphisms. -/
theorem eq_of_comp_map_tilde_toSpanSingleton (M : ModuleCat.{u} R) {k : ℕ} (g : Fin k → M)
    (hg : Submodule.span R (Set.range g) = ⊤) {Y : (Spec R).Modules}
    (h₁ h₂ : (tilde.functor R).obj M ⟶ Y)
    (hh : ∀ j : Fin k, (tilde.functor R).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (g j))) ≫ h₁ =
      (tilde.functor R).map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (g j))) ≫ h₂) :
    h₁ = h₂ := by
  classical
  have hpe : (tilde.functor R).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction tilde.adjunction
  have hepi : Epi (ModuleCat.ofHom (Fintype.linearCombination R g)) :=
    (ModuleCat.epi_iff_surjective _).2
      ((span_range_eq_top_iff_surjective_fintypeLinearCombination R g).1 hg)
  have hsum : ModuleCat.ofHom (Fintype.linearCombination R g) =
      ∑ j : Fin k, ModuleCat.ofHom (LinearMap.proj (R := R) (φ := fun _ : Fin k => R) j) ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R M (g j)) := by
    ext a
    simp [Fintype.linearCombination_apply]
  rw [← cancel_epi ((tilde.functor R).map (ModuleCat.ofHom (Fintype.linearCombination R g))),
    hsum, (tilde.functor R).map_sum, Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(tilde.functor R).map_comp, Category.assoc, Category.assoc, hh j]

/-! ### The Koszul power lift with the hypothesis of the source -/

/-- **The Koszul power lift on an affine scheme, with the geometric hypothesis of
[Stacks, Tag 08E3].** Let `f₁, …, f_r ∈ R` and let `F` be an object of `D(𝒪_{Spec R})` with
quasi-coherent cohomology whose cohomology sheaves vanish on `⋃ᵢ D(f_i)` in the degrees
`-r + 1, …, 0`. Then every morphism `𝒪_{Spec R}[0] ⟶ F` factors through the sheafified Koszul
complex on the `(e+1)`-st powers of the sequence, for some `e`, and that complex is a perfect
object with cohomology supported on `V(f₁, …, f_r)`.

This is `Stacks.AffineTilde.exists_isAdmissible_koszulPowerTilde_lift` with its presentation
hypothesis supplied by
`Stacks.AffineTilde.exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard` and its
torsion hypothesis by
`Stacks.AffineTilde.forall_exists_pow_smul_eq_zero_of_isZero_stalk_homology`. -/
theorem exists_isAdmissible_koszulPowerTilde_lift_of_isZero_stalk_homology
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (f : Fin r → R) :
    let _inst : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
    ∀ F : DerivedCategory (Spec R).Modules,
      (∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj F).IsQuasicoherent) →
      (∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 → ∀ x : PrimeSpectrum R,
        x ∉ PrimeSpectrum.zeroLocus (Set.range f) →
        IsZero (TopCat.Presheaf.stalk
          (((DerivedCategory.homologyFunctor (Spec R).Modules n).obj F).val.presheaf) x)) →
      ∀ s : DerivedCategory.Q.obj (structureSheafSingleComplex R) ⟶ F,
      ∃ e : ℕ, ∃ t : DerivedCategory.Q.obj (koszulPowerTildeComplex f e) ⟶ F,
        PerfectApproximation.IsAdmissible (Spec R) (PrimeSpectrum.zeroLocus (Set.range f))
            (DerivedCategory.Q.obj (koszulPowerTildeComplex f e)) ∧
          s = DerivedCategory.Q.map (koszulPowerUnitTilde f e) ≫ t := by
  intro _inst F hqc hvan s
  obtain ⟨E, ⟨hEF⟩⟩ := exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard F hqc
  exact exists_isAdmissible_koszulPowerTilde_lift f E hEF
    (forall_exists_pow_smul_eq_zero_of_isZero_stalk_homology f E hEF hvan) s

/-! ### The one-step construction in cohomological degree zero -/

/-- **The one-step construction of [Stacks, Tag 08EQ], in cohomological degree zero.** Let
`f₁, …, f_r ∈ R` and let `G` be an object of `D(𝒪_{Spec R})` with quasi-coherent cohomology whose
cohomology sheaf in degree zero is of finite type, and such that every morphism `𝒪[0] ⟶ G`
factors through a sheafified Koszul complex on powers of the `f_i`. Then there is a perfect
object supported on `V(f₁, …, f_r)`, with vanishing cohomology in positive degrees, mapping to
`G` by an epimorphism on `H⁰`.

`H⁰(G)` is the sheaf associated to a finite `R`-module, by [Stacks, Tag 01PB]; a finite
generating family of that module gives, through
`DerivedCategory.homologyFromSingleAddEquiv`, finitely many morphisms `𝒪_{Spec R}[0] ⟶ G` which
are jointly epimorphic on `H⁰`; each factors through a sheafified Koszul complex, and
`AlgebraicGeometry.PerfectApproximation.exists_isAdmissible_epi_homology_of_fin` replaces the
finite family by a single morphism. -/
theorem exists_isAdmissible_epi_homology_zero
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (f : Fin r → R) :
    let _inst : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
    ∀ G : DerivedCategory (Spec R).Modules,
      (∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj G).IsQuasicoherent) →
      (∀ s : DerivedCategory.Q.obj (structureSheafSingleComplex R) ⟶ G,
        ∃ e : ℕ, ∃ t : DerivedCategory.Q.obj (koszulPowerTildeComplex f e) ⟶ G,
          PerfectApproximation.IsAdmissible (Spec R) (PrimeSpectrum.zeroLocus (Set.range f))
              (DerivedCategory.Q.obj (koszulPowerTildeComplex f e)) ∧
            s = DerivedCategory.Q.map (koszulPowerUnitTilde f e) ≫ t) →
      ((DerivedCategory.homologyFunctor (Spec R).Modules 0).obj G).IsFiniteType →
      ∃ P : DerivedCategory (Spec R).Modules,
        PerfectApproximation.IsAdmissible (Spec R)
            (PrimeSpectrum.zeroLocus (Set.range f)) P ∧
          (∀ i : ℤ, 0 < i →
            IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj P)) ∧
          ∃ α : P ⟶ G, Epi ((DerivedCategory.homologyFunctor (Spec R).Modules 0).map α) := by
  intro _inst G hqc hlift hft
  classical
  obtain ⟨E, ⟨hEG⟩⟩ := exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard G hqc
  have : PreservesFiniteLimits (tilde.functor R) := AlgebraicGeometry.tilde.preservesFiniteLimits R
  have : PreservesFiniteColimits (tilde.functor R) := preservesFiniteColimits_tildeFunctor R
  set M₀ := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj E with hM₀
  obtain ⟨Φ⟩ : Nonempty ((tilde.functor R).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor (Spec R).Modules 0 ≅
    DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0 ⋙ tilde.functor R) :=
    ⟨mapDerivedCategoryCompHomologyFunctorIso (tilde.functor R) 0⟩
  obtain ⟨ν, hνh⟩ : ∃ ν : (tilde.functor R).obj M₀ ≅
      (DerivedCategory.homologyFunctor (Spec R).Modules 0).obj G,
      ν.hom = Φ.inv.app E ≫
        (DerivedCategory.homologyFunctor (Spec R).Modules 0).map hEG.hom :=
    ⟨(Φ.app E).symm ≪≫
      (DerivedCategory.homologyFunctor (Spec R).Modules 0).mapIso hEG, rfl⟩
  have := hft
  have hfin : Module.Finite R M₀ := (tilde_isFiniteType_iff M₀).1
    (Stacks.SheafOfModules.isFiniteType_of_iso.{u} ν.symm)
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := (R : Type u)) (M := (M₀ : Type u))
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin k → ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R) ⟶ E), ∀ j : Fin k,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app
          (ModuleCat.of R R) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map (σ j) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R M₀ (g j)) :=
    ⟨fun j => (DerivedCategory.homologyFromSingleAddEquiv (ModuleCat.of R R) E 0).symm _,
      fun j => (DerivedCategory.homologyFromSingleAddEquiv
        (ModuleCat.of R R) E 0).apply_symm_apply _⟩
  obtain ⟨ι⟩ : Nonempty (DerivedCategory.Q.obj (structureSheafSingleComplex R) ≅
      (tilde.functor R).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) :=
    ⟨(DerivedCategory.Q.mapIso (tildeSingleSelfIso R)).symm ≪≫
      ((tilde.functor R).mapDerivedCategoryFactors.app
        (((CochainComplex.singleFunctors (ModuleCat.{u} R)).functor 0).obj
          (ModuleCat.of R R))).symm⟩
  have hlift : ∀ j : Fin k, ∃ e : ℕ,
      ∃ t : DerivedCategory.Q.obj (koszulPowerTildeComplex f e) ⟶ G,
      PerfectApproximation.IsAdmissible (Spec R) (PrimeSpectrum.zeroLocus (Set.range f))
          (DerivedCategory.Q.obj (koszulPowerTildeComplex f e)) ∧
        ι.hom ≫ (tilde.functor R).mapDerivedCategory.map (σ j) ≫ hEG.hom =
          DerivedCategory.Q.map (koszulPowerUnitTilde f e) ≫ t := fun j => hlift _
  choose ee tt hadm hfact using hlift
  refine PerfectApproximation.exists_isAdmissible_epi_homology_of_fin (Spec R)
    (PrimeSpectrum.zeroLocus (Set.range f)) 0 G k
    (fun j => DerivedCategory.Q.obj (koszulPowerTildeComplex f (ee j))) hadm
    (fun j i hi => isZero_homology_Q_obj_tildeComplex_extend_seqComplex
      (fun i => f i ^ (ee j + 1)) i hi) tt ?_
  intro Y h₁ h₂ hh
  rw [← cancel_epi ν.hom]
  refine eq_of_comp_map_tilde_toSpanSingleton M₀ g hg _ _ fun j => ?_
  have hnat : ∀ {Z : (Spec R).Modules}
      (h : (DerivedCategory.homologyFunctor (Spec R).Modules 0).obj
        ((tilde.functor R).mapDerivedCategory.obj E) ⟶ Z),
      (tilde.functor R).map ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map (σ j)) ≫
          Φ.inv.app E ≫ h =
        Φ.inv.app ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R)) ≫
        (DerivedCategory.homologyFunctor (Spec R).Modules 0).map
          ((tilde.functor R).mapDerivedCategory.map (σ j)) ≫ h := by
    intro Z h
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact Φ.inv.naturality (σ j)
  have hstar : (DerivedCategory.homologyFunctor (Spec R).Modules 0).map
        ((tilde.functor R).mapDerivedCategory.map (σ j)) ≫
      (DerivedCategory.homologyFunctor (Spec R).Modules 0).map hEG.hom =
    (DerivedCategory.homologyFunctor (Spec R).Modules 0).map ι.inv ≫
      (DerivedCategory.homologyFunctor (Spec R).Modules 0).map
        (DerivedCategory.Q.map (koszulPowerUnitTilde f (ee j))) ≫
      (DerivedCategory.homologyFunctor (Spec R).Modules 0).map (tt j) := by
    simp only [← Functor.map_comp]
    congr 1
    rw [← hfact j, Iso.inv_hom_id_assoc]
  have key : (tilde.functor R).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R M₀ (g j))) ≫ ν.hom =
      ((tilde.functor R).map
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app
            (ModuleCat.of R R)) ≫
        Φ.inv.app ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R)) ≫
        (DerivedCategory.homologyFunctor (Spec R).Modules 0).map ι.inv ≫
        (DerivedCategory.homologyFunctor (Spec R).Modules 0).map
          (DerivedCategory.Q.map (koszulPowerUnitTilde f (ee j)))) ≫
      (DerivedCategory.homologyFunctor (Spec R).Modules 0).map (tt j) := by
    rw [← hσ j, (tilde.functor R).map_comp, hνh, Category.assoc, hnat, hstar]
    simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, key]
  simp only [Category.assoc]
  rw [hh j]

/-! ### The one-step construction in an arbitrary degree -/

/-- **The one-step construction of [Stacks, Tag 08EQ], from the Koszul lift.** Let
`f₁, …, f_r ∈ R`, let `F` be an object of `D(𝒪_{Spec R})` with quasi-coherent cohomology which is
`m`-pseudo-coherent, let `t ≥ m` be a degree above which the cohomology of `F` vanishes, and
suppose every morphism `𝒪[0] ⟶ F[t]` factors through a sheafified Koszul complex on powers of
the `f_i`. Then there is a perfect object supported on `V(f₁, …, f_r)`, with the same vanishing,
mapping to `F` by an epimorphism on `H^t`.

The cohomology sheaf `H^t(F)` is of finite type by [Stacks, Tag 08DN], so
`Stacks.AffineTilde.exists_isAdmissible_epi_homology_zero` applies to `F[t]`; shifting the
resulting morphism back by `-t` turns the epimorphism on `H⁰` into one on `H^t`. -/
theorem exists_isAdmissible_epi_homology_of_lift
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (f : Fin r → R) (m b : ℤ) :
    let _inst : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
    ∀ F : DerivedCategory (Spec R).Modules,
      PerfectApproximation.ApproximationClass (Spec R)
          (PrimeSpectrum.zeroLocus (Set.range f)) m b F →
      ∀ t : ℤ, m ≤ t →
      (∀ i : ℤ, t < i →
        IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj F)) →
      (∀ s : DerivedCategory.Q.obj (structureSheafSingleComplex R) ⟶ F⟦t⟧,
        ∃ e : ℕ, ∃ t' : DerivedCategory.Q.obj (koszulPowerTildeComplex f e) ⟶ F⟦t⟧,
          PerfectApproximation.IsAdmissible (Spec R) (PrimeSpectrum.zeroLocus (Set.range f))
              (DerivedCategory.Q.obj (koszulPowerTildeComplex f e)) ∧
            s = DerivedCategory.Q.map (koszulPowerUnitTilde f e) ≫ t') →
      ∃ P : DerivedCategory (Spec R).Modules,
        PerfectApproximation.IsAdmissible (Spec R)
            (PrimeSpectrum.zeroLocus (Set.range f)) P ∧
          (∀ i : ℤ, t < i →
            IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj P)) ∧
          ∃ α : P ⟶ F, Epi ((DerivedCategory.homologyFunctor (Spec R).Modules t).map α) := by
  intro _inst F hF t hmt hvanF hlift
  obtain ⟨hqc, hpc, -⟩ := hF
  have hqcG := AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_shift
    (Spec R) hqc t
  let _instOX : HasDerivedCategory.{u + 1}
    (StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace) := _inst
  have hftF : _root_.SheafOfModules.IsFiniteType.{u, u, u}
      ((DerivedCategory.homologyFunctor (Spec R).Modules t).obj F) :=
    RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom
      (X := (Spec R).toRingedSpace) F t (hpc.mono hmt) hvanF
  have hft0 : _root_.SheafOfModules.IsFiniteType.{u, u, u}
      ((DerivedCategory.homologyFunctor (Spec R).Modules 0).obj (F⟦t⟧)) := by
    have := hftF
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((AlgebraicGeometry.PerfectApproximation.homologyShiftIso
        (Spec R).Modules t 0 t (by ring)).app F).symm
  obtain ⟨P₀, hadm₀, hvan₀, α₀, hepi₀⟩ :=
    exists_isAdmissible_epi_homology_zero f (F⟦t⟧) hqcG hlift hft0
  have hΘ := AlgebraicGeometry.PerfectApproximation.homologyShiftIso
    (Spec R).Modules (-t) t 0 (by ring)
  refine ⟨P₀⟦(-t : ℤ)⟧,
    AlgebraicGeometry.PerfectApproximation.isAdmissible_shift (Spec R) _ hadm₀ (-t),
    fun i hi => (hvan₀ (-t + i) (by omega)).of_iso
      ((AlgebraicGeometry.PerfectApproximation.homologyShiftIso (Spec R).Modules
        (-t) i (-t + i) rfl).app P₀),
    α₀⟦(-t : ℤ)⟧' ≫ (shiftFunctorCompIsoId (DerivedCategory (Spec R).Modules) t (-t)
      (add_neg_cancel t)).hom.app F, ?_⟩
  have hshift : (DerivedCategory.homologyFunctor (Spec R).Modules t).map (α₀⟦(-t : ℤ)⟧') =
      ((hΘ.app P₀).hom ≫
        (DerivedCategory.homologyFunctor (Spec R).Modules 0).map α₀) ≫
      (hΘ.app (F⟦t⟧)).symm.hom := (Iso.eq_comp_inv _).2 (hΘ.hom.naturality α₀)
  rw [Functor.map_comp, hshift]
  infer_instance

/-- **The one-step construction of [Stacks, Tag 08EQ].** Let `f₁, …, f_r ∈ R`, let `F` be an
object of the class of [Stacks, Tag 08EQ] for `T = V(f₁, …, f_r)` and the degree `m`, and let
`t ≥ m` be a degree above which the cohomology of `F` vanishes. Then there is a perfect object
supported on `T`, with the same vanishing, mapping to `F` by an epimorphism on `H^t`.

This is the hypothesis `hstep` of
`AlgebraicGeometry.PerfectApproximation.approximationHolds_of_oneStep_approximationClass`. The
cohomology of `F[t]` in the degrees `-r + 1, …, 0` is that of `F` in the degrees
`t - r + 1, …, t`, and therefore supported on `T`, so
`Stacks.AffineTilde.exists_isAdmissible_koszulPowerTilde_lift_of_isZero_stalk_homology` supplies
the lift of `Stacks.AffineTilde.exists_isAdmissible_epi_homology_of_lift`. -/
theorem exists_isAdmissible_epi_homology_of_approximationClass
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (f : Fin r → R) (m : ℤ) :
    let _inst : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
    ∀ F : DerivedCategory (Spec R).Modules,
      PerfectApproximation.ApproximationClass (Spec R)
          (PrimeSpectrum.zeroLocus (Set.range f)) m (m - (r : ℤ) + 1) F →
      ∀ t : ℤ, m ≤ t →
      (∀ i : ℤ, t < i →
        IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj F)) →
      ∃ P : DerivedCategory (Spec R).Modules,
        PerfectApproximation.IsAdmissible (Spec R)
            (PrimeSpectrum.zeroLocus (Set.range f)) P ∧
          (∀ i : ℤ, t < i →
            IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj P)) ∧
          ∃ α : P ⟶ F, Epi ((DerivedCategory.homologyFunctor (Spec R).Modules t).map α) := by
  intro _inst F hF t hmt hvanF
  refine exists_isAdmissible_epi_homology_of_lift f m _ F hF t hmt hvanF fun s => ?_
  obtain ⟨hqc, -, hsupp⟩ := hF
  have hvanG : ∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 → ∀ x : PrimeSpectrum R,
      x ∉ PrimeSpectrum.zeroLocus (Set.range f) →
      IsZero (TopCat.Presheaf.stalk
        (((DerivedCategory.homologyFunctor (Spec R).Modules n).obj (F⟦t⟧)).val.presheaf) x) :=
    fun n hn hn' x hx => AlgebraicGeometry.PerfectApproximation.isZero_stalk_homology_shift
      (Spec R) t n (hsupp (t + n) (by omega) x hx)
  exact exists_isAdmissible_koszulPowerTilde_lift_of_isZero_stalk_homology f (F⟦t⟧)
    (AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_shift (Spec R) hqc t)
    hvanG s

end Stacks.AffineTilde

namespace AlgebraicGeometry.PerfectApproximation

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Approximation for a closed subset cut out by `r` equations.** Let `R` be a commutative
ring, let `f₁, …, f_r ∈ R` and let `T = V(f₁, …, f_r)`, so that `Spec R ∖ T` is the union of the
`r` basic
opens `D(f_i)`. Approximation holds for every triple `(T, E, m)` with `E` of quasi-coherent
cohomology such that `E` is `m`-pseudo-coherent and the cohomology of `E` is supported on `T` in
all degrees `≥ m - r + 1`.

The cohomology of `E` is bounded above because `Spec R` is quasi-compact and `E` is
`m`-pseudo-coherent, so the induction of
`AlgebraicGeometry.PerfectApproximation.approximationHolds_of_oneStep_approximationClass` applies,
with its one-step hypothesis discharged by
`Stacks.AffineTilde.exists_isAdmissible_epi_homology_of_approximationClass`. -/
theorem approximationHolds_of_zeroLocus (R : CommRingCat.{u}) {r : ℕ} (f : Fin r → R)
    (E : DerivedCategory.{u + 1} (Spec R).Modules) (m : ℤ)
    (hqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).IsQuasicoherent)
    (hpc : RingedSpace.IsPseudoCoherentFrom (X := (Spec R).toRingedSpace) E m)
    (hsupp : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i → ∀ x : PrimeSpectrum R,
      x ∉ PrimeSpectrum.zeroLocus (Set.range f) →
      IsZero (TopCat.Presheaf.stalk (X := Spec R)
        (((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).val.presheaf) x)) :
    ApproximationHolds (Spec R) (PrimeSpectrum.zeroLocus (Set.range f)) E m := by
  let _instOX : HasDerivedCategory.{u + 1}
    (StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace) := inferInstance
  let _instM : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
  have hcpt : CompactSpace (Spec R).toRingedSpace.carrier :=
    inferInstanceAs (CompactSpace (Spec R))
  obtain ⟨b, hb⟩ := RingedSpace.exists_isZero_homology_of_isPseudoCoherentFrom
    (X := (Spec R).toRingedSpace) E m hpc
  exact approximationHolds_of_oneStep_approximationClass (Spec R)
    (PrimeSpectrum.zeroLocus (Set.range f)) m (m - (r : ℤ) + 1)
    (fun F hF t hmt hvan =>
      Stacks.AffineTilde.exists_isAdmissible_epi_homology_of_approximationClass
        f m F hF t hmt hvan)
    E ⟨hqc, hpc, hsupp⟩ (b - 1) (fun i hi => hb i (by omega))

/-- **Approximation by perfect complexes holds on `Spec R`.** This is the second assertion of
[Stacks, Tag 08EQ] for `X = Spec R`.

A closed subset of `Spec R` with retrocompact complement is the zero locus of a finite subset of
`R`, by [Stacks, Tag 00E8]; taking for the integer of [Stacks, Tag 08EN] the cardinality of that
subset, the hypotheses of
`AlgebraicGeometry.PerfectApproximation.approximationHolds_of_zeroLocus` follow from those of
[Stacks, Tag 08EN] because `m`-pseudo-coherence is monotone in `m`. -/
theorem approximationByPerfectComplexes_spec (R : CommRingCat.{u}) :
    ApproximationByPerfectComplexes (Spec R) := by
  classical
  intro T hT hTc
  obtain ⟨s, hs⟩ := PrimeSpectrum.isCompact_isOpen_iff.1 ⟨hTc.isCompact, hT.isOpen_compl⟩
  set f : Fin s.card → R := fun i => (s.equivFin.symm i : R) with hf
  have hrange : Set.range f = (↑s : Set R) := by
    refine Set.eq_of_subset_of_subset ?_ fun x hx => ?_
    · rintro _ ⟨i, rfl⟩
      simp [hf]
    · exact ⟨s.equivFin ⟨x, hx⟩, by simp [hf]⟩
  have hTz : T = PrimeSpectrum.zeroLocus (Set.range f) := by
    rw [hrange]
    ext x
    exact (not_iff_not.1 (Set.ext_iff.1 hs x)).symm
  refine ⟨(s.card : ℤ), fun E m hqc hpc hsupp => ?_⟩
  rw [hTz]
  exact approximationHolds_of_zeroLocus R f E m hqc (hpc.mono (by omega))
    fun i hi x hx => hsupp i x (by omega) (hTz ▸ hx)

/-- **Approximation by perfect complexes holds on `Spec R`**, in the encoding of
`AlgebraicGeometry.HasApproximationByPerfectComplexes`. -/
theorem hasApproximationByPerfectComplexes_spec (R : CommRingCat.{u}) :
    HasApproximationByPerfectComplexes (Spec R) :=
  (approximationByPerfectComplexes_iff (Spec R)).1 (approximationByPerfectComplexes_spec R)

end AlgebraicGeometry.PerfectApproximation

end
