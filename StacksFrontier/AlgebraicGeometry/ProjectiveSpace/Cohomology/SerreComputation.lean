module

public import StacksFrontier.Algebra.Homology.RestrictScalarsHomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechCohomologyIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ChartSectionsLinear
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.OrderedCechMonomialModel
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCechComplex
public import
 StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.ModuleValuedAlternatingComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.SliceScalarAction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of the twists of the structure sheaf on projective space

Let `R` be a commutative ring, let `n = m + 1 ≥ 1` and let `d` be an integer. The cohomology of
the twist `𝒪(d)` on `ℙⁿ_R = Proj R[T₀, …, Tₙ]` is a module over `R` through the structure
morphism `ℙⁿ_R ⟶ Spec R`, and

$$ H^q(\mathbf{P}^n_R, \mathcal{O}(d)) =
  \begin{cases} (R[T_0, \ldots, T_n])_d & q = 0 \\
    0 & q \neq 0, n \\
    \operatorname{Hom}_R((R[T_0, \ldots, T_n])_{-n-1-d}, R) & q = n \end{cases} $$

as `R`-modules. The hypothesis `n ≥ 1` is part of the statement: at `n = 0` the first and third
rows would both apply and would disagree. The degree-`e` part of `R[T₀, …, Tₙ]` is read as the
monomial chart `Stacks.ProjectiveSpace.Cohomology.twistChart R n e ∅` with no variable inverted,
which vanishes for `e < 0`, so the first and third rows hold for every integer `d`; in the degrees
where the index is a natural number they are also stated with
`MvPolynomial.homogeneousSubmodule`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.coeffScalar`: the coefficients as global functions on `ℙⁿ_R`,
  the ring homomorphism along which the cohomology is read as an `R`-module.
* `Stacks.ProjectiveSpace.Cohomology.twistCohomology`: `H^q(ℙⁿ_R, 𝒪(d))` as an `R`-module.
* `Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoOrderedHomology` and
  `Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoLaurentHomology`: that `R`-module is the
  homology of the ordered Čech complex of the standard cover, and of the monomial Čech complex
  `Stacks.ProjectiveSpace.Cohomology.laurentCechComplex`.
* `Stacks.ProjectiveSpace.Cohomology.SerreTwistCohomology`: the rows of the displayed equation,
  bundled.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquivTwistChart_coeffScalar_smul` and
  `Stacks.ProjectiveSpace.Cohomology.ordInterChartAddEquiv_coeffScalar_smul`: the monomial model
  of a Čech term of `𝒪(d)` is linear for the action of the coefficients through the structure
  morphism.
* `Stacks.ProjectiveSpace.Cohomology.twistOrdCochainLinearEquiv` and
  `Stacks.ProjectiveSpace.Cohomology.twistOrderedComplexIsoLaurent`: **the ordered Čech complex
  of the standard cover of `ℙⁿ_R` for `𝒪(d)` is the monomial Čech complex**, as complexes of
  `R`-modules.
* `Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology`: **the displayed equation of
  [Stacks, Tag 01XU]**, all its rows, as isomorphisms of `R`-modules.

## References

* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf Stacks.ProjectiveCohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ProjectiveSpace.Cohomology

/-- A module which is a zero object of `ModuleCat R` is a finite `R`-module. -/
theorem moduleFinite_of_isZero {R : Type u} [CommRing R] {M : ModuleCat.{u} R}
    (h : IsZero M) : Module.Finite R M :=
  have := ModuleCat.subsingleton_of_isZero h
  have : Finite M := Finite.of_subsingleton
  Module.Finite.of_finite

/-! ### The coefficients as scalars on the Čech cochains -/

/-- The structure sheaf of `ℙⁿ_R` as a sheaf of rings, in the spelling the twisting sheaf is a
sheaf of modules over. -/
abbrev projRingSheaf (R : Type u) [CommRing R] (n : ℕ) :=
  (sheafCompose (Opens.grothendieckTopology ↑(ProjectiveSpectrum.top (polyGrading R n)))
      (forget₂ CommRingCat RingCat)).obj
    (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))

/-- **The coefficients as global functions on `ℙⁿ_R`.** The ring homomorphism
`R → Γ(ℙⁿ_R, 𝒪)` of `Stacks.ProjectiveSpace.Cohomology.coeffToGlobalSections`, with its target
spelled as the ring of global sections of the sheaf of rings that `𝒪(d)` is a module over. -/
def coeffScalar (R : Type u) [CommRing R] (n : ℕ) : R →+* SectionRing (projRingSheaf R n) ⊤ :=
  coeffToGlobalSections R n

/-- **The monomial model of the sections of `𝒪(d)` over a standard open is linear over the
coefficients**, for the action of `Γ(ℙⁿ_R, 𝒪)` on the sections over that open. -/
theorem chartSectionsAddEquivTwistChart_coeffScalar_smul (R : Type u) [CommRing R] (n : ℕ)
    (d : ℤ) (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (r : R)
    (x : ToType ((abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)).obj
      (op (ProjectiveSpectrum.basicOpen (polyGrading R n) (chartDenom R n s))))) :
    chartSectionsAddEquivTwistChart R n d s hs
        (letI := sectionsModuleOfLE
          (⊤ : Opens ↑(ProjectiveSpectrum.top (polyGrading R n)))
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
          (W := ProjectiveSpectrum.basicOpen (polyGrading R n) (chartDenom R n s)) le_top
         coeffScalar R n r • x)
      = r • chartSectionsAddEquivTwistChart R n d s hs x :=
  (congrArg (chartSectionsAddEquivTwistChart R n d s hs)
      (smul_sectionsModuleOfLE (⊤ : Opens ↑(ProjectiveSpectrum.top (polyGrading R n)))
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
        (W := ProjectiveSpectrum.basicOpen (polyGrading R n) (chartDenom R n s)) le_top
        (coeffScalar R n r) x)).trans
    (chartSectionsAddEquivTwistChart_smul R n d s hs r x)

/-! ### The cohomology of a twist as an `R`-module -/

/-- **The cohomology `H^q(ℙⁿ_R, 𝒪(d))` as an `R`-module**, the coefficients acting through the
structure morphism `ℙⁿ_R ⟶ Spec R`. -/
abbrev twistCohomology (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars.{u} (coeffScalar R n)).obj
    (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n))
        ⊤).rightDerived q).obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d))

/-- The ordered Čech complex of the standard cover of `ℙⁿ_R` for `𝒪(d)`. -/
abbrev twistOrderedComplex (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :=
  orderedModuleComplex (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)

/-- **The cohomology of `𝒪(d)` is the homology of the ordered Čech complex of the standard
cover**, as modules over the global sections of `𝒪`. This is [Stacks, Tag 01XD] composed with the
`R(V)`-linear comparisons of [Stacks, Tags 01FJ and 01FM]. -/
def sheafCohomologyIsoOrderedHomology (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ) :
    (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n))
          ⊤).rightDerived q).obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) ≅
      (twistOrderedComplex R n d).homology q :=
  (Stacks.ProjectiveCohomology.cechHomologyIsoRightDerivedTwistingSheaf R n d q).trans
    (orderedCechHomologyModuleIso (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
      (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) q).symm

/-- **The cohomology of `𝒪(d)` is the homology of the ordered Čech complex of the standard
cover, `R`-linearly**: restriction of scalars along
`Stacks.ProjectiveSpace.Cohomology.coeffScalar` commutes with homology. -/
def twistCohomologyIsoOrderedHomology (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ) :
    twistCohomology R n d q ≅
      (((ModuleCat.restrictScalars.{u} (coeffScalar R n)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (twistOrderedComplex R n d)).homology q :=
  (ModuleCat.restrictScalars.{u} (coeffScalar R n)).mapIso
      (sheafCohomologyIsoOrderedHomology R n d q) ≪≫
    (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso (coeffScalar R n)
      (twistOrderedComplex R n d) q).symm

/-! ### The monomial model of the ordered Čech complex, `R`-linearly -/

/-- **The monomial model of a Čech term of `𝒪(d)` is linear over the coefficients.** At a
strictly increasing tuple of coordinate indices, the identification of the Čech term with the
monomial chart of the set of values of the tuple carries the action of the pullback of `r : R` to
multiplication by `r` on Laurent coefficients. -/
theorem ordInterChartAddEquiv_coeffScalar_smul (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ)
    (i : CechCochains.OrdIndex (I := ULift.{u} (Fin (n + 1))) p) (r : R)
    (u : twistInterSections R n d i.1) :
    letI := sectionsModuleOfLE (⊤ : Opens ↑(ProjectiveSpectrum.top (polyGrading R n)))
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
      (W := CechCochains.inter (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
        (basicOpenXAtUniverse R n) i.1) le_top
    ordInterChartAddEquiv R n d p i (coeffScalar R n r • u)
      = r • ordInterChartAddEquiv R n d p i u := by
  have hres := res_smul (⊤ : Opens ↑(ProjectiveSpectrum.top (polyGrading R n)))
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
    (W := ProjectiveSpectrum.basicOpen (polyGrading R n)
      (chartDenom R n (Finset.image (chartIndices i.1) Finset.univ)))
    (W' := CechCochains.inter (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
      (basicOpenXAtUniverse R n) i.1)
    le_top le_top
    (inter_eq_basicOpen_chartDenom R n p i.1 (strictMono_chartIndices i.2).injective).ge
    (coeffScalar R n r) u
  let e : twistChart R n d (↑(Finset.image (chartIndices i.1) Finset.univ) : Set (Fin (n + 1)))
      ≃ₗ[R] twistChart R n d (Set.range (chartIndices i.1)) :=
    LinearEquiv.ofEq _ _ (congrArg (twistChart R n d)
      (coe_image_univ_eq_range (chartIndices i.1)))
  exact (congrArg e ((congrArg (chartSectionsAddEquivTwistChart R n d
        (Finset.image (chartIndices i.1) Finset.univ)
        (image_univ_nonempty (chartIndices i.1))) hres).trans
      (chartSectionsAddEquivTwistChart_coeffScalar_smul R n d
        (Finset.image (chartIndices i.1) Finset.univ)
        (image_univ_nonempty (chartIndices i.1)) r _))).trans (e.map_smul r _)

/-- **The degree-`p` ordered Čech cochains of `𝒪(d)` for the standard cover are the degree-`p`
monomial Čech cochains, `R`-linearly.** The underlying additive equivalence is
`Stacks.ProjectiveSpace.Cohomology.twistOrdCochainEquiv`, and the `R`-action on the Čech cochains
is the action of the global sections of `𝒪` read along
`Stacks.ProjectiveSpace.Cohomology.coeffScalar`. -/
def twistOrdCochainLinearEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ) :
    (((ModuleCat.restrictScalars.{u} (coeffScalar R n)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (twistOrderedComplex R n d)).X p ≃ₗ[R]
      laurentCechCochains R n d p where
  toFun := twistOrdCochainEquiv R n d p
  map_add' := (twistOrdCochainEquiv R n d p).map_add
  invFun := (twistOrdCochainEquiv R n d p).symm
  left_inv := (twistOrdCochainEquiv R n d p).left_inv
  right_inv := (twistOrdCochainEquiv R n d p).right_inv
  map_smul' r s := by
    refine (ordChartEquiv R n d p).injective ?_
    refine ((ordChartEquiv_twistOrdCochainEquiv R n d p _).trans ?_).trans
      (((ordChartEquiv R n d p).map_smul r (twistOrdCochainEquiv R n d p s)).trans
        (congrArg (fun z => r • z)
          (ordChartEquiv_twistOrdCochainEquiv R n d p s))).symm
    refine funext fun i => ?_
    exact ordInterChartAddEquiv_coeffScalar_smul R n d p (ordIndexUp n p i) r
      (s (ordIndexUp n p i))

/-- **The ordered Čech cochains of `𝒪(d)` are the monomial Čech cochains**, as `R`-modules. -/
def twistOrdCochainModuleIso (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ) :
    (((ModuleCat.restrictScalars.{u} (coeffScalar R n)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (twistOrderedComplex R n d)).X p ≅
      ModuleCat.of R (laurentCechCochains R n d p) :=
  LinearEquiv.toModuleIso (twistOrdCochainLinearEquiv R n d p)

/-- **The ordered Čech complex of the standard cover of `ℙⁿ_R` for `𝒪(d)` is the monomial Čech
complex**, as cochain complexes of `R`-modules. -/
def twistOrderedComplexIsoLaurent (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    ((ModuleCat.restrictScalars.{u} (coeffScalar R n)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (twistOrderedComplex R n d) ≅ laurentCechComplex R n d :=
  HomologicalComplex.Hom.isoOfComponents (twistOrdCochainModuleIso R n d) fun {i j} hij => by
    obtain rfl : i + 1 = j := hij
    rw [laurentCechComplex_d]
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun s => ?_
    have hd : (twistOrderedComplex R n d).d i (i + 1)
        = ordModuleDiff (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
          (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) i :=
      orderedModuleComplex_d _ _ _ _ i
    have hD : ConcreteCategory.hom
          ((((ModuleCat.restrictScalars.{u} (coeffScalar R n)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (twistOrderedComplex R n d)).d i (i + 1)) s
        = CechCochains.ordD (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
          (basicOpenXAtUniverse R n)
          (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) i s :=
      congrArg (fun m => ConcreteCategory.hom
        ((ModuleCat.restrictScalars.{u} (coeffScalar R n)).map m) s) hd
    exact (twistOrdCochainEquiv_ordD R n d i s).symm.trans
      (congrArg (twistOrdCochainEquiv R n d (i + 1)) hD.symm)

/-- **The cohomology of `𝒪(d)` on `ℙⁿ_R` is the homology of the monomial Čech complex of the
standard cover**, as `R`-modules. -/
def twistCohomologyIsoLaurentHomology (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ) :
    twistCohomology R n d q ≅ (laurentCechComplex R n d).homology q :=
  twistCohomologyIsoOrderedHomology R n d q ≪≫
    HomologicalComplex.homologyMapIso (twistOrderedComplexIsoLaurent R n d) q

/-! ### The three cases -/

/-- The displayed equation of [Stacks, Tag 01XU] for `ℙⁿ_R` with `n = m + 1 ≥ 1`: the cohomology
of `𝒪(d)` is the degree-`d` part of `R[T₀, …, Tₙ]` in degree `0`, vanishes outside the degrees `0`
and `n`, and is `Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)` in degree `n`. The degree-`e` part of
`R[T₀, …, Tₙ]` is the monomial chart with no variable inverted, which vanishes for `e < 0`; the
last two fields restate the two non-vanishing cases with that chart written as a module of
homogeneous polynomials, in the degrees where the index is a natural number. -/
structure SerreTwistCohomology (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) where
  /-- `H⁰(ℙⁿ_R, 𝒪(d))` is the degree-`d` part of `R[T₀, …, Tₙ]`. -/
  degreeZero : twistCohomology R (m + 1) d 0 ≅
    ModuleCat.of R (twistChart R (m + 1) d (∅ : Set (Fin (m + 1 + 1))))
  /-- `H^q(ℙⁿ_R, 𝒪(d)) = 0` for `q ≠ 0, n`. -/
  vanishing : ∀ q : ℕ, q + 1 ≠ m + 1 → IsZero (twistCohomology R (m + 1) d (q + 1))
  /-- `Hⁿ(ℙⁿ_R, 𝒪(d))` is `Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`. -/
  degreeTop : twistCohomology R (m + 1) d (m + 1) ≅
    ModuleCat.of R (twistChart R (m + 1) (-d - (((m + 1 : ℕ) : ℤ) + 1))
      (∅ : Set (Fin (m + 1 + 1))) →ₗ[R] R)
  /-- The degree-zero case with the polynomials written as homogeneous polynomials. -/
  degreeZeroPolynomial : 0 ≤ d → (twistCohomology R (m + 1) d 0 ≅
    ModuleCat.of R (MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R d.toNat))
  /-- The top-degree case with the polynomials written as homogeneous polynomials. -/
  degreeTopPolynomial : d ≤ -((m + 1 : ℕ) : ℤ) - 1 → (twistCohomology R (m + 1) d (m + 1) ≅
    ModuleCat.of R (MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R
      (-d - (((m + 1 : ℕ) : ℤ) + 1)).toNat →ₗ[R] R))

/-- **Serre's computation of the cohomology of the twists of the structure sheaf on projective
space.** For a commutative ring `R`, `n = m + 1 ≥ 1` and every integer `d`,
`H^q(ℙⁿ_R, 𝒪(d))` is the degree-`d` part of `R[T₀, …, Tₙ]` for `q = 0`, is zero for
`q ≠ 0, n`, and is `Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)` for `q = n`, as `R`-modules. -/
@[stacks 01XU, ega "III 2.1.13" "more general", sga "7 XIX 1.2" "special case"]
def serreTwistCohomology (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    SerreTwistCohomology R m d where
  degreeZero := twistCohomologyIsoLaurentHomology R (m + 1) d 0 ≪≫ homologyZeroIso R m d
  vanishing _ hq := (twistCohomologyIsoLaurentHomology R (m + 1) d _).isZero_iff.2
    (isZero_homology_laurentCechComplex hq)
  degreeTop := twistCohomologyIsoLaurentHomology R (m + 1) d (m + 1) ≪≫ homologyTopIso R m d
  degreeZeroPolynomial hd := twistCohomologyIsoLaurentHomology R (m + 1) d 0 ≪≫
    homologyZeroIso R m d ≪≫ (twistChartEmptyLinearEquiv (R := R) (m + 1) hd).toModuleIso
  degreeTopPolynomial hd := twistCohomologyIsoLaurentHomology R (m + 1) d (m + 1) ≪≫
    homologyTopIso R m d ≪≫
      (twistChartEmptyLinearEquiv (R := R) (m + 1)
        (d := -d - (((m + 1 : ℕ) : ℤ) + 1)) (by omega)).dualMap.symm.toModuleIso

end Stacks.ProjectiveSpace.Cohomology

end
