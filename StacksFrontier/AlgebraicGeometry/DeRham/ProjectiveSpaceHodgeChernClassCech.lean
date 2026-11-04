module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HypercohomologyCechComputes
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.LogarithmicDifferential
public import
    StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyAbelianDegreeOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hodge first Chern class of `𝒪(1)` on Čech cocycles

On `X = ℙⁿ_A = Proj A[T₀, …, Tₙ]` the coordinate `Tᵢ` generates `𝒪(1)` over the standard open
`D₊(Tᵢ)`, so the class of `𝒪(1)` in `H¹(X, 𝒪_X^*)` is the class of the transition cocycle
`T_{i₁} / T_{i₀}` on the standard covering, and its Hodge first Chern class is the class of the
Čech cocycle `d log(T_{i₁} / T_{i₀})` of `Ω_{X/A}`. Lifting `1 ∈ H⁰(X, 𝒪_X)` along the Euler
sequence `0 ⟶ Ω ⟶ 𝒪(-1)^{⊕ (n+1)} ⟶ 𝒪 ⟶ 0` by the local splittings `eᵢ / Tᵢ` of the Euler
contraction, the Čech coboundary of the lift is the image of that same cocycle. Hence the boundary
of `1` along the Euler sequence is `c₁^{Hodge}(𝒪(1))`, which is the step of the proof of
[Stacks, Tag 0FMI] in degree one.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.boundary_euler_one`: the boundary of `1` along
  the Euler sequence is the Hodge first Chern class of `𝒪(1)`.

## References

* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (abSections)
open Stacks.Cech.Hypercohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHodge

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence

variable (A : Type u) [CommRing A] (m : ℕ)

/-- The standard covering of `ℙⁿ_A` by the opens `D₊(Tᵢ)`, indexed in the universe of `A`. -/
def stdCover : ULift.{u} (Fin (m + 2)) → Opens (projSpace A m) :=
  fun i => ProjectiveSpectrum.basicOpen (polyGrading A (m + 1)) (MvPolynomial.X i.down)

/-- The standard opens `D₊(Tᵢ)` cover `ℙⁿ_A`. -/
theorem top_eq_iSup_stdCover : (⊤ : Opens (projSpace A m)) = ⨆ i, stdCover A m i := by
  refine (eq_top_iff.2 fun x _ => ?_).symm
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_X A (m + 1) x
  exact Opens.mem_iSup.2 ⟨ULift.up i, hi⟩

/-- A finite intersection of standard opens lies in each of them. -/
theorem inter_le_stdCover {p : ℕ} (x : Fin (p + 1) → ULift.{u} (Fin (m + 2))) (k : Fin (p + 1)) :
    CechCochains.inter (stdCover A m) x ≤
      ProjectiveSpectrum.basicOpen (polyGrading A (m + 1)) (MvPolynomial.X (x k).down) :=
  iInf_le (fun j => stdCover A m (x j)) k

/-- The Euler sequence `0 ⟶ Ω ⟶ 𝒪(-1)^{⊕ (n+1)} ⟶ 𝒪 ⟶ 0` of `ℙⁿ_A`. -/
@[sga "6 VIII 5.2"]
abbrev eulerSC : ShortComplex (SheafOfModules.{u} (ringSheaf (projSpace A m).sheaf)) :=
  ShortComplex.mk (eulerFirstArrow A (m + 1)) (eulerSurjection A (m + 1))
    (eulerFirstArrow_comp_eulerSurjection A (m + 1))

/-- The Euler sequence of `ℙⁿ_A` is short exact ([Stacks, Tag 0FMH]). -/
@[sga "6 VIII 5.2" "(E), special case", sga "7 XVII 5.1" "more general"]
theorem shortExact_eulerSC : (eulerSC A m).ShortExact :=
  shortExact_eulerSequence A (m + 1)

/-! ### The lift of `1` along the Euler sequence -/

/-- The Čech `0`-cochain of `𝒪(-1)^{⊕ (n+1)}` of the local splittings `eᵢ / Tᵢ` of the Euler
contraction on the standard covering. -/
def eulerLift : CechCochains.Cochain (stdCover A m) (abSections (twistMinusOneSum A (m + 1))) 0 :=
  fun x => eulerSection A (m + 1) (x 0).down (inter_le_stdCover A m x 0)

/-- The local splittings lift the restrictions of `1`. -/
theorem push_eulerSurjection_eulerLift :
    Stacks.Cohomology.CechOne.push (stdCover A m)
        ((SheafOfModules.toSheaf _).map (eulerSurjection A (m + 1))).hom 0 (eulerLift A m) =
      restrictionCochain (stdCover A m) (SheafOfModules.unit (ringSheaf (projSpace A m).sheaf))
        (1 : (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj.obj (op ⊤)) := by
  funext x
  refine (eulerSurjection_app_eulerSection A (m + 1) (x 0).down
    (inter_le_stdCover A m x 0)).trans ?_
  exact (map_one ((ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj.map
    (homOfLE le_top).op).hom).symm

/-! ### The transition cocycle of `𝒪(1)` -/

/-- The generator torsor of `𝒪(1)`: the sheaf of local generators of `𝒪(1)`, a torsor under the
units of `𝒪`. Its class is the class of `𝒪(1)` in `H¹(ℙⁿ_A, 𝒪^*)` ([Stacks, Tag 09NU]). -/
abbrev twistOneTorsor :=
  Stacks.Cohomology.Generators.generatorTorsorOfInvertible (projSpace A m).toRingedSpace
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 1)
    (isInvertible_twistingSheafOne A m)

/-- **The coordinate `Tᵢ` generates `𝒪(1)` over `D₊(Tᵢ)`.** -/
def coordGenerator (i : ULift.{u} (Fin (m + 2))) :
    Stacks.Cohomology.Generators.GeneratorSections (projSpace A m).toRingedSpace
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 1) (stdCover A m i) :=
  ⟨coordSection A (m + 1) i.down (stdCover A m i), fun _ h =>
    (bijective_smul_coordSection A (m + 1) i.down h :)⟩

/-- The local sections `Tᵢ` of the generator torsor of `𝒪(1)` on the standard covering. -/
def twistOneSection (i : ULift.{u} (Fin (m + 2))) : (twistOneTorsor A m).F.obj (stdCover A m i) :=
  ((twistOneTorsor A m).sectionsEquiv (stdCover A m i)).symm (coordGenerator A m i)

/-- **The transition cocycle of `𝒪(1)`** on the standard covering, `T_{i₁} / T_{i₀}`. -/
abbrev twistOneCocycle : CechCochains.cocycles1 (stdCover A m)
    (Stacks.Cohomology.Generators.unitsSheaf (projSpace A m).toRingedSpace).presheaf :=
  Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle (twistOneTorsor A m).toTorsor
    (stdCover A m) (twistOneSection A m)

/-- The local generator `Tᵢ` of `𝒪(1)`, restricted to a smaller open, is `Tᵢ` there. -/
theorem sectionsEquiv_res_twistOneSection (i : ULift.{u} (Fin (m + 2)))
    {W : Opens (projSpace A m)} (h : W ≤ stdCover A m i) :
    ((twistOneTorsor A m).sectionsEquiv W ((twistOneTorsor A m).F.res h
      (twistOneSection A m i))).val = coordSection A (m + 1) i.down W := by
  refine ((twistOneTorsor A m).sectionsEquiv_restrict h (twistOneSection A m i)).trans ?_
  rw [twistOneSection, Equiv.apply_symm_apply]
  rfl

/-- **The transition unit carries `T_{i₀}` to `T_{i₁}`.** -/
theorem twistOneCocycle_smul (y : Fin 2 → ULift.{u} (Fin (m + 2))) :
    ((Additive.toMul ((twistOneCocycle A m).val y) :
        ((ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj.obj
          (op (CechCochains.inter (stdCover A m) y)))ˣ) :
        (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj.obj
          (op (CechCochains.inter (stdCover A m) y))) •
      coordSection A (m + 1) (y 0).down (CechCochains.inter (stdCover A m) y) =
      coordSection A (m + 1) (y 1).down (CechCochains.inter (stdCover A m) y) := by
  have h := Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_spec
    (twistOneTorsor A m).toTorsor (stdCover A m) (twistOneSection A m) y
  refine (congrArg (fun t : ProjectiveSpectrum.Proj.moduleSections (polyGrading A (m + 1))
      (ProjectiveSpectrum.Proj.twistGrading (polyGrading A (m + 1)) 1)
      (CechCochains.inter (stdCover A m) y) => (((Additive.toMul ((twistOneCocycle A m).val y) :
        ((ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj.obj
          (op (CechCochains.inter (stdCover A m) y)))ˣ) :
        (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj.obj
          (op (CechCochains.inter (stdCover A m) y))) • t))
    (sectionsEquiv_res_twistOneSection A m (y 0) (iInf_le _ 0)).symm).trans ?_
  refine ((twistOneTorsor A m).sectionsEquiv_smul (CechCochains.inter (stdCover A m) y)
    (Additive.toMul ((twistOneCocycle A m).val y)) _).symm.trans ?_
  refine (congrArg (fun t => ((twistOneTorsor A m).sectionsEquiv
    (CechCochains.inter (stdCover A m) y) t).val) h).trans ?_
  exact sectionsEquiv_res_twistOneSection A m (y 1) (iInf_le _ 1)

/-! ### The logarithmic differential of the transition cocycle -/

/-- The local splitting of the Euler contraction restricts to the local splitting. -/
theorem restr_eulerSection (i : Fin (m + 2)) {W W' : Opens (projSpace A m)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (polyGrading A (m + 1)) (MvPolynomial.X i))
    (h : W' ≤ W) :
    CechCochains.restr (abSections (twistMinusOneSum A (m + 1))) h
        (eulerSection A (m + 1) i hW) = eulerSection A (m + 1) i (h.trans hW) :=
  eulerSection_restrict A (m + 1) i hW h

/-- **The Čech cocycle `d log (T_{i₁} / T_{i₀})`** of `Ω_{ℙⁿ_A/A}` on the standard covering. -/
def dlogCocycle : CechCochains.cocycles1 (stdCover A m)
    (Scheme.Hom.relativeDifferentialsAbelian (projToSpecCoeff A (m + 1))).presheaf :=
  ⟨Stacks.Cohomology.CechOne.push (stdCover A m)
      (Scheme.Hom.logarithmicDifferentialSheafHom (projToSpecCoeff A (m + 1))).hom 1
      (twistOneCocycle A m).val,
    Stacks.Cohomology.CechOne.cechD_push _ _ 1 _
      ((CechCochains.mem_cocycles1_iff _ _ _).mp (twistOneCocycle A m).2)⟩

/-- **The Euler sequence carries `d log (T_{i₁} / T_{i₀})` to the Čech coboundary of the local
splittings `eᵢ / Tᵢ`.** -/
theorem push_eulerFirstArrow_dlogCocycle :
    Stacks.Cohomology.CechOne.push (stdCover A m)
        ((SheafOfModules.toSheaf _).map (eulerFirstArrow A (m + 1))).hom 1 (dlogCocycle A m).val =
      CechCochains.cechD (stdCover A m) (abSections (twistMinusOneSum A (m + 1))) 0
        (eulerLift A m) := by
  funext y
  refine (eulerFirstArrow_logarithmicDifferential A (m + 1) (inter_le_stdCover A m y 0)
    (inter_le_stdCover A m y 1) (Additive.toMul ((twistOneCocycle A m).val y))
    (twistOneCocycle_smul A m y)).trans ?_
  rw [CechCochains.cechD_apply, Fin.sum_univ_two]
  show _ = (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) • CechCochains.restr
      (abSections (twistMinusOneSum A (m + 1))) (CechCochains.inter_le_omit (stdCover A m) y 0)
      (eulerSection A (m + 1) (y 1).down (inter_le_stdCover A m (y ∘ (0 : Fin 2).succAbove) 0)) +
    (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) • CechCochains.restr
      (abSections (twistMinusOneSum A (m + 1))) (CechCochains.inter_le_omit (stdCover A m) y 1)
      (eulerSection A (m + 1) (y 0).down (inter_le_stdCover A m (y ∘ (1 : Fin 2).succAbove) 0))
  refine Eq.trans ?_ (congrArg₂ (fun a b => (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) • a +
    (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) • b) (restr_eulerSection A m (y 1).down _ _).symm
    (restr_eulerSection A m (y 0).down _ _).symm)
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_smul ℤ _).symm (neg_one_smul ℤ _).symm

/-! ### The boundary of `1` along the Euler sequence -/

/-- **The boundary of `1 ∈ H⁰(ℙⁿ_A, 𝒪)` along the Euler sequence is the class of the Čech cocycle
`d log (T_{i₁} / T_{i₀})`.** -/
theorem boundary_euler_one_eq_cechCocycleClass :
    boundary (projSpace A m).sheaf (singlePlusSC (projSpace A m).sheaf (eulerSC A m))
        (shortExact_singlePlusSC (projSpace A m).sheaf (shortExact_eulerSC A m)) 0 (0 + 1) rfl
        (sectionClass (SheafOfModules.unit (ringSheaf (projSpace A m).sheaf))
          (1 : (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj.obj (op ⊤))) =
      cechCocycleClass (stdCover A m) (top_eq_iSup_stdCover A m) (projDifferentials A (m + 1))
        (dlogCocycle A m).val ((CechCochains.mem_cocycles1_iff _ _ _).mp (dlogCocycle A m).2) :=
  boundary_sectionClass (stdCover A m) (top_eq_iSup_stdCover A m) (shortExact_eulerSC A m) _
    (eulerLift A m) (push_eulerSurjection_eulerLift A m) (dlogCocycle A m).val _
    (push_eulerFirstArrow_dlogCocycle A m)

/-- **The Hodge first Chern class of `𝒪(1)` is the Čech class of `d log (T_{i₁} / T_{i₀})`**, in
the cohomology of `Ω_{ℙⁿ_A/A}` as a sheaf of abelian groups ([Stacks, Tags 09NU, 0FLE]). -/
theorem hodgeFirstChernClassTwistingSheafOne_eq :
    hodgeFirstChernClassTwistingSheafOne A m =
      Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections _ ⊤ (stdCover A m)
        (top_eq_iSup_stdCover A m)
        (Scheme.Hom.relativeDifferentialsAbelian (projToSpecCoeff A (m + 1)))
        (CechCochains.cls _ _ (dlogCocycle A m)) := by
  have h1 := Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard_symm_classOf (projSpace A m)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 1)
    (isInvertible_twistingSheafOne A m)
  have h2 := Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne_of_cocycle _ _
    (twistOneTorsor A m).toTorsor (stdCover A m) (top_eq_iSup_stdCover A m) (twistOneSection A m)
    (twistOneCocycle A m) (Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_spec _ _ _)
  have h3 := Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections_naturality.{u, u, u} _ ⊤
    (stdCover A m) (top_eq_iSup_stdCover A m)
    (Scheme.Hom.logarithmicDifferentialSheafHom (projToSpecCoeff A (m + 1)))
    (twistOneCocycle A m) (dlogCocycle A m) (fun _ => rfl)
  refine Eq.trans ?_ h3
  show ((Stacks.Cohomology.LerayLowDegree.abelianCohomology.{u, u} _ ⊤ 1).map
    (Scheme.Hom.logarithmicDifferentialSheafHom (projToSpecCoeff A (m + 1)))).hom
      ((Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard (projSpace A m)).symm
        (twistingSheafOnePicardClass A m)) = _
  rw [twistingSheafOnePicardClass, h1, h2]

/-- **The Hodge first Chern class of `𝒪(1)`, as a class of the sheaf of modules `Ω_{ℙⁿ_A/A}`**:
its image under the identification of first cohomology of [Stacks, Tag 03FD]. -/
@[sga "7 XI 1.0" "special case", sga "7 XI 1.5" "η for Y = P^{m+1}_A"]
abbrev hodgeFirstChernClassModule :
    hypercohomology (projSpace A m).sheaf
      (singlePlus (projSpace A m).sheaf (projDifferentials A (m + 1)) 0) 1 :=
  abelianToModuleH1 (projDifferentials A (m + 1)) (hodgeFirstChernClassTwistingSheafOne A m)

/-- **The boundary of `1 ∈ H⁰(ℙⁿ_A, 𝒪)` along the Euler sequence is the Hodge first Chern class
of `𝒪(1)`.** This is the degree-one step of the proof of [Stacks, Tag 0FMI]. -/
theorem boundary_euler_one :
    boundary (projSpace A m).sheaf (singlePlusSC (projSpace A m).sheaf (eulerSC A m))
        (shortExact_singlePlusSC (projSpace A m).sheaf (shortExact_eulerSC A m)) 0 (0 + 1) rfl
        (sectionClass (SheafOfModules.unit (ringSheaf (projSpace A m).sheaf))
          (1 : (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A (m + 1))).obj.obj (op ⊤))) =
      hodgeFirstChernClassModule A m := by
  rw [boundary_euler_one_eq_cechCocycleClass, hodgeFirstChernClassModule,
    hodgeFirstChernClassTwistingSheafOne_eq]
  exact (abelianToModuleH1_cechH1ToRightDerivedSections (projDifferentials A (m + 1))
    (stdCover A m) (top_eq_iSup_stdCover A m) (dlogCocycle A m)).symm

end Stacks.AlgebraicGeometry.ProjectiveSpaceHodge
