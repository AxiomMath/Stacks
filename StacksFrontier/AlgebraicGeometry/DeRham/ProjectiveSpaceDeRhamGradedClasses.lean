module

public import StacksFrontier.Algebra.Module.RankOneGenerator
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeClassShifted
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceDeRhamGradedPieces
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyAbelianDegreeOneNaturality

/-!
# The powers of the de Rham first Chern class of `𝒪(1)` on the graded pieces

Let `A` be a commutative ring, `n = m + 1` and `p : ℙⁿ_A ⟶ Spec A` the structure morphism. The
powers `γ₁(𝒪(1))ⁱ ∈ H^{2i}(ℙⁿ_A, σ^{≥i}Ω^•)` of the Hodge-filtered first Chern class of `𝒪(1)`
project to classes in the hypercohomology `H^{2i}(ℙⁿ_A, Ωⁱ[-i])` of the graded pieces of the
brutal filtration, which is `Hⁱ(ℙⁿ_A, Ωⁱ)`. This file shows that, there, they are unit multiples
of the powers `c₁^{Hodge}(𝒪(1))ⁱ` of [Stacks, Tag 0FMI]; this is the step of the proof of
[Stacks, Tag 0FMJ] where the Hodge-to-de Rham spectral sequence identifies the graded pieces.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.gradedChernPow`: the projection of
  `γ₁(𝒪(1))ⁱ` to `H^{2i}(ℙⁿ_A, Ωⁱ[-i])`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.gradedFirstChernClass`: the projection of
  `γ₁(𝒪(1))` to `H²(ℙⁿ_A, Ω¹[-1])`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.gradedEquiv_gradedChernPow_zero`: in degree
  zero it is the unit.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.exists_gradedEquiv_gradedFirstChernClass`: in
  degree one it is a unit multiple of `c₁^{Hodge}(𝒪(1))`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.gradedChernPow_succ`: it is multiplicative.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.exists_gradedEquiv_gradedChernPow`: in every
  degree it is a unit multiple of `c₁^{Hodge}(𝒪(1))ⁱ`.

## References

* [Stacks Project, Tag 0FMJ](https://stacks.math.columbia.edu/tag/0FMJ)
* [Stacks Project, Remark 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cech.Hypercohomology
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)
open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.Cohomology.InvertibleDerived (smulHom smulHom_naturality smulHom_naturality_assoc)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup
  MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjectiveSpaceHodge
open Stacks.AlgebraicGeometry.ProjEulerSequence (projDifferentials)
open Stacks.ProjectiveSpace.Cohomology (coeffScalar)

variable (A : Type u) [CommRing A] (m : ℕ)

/-- The class of `𝒪(1)` in the Picard group of `ℙⁿ_A`, the class whose de Rham first Chern class
is taken. -/
abbrev twistingSheafOneClass :=
  Stacks.SheafOfModules.Picard.classOf (projSpace A m).toRingedSpace.sheaf.obj
    (_root_.structureSheaf (projSpace A m).toRingedSpace.sheaf).property
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 1)
    (isInvertible_twistingSheafOne A m)

/-- **The projection of `γ₁(𝒪(1))ⁱ` to the graded piece `H^{2i}(ℙⁿ_A, Ωⁱ[-i])`** of the brutal
filtration of the de Rham complex, with `Ωⁱ` read over `p⁻¹𝒪_{Spec A}`. -/
abbrev gradedChernPow (i : ℕ) :
    hypercohomology (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
      ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m i)) (i : ℤ))
      (2 * (i : ℤ)) :=
  hypercohomologyMap (baseRingSheaf A m)
    (singlePlusMapAt (baseRingSheaf A m) (eqToHom (deRhamComplexIntTerm A m i)) (i : ℤ))
    (2 * (i : ℤ))
    (hypercohomologyMap (baseRingSheaf A m) (truncPlusπ (deRhamComplexIntCech A m) (i : ℤ))
      (2 * (i : ℤ))
      (SheafOfModules.filteredChernPow (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
        (SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))
        (Scheme.Hom.cechComputesSheaf_deRhamComplexInt_X (structureMorphism A m))
        (twistingSheafOneClass A m) i))

/-- **The unit of the de Rham complex projects to the class of the unit section** of its term in
degree zero. -/
theorem hypercohomologyMap_truncPlusπ_truncatedUnitClass :
    hypercohomologyMap (baseRingSheaf A m) (truncPlusπ (deRhamComplexIntCech A m) 0) 0
        (SheafOfModules.truncatedUnitClass
          (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
          (SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))) =
      sectionClass ((deRhamComplexIntCech A m).X 0)
        ((SheafOfModules.deRhamDifferentialGradedAlgebra
          (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
          (SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))).one.eval (op ⊤)) := by
  have e := congrArg (fun f => hypercohomologyMap (baseRingSheaf A m) f 0
      (sectionClass (unitSheaf (baseRingSheaf A m)) (oneSection (baseRingSheaf A m))))
    (globalCocycleHom_comp_truncPlusπ (O := baseRingSheaf A m)
      (SheafOfModules.deRhamComplexPlus (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
        (SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (structureMorphism A m))))
      _ (unitHom_comp_d_eq_zero (SheafOfModules.deRhamDifferentialGradedAlgebra
        (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
        (SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (structureMorphism A m))))))
  simp only [hypercohomologyMap_comp, ConcreteCategory.comp_apply] at e
  exact e.trans ((hypercohomologyMap_sectionClass _ _).trans (congrArg _ (one_smul _ _)))

/-- **The unit of the de Rham complex is the unit form**: under the identification of the term of
degree zero of the de Rham complex with `Ω⁰` read over `p⁻¹𝒪_{Spec A}`, the unit section is the
unit section `1` of `Ω⁰ = 𝒪`. -/
theorem eqToHom_deRhamUnit_eq_unitForm :
    (eqToHom (deRhamComplexIntTerm A m 0)).val.app (op ⊤)
        ((SheafOfModules.deRhamDifferentialGradedAlgebra
          (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
          (SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))).one.eval (op ⊤)) =
      unitForm A m := by
  have key : ∀ {M N : _root_.SheafOfModules.{u} (ringSheaf (baseRingSheaf A m))} (h : M = N)
      (z : M.val.obj (op ⊤)), HEq ((eqToHom h).val.app (op ⊤) z) z := by
    intro M N h z
    subst h
    rfl
  have hu : unitForm A m = (Scheme.Hom.deRhamAlgebras (structureMorphism A m)).exterior.one.eval
      (op ⊤) := by
    have h1 := (Scheme.Hom.deRhamAlgebras (structureMorphism A m)).exteriorPieceZeroIsoUnit_one
      (op ⊤)
    have h2 : ((Scheme.Hom.deRhamAlgebras
        (structureMorphism A m)).exteriorPieceZeroIsoUnit.inv.val.app (op ⊤)).hom
        (((Scheme.Hom.deRhamAlgebras
          (structureMorphism A m)).exteriorPieceZeroIsoUnit.hom.val.app (op ⊤)).hom
          ((Scheme.Hom.deRhamAlgebras (structureMorphism A m)).exterior.one.eval (op ⊤))) =
        (Scheme.Hom.deRhamAlgebras (structureMorphism A m)).exterior.one.eval (op ⊤) := by
      change (((Scheme.Hom.deRhamAlgebras (structureMorphism A m)).exteriorPieceZeroIsoUnit.hom ≫
        (Scheme.Hom.deRhamAlgebras
          (structureMorphism A m)).exteriorPieceZeroIsoUnit.inv).val.app (op ⊤)).hom _ = _
      rw [Iso.hom_inv_id]
      rfl
    rw [h1] at h2
    exact h2
  rw [hu]
  exact eq_of_heq ((key _ _).trans (SheafOfModules.deRhamDifferentialGradedAlgebra_one _ _ _))

/-- **In degree zero the graded piece of the de Rham complex carries the unit to
`c₁^{Hodge}(𝒪(1))⁰ = 1`.** -/
theorem gradedEquiv_gradedChernPow_zero :
    gradedEquiv A m 0 0 (gradedChernPow A m 0) = chernPowR2 A m 0 := by
  have h := hypercohomologyMap_truncPlusπ_truncatedUnitClass A m
  have h2 := hypercohomologyMap_sectionClass (O := baseRingSheaf A m)
    (eqToHom (deRhamComplexIntTerm A m 0))
    ((SheafOfModules.deRhamDifferentialGradedAlgebra
      (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
      (SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))).one.eval (op ⊤))
  rw [eqToHom_deRhamUnit_eq_unitForm] at h2
  have h3 := restrictScalarsCechEquiv_sectionClass (baseRingHom A m) (forms A m 0)
    (cechComputes_forms_restrictScalars A m 0 0) (cechComputesSheaf_forms A m 0) (unitForm A m)
  refine Eq.trans ?_ h3
  exact congrArg (gradedEquiv A m 0 0) ((congrArg (hypercohomologyMap (baseRingSheaf A m)
    (singlePlusMapAt (baseRingSheaf A m) (eqToHom (deRhamComplexIntTerm A m 0)) 0) 0) h).trans h2)

/-! ### Degree one -/

section DegreeOne

/-- The scalar `a ∈ A` as a global section of the base ring sheaf `p⁻¹𝒪_{Spec A}`. -/
abbrev baseScalar (a : A) : SectionRing (ringSheaf (baseRingSheaf A m)) ⊤ :=
  (Scheme.Hom.inverseImageGlobalSections (structureMorphism A m)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)

/-- **The identification `H¹(ℙⁿ_A, Ω) ≅ H²(ℙⁿ_A, Ω¹[-1])` is compatible with the coefficients**:
multiplication by `a ∈ A` on `Ω` induces multiplication by `a` on `H²(ℙⁿ_A, Ω¹[-1])`. -/
theorem hodgeOneShiftedEquiv_smulHom (a : A)
    (x : ((sectionsFunctor (projSpace A m).carrier ⊤).rightDerived 1).obj
      ((_root_.SheafOfModules.toSheaf (projSpace A m).ringCatSheaf).obj
        (Scheme.Hom.relativeDifferentials (structureMorphism A m)))) :
    Scheme.Hom.hodgeOneShiftedEquiv (structureMorphism A m)
        ((((sectionsFunctor (projSpace A m).carrier ⊤).rightDerived 1).map
          ((_root_.SheafOfModules.toSheaf (projSpace A m).ringCatSheaf).map
            (smulHom (X := (projSpace A m).toRingedSpace) (coeffScalar A (m + 1) a)
              (Scheme.Hom.relativeDifferentials (structureMorphism A m))))).hom x) =
      baseScalar A m a • Scheme.Hom.hodgeOneShiftedEquiv (structureMorphism A m) x := by
  let B := Scheme.Hom.deRhamAlgebras (structureMorphism A m)
  let D := SheafOfModules.deRhamDifferential B
  let f : (SheafOfModules.deRhamComplex B D).X 1 ⟶ (SheafOfModules.deRhamComplex B D).X 1 :=
    smulHom (X := SheafOfModules.baseRingedSpace (X := (projSpace A m).toRingedSpace)
      (baseRingSheaf A m)) (baseScalar A m a) _
  have hf : (_root_.SheafOfModules.toSheaf (projSpace A m).ringCatSheaf).map
      (smulHom (X := (projSpace A m).toRingedSpace) (coeffScalar A (m + 1) a) (forms A m 1)) =
      (_root_.SheafOfModules.toSheaf (SheafOfModules.underlyingRingSheaf (baseRingSheaf A m))).map
        f := by
    rw [← baseRingHom_app_top A m a]
    exact congrArg (_root_.SheafOfModules.toSheaf
      (SheafOfModules.underlyingRingSheaf (baseRingSheaf A m))).map
        (restrictScalars_map_smulHom A m (baseScalar A m a) (forms A m 1))
  let H := (sectionsFunctor (projSpace A m).carrier ⊤).rightDerived 1
  let T := _root_.SheafOfModules.toSheaf (projSpace A m).ringCatSheaf
  let gen := Scheme.Modules.exteriorGenerator
    (Scheme.Hom.relativeDifferentials (structureMorphism A m))
  let mΩ := smulHom (X := (projSpace A m).toRingedSpace) (coeffScalar A (m + 1) a)
    (Scheme.Hom.relativeDifferentials (structureMorphism A m))
  let m₁ := smulHom (X := (projSpace A m).toRingedSpace) (coeffScalar A (m + 1) a) (forms A m 1)
  have key : (H.map (T.map gen)).hom ((H.map (T.map mΩ)).hom x) =
      (H.map (T.map m₁)).hom ((H.map (T.map gen)).hom x) := by
    have comp : ∀ {P Q R : _root_.SheafOfModules.{u} (projSpace A m).ringCatSheaf}
        (g₁ : P ⟶ Q) (g₂ : Q ⟶ R) (y : H.obj (T.obj P)),
        (H.map (T.map g₂)).hom ((H.map (T.map g₁)).hom y) = (H.map (T.map (g₁ ≫ g₂))).hom y :=
      fun g₁ g₂ y => by
        simp only [Functor.map_comp, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    exact (comp mΩ gen x).trans ((congrArg (fun g => (H.map (T.map g)).hom x)
      (smulHom_naturality (X := (projSpace A m).toRingedSpace)
        (coeffScalar A (m + 1) a) gen).symm).trans (comp gen m₁ x).symm)
  have e3 : SheafOfModules.formsOneIntMap B D f =
      smulHom (X := SheafOfModules.baseRingedSpace (X := (projSpace A m).toRingedSpace)
        (baseRingSheaf A m)) (baseScalar A m a) _ := by
    let e := (SheafOfModules.deRhamComplex B D).extendXIso embeddingUpNat (i := 1) (i' := 1) rfl
    have n := smulHom_naturality (X := SheafOfModules.baseRingedSpace
      (X := (projSpace A m).toRingedSpace) (baseRingSheaf A m)) (baseScalar A m a) e.inv
    change e.hom ≫ f ≫ e.inv = _
    exact (congrArg (e.hom ≫ ·) n.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) e.hom_inv_id).trans (Category.id_comp _)))
  refine (Scheme.Hom.hodgeOneShiftedEquiv_apply _ _).trans ?_
  refine (congrArg (SheafOfModules.shiftedFormsOneComparison B D)
      (key.trans (congrArg (fun g => (H.map g).hom ((H.map (T.map gen)).hom x)) hf))).trans ?_
  refine (SheafOfModules.shiftedFormsOneComparison_naturality B D f _).trans ?_
  refine (congrArg (fun g => hypercohomologyMap (baseRingSheaf A m)
      (singlePlusMapAt (baseRingSheaf A m) g 1) 2
      (SheafOfModules.shiftedFormsOneComparison B D ((H.map (T.map gen)).hom x))) e3).trans ?_
  have hc := hypercohomologyMap_smulHom (X := SheafOfModules.baseRingedSpace
      (X := (projSpace A m).toRingedSpace) (baseRingSheaf A m)) (baseScalar A m a)
    ((SheafOfModules.deRhamComplexInt B D).X 1) 1
    ((Scheme.Hom.cechComputesSheaf_deRhamComplexInt_X (structureMorphism A m) 1).singlePlus
      _ 1) 2 (SheafOfModules.shiftedFormsOneComparison B D ((H.map (T.map gen)).hom x))
  exact hc

/-- **The projection of `γ₁(𝒪(1))` to the graded piece `H²(ℙⁿ_A, Ω¹[-1])`**, with `Ω¹` read over
`p⁻¹𝒪_{Spec A}`. -/
abbrev gradedFirstChernClass :
    hypercohomology (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
      ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m 1)) 1) 2 :=
  hypercohomologyMap (baseRingSheaf A m)
    (singlePlusMapAt (baseRingSheaf A m) (eqToHom (deRhamComplexIntTerm A m 1)) 1) 2
    (hypercohomologyMap (baseRingSheaf A m) (truncPlusπ (deRhamComplexIntCech A m) 1) 2
      (SheafOfModules.filteredFirstChernClassModule
        (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
        (SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))
        (twistingSheafOneClass A m)))

/-- The identification `H¹(ℙⁿ_A, Ω) ≅ H¹(ℙⁿ_A, Ω¹)` of cohomology of sheaves of modules induced by
the degree-one generator `Ω ⟶ ⋀¹Ω = Ω¹`, an isomorphism. -/
abbrev generatorIso :
    hypercohomology (projSpace A m).sheaf
        (singlePlus (projSpace A m).sheaf (projDifferentials A (m + 1)) 0) 1 ≅
      hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m 1) 0) 1 :=
  hypercohomologySingleIso (projSpace A m).sheaf
    (@asIso _ _ _ _ (Scheme.Modules.exteriorGenerator
        (Scheme.Hom.relativeDifferentials (structureMorphism A m)))
      (Scheme.Hom.isIso_exteriorGenerator_relativeDifferentials (structureMorphism A m))) 1

/-- **On `H²(ℙⁿ_A, Ω¹[-1])` the image of `γ₁(𝒪(1))` is a unit multiple of
`c₁^{Hodge}(𝒪(1))`.** Both `H¹(ℙⁿ_A, Ω)` of the abelian sheaf and of the sheaf of modules carry an
action of `A`, and the two identifications with `H¹(ℙⁿ_A, Ω)` — through `H²(ℙⁿ_A, Ω¹[-1])`, and
through Čech cocycles — are compatible with it; the first is bijective and the target is free of
rank one, so they differ by a scalar, which is a unit because `c₁^{Hodge}(𝒪(1))` is a basis
element. -/
theorem exists_gradedEquiv_gradedFirstChernClass :
    ∃ ε : Aˣ, gradedEquiv A m 1 1 (gradedFirstChernClass A m) =
      (show SectionRing (ringSheaf (projSpace A m).sheaf) ⊤ from coeffScalar A (m + 1) ε) •
        (generatorIso A m).hom (hodgeFirstChernClassModule A m) := by
  let Ω := Scheme.Hom.relativeDifferentials (structureMorphism A m)
  let H := (sectionsFunctor (projSpace A m).carrier ⊤).rightDerived 1
  let T := _root_.SheafOfModules.toSheaf (projSpace A m).ringCatSheaf
  let eqIso := hypercohomologyMapIso (baseRingSheaf A m)
    (eqToIso (congrArg (fun F => singlePlus (baseRingSheaf A m) F 1)
      (deRhamComplexIntTerm A m 1))) 2
  let e : H.obj (T.obj Ω) ≃+ (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
      (hypercohomology (projSpace A m).sheaf
        (singlePlus (projSpace A m).sheaf (projDifferentials A (m + 1)) 0) 1) :=
    ((Scheme.Hom.hodgeOneShiftedEquiv (structureMorphism A m)).trans
      eqIso.toLinearEquiv.toAddEquiv).trans
      ((gradedEquiv A m 1 1).trans (generatorIso A m).symm.toLinearEquiv.toAddEquiv)
  obtain ⟨b, hb⟩ := exists_basis_chernPowR2 A m 1 (by omega)
  let G := ((ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).mapIso
    (generatorIso A m)).toLinearEquiv
  let L : (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
      (hypercohomology (projSpace A m).sheaf
        (singlePlus (projSpace A m).sheaf (projDifferentials A (m + 1)) 0) 1) →
      (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
        (hypercohomology (projSpace A m).sheaf
          (singlePlus (projSpace A m).sheaf (forms A m 1) 0) ((1 : ℕ) : ℤ)) := fun y =>
    cup (projSpace A m).sheaf (cechComputesSheaf_forms A m 0)
      (cechComputesSheaf_differentials A m) (wedgePairing A m 0) ((0 : ℕ) : ℤ) 1
      ((0 + 1 : ℕ) : ℤ) rfl (chernPowR2 A m 0) y
  have hL : ∀ (r : A) y, L (r • y) = r • L y := fun r y =>
    cup_smul_right (projSpace A m).sheaf _ _ _ _ _ _ _ _ _ (coeffScalar A (m + 1) r)
  let τ : A → H.obj (T.obj Ω) → H.obj (T.obj Ω) := fun r x =>
    (H.map (T.map (smulHom (X := (projSpace A m).toRingedSpace) (coeffScalar A (m + 1) r) Ω))).hom x
  have hτβ : ∀ (r : A) x, abelianToModuleH1 (projDifferentials A (m + 1)) (τ r x) =
      r • (show (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj
        (hypercohomology (projSpace A m).sheaf
          (singlePlus (projSpace A m).sheaf (projDifferentials A (m + 1)) 0) 1) from
        abelianToModuleH1 (projDifferentials A (m + 1)) x) := fun r x =>
    (abelianToModuleH1_naturality (smulHom (X := (projSpace A m).toRingedSpace)
      (coeffScalar A (m + 1) r) Ω) x).trans
      (hypercohomologyMap_smulHom (X := (projSpace A m).toRingedSpace) (coeffScalar A (m + 1) r)
        Ω 0 (cechComputesSheaf_differentials A m) 1 _)
  have hτα : ∀ (r : A) x, e (τ r x) = r • e x := fun r x => by
    have h1 := hodgeOneShiftedEquiv_smulHom A m r x
    have h2 := congrArg (fun z => gradedEquiv A m 1 1 (eqIso.hom z)) h1
    have h3 := gradedEquiv_smul A m 1 1 (baseScalar A m r) (eqIso.hom
      (Scheme.Hom.hodgeOneShiftedEquiv (structureMorphism A m) x))
    rw [baseRingHom_app_top] at h3
    have h4 := congrArg (generatorIso A m).inv.hom ((h2.trans (congrArg (gradedEquiv A m 1 1)
      (map_smul eqIso.hom.hom _ _))).trans h3)
    exact h4.trans (map_smul (generatorIso A m).inv.hom _ _)
  obtain ⟨ε, hε⟩ := exists_unit_smul_eq_of_bijective_of_semilinear (b.map G.symm) b L hL τ e
    (fun x => abelianToModuleH1 (projDifferentials A (m + 1)) x) e.bijective hτα hτβ
    (hodgeFirstChernClassTwistingSheafOne A m) hb.symm
  refine ⟨ε, ?_⟩
  have h1 : gradedFirstChernClass A m = eqIso.hom
      (Scheme.Hom.hodgeOneShiftedEquiv (structureMorphism A m)
        (hodgeFirstChernClassTwistingSheafOne A m)) := by
    refine (congrArg (hypercohomologyMap (baseRingSheaf A m)
      (singlePlusMapAt (baseRingSheaf A m) (eqToHom (deRhamComplexIntTerm A m 1)) 1) 2)
      (Scheme.Hom.hypercohomologyMap_truncPlusπ_filteredFirstChernClassModule
        (structureMorphism A m) _ (isInvertible_twistingSheafOne A m))).trans ?_
    rw [singlePlusMapAt_eqToHom]
    rfl
  have h5 := congrArg (generatorIso A m).hom.hom hε
  exact (congrArg (gradedEquiv A m 1 1) h1).trans
    ((Iso.inv_hom_id_apply (generatorIso A m) _).symm.trans (h5.trans
      ((generatorIso A m).hom.hom.map_smul _ _)))

end DegreeOne

/-! ### The powers -/

section Powers

/-- **The projection of `γ₁(𝒪(1))^{i+1}` to its graded piece is the cup product**, for the wedge
product of forms, of the projections of `γ₁(𝒪(1))ⁱ` and of `γ₁(𝒪(1))` ([Stacks, Remark 0FME]). -/
theorem gradedChernPow_succ (i : ℕ) :
    gradedChernPow A m (i + 1) =
      cup (baseRingSheaf A m) (cechComputes_forms_restrictScalars A m i i)
        (cechComputes_forms_restrictScalars A m 1 1)
        (singlePairingAt (i : ℤ) ((1 : ℕ) : ℤ) (bilinearPairing (formsMul A m i 1)))
        (2 * (i : ℤ)) 2 (2 * ((i + 1 : ℕ) : ℤ)) (by push_cast; ring)
        (gradedChernPow A m i) (gradedFirstChernClass A m) := by
  have h := SheafOfModules.hypercohomologyMap_truncPlusπ_filteredChernPow_succ
    (Scheme.Hom.deRhamAlgebras (structureMorphism A m))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (structureMorphism A m)))
    (Scheme.Hom.cechComputesSheaf_deRhamComplexInt_X (structureMorphism A m))
    (twistingSheafOneClass A m) i
  refine (congrArg (hypercohomologyMap (baseRingSheaf A m)
    (singlePlusMapAt (baseRingSheaf A m) (eqToHom (deRhamComplexIntTerm A m (i + 1)))
      ((i : ℤ) + ((1 : ℕ) : ℤ))) (2 * ((i + 1 : ℕ) : ℤ))) h).trans ?_
  exact cup_natural (baseRingSheaf A m) _ _ _ _ _ _ _ _ _ (pairingHom_deRhamCechPairing A m i 1)
    _ _ _ _ _ _

/-- The wedge product `Ωⁱ × Ω¹ ⟶ Ω^{i+1}` of differential forms on `ℙⁿ_A`. -/
abbrev formsMulO (i : ℕ) :
    Stacks.BilinearMap (forms A m i).val (forms A m 1).val (forms A m (i + 1)).val :=
  (Scheme.Modules.exteriorAlgebra (X := projSpace A m)
    (Scheme.Hom.relativeDifferentials (structureMorphism A m))).mul (i : ℤ) 1

/-- **The cup product with the image of a class of `Ω` in `Ω¹` is the cup product for the wedge
product `Ωⁱ × Ω ⟶ Ω^{i+1}`.** -/
theorem cup_generatorIso (i : ℕ)
    (x : hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf (forms A m i) 0)
      (i : ℤ))
    (c : hypercohomology (projSpace A m).sheaf
      (singlePlus (projSpace A m).sheaf (projDifferentials A (m + 1)) 0) 1) :
    cup (projSpace A m).sheaf (cechComputesSheaf_forms A m i) (cechComputesSheaf_forms A m 1)
        (singlePairing (bilinearPairing (formsMulO A m i))) (i : ℤ) ((1 : ℕ) : ℤ)
        ((i + 1 : ℕ) : ℤ) (by push_cast; rfl) x ((generatorIso A m).hom c) =
      cup (projSpace A m).sheaf (cechComputesSheaf_forms A m i)
        (cechComputesSheaf_differentials A m) (wedgePairing A m i) (i : ℤ) 1
        ((i + 1 : ℕ) : ℤ) (by push_cast; rfl) x c := by
  have hP := pairingHom_singlePairing (O := (projSpace A m).sheaf) (𝟙 (forms A m i))
    (Scheme.Modules.exteriorGenerator
      (Scheme.Hom.relativeDifferentials (structureMorphism A m)))
    (𝟙 (forms A m (i + 1))) (wedgeBilinear A m i) (formsMulO A m i) (fun _ _ _ => rfl)
  have hid : ∀ (F : SheafOfModules.{u} (ringSheaf (projSpace A m).sheaf)) (n : ℤ)
      (z : hypercohomology (projSpace A m).sheaf (singlePlus (projSpace A m).sheaf F 0) n),
      hypercohomologyMap (projSpace A m).sheaf (singlePlusMap (projSpace A m).sheaf (𝟙 F)) n z =
        z := fun F n z => by
    have h1 : singlePlusMap (projSpace A m).sheaf (𝟙 F) = 𝟙 _ :=
      ObjectProperty.hom_ext _ ((HomologicalComplex.single _ (up ℤ) 0).map_id F)
    rw [h1, hypercohomologyMap_id]
    rfl
  have h := cup_natural (projSpace A m).sheaf (cechComputesSheaf_forms A m i)
    (cechComputesSheaf_differentials A m) (cechComputesSheaf_forms A m i)
    (cechComputesSheaf_forms A m 1) _ _ _ _ _ hP (i : ℤ) 1 ((i + 1 : ℕ) : ℤ) (by push_cast; rfl)
    x c
  exact (congrArg (fun z => cup (projSpace A m).sheaf (cechComputesSheaf_forms A m i)
      (cechComputesSheaf_forms A m 1) (singlePairing (bilinearPairing (formsMulO A m i)))
      (i : ℤ) ((1 : ℕ) : ℤ) ((i + 1 : ℕ) : ℤ) (by push_cast; rfl) z ((generatorIso A m).hom c))
    (hid (forms A m i) _ x).symm).trans (h.symm.trans (hid (forms A m (i + 1)) _ _))

/-- **On `H^{2i}(ℙⁿ_A, Ωⁱ[-i]) = Hⁱ(ℙⁿ_A, Ωⁱ)` the image of `γ₁(𝒪(1))ⁱ` is a unit multiple of
`c₁^{Hodge}(𝒪(1))ⁱ`**, by induction on `i`: in degree zero both are the unit, and the step is
the multiplicativity of the projection to the graded pieces, the compatibility of the
identification of the graded pieces with cup products, and the degree-one case. -/
theorem exists_gradedEquiv_gradedChernPow (i : ℕ) :
    ∃ ε : Aˣ, gradedEquiv A m i i
        ((eqToHom (congrArg (hypercohomology (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
          ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m i)) (i : ℤ)))
          (two_mul (i : ℤ)))).hom (gradedChernPow A m i)) =
      (show SectionRing (ringSheaf (projSpace A m).sheaf) ⊤ from coeffScalar A (m + 1) ε) •
        chernPowR2 A m i := by
  induction i with
  | zero =>
    refine ⟨1, (gradedEquiv_gradedChernPow_zero A m).trans ?_⟩
    exact (one_smul _ _).symm.trans
      (congrArg (fun r : SectionRing (ringSheaf (projSpace A m).sheaf) ⊤ =>
        r • chernPowR2 A m 0) ((map_one (coeffScalar A (m + 1))).symm.trans
          (congrArg (coeffScalar A (m + 1)) Units.val_one.symm)))
  | succ i ih =>
    obtain ⟨εi, hi⟩ := ih
    obtain ⟨ε₁, h₁⟩ := exists_gradedEquiv_gradedFirstChernClass A m
    let σ : ℤˣ := ((i : ℤ) * ((1 : ℕ) : ℤ)).negOnePow
    refine ⟨Units.map (Int.castRingHom A).toMonoidHom σ * εi * ε₁, ?_⟩
    have hcup := cup_eqToHom (baseRingSheaf A m) (cechComputes_forms_restrictScalars A m i i)
      (cechComputes_forms_restrictScalars A m 1 1)
      (singlePairingAt (i : ℤ) ((1 : ℕ) : ℤ) (bilinearPairing (formsMul A m i 1)))
      (two_mul (i : ℤ)) (rfl : (2 : ℤ) = ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ))
      (two_mul ((i + 1 : ℕ) : ℤ)) (by push_cast; ring) (by push_cast; ring)
      (gradedChernPow A m i) (gradedFirstChernClass A m)
    have hΘ := restrictScalarsCechEquiv_cup (baseRingHom A m) (forms A m i) (i : ℤ)
      ((1 : ℕ) : ℤ) (formsMulO A m i) (cechComputes_forms_restrictScalars A m i i)
      (cechComputes_forms_restrictScalars A m 1 1)
      (cechComputes_forms_restrictScalars A m (i + 1) (i + 1)) (cechComputesSheaf_forms A m i)
      (cechComputesSheaf_forms A m 1) (cechComputesSheaf_forms A m (i + 1)) i 1
      ((eqToHom (congrArg (hypercohomology (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
          ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m i)) (i : ℤ)))
          (two_mul (i : ℤ)))).hom (gradedChernPow A m i))
      (gradedFirstChernClass A m)
    have e1 : gradedEquiv A m (i + 1) (i + 1)
        ((eqToHom (congrArg (hypercohomology (baseRingSheaf A m) (singlePlus (baseRingSheaf A m)
          ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m (i + 1)))
            ((i + 1 : ℕ) : ℤ))) (two_mul ((i + 1 : ℕ) : ℤ)))).hom (gradedChernPow A m (i + 1))) =
        (σ : ℤ) • cup (projSpace A m).sheaf (cechComputesSheaf_forms A m i)
          (cechComputesSheaf_forms A m 1) (singlePairing (bilinearPairing (formsMulO A m i)))
          (i : ℤ) ((1 : ℕ) : ℤ) ((i + 1 : ℕ) : ℤ) (by push_cast; rfl)
          (gradedEquiv A m i i ((eqToHom (congrArg (hypercohomology (baseRingSheaf A m)
            (singlePlus (baseRingSheaf A m)
              ((_root_.SheafOfModules.restrictScalars (baseRingHom A m)).obj (forms A m i))
              (i : ℤ))) (two_mul (i : ℤ)))).hom (gradedChernPow A m i)))
          (gradedEquiv A m 1 1 (gradedFirstChernClass A m)) := by
      rw [gradedChernPow_succ]
      exact (congrArg (gradedEquiv A m (i + 1) (i + 1)) hcup.symm).trans hΘ
    refine e1.trans ?_
    rw [hi, h₁]
    let r : SectionRing (ringSheaf (projSpace A m).sheaf) ⊤ := coeffScalar A (m + 1) εi
    let r₁ : SectionRing (ringSheaf (projSpace A m).sheaf) ⊤ := coeffScalar A (m + 1) ε₁
    have e3 := (cup_smul_left (projSpace A m).sheaf (cechComputesSheaf_forms A m i)
      (cechComputesSheaf_forms A m 1) (singlePairing (bilinearPairing (formsMulO A m i)))
      (i : ℤ) ((1 : ℕ) : ℤ) ((i + 1 : ℕ) : ℤ) (by push_cast; rfl) (chernPowR2 A m i)
      (r₁ • (generatorIso A m).hom (hodgeFirstChernClassModule A m)) r).trans
      (congrArg (r • ·) (cup_smul_right (projSpace A m).sheaf (cechComputesSheaf_forms A m i)
        (cechComputesSheaf_forms A m 1) (singlePairing (bilinearPairing (formsMulO A m i)))
        (i : ℤ) ((1 : ℕ) : ℤ) ((i + 1 : ℕ) : ℤ) (by push_cast; rfl) (chernPowR2 A m i)
        ((generatorIso A m).hom (hodgeFirstChernClassModule A m)) r₁))
    have e4 := cup_generatorIso A m i (chernPowR2 A m i) (hodgeFirstChernClassModule A m)
    refine (congrArg ((σ : ℤ) • ·) (e3.trans (congrArg (fun z => r • r₁ • z) e4))).trans ?_
    have hc : (((σ : ℤ) : SectionRing (ringSheaf (projSpace A m).sheaf) ⊤) * r * r₁ :
        SectionRing (ringSheaf (projSpace A m).sheaf) ⊤) = coeffScalar A (m + 1)
          ((Units.map (Int.castRingHom A).toMonoidHom σ * εi * ε₁ : Aˣ) : A) := by
      rw [Units.val_mul, Units.val_mul, map_mul, map_mul, Units.coe_map]
      exact congrArg (· * r * r₁) (map_intCast (coeffScalar A (m + 1)) (σ : ℤ)).symm
    have hs : (σ : ℤ) • r • r₁ • chernPowR2 A m (i + 1) =
        (((σ : ℤ) : SectionRing (ringSheaf (projSpace A m).sheaf) ⊤) * r * r₁) •
          chernPowR2 A m (i + 1) := by
      rw [mul_smul, mul_smul, Int.cast_smul_eq_zsmul]
    exact hs.trans (congrArg (fun c : SectionRing (ringSheaf (projSpace A m).sheaf) ⊤ =>
      c • chernPowR2 A m (i + 1)) hc)

end Powers

end Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham
