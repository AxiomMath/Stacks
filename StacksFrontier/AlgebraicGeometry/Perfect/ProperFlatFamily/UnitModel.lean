module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.FibreTransport
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsArbitraryBase
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# The unit of a proper flat family, as a chain map into the Čech model

Let `f : X ⟶ Spec A` and let `U` be a finite family of opens covering `X`. The base ring `A`,
placed in degree zero, maps to the `ℤ`-indexed Čech model `baseAlternatingCechComplex f U hU 𝒪_X`
of the structure sheaf: `a` goes to the restriction to the members of `U` of the global function
`f^#(a)`. On `H⁰` this is the unit `A ⟶ Γ(X, 𝒪_X)`. The source of this chain map is a bounded
perfect complex of flat modules.

## Main definitions

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseUnitComplex`: `A` in degree zero.
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.unitCochain`: the degree-zero component.
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.sectionModelMap`: the chain map
  `A ⟶ RΓ(X, F)` of a global section, and `unitModelMap`, the case of `1 ∈ Γ(X, 𝒪_X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

section Source

variable (A : Type u) [CommRing A]

/-- **`A` placed in degree zero.** -/
abbrev baseUnitComplex : CochainComplex (ModuleCat.{u} A) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj (ModuleCat.of A A)

/-- `A` placed in degree zero is strictly concentrated in degrees `≥ 0`. -/
instance : (baseUnitComplex A).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

/-- `A` placed in degree zero is strictly concentrated in degrees `≤ 0`. -/
instance : (baseUnitComplex A).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

private theorem baseUnitComplex_X_finite_projective (i : ℤ) :
    Module.Finite A ((baseUnitComplex A).X i) ∧ Module.Projective A ((baseUnitComplex A).X i) := by
  by_cases hi : i = 0
  · subst hi
    let e : (baseUnitComplex A).X 0 ≃ₗ[A] A :=
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩
  · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of A A) i hi
    have : Subsingleton ((baseUnitComplex A).X i) := ModuleCat.subsingleton_of_isZero hz
    exact ⟨inferInstance, inferInstance⟩

/-- Every term of `A` placed in degree zero is a flat `A`-module. -/
instance (i : ℤ) : Module.Flat A ((baseUnitComplex A).X i) :=
  have := (baseUnitComplex_X_finite_projective A i).2
  inferInstance

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `A` in degree zero is perfect. -/
theorem isPerfect_baseUnitComplex :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (baseUnitComplex A)) :=
  ⟨baseUnitComplex A, 0, 0, inferInstance, inferInstance,
    fun i => (baseUnitComplex_X_finite_projective A i).1,
    fun i => (baseUnitComplex_X_finite_projective A i).2, ⟨Iso.refl _⟩⟩

end Source

section Map

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)

/-- **The degree-zero component of the map `A ⟶ RΓ(X, F)` given by a global section `σ`.**
`a ∈ A` goes to the alternating `0`-cochain restricting `a • σ` to the members of `U`. -/
def sectionCochain (F : X.Modules) (σ : Γ(F, ⊤)) :
    ModuleCat.of A A ⟶ (baseAlternatingCechComplex f U hU F).X 0 :=
  letI := Stacks.Cech.sectionsModule f F ⊤
  ModuleCat.ofHom ((Stacks.Cech.sectionsToAlternatingₗ f U F (fun _ => le_top)).comp
    (LinearMap.toSpanSingleton A _ σ)) ≫ (baseAlternatingCechComplexXIso f U hU F 0).inv

/-- The `0`-cochain `sectionCochain f U hU F σ` is a cocycle: its composite with the Čech
differential in degree `0` vanishes. -/
theorem sectionCochain_comp_d (hcov : (⊤ : X.Opens) ≤ ⨆ i, U i) (F : X.Modules)
    (σ : Γ(F, ⊤)) :
    sectionCochain f U hU F σ ≫ (baseAlternatingCechComplex f U hU F).d 0 1 = 0 := by
  let := Stacks.Cech.sectionsModule f F ⊤
  let := Stacks.Cech.cochainModule f U F 0
  let := Stacks.Cech.cochainModule f U F 1
  ext
  have hr := Stacks.Cech.range_sectionsToAlternatingₗ f U F (fun _ => le_top) hcov
  set y := Stacks.Cech.sectionsToAlternatingₗ f U F (fun _ => le_top) ((1 : A) • σ)
  have hm : y ∈ LinearMap.ker (Stacks.Cech.alternatingCechModuleD f U F 0) :=
    hr ▸ LinearMap.mem_range_self _ _
  have h := congr($(baseAlternatingCechComplexXIso_inv_comp_d f U hU F 0) y)
  show (baseAlternatingCechComplex f U hU F).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ)
    ((baseAlternatingCechComplexXIso f U hU F 0).inv y) = 0
  refine h.trans ?_
  show (baseAlternatingCechComplexXIso f U hU F (0 + 1)).inv
    (Stacks.Cech.alternatingCechModuleD f U F 0 y) = 0
  rw [LinearMap.mem_ker.1 hm]
  exact ((baseAlternatingCechComplexXIso f U hU F (0 + 1)).inv).hom.map_zero

/-- **The map `A ⟶ RΓ(X, F)` given by a global section, on the Čech model.** -/
def sectionModelMap (hcov : (⊤ : X.Opens) ≤ ⨆ i, U i) (F : X.Modules) (σ : Γ(F, ⊤)) :
    baseUnitComplex A ⟶ baseAlternatingCechComplex f U hU F :=
  HomologicalComplex.mkHomFromSingle (sectionCochain f U hU F σ) (by
    rintro k hk
    obtain rfl : k = 1 := by simpa using hk.symm
    exact sectionCochain_comp_d f U hU hcov F σ)

/-- The map of a global section on `r ∈ A`, placed in degree zero. -/
theorem sectionModelMap_f_zero_apply (hcov : (⊤ : X.Opens) ≤ ⨆ i, U i) (F : X.Modules)
    (σ : Γ(F, ⊤)) (r : A) :
    (sectionModelMap f U hU hcov F σ).f 0
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv r) =
      sectionCochain f U hU F σ r := by
  simp [sectionModelMap]

/-- **The degree-zero component of the unit.** `a ∈ A` goes to the alternating `0`-cochain
restricting the global function `a • 1` to the members of `U`. -/
abbrev unitCochain : ModuleCat.of A A ⟶
    (baseAlternatingCechComplex f U hU (SheafOfModules.unit X.ringCatSheaf)).X 0 :=
  sectionCochain f U hU (SheafOfModules.unit X.ringCatSheaf)
    (show Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) from (1 : Γ(X, ⊤)))

/-- The `0`-cochain `unitCochain f U hU` is a cocycle: its composite with the Čech differential
in degree `0` vanishes. -/
theorem unitCochain_comp_d (hcov : (⊤ : X.Opens) ≤ ⨆ i, U i) :
    unitCochain f U hU ≫
      (baseAlternatingCechComplex f U hU (SheafOfModules.unit X.ringCatSheaf)).d 0 1 = 0 :=
  sectionCochain_comp_d f U hU hcov _ _

/-- **The unit `A ⟶ RΓ(X, 𝒪_X)` on the Čech model.** -/
abbrev unitModelMap (hcov : (⊤ : X.Opens) ≤ ⨆ i, U i) :
    baseUnitComplex A ⟶ baseAlternatingCechComplex f U hU (SheafOfModules.unit X.ringCatSheaf) :=
  sectionModelMap f U hU hcov (SheafOfModules.unit X.ringCatSheaf)
    (show Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) from (1 : Γ(X, ⊤)))

end Map

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
