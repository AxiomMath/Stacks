module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Duality.ProductOfStructureSheavesNotQuasiCoherent

/-!
# A countable product of structure sheaves of an algebraic space which is not quasi-coherent

Let `F` be an algebraic space, `U` an étale chart of `F` with affine underlying scheme, and
`t ∈ 𝒪_F(U)` a regular function admitting no equation `t^j = t^{j+1} b`. Then the countable
product `∏_{n ≥ 0} 𝒪_F`, taken in the category of `𝒪_F`-modules on the small étale site of `F`,
is not quasi-coherent.

This is the étale form of `Stacks.Duality.not_isQuasicoherent_piStructureSheaf`, the obstruction
of [Stacks, Tag 0GEU], and the argument is the same: a quasi-coherent `𝒪_F`-module is cartesian
on affine charts (Descent, Proposition 03DX (2)), so its sections over the basic-open chart of `t`
are the localization away from `t` of its sections over `U`
(`AlgebraicGeometry.Space.isLocalizedModule_chartRestrictLinear_openChart_basicOpen`); the section
of the product over the basic-open chart whose `n`-th coordinate is `1/t^n` would then be a section
over `U` divided by a single power of `t`, and `Stacks.Duality.exists_pow_smul_eq_succ` turns that
into the forbidden equation.

## Main results

* `AlgebraicGeometry.Space.bijective_piSections` — sections of a product of sheaves of modules
  are families of sections.
* `AlgebraicGeometry.Space.not_isQuasicoherentOnSite_piUnit` — the product is not
  quasi-coherent.

## References

* [Stacks Project, Tag 0GEU](https://stacks.math.columbia.edu/tag/0GEU)
* [Stacks Project, Tag 0GG3](https://stacks.math.columbia.edu/tag/0GG3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- **Sections of a product are the product of the sections**, for a product indexed by a type
in the universe of the module sections. -/
theorem bijective_piSections {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {ι : Type u} (f : ι → SheafOfModules.{u} R) (U : Cᵒᵖ) :
    Function.Bijective
      (fun (s : ((SheafOfModules.evaluation R U).obj (∏ᶜ f) : Type u)) (i : ι) =>
        ((SheafOfModules.evaluation R U).map (Pi.π f i) s :
          ((SheafOfModules.evaluation R U).obj (f i) : Type u))) := by
  have key :
      (fun (s : ((SheafOfModules.evaluation R U).obj (∏ᶜ f) : Type u)) (i : ι) =>
        ((SheafOfModules.evaluation R U).map (Pi.π f i) s :
          ((SheafOfModules.evaluation R U).obj (f i) : Type u))) =
      fun s => (piComparison (SheafOfModules.evaluation R U) f ≫
        (ModuleCat.piIsoPi (fun i => (SheafOfModules.evaluation R U).obj (f i))).hom) s := by
    funext s i
    have h2 : piComparison (SheafOfModules.evaluation R U) f ≫ Pi.π _ i =
        (SheafOfModules.evaluation R U).map (Pi.π f i) := by simp [piComparison]
    have h1 := congrArg (fun φ => ModuleCat.Hom.hom φ
        ((ModuleCat.Hom.hom (piComparison (SheafOfModules.evaluation R U) f)) s))
      (ModuleCat.piIsoPi_hom_ker_subtype
        (fun i => (SheafOfModules.evaluation R U).obj (f i)) i)
    rw [ModuleCat.comp_apply, ← h2, ModuleCat.comp_apply]
    exact h1.symm
  rw [key]
  exact ConcreteCategory.bijective_of_isIso _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)

/-- The product `∏_{n ≥ 0} 𝒪_F` of countably many copies of the structure sheaf, in the category
of `𝒪_F`-modules on the small étale site. -/
abbrev piUnit : Modules.{u, u} B S hS F hF :=
  ∏ᶜ fun _ : ULift.{u} ℕ =>
    SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)

/-- The `n`-th coordinate of a section over `V` of `∏_{n ≥ 0} 𝒪_F`, as a map linear over the
functions on a chart `U` under `V`. -/
def piUnitCoordinate {U V : SmallEtale B S hS F} (φ : V ⟶ U) (n : ℕ) :
    letI := chartSectionsModule (piUnit hF) φ
    letI := chartSectionsModule
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) φ
    ((piUnit hF).val.obj (op V) : Type u) →ₗ[chartRing B S hS F hF U]
      ((SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).val.obj
          (op V) : Type u) :=
  letI := chartSectionsModule (piUnit hF) φ
  letI := chartSectionsModule
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) φ
  { toFun := fun s => ((Pi.π _ (ULift.up n) : piUnit hF ⟶ _).val.app (op V)).hom s
    map_add' := fun s s' => map_add _ s s'
    map_smul' := fun r s => ((Pi.π _ (ULift.up n) : piUnit hF ⟶ _).val.app (op V)).hom.map_smul
      (chartRestrict φ r) s }

/-- **`∏_{n ≥ 0} 𝒪_F` is not quasi-coherent** as soon as some affine étale chart `U` of `F`
carries a regular function `t` admitting no equation `t^j = t^{j+1} b`. -/
theorem not_isQuasicoherentOnSite_piUnit (U : SmallEtale B S hS F)
    (hU : IsAffine (chartScheme U)) (t : chartRing B S hS F hF U)
    (ht : ∀ (j : ℕ) (b : chartRing B S hS F hF U), t ^ j ≠ t ^ (j + 1) * b) :
    ¬ (piUnit hF).IsQuasicoherentOnSite := by
  intro hqc
  let O := SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  let i := openChartInclusion B S hS F U ((chartScheme U).basicOpen t)
  let := chartSectionsModule (piUnit hF) i
  let := chartSectionsModule O i
  have hO := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS hF O
    isCartesianOnAffineCharts_unit U hU t
  have hP := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS hF (piUnit hF)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ hqc) U hU t
  obtain ⟨j, b, hjb⟩ := Stacks.Duality.exists_pow_smul_eq_succ t hO hP
    (fun n => piUnitCoordinate hF (𝟙 U) n) (fun n => piUnitCoordinate hF i n)
    (fun n x => PresheafOfModules.naturality_apply
      (Pi.π _ (ULift.up n) : piUnit hF ⟶ _).val i.op x)
    (fun y => by
      obtain ⟨s, hs⟩ := (bijective_piSections
        (fun _ : ULift.{u} ℕ => O) (op (openChart B S hS F U ((chartScheme U).basicOpen t)))).2
        (fun k => y k.down)
      exact ⟨s, funext fun n => congrFun hs (ULift.up n)⟩)
    (1 : chartRing B S hS F hF U)
  refine ht j (show chartRing B S hS F hF U from b) ?_
  have h : t ^ j * (1 : chartRing B S hS F hF U) =
      t ^ (j + 1) * (show chartRing B S hS F hF U from b) := hjb
  rwa [mul_one] at h

end AlgebraicGeometry.Space

end
